import Lax842588Proofs.PrimitiveRecursivePairing
import Lax865980Proofs.Frame
import Lax865980Proofs.Compile
import Mathlib.Logic.Equiv.List

/-!
Charged conversion from an array prefix to the internal numeric list convention.
The source array is built by preceding runtime phases. This routine reads each
entry, in reverse order, and executes the pairing arithmetic; an encoded list
is never supplied for free. The scratch registers are fixed and the source
array, all other arrays, and both tapes are preserved.
-/

namespace Lax842588Proofs.CompilerArrayPacking

set_option maxHeartbeats 1000000

open Lax865980Proofs.Imp Lax865980Proofs.Reasoning Lax865980Proofs.Compile
open Lax842588Proofs.PrimitiveRecursivePairing
open Encodable

def Prefix (arr : String) (xs : List Nat) (σ : Env) : Prop :=
  ∀ i (hi : i < xs.length), (σ.arrs arr)[i]? = some xs[i]

theorem encode_drop_le (xs : List Nat) (i : Nat) : encode (xs.drop i) ≤ encode xs := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [List.drop_succ_cons, encode_list_cons]
          exact (ih i).trans ((Nat.right_le_pair _ _).trans (Nat.le_succ _))

theorem entry_le_encode (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    xs[i] ≤ encode xs := by
  have hd := encode_drop_le xs i
  rw [List.drop_eq_getElem_cons hi, encode_list_cons] at hd
  exact (Nat.left_le_pair xs[i] (encode (xs.drop (i + 1)))).trans
    (Nat.le_of_lt (by simpa using hd))

def condition : Cond := .lt (.lit 0) (.var "packIndex")

def step (arr : String) : Com :=
  .seq (.assign "packIndex" (.sub (.var "packIndex") (.lit 1)))
    (.seq (.assign "packValue" (.get arr (.var "packIndex")))
      (.seq (pairProgram "packValue" "packCode" "packCode")
        (.assign "packCode" (.add (.var "packCode") (.lit 1)))))

def loop (arr : String) : Com := .while condition (step arr)

def program (arr length : String) : Com :=
  .seq (.assign "packIndex" (.var length))
    (.seq (.assign "packCode" (.lit 0)) (loop arr))

def Inv (arr : String) (xs : List Nat) (σ : Env) : Prop :=
  Prefix arr xs σ ∧ σ.vars "packIndex" ≤ xs.length ∧
    σ.vars "packCode" = encode (xs.drop (σ.vars "packIndex"))

theorem condition_eval (B : Nat) (arr : String) (xs : List Nat) (σ : Env)
    (hB : (2 * encode xs + 3) ^ 2 < B) (hI : Inv arr xs σ) :
    condition.evalB B σ = some (decide (0 < σ.vars "packIndex")) := by
  have hl := length_le_encode xs
  have hi : σ.vars "packIndex" < B := by obtain ⟨_, hi, _⟩ := hI; nlinarith
  have h0 : 0 < B := by nlinarith
  simp [condition, Cond.evalB, Expr.evalB, fit_self hi, fit_self h0]

theorem step_spec (B : Nat) (arr : String) (xs : List Nat)
    (hB : (2 * encode xs + 3) ^ 2 < B) :
    Spec B (fun σ => Inv arr xs σ ∧ condition.evalB B σ = some true)
      (step arr) (fun σ σ' => Inv arr xs σ' ∧
        σ'.vars "packIndex" < σ.vars "packIndex") 40 := by
  intro σ hσ
  obtain ⟨hI, ht⟩ := hσ
  rw [condition_eval B arr xs σ hB hI] at ht
  have hpos : 0 < σ.vars "packIndex" := by simpa using ht
  obtain ⟨hp, hi, hc⟩ := hI
  have hj : σ.vars "packIndex" - 1 < xs.length := by omega
  have hget := hp (σ.vars "packIndex" - 1) hj
  have harrayIndex : σ.vars "packIndex" - 1 < (σ.arrs arr).length := by
    by_contra h
    have hn : (σ.arrs arr)[σ.vars "packIndex" - 1]? = none :=
      List.getElem?_eq_none (by omega)
    rw [hn] at hget
    contradiction
  have hentry := entry_le_encode xs (σ.vars "packIndex" - 1) hj
  have htail := encode_drop_le xs (σ.vars "packIndex")
  have hlen := length_le_encode xs
  have hdrop : encode (xs.drop (σ.vars "packIndex" - 1)) =
      Nat.pair xs[σ.vars "packIndex" - 1]
        (encode (xs.drop (σ.vars "packIndex"))) + 1 := by
    have hk : σ.vars "packIndex" - 1 + 1 = σ.vars "packIndex" := by omega
    rw [List.drop_eq_getElem_cons hj, encode_list_cons, hk]
    rfl
  have hnext := encode_drop_le xs (σ.vars "packIndex" - 1)
  have hsquare : (xs[σ.vars "packIndex" - 1] + σ.vars "packCode" + 1) ^ 2 < B := by
    rw [hc]
    nlinarith
  have hpair := (pair_spec B xs[σ.vars "packIndex" - 1] (σ.vars "packCode")
    "packValue" "packCode" "packCode" hsquare).frame
  unfold step
  run_vcg [hpair]
  all_goals simp_all [Inv, Prefix, pairProgram, Com.wvars, Com.warrs]
  all_goals nlinarith

theorem loop_spec (B : Nat) (arr : String) (xs : List Nat)
    (hB : (2 * encode xs + 3) ^ 2 < B) :
    Spec B (Inv arr xs) (loop arr)
      (fun _ σ => σ.vars "packCode" = encode xs) (50 * (xs.length + 1)) := by
  have hl : Spec B (Inv arr xs) (loop arr)
      (fun _ σ => Inv arr xs σ ∧ condition.evalB B σ = some false)
      (50 * (xs.length + 1)) := by
    apply Spec.while_count (Inv arr xs) (fun σ => σ.vars "packIndex") 40
    · intro σ hI
      exact ⟨_, condition_eval B arr xs σ hB hI⟩
    · exact step_spec B arr xs hB
    · exact fun _ h => h
    · intro σ hI
      obtain ⟨_, hi, _⟩ := hI
      simp [condition, Cond.size, Expr.size]
      omega
  apply hl.post
  intro σ σ' _ hpost
  obtain ⟨hI, ht⟩ := hpost
  rw [condition_eval B arr xs σ' hB hI] at ht
  have hi : σ'.vars "packIndex" = 0 := by simpa using ht
  simpa [hi] using hI.2.2

theorem program_spec (B : Nat) (arr length : String) (xs : List Nat)
    (hB : (2 * encode xs + 3) ^ 2 < B) :
    Spec B (fun σ => Prefix arr xs σ ∧ σ.vars length = xs.length)
      (program arr length) (fun _ σ => σ.vars "packCode" = encode xs)
      (60 * (xs.length + 1)) := by
  have hlen := length_le_encode xs
  have hloop := loop_spec B arr xs hB
  intro σ hσ
  obtain ⟨hp, hl⟩ := hσ
  unfold program
  run_vcg [hloop]
  all_goals simp_all [Inv, Prefix]
  all_goals nlinarith

@[simp] theorem program_warrs (arr length : String) : (program arr length).warrs = [] := by
  simp [program, loop, step, pairProgram, Com.warrs]

theorem program_noRead (arr length : String) : ¬ (program arr length).reads := by
  simp [program, loop, step, pairProgram, Com.reads]

theorem program_noWrite (arr length : String) : (program arr length).NoWrite := by
  simp [program, loop, step, pairProgram, Com.NoWrite]

theorem program_ok (arr length : String) (L : Layout)
    (ht : 5 ≤ L.temps) (ha : arr ∈ L.arrays) (hl : length ∈ L.scalars)
    (hi : "packIndex" ∈ L.scalars) (hv : "packValue" ∈ L.scalars)
    (hc : "packCode" ∈ L.scalars) : Com.Ok L (program arr length) := by
  simp [program, loop, step, condition, pairProgram, Com.Ok, Cond.Ok, Expr.Ok,
    Lax865980Proofs.Compile.condExpr, ha, hl, hi, hv, hc]
  omega

/-- Fixed-register counterpart used for one six-field compiler row. The
register list is program syntax, not input-dependent program generation. -/
def registerProgram (dst : String) : List String → Com
  | [] => .assign dst (.lit 0)
  | src :: rest => .seq (registerProgram dst rest)
      (.seq (pairProgram src dst dst) (.assign dst (.add (.var dst) (.lit 1))))

theorem registerProgram_wvars (dst : String) (regs : List String) (s : String)
    (hne : s ≠ dst) : s ∉ (registerProgram dst regs).wvars := by
  induction regs with
  | nil => simp [registerProgram, Com.wvars, hne]
  | cons src rest ih => simp [registerProgram, pairProgram, Com.wvars, hne, ih]

theorem registerProgram_spec (B : Nat) (dst : String) (regs : List String)
    (xs : List Nat) (hdst : dst ∉ regs) (hB : (2 * encode xs + 3) ^ 2 < B) :
    Spec B (fun σ => regs.map σ.vars = xs) (registerProgram dst regs)
      (fun _ σ => σ.vars dst = encode xs) (25 * (regs.length + 1)) := by
  induction regs generalizing xs with
  | nil =>
      intro σ hσ
      have hx : xs = [] := by simpa using hσ.symm
      subst xs
      unfold registerProgram
      run_vcg
      all_goals simp_all
      all_goals omega
  | cons src rest ih =>
      intro σ hσ
      cases xs with
      | nil => simp at hσ
      | cons x xs =>
          obtain ⟨hx, hxs⟩ := List.cons.inj hσ
          have htail : encode xs ≤ encode (x :: xs) :=
            (Nat.right_le_pair _ _).trans (Nat.le_succ _)
          have hhead : x ≤ encode (x :: xs) :=
            (Nat.left_le_pair _ _).trans (Nat.le_succ _)
          simp only [List.mem_cons, not_or] at hdst
          have hsrc : src ≠ dst := Ne.symm hdst.1
          have hrest : dst ∉ rest := hdst.2
          have htailB : (2 * encode xs + 3) ^ 2 < B := by nlinarith
          obtain ⟨τ, hr, hc⟩ := ih xs hrest htailB σ hxs
          have hkeep : τ.vars src = x :=
            (hr.frame_var src (registerProgram_wvars dst rest src hsrc)).trans hx
          have hpairB : (x + encode xs + 1) ^ 2 < B := by nlinarith
          obtain ⟨υ, hp, hv⟩ := pair_spec B x (encode xs) src dst dst hpairB τ ⟨hkeep, hc⟩
          have hval : Nat.pair x (encode xs) + 1 < B := by
            have he : encode (x :: xs) = Nat.pair x (encode xs) + 1 := rfl
            nlinarith
          have heval : (Expr.add (.var dst) (.lit 1)).evalB B υ =
              some (encode (x :: xs)) := by
            simp [Expr.evalB, Bop.apply, hv, fit_self (show Nat.pair x (encode xs) < B by omega),
              fit_self (show 1 < B by omega), fit_self hval, encode_list_cons]
          exact ⟨υ.setVar dst (encode (x :: xs)),
            (hr.seq (hp.seq (Run.assign heval))).mono
              (by simp [Expr.size]; omega), by simp⟩

@[simp] theorem registerProgram_warrs (dst : String) (regs : List String) :
    (registerProgram dst regs).warrs = [] := by
  induction regs with
  | nil => simp [registerProgram, Com.warrs]
  | cons src rest ih => simp [registerProgram, pairProgram, Com.warrs, ih]

theorem registerProgram_noRead (dst : String) (regs : List String) :
    ¬ (registerProgram dst regs).reads := by
  induction regs with
  | nil => simp [registerProgram, Com.reads]
  | cons src rest ih => simp [registerProgram, pairProgram, Com.reads, ih]

theorem registerProgram_noWrite (dst : String) (regs : List String) :
    (registerProgram dst regs).NoWrite := by
  induction regs with
  | nil => simp [registerProgram, Com.NoWrite]
  | cons src rest ih => simp [registerProgram, pairProgram, Com.NoWrite, ih]

theorem registerProgram_ok (dst : String) (regs : List String) (L : Layout)
    (ht : 5 ≤ L.temps) (hd : dst ∈ L.scalars)
    (hs : ∀ s ∈ regs, s ∈ L.scalars) : Com.Ok L (registerProgram dst regs) := by
  induction regs with
  | nil => simp [registerProgram, Com.Ok, Expr.Ok, hd]
  | cons src rest ih =>
      have hsrc := hs src (by simp)
      have hr := ih (fun s h => hs s (by simp [h]))
      simp [registerProgram, pairProgram, Com.Ok, Cond.Ok, Expr.Ok, condExpr, hd, hsrc, hr]
      omega

end Lax842588Proofs.CompilerArrayPacking
