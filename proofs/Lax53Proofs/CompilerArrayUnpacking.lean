import Lax53Proofs.CompilerArrayPacking
import Lax53Proofs.ImpArrayLengths

/-!
Counted materialization of the compiler's flat numeric result. Every list
cell is decoded by the verified subtraction/square-root unpairing routines
and stored into the existing evaluator array. This is an internal phase:
neither encoded numbers nor automata become additional public inputs.
-/

namespace Lax53Proofs.CompilerArrayUnpacking

set_option maxHeartbeats 1500000

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax53Proofs.PrimitiveRecursivePairing
open Lax53Proofs.CompilerArrayPacking (encode_drop_le entry_le_encode)
open Encodable

def splitCell : Com :=
  .seq (.assign "unpackHead" (.sub (.var "unpackCode") (.lit 1)))
    (.seq (.assign "unpackTail" (.var "unpackHead"))
      (.seq (unpairLeftProgram "unpackHead" "unpackSqrt" "unpackRem")
        (unpairRightProgram "unpackTail" "unpackSqrt" "unpackRem")))

theorem splitCell_spec (B head tail : Nat)
    (hB : 2 * Nat.pair head tail + 3 < B) :
    Spec B (fun σ => σ.vars "unpackCode" = Nat.pair head tail + 1)
      splitCell (fun _ σ => σ.vars "unpackHead" = head ∧ σ.vars "unpackTail" = tail)
      (130 * (Nat.pair head tail + 1)) := by
  have hl := (unpairLeft_spec B (Nat.pair head tail)
    "unpackHead" "unpackSqrt" "unpackRem" (by decide) hB).frame
  have hr := (unpairRight_spec B (Nat.pair head tail)
    "unpackTail" "unpackSqrt" "unpackRem" (by decide) hB).frame
  intro σ hc
  unfold splitCell
  run_vcg [hl, hr]
  all_goals simp_all [unpairLeftProgram, unpairRightProgram, sqrtProgram,
    sqrtLoop, sqrtStep, Com.wvars, Com.warrs]

def condition : Cond := .lt (.lit 0) (.var "unpackCode")

def step (arr : String) : Com :=
  .seq splitCell
    (.seq (.store arr (.var "unpackIndex") (.var "unpackHead"))
      (.seq (.assign "unpackCode" (.var "unpackTail"))
        (.assign "unpackIndex" (.add (.var "unpackIndex") (.lit 1)))))

def loop (arr : String) : Com := .while condition (step arr)

/-- Input is an untagged list code; the typed compiler's outer `some` tag is
removed by the separate composition wrapper. -/
def program (arr : String) : Com :=
  .seq (.assign "unpackIndex" (.lit 0)) (loop arr)

def Inv (arr : String) (xs : List Nat) (σ : Env) : Prop :=
  σ.vars "unpackIndex" ≤ xs.length ∧
    σ.vars "unpackCode" = encode (xs.drop (σ.vars "unpackIndex")) ∧
    xs.length ≤ (σ.arrs arr).length ∧
    (σ.arrs arr).take (σ.vars "unpackIndex") = xs.take (σ.vars "unpackIndex")

theorem take_set_next (data xs : List Nat) (i : Nat)
    (hi : i < xs.length) (hd : xs.length ≤ data.length)
    (hp : data.take i = xs.take i) :
    (data.set i xs[i]).take (i + 1) = xs.take (i + 1) := by
  rw [List.take_succ_eq_append_getElem (by simpa using hi.trans_le hd),
    List.take_set_of_le (by omega), List.getElem_set_self, hp,
    List.take_succ_eq_append_getElem hi]

theorem condition_eval (B : Nat) (arr : String) (xs : List Nat) (σ : Env)
    (hB : 2 * encode xs + 3 < B) (hI : Inv arr xs σ) :
    condition.evalB B σ = some (decide (0 < σ.vars "unpackCode")) := by
  have hc := encode_drop_le xs (σ.vars "unpackIndex")
  have hv : σ.vars "unpackCode" < B := by rw [hI.2.1]; omega
  simp [condition, Cond.evalB, Expr.evalB, fit_self hv, fit_self (show 0 < B by omega)]

theorem step_spec (B : Nat) (arr : String) (xs : List Nat)
    (hB : 2 * encode xs + 3 < B) :
    Spec B (fun σ => Inv arr xs σ ∧ condition.evalB B σ = some true)
      (step arr) (fun σ σ' => Inv arr xs σ' ∧
        xs.length - σ'.vars "unpackIndex" < xs.length - σ.vars "unpackIndex")
      (150 * (encode xs + 1)) := by
  intro σ hσ
  obtain ⟨hI, ht⟩ := hσ
  rw [condition_eval B arr xs σ hB hI] at ht
  have hpos : 0 < σ.vars "unpackCode" := by simpa using ht
  obtain ⟨hi, hc, hlen, hp⟩ := hI
  have hj : σ.vars "unpackIndex" < xs.length := by
    by_contra h
    have he : σ.vars "unpackIndex" = xs.length := by omega
    simp [he] at hc
    omega
  have hcell : σ.vars "unpackCode" = Nat.pair xs[σ.vars "unpackIndex"]
      (encode (xs.drop (σ.vars "unpackIndex" + 1))) + 1 := by
    rw [hc, List.drop_eq_getElem_cons hj, encode_list_cons]
    rfl
  have hbound := encode_drop_le xs (σ.vars "unpackIndex")
  have hentry := entry_le_encode xs (σ.vars "unpackIndex") hj
  have htail := encode_drop_le xs (σ.vars "unpackIndex" + 1)
  have hsize := length_le_encode xs
  have hpairB : 2 * Nat.pair xs[σ.vars "unpackIndex"]
      (encode (xs.drop (σ.vars "unpackIndex" + 1))) + 3 < B := by
    rw [← hc, hcell] at hbound
    omega
  have hsplit := (splitCell_spec B xs[σ.vars "unpackIndex"]
    (encode (xs.drop (σ.vars "unpackIndex" + 1))) hpairB).frame
  have hprefix := take_set_next (σ.arrs arr) xs (σ.vars "unpackIndex") hj hlen hp
  unfold step
  run_vcg [hsplit]
  all_goals simp_all [Inv, splitCell, unpairLeftProgram, unpairRightProgram,
    sqrtProgram, sqrtLoop, sqrtStep, Com.wvars, Com.warrs]
  all_goals omega

theorem loop_spec (B : Nat) (arr : String) (xs : List Nat)
    (hB : 2 * encode xs + 3 < B) :
    Spec B (Inv arr xs) (loop arr)
      (fun _ σ => (σ.arrs arr).take xs.length = xs ∧ σ.vars "unpackIndex" = xs.length)
      (160 * (encode xs + 1) * (xs.length + 1)) := by
  have hl : Spec B (Inv arr xs) (loop arr)
      (fun _ σ => Inv arr xs σ ∧ condition.evalB B σ = some false)
      (160 * (encode xs + 1) * (xs.length + 1)) := by
    apply Spec.while_count (Inv arr xs)
      (fun σ => xs.length - σ.vars "unpackIndex") (150 * (encode xs + 1))
    · intro σ hI
      exact ⟨_, condition_eval B arr xs σ hB hI⟩
    · exact step_spec B arr xs hB
    · exact fun _ h => h
    · intro σ hI
      have hs : xs.length - σ.vars "unpackIndex" ≤ xs.length := Nat.sub_le _ _
      simp [condition, Cond.size, Expr.size]
      nlinarith
  apply hl.post
  intro σ σ' _ hpost
  obtain ⟨hI, ht⟩ := hpost
  rw [condition_eval B arr xs σ' hB hI] at ht
  have hc : σ'.vars "unpackCode" = 0 := by simpa using ht
  have hi : σ'.vars "unpackIndex" = xs.length := by
    by_contra h
    have hj : σ'.vars "unpackIndex" < xs.length := by have := hI.1; omega
    have he := hI.2.1
    rw [List.drop_eq_getElem_cons hj, encode_list_cons, hc] at he
    omega
  exact ⟨by simpa [hi] using hI.2.2.2, hi⟩

theorem program_spec (B : Nat) (arr : String) (xs : List Nat)
    (hB : 2 * encode xs + 3 < B) :
    Spec B (fun σ => σ.vars "unpackCode" = encode xs ∧ xs.length ≤ (σ.arrs arr).length)
      (program arr)
      (fun _ σ => (σ.arrs arr).take xs.length = xs ∧ σ.vars "unpackIndex" = xs.length)
      (170 * (encode xs + 1) * (xs.length + 1)) := by
  intro σ hσ
  have hinit : Run B (.assign "unpackIndex" (.lit 0)) σ
      (σ.setVar "unpackIndex" 0) 2 :=
    Run.assign (by simp [Expr.evalB, fit_self (show 0 < B by omega)])
  obtain ⟨τ, hrun, hout⟩ := loop_spec B arr xs hB
    (σ.setVar "unpackIndex" 0) (by simp [Inv, hσ.1, hσ.2])
  exact ⟨τ, (hinit.seq hrun).mono (by nlinarith), hout⟩

theorem program_noRead (arr : String) : ¬ (program arr).reads := by
  simp [program, loop, step, splitCell, unpairLeftProgram, unpairRightProgram,
    sqrtProgram, sqrtLoop, sqrtStep, Com.reads]

theorem program_noWrite (arr : String) : (program arr).NoWrite := by
  simp [program, loop, step, splitCell, unpairLeftProgram, unpairRightProgram,
    sqrtProgram, sqrtLoop, sqrtStep, Com.NoWrite]

theorem program_warrs (arr : String) : (program arr).warrs = [arr] := by
  simp [program, loop, step, splitCell, unpairLeftProgram, unpairRightProgram,
    sqrtProgram, sqrtLoop, sqrtStep, Com.warrs]

def scalars : List String :=
  ["unpackCode", "unpackIndex", "unpackHead", "unpackTail", "unpackSqrt", "unpackRem"]

theorem program_ok (arr : String) (L : Layout) (ht : 5 ≤ L.temps)
    (ha : arr ∈ L.arrays) (hvars : ∀ name ∈ scalars, name ∈ L.scalars) :
    Com.Ok L (program arr) := by
  have hc := hvars "unpackCode" (by simp [scalars])
  have hi := hvars "unpackIndex" (by simp [scalars])
  have hh := hvars "unpackHead" (by simp [scalars])
  have htail := hvars "unpackTail" (by simp [scalars])
  have hs := hvars "unpackSqrt" (by simp [scalars])
  have hr := hvars "unpackRem" (by simp [scalars])
  simp [program, loop, step, condition, splitCell, unpairLeftProgram,
    unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep, sqrtCond, oddExpr,
    Com.Ok, Cond.Ok, Expr.Ok, condExpr, ha, hc, hi, hh, htail, hs, hr]
  omega

end Lax53Proofs.CompilerArrayUnpacking
