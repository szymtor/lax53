import Lax865980Proofs.Tactic
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Linarith

/-!
Charged arithmetic for the primitive-recursive execution bridge.

Pairing is ordinary multiplication and addition. Unpairing uses a counted
subtraction loop to obtain the square root and remainder; neither square
root nor an arbitrary Lean function is treated as a machine instruction.
All specifications use the existing bounded IMP+ semantics consumed by the
verified IMP+-to-RAM compiler. Registers are parameters, so callers can
reserve fresh scratch space without introducing another memory convention.
-/

namespace Lax842588Proofs.PrimitiveRecursivePairing

open Lax865980Proofs.Imp Lax865980Proofs.Reasoning

def pairProgram (x y out : String) : Com :=
  .ite (.lt (.var x) (.var y))
    (.assign out (.add (.mul (.var y) (.var y)) (.var x)))
    (.assign out (.add (.add (.mul (.var x) (.var x)) (.var x)) (.var y)))

theorem pair_spec (B a b : Nat) (x y out : String)
    (hB : (a + b + 1) ^ 2 < B) :
    Spec B (fun σ => σ.vars x = a ∧ σ.vars y = b)
      (pairProgram x y out) (fun _ σ => σ.vars out = Nat.pair a b) 20 := by
  intro σ hσ
  obtain ⟨hx, hy⟩ := hσ
  have ha : a < B := by nlinarith
  have hb : b < B := by nlinarith
  have haa : a * a < B := by nlinarith
  have hbb : b * b < B := by nlinarith
  have hab : a * a + a + b < B := by nlinarith
  have hba : b * b + a < B := by nlinarith
  unfold pairProgram
  run_vcg
  all_goals simp_all [Nat.pair]
  all_goals omega

/-- The next odd number is the difference between consecutive squares. -/
def oddExpr (s : String) : Expr := .add (.mul (.lit 2) (.var s)) (.lit 1)

def sqrtCond (s r : String) : Cond := .lt (oddExpr s) (.add (.var r) (.lit 1))

def sqrtStep (s r : String) : Com :=
  .seq (.assign r (.sub (.var r) (oddExpr s)))
    (.assign s (.add (.var s) (.lit 1)))

def sqrtLoop (s r : String) : Com := .while (sqrtCond s r) (sqrtStep s r)

def SqrtInv (n : Nat) (s r : String) (σ : Env) : Prop :=
  n = σ.vars s * σ.vars s + σ.vars r ∧ σ.vars s ≤ n ∧ σ.vars r ≤ n

theorem sqrtCond_eval (B n : Nat) (s r : String) (σ : Env)
    (hB : 2 * n + 3 < B) (hI : SqrtInv n s r σ) :
    (sqrtCond s r).evalB B σ = some (decide (2 * σ.vars s + 1 ≤ σ.vars r)) := by
  obtain ⟨_, hs, hr⟩ := hI
  have hsB : σ.vars s < B := by omega
  have hrB : σ.vars r < B := by omega
  have h2 : 2 < B := by omega
  have h1 : 1 < B := by omega
  have hmul : 2 * σ.vars s < B := by omega
  have hadd : 2 * σ.vars s + 1 < B := by omega
  have hradd : σ.vars r + 1 < B := by omega
  simp [sqrtCond, oddExpr, Cond.evalB, Expr.evalB, Bop.apply,
    fit_self hsB, fit_self hrB, fit_self h2, fit_self h1,
    fit_self hmul, fit_self hadd, fit_self hradd]

theorem sqrtStep_spec (B n : Nat) (s r : String) (hsr : s ≠ r)
    (hB : 2 * n + 3 < B) :
    Spec B (fun σ => SqrtInv n s r σ ∧ (sqrtCond s r).evalB B σ = some true)
      (sqrtStep s r)
      (fun σ σ' => SqrtInv n s r σ' ∧ σ'.vars r < σ.vars r) 20 := by
  intro σ hσ
  obtain ⟨hI, ht⟩ := hσ
  rw [sqrtCond_eval B n s r σ hB hI] at ht
  have hodd : 2 * σ.vars s + 1 ≤ σ.vars r := by simpa using ht
  obtain ⟨heq, hs, hr⟩ := hI
  have hsub := Nat.sub_add_cancel hodd
  have hnext : σ.vars s + 1 ≤ n := by nlinarith
  have hnextEq : n = (σ.vars s + 1) * (σ.vars s + 1) +
      (σ.vars r - (2 * σ.vars s + 1)) := by nlinarith
  unfold sqrtStep oddExpr
  run_vcg
  all_goals simp_all [SqrtInv, Ne.symm hsr]
  all_goals omega

theorem sqrtLoop_spec (B n : Nat) (s r : String) (hsr : s ≠ r)
    (hB : 2 * n + 3 < B) :
    Spec B (SqrtInv n s r) (sqrtLoop s r)
      (fun _ σ => σ.vars s = n.sqrt ∧ σ.vars r = n - n.sqrt * n.sqrt)
      (40 * (n + 1)) := by
  have hloop : Spec B (SqrtInv n s r) (sqrtLoop s r)
      (fun _ σ => SqrtInv n s r σ ∧ (sqrtCond s r).evalB B σ = some false)
      (40 * (n + 1)) := by
    apply Spec.while_count (SqrtInv n s r) (fun σ => σ.vars r) 20
    · intro σ hI
      exact ⟨_, sqrtCond_eval B n s r σ hB hI⟩
    · exact sqrtStep_spec B n s r hsr hB
    · exact fun _ h => h
    · intro σ hI
      obtain ⟨_, _, hr⟩ := hI
      simp [sqrtCond, oddExpr, Cond.size, Expr.size]
      omega
  apply hloop.post
  intro σ σ' _ hpost
  obtain ⟨hI, hfalse⟩ := hpost
  rw [sqrtCond_eval B n s r σ' hB hI] at hfalse
  have hstop : σ'.vars r < 2 * σ'.vars s + 1 := by simpa using hfalse
  obtain ⟨heq, _, _⟩ := hI
  have hsqrt : σ'.vars s = n.sqrt := Nat.eq_sqrt.mpr ⟨by omega, by nlinarith⟩
  exact ⟨hsqrt, by rw [← hsqrt]; omega⟩

def sqrtProgram (x s r : String) : Com :=
  .seq (.assign r (.var x))
    (.seq (.assign s (.lit 0)) (sqrtLoop s r))

theorem sqrt_spec (B n : Nat) (x s r : String) (hsr : s ≠ r)
    (hB : 2 * n + 3 < B) :
    Spec B (fun σ => σ.vars x = n) (sqrtProgram x s r)
      (fun _ σ => σ.vars s = n.sqrt ∧ σ.vars r = n - n.sqrt * n.sqrt)
      (50 * (n + 1)) := by
  have hloop := sqrtLoop_spec B n s r hsr hB
  intro σ hx
  unfold sqrtProgram
  run_vcg [hloop]
  all_goals simp_all [SqrtInv, Ne.symm hsr]

def unpairLeftProgram (x s r : String) : Com :=
  .seq (sqrtProgram x s r)
    (.ite (.lt (.var r) (.var s))
      (.assign x (.var r)) (.assign x (.var s)))

def unpairRightProgram (x s r : String) : Com :=
  .seq (sqrtProgram x s r)
    (.ite (.lt (.var r) (.var s))
      (.assign x (.var s)) (.assign x (.sub (.var r) (.var s))))

theorem unpairLeft_spec (B n : Nat) (x s r : String) (hsr : s ≠ r)
    (hB : 2 * n + 3 < B) :
    Spec B (fun σ => σ.vars x = n) (unpairLeftProgram x s r)
      (fun _ σ => σ.vars x = n.unpair.1) (60 * (n + 1)) := by
  have hs := Nat.sqrt_le_self n
  have hr : n - n.sqrt * n.sqrt ≤ n := Nat.sub_le _ _
  have hroot := sqrt_spec B n x s r hsr hB
  intro σ hx
  unfold unpairLeftProgram
  run_vcg [hroot]
  all_goals simp_all [Nat.unpair]
  all_goals split_ifs <;> simp_all [Nat.sub_sub]
  all_goals omega

theorem unpairRight_spec (B n : Nat) (x s r : String) (hsr : s ≠ r)
    (hB : 2 * n + 3 < B) :
    Spec B (fun σ => σ.vars x = n) (unpairRightProgram x s r)
      (fun _ σ => σ.vars x = n.unpair.2) (60 * (n + 1)) := by
  have hs := Nat.sqrt_le_self n
  have hr : n - n.sqrt * n.sqrt ≤ n := Nat.sub_le _ _
  have hroot := sqrt_spec B n x s r hsr hB
  intro σ hx
  unfold unpairRightProgram
  run_vcg [hroot]
  all_goals simp_all [Nat.unpair]
  all_goals split_ifs <;> simp_all [Nat.sub_sub]
  all_goals omega

end Lax842588Proofs.PrimitiveRecursivePairing
