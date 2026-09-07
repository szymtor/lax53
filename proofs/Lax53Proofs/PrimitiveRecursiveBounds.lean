import Lax53Proofs.PrimitiveRecursiveCode
import Mathlib.Tactic.Linarith

/-!
Coarse, computable resource envelopes for the structural execution bridge.

An envelope is indexed by an upper bound on the input, not its exact value.
Primitive recursion iterates a growing envelope, so every earlier accumulator
and step budget remains bounded by the final envelope. This deliberately
trades efficiency for a single compositional proof. No maximum over an
unbounded or non-effectively presented set is used.
-/

namespace Lax53Proofs.PrimitiveRecursiveBounds

open Lax53Proofs.PrimitiveRecursiveCode

def pairCap (a b : Nat) : Nat := (a + b + 1) * (a + b + 1)

theorem pair_lt_cap (a b : Nat) : Nat.pair a b < pairCap a b := by
  unfold Nat.pair pairCap
  split <;> nlinarith

theorem pairCap_mono {a b A B : Nat} (ha : a ≤ A) (hb : b ≤ B) :
    pairCap a b ≤ pairCap A B := by
  unfold pairCap
  exact Nat.mul_self_le_mul_self (by omega)

theorem pair_le_cap {a b A B : Nat} (ha : a ≤ A) (hb : b ≤ B) :
    Nat.pair a b ≤ pairCap A B :=
  (pair_lt_cap a b).le.trans (pairCap_mono ha hb)

def recInputCap (N v : Nat) : Nat := pairCap N (pairCap N v)

def recGrow (stepBound : Nat → Nat) (N v : Nat) : Nat :=
  v + stepBound (recInputCap N v) + recInputCap N v + 100

def recCeiling (initialBound stepBound : Nat → Nat) (N k : Nat) : Nat :=
  (recGrow stepBound N)^[k] (initialBound N + N + 100)

@[simp] theorem recCeiling_zero (bi bs : Nat → Nat) (N : Nat) :
    recCeiling bi bs N 0 = bi N + N + 100 := rfl

@[simp] theorem recCeiling_succ (bi bs : Nat → Nat) (N k : Nat) :
    recCeiling bi bs N (k + 1) = recGrow bs N (recCeiling bi bs N k) := by
  simp [recCeiling, Function.iterate_succ_apply']

theorem recCeiling_mono (bi bs : Nat → Nat) (N : Nat) :
    Monotone (recCeiling bi bs N) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [recCeiling_succ]
  unfold recGrow
  omega

/-- One envelope pays for both instruction count and intermediate values.
Its adequacy for machine execution is proved alongside compiler correctness. -/
def budget : Code → Nat → Nat
  | .zero, N => 100 * (N + 1)
  | .succ, N => 100 * (N + 1)
  | .left, N => 100 * (N + 1)
  | .right, N => 100 * (N + 1)
  | .pair f g, N => budget f N + budget g N + pairCap (budget f N) (budget g N) + 100
  | .comp f g, N => budget g N + budget f (budget g N) + 100
  | .prec initial step, N =>
      200 * (N + 1) * (recCeiling (budget initial) (budget step) N N + 1)

theorem pairCap_prim : Primrec₂ pairCap := by
  unfold pairCap
  have h : Primrec (fun x : Nat × Nat => x.1 + x.2 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd) (Primrec.const 1)
  exact Primrec.nat_mul.comp h h

theorem recInputCap_prim : Primrec₂ recInputCap :=
  pairCap_prim.comp Primrec.fst (pairCap_prim.comp Primrec.fst Primrec.snd)

theorem recGrow_prim {bs : Nat → Nat} (hbs : Primrec bs) : Primrec₂ (recGrow bs) := by
  unfold recGrow
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd (hbs.comp recInputCap_prim))
      recInputCap_prim) (Primrec.const 100)

theorem recCeiling_diag_prim {bi bs : Nat → Nat} (hbi : Primrec bi) (hbs : Primrec bs) :
    Primrec (fun N => recCeiling bi bs N N) :=
  Primrec.nat_iterate Primrec.id
    (Primrec.nat_add.comp (Primrec.nat_add.comp hbi Primrec.id) (Primrec.const 100))
    (recGrow_prim hbs)

theorem budget_prim (c : Code) : Primrec (budget c) := by
  induction c with
  | zero => exact Primrec.nat_mul.comp (Primrec.const 100) (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  | succ => exact Primrec.nat_mul.comp (Primrec.const 100) (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  | left => exact Primrec.nat_mul.comp (Primrec.const 100) (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  | right => exact Primrec.nat_mul.comp (Primrec.const 100) (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  | pair f g hf hg =>
      exact Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.nat_add.comp hf hg) (pairCap_prim.comp hf hg))
        (Primrec.const 100)
  | comp f g hf hg =>
      exact Primrec.nat_add.comp (Primrec.nat_add.comp hg (hf.comp hg)) (Primrec.const 100)
  | prec initial step hi hs =>
      exact Primrec.nat_mul.comp
        (Primrec.nat_mul.comp (Primrec.const 200) (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))
        (Primrec.nat_add.comp (recCeiling_diag_prim hi hs) (Primrec.const 1))

theorem input_le_budget (c : Code) (N : Nat) : N ≤ budget c N := by
  induction c generalizing N with
  | zero => simp [budget]; omega
  | succ => simp [budget]; omega
  | left => simp [budget]; omega
  | right => simp [budget]; omega
  | pair f g hf hg =>
      have := hf N
      simp only [budget]
      omega
  | comp f g hf hg =>
      have := hg N
      simp only [budget]
      omega
  | prec initial step hi hs =>
      have h := recCeiling_mono (budget initial) (budget step) N (Nat.zero_le N)
      rw [recCeiling_zero] at h
      simp only [budget]
      nlinarith

/-- The envelope bounds results uniformly over all inputs up to `N`.
The stronger machine theorem must additionally account for execution cost
and every temporary register value. -/
theorem eval_le_budget (c : Code) (N n : Nat) (hn : n ≤ N) :
    c.eval n ≤ budget c N := by
  induction c generalizing N n with
  | zero => simp [Code.eval, budget]
  | succ => simp only [Code.eval, budget]; omega
  | left =>
      have := Nat.unpair_left_le n
      simp only [Code.eval, budget]
      omega
  | right =>
      have := Nat.unpair_right_le n
      simp only [Code.eval, budget]
      omega
  | pair f g hf hg =>
      have hpair := pair_le_cap (hf N n hn) (hg N n hn)
      simp only [Code.eval, budget]
      omega
  | comp f g hf hg =>
      have hout := hf (budget g N) (g.eval n) (hg N n hn)
      simp only [Code.eval, budget]
      omega
  | prec initial step hi hs =>
      have hz : n.unpair.1 ≤ N := (Nat.unpair_left_le n).trans hn
      have hk : n.unpair.2 ≤ N := (Nat.unpair_right_le n).trans hn
      let acc : Nat → Nat := Nat.rec (initial.eval n.unpair.1)
        (fun k v => step.eval (Nat.pair n.unpair.1 (Nat.pair k v)))
      have hacc : ∀ k, k ≤ N → acc k ≤ recCeiling (budget initial) (budget step) N k := by
        intro k
        induction k with
        | zero =>
            intro _
            have hinit := hi N n.unpair.1 hz
            simp only [acc, Nat.rec_zero, recCeiling_zero]
            omega
        | succ k ih =>
            intro hkN
            have hv := ih (by omega)
            have hin : Nat.pair n.unpair.1 (Nat.pair k (acc k)) ≤
                recInputCap N (recCeiling (budget initial) (budget step) N k) :=
              pair_le_cap hz (pair_le_cap (by omega) hv)
            have hout := hs _ _ hin
            change step.eval (Nat.pair n.unpair.1 (Nat.pair k (acc k))) ≤ _
            rw [recCeiling_succ]
            unfold recGrow
            omega
      have hresult := (hacc n.unpair.2 hk).trans
        (recCeiling_mono (budget initial) (budget step) N hk)
      change acc n.unpair.2 ≤ 200 * (N + 1) *
        (recCeiling (budget initial) (budget step) N N + 1)
      nlinarith

end Lax53Proofs.PrimitiveRecursiveBounds
