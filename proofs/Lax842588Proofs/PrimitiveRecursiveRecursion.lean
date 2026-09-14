import Lax842588Proofs.PrimitiveRecursiveCorrectness

/-!
The primitive-recursion case of the verified execution bridge. The loop
keeps the parameter and bound below the step call's scratch registers and
uses a growing, primitive-recursive ceiling to bound every accumulator,
pairing intermediate, and recursive step cost.
-/

namespace Lax842588Proofs.PrimitiveRecursiveCorrectness

open Lax865980Proofs.Imp Lax865980Proofs.Reasoning
open Lax842588Proofs.PrimitiveRecursiveCode Lax842588Proofs.PrimitiveRecursivePairing
open Lax842588Proofs.PrimitiveRecursiveCompile Lax842588Proofs.PrimitiveRecursiveBounds

def recAcc (initial step : Code) (z : Nat) : Nat → Nat :=
  Nat.rec (initial.eval z) (fun k v => step.eval (Nat.pair z (Nat.pair k v)))

def RecInv (initial step : Code) (d z m N : Nat) (σ : Env) : Prop :=
  σ.vars (reg (d + 1)) = z ∧ σ.vars (reg (d + 2)) = m ∧
  σ.vars (reg (d + 3)) ≤ m ∧
  σ.vars (reg (d + 4)) = recAcc initial step z (σ.vars (reg (d + 3))) ∧
  σ.vars (reg (d + 4)) ≤
    recCeiling (budget initial) (budget step) N (σ.vars (reg (d + 3)))

theorem pair_vars {B K : Nat} {σ σ' : Env} {x y out j : String}
    (h : Run B (pairProgram x y out) σ σ' K) (hj : j ≠ out) :
    σ'.vars j = σ.vars j := h.frame_var j (by simp [pairProgram, Com.wvars, hj])

theorem recursionStep_spec (initial step : Code) (hstep : Correct step)
    (d B N z m : Nat) (hzN : z ≤ N) (hmN : m ≤ N)
    (hB : budget (.prec initial step) N < B) :
    Spec B (fun σ => RecInv initial step d z m N σ ∧ σ.vars (reg (d + 3)) < m)
      (recursionStep (compile step (d + 5)) d)
      (fun σ σ' => RecInv initial step d z m N σ' ∧
        σ'.vars (reg (d + 3)) = σ.vars (reg (d + 3)) + 1)
      (recCeiling (budget initial) (budget step) N N + 50) := by
  intro σ hσ
  obtain ⟨⟨hz, hm, hk, ha, hav⟩, hklt⟩ := hσ
  let k := σ.vars (reg (d + 3))
  let a := σ.vars (reg (d + 4))
  let R := recCeiling (budget initial) (budget step) N k
  let P := recInputCap N R
  let v := Nat.pair z (Nat.pair k a)
  let T := recCeiling (budget initial) (budget step) N N
  have hkN : k + 1 ≤ N := by dsimp [k]; omega
  have hnext : recCeiling (budget initial) (budget step) N (k + 1) ≤ T :=
    recCeiling_mono _ _ N hkN
  have hR : R + budget step P + P + 100 ≤ T := by
    simpa [recCeiling_succ, recGrow, R, P] using hnext
  have hTB : T < B := by
    change 200 * (N + 1) * (T + 1) < B at hB
    nlinarith
  have hP : v ≤ P := pair_le_cap hzN (pair_le_cap (by omega) hav)
  have hcap₁ : pairCap k a ≤ P := by
    have h₁ := pairCap_mono (show k ≤ N by omega) hav
    have h₂ : pairCap N R ≤ pairCap N (pairCap N R) := by
      unfold pairCap
      nlinarith
    exact h₁.trans h₂
  have hcap₂ : pairCap z (Nat.pair k a) ≤ P :=
    pairCap_mono hzN (pair_le_cap (by omega) hav)
  obtain ⟨τ, hpair₁, hp₁⟩ :=
    pair_spec B k a (reg (d + 3)) (reg (d + 4)) (reg (d + 5))
      (by simpa [Nat.pow_two, pairCap] using (show pairCap k a < B by omega)) σ ⟨rfl, rfl⟩
  have hτz : τ.vars (reg (d + 1)) = z := by
    rw [pair_vars hpair₁ (by simp)]; exact hz
  obtain ⟨υ, hpair₂, hp₂⟩ :=
    pair_spec B z (Nat.pair k a) (reg (d + 1)) (reg (d + 5)) (reg (d + 5))
      (by simpa [Nat.pow_two, pairCap] using
        (show pairCap z (Nat.pair k a) < B by omega)) τ ⟨hτz, hp₁⟩
  obtain ⟨ω, hcall, hresult⟩ := hstep (d + 5) B P v hP (by omega) υ hp₂
  have hkeep (j : Nat) (hj : j < d + 5) : ω.vars (reg j) = σ.vars (reg j) := by
    rw [compile_frame hcall j hj, pair_vars hpair₂ (by simp; omega),
      pair_vars hpair₁ (by simp; omega)]
  have hout := eval_le_budget step P v hP
  have houtB : step.eval v < B := by omega
  have hcopy := copy_run B (d + 4) (d + 5) (step.eval v) ω hresult houtB
  let ω' := ω.setVar (reg (d + 4)) (step.eval v)
  have hkω : ω'.vars (reg (d + 3)) = k := by
    simpa [ω', k] using hkeep (d + 3) (by omega)
  have hinc : Run B (.assign (reg (d + 3)) (.add (.var (reg (d + 3))) (.lit 1)))
      ω' (ω'.setVar (reg (d + 3)) (k + 1)) 4 := by
    apply Run.assign
    have hNB : N < B := (input_le_budget (.prec initial step) N).trans_lt hB
    simp [Expr.evalB, hkω, Bop.apply, fit_self (show k < B by omega),
      fit_self (show 1 < B by omega), fit_self (show k + 1 < B by omega)]
  refine ⟨ω'.setVar (reg (d + 3)) (k + 1), ?_, ?_⟩
  · exact (hpair₁.seq (hpair₂.seq (hcall.seq (hcopy.seq hinc)))).mono (by omega)
  · have hωz := hkeep (d + 1) (by omega)
    have hωm := hkeep (d + 2) (by omega)
    have hav' : step.eval v ≤ recCeiling (budget initial) (budget step) N (k + 1) := by
      rw [recCeiling_succ]
      change step.eval v ≤ R + budget step P + P + 100
      omega
    have hvalue : step.eval v = recAcc initial step z (k + 1) := by
      simp only [recAcc]
      change step.eval v = step.eval (Nat.pair z (Nat.pair k (recAcc initial step z k)))
      rw [← ha]
    have hbound : recAcc initial step z (k + 1) ≤
        recCeiling (budget initial) (budget step) N (k + 1) := hvalue ▸ hav'
    simp [RecInv, ω', hωz, hωm, hz, hm, hklt, k, hvalue]
    simpa [k] using hbound

theorem recursionLoop_spec (initial step : Code) (hstep : Correct step)
    (d B N z m : Nat) (hzN : z ≤ N) (hmN : m ≤ N)
    (hB : budget (.prec initial step) N < B) :
    Spec B (RecInv initial step d z m N)
      (.while (.lt (.var (reg (d + 3))) (.var (reg (d + 2))))
        (recursionStep (compile step (d + 5)) d))
      (fun _ σ => σ.vars (reg (d + 4)) = recAcc initial step z m)
      ((recCeiling (budget initial) (budget step) N N + 54) * m + 4) := by
  have hNB := (input_le_budget (.prec initial step) N).trans_lt hB
  have hloop := Spec.forRange (reg (d + 3)) (reg (d + 2))
    (RecInv initial step d z m N) m
    (recCeiling (budget initial) (budget step) N N + 50)
    ((recCeiling (budget initial) (budget step) N N + 54) * m + 4)
    (B := B) (P := RecInv initial step d z m N)
    (fun σ hI => by obtain ⟨_, _, hk, _⟩ := hI; omega)
    (fun σ hI => by obtain ⟨_, hm, _⟩ := hI; omega)
    (fun _ hI => hI.2.1) (fun _ hI => hI.2.2.1)
    (recursionStep_spec initial step hstep d B N z m hzN hmN hB)
    (fun _ hI => hI)
    (fun σ _ => by
      have := Nat.mul_le_mul_left
        (recCeiling (budget initial) (budget step) N N + 54)
        (Nat.sub_le m (σ.vars (reg (d + 3))))
      simpa [Nat.add_assoc] using Nat.add_le_add_right this 4)
  exact hloop.post fun _ _ _ hpost => by
    simpa only [hpost.2] using hpost.1.2.2.2.1

theorem correct_prec {initial step : Code} (hi : Correct initial) (hs : Correct step) :
    Correct (.prec initial step) := by
  intro d B N n hn hB σ hx
  let z := n.unpair.1
  let m := n.unpair.2
  let T := recCeiling (budget initial) (budget step) N N
  have hzN : z ≤ N := (Nat.unpair_left_le n).trans hn
  have hmN : m ≤ N := (Nat.unpair_right_le n).trans hn
  have hT : budget initial N + N + 100 ≤ T := by
    exact recCeiling_mono _ _ N (Nat.zero_le N)
  have hTB : T < B := by
    change 200 * (N + 1) * (T + 1) < B at hB
    nlinarith
  have hbase : 100 * (N + 1) < B := by
    change 200 * (N + 1) * (T + 1) < B at hB
    nlinarith
  have hnB : n < B := by omega
  have hzB : z < B := by omega
  have hcopy₁ := copy_run B (d + 1) d n σ hx hnB
  obtain ⟨τ, hleft, hz⟩ := correct_left (d + 1) B N n hn hbase
    (σ.setVar (reg (d + 1)) n) (by simp)
  have hnτ : τ.vars (reg d) = n := by
    rw [compile_frame hleft d (by omega)]; simpa using hx
  have hcopy₂ := copy_run B (d + 2) d n τ hnτ hnB
  obtain ⟨υ, hright, hm⟩ := correct_right (d + 2) B N n hn hbase
    (τ.setVar (reg (d + 2)) n) (by simp)
  have hzυ : υ.vars (reg (d + 1)) = z := by
    rw [compile_frame hright (d + 1) (by omega)]; simpa [z, Code.eval] using hz
  have hzero : Run B (.assign (reg (d + 3)) (.lit 0))
      υ (υ.setVar (reg (d + 3)) 0) 2 :=
    Run.assign (by simp [Expr.evalB, fit_self (show 0 < B by omega)])
  let υ' := υ.setVar (reg (d + 3)) 0
  have hzυ' : υ'.vars (reg (d + 1)) = z := by simpa [υ'] using hzυ
  have hcopy₃ := copy_run B (d + 4) (d + 1) z υ' hzυ' hzB
  obtain ⟨ω, hinit, ha⟩ := hi (d + 4) B N z hzN (by omega)
    (υ'.setVar (reg (d + 4)) z) (by simp)
  have hkeep (j : Nat) (hj : j < d + 4) : ω.vars (reg j) = υ'.vars (reg j) := by
    rw [compile_frame hinit j hj]; simp; omega
  have hzω : ω.vars (reg (d + 1)) = z := by
    rw [hkeep _ (by omega)]; exact hzυ'
  have hmω : ω.vars (reg (d + 2)) = m := by
    rw [hkeep _ (by omega)]; simpa [υ', m, Code.eval] using hm
  have hkω : ω.vars (reg (d + 3)) = 0 := by
    rw [hkeep _ (by omega)]; simp [υ']
  have hI : RecInv initial step d z m N ω := by
    have hval := eval_le_budget initial N z hzN
    simp [RecInv, hzω, hmω, hkω, ha, recAcc]
    omega
  obtain ⟨η, hloop, hout⟩ :=
    recursionLoop_spec initial step hs d B N z m hzN hmN hB ω hI
  have hvB : recAcc initial step z m < B :=
    (eval_le_budget (.prec initial step) N n hn).trans_lt hB
  have hcopy₄ := copy_run B d (d + 4) (recAcc initial step z m) η hout hvB
  refine ⟨η.setVar (reg d) (recAcc initial step z m), ?_, by simp [Code.eval, recAcc, z, m]⟩
  have hrun := hcopy₁.seq (hleft.seq (hcopy₂.seq (hright.seq (hzero.seq
    (hcopy₃.seq (hinit.seq (hloop.seq hcopy₄)))))))
  apply hrun.mono
  change 2 + (100 * (N + 1) + (2 + (100 * (N + 1) + (2 + (2 +
    (budget initial N + (((T + 54) * m + 4) + 2))))))) ≤
      200 * (N + 1) * (T + 1)
  have hmul := Nat.mul_le_mul_left (T + 54) hmN
  nlinarith

/-- Every finite primitive-recursive code has a bounded, charged execution
under the structurally generated program, uniformly over all offsets and
all inputs below the envelope parameter. -/
theorem compile_correct (c : Code) : Correct c := by
  induction c with
  | zero => exact correct_zero
  | succ => exact correct_succ
  | left => exact correct_left
  | right => exact correct_right
  | pair f g hf hg => exact correct_pair hf hg
  | comp f g hf hg => exact correct_comp hf hg
  | prec initial step hi hs => exact correct_prec hi hs

end Lax842588Proofs.PrimitiveRecursiveCorrectness
