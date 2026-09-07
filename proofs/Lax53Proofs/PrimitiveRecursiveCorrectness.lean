import Lax53Proofs.PrimitiveRecursiveCompile
import Lax53Proofs.PrimitiveRecursiveBounds

/-!
Compositional bounded-execution correctness for the primitive-recursive
compiler. `Correct` includes the instruction bound and every intermediate
word-fit obligation, not just equality with the pure evaluator.
-/

namespace Lax53Proofs.PrimitiveRecursiveCorrectness

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax53Proofs.PrimitiveRecursiveCode Lax53Proofs.PrimitiveRecursivePairing
open Lax53Proofs.PrimitiveRecursiveCompile Lax53Proofs.PrimitiveRecursiveBounds

def Correct (c : Code) : Prop :=
  ∀ (d B N n : Nat), n ≤ N → budget c N < B →
    Spec B (fun σ => σ.vars (reg d) = n) (compile c d)
      (fun _ σ => σ.vars (reg d) = c.eval n) (budget c N)

theorem correct_zero : Correct .zero := by
  intro d B N n hn hB σ hx
  simp only [budget] at hB
  simp only [compile, Code.eval, budget]
  run_vcg
  all_goals simp

theorem correct_succ : Correct .succ := by
  intro d B N n hn hB σ hx
  simp only [budget] at hB
  simp only [compile, Code.eval, budget]
  run_vcg
  all_goals simp_all
  all_goals omega

theorem correct_left : Correct .left := by
  intro d B N n hn hB
  simp only [budget] at hB
  exact (unpairLeft_spec B n (reg d) (reg (d + 1)) (reg (d + 2))
    (by simp) (by omega)).mono (by simp [budget]; omega)

theorem correct_right : Correct .right := by
  intro d B N n hn hB
  simp only [budget] at hB
  exact (unpairRight_spec B n (reg d) (reg (d + 1)) (reg (d + 2))
    (by simp) (by omega)).mono (by simp [budget]; omega)

theorem correct_comp {f g : Code} (hf : Correct f) (hg : Correct g) :
    Correct (.comp f g) := by
  intro d B N n hn hB σ hx
  simp only [budget] at hB
  obtain ⟨τ, hgrun, hgout⟩ := hg d B N n hn (by omega) σ hx
  obtain ⟨τ', hfrun, hfout⟩ :=
    hf d B (budget g N) (g.eval n) (eval_le_budget g N n hn) (by omega) τ hgout
  exact ⟨τ', (hgrun.seq hfrun).mono (by simp [budget]), hfout⟩

theorem copy_run (B dst src n : Nat) (σ : Env) (hx : σ.vars (reg src) = n)
    (hnB : n < B) : Run B (copy dst src) σ (σ.setVar (reg dst) n) 2 := by
  apply Run.assign
  simp [Expr.evalB, hx, fit_self hnB]

theorem correct_pair {f g : Code} (hf : Correct f) (hg : Correct g) :
    Correct (.pair f g) := by
  intro d B N n hn hB σ hx
  have hfval := eval_le_budget f N n hn
  have hgval := eval_le_budget g N n hn
  have hpB : (f.eval n + g.eval n + 1) ^ 2 < B := by
    have hcap := pairCap_mono hfval hgval
    simp only [budget] at hB
    simpa only [pairCap, Nat.pow_two] using hcap.trans_lt (by omega)
  have hnB : n < B := by
    -- The input copy needs its own bound; it is not implied by an output bound.
    have : N ≤ budget f N := by
      -- This general envelope property is proved in the bounds module.
      exact input_le_budget f N
    simp only [budget] at hB
    omega
  have hcopy₁ := copy_run B (d + 1) d n σ hx hnB
  obtain ⟨τ, hfrun, hfout⟩ := hf (d + 1) B N n hn
    (by simp only [budget] at hB; omega) (σ.setVar (reg (d + 1)) n) (by simp)
  have hkeep : τ.vars (reg d) = n := by
    rw [compile_frame hfrun d (by omega)]
    simpa using hx
  have hcopy₂ := copy_run B (d + 2) d n τ hkeep hnB
  obtain ⟨υ, hgrun, hgout⟩ := hg (d + 2) B N n hn
    (by simp only [budget] at hB; omega) (τ.setVar (reg (d + 2)) n) (by simp)
  have hfkeep : υ.vars (reg (d + 1)) = f.eval n := by
    rw [compile_frame hgrun (d + 1) (by omega)]
    simpa using hfout
  obtain ⟨ω, hprun, hpout⟩ :=
    pair_spec B (f.eval n) (g.eval n) (reg (d + 1)) (reg (d + 2)) (reg d) hpB
      υ ⟨hfkeep, hgout⟩
  refine ⟨ω, ?_, hpout⟩
  exact (hcopy₁.seq (hfrun.seq (hcopy₂.seq (hgrun.seq hprun)))).mono
    (by simp [budget]; omega)

end Lax53Proofs.PrimitiveRecursiveCorrectness
