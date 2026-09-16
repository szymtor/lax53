import Lax842588Proofs.PrimitiveRecursiveRecursion
import Lax842588Proofs.PrimitiveRecursiveLayout
import Lax759944Proofs.Legacy.Transfer
import Mathlib.Computability.Partrec

/-!
Actual word-RAM realization of primitive-recursive functions, via the
verified bounded IMP+ compiler and the existing instruction-level simulation.

The one-word input/output convention here is proof-private. A caller using
the certified public arena must build and decode these intermediate words
at runtime and charge that work. This theorem does not change admissible
Lax-53 inputs or move pure Lean evaluation outside the measured execution.
-/

namespace Lax842588Proofs.PrimitiveRecursiveRam

open Lax759944Proofs.Legacy.Ram Lax759944Proofs.Legacy.RamComputes Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Reasoning
open Lax842588Proofs.PrimitiveRecursiveCode Lax842588Proofs.PrimitiveRecursiveCompile
open Lax842588Proofs.PrimitiveRecursiveBounds Lax842588Proofs.PrimitiveRecursiveCorrectness

def runner (c : Code) : Com :=
  .seq (.read (reg 0)) (.seq (compile c 0) (.write (.var (reg 0))))

def program (c : Code) : Program := Lax759944Proofs.Legacy.Compile.compileProgram (layout c) (runner c)

def timeBound (c : Code) (n : Nat) : Nat := 10 * (budget c n + 3)

def wordBound (c : Code) (n : Nat) : Nat := budget c n + space c + 10

theorem timeBound_prim (c : Code) : Primrec (timeBound c) :=
  Primrec.nat_mul.comp (Primrec.const 10)
    (Primrec.nat_add.comp (budget_prim c) (Primrec.const 3))

theorem wordBound_prim (c : Code) : Primrec (wordBound c) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (budget_prim c) (Primrec.const (space c)))
    (Primrec.const 10)

theorem runner_ok (c : Code) : Lax759944Proofs.Legacy.Compile.Com.Ok (layout c) (runner c) := by
  have hzero : reg 0 ∈ (layout c).scalars := by
    apply List.mem_map.mpr
    exact ⟨0, List.mem_range.mpr (by have := space_ge_three c; omega), rfl⟩
  have hc := layout_ok c
  simpa [runner, Lax759944Proofs.Legacy.Compile.Com.Ok, Lax759944Proofs.Legacy.Compile.Expr.Ok, layout] using
    (show reg 0 ∈ (layout c).scalars ∧
      Lax759944Proofs.Legacy.Compile.Com.Ok (layout c) (compile c 0) ∧
      reg 0 ∈ (layout c).scalars from ⟨hzero, hc, hzero⟩)

theorem runner_solves (c : Code) (n : Nat) :
    Lax759944Proofs.Legacy.Transfer.Solves (layout c) (runner c) {[n]}
      (fun _ => [c.eval n]) (fun _ => budget c n + 2) (fun _ => budget c n + 3) := by
  refine ⟨runner_ok c, ?_, ?_⟩
  · intro x hx v hv
    have hx' : x = [n] := hx
    subst x
    have hv' : v = n := by simpa using hv
    subst v
    have := input_le_budget c n
    omega
  · intro x hx
    have hx' : x = [n] := hx
    subst x
    let σ := initEnv (fun _ => 0) [n]
    let σ₁ : Env := { σ.setVar (reg 0) n with inp := [] }
    have hread : Run (budget c n + 2) (.read (reg 0)) σ σ₁ 1 := Run.read rfl
    obtain ⟨τ, hcall, hout⟩ := compile_correct c 0 (budget c n + 2) n n le_rfl
      (by omega) σ₁ (by simp [σ₁])
    have hval : c.eval n < budget c n + 2 := by have := eval_le_budget c n n le_rfl; omega
    have hwrite : Run (budget c n + 2) (.write (.var (reg 0))) τ
        {τ with out := τ.out ++ [c.eval n]} 2 :=
      Run.write (by simp [Expr.evalB, hout, fit_self hval])
    have hnil : τ.out = [] := by
      rw [hcall.out_eq (compile_noWrite c 0)]
      rfl
    refine ⟨(fun _ => 0), {τ with out := τ.out ++ [c.eval n]}, ?_, by simp [hnil]⟩
    exact (hread.seq (hcall.seq hwrite)).mono (by omega)

theorem code_computes (c : Code) (n w : Nat) (hfit : wordBound c n ≤ 2 ^ w) :
    ComputesInTime w (program c) {[n]} (fun _ => [c.eval n]) (fun _ => timeBound c n) := by
  apply Lax759944Proofs.Legacy.Transfer.computesInTime_of_solves (runner_solves c n)
  · intro _ _
    refine ⟨by omega, ?_, ?_⟩
    · unfold wordBound at hfit
      omega
    · rw [layout_span]
      unfold wordBound at hfit
      omega
  · intro _ _
    exact le_rfl

/-- One fixed RAM program realizes a primitive-recursive function at every
sufficient word width, with primitive-recursive (hence computable) resources. -/
theorem exists_ram {f : Nat → Nat} (hf : Nat.Primrec f) :
    ∃ (p : Program) (time words : Nat → Nat), Primrec time ∧ Primrec words ∧
      ∀ n w, words n ≤ 2 ^ w →
        ComputesInTime w p {[n]} (fun _ => [f n]) (fun _ => time n) := by
  obtain ⟨c, hc⟩ := exists_code hf
  refine ⟨program c, timeBound c, wordBound c, timeBound_prim c, wordBound_prim c, ?_⟩
  intro n w hw
  simpa only [congrFun hc n] using code_computes c n w hw

/-- Typed realization preserves Mathlib's exact tagged output convention;
the scalar input is still internal data, not an alternative certified arena. -/
theorem exists_typed_ram {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} (hf : Primrec f) :
    ∃ (p : Program) (time words : Nat → Nat), Primrec time ∧ Primrec words ∧
      ∀ (a : α) w, words (Encodable.encode a) ≤ 2 ^ w →
        ComputesInTime w p {[Encodable.encode a]}
          (fun _ => [Encodable.encode (some (f a))])
          (fun _ => time (Encodable.encode a)) := by
  obtain ⟨c, hc⟩ := exists_typed_code hf
  refine ⟨program c, timeBound c, wordBound c, timeBound_prim c, wordBound_prim c, ?_⟩
  intro a w hw
  simpa only [typed_code_on_value hc a] using code_computes c (Encodable.encode a) w hw

end Lax842588Proofs.PrimitiveRecursiveRam
