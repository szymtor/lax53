import Lax53Proofs.PrimitiveRecursiveCode
import Lax53Proofs.PrimitiveRecursivePairing

/-!
Structural compilation of the seven primitive-recursive constructors into
ordinary IMP+. A call at offset `d` takes its input and returns its output
in register `d`; it may use only registers at or above `d` as scratch space.
The compiler generates finite command syntax, not function-valued machine
instructions. Correctness and computable resource bounds are separate proof
obligations; the pure source evaluator is never executed for free.
-/

namespace Lax53Proofs.PrimitiveRecursiveCompile

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax53Proofs.PrimitiveRecursiveCode Lax53Proofs.PrimitiveRecursivePairing

/-- An injective, proof-private naming convention for compiler registers. -/
def reg (n : Nat) : String := String.ofList (List.replicate n 'r')

theorem reg_injective : Function.Injective reg := by
  intro i j h
  have := congrArg (fun s : String => s.toList.length) h
  simpa [reg] using this

@[simp] theorem reg_eq_iff (i j : Nat) : reg i = reg j ↔ i = j := reg_injective.eq_iff

def copy (dst src : Nat) : Com := .assign (reg dst) (.var (reg src))

/-- One primitive-recursion iteration. The first four registers above `d`
hold the parameter, recursion bound, counter, and accumulator respectively.
The step call starts above all four, so their values survive that call. -/
def recursionStep (step : Com) (d : Nat) : Com :=
  .seq (pairProgram (reg (d + 3)) (reg (d + 4)) (reg (d + 5)))
    (.seq (pairProgram (reg (d + 1)) (reg (d + 5)) (reg (d + 5)))
      (.seq step
        (.seq (copy (d + 4) (d + 5))
          (.assign (reg (d + 3)) (.add (.var (reg (d + 3))) (.lit 1))))))

def compile : Code → Nat → Com
  | .zero, d => .assign (reg d) (.lit 0)
  | .succ, d => .assign (reg d) (.add (.var (reg d)) (.lit 1))
  | .left, d => unpairLeftProgram (reg d) (reg (d + 1)) (reg (d + 2))
  | .right, d => unpairRightProgram (reg d) (reg (d + 1)) (reg (d + 2))
  | .pair f g, d =>
      .seq (copy (d + 1) d)
        (.seq (compile f (d + 1))
          (.seq (copy (d + 2) d)
            (.seq (compile g (d + 2))
              (pairProgram (reg (d + 1)) (reg (d + 2)) (reg d)))))
  | .comp f g, d => .seq (compile g d) (compile f d)
  | .prec initial step, d =>
      .seq (copy (d + 1) d)
        (.seq (unpairLeftProgram (reg (d + 1)) (reg (d + 2)) (reg (d + 3)))
          (.seq (copy (d + 2) d)
            (.seq (unpairRightProgram (reg (d + 2)) (reg (d + 3)) (reg (d + 4)))
              (.seq (.assign (reg (d + 3)) (.lit 0))
                (.seq (copy (d + 4) (d + 1))
                  (.seq (compile initial (d + 4))
                    (.seq (.while (.lt (.var (reg (d + 3))) (.var (reg (d + 2))))
                      (recursionStep (compile step (d + 5)) d))
                      (copy d (d + 4)))))))))

/-- Syntactic freshness, proved once for all generated programs. -/
theorem compile_below (c : Code) (d j : Nat) (hj : j < d) :
    reg j ∉ (compile c d).wvars := by
  induction c generalizing d with
  | zero => simp [compile, Com.wvars]; omega
  | succ => simp [compile, Com.wvars]; omega
  | left =>
      simp [compile, unpairLeftProgram, sqrtProgram, sqrtLoop, sqrtStep, Com.wvars]
      omega
  | right =>
      simp [compile, unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep, Com.wvars]
      omega
  | pair f g hf hg =>
      have hf' := hf (d + 1) (by omega)
      have hg' := hg (d + 2) (by omega)
      simp [compile, copy, pairProgram, Com.wvars, hf', hg']
      omega
  | comp f g hf hg =>
      simpa only [compile, Com.wvars, List.mem_append, not_or] using ⟨hg d hj, hf d hj⟩
  | prec initial step hi hs =>
      have hi' := hi (d + 4) (by omega)
      have hs' := hs (d + 5) (by omega)
      simp [compile, copy, recursionStep, pairProgram, unpairLeftProgram,
        unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep, Com.wvars, hi', hs']
      omega

theorem compile_frame {B K : Nat} {c : Code} {d : Nat} {σ σ' : Env}
    (h : Run B (compile c d) σ σ' K) (j : Nat) (hj : j < d) :
    σ'.vars (reg j) = σ.vars (reg j) := h.frame_var _ (compile_below c d j hj)

theorem compile_warrs (c : Code) (d : Nat) : (compile c d).warrs = [] := by
  induction c generalizing d <;>
    simp_all [compile, copy, recursionStep, pairProgram, unpairLeftProgram,
      unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep, Com.warrs]

theorem compile_not_reads (c : Code) (d : Nat) : ¬ (compile c d).reads := by
  induction c generalizing d <;>
    simp_all [compile, copy, recursionStep, pairProgram, unpairLeftProgram,
      unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep, Com.reads]

theorem compile_noWrite (c : Code) (d : Nat) : (compile c d).NoWrite := by
  induction c generalizing d <;>
    simp_all [compile, copy, recursionStep, pairProgram, unpairLeftProgram,
      unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep, Com.NoWrite]

end Lax53Proofs.PrimitiveRecursiveCompile
