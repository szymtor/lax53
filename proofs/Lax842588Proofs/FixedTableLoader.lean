import Lax842588Proofs.CompilerArrayUnpacking

/-!
A fixed-sentence program may contain a fixed automaton in its instructions.
This loader materializes that constant into initially empty workspace during
the counted run. It adds no input tape and assumes no initialized table.
-/

namespace Lax842588Proofs.FixedTableLoader

open Encodable Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Reasoning

def program (xs : List Nat) : Com :=
  .seq (.assign "unpackCode" (.lit (encode xs))) (CompilerArrayUnpacking.program "P")

def timeBound (xs : List Nat) : Nat := 2 + 170 * (encode xs + 1) * (xs.length + 1)

theorem program_spec (B : Nat) (xs : List Nat) (hB : 2 * encode xs + 3 < B) :
    Spec B (fun σ => (σ.arrs "P").length = xs.length) (program xs)
      (fun _ σ => σ.arrs "P" = xs) (timeBound xs) := by
  intro σ hσ
  have hset : Run B (.assign "unpackCode" (.lit (encode xs))) σ
      (σ.setVar "unpackCode" (encode xs)) 2 :=
    Run.assign (by simp [Expr.evalB, fit_self (show encode xs < B by omega)])
  obtain ⟨τ, hu, hp, _⟩ := CompilerArrayUnpacking.program_spec B "P" xs hB
    (σ.setVar "unpackCode" (encode xs)) (by simp [hσ])
  have hlen : (τ.arrs "P").length = xs.length := by
    rw [Lax842588Proofs.Run.arrayLength_eq hu "P"]
    exact hσ
  exact ⟨τ, hset.seq hu, by simpa [← hlen] using hp⟩

theorem program_noRead (xs : List Nat) : ¬ (program xs).reads := by
  simp [program, Com.reads, CompilerArrayUnpacking.program_noRead]

theorem program_noWrite (xs : List Nat) : (program xs).NoWrite := by
  simp [program, Com.NoWrite, CompilerArrayUnpacking.program_noWrite]

theorem program_warrs (xs : List Nat) : (program xs).warrs = ["P"] := by
  simp [program, Com.warrs, CompilerArrayUnpacking.program_warrs]

end Lax842588Proofs.FixedTableLoader
