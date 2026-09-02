import Lax53.MSOLinearTime
import Lax53Proofs.AutomatonLinearTime
import Lax53Proofs.EncodedFormulaCompiler

namespace Lax53Proofs.MSOLinearTime

open Classical

open Lax13.Ram
open Lax53.RankedTree
open Lax53.EffectiveTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.EncodedFormulaCompiler

/-- The value-level automaton body produced from a raw MSO sentence. -/
def compileMSO (phi : EncodedSentence) : AutomatonCode :=
  (compileSentence phi).2

def compiledCoefficient (constant : Nat) (phi : EncodedSentence) : Nat :=
  constant * ((encodeAutomaton (phi.1, compileMSO phi)).length + 1) ^ 2

noncomputable def evaluatorProgram : Program :=
  Classical.choose
    Lax53Proofs.AutomatonLinearTime.exists_uniform_linearTime_automatonAcceptance

noncomputable def evaluatorConstant : Nat :=
  Classical.choose (Classical.choose_spec
    Lax53Proofs.AutomatonLinearTime.exists_uniform_linearTime_automatonAcceptance)

private noncomputable def evaluatorBound :=
  Classical.choose_spec (Classical.choose_spec
    Lax53Proofs.AutomatonLinearTime.exists_uniform_linearTime_automatonAcceptance)

/--
---
conclusion: Lax53.MSOLinearTime.exists_uniform_linearTime_msoModelChecking
---
The sentence is translated before the measured word-RAM execution. The
automaton theorem then supplies the single evaluator and its linear bound in
the runtime tree size.
-/
theorem exists_uniform_linearTime_msoModelChecking :
    ∃ (compiler : EncodedSentence → AutomatonCode) (program : Program)
        (coefficient : EncodedSentence → Nat),
      (∀ phi,
        AutomatonCode.language phi.1 (compiler phi) =
          FormulaCode.language phi.1 phi.2) ∧
      ∀ (phi : EncodedSentence) (t : Tree phi.1.toRankedAlphabet) (w : Nat),
        let M : EncodedAutomaton := (phi.1, compiler phi)
        let c := coefficient phi
        let input := automatonInput M t
        (∀ v ∈ input, c * (input.length + v + 1) ≤ 2 ^ w) →
          ∃ time ≤ c * treeSize t,
            RunsTo w program input
              (if t ∈ FormulaCode.language phi.1 phi.2 then [1] else [0])
              time := by
  classical
  refine ⟨compileMSO, evaluatorProgram, compiledCoefficient evaluatorConstant, ?_, ?_⟩
  · intro phi
    exact compileSentence_language phi
  · intro phi t w
    dsimp only [compiledCoefficient]
    intro hword
    obtain ⟨time, htime, hrun⟩ :=
      evaluatorBound (phi.1, compileMSO phi) t w hword
    refine ⟨time, htime, ?_⟩
    have hsem : ((compileMSO phi).toAutomaton phi.1).Accepts t ↔
        t ∈ FormulaCode.language phi.1 phi.2 := by
      change t ∈ AutomatonCode.language phi.1 (compileMSO phi) ↔
        t ∈ FormulaCode.language phi.1 phi.2
      exact Set.ext_iff.mp (compileSentence_language phi) t
    have hout :
        (if ((compileMSO phi).toAutomaton phi.1).Accepts t then [1] else [0]) =
          (if t ∈ FormulaCode.language phi.1 phi.2 then [1] else [0]) := by
      by_cases h : ((compileMSO phi).toAutomaton phi.1).Accepts t
      · simp [h, hsem.mp h]
      · have hn : t ∉ FormulaCode.language phi.1 phi.2 := by
          intro ht
          exact h (hsem.mpr ht)
        simp [h, hn]
    rw [← hout]
    exact hrun

end Lax53Proofs.MSOLinearTime
