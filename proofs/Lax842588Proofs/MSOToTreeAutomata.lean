import Lax842588Proofs.EmptyMarkers

namespace Lax842588Proofs.MSOToTreeAutomata

open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588.TreeStructure
open Lax842588Proofs.MarkedTrees
open Lax842588Proofs.EmptyMarkers

universe u

/--
---
conclusion: Lax842588.MSOTreeAutomataEquivalence.mso_definable_is_recognizable
---
-/
theorem mso_definable_is_recognizable_proof {A : RankedAlphabet.{u}}
    (phi : Lax146103.MSOSyntax.Sentence (treeSignature A)) :
    Recognizable (sentenceLanguage phi) := by
  rcases Lax842588Proofs.MSOFormulaToTreeAutomata.formulaLanguage_recognizable phi with
    ⟨Q, hQ, M, hM⟩
  letI := hQ
  refine ⟨Q, inferInstance, unmarkAutomaton M, ?_⟩
  ext t
  change (unmarkAutomaton M).Accepts t ↔ TreeModels t phi
  rw [unmarkAutomaton_accepts_iff]
  change emptyMark t ∈ M.language ↔ TreeModels t phi
  rw [hM]
  exact emptyMark_mem_formulaLanguage_iff t phi

end Lax842588Proofs.MSOToTreeAutomata
