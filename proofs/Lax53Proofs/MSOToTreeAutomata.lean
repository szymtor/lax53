import Lax53Proofs.EmptyMarkers

namespace Lax53Proofs.MSOToTreeAutomata

open Lax53.RankedTree
open Lax53.TreeAutomaton
open Lax53.TreeStructure
open Lax53Proofs.MarkedTrees
open Lax53Proofs.EmptyMarkers

universe u

/--
---
conclusion: Lax53.MSOTreeAutomataEquivalence.mso_definable_is_recognizable
---
-/
theorem mso_definable_is_recognizable_proof {A : RankedAlphabet.{u}}
    (phi : Lax52.MSOSyntax.Sentence (treeSignature A)) :
    Recognizable (sentenceLanguage phi) := by
  rcases Lax53Proofs.MSOFormulaToTreeAutomata.formulaLanguage_recognizable phi with
    ⟨Q, hQ, M, hM⟩
  letI := hQ
  refine ⟨Q, inferInstance, unmarkAutomaton M, ?_⟩
  ext t
  change (unmarkAutomaton M).Accepts t ↔ TreeModels t phi
  rw [unmarkAutomaton_accepts_iff]
  change emptyMark t ∈ M.language ↔ TreeModels t phi
  rw [hM]
  exact emptyMark_mem_formulaLanguage_iff t phi

end Lax53Proofs.MSOToTreeAutomata
