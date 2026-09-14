import Lax842588.MSOTreeAutomataEquivalence
import Lax842588Proofs.TreeAutomataToMSO
import Lax842588Proofs.MSOToTreeAutomata

namespace Lax842588Proofs.MSOTreeAutomataEquivalence

open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588.TreeStructure

universe u

/--
---
conclusion: Lax842588.MSOTreeAutomataEquivalence.recognizable_iff_msoDefinable
---
-/
theorem recognizable_iff_msoDefinable_proof {A : RankedAlphabet.{u}}
    (L : TreeLanguage A) :
    Recognizable L ↔
      ∃ phi : Lax146103.MSOSyntax.Sentence (treeSignature A),
        L = sentenceLanguage phi := by
  constructor
  · rintro ⟨Q, hQ, M, hM⟩
    letI := hQ
    obtain ⟨phi, hphi⟩ :=
      Lax842588Proofs.TreeAutomataToMSO.automaton_definable_by_mso_proof M
    exact ⟨phi, hM.symm.trans hphi⟩
  · rintro ⟨phi, rfl⟩
    exact Lax842588Proofs.MSOToTreeAutomata.mso_definable_is_recognizable_proof phi

end Lax842588Proofs.MSOTreeAutomataEquivalence
