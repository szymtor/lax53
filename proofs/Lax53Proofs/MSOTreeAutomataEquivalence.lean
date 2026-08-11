import Lax53.MSOTreeAutomataEquivalence
import Lax53Proofs.TreeAutomataToMSO
import Lax53Proofs.MSOToTreeAutomata

namespace Lax53Proofs.MSOTreeAutomataEquivalence

open Lax53.RankedTree
open Lax53.TreeAutomaton
open Lax53.TreeStructure

universe u

/--
---
conclusion: Lax53.MSOTreeAutomataEquivalence.recognizable_iff_msoDefinable
---
-/
theorem recognizable_iff_msoDefinable_proof {A : RankedAlphabet.{u}}
    (L : TreeLanguage A) :
    Recognizable L ↔
      ∃ phi : Lax52.MSOSyntax.Sentence (treeSignature A),
        L = sentenceLanguage phi := by
  constructor
  · rintro ⟨Q, hQ, M, hM⟩
    letI := hQ
    obtain ⟨phi, hphi⟩ :=
      Lax53Proofs.TreeAutomataToMSO.automaton_definable_by_mso_proof M
    exact ⟨phi, hM.symm.trans hphi⟩
  · rintro ⟨phi, rfl⟩
    exact Lax53Proofs.MSOToTreeAutomata.mso_definable_is_recognizable_proof phi

end Lax53Proofs.MSOTreeAutomataEquivalence
