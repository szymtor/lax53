import Lax53.ValueTranslations
import Lax53Proofs.TreeAutomataToMSO

/-!
The automaton-to-MSO half of the value-level result needs no separate raw
formula construction. We instantiate the already verified intrinsic
automaton formula directly at the concrete finite-state automaton denoted by
an `AutomatonCode`.
-/

namespace Lax53Proofs.TranslationConstructions

open Lax52.MSOSyntax
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.TreeAutomaton
open Lax53.ValueTranslations

namespace AutomatonToMSO

/-- Intrinsic automaton-to-MSO translation exposed by the value theorem. -/
noncomputable def compile (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    Sentence (treeSignature alphabet.toRankedAlphabet) :=
  Lax53Proofs.TreeAutomataToMSO.RunFormula.runSentence
    (M.toAutomaton alphabet)

theorem compile_language (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    AutomatonCode.language alphabet M =
      sentenceLanguage (compile alphabet M) := by
  ext t
  exact (Lax53Proofs.TreeAutomataToMSO.RunFormula.runSentence_correct
    (M.toAutomaton alphabet) t).symm

end AutomatonToMSO

end Lax53Proofs.TranslationConstructions
