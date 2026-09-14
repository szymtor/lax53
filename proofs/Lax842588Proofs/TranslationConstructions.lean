import Lax842588.ValueTranslations
import Lax842588Proofs.TreeAutomataToMSO

/-!
The automaton-to-MSO half of the value-level result needs no separate raw
formula construction. We instantiate the already verified intrinsic
automaton formula directly at the concrete finite-state automaton denoted by
an `AutomatonCode`.
-/

namespace Lax842588Proofs.TranslationConstructions

open Lax146103.MSOSyntax
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.TreeAutomaton
open Lax842588.ValueTranslations

namespace AutomatonToMSO

/-- Intrinsic automaton-to-MSO translation exposed by the value theorem. -/
noncomputable def compile (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    Sentence (treeSignature alphabet.toRankedAlphabet) :=
  Lax842588Proofs.TreeAutomataToMSO.RunFormula.runSentence
    (M.toAutomaton alphabet)

theorem compile_language (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    AutomatonCode.language alphabet M =
      sentenceLanguage (compile alphabet M) := by
  ext t
  exact (Lax842588Proofs.TreeAutomataToMSO.RunFormula.runSentence_correct
    (M.toAutomaton alphabet) t).symm

end AutomatonToMSO

end Lax842588Proofs.TranslationConstructions
