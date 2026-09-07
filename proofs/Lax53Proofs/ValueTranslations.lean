import Lax53Proofs.TranslationConstructions
import Lax53Proofs.IntrinsicFormulaCompiler

namespace Lax53Proofs.ValueTranslations

open Lax53.ValueTranslations
open Lax53Proofs.TranslationConstructions.AutomatonToMSO
open Lax53Proofs.IntrinsicFormulaCompiler

/--
---
conclusion: Lax53.ValueTranslations.language_equivalence
---
The two witnesses operate directly on finite Lean values. Their correctness
uses the previously verified automaton-to-formula construction and the
marked-tree formula compiler; no serialization theorem occurs in the result.
-/
theorem language_equivalence_proof :
    (∃ automatonToMSO : (alphabet : RankedAlphabetCode) → AutomatonCode →
        Lax52.MSOSyntax.Sentence
          (Lax53.TreeStructure.treeSignature alphabet.toRankedAlphabet),
      ∀ alphabet M,
        AutomatonCode.language alphabet M =
          Lax53.TreeStructure.sentenceLanguage (automatonToMSO alphabet M)) ∧
    (∃ msoToAutomaton : (alphabet : RankedAlphabetCode) →
        Lax52.MSOSyntax.Sentence
          (Lax53.TreeStructure.treeSignature alphabet.toRankedAlphabet) →
            AutomatonCode,
      ∀ alphabet phi,
        AutomatonCode.language alphabet (msoToAutomaton alphabet phi) =
          Lax53.TreeStructure.sentenceLanguage phi) := by
  exact ⟨⟨compile, compile_language⟩,
    ⟨compileSentence, compileSentence_language⟩⟩

end Lax53Proofs.ValueTranslations
