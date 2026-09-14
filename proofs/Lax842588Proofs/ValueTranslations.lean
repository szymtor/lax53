import Lax842588Proofs.TranslationConstructions
import Lax842588Proofs.IntrinsicFormulaCompiler

namespace Lax842588Proofs.ValueTranslations

open Lax842588.ValueTranslations
open Lax842588Proofs.TranslationConstructions.AutomatonToMSO
open Lax842588Proofs.IntrinsicFormulaCompiler

/--
---
conclusion: Lax842588.ValueTranslations.language_equivalence
---
The two witnesses operate directly on finite Lean values. Their correctness
uses the previously verified automaton-to-formula construction and the
marked-tree formula compiler; no serialization theorem occurs in the result.
-/
theorem language_equivalence_proof :
    (∃ automatonToMSO : (alphabet : RankedAlphabetCode) → AutomatonCode →
        Lax146103.MSOSyntax.Sentence
          (Lax842588.TreeStructure.treeSignature alphabet.toRankedAlphabet),
      ∀ alphabet M,
        AutomatonCode.language alphabet M =
          Lax842588.TreeStructure.sentenceLanguage (automatonToMSO alphabet M)) ∧
    (∃ msoToAutomaton : (alphabet : RankedAlphabetCode) →
        Lax146103.MSOSyntax.Sentence
          (Lax842588.TreeStructure.treeSignature alphabet.toRankedAlphabet) →
            AutomatonCode,
      ∀ alphabet phi,
        AutomatonCode.language alphabet (msoToAutomaton alphabet phi) =
          Lax842588.TreeStructure.sentenceLanguage phi) := by
  exact ⟨⟨compile, compile_language⟩,
    ⟨compileSentence, compileSentence_language⟩⟩

end Lax842588Proofs.ValueTranslations
