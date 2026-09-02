import Lax53Proofs.EffectiveTranslations
import Lax53Proofs.EncodedFormulaCompiler

namespace Lax53Proofs.ValueTranslations

open Lax53.EffectiveTranslations
open Lax53Proofs.EffectiveTranslations.AutomatonToMSO
open Lax53Proofs.EncodedFormulaCompiler

/--
---
conclusion: Lax53.EffectiveTranslations.uniform_language_equivalence
---
The two witnesses operate directly on finite Lean values. Their correctness
uses the previously verified automaton-to-formula construction and the
marked-tree formula compiler; no serialization theorem occurs in the result.
-/
theorem uniform_language_equivalence_proof :
    (∃ automatonToMSO : EncodedAutomaton → EncodedSentence,
      ∀ input,
        (automatonToMSO input).1 = input.1 ∧
        AutomatonCode.language input.1 input.2 =
          FormulaCode.language input.1 (automatonToMSO input).2) ∧
    (∃ msoToAutomaton : EncodedSentence → EncodedAutomaton,
      ∀ input,
        (msoToAutomaton input).1 = input.1 ∧
        AutomatonCode.language input.1 (msoToAutomaton input).2 =
          FormulaCode.language input.1 input.2) := by
  exact ⟨⟨compile, fun input => ⟨compile_alphabet input, compile_language input⟩⟩,
    ⟨compileSentence,
      fun input => ⟨compileSentence_alphabet input, compileSentence_language input⟩⟩⟩

end Lax53Proofs.ValueTranslations
