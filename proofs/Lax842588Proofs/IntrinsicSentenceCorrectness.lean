import Lax842588Proofs.IntrinsicCompilerOutput

/-! At empty scope the compiler's symbol numbers are the original alphabet's numbers. -/

namespace Lax842588Proofs.IntrinsicSentenceCorrectness

open Lax146103.MSOSyntax Lax842588.RankedTree Lax842588.TreeStructure Lax842588.ValueTranslations
open Lax842588Proofs.IntrinsicFormulaCompiler Lax842588Proofs.IntrinsicCompilerFields
open Lax842588Proofs.MarkedAlphabetEncoding Lax842588Proofs.EncodedProjection
open Lax842588Proofs.FiniteWordStates Lax842588Proofs.FiniteAutomatonEncoding

theorem zeroSymbolMap_val (alphabet : RankedAlphabetCode)
    (a : alphabet.toRankedAlphabet.Symbol) : (zeroSymbolMap alphabet a).val = a.val := by
  have hz (d : WordState 2 0) : d.val = 0 := by
    have : d.val < 1 := d.isLt
    omega
  have hp (x y : WordState 2 0) : (pack alphabet 0 0 ((a, x), y)).val = a.val := by
    change y.val + (words 2 0).length * (x.val + (words 2 0).length * a.val) = a.val
    rw [hz x, hz y]
    simp [words]
  exact hp _ _

theorem mapTree_id (alphabet : RankedAlphabetCode) (t : Tree alphabet.toRankedAlphabet) :
    mapTree alphabet alphabet id (fun _ => rfl) t = t := by
  induction t with
  | node a children ih =>
    simp only [mapTree, id_eq, Fin.cast_refl]
    exact congrArg (Lax842588.RankedTree.Tree.node (A := alphabet.toRankedAlphabet) a) (funext ih)

theorem compileFormula_sentence (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    ((compileFormula alphabet φ).toAutomaton alphabet).Accepts t ↔
      t ∈ sentenceLanguage φ := by
  have hp := pullback_accepts_iff alphabet alphabet id (fun _ => rfl)
    (compileFormula alphabet φ) t
  have hl : ((compileSentence alphabet φ).toAutomaton alphabet).Accepts t ↔
      t ∈ sentenceLanguage φ := by
    change t ∈ AutomatonCode.language alphabet (compileSentence alphabet φ) ↔ _
    rw [compileSentence_language]
  have hmap : (fun a => if h : a < alphabet.length then
      (zeroSymbolMap alphabet ⟨a, h⟩).val else 0) =
      (fun a => if h : a < alphabet.length then (id (⟨a, h⟩ : Fin alphabet.length)).val else 0) := by
    funext a
    split <;> simp_all only [zeroSymbolMap_val, id_eq]
  rw [compileSentence, hmap] at hl
  simpa only [mapTree_id] using hp.symm.trans hl

theorem compileRows_sentence (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    ((compileRows alphabet ((FormulaArenaTraversalModel.postorder alphabet φ).map fields)).toAutomaton
      alphabet).Accepts t ↔ t ∈ sentenceLanguage φ := by
  rw [compileRows_eq]
  exact compileFormula_sentence alphabet φ t

end Lax842588Proofs.IntrinsicSentenceCorrectness
