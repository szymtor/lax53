import Lax842588Proofs.CompilerNumericBounds
import Lax842588Proofs.IntrinsicParameterFields
import Lax842588Proofs.IntrinsicFormulaInput

/-! A primitive-recursive bound on the runtime-built compiler input from the public parameter size. -/

namespace Lax842588Proofs.IntrinsicParameterEncoding

open Encodable Lax146103.MSOSyntax Lax842588.ValueTranslations Lax842588.TreeStructure
open Lax842588.MSOLinearTime Lax842588.TreeModelCheckingEncoding
open Lax560851.StructuralPresentation Lax560851.StructuralCombinators
open Lax842588Proofs.CompilerNumericBounds Lax842588Proofs.PrimitiveRecursiveBounds
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.IntrinsicCompilerFields
open Lax842588Proofs.IntrinsicParameterFields Lax842588Proofs.IntrinsicFormulaInput

theorem alphabet_size (alphabet : RankedAlphabetCode) :
    (derivedPresentation : Presentation RankedAlphabetCode).structuralSize alphabet =
      1 + 2 * alphabet.length := by
  change (listToRaw nat alphabet).nodes = _
  induction alphabet with
  | nil => rfl
  | cons x xs ih =>
    simp only [listToRaw, Raw.nodes, List.length_cons]
    rw [ih]
    simp only [nat, Raw.nodes]
    omega

theorem parameter_components (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    alphabet.length ≤ parameterSize alphabet φ ∧
      sentenceSize alphabet φ ≤ parameterSize alphabet φ ∧
      maximumRank alphabet ≤ parameterSize alphabet φ := by
  unfold parameterSize
  rw [alphabet_size]
  omega

def fieldBound (p : Nat) : Nat := 8 + 5 * p

theorem fieldBound_prim : Primrec fieldBound :=
  Primrec.nat_add.comp (Primrec.const 8)
    (Primrec.nat_mul.comp (Primrec.const 5) Primrec.id)

structure ShapeBounds (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) (K : Nat) : Prop where
  alphabetLength : alphabet.length ≤ K
  alphabetValues : ∀ v ∈ alphabet, v ≤ K
  count : (postorder alphabet φ).length ≤ K
  steps : traversalSteps alphabet φ ≤ K
  scopes : ∀ o ∈ postorder alphabet φ, o.fo + o.so ≤ K
  fields : ∀ o ∈ postorder alphabet φ, ∀ v ∈ IntrinsicCompilerFields.fields o, v ≤ K

theorem shape_bounds (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    ShapeBounds alphabet φ (fieldBound (parameterSize alphabet φ)) := by
  obtain ⟨hα, hφ, hR⟩ := parameter_components alphabet φ
  have hsteps := traversalSteps_le_structure alphabet φ
  change traversalSteps alphabet φ ≤ 3 * sentenceSize alphabet φ at hsteps
  have hcount := postorder_length_le_traversalSteps alphabet φ
  refine ⟨by unfold fieldBound; omega, ?_, by unfold fieldBound; omega,
    by unfold fieldBound; omega, ?_, ?_⟩
  · intro v hv
    have hvR : v ≤ maximumRank alphabet := fold_max_mem alphabet 0 v hv
    unfold fieldBound
    omega
  · intro o ho
    have hs := scopes_le_size alphabet φ o ho
    change o.fo + o.so ≤ 0 + 0 + 3 * sentenceSize alphabet φ at hs
    unfold fieldBound
    omega
  · intro o ho v hv
    have hs := sentence_fields_le alphabet φ o ho v hv
    unfold fieldBound
    omega

def alphabetCodeBound (p : Nat) : Nat := listBound (fieldBound p) (fieldBound p)
def headerCodeBound (p : Nat) : Nat := listBound (fieldBound p) (fieldBound p + 1)
def rowsCodeBound (p : Nat) : Nat := listBound (listBound (fieldBound p) 6) (fieldBound p)
def inputCodeBound (p : Nat) : Nat := pairCap (alphabetCodeBound p) (rowsCodeBound p)

theorem alphabetCodeBound_prim : Primrec alphabetCodeBound :=
  listBound_prim.comp fieldBound_prim fieldBound_prim
theorem headerCodeBound_prim : Primrec headerCodeBound :=
  listBound_prim.comp fieldBound_prim (Primrec.nat_add.comp fieldBound_prim (Primrec.const 1))
theorem rowsCodeBound_prim : Primrec rowsCodeBound :=
  listBound_prim.comp (listBound_prim.comp fieldBound_prim (Primrec.const 6)) fieldBound_prim
theorem inputCodeBound_prim : Primrec inputCodeBound :=
  pairCap_prim.comp alphabetCodeBound_prim rowsCodeBound_prim

theorem alphabet_code_le (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    encode alphabet ≤ alphabetCodeBound (parameterSize alphabet φ) :=
  encode_list_le _ _ alphabet (shape_bounds alphabet φ).alphabetLength
    (shape_bounds alphabet φ).alphabetValues

theorem header_code_le (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    encode (alphabet.length :: alphabet) ≤ headerCodeBound (parameterSize alphabet φ) := by
  have h := shape_bounds alphabet φ
  apply encode_list_le
  · simpa using Nat.add_le_add_right h.alphabetLength 1
  · intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h.alphabetLength
    · exact h.alphabetValues v hv

theorem rows_code_le (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    encode ((postorder alphabet φ).map fields) ≤ rowsCodeBound (parameterSize alphabet φ) := by
  rw [← encode_rowCodes]
  apply encode_list_le
  · simpa [rowCodes] using (shape_bounds alphabet φ).count
  · intro v hv
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv
    exact encode_list_le _ 6 (fields o) (by simp [fields_length])
      ((shape_bounds alphabet φ).fields o ho)

theorem input_code_le (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    encode (alphabet, (postorder alphabet φ).map fields) ≤ inputCodeBound (parameterSize alphabet φ) :=
  pair_le_cap (alphabet_code_le alphabet φ) (rows_code_le alphabet φ)

end Lax842588Proofs.IntrinsicParameterEncoding
