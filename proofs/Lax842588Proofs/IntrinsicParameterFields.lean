import Lax842588Proofs.IntrinsicCompilerFields
import Lax842588Proofs.AutomatonTableEncoding
import Lax842588.MSOLinearTime

/-! Scope counts and extracted field values are bounded by mathematical sentence size. -/

namespace Lax842588Proofs.IntrinsicParameterFields

open Lax146103.MSOSyntax Lax842588.ValueTranslations Lax842588.TreeStructure Lax842588.RankedTree
open Lax842588.StructuralRepresentations Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.IntrinsicCompilerFields
open Lax842588Proofs.MarkedTrees

theorem scopes_le_count (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat} (f : Formula (treeSignature alphabet.toRankedAlphabet) n m),
      ∀ o ∈ postorder alphabet f, o.fo + o.so ≤ n + m + (postorder alphabet f).length := by
  intro n m f
  induction f with
  | falsum | equal _ _ | rel _ _ | mem _ _ =>
    intro o ho
    simp only [postorder, List.mem_singleton] at ho
    subst o
    simp only [postorder, List.length_singleton]
    omega
  | or f g hf hg =>
    intro o ho
    simp only [postorder, List.mem_append, List.mem_singleton] at ho
    simp only [postorder, List.length_append, List.length_singleton]
    rcases ho with (ho | ho) | rfl
    · have := hf o ho; omega
    · have := hg o ho; omega
    · simp
  | neg f ih | exFO f ih | exSO f ih =>
    intro o ho
    simp only [postorder, List.mem_append, List.mem_singleton] at ho
    simp only [postorder, List.length_append, List.length_singleton]
    rcases ho with ho | rfl
    · have := ih o ho; omega
    · simp

theorem scopes_le_size (alphabet : RankedAlphabetCode) {n m : Nat}
    (f : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (o : Occurrence alphabet) (ho : o ∈ postorder alphabet f) :
    o.fo + o.so ≤ n + m + 3 * (formulaStructure alphabet f).nodes := by
  have := scopes_le_count alphabet f o ho
  have := postorder_length_le_traversalSteps alphabet f
  have := traversalSteps_le_structure alphabet f
  omega

theorem childIndex_le_rank (alphabet : RankedAlphabetCode)
    (i : ChildIndex alphabet.toRankedAlphabet) : i.val ≤ maximumRank alphabet := by
  obtain ⟨a, ha⟩ := i.property
  have hr := AutomatonTableEncoding.maximumRank_ge alphabet a.val a.isLt
  have hi : i.val < alphabet.getD a.val 0 := by
    simpa [RankedAlphabetCode.toRankedAlphabet, List.getD_eq_getElem] using ha
  omega

theorem fields_le (alphabet : RankedAlphabetCode) (o : Occurrence alphabet) :
    ∀ v ∈ fields o, v ≤ 8 + alphabet.length + maximumRank alphabet + o.fo + o.so := by
  obtain ⟨n, m, f⟩ := o
  cases f with
  | equal x y =>
    have hx := (treeTermVar x).isLt
    have hy := (treeTermVar y).isLt
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false]
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | rel relation ts =>
    cases relation with
    | label a =>
      have ha := a.isLt
      have hx := (treeTermVar (ts 0)).isLt
      simp only [fields, List.mem_cons, List.not_mem_nil, or_false]
      intro v hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    | child i =>
      have hi := childIndex_le_rank alphabet i
      have hx := (treeTermVar (ts 0)).isLt
      have hy := (treeTermVar (ts 1)).isLt
      simp only [fields, List.mem_cons, List.not_mem_nil, or_false]
      intro v hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | mem x X =>
    have hx := (treeTermVar x).isLt
    have hX := X.isLt
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false]
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | falsum | or _ _ | neg _ | exFO _ | exSO _ =>
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false]
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem sentence_fields_le (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (o : Occurrence alphabet) (ho : o ∈ postorder alphabet φ) :
    ∀ v ∈ fields o, v ≤ 8 + alphabet.length + maximumRank alphabet +
      3 * Lax842588.MSOLinearTime.sentenceSize alphabet φ := by
  intro v hv
  have := fields_le alphabet o v hv
  have := scopes_le_size alphabet φ o ho
  unfold Lax842588.MSOLinearTime.sentenceSize
  omega

end Lax842588Proofs.IntrinsicParameterFields
