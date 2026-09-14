import Lax842588Proofs.FormulaArenaTraversalStack

/-!
Pointwise representation of the postorder formula-occurrence prefix emitted
by the charged traversal.
-/

namespace Lax842588Proofs.FormulaArenaTraversalOrder

open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.FormulaArenaTraversalModel
open Lax560851.WordArena

inductive RootsRepresentOccurrences (I : WordImage)
    (alphabet : RankedAlphabetCode) :
    List Nat → List (Occurrence alphabet) → Prop
  | nil : RootsRepresentOccurrences I alphabet [] []
  | cons {root : Nat} {occurrence : Occurrence alphabet}
      {roots : List Nat} {occurrences : List (Occurrence alphabet)} :
      I.Represents root occurrence.raw →
      RootsRepresentOccurrences I alphabet roots occurrences →
      RootsRepresentOccurrences I alphabet (root :: roots)
        (occurrence :: occurrences)

theorem RootsRepresentOccurrences.toForall₂ {I : WordImage}
    {alphabet : RankedAlphabetCode} {roots : List Nat}
    {occurrences : List (Occurrence alphabet)}
    (h : RootsRepresentOccurrences I alphabet roots occurrences) :
    List.Forall₂ (fun root occurrence =>
      I.Represents root occurrence.raw) roots occurrences := by
  induction h with
  | nil => exact .nil
  | cons hroot _ ih => exact .cons hroot ih

theorem RootsRepresentOccurrences.length_eq {I : WordImage}
    {alphabet : RankedAlphabetCode} {roots : List Nat}
    {occurrences : List (Occurrence alphabet)}
    (h : RootsRepresentOccurrences I alphabet roots occurrences) :
    roots.length = occurrences.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem RootsRepresentOccurrences.append {I : WordImage}
    {alphabet : RankedAlphabetCode} {roots : List Nat}
    {occurrences : List (Occurrence alphabet)}
    (h : RootsRepresentOccurrences I alphabet roots occurrences)
    {root : Nat} {occurrence : Occurrence alphabet}
    (hroot : I.Represents root occurrence.raw) :
    RootsRepresentOccurrences I alphabet (roots ++ [root])
      (occurrences ++ [occurrence]) := by
  induction h with
  | nil => exact .cons hroot .nil
  | cons hhead htail ih => exact .cons hhead ih

def occurrenceFOs (alphabet : RankedAlphabetCode)
    (occurrences : List (Occurrence alphabet)) : List Nat :=
  occurrences.map Occurrence.fo

def occurrenceSOs (alphabet : RankedAlphabetCode)
    (occurrences : List (Occurrence alphabet)) : List Nat :=
  occurrences.map Occurrence.so

/-- The occupied prefixes of the three output arrays describe exactly the
already emitted original formula occurrences. -/
def FormulaOrderRep (I : WordImage) (alphabet : RankedAlphabetCode)
    (occurrences : List (Occurrence alphabet))
    (rootOrder foOrder soOrder : List Nat) : Prop :=
  ∃ roots,
    RootsRepresentOccurrences I alphabet roots occurrences ∧
    WordsAt rootOrder 0 roots ∧
    WordsAt foOrder 0 (occurrenceFOs alphabet occurrences) ∧
    WordsAt soOrder 0 (occurrenceSOs alphabet occurrences)

/-- Pointwise form used by the compiler pass that consumes the completed
postorder arrays. -/
theorem FormulaOrderRep.getD {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {occurrences : List (Occurrence alphabet)}
    {rootOrder foOrder soOrder : List Nat}
    (h : FormulaOrderRep I alphabet occurrences rootOrder foOrder soOrder)
    (i : Nat) (hi : i < occurrences.length) :
    ∃ root,
      rootOrder.getD i 0 = root ∧
      foOrder.getD i 0 = (occurrences.get ⟨i, hi⟩).fo ∧
      soOrder.getD i 0 = (occurrences.get ⟨i, hi⟩).so ∧
      I.Represents root (occurrences.get ⟨i, hi⟩).raw := by
  rcases h with ⟨roots, hroots, hrootWords, hfoWords, hsoWords⟩
  have hlength := hroots.length_eq
  let root := roots.get ⟨i, by omega⟩
  have hrep := hroots.toForall₂.get (i := i) (by omega) hi
  have hroot : rootOrder.getD i 0 = root := by
    have hword := hrootWords i (by simpa [hlength] using hi)
    simp only [zero_add] at hword
    rw [hword]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp [root]
  have hfo : foOrder.getD i 0 = (occurrences.get ⟨i, hi⟩).fo := by
    have hmap : i < (occurrenceFOs alphabet occurrences).length := by
      simpa [occurrenceFOs] using hi
    have hword := hfoWords i hmap
    simp only [zero_add] at hword
    rw [hword, List.getD_eq_getElem _ _ hmap]
    simp [occurrenceFOs]
  have hso : soOrder.getD i 0 = (occurrences.get ⟨i, hi⟩).so := by
    have hmap : i < (occurrenceSOs alphabet occurrences).length := by
      simpa [occurrenceSOs] using hi
    have hword := hsoWords i hmap
    simp only [zero_add] at hword
    rw [hword, List.getD_eq_getElem _ _ hmap]
    simp [occurrenceSOs]
  exact ⟨root, hroot, hfo, hso, hrep⟩

theorem formulaOrderRep_nil (I : WordImage) (alphabet : RankedAlphabetCode)
    (rootOrder foOrder soOrder : List Nat) :
    FormulaOrderRep I alphabet [] rootOrder foOrder soOrder := by
  exact ⟨[], .nil, wordsAt_nil _ _, wordsAt_nil _ _, wordsAt_nil _ _⟩

theorem formulaOrderRep_append {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {occurrences : List (Occurrence alphabet)}
    {rootOrder foOrder soOrder : List Nat}
    (occurrence : Occurrence alphabet) (root : Nat)
    (horder : FormulaOrderRep I alphabet occurrences rootOrder foOrder soOrder)
    (hroot : I.Represents root occurrence.raw)
    (hrootSpace : occurrences.length < rootOrder.length)
    (hfoSpace : occurrences.length < foOrder.length)
    (hsoSpace : occurrences.length < soOrder.length) :
    FormulaOrderRep I alphabet (occurrences ++ [occurrence])
      (rootOrder.set occurrences.length root)
      (foOrder.set occurrences.length occurrence.fo)
      (soOrder.set occurrences.length occurrence.so) := by
  rcases horder with ⟨roots, hroots, hrootWords, hfoWords, hsoWords⟩
  have hrootsLength := hroots.length_eq
  have hrootWords' := wordsAt_set_append (value := root) hrootWords (by
    simpa [hrootsLength] using hrootSpace)
  have hfoWords' := wordsAt_set_append (value := occurrence.fo) hfoWords (by
    simpa [occurrenceFOs] using hfoSpace)
  have hsoWords' := wordsAt_set_append (value := occurrence.so) hsoWords (by
    simpa [occurrenceSOs] using hsoSpace)
  refine ⟨roots ++ [root], ?_, ?_, ?_, ?_⟩
  · exact hroots.append hroot
  · simpa [hrootsLength] using hrootWords'
  · simpa [occurrenceFOs, List.map_append] using hfoWords'
  · simpa [occurrenceSOs, List.map_append] using hsoWords'

end Lax842588Proofs.FormulaArenaTraversalOrder
