import Lax58Proofs.WordArena
import Lax53Proofs.StructuralRepresentations

/-!
Proof-only semantic access lemmas for the distinguished Lax-58 arena.
They expose no layout in the Lax-53 concept package.
-/

namespace Lax53Proofs.ArenaSemantics

open Lax58.StructuralPresentation
open Lax58.StructuralCombinators
open Lax58.WordArena

/-- The logical list view copied from an arena image. -/
def arenaWords (I : WordImage) : List Nat := I.memory.toList

theorem getD_eq_of_wordAt {I : WordImage} {address value : Nat}
    (h : I.wordAt? address = some value) :
    (arenaWords I).getD address 0 = value := by
  simp only [arenaWords, WordImage.wordAt?, List.getD_eq_getElem?_getD]
  rw [Array.getElem?_toList]
  change I.memory[address]? = some value at h
  rw [h]
  rfl

theorem Represents.valid {I : WordImage} {address : Nat} {raw : Raw}
    (h : I.Represents address raw) : I.ValidAddress address := by
  cases h with
  | nat hvalid _ _ _ => exact hvalid
  | pair hvalid _ _ _ _ _ => exact hvalid

theorem ValidAddress.lt_arenaWords_length {I : WordImage} {address : Nat}
    (h : I.ValidAddress address) : address + 2 < (arenaWords I).length := by
  simpa [arenaWords, WordImage.ValidAddress, WordImage.memoryWords] using h.2

theorem Represents.nat_words {I : WordImage} {address payload : Nat}
    (h : I.Represents address (.nat payload)) :
    (arenaWords I).getD address 0 = WordImage.natTag ∧
      (arenaWords I).getD (address + 1) 0 = payload ∧
      (arenaWords I).getD (address + 2) 0 = 0 := by
  cases h with
  | nat _ htag hvalue hpadding =>
      exact ⟨getD_eq_of_wordAt htag, getD_eq_of_wordAt hvalue,
        getD_eq_of_wordAt hpadding⟩

theorem Represents.pair_words {I : WordImage} {address : Nat}
    {left right : Raw} (h : I.Represents address (.pair left right)) :
    ∃ leftAddress rightAddress,
      (arenaWords I).getD address 0 = WordImage.pairTag ∧
      (arenaWords I).getD (address + 1) 0 = leftAddress ∧
      (arenaWords I).getD (address + 2) 0 = rightAddress ∧
      I.Represents leftAddress left ∧ I.Represents rightAddress right := by
  cases h with
  | pair _ htag hleft hright leftRep rightRep =>
      exact ⟨_, _, getD_eq_of_wordAt htag, getD_eq_of_wordAt hleft,
        getD_eq_of_wordAt hright, leftRep, rightRep⟩

theorem Represents.nat_payload {I : WordImage} {address payload : Nat}
    (h : I.Represents address (Lax58.StructuralCombinators.nat.toRaw payload)) :
    (arenaWords I).getD (address + 1) 0 = payload :=
  (Lax53Proofs.ArenaSemantics.Represents.nat_words h).2.1

theorem Represents.fields_nil {I : WordImage} {address : Nat}
    (h : I.Represents address (Raw.fields [])) :
    (arenaWords I).getD address 0 = WordImage.natTag := by
  exact (Lax53Proofs.ArenaSemantics.Represents.nat_words h).1

theorem Represents.fields_cons {I : WordImage} {address : Nat}
    {raw : Raw} {raws : List Raw}
    (h : I.Represents address (Raw.fields (raw :: raws))) :
    ∃ rawAddress restAddress,
      (arenaWords I).getD address 0 = WordImage.pairTag ∧
      (arenaWords I).getD (address + 1) 0 = rawAddress ∧
      (arenaWords I).getD (address + 2) 0 = restAddress ∧
      I.Represents rawAddress raw ∧
      I.Represents restAddress (Raw.fields raws) := by
  simpa [Raw.fields] using
    (Lax53Proofs.ArenaSemantics.Represents.pair_words h)

theorem Represents.list_nil {α : Type} {P : Presentation α}
    {I : WordImage} {address : Nat}
    (h : I.Represents address ((Lax58.StructuralCombinators.list P).toRaw [])) :
    (arenaWords I).getD address 0 = WordImage.natTag := by
  exact (Lax53Proofs.ArenaSemantics.Represents.nat_words h).1

theorem Represents.list_cons {α : Type} {P : Presentation α}
    {I : WordImage} {address : Nat} {x : α} {xs : List α}
    (h : I.Represents address ((Lax58.StructuralCombinators.list P).toRaw (x :: xs))) :
    ∃ xAddress restAddress,
      (arenaWords I).getD address 0 = WordImage.pairTag ∧
      (arenaWords I).getD (address + 1) 0 = xAddress ∧
      (arenaWords I).getD (address + 2) 0 = restAddress ∧
      I.Represents xAddress (P.toRaw x) ∧
      I.Represents restAddress ((Lax58.StructuralCombinators.list P).toRaw xs) := by
  simpa [Lax58.StructuralCombinators.list, listToRaw] using
    (Lax53Proofs.ArenaSemantics.Represents.pair_words h)

/-- The tag at a structurally represented list cursor says exactly whether
the represented suffix is a cons cell. -/
theorem Represents.list_tag {α : Type} {P : Presentation α}
    {I : WordImage} {address : Nat} {xs : List α}
    (h : I.Represents address ((Lax58.StructuralCombinators.list P).toRaw xs)) :
    (arenaWords I).getD address 0 = if xs.isEmpty then
      WordImage.natTag else WordImage.pairTag := by
  cases xs with
  | nil =>
      simpa using Lax53Proofs.ArenaSemantics.Represents.list_nil h
  | cons x xs =>
      obtain ⟨_, _, htag, -⟩ :=
        Lax53Proofs.ArenaSemantics.Represents.list_cons h
      simpa using htag

theorem Represents.prod_fields {α : Type} {β : Type} {A : Presentation α}
    {B : Presentation β} {I : WordImage} {address : Nat} {x : α} {y : β}
    (h : I.Represents address ((Lax58.StructuralCombinators.prod A B).toRaw (x, y))) :
    ∃ xAddress yAddress,
      (arenaWords I).getD address 0 = WordImage.pairTag ∧
      (arenaWords I).getD (address + 1) 0 = xAddress ∧
      (arenaWords I).getD (address + 2) 0 = yAddress ∧
      I.Represents xAddress (A.toRaw x) ∧ I.Represents yAddress (B.toRaw y) := by
  simpa [Lax58.StructuralCombinators.prod] using
    (Lax53Proofs.ArenaSemantics.Represents.pair_words h)

end Lax53Proofs.ArenaSemantics
