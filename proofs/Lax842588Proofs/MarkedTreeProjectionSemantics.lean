import Lax842588Proofs.MarkedTrees
import Lax842588Proofs.MSOSemantics

namespace Lax842588Proofs.MarkedTreeProjectionSemantics

open FirstOrder
open FirstOrder.Language
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588Proofs.MarkedTrees

universe u

/-- Forgetting one first-order marker preserves the underlying labelled-tree
structure. -/
def dropFOStructureEquiv {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A (n + 1) m)) :
    @Language.Equiv (treeSignature A) (Node t) (Node (dropFOTree t))
      (@markedStructure A (n + 1) m t) (@markedStructure A n m (dropFOTree t)) := by
  letI : (treeSignature A).Structure (Node t) := markedStructure t
  letI : (treeSignature A).Structure (Node (dropFOTree t)) :=
    markedStructure (dropFOTree t)
  exact
    { toEquiv := dropFONodeEquiv t
      map_fun' := by
        intro _ f
        exact nomatch f
      map_rel' := by
        intro _ r xs
        cases r with
        | label a =>
            change (dropFONode (xs 0)).label.1 = a ↔ (xs 0).label.1 = a
            rw [dropFONode_label]
            rfl
        | child slot =>
            change
              (∃ j : Fin (A.rank (dropFONode (xs 0)).label.1),
                j.val = slot.val ∧
                  dropFONode (xs 1) = Node.child (dropFONode (xs 0)) j) ↔
              ∃ i : Fin (A.rank (xs 0).label.1),
                i.val = slot.val ∧ xs 1 = Node.child (xs 0) i
            constructor
            · rintro ⟨j, hj, hchild⟩
              obtain ⟨i, hij, hi⟩ :=
                (dropFONode_child_iff (xs 0) (xs 1) j).mp hchild
              exact ⟨i, hij.trans hj, hi⟩
            · rintro ⟨i, hi, hchild⟩
              obtain ⟨j, hji, hj⟩ := dropFONode_child_exists (xs 0) i
              refine ⟨j, hji.trans hi, ?_⟩
              rw [hchild]
              exact hj }

/-- Forgetting one monadic marker preserves the underlying labelled-tree
structure. -/
def dropSOStructureEquiv {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n (m + 1))) :
    @Language.Equiv (treeSignature A) (Node t) (Node (dropSOTree t))
      (@markedStructure A n (m + 1) t) (@markedStructure A n m (dropSOTree t)) := by
  letI : (treeSignature A).Structure (Node t) := markedStructure t
  letI : (treeSignature A).Structure (Node (dropSOTree t)) :=
    markedStructure (dropSOTree t)
  exact
    { toEquiv := dropSONodeEquiv t
      map_fun' := by
        intro _ f
        exact nomatch f
      map_rel' := by
        intro _ r xs
        cases r with
        | label a =>
            change (dropSONode (xs 0)).label.1 = a ↔ (xs 0).label.1 = a
            rw [dropSONode_label]
            rfl
        | child slot =>
            change
              (∃ j : Fin (A.rank (dropSONode (xs 0)).label.1),
                j.val = slot.val ∧
                  dropSONode (xs 1) = Node.child (dropSONode (xs 0)) j) ↔
              ∃ i : Fin (A.rank (xs 0).label.1),
                i.val = slot.val ∧ xs 1 = Node.child (xs 0) i
            constructor
            · rintro ⟨j, hj, hchild⟩
              obtain ⟨i, hij, hi⟩ :=
                (dropSONode_child_iff (xs 0) (xs 1) j).mp hchild
              exact ⟨i, hij.trans hj, hi⟩
            · rintro ⟨i, hi, hchild⟩
              obtain ⟨j, hji, hj⟩ := dropSONode_child_exists (xs 0) i
              refine ⟨j, hji.trans hi, ?_⟩
              rw [hchild]
              exact hj }

end Lax842588Proofs.MarkedTreeProjectionSemantics
