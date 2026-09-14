import Lax842588.TreeStructure

namespace Lax842588Proofs.TreeNodes

open Lax842588.RankedTree
open Lax842588.RankedTree.Node

universe u

/-- Proof-local compatibility name for the tree-intrinsic child operation. -/
abbrev childNode {A : RankedAlphabet.{u}} {t : Tree A}
    (p : Node t) (i : Fin (A.rank p.label)) : Node t := Node.child p i

/-- The node constructed by `childNode` is related to its parent by the
corresponding indexed child relation. -/
theorem childAt_childNode {A : RankedAlphabet.{u}} {t : Tree A}
    (p : Node t) (i : Fin (A.rank p.label)) :
    Lax842588.RankedTree.Node.ChildAt (ChildIndex.ofSymbolIndex p.label i) p
      (childNode p i) := by
  exact ⟨i, rfl, rfl⟩

/-- For a fixed parent and child slot, the immediate child is unique. -/
theorem childAt_functional {A : RankedAlphabet.{u}} {t : Tree A}
    {i : ChildIndex A} {p q r : Node t}
    (hq : Lax842588.RankedTree.Node.ChildAt i p q)
    (hr : Lax842588.RankedTree.Node.ChildAt i p r) : q = r := by
  rcases hq with ⟨j, hj, rfl⟩
  rcases hr with ⟨k, hk, rfl⟩
  have hjk : j = k := by
    apply Fin.ext
    exact congrArg Subtype.val (hj.trans hk.symm)
  subst k
  rfl

/-- An indexed immediate child of a node is uniquely determined. -/
theorem childAt_iff_eq_childNode {A : RankedAlphabet.{u}} {t : Tree A}
    (p q : Node t) (i : Fin (A.rank p.label)) :
    Lax842588.RankedTree.Node.ChildAt (ChildIndex.ofSymbolIndex p.label i) p q ↔
      q = childNode p i := by
  constructor
  · intro h
    exact childAt_functional h (childAt_childNode p i)
  · rintro rfl
    exact childAt_childNode p i

/-- Every node is either the root or has an immediate parent. -/
theorem root_or_exists_parent {A : RankedAlphabet.{u}} {t : Tree A} (p : Node t) :
    p = Node.rootOf t ∨
      ∃ (i : ChildIndex A) (parent : Node t), Node.ChildAt i parent p := by
  induction p with
  | @root a children =>
      exact Or.inl rfl
  | @inChild a children j p ih =>
      refine Or.inr ?_
      rcases ih with hp | ⟨i, parent, k, hk, hp⟩
      · subst p
        refine ⟨ChildIndex.ofSymbolIndex a j, Node.root, j, rfl, ?_⟩
        rfl
      · refine ⟨i, Node.inChild j parent, k, ?_, ?_⟩
        · simpa [Node.label] using hk
        · simpa [Node.child] using congrArg (Node.inChild j) hp

end Lax842588Proofs.TreeNodes
