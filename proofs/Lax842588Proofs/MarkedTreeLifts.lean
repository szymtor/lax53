import Lax842588Proofs.MarkedTreeProjectionSemantics

namespace Lax842588Proofs.MarkedTreeLifts

open FirstOrder
open FirstOrder.Language
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588Proofs.MarkedTrees

universe u

/-- Add a first-order marker whose value at a node is prescribed by `mark`. -/
def liftFOTreeWith {A : RankedAlphabet.{u}} {n m : Nat} :
    (t : Tree (MarkedAlphabet A n m)) → (Node t → Bool) →
      Tree (MarkedAlphabet A (n + 1) m)
  | .node s children, mark =>
      .node (MarkedAlphabet.liftFO s (mark .root))
        (fun i => liftFOTreeWith (children i) (fun p => mark (.inChild i p)))

/-- Add a monadic marker whose value at a node is prescribed by `mark`. -/
def liftSOTreeWith {A : RankedAlphabet.{u}} {n m : Nat} :
    (t : Tree (MarkedAlphabet A n m)) → (Node t → Bool) →
      Tree (MarkedAlphabet A n (m + 1))
  | .node s children, mark =>
      .node (MarkedAlphabet.liftSO s (mark .root))
        (fun i => liftSOTreeWith (children i) (fun p => mark (.inChild i p)))

def liftFOTreeNodeTo {A : RankedAlphabet.{u}} {n m : Nat} :
    {t : Tree (MarkedAlphabet A n m)} → (mark : Node t → Bool) →
      Node (liftFOTreeWith t mark) → Node t
  | .node _ _, _, .root => .root
  | .node _ _, mark, .inChild i p =>
      .inChild i (liftFOTreeNodeTo (fun q => mark (.inChild i q)) p)

def liftFOTreeNodeFrom {A : RankedAlphabet.{u}} {n m : Nat} :
    {t : Tree (MarkedAlphabet A n m)} → (mark : Node t → Bool) →
      Node t → Node (liftFOTreeWith t mark)
  | .node _ _, _, .root => .root
  | .node _ _, mark, .inChild i p =>
      .inChild i (liftFOTreeNodeFrom (fun q => mark (.inChild i q)) p)

def liftSOTreeNodeTo {A : RankedAlphabet.{u}} {n m : Nat} :
    {t : Tree (MarkedAlphabet A n m)} → (mark : Node t → Bool) →
      Node (liftSOTreeWith t mark) → Node t
  | .node _ _, _, .root => .root
  | .node _ _, mark, .inChild i p =>
      .inChild i (liftSOTreeNodeTo (fun q => mark (.inChild i q)) p)

def liftSOTreeNodeFrom {A : RankedAlphabet.{u}} {n m : Nat} :
    {t : Tree (MarkedAlphabet A n m)} → (mark : Node t → Bool) →
      Node t → Node (liftSOTreeWith t mark)
  | .node _ _, _, .root => .root
  | .node _ _, mark, .inChild i p =>
      .inChild i (liftSOTreeNodeFrom (fun q => mark (.inChild i q)) p)

@[simp] theorem liftFOTreeNodeTo_from {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool) (p : Node t) :
    liftFOTreeNodeTo mark (liftFOTreeNodeFrom mark p) = p := by
  induction p with
  | root => rfl
  | inChild i p ih =>
      exact congrArg (Node.inChild i) (ih (fun q => mark (.inChild i q)))

@[simp] theorem liftFOTreeNodeFrom_to {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p : Node (liftFOTreeWith t mark)) :
    liftFOTreeNodeFrom mark (liftFOTreeNodeTo mark p) = p := by
  induction t with
  | node s children ih =>
      cases p with
      | root => rfl
      | inChild i p =>
          simpa only [liftFOTreeNodeFrom, liftFOTreeNodeTo] using congrArg
            (@Node.inChild (MarkedAlphabet A (n + 1) m)
              (MarkedAlphabet.liftFO s (mark .root))
              (fun j => liftFOTreeWith (children j) (fun q => mark (.inChild j q))) i)
            (ih i (fun q => mark (.inChild i q)) p)

@[simp] theorem liftSOTreeNodeTo_from {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool) (p : Node t) :
    liftSOTreeNodeTo mark (liftSOTreeNodeFrom mark p) = p := by
  induction p with
  | root => rfl
  | inChild i p ih =>
      exact congrArg (Node.inChild i) (ih (fun q => mark (.inChild i q)))

@[simp] theorem liftSOTreeNodeFrom_to {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p : Node (liftSOTreeWith t mark)) :
    liftSOTreeNodeFrom mark (liftSOTreeNodeTo mark p) = p := by
  induction t with
  | node s children ih =>
      cases p with
      | root => rfl
      | inChild i p =>
          simpa only [liftSOTreeNodeFrom, liftSOTreeNodeTo] using congrArg
            (@Node.inChild (MarkedAlphabet A n (m + 1))
              (MarkedAlphabet.liftSO s (mark .root))
              (fun j => liftSOTreeWith (children j) (fun q => mark (.inChild j q))) i)
            (ih i (fun q => mark (.inChild i q)) p)

def liftFOTreeNodeEquiv {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (mark : Node t → Bool) :
    Node (liftFOTreeWith t mark) ≃ Node t where
  toFun := liftFOTreeNodeTo mark
  invFun := liftFOTreeNodeFrom mark
  left_inv := liftFOTreeNodeFrom_to mark
  right_inv := liftFOTreeNodeTo_from mark

def liftSOTreeNodeEquiv {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (mark : Node t → Bool) :
    Node (liftSOTreeWith t mark) ≃ Node t where
  toFun := liftSOTreeNodeTo mark
  invFun := liftSOTreeNodeFrom mark
  left_inv := liftSOTreeNodeFrom_to mark
  right_inv := liftSOTreeNodeTo_from mark

@[simp] theorem liftFOTreeNode_label {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p : Node (liftFOTreeWith t mark)) :
    p.label = MarkedAlphabet.liftFO (liftFOTreeNodeTo mark p).label
      (mark (liftFOTreeNodeTo mark p)) := by
  induction t with
  | node s children ih =>
      cases p with
      | root => rfl
      | inChild i p =>
          exact ih i (fun q => mark (.inChild i q)) p

@[simp] theorem liftSOTreeNode_label {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p : Node (liftSOTreeWith t mark)) :
    p.label = MarkedAlphabet.liftSO (liftSOTreeNodeTo mark p).label
      (mark (liftSOTreeNodeTo mark p)) := by
  induction t with
  | node s children ih =>
      cases p with
      | root => rfl
      | inChild i p =>
          exact ih i (fun q => mark (.inChild i q)) p

@[simp] theorem liftFOTreeNodeTo_rootOf {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (mark : Node t → Bool) :
    liftFOTreeNodeTo mark (Node.rootOf (liftFOTreeWith t mark)) = Node.rootOf t := by
  cases t
  rfl

@[simp] theorem liftSOTreeNodeTo_rootOf {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (mark : Node t → Bool) :
    liftSOTreeNodeTo mark (Node.rootOf (liftSOTreeWith t mark)) = Node.rootOf t := by
  cases t
  rfl

@[simp] theorem liftFOTreeNodeTo_label {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p : Node (liftFOTreeWith t mark)) :
    (liftFOTreeNodeTo mark p).label = MarkedAlphabet.dropFO p.label := by
  simp only [liftFOTreeNode_label, MarkedAlphabet.dropFO_liftFO]

@[simp] theorem liftSOTreeNodeTo_label {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p : Node (liftSOTreeWith t mark)) :
    (liftSOTreeNodeTo mark p).label = MarkedAlphabet.dropSO p.label := by
  simp only [liftSOTreeNode_label, MarkedAlphabet.dropSO_liftSO]

theorem liftFOTreeNodeTo_child_exists {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p : Node (liftFOTreeWith t mark)) (i : Fin (A.rank p.label.1)) :
    ∃ j : Fin (A.rank (liftFOTreeNodeTo mark p).label.1),
      j.val = i.val ∧
        liftFOTreeNodeTo mark (Node.child p i) =
          Node.child (liftFOTreeNodeTo mark p) j := by
  induction t with
  | node s children ih =>
    cases p with
    | root =>
      let j : Fin (A.rank
          (liftFOTreeNodeTo mark
            (Node.root : Node (liftFOTreeWith (.node s children) mark))).label.1) :=
        ⟨i.val, by simpa only [liftFOTreeNodeTo_label, MarkedAlphabet.dropFO] using i.isLt⟩
      refine ⟨j, rfl, ?_⟩
      have hji : j = i := Fin.ext rfl
      rw [hji]
      exact congrArg
        (@Node.inChild (MarkedAlphabet A n m) s children i)
        (liftFOTreeNodeTo_rootOf (children i) (fun q => mark (.inChild i q)))
    | inChild k p =>
      obtain ⟨j, hval, hchild⟩ := ih k (fun q => mark (.inChild k q)) p i
      refine ⟨j, hval, ?_⟩
      exact congrArg (@Node.inChild (MarkedAlphabet A n m) s children k) hchild

theorem liftSOTreeNodeTo_child_exists {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p : Node (liftSOTreeWith t mark)) (i : Fin (A.rank p.label.1)) :
    ∃ j : Fin (A.rank (liftSOTreeNodeTo mark p).label.1),
      j.val = i.val ∧
        liftSOTreeNodeTo mark (Node.child p i) =
          Node.child (liftSOTreeNodeTo mark p) j := by
  induction t with
  | node s children ih =>
    cases p with
    | root =>
      let j : Fin (A.rank
          (liftSOTreeNodeTo mark
            (Node.root : Node (liftSOTreeWith (.node s children) mark))).label.1) :=
        ⟨i.val, by simpa only [liftSOTreeNodeTo_label, MarkedAlphabet.dropSO] using i.isLt⟩
      refine ⟨j, rfl, ?_⟩
      have hji : j = i := Fin.ext rfl
      rw [hji]
      exact congrArg
        (@Node.inChild (MarkedAlphabet A n m) s children i)
        (liftSOTreeNodeTo_rootOf (children i) (fun q => mark (.inChild i q)))
    | inChild k p =>
      obtain ⟨j, hval, hchild⟩ := ih k (fun q => mark (.inChild k q)) p i
      refine ⟨j, hval, ?_⟩
      exact congrArg (@Node.inChild (MarkedAlphabet A n m) s children k) hchild

theorem liftFOTreeNodeTo_child_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p q : Node (liftFOTreeWith t mark))
    (j : Fin (A.rank (liftFOTreeNodeTo mark p).label.1)) :
    liftFOTreeNodeTo mark q = Node.child (liftFOTreeNodeTo mark p) j ↔
      ∃ i : Fin (A.rank p.label.1), i.val = j.val ∧ q = Node.child p i := by
  constructor
  · intro hq
    let i : Fin (A.rank p.label.1) :=
      ⟨j.val, by simpa only [liftFOTreeNodeTo_label, MarkedAlphabet.dropFO] using j.isLt⟩
    obtain ⟨j', hval, hchild⟩ := liftFOTreeNodeTo_child_exists mark p i
    have hj' : j' = j := Fin.ext hval
    subst j'
    refine ⟨i, rfl, ?_⟩
    apply (liftFOTreeNodeEquiv t mark).injective
    exact hq.trans hchild.symm
  · rintro ⟨i, hval, rfl⟩
    obtain ⟨j', hval', hchild⟩ := liftFOTreeNodeTo_child_exists mark p i
    have hj' : j' = j := Fin.ext (hval'.trans hval)
    subst j'
    exact hchild

theorem liftSOTreeNodeTo_child_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (mark : Node t → Bool)
    (p q : Node (liftSOTreeWith t mark))
    (j : Fin (A.rank (liftSOTreeNodeTo mark p).label.1)) :
    liftSOTreeNodeTo mark q = Node.child (liftSOTreeNodeTo mark p) j ↔
      ∃ i : Fin (A.rank p.label.1), i.val = j.val ∧ q = Node.child p i := by
  constructor
  · intro hq
    let i : Fin (A.rank p.label.1) :=
      ⟨j.val, by simpa only [liftSOTreeNodeTo_label, MarkedAlphabet.dropSO] using j.isLt⟩
    obtain ⟨j', hval, hchild⟩ := liftSOTreeNodeTo_child_exists mark p i
    have hj' : j' = j := Fin.ext hval
    subst j'
    refine ⟨i, rfl, ?_⟩
    apply (liftSOTreeNodeEquiv t mark).injective
    exact hq.trans hchild.symm
  · rintro ⟨i, hval, rfl⟩
    obtain ⟨j', hval', hchild⟩ := liftSOTreeNodeTo_child_exists mark p i
    have hj' : j' = j := Fin.ext (hval'.trans hval)
    subst j'
    exact hchild

/-- Adding a first-order marker leaves the underlying labelled-tree structure
unchanged. -/
def liftFOTreeStructureEquiv {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (mark : Node t → Bool) :
    @Language.Equiv (treeSignature A) (Node (liftFOTreeWith t mark)) (Node t)
      (@markedStructure A (n + 1) m (liftFOTreeWith t mark))
      (@markedStructure A n m t) := by
  letI : (treeSignature A).Structure (Node (liftFOTreeWith t mark)) :=
    markedStructure (liftFOTreeWith t mark)
  letI : (treeSignature A).Structure (Node t) := markedStructure t
  exact
    { toEquiv := liftFOTreeNodeEquiv t mark
      map_fun' := by
        intro _ f
        exact nomatch f
      map_rel' := by
        intro _ r xs
        cases r with
        | label a =>
            change (liftFOTreeNodeTo mark (xs 0)).label.1 = a ↔ (xs 0).label.1 = a
            rw [liftFOTreeNodeTo_label]
            rfl
        | child slot =>
            change
              (∃ j : Fin (A.rank (liftFOTreeNodeTo mark (xs 0)).label.1),
                j.val = slot.val ∧
                  liftFOTreeNodeTo mark (xs 1) =
                    Node.child (liftFOTreeNodeTo mark (xs 0)) j) ↔
              ∃ i : Fin (A.rank (xs 0).label.1),
                i.val = slot.val ∧ xs 1 = Node.child (xs 0) i
            constructor
            · rintro ⟨j, hj, hchild⟩
              obtain ⟨i, hij, hi⟩ :=
                (liftFOTreeNodeTo_child_iff mark (xs 0) (xs 1) j).mp hchild
              exact ⟨i, hij.trans hj, hi⟩
            · rintro ⟨i, hi, hchild⟩
              obtain ⟨j, hji, hj⟩ := liftFOTreeNodeTo_child_exists mark (xs 0) i
              refine ⟨j, hji.trans hi, ?_⟩
              rw [hchild]
              exact hj }

/-- Adding a monadic marker leaves the underlying labelled-tree structure
unchanged. -/
def liftSOTreeStructureEquiv {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (mark : Node t → Bool) :
    @Language.Equiv (treeSignature A) (Node (liftSOTreeWith t mark)) (Node t)
      (@markedStructure A n (m + 1) (liftSOTreeWith t mark))
      (@markedStructure A n m t) := by
  letI : (treeSignature A).Structure (Node (liftSOTreeWith t mark)) :=
    markedStructure (liftSOTreeWith t mark)
  letI : (treeSignature A).Structure (Node t) := markedStructure t
  exact
    { toEquiv := liftSOTreeNodeEquiv t mark
      map_fun' := by
        intro _ f
        exact nomatch f
      map_rel' := by
        intro _ r xs
        cases r with
        | label a =>
            change (liftSOTreeNodeTo mark (xs 0)).label.1 = a ↔ (xs 0).label.1 = a
            rw [liftSOTreeNodeTo_label]
            rfl
        | child slot =>
            change
              (∃ j : Fin (A.rank (liftSOTreeNodeTo mark (xs 0)).label.1),
                j.val = slot.val ∧
                  liftSOTreeNodeTo mark (xs 1) =
                    Node.child (liftSOTreeNodeTo mark (xs 0)) j) ↔
              ∃ i : Fin (A.rank (xs 0).label.1),
                i.val = slot.val ∧ xs 1 = Node.child (xs 0) i
            constructor
            · rintro ⟨j, hj, hchild⟩
              obtain ⟨i, hij, hi⟩ :=
                (liftSOTreeNodeTo_child_iff mark (xs 0) (xs 1) j).mp hchild
              exact ⟨i, hij.trans hj, hi⟩
            · rintro ⟨i, hi, hchild⟩
              obtain ⟨j, hji, hj⟩ := liftSOTreeNodeTo_child_exists mark (xs 0) i
              refine ⟨j, hji.trans hi, ?_⟩
              rw [hchild]
              exact hj }

@[simp] theorem dropFOTree_liftFOTreeWith {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (mark : Node t → Bool) :
    dropFOTree (liftFOTreeWith t mark) = t := by
  induction t with
  | node s children ih =>
      simp only [liftFOTreeWith, dropFOTree, MarkedAlphabet.dropFO_liftFO,
        Tree.node.injEq, true_and]
      exact heq_of_eq (funext fun i => ih i (fun p => mark (.inChild i p)))

@[simp] theorem dropSOTree_liftSOTreeWith {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (mark : Node t → Bool) :
    dropSOTree (liftSOTreeWith t mark) = t := by
  induction t with
  | node s children ih =>
      simp only [liftSOTreeWith, dropSOTree, MarkedAlphabet.dropSO_liftSO,
        Tree.node.injEq, true_and]
      exact heq_of_eq (funext fun i => ih i (fun p => mark (.inChild i p)))

end Lax842588Proofs.MarkedTreeLifts
