import Lax53.MSOToTreeAutomata

namespace Lax53Proofs.MarkedTrees

open FirstOrder
open FirstOrder.Language
open Lax52.MSOSyntax
open Lax52.MSOSemantics
open Lax53.RankedTree
open Lax53.TreeStructure

universe u

/-- A ranked symbol decorated with Boolean tracks for first-order and monadic
variables. The decoration does not change its rank. -/
def MarkedAlphabet (A : RankedAlphabet.{u}) (n m : Nat) : RankedAlphabet.{u} where
  Symbol := A.Symbol × (Fin n → Bool) × (Fin m → Bool)
  symbolsFintype := inferInstance
  symbolsDecidableEq := inferInstance
  rank s := A.rank s.1

namespace MarkedAlphabet

def underlying {A : RankedAlphabet.{u}} {n m : Nat} :
    (MarkedAlphabet A n m).Symbol → A.Symbol := fun s => s.1

def fo {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n m).Symbol) : Fin n → Bool := s.2.1

def so {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n m).Symbol) : Fin m → Bool := s.2.2

/-- Forget the newest first-order marker (index zero). -/
def dropFO {A : RankedAlphabet.{u}} {n m : Nat} :
    (MarkedAlphabet A (n + 1) m).Symbol → (MarkedAlphabet A n m).Symbol :=
  fun s => ⟨s.1, fun x => s.2.1 x.succ, s.2.2⟩

/-- Forget the newest monadic marker (index zero). -/
def dropSO {A : RankedAlphabet.{u}} {n m : Nat} :
    (MarkedAlphabet A n (m + 1)).Symbol → (MarkedAlphabet A n m).Symbol :=
  fun s => ⟨s.1, s.2.1, fun X => s.2.2 X.succ⟩

/-- Add a chosen newest first-order bit. -/
def liftFO {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n m).Symbol) (bit : Bool) :
    (MarkedAlphabet A (n + 1) m).Symbol :=
  ⟨s.1, Fin.cases bit s.2.1, s.2.2⟩

/-- Add a chosen newest monadic bit. -/
def liftSO {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n m).Symbol) (bit : Bool) :
    (MarkedAlphabet A n (m + 1)).Symbol :=
  ⟨s.1, s.2.1, Fin.cases bit s.2.2⟩

@[simp] theorem dropFO_liftFO {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n m).Symbol) (bit : Bool) :
    dropFO (liftFO s bit) = s := by
  rcases s with ⟨a, fo, so⟩
  simp [dropFO, liftFO]

@[simp] theorem dropSO_liftSO {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n m).Symbol) (bit : Bool) :
    dropSO (liftSO s bit) = s := by
  rcases s with ⟨a, fo, so⟩
  simp [dropSO, liftSO]

@[simp] theorem liftFO_dropFO_zero {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A (n + 1) m).Symbol) :
    liftFO (dropFO s) (s.2.1 0) = s := by
  rcases s with ⟨a, fo, so⟩
  simp only [liftFO, dropFO]
  congr 2
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem liftSO_dropSO_zero {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n (m + 1)).Symbol) :
    liftSO (dropSO s) (s.2.2 0) = s := by
  rcases s with ⟨a, fo, so⟩
  simp only [liftSO, dropSO]
  congr 2
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end MarkedAlphabet

/-- The underlying ranked-tree relations on a decorated tree. -/
@[implicit_reducible]
def markedStructure {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) :
    (treeSignature A).Structure (Node t) where
  funMap f := nomatch f
  RelMap
    | .label a, xs => (xs 0).label.1 = a
    | .child i, xs =>
        ∃ j : Fin (A.rank (xs 0).label.1),
          j.val = i.val ∧ xs 1 = Node.child (xs 0) j

/-- A decorated tree exactly represents the supplied valuations. -/
def Represents {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m))
    (v : Fin n → Node t) (V : Fin m → Set (Node t)) : Prop :=
  (∀ (p : Node t) (x : Fin n), p.label.2.1 x = true ↔ v x = p) ∧
  (∀ (p : Node t) (X : Fin m), p.label.2.2 X = true ↔ p ∈ V X)

/-- Satisfaction using the underlying ranked-tree relations and the
valuations recorded by the Boolean tracks. -/
def MarkedRealize {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m))
    (phi : Formula (treeSignature A) n m)
    (v : Fin n → Node t) (V : Fin m → Set (Node t)) : Prop :=
  @Realize (treeSignature A) (Node t) (markedStructure t) n m phi v V

/-- The valid marked encodings whose represented valuations satisfy a
formula. -/
def formulaLanguage {A : RankedAlphabet.{u}} {n m : Nat}
    (phi : Formula (treeSignature A) n m) : TreeLanguage (MarkedAlphabet A n m) :=
  {t | ∃ (v : Fin n → Node t) (V : Fin m → Set (Node t)),
    Represents t v V ∧ MarkedRealize t phi v V}

/-- All valid marked encodings. Only first-order tracks need a uniqueness
condition; monadic tracks represent arbitrary node sets. -/
def validMarkedLanguage (A : RankedAlphabet.{u}) (n m : Nat) :
    TreeLanguage (MarkedAlphabet A n m) :=
  {t | ∃ (v : Fin n → Node t) (V : Fin m → Set (Node t)), Represents t v V}

/-- The uniquely decorated copy of an undecorated tree with no variable
tracks. -/
def emptyMark {A : RankedAlphabet.{u}} : Tree A → Tree (MarkedAlphabet A 0 0)
  | .node a children =>
      .node ⟨a, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
        (fun i => emptyMark (children i))

/-- Erase every variable track. -/
def erase {A : RankedAlphabet.{u}} {n m : Nat} :
    Tree (MarkedAlphabet A n m) → Tree A
  | .node s children => .node s.1 (fun i => erase (children i))

/-- Forget the newest first-order marker throughout a tree. -/
def dropFOTree {A : RankedAlphabet.{u}} {n m : Nat} :
    Tree (MarkedAlphabet A (n + 1) m) → Tree (MarkedAlphabet A n m)
  | .node s children => .node (MarkedAlphabet.dropFO s)
      (fun i => dropFOTree (children i))

/-- Forget the newest monadic marker throughout a tree. -/
def dropSOTree {A : RankedAlphabet.{u}} {n m : Nat} :
    Tree (MarkedAlphabet A n (m + 1)) → Tree (MarkedAlphabet A n m)
  | .node s children => .node (MarkedAlphabet.dropSO s)
      (fun i => dropSOTree (children i))

def dropFONode {A : RankedAlphabet.{u}} {n m : Nat} :
    {t : Tree (MarkedAlphabet A (n + 1) m)} → Node t → Node (dropFOTree t)
  | .node _ _, .root => .root
  | .node _ _, .inChild i p => .inChild i (dropFONode p)

def liftFONode {A : RankedAlphabet.{u}} {n m : Nat} :
    {t : Tree (MarkedAlphabet A (n + 1) m)} → Node (dropFOTree t) → Node t
  | .node _ _, .root => .root
  | .node _ _, .inChild i p => .inChild i (liftFONode p)

def dropSONode {A : RankedAlphabet.{u}} {n m : Nat} :
    {t : Tree (MarkedAlphabet A n (m + 1))} → Node t → Node (dropSOTree t)
  | .node _ _, .root => .root
  | .node _ _, .inChild i p => .inChild i (dropSONode p)

def liftSONode {A : RankedAlphabet.{u}} {n m : Nat} :
    {t : Tree (MarkedAlphabet A n (m + 1))} → Node (dropSOTree t) → Node t
  | .node _ _, .root => .root
  | .node _ _, .inChild i p => .inChild i (liftSONode p)

@[simp] theorem dropFONode_rootOf {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A (n + 1) m)) :
    dropFONode (Node.rootOf t) = Node.rootOf (dropFOTree t) := by
  cases t
  rfl

@[simp] theorem dropSONode_rootOf {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n (m + 1))) :
    dropSONode (Node.rootOf t) = Node.rootOf (dropSOTree t) := by
  cases t
  rfl

@[simp] theorem liftFONode_dropFONode {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A (n + 1) m)} (p : Node t) :
    liftFONode (dropFONode p) = p := by
  induction p with
  | root => rfl
  | inChild i p ih =>
      change Node.inChild i (liftFONode (dropFONode p)) = Node.inChild i p
      exact congrArg (Node.inChild i) ih

@[simp] theorem dropFONode_liftFONode {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A (n + 1) m)} (p : Node (dropFOTree t)) :
    dropFONode (liftFONode p) = p := by
  induction t with
  | node s children ih =>
      cases p with
      | root => rfl
      | inChild i p =>
          simpa only [dropFONode, liftFONode] using congrArg
            (@Node.inChild (MarkedAlphabet A n m) (MarkedAlphabet.dropFO s)
              (fun j => dropFOTree (children j)) i) (ih i p)

@[simp] theorem liftSONode_dropSONode {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n (m + 1))} (p : Node t) :
    liftSONode (dropSONode p) = p := by
  induction p with
  | root => rfl
  | inChild i p ih =>
      change Node.inChild i (liftSONode (dropSONode p)) = Node.inChild i p
      exact congrArg (Node.inChild i) ih

@[simp] theorem dropSONode_liftSONode {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n (m + 1))} (p : Node (dropSOTree t)) :
    dropSONode (liftSONode p) = p := by
  induction t with
  | node s children ih =>
      cases p with
      | root => rfl
      | inChild i p =>
          simpa only [dropSONode, liftSONode] using congrArg
            (@Node.inChild (MarkedAlphabet A n m) (MarkedAlphabet.dropSO s)
              (fun j => dropSOTree (children j)) i) (ih i p)

def dropFONodeEquiv {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A (n + 1) m)) : Node t ≃ Node (dropFOTree t) where
  toFun := dropFONode
  invFun := liftFONode
  left_inv := liftFONode_dropFONode
  right_inv := dropFONode_liftFONode

def dropSONodeEquiv {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n (m + 1))) : Node t ≃ Node (dropSOTree t) where
  toFun := dropSONode
  invFun := liftSONode
  left_inv := liftSONode_dropSONode
  right_inv := dropSONode_liftSONode

@[simp] theorem dropFONode_label {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A (n + 1) m)} (p : Node t) :
    (dropFONode p).label = MarkedAlphabet.dropFO p.label := by
  induction p with
  | root => rfl
  | inChild i p ih => exact ih

@[simp] theorem dropSONode_label {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n (m + 1))} (p : Node t) :
    (dropSONode p).label = MarkedAlphabet.dropSO p.label := by
  induction p with
  | root => rfl
  | inChild i p ih => exact ih

theorem dropFONode_child_exists {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A (n + 1) m)}
    (p : Node t) (i : Fin (A.rank p.label.1)) :
    ∃ j : Fin (A.rank (dropFONode p).label.1),
      j.val = i.val ∧ dropFONode (Node.child p i) = Node.child (dropFONode p) j := by
  induction p with
  | @root s children =>
      let j : Fin (A.rank (dropFONode (Node.root : Node (.node s children))).label.1) :=
        ⟨i.val, by simpa only [dropFONode_label, MarkedAlphabet.dropFO] using i.isLt⟩
      refine ⟨j, rfl, ?_⟩
      have hji : j = i := Fin.ext rfl
      rw [hji]
      exact congrArg
        (@Node.inChild (MarkedAlphabet A n m) (MarkedAlphabet.dropFO s)
          (fun l => dropFOTree (children l)) i) (dropFONode_rootOf (children i))
  | @inChild s children k p ih =>
      obtain ⟨j, hval, hchild⟩ := ih i
      refine ⟨j, hval, ?_⟩
      exact congrArg
        (@Node.inChild (MarkedAlphabet A n m) (MarkedAlphabet.dropFO s)
          (fun l => dropFOTree (children l)) k) hchild

theorem dropSONode_child_exists {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n (m + 1))}
    (p : Node t) (i : Fin (A.rank p.label.1)) :
    ∃ j : Fin (A.rank (dropSONode p).label.1),
      j.val = i.val ∧ dropSONode (Node.child p i) = Node.child (dropSONode p) j := by
  induction p with
  | @root s children =>
      let j : Fin (A.rank (dropSONode (Node.root : Node (.node s children))).label.1) :=
        ⟨i.val, by simpa only [dropSONode_label, MarkedAlphabet.dropSO] using i.isLt⟩
      refine ⟨j, rfl, ?_⟩
      have hji : j = i := Fin.ext rfl
      rw [hji]
      exact congrArg
        (@Node.inChild (MarkedAlphabet A n m) (MarkedAlphabet.dropSO s)
          (fun l => dropSOTree (children l)) i) (dropSONode_rootOf (children i))
  | @inChild s children k p ih =>
      obtain ⟨j, hval, hchild⟩ := ih i
      refine ⟨j, hval, ?_⟩
      exact congrArg
        (@Node.inChild (MarkedAlphabet A n m) (MarkedAlphabet.dropSO s)
          (fun l => dropSOTree (children l)) k) hchild

theorem dropFONode_child_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A (n + 1) m)} (p q : Node t)
    (j : Fin (A.rank (dropFONode p).label.1)) :
    dropFONode q = Node.child (dropFONode p) j ↔
      ∃ i : Fin (A.rank p.label.1), i.val = j.val ∧ q = Node.child p i := by
  constructor
  · intro hq
    let i : Fin (A.rank p.label.1) :=
      ⟨j.val, by simpa only [dropFONode_label, MarkedAlphabet.dropFO] using j.isLt⟩
    obtain ⟨j', hval, hchild⟩ := dropFONode_child_exists p i
    have hj' : j' = j := Fin.ext hval
    subst j'
    refine ⟨i, rfl, ?_⟩
    apply (dropFONodeEquiv t).injective
    exact hq.trans hchild.symm
  · rintro ⟨i, hval, rfl⟩
    obtain ⟨j', hval', hchild⟩ := dropFONode_child_exists p i
    have hj' : j' = j := Fin.ext (hval'.trans hval)
    subst j'
    exact hchild

theorem dropSONode_child_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n (m + 1))} (p q : Node t)
    (j : Fin (A.rank (dropSONode p).label.1)) :
    dropSONode q = Node.child (dropSONode p) j ↔
      ∃ i : Fin (A.rank p.label.1), i.val = j.val ∧ q = Node.child p i := by
  constructor
  · intro hq
    let i : Fin (A.rank p.label.1) :=
      ⟨j.val, by simpa only [dropSONode_label, MarkedAlphabet.dropSO] using j.isLt⟩
    obtain ⟨j', hval, hchild⟩ := dropSONode_child_exists p i
    have hj' : j' = j := Fin.ext hval
    subst j'
    refine ⟨i, rfl, ?_⟩
    apply (dropSONodeEquiv t).injective
    exact hq.trans hchild.symm
  · rintro ⟨i, hval, rfl⟩
    obtain ⟨j', hval', hchild⟩ := dropSONode_child_exists p i
    have hj' : j' = j := Fin.ext (hval'.trans hval)
    subst j'
    exact hchild

@[simp] theorem erase_emptyMark {A : RankedAlphabet.{u}} (t : Tree A) :
    erase (emptyMark t) = t := by
  induction t with
  | node a children ih =>
      simp only [emptyMark, erase, Tree.node.injEq, heq_eq_eq]
      exact ⟨True.intro, funext ih⟩

/-- In the function-free tree signature every term is a variable. -/
def treeTermVar {A : RankedAlphabet.{u}} {n : Nat} :
    (treeSignature A).Term (Fin n) → Fin n
  | .var x => x
  | .func f _ => nomatch f

@[simp] theorem treeTerm_eq_var {A : RankedAlphabet.{u}} {n : Nat}
    (t : (treeSignature A).Term (Fin n)) : t = .var (treeTermVar t) := by
  cases t with
  | var x => rfl
  | func f _ => exact nomatch f

@[simp] theorem treeTerm_realize {A : RankedAlphabet.{u}} {n : Nat}
    {X : Type*} [((treeSignature A).Structure X)]
    (t : (treeSignature A).Term (Fin n)) (v : Fin n → X) :
    t.realize v = v (treeTermVar t) := by
  rw [treeTerm_eq_var t]
  rfl

end Lax53Proofs.MarkedTrees
