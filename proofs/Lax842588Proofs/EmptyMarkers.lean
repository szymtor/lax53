import Lax842588Proofs.MSOFormulaToTreeAutomata

namespace Lax842588Proofs.EmptyMarkers

open FirstOrder
open FirstOrder.Language
open Lax146103.MSOSyntax
open Lax146103.MSOSemantics
open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588.TreeStructure
open Lax842588Proofs.MarkedTrees

universe u v

def emptyMarkNodeTo {A : RankedAlphabet.{u}} :
    {t : Tree A} → Node (emptyMark t) → Node t
  | .node _ _, .root => .root
  | .node _ _, .inChild i p => .inChild i (emptyMarkNodeTo p)

def emptyMarkNodeFrom {A : RankedAlphabet.{u}} :
    {t : Tree A} → Node t → Node (emptyMark t)
  | .node _ _, .root => .root
  | .node _ _, .inChild i p => .inChild i (emptyMarkNodeFrom p)

@[simp] theorem emptyMarkNodeTo_from {A : RankedAlphabet.{u}}
    {t : Tree A} (p : Node t) : emptyMarkNodeTo (emptyMarkNodeFrom p) = p := by
  induction p with
  | root => rfl
  | inChild i p ih => exact congrArg (Node.inChild i) ih

@[simp] theorem emptyMarkNodeFrom_to {A : RankedAlphabet.{u}}
    {t : Tree A} (p : Node (emptyMark t)) : emptyMarkNodeFrom (emptyMarkNodeTo p) = p := by
  induction t with
  | node a children ih =>
      cases p with
      | root => rfl
      | inChild i p =>
          simpa only [emptyMarkNodeFrom, emptyMarkNodeTo] using! congrArg
            (@Node.inChild (MarkedAlphabet A 0 0)
              (a, fun x => Fin.elim0 x, fun X => Fin.elim0 X)
              (fun j => emptyMark (children j)) i) (ih i p)

def emptyMarkNodeEquiv {A : RankedAlphabet.{u}} (t : Tree A) :
    Node (emptyMark t) ≃ Node t where
  toFun := emptyMarkNodeTo
  invFun := emptyMarkNodeFrom
  left_inv := emptyMarkNodeFrom_to
  right_inv := emptyMarkNodeTo_from

@[simp] theorem emptyMarkNodeTo_label {A : RankedAlphabet.{u}}
    {t : Tree A} (p : Node (emptyMark t)) :
    (emptyMarkNodeTo p).label = p.label.1 := by
  induction t with
  | node a children ih =>
      cases p with
      | root => rfl
      | inChild i p => exact ih i p

@[simp] theorem emptyMarkNodeTo_rootOf {A : RankedAlphabet.{u}} (t : Tree A) :
    emptyMarkNodeTo (Node.rootOf (emptyMark t)) = Node.rootOf t := by
  cases t
  rfl

theorem emptyMarkNodeTo_child_exists {A : RankedAlphabet.{u}} {t : Tree A}
    (p : Node (emptyMark t)) (i : Fin (A.rank p.label.1)) :
    ∃ j : Fin (A.rank (emptyMarkNodeTo p).label),
      j.val = i.val ∧
        emptyMarkNodeTo (Node.child p i) = Node.child (emptyMarkNodeTo p) j := by
  induction t with
  | node a children ih =>
    cases p with
    | root =>
      refine ⟨i, rfl, ?_⟩
      exact congrArg (@Node.inChild A a children i)
        (emptyMarkNodeTo_rootOf (children i))
    | inChild k p =>
      obtain ⟨j, hval, hchild⟩ := ih k p i
      exact ⟨j, hval, congrArg (@Node.inChild A a children k) hchild⟩

theorem emptyMarkNodeTo_child_iff {A : RankedAlphabet.{u}} {t : Tree A}
    (p q : Node (emptyMark t))
    (j : Fin (A.rank (emptyMarkNodeTo p).label)) :
    emptyMarkNodeTo q = Node.child (emptyMarkNodeTo p) j ↔
      ∃ i : Fin (A.rank p.label.1), i.val = j.val ∧ q = Node.child p i := by
  constructor
  · intro hq
    let i : Fin (A.rank p.label.1) :=
      ⟨j.val, by simpa only [emptyMarkNodeTo_label] using j.isLt⟩
    obtain ⟨j', hval, hchild⟩ := emptyMarkNodeTo_child_exists p i
    have hj' : j' = j := Fin.ext hval
    subst j'
    refine ⟨i, rfl, ?_⟩
    apply (emptyMarkNodeEquiv t).injective
    exact hq.trans hchild.symm
  · rintro ⟨i, hval, rfl⟩
    obtain ⟨j', hval', hchild⟩ := emptyMarkNodeTo_child_exists p i
    have hj' : j' = j := Fin.ext (hval'.trans hval)
    subst j'
    exact hchild

def emptyMarkStructureEquiv {A : RankedAlphabet.{u}} (t : Tree A) :
    @Language.Equiv (treeSignature A) (Node (emptyMark t)) (Node t)
      (@markedStructure A 0 0 (emptyMark t)) (treeStructure t) := by
  letI : (treeSignature A).Structure (Node (emptyMark t)) := markedStructure (emptyMark t)
  letI : (treeSignature A).Structure (Node t) := treeStructure t
  exact
    { toEquiv := emptyMarkNodeEquiv t
      map_fun' := by
        intro _ f
        exact nomatch f
      map_rel' := by
        intro _ r xs
        cases r with
        | label a =>
            change (emptyMarkNodeTo (xs 0)).label = a ↔ (xs 0).label.1 = a
            rw [emptyMarkNodeTo_label]
        | child slot =>
            change
              (∃ j : Fin (A.rank (emptyMarkNodeTo (xs 0)).label),
                ChildIndex.ofSymbolIndex (emptyMarkNodeTo (xs 0)).label j = slot ∧
                  emptyMarkNodeTo (xs 1) = Node.child (emptyMarkNodeTo (xs 0)) j) ↔
              ∃ i : Fin (A.rank (xs 0).label.1),
                i.val = slot.val ∧ xs 1 = Node.child (xs 0) i
            constructor
            · rintro ⟨j, hj, hchild⟩
              obtain ⟨i, hij, hi⟩ :=
                (emptyMarkNodeTo_child_iff (xs 0) (xs 1) j).mp hchild
              exact ⟨i, hij.trans (congrArg Subtype.val hj), hi⟩
            · rintro ⟨i, hi, hchild⟩
              obtain ⟨j, hji, hj⟩ := emptyMarkNodeTo_child_exists (xs 0) i
              refine ⟨j, ?_, ?_⟩
              · apply Subtype.ext
                exact hji.trans hi
              rw [hchild]
              exact hj }

theorem emptyMark_represents {A : RankedAlphabet.{u}} (t : Tree A) :
    Represents (emptyMark t)
      (fun x : Fin 0 => Fin.elim0 x) (fun X : Fin 0 => Fin.elim0 X) := by
  constructor <;> intro _ i <;> exact Fin.elim0 i

/-- Closed formulas have the same semantics on a tree and its uniquely
zero-marked copy. -/
theorem emptyMark_mem_formulaLanguage_iff {A : RankedAlphabet.{u}}
    (t : Tree A) (phi : Lax146103.MSOSyntax.Sentence (treeSignature A)) :
    emptyMark t ∈ formulaLanguage phi ↔ TreeModels t phi := by
  let emptyNode : Fin 0 → Node (emptyMark t) := fun i => Fin.elim0 i
  let emptySet : Fin 0 → Set (Node (emptyMark t)) := fun i => Fin.elim0 i
  let targetNode : Fin 0 → Node t := fun i => Fin.elim0 i
  let targetSet : Fin 0 → Set (Node t) := fun i => Fin.elim0 i
  letI : (treeSignature A).Structure (Node (emptyMark t)) := markedStructure (emptyMark t)
  letI : (treeSignature A).Structure (Node t) := treeStructure t
  let e := emptyMarkStructureEquiv t
  have hsem : MarkedRealize (emptyMark t) phi emptyNode emptySet ↔ TreeModels t phi := by
    have hvmap : e ∘ emptyNode = targetNode := by
      funext i
      exact Fin.elim0 i
    have hVmap : (fun X => e '' emptySet X) = targetSet := by
      funext X
      exact Fin.elim0 X
    have h := (Lax842588Proofs.MSOSemantics.realize_equiv e phi emptyNode emptySet).symm
    change @Realize _ _ (markedStructure (emptyMark t)) _ _ phi emptyNode emptySet ↔
      @Realize _ _ (treeStructure t) _ _ phi targetNode targetSet
    simpa only [hvmap, hVmap] using h
  constructor
  · rintro ⟨v, V, _, hphi⟩
    have hv : v = emptyNode := by funext i; exact Fin.elim0 i
    have hV : V = emptySet := by funext i; exact Fin.elim0 i
    subst v
    subst V
    exact hsem.mp hphi
  · intro hphi
    exact ⟨emptyNode, emptySet, emptyMark_represents t, hsem.mpr hphi⟩

/-- Pull an automaton on zero-marked symbols back to the original alphabet. -/
def unmarkAutomaton {A : RankedAlphabet.{u}} {Q : Type v}
    (M : Automaton (MarkedAlphabet A 0 0) Q) : Automaton A Q where
  transition a q children :=
    M.transition (a, fun i => Fin.elim0 i, fun i => Fin.elim0 i) q children
  accept := M.accept

theorem unmarkAutomaton_runsTo_iff {A : RankedAlphabet.{u}} {Q : Type v}
    (M : Automaton (MarkedAlphabet A 0 0) Q) (t : Tree A) (q : Q) :
    (unmarkAutomaton M).RunsTo t q ↔ M.RunsTo (emptyMark t) q := by
  induction t generalizing q with
  | node a children ih =>
      constructor
      · rintro ⟨states, hstep, hruns⟩
        exact ⟨states, hstep, fun i => (ih i (states i)).mp (hruns i)⟩
      · rintro ⟨states, hstep, hruns⟩
        exact ⟨states, hstep, fun i => (ih i (states i)).mpr (hruns i)⟩

theorem unmarkAutomaton_accepts_iff {A : RankedAlphabet.{u}} {Q : Type v}
    (M : Automaton (MarkedAlphabet A 0 0) Q) (t : Tree A) :
    (unmarkAutomaton M).Accepts t ↔ M.Accepts (emptyMark t) := by
  constructor
  · rintro ⟨q, hq, hrun⟩
    exact ⟨q, hq, (unmarkAutomaton_runsTo_iff M t q).mp hrun⟩
  · rintro ⟨q, hq, hrun⟩
    exact ⟨q, hq, (unmarkAutomaton_runsTo_iff M t q).mpr hrun⟩

end Lax842588Proofs.EmptyMarkers
