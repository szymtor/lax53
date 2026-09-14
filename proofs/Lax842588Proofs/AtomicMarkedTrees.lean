import Lax842588Proofs.MSOSemantics
import Lax842588Proofs.TreeAutomataClosure
import Lax842588Proofs.ValidMarkedTrees

namespace Lax842588Proofs.AtomicMarkedTrees

open FirstOrder
open FirstOrder.Language
open Lax146103.MSOSyntax
open Lax146103.MSOSemantics
open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588.TreeStructure
open Lax842588Proofs.MarkedTrees
open Lax842588Proofs.TreeAutomataClosure

universe u

def Somewhere {A : RankedAlphabet.{u}} {n m : Nat}
    (pred : (MarkedAlphabet A n m).Symbol → Bool)
    (t : Tree (MarkedAlphabet A n m)) : Prop :=
  ∃ p : Node t, pred p.label = true

noncomputable def somewhereAutomaton {A : RankedAlphabet.{u}} {n m : Nat}
    (pred : (MarkedAlphabet A n m).Symbol → Bool) :
    Automaton (MarkedAlphabet A n m) Bool := by
  classical
  exact
    { transition := fun s parent children =>
        decide (parent = (pred s || decide (∃ i, children i = true)))
      accept := fun state => state }

theorem somewhere_runsTo_iff {A : RankedAlphabet.{u}} {n m : Nat}
    (pred : (MarkedAlphabet A n m).Symbol → Bool)
    (t : Tree (MarkedAlphabet A n m)) (state : Bool) :
    (somewhereAutomaton pred).RunsTo t state ↔
      (state = true ↔ Somewhere pred t) := by
  classical
  induction t generalizing state with
  | node s children ih =>
      constructor
      · rintro ⟨childStates, hstep, hruns⟩
        have heq : state = (pred s || decide (∃ i, childStates i = true)) := by
          simpa [somewhereAutomaton] using hstep
        rw [heq, Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (hroot | ⟨i, hi⟩)
          · exact ⟨Node.root, hroot⟩
          · have hchild := (ih i (childStates i)).mp (hruns i)
            obtain ⟨p, hp⟩ := hchild.mp hi
            exact ⟨Node.inChild i p, hp⟩
        · rintro ⟨p, hp⟩
          cases p with
          | root => exact Or.inl hp
          | inChild i p =>
              right
              refine ⟨i, ?_⟩
              exact ((ih i (childStates i)).mp (hruns i)).mpr ⟨p, hp⟩
      · intro hstate
        let childStates : Fin ((MarkedAlphabet A n m).rank s) → Bool :=
          fun i => decide (Somewhere pred (children i))
        refine ⟨childStates, ?_, ?_⟩
        · change decide (state =
            (pred s || decide (∃ i, childStates i = true))) = true
          simp only [decide_eq_true_eq]
          have hnode : Somewhere pred (.node s children) ↔
              pred s = true ∨ ∃ i, Somewhere pred (children i) := by
            constructor
            · rintro ⟨p, hp⟩
              cases p with
              | root => exact Or.inl hp
              | inChild i p => exact Or.inr ⟨i, p, hp⟩
            · rintro (hroot | ⟨i, p, hp⟩)
              · exact ⟨Node.root, hroot⟩
              · exact ⟨Node.inChild i p, hp⟩
          apply Bool.eq_iff_iff.mpr
          refine hstate.trans ?_
          simp only [Bool.or_eq_true, decide_eq_true_eq, childStates,
            decide_eq_true_eq]
          exact hnode
        · intro i
          apply (ih i (childStates i)).mpr
          simp [childStates]

theorem somewhere_accepts_iff {A : RankedAlphabet.{u}} {n m : Nat}
    (pred : (MarkedAlphabet A n m).Symbol → Bool)
    (t : Tree (MarkedAlphabet A n m)) :
    (somewhereAutomaton pred).Accepts t ↔ Somewhere pred t := by
  constructor
  · rintro ⟨state, haccept, hrun⟩
    change state = true at haccept
    exact ((somewhere_runsTo_iff pred t state).mp hrun).mp haccept
  · intro h
    refine ⟨true, rfl, ?_⟩
    exact (somewhere_runsTo_iff pred t true).mpr ⟨fun _ => h, fun _ => rfl⟩

theorem somewhere_recognizable {A : RankedAlphabet.{u}} {n m : Nat}
    (pred : (MarkedAlphabet A n m).Symbol → Bool) :
    Recognizable {t | Somewhere pred t} := by
  refine ⟨Bool, inferInstance, somewhereAutomaton pred, ?_⟩
  ext t
  exact somewhere_accepts_iff pred t

def bothFO {A : RankedAlphabet.{u}} {n m : Nat} (x y : Fin n) :
    (MarkedAlphabet A n m).Symbol → Bool := fun s => s.2.1 x && s.2.1 y

def foSO {A : RankedAlphabet.{u}} {n m : Nat} (x : Fin n) (X : Fin m) :
    (MarkedAlphabet A n m).Symbol → Bool := fun s => s.2.1 x && s.2.2 X

noncomputable def labelFO {A : RankedAlphabet.{u}} {n m : Nat}
    (a : A.Symbol) (x : Fin n) :
    (MarkedAlphabet A n m).Symbol → Bool := by
  classical
  exact fun s => decide (s.1 = a) && s.2.1 x

theorem represented_somewhere_bothFO_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} {v : Fin n → Node t}
    {V : Fin m → Set (Node t)} (h : Represents t v V) (x y : Fin n) :
    Somewhere (bothFO (A := A) (m := m) x y) t ↔ v x = v y := by
  rcases h with ⟨hv, _⟩
  constructor
  · rintro ⟨p, hp⟩
    simp only [bothFO, Bool.and_eq_true] at hp
    exact (hv p x).mp hp.1 |>.trans ((hv p y).mp hp.2).symm
  · intro hxy
    refine ⟨v x, ?_⟩
    simp only [bothFO, Bool.and_eq_true]
    exact ⟨(hv (v x) x).mpr rfl, (hv (v x) y).mpr hxy.symm⟩

theorem represented_somewhere_foSO_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} {v : Fin n → Node t}
    {V : Fin m → Set (Node t)} (h : Represents t v V) (x : Fin n) (X : Fin m) :
    Somewhere (foSO (A := A) x X) t ↔ v x ∈ V X := by
  rcases h with ⟨hv, hV⟩
  constructor
  · rintro ⟨p, hp⟩
    simp only [foSO, Bool.and_eq_true] at hp
    rw [(hv p x).mp hp.1]
    exact (hV p X).mp hp.2
  · intro hx
    refine ⟨v x, ?_⟩
    simp only [foSO, Bool.and_eq_true]
    exact ⟨(hv (v x) x).mpr rfl, (hV (v x) X).mpr hx⟩

theorem represented_somewhere_labelFO_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} {v : Fin n → Node t}
    {V : Fin m → Set (Node t)} (h : Represents t v V)
    (a : A.Symbol) (x : Fin n) :
    Somewhere (labelFO (m := m) a x) t ↔ (v x).label.1 = a := by
  rcases h with ⟨hv, _⟩
  constructor
  · rintro ⟨p, hp⟩
    simp only [labelFO, Bool.and_eq_true, decide_eq_true_eq] at hp
    rw [(hv p x).mp hp.2]
    exact hp.1
  · intro ha
    refine ⟨v x, ?_⟩
    simp only [labelFO, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨ha, (hv (v x) x).mpr rfl⟩

def EdgeSomewhere {A : RankedAlphabet.{u}} {n m : Nat}
    (slot : ChildIndex A) (x y : Fin n)
    (t : Tree (MarkedAlphabet A n m)) : Prop :=
  ∃ (p q : Node t), p.label.2.1 x = true ∧ q.label.2.1 y = true ∧
    ∃ i : Fin (A.rank p.label.1), i.val = slot.val ∧ q = Node.child p i

abbrev EdgeState (n : Nat) := (Fin n → Bool) × Bool

noncomputable def edgeAutomaton {A : RankedAlphabet.{u}} {n m : Nat}
    (slot : ChildIndex A) (x y : Fin n) :
    Automaton (MarkedAlphabet A n m) (EdgeState n) := by
  classical
  exact
    { transition := fun s parent children =>
        decide (parent.1 = s.2.1 ∧
          (parent.2 = true ↔
            (∃ i, (children i).2 = true) ∨
            (s.2.1 x = true ∧
              ∃ i, i.val = slot.val ∧ (children i).1 y = true)))
      accept := fun state => state.2 }

theorem edgeSomewhere_node_iff {A : RankedAlphabet.{u}} {n m : Nat}
    (slot : ChildIndex A) (x y : Fin n)
    (s : (MarkedAlphabet A n m).Symbol)
    (children : Fin ((MarkedAlphabet A n m).rank s) → Tree (MarkedAlphabet A n m)) :
    EdgeSomewhere slot x y (.node s children) ↔
      (∃ i, EdgeSomewhere slot x y (children i)) ∨
      (s.2.1 x = true ∧
        ∃ i, i.val = slot.val ∧ (Node.rootOf (children i)).label.2.1 y = true) := by
  constructor
  · rintro ⟨p, q, hpx, hqy, i, hi, hchild⟩
    cases p with
    | root =>
        right
        cases q with
        | root => contradiction
        | inChild j q =>
            simp only [Node.child] at hchild
            have hj := Node.inChild.inj hchild
            cases hj.1
            have hqroot : q = Node.rootOf (children i) := eq_of_heq hj.2
            subst q
            exact ⟨hpx, i, hi, hqy⟩
    | inChild j p =>
        left
        cases q with
        | root => contradiction
        | inChild k q =>
            simp only [Node.child] at hchild
            have hjk := Node.inChild.inj hchild
            cases hjk.1
            have hq : q = Node.child p i := eq_of_heq hjk.2
            exact ⟨j, p, q, hpx, hqy, i, hi, hq⟩
  · rintro (hchild | ⟨hx, i, hi, hy⟩)
    · rcases hchild with ⟨j, p, q, hx, hy, i, hi, hpq⟩
      exact ⟨Node.inChild j p, Node.inChild j q, hx, hy, i, hi,
        congrArg (Node.inChild j) hpq⟩
    · exact ⟨Node.root, Node.inChild i (Node.rootOf (children i)), hx, hy,
        i, hi, rfl⟩

theorem edge_runsTo_iff {A : RankedAlphabet.{u}} {n m : Nat}
    (slot : ChildIndex A) (x y : Fin n)
    (t : Tree (MarkedAlphabet A n m)) (state : EdgeState n) :
    (edgeAutomaton (m := m) slot x y).RunsTo t state ↔
      state.1 = (Node.rootOf t).label.2.1 ∧
        (state.2 = true ↔ EdgeSomewhere slot x y t) := by
  classical
  induction t generalizing state with
  | node s children ih =>
      constructor
      · rintro ⟨childStates, hstep, hruns⟩
        have hs : state.1 = s.2.1 ∧
            (state.2 = true ↔
              (∃ i, (childStates i).2 = true) ∨
              (s.2.1 x = true ∧ ∃ i, i.val = slot.val ∧
                (childStates i).1 y = true)) := by
          change decide (state.1 = s.2.1 ∧
            (state.2 = true ↔
              (∃ i, (childStates i).2 = true) ∨
              (s.2.1 x = true ∧ ∃ i, i.val = slot.val ∧
                (childStates i).1 y = true))) = true at hstep
          exact of_decide_eq_true hstep
        refine ⟨hs.1, ?_⟩
        rw [hs.2, edgeSomewhere_node_iff]
        apply or_congr
        · constructor
          · rintro ⟨i, hi⟩
            exact ⟨i, ((ih i (childStates i)).mp (hruns i)).2.mp hi⟩
          · rintro ⟨i, hi⟩
            exact ⟨i, ((ih i (childStates i)).mp (hruns i)).2.mpr hi⟩
        · apply and_congr Iff.rfl
          constructor
          · rintro ⟨i, hi, hmark⟩
            have hroot := ((ih i (childStates i)).mp (hruns i)).1
            exact ⟨i, hi, by simpa [hroot] using hmark⟩
          · rintro ⟨i, hi, hmark⟩
            have hroot := ((ih i (childStates i)).mp (hruns i)).1
            exact ⟨i, hi, by simpa [hroot] using hmark⟩
      · rintro ⟨hroot, hfound⟩
        let childStates : Fin ((MarkedAlphabet A n m).rank s) → EdgeState n :=
          fun i => ((Node.rootOf (children i)).label.2.1,
            decide (EdgeSomewhere slot x y (children i)))
        refine ⟨childStates, ?_, ?_⟩
        · change decide (state.1 = s.2.1 ∧
            (state.2 = true ↔
              (∃ i, (childStates i).2 = true) ∨
              (s.2.1 x = true ∧ ∃ i, i.val = slot.val ∧
                (childStates i).1 y = true))) = true
          apply decide_eq_true_eq.mpr
          refine ⟨hroot, ?_⟩
          rw [hfound, edgeSomewhere_node_iff]
          simp only [childStates, decide_eq_true_eq]
        · intro i
          apply (ih i (childStates i)).mpr
          exact ⟨rfl, by simp [childStates]⟩

theorem edge_accepts_iff {A : RankedAlphabet.{u}} {n m : Nat}
    (slot : ChildIndex A) (x y : Fin n) (t : Tree (MarkedAlphabet A n m)) :
    (edgeAutomaton (m := m) slot x y).Accepts t ↔ EdgeSomewhere slot x y t := by
  constructor
  · rintro ⟨state, haccept, hrun⟩
    change state.2 = true at haccept
    exact ((edge_runsTo_iff (m := m) slot x y t state).mp hrun).2.mp haccept
  · intro h
    let state : EdgeState n := ((Node.rootOf t).label.2.1, true)
    refine ⟨state, rfl, ?_⟩
    apply (edge_runsTo_iff (m := m) slot x y t state).mpr
    exact ⟨rfl, ⟨fun _ => h, fun _ => rfl⟩⟩

theorem edge_recognizable {A : RankedAlphabet.{u}} {n m : Nat}
    (slot : ChildIndex A) (x y : Fin n) :
    Recognizable {t | EdgeSomewhere (m := m) slot x y t} := by
  refine ⟨EdgeState n, inferInstance, edgeAutomaton (m := m) slot x y, ?_⟩
  ext t
  exact edge_accepts_iff (m := m) slot x y t

theorem represented_edge_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} {v : Fin n → Node t}
    {V : Fin m → Set (Node t)} (h : Represents t v V)
    (slot : ChildIndex A) (x y : Fin n) :
    EdgeSomewhere slot x y t ↔
      ∃ i : Fin (A.rank (v x).label.1),
        i.val = slot.val ∧ v y = Node.child (v x) i := by
  rcases h with ⟨hv, _⟩
  constructor
  · rintro ⟨p, q, hpx, hqy, i, hi, hpq⟩
    have hpx' := (hv p x).mp hpx
    have hqy' := (hv q y).mp hqy
    subst p
    subst q
    exact ⟨i, hi, hpq⟩
  · rintro ⟨i, hi, hpq⟩
    exact ⟨v x, v y, (hv (v x) x).mpr rfl, (hv (v y) y).mpr rfl,
      i, hi, hpq⟩

theorem formulaLanguage_equal_eq {A : RankedAlphabet.{u}} {n m : Nat}
    (t₁ t₂ : (treeSignature A).Term (Fin n)) :
    formulaLanguage (Formula.equal (m := m) t₁ t₂) =
      validMarkedLanguage A n m ∩
        {t | Somewhere (bothFO (A := A) (m := m)
          (treeTermVar t₁) (treeTermVar t₂)) t} := by
  ext t
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    letI := markedStructure t
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    apply (represented_somewhere_bothFO_iff hrep
      (treeTermVar t₁) (treeTermVar t₂)).mpr
    change t₁.realize v = t₂.realize v at hreal
    simpa only [treeTerm_realize] using hreal
  · rintro ⟨⟨v, V, hrep⟩, hsome⟩
    letI := markedStructure t
    refine ⟨v, V, hrep, ?_⟩
    change t₁.realize v = t₂.realize v
    simpa only [treeTerm_realize] using
      (represented_somewhere_bothFO_iff hrep
        (treeTermVar t₁) (treeTermVar t₂)).mp hsome

theorem formulaLanguage_mem_eq {A : RankedAlphabet.{u}} {n m : Nat}
    (t₁ : (treeSignature A).Term (Fin n)) (X : Fin m) :
    formulaLanguage (Formula.mem t₁ X) = validMarkedLanguage A n m ∩
      {t | Somewhere (foSO (A := A) (treeTermVar t₁) X) t} := by
  ext t
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    letI := markedStructure t
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    apply (represented_somewhere_foSO_iff hrep (treeTermVar t₁) X).mpr
    change t₁.realize v ∈ V X at hreal
    simpa only [treeTerm_realize] using hreal
  · rintro ⟨⟨v, V, hrep⟩, hsome⟩
    letI := markedStructure t
    refine ⟨v, V, hrep, ?_⟩
    change t₁.realize v ∈ V X
    simpa only [treeTerm_realize] using
      (represented_somewhere_foSO_iff hrep (treeTermVar t₁) X).mp hsome

theorem formulaLanguage_label_eq {A : RankedAlphabet.{u}} {n m : Nat}
    (a : A.Symbol) (ts : Fin 1 → (treeSignature A).Term (Fin n)) :
    formulaLanguage (Formula.rel (m := m) (.label a) ts) =
      validMarkedLanguage A n m ∩
        {t | Somewhere (labelFO (m := m) a (treeTermVar (ts 0))) t} := by
  ext t
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    letI := markedStructure t
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    apply (represented_somewhere_labelFO_iff hrep a (treeTermVar (ts 0))).mpr
    change ((ts 0).realize v).label.1 = a at hreal
    simpa only [treeTerm_realize] using hreal
  · rintro ⟨⟨v, V, hrep⟩, hsome⟩
    letI := markedStructure t
    refine ⟨v, V, hrep, ?_⟩
    change ((ts 0).realize v).label.1 = a
    simpa only [treeTerm_realize] using
      (represented_somewhere_labelFO_iff hrep a (treeTermVar (ts 0))).mp hsome

theorem formulaLanguage_child_eq {A : RankedAlphabet.{u}} {n m : Nat}
    (slot : ChildIndex A) (ts : Fin 2 → (treeSignature A).Term (Fin n)) :
    formulaLanguage (Formula.rel (m := m) (.child slot) ts) =
      validMarkedLanguage A n m ∩ {t | EdgeSomewhere (m := m) slot
        (treeTermVar (ts 0)) (treeTermVar (ts 1)) t} := by
  ext t
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    letI := markedStructure t
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    apply (represented_edge_iff hrep slot
      (treeTermVar (ts 0)) (treeTermVar (ts 1))).mpr
    change ∃ i : Fin (A.rank ((ts 0).realize v).label.1),
      i.val = slot.val ∧ (ts 1).realize v = Node.child ((ts 0).realize v) i at hreal
    have h₀ : (ts 0).realize v = v (treeTermVar (ts 0)) := treeTerm_realize _ _
    have h₁ : (ts 1).realize v = v (treeTermVar (ts 1)) := treeTerm_realize _ _
    rw [h₀, h₁] at hreal
    exact hreal
  · rintro ⟨⟨v, V, hrep⟩, hedge⟩
    letI := markedStructure t
    refine ⟨v, V, hrep, ?_⟩
    change ∃ i : Fin (A.rank ((ts 0).realize v).label.1),
      i.val = slot.val ∧ (ts 1).realize v = Node.child ((ts 0).realize v) i
    have h₀ : (ts 0).realize v = v (treeTermVar (ts 0)) := treeTerm_realize _ _
    have h₁ : (ts 1).realize v = v (treeTermVar (ts 1)) := treeTerm_realize _ _
    rw [h₀, h₁]
    exact (represented_edge_iff hrep slot
      (treeTermVar (ts 0)) (treeTermVar (ts 1))).mp hedge

theorem formulaLanguage_falsum_recognizable {A : RankedAlphabet.{u}} {n m : Nat} :
    Recognizable (formulaLanguage
      (Formula.falsum : Formula (treeSignature A) n m)) := by
  have hempty : formulaLanguage
      (Formula.falsum : Formula (treeSignature A) n m) = ∅ := by
    ext t
    constructor
    · rintro ⟨v, V, hrep, hfalse⟩
      exact hfalse
    · simp
  rw [hempty]
  exact recognizable_empty

theorem formulaLanguage_equal_recognizable {A : RankedAlphabet.{u}} {n m : Nat}
    (t₁ t₂ : (treeSignature A).Term (Fin n)) :
    Recognizable (formulaLanguage (Formula.equal (m := m) t₁ t₂)) := by
  let x := treeTermVar t₁
  let y := treeTermVar t₂
  have hlang : formulaLanguage (Formula.equal (m := m) t₁ t₂) =
      validMarkedLanguage A n m ∩ {t | Somewhere (bothFO (A := A) (m := m) x y) t} := by
    ext t
    constructor
    · rintro ⟨v, V, hrep, hreal⟩
      letI := markedStructure t
      refine ⟨⟨v, V, hrep⟩, ?_⟩
      apply (represented_somewhere_bothFO_iff hrep x y).mpr
      change t₁.realize v = t₂.realize v at hreal
      simpa only [x, y, treeTerm_realize] using hreal
    · rintro ⟨⟨v, V, hrep⟩, hsome⟩
      letI := markedStructure t
      refine ⟨v, V, hrep, ?_⟩
      change t₁.realize v = t₂.realize v
      simpa only [x, y, treeTerm_realize] using
        (represented_somewhere_bothFO_iff hrep x y).mp hsome
  rw [hlang]
  exact recognizable_intersection _ _
    (Lax842588Proofs.ValidMarkedTrees.validMarked_recognizable A n m)
    (somewhere_recognizable _)

theorem formulaLanguage_mem_recognizable {A : RankedAlphabet.{u}} {n m : Nat}
    (t₁ : (treeSignature A).Term (Fin n)) (X : Fin m) :
    Recognizable (formulaLanguage (Formula.mem t₁ X)) := by
  let x := treeTermVar t₁
  have hlang : formulaLanguage (Formula.mem t₁ X) =
      validMarkedLanguage A n m ∩ {t | Somewhere (foSO (A := A) x X) t} := by
    ext t
    constructor
    · rintro ⟨v, V, hrep, hreal⟩
      letI := markedStructure t
      refine ⟨⟨v, V, hrep⟩, ?_⟩
      apply (represented_somewhere_foSO_iff hrep x X).mpr
      change t₁.realize v ∈ V X at hreal
      simpa only [x, treeTerm_realize] using hreal
    · rintro ⟨⟨v, V, hrep⟩, hsome⟩
      letI := markedStructure t
      refine ⟨v, V, hrep, ?_⟩
      change t₁.realize v ∈ V X
      simpa only [x, treeTerm_realize] using
        (represented_somewhere_foSO_iff hrep x X).mp hsome
  rw [hlang]
  exact recognizable_intersection _ _
    (Lax842588Proofs.ValidMarkedTrees.validMarked_recognizable A n m)
    (somewhere_recognizable _)

theorem formulaLanguage_label_recognizable {A : RankedAlphabet.{u}} {n m : Nat}
    (a : A.Symbol) (ts : Fin 1 → (treeSignature A).Term (Fin n)) :
    Recognizable (formulaLanguage (Formula.rel (m := m) (.label a) ts)) := by
  let x := treeTermVar (ts 0)
  have hlang : formulaLanguage (Formula.rel (m := m) (.label a) ts) =
      validMarkedLanguage A n m ∩ {t | Somewhere (labelFO (m := m) a x) t} := by
    ext t
    constructor
    · rintro ⟨v, V, hrep, hreal⟩
      letI := markedStructure t
      refine ⟨⟨v, V, hrep⟩, ?_⟩
      apply (represented_somewhere_labelFO_iff hrep a x).mpr
      change ((ts 0).realize v).label.1 = a at hreal
      simpa only [x, treeTerm_realize] using hreal
    · rintro ⟨⟨v, V, hrep⟩, hsome⟩
      letI := markedStructure t
      refine ⟨v, V, hrep, ?_⟩
      change ((ts 0).realize v).label.1 = a
      simpa only [x, treeTerm_realize] using
        (represented_somewhere_labelFO_iff hrep a x).mp hsome
  rw [hlang]
  exact recognizable_intersection _ _
    (Lax842588Proofs.ValidMarkedTrees.validMarked_recognizable A n m)
    (somewhere_recognizable _)

theorem formulaLanguage_child_recognizable {A : RankedAlphabet.{u}} {n m : Nat}
    (slot : ChildIndex A) (ts : Fin 2 → (treeSignature A).Term (Fin n)) :
    Recognizable (formulaLanguage (Formula.rel (m := m) (.child slot) ts)) := by
  let x := treeTermVar (ts 0)
  let y := treeTermVar (ts 1)
  have hlang : formulaLanguage (Formula.rel (m := m) (.child slot) ts) =
      validMarkedLanguage A n m ∩ {t | EdgeSomewhere (m := m) slot x y t} := by
    ext t
    constructor
    · rintro ⟨v, V, hrep, hreal⟩
      letI := markedStructure t
      refine ⟨⟨v, V, hrep⟩, ?_⟩
      apply (represented_edge_iff hrep slot x y).mpr
      change ∃ i : Fin (A.rank ((ts 0).realize v).label.1),
        i.val = slot.val ∧ (ts 1).realize v = Node.child ((ts 0).realize v) i at hreal
      have h₀ : (ts 0).realize v = v x := by simpa only [x] using treeTerm_realize (ts 0) v
      have h₁ : (ts 1).realize v = v y := by simpa only [y] using treeTerm_realize (ts 1) v
      rw [h₀, h₁] at hreal
      exact hreal
    · rintro ⟨⟨v, V, hrep⟩, hedge⟩
      letI := markedStructure t
      refine ⟨v, V, hrep, ?_⟩
      change ∃ i : Fin (A.rank ((ts 0).realize v).label.1),
        i.val = slot.val ∧ (ts 1).realize v = Node.child ((ts 0).realize v) i
      have h₀ : (ts 0).realize v = v x := by simpa only [x] using treeTerm_realize (ts 0) v
      have h₁ : (ts 1).realize v = v y := by simpa only [y] using treeTerm_realize (ts 1) v
      rw [h₀, h₁]
      exact (represented_edge_iff hrep slot x y).mp hedge
  rw [hlang]
  exact recognizable_intersection _ _
    (Lax842588Proofs.ValidMarkedTrees.validMarked_recognizable A n m)
    (edge_recognizable (m := m) slot x y)

end Lax842588Proofs.AtomicMarkedTrees
