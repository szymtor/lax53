import Lax53.TreeAutomataToMSO
import Lax53Proofs.MSOSemantics
import Lax53Proofs.TreeNodes

namespace Lax53Proofs.TreeAutomataToMSO

open FirstOrder
open FirstOrder.Language
open Lax52
open Lax52.MSOSyntax
open Lax52.MSOSemantics
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.TreeAutomaton

universe u v

namespace RunFormula

/-- A proposition decided while constructing the finite automaton formula. -/
noncomputable def holds {A : RankedAlphabet.{u}} {n m : Nat} (P : Prop) :
    Formula (treeSignature A) n m := by
  classical
  exact if P then .verum else .falsum

theorem realize_holds {A : RankedAlphabet.{u}} {n m : Nat} (P : Prop)
    {X : Type*} [((treeSignature A).Structure X)]
    (x : Fin n → X) (V : Fin m → Set X) :
    Realize (holds (A := A) P) x V ↔ P := by
  classical
  by_cases h : P <;> simp [holds, h]

/-- Finite disjunction indexed by `Fin k`. -/
def anyFin {A : RankedAlphabet.{u}} {n m : Nat} :
    (k : Nat) → (Fin k → Formula (treeSignature A) n m) →
      Formula (treeSignature A) n m
  | 0, _ => .falsum
  | k + 1, f => .or (f 0) (anyFin k (fun i => f i.succ))

/-- Finite conjunction indexed by `Fin k`. -/
def allFin {A : RankedAlphabet.{u}} {n m : Nat} :
    (k : Nat) → (Fin k → Formula (treeSignature A) n m) →
      Formula (treeSignature A) n m
  | 0, _ => .verum
  | k + 1, f => .and (f 0) (allFin k (fun i => f i.succ))

theorem realize_anyFin {A : RankedAlphabet.{u}} {n m k : Nat}
    (f : Fin k → Formula (treeSignature A) n m)
    {X : Type*} [((treeSignature A).Structure X)]
    (x : Fin n → X) (V : Fin m → Set X) :
    Realize (anyFin k f) x V ↔ ∃ i : Fin k, Realize (f i) x V := by
  induction k with
  | zero => simp [anyFin]
  | succ k ih =>
      simp only [anyFin, MSOSemantics.realize_or, ih]
      constructor
      · rintro (h | ⟨i, hi⟩)
        · exact ⟨0, h⟩
        · exact ⟨i.succ, hi⟩
      · rintro ⟨i, hi⟩
        obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
        · exact Or.inl hi
        · exact Or.inr ⟨j, hi⟩

theorem realize_allFin {A : RankedAlphabet.{u}} {n m k : Nat}
    (f : Fin k → Formula (treeSignature A) n m)
    {X : Type*} [((treeSignature A).Structure X)]
    (x : Fin n → X) (V : Fin m → Set X) :
    Realize (allFin k f) x V ↔ ∀ i : Fin k, Realize (f i) x V := by
  induction k with
  | zero => simp [allFin]
  | succ k ih =>
      simp only [allFin, MSOSemantics.realize_and, ih]
      constructor
      · rintro ⟨h0, hs⟩ i
        exact Fin.cases h0 (fun j => hs j) i
      · intro h
        exact ⟨h 0, fun i => h i.succ⟩

/-- Close every monadic variable. -/
def closeSO {A : RankedAlphabet.{u}} {n : Nat} :
    (m : Nat) → Formula (treeSignature A) n m → Formula (treeSignature A) n 0
  | 0, phi => phi
  | m + 1, phi => closeSO m (.exSO phi)

theorem realize_closeSO {A : RankedAlphabet.{u}} {n m : Nat}
    (phi : Formula (treeSignature A) n m)
    {X : Type*} [((treeSignature A).Structure X)] (x : Fin n → X) :
    Realize (closeSO m phi) x (fun i : Fin 0 => Fin.elim0 i) ↔
      ∃ V : Fin m → Set X, Realize phi x V := by
  induction m with
  | zero =>
      constructor
      · intro h
        exact ⟨fun i => Fin.elim0 i, h⟩
      · rintro ⟨V, h⟩
        simpa only [Subsingleton.elim V (fun i : Fin 0 => Fin.elim0 i)] using h
  | succ m ih =>
      rw [closeSO, ih]
      simp only [MSOSemantics.realize_exSO]
      constructor
      · rintro ⟨V, S, h⟩
        exact ⟨MSOSemantics.consVal S V, h⟩
      · rintro ⟨W, hW⟩
        let V : Fin m → Set X := fun i => W i.succ
        refine ⟨V, W 0, ?_⟩
        have hcons : MSOSemantics.consVal (W 0) V = W := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        rwa [hcons]

def var {A : RankedAlphabet.{u}} {n : Nat} (x : Fin n) :
    (treeSignature A).Term (Fin n) := .var x

def mem {A : RankedAlphabet.{u}} {n m : Nat} (x : Fin n) (X : Fin m) :
    Formula (treeSignature A) n m := .mem (var x) X

def label {A : RankedAlphabet.{u}} {n m : Nat} (a : A.Symbol) (x : Fin n) :
    Formula (treeSignature A) n m :=
  .rel (.label a) (fun _ => var x)

def child {A : RankedAlphabet.{u}} {n m : Nat} (i : ChildIndex A)
    (x y : Fin n) : Formula (treeSignature A) n m :=
  .rel (.child i) (fun j => Fin.cases (var x) (fun _ => var y) j)

theorem realize_mem {A : RankedAlphabet.{u}} {n m : Nat} (x : Fin n) (X : Fin m)
    {Y : Type*} [((treeSignature A).Structure Y)]
    (v : Fin n → Y) (V : Fin m → Set Y) :
    Realize (mem (A := A) x X) v V ↔ v x ∈ V X := Iff.rfl

theorem realize_label {A : RankedAlphabet.{u}} {t : Tree A} {n m : Nat}
    (a : A.Symbol) (x : Fin n) (v : Fin n → Node t)
    (V : Fin m → Set (Node t)) :
    @Realize _ (Node t) (treeStructure t) _ _ (label a x) v V ↔
      Node.label (v x) = a := Iff.rfl

theorem realize_child {A : RankedAlphabet.{u}} {t : Tree A} {n m : Nat}
    (i : ChildIndex A) (x y : Fin n) (v : Fin n → Node t)
    (V : Fin m → Set (Node t)) :
    @Realize _ (Node t) (treeStructure t) _ _ (child i x y) v V ↔
      Node.ChildAt i (v x) (v y) := Iff.rfl

/-- The fixed enumeration used to assign monadic variables to states. -/
noncomputable def enum (X : Type*) [Fintype X] : Fin (Fintype.card X) ≃ X :=
  (Fintype.equivFin X).symm

variable {A : RankedAlphabet.{u}} {Q : Type v} [Fintype Q]

def someState (x : Fin 1) :
    Formula (treeSignature A) 1 (Fintype.card Q) :=
  anyFin (Fintype.card Q) (fun q => mem x q)

noncomputable def uniqueState (x : Fin 1) :
    Formula (treeSignature A) 1 (Fintype.card Q) :=
  .and (someState x)
    (allFin (Fintype.card Q) fun q =>
      allFin (Fintype.card Q) fun r =>
        .imp (.and (mem x q) (mem x r)) (holds (q = r)))

noncomputable def partitionFormula :
    Formula (treeSignature A) 0 (Fintype.card Q) :=
  .allFO (uniqueState 0)

/-- A node carries a label, a state, and a tuple of child states forming an
automaton transition. -/
noncomputable def transitionAt (M : Automaton A Q) :
    Formula (treeSignature A) 1 (Fintype.card Q) :=
  allFin (Fintype.card A.Symbol) fun ai =>
    let a := enum A.Symbol ai
    .imp (label a 0) <|
      anyFin (Fintype.card Q) fun qi =>
        anyFin (Fintype.card (Fin (A.rank a) → Q)) fun si =>
          let qs := enum (Fin (A.rank a) → Q) si
          .and (mem 0 qi) <|
            .and (holds (M.transition a (enum Q qi) qs = true)) <|
              allFin (A.rank a) fun i =>
                .allFO (.imp
                  (child (ChildIndex.ofSymbolIndex a i) 1 0)
                  (mem 0 ((enum Q).symm (qs i))))

noncomputable def transitionFormula (M : Automaton A Q) :
    Formula (treeSignature A) 0 (Fintype.card Q) :=
  .allFO (transitionAt M)

/-- A node is the root when it is not a child in any symbol's child slot. -/
noncomputable def rootAt : Formula (treeSignature A) 1 (Fintype.card Q) :=
  allFin (Fintype.card A.Symbol) fun ai =>
    let a := enum A.Symbol ai
    allFin (A.rank a) fun i =>
      .allFO (.neg (child (ChildIndex.ofSymbolIndex a i) 0 1))

noncomputable def acceptingFormula (M : Automaton A Q) :
    Formula (treeSignature A) 0 (Fintype.card Q) :=
  .allFO (.imp rootAt <|
    anyFin (Fintype.card Q) fun qi =>
      .and (mem 0 qi) (holds (M.accept (enum Q qi) = true)))

noncomputable def runBody (M : Automaton A Q) :
    Formula (treeSignature A) 0 (Fintype.card Q) :=
  .and partitionFormula (.and (transitionFormula M) (acceptingFormula M))

noncomputable def runSentence (M : Automaton A Q) :
    MSOSyntax.Sentence (treeSignature A) := closeSO (Fintype.card Q) (runBody M)

def StatePartition {X : Type*} (V : Fin (Fintype.card Q) → Set X) : Prop :=
  ∀ x : X, ∃! qi : Fin (Fintype.card Q), x ∈ V qi

def TransitionCondition (M : Automaton A Q) (t : Tree A)
    (V : Fin (Fintype.card Q) → Set (Node t)) : Prop :=
  ∀ (p : Node t) (ai : Fin (Fintype.card A.Symbol)),
    p.label = enum A.Symbol ai →
      ∃ qi : Fin (Fintype.card Q),
        ∃ si : Fin (Fintype.card (Fin (A.rank (enum A.Symbol ai)) → Q)),
          let qs := enum (Fin (A.rank (enum A.Symbol ai)) → Q) si
          p ∈ V qi ∧ M.transition (enum A.Symbol ai) (enum Q qi) qs = true ∧
            ∀ (i : Fin (A.rank (enum A.Symbol ai))) (y : Node t),
              Node.ChildAt (ChildIndex.ofSymbolIndex (enum A.Symbol ai) i) p y →
                y ∈ V ((enum Q).symm (qs i))

def IsRoot {t : Tree A} (p : Node t) : Prop :=
  ∀ (ai : Fin (Fintype.card A.Symbol))
    (i : Fin (A.rank (enum A.Symbol ai))) (y : Node t),
      ¬Node.ChildAt (ChildIndex.ofSymbolIndex (enum A.Symbol ai) i) y p

def AcceptingCondition (M : Automaton A Q) (t : Tree A)
    (V : Fin (Fintype.card Q) → Set (Node t)) : Prop :=
  ∀ p : Node t, IsRoot p →
    ∃ qi : Fin (Fintype.card Q), p ∈ V qi ∧ M.accept (enum Q qi) = true

def RunValuation (M : Automaton A Q) (t : Tree A)
    (V : Fin (Fintype.card Q) → Set (Node t)) : Prop :=
  StatePartition V ∧ TransitionCondition M t V ∧ AcceptingCondition M t V

theorem realize_someState (x : Fin 1) {X : Type*}
    [((treeSignature A).Structure X)] (v : Fin 1 → X)
    (V : Fin (Fintype.card Q) → Set X) :
    Realize (someState (A := A) (Q := Q) x) v V ↔
      ∃ qi : Fin (Fintype.card Q), v x ∈ V qi := by
  simp [someState, realize_anyFin, realize_mem]

theorem realize_uniqueState (x : Fin 1) {X : Type*}
    [((treeSignature A).Structure X)] (v : Fin 1 → X)
    (V : Fin (Fintype.card Q) → Set X) :
    Realize (uniqueState (A := A) (Q := Q) x) v V ↔
      ∃! qi : Fin (Fintype.card Q), v x ∈ V qi := by
  simp only [uniqueState, MSOSemantics.realize_and, realize_someState,
    realize_allFin, MSOSemantics.realize_imp, realize_mem, realize_holds]
  constructor
  · rintro ⟨⟨qi, hqi⟩, hu⟩
    refine ⟨qi, hqi, ?_⟩
    intro ri hri
    exact hu ri qi ⟨hri, hqi⟩
  · rintro ⟨qi, hqi, hu⟩
    refine ⟨⟨qi, hqi⟩, ?_⟩
    intro ri si hrs
    exact (hu ri hrs.1).trans (hu si hrs.2).symm

theorem realize_partitionFormula (t : Tree A)
    (V : Fin (Fintype.card Q) → Set (Node t)) :
    @Realize _ (Node t) (treeStructure t) _ _
      (partitionFormula (A := A) (Q := Q))
      (fun i : Fin 0 => Fin.elim0 i) V ↔ StatePartition V := by
  simp only [partitionFormula, MSOSemantics.realize_allFO, realize_uniqueState]
  rfl

theorem realize_transitionAt (M : Automaton A Q) (t : Tree A) (p : Node t)
    (V : Fin (Fintype.card Q) → Set (Node t)) :
    @Realize _ (Node t) (treeStructure t) _ _ (transitionAt M)
      (fun _ : Fin 1 => p) V ↔
      ∀ ai : Fin (Fintype.card A.Symbol),
        p.label = enum A.Symbol ai →
          ∃ qi : Fin (Fintype.card Q),
            ∃ si : Fin (Fintype.card (Fin (A.rank (enum A.Symbol ai)) → Q)),
              let qs := enum (Fin (A.rank (enum A.Symbol ai)) → Q) si
              p ∈ V qi ∧ M.transition (enum A.Symbol ai) (enum Q qi) qs = true ∧
                ∀ (i : Fin (A.rank (enum A.Symbol ai))) (y : Node t),
                  Node.ChildAt (ChildIndex.ofSymbolIndex (enum A.Symbol ai) i) p y →
                    y ∈ V ((enum Q).symm (qs i)) := by
  simp only [transitionAt, realize_allFin, MSOSemantics.realize_imp,
    realize_label, realize_anyFin, MSOSemantics.realize_and, realize_mem,
    realize_holds, realize_allFin, MSOSemantics.realize_allFO, realize_child]
  rfl

theorem realize_transitionFormula (M : Automaton A Q) (t : Tree A)
    (V : Fin (Fintype.card Q) → Set (Node t)) :
    @Realize _ (Node t) (treeStructure t) _ _ (transitionFormula M)
      (fun i : Fin 0 => Fin.elim0 i) V ↔ TransitionCondition M t V := by
  simp only [transitionFormula, MSOSemantics.realize_allFO]
  constructor
  · intro h p
    have hv : MSOSemantics.consVal p (fun i : Fin 0 => Fin.elim0 i) =
        (fun _ : Fin 1 => p) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    exact (realize_transitionAt M t p V).mp (hv ▸ h p)
  · intro h p
    have hv : MSOSemantics.consVal p (fun i : Fin 0 => Fin.elim0 i) =
        (fun _ : Fin 1 => p) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]
    exact (realize_transitionAt M t p V).mpr (h p)

theorem realize_rootAt (t : Tree A) (p : Node t)
    (V : Fin (Fintype.card Q) → Set (Node t)) :
    @Realize _ (Node t) (treeStructure t) _ _ (rootAt (A := A) (Q := Q))
      (fun _ : Fin 1 => p) V ↔ IsRoot p := by
  simp only [rootAt, realize_allFin, MSOSemantics.realize_allFO,
    MSOSemantics.realize_neg, realize_child]
  rfl

theorem realize_acceptingFormula (M : Automaton A Q) (t : Tree A)
    (V : Fin (Fintype.card Q) → Set (Node t)) :
    @Realize _ (Node t) (treeStructure t) _ _ (acceptingFormula M)
      (fun i : Fin 0 => Fin.elim0 i) V ↔ AcceptingCondition M t V := by
  simp only [acceptingFormula, MSOSemantics.realize_allFO, MSOSemantics.realize_imp,
    realize_anyFin, MSOSemantics.realize_and, realize_mem, realize_holds]
  constructor
  · intro h p hp
    apply h p
    have := (realize_rootAt (Q := Q) t p V).mpr hp
    have hv : MSOSemantics.consVal p (fun i : Fin 0 => Fin.elim0 i) =
        (fun _ : Fin 1 => p) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rwa [hv]
  · intro h p hp
    apply h p
    apply (realize_rootAt (Q := Q) t p V).mp
    have hv : MSOSemantics.consVal p (fun i : Fin 0 => Fin.elim0 i) =
        (fun _ : Fin 1 => p) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rwa [← hv]

theorem realize_runBody (M : Automaton A Q) (t : Tree A)
    (V : Fin (Fintype.card Q) → Set (Node t)) :
    @Realize _ (Node t) (treeStructure t) _ _ (runBody M)
      (fun i : Fin 0 => Fin.elim0 i) V ↔ RunValuation M t V := by
  simp only [runBody, MSOSemantics.realize_and, realize_partitionFormula,
    realize_transitionFormula, realize_acceptingFormula, RunValuation]

theorem realize_runSentence (M : Automaton A Q) (t : Tree A) :
    TreeModels t (runSentence M) ↔
      ∃ V : Fin (Fintype.card Q) → Set (Node t), RunValuation M t V := by
  unfold TreeModels runSentence
  rw [realize_closeSO]
  apply exists_congr
  intro V
  exact realize_runBody M t V

theorem isRoot_iff_eq_root (t : Tree A) (p : Node t) :
    IsRoot p ↔ p = Node.rootOf t := by
  constructor
  · intro hp
    rcases Lax53Proofs.TreeNodes.root_or_exists_parent p with hroot | ⟨_, parent, hparent⟩
    · exact hroot
    · rcases hparent with ⟨j, _, hj⟩
      let ai := (enum A.Symbol).symm parent.label
      have ha : enum A.Symbol ai = parent.label := (enum A.Symbol).apply_symm_apply _
      let i : Fin (A.rank (enum A.Symbol ai)) := Fin.cast (congrArg A.rank ha).symm j
      exfalso
      apply hp ai i parent
      refine ⟨j, ?_, hj⟩
      apply Subtype.ext
      change j.val = i.val
      rfl
  · rintro rfl ai i parent hparent
    rcases hparent with ⟨j, _, hj⟩
    cases parent <;> simp [Node.rootOf, Node.child] at hj

/-- A state attached to every node is locally compatible when each node and
its child states form an automaton transition. -/
def LocallyCompatible (M : Automaton A Q) (t : Tree A) (r : Node t → Q) : Prop :=
  ∀ p : Node t,
    M.transition p.label (r p) (fun i => r (Node.child p i)) = true

def AcceptingLabeling (M : Automaton A Q) (t : Tree A) (r : Node t → Q) : Prop :=
  LocallyCompatible M t r ∧ M.accept (r (Node.rootOf t)) = true

noncomputable def stateIndex {t : Tree A}
    (V : Fin (Fintype.card Q) → Set (Node t))
    (hV : StatePartition V) (p : Node t) : Fin (Fintype.card Q) :=
  Classical.choose (hV p)

theorem mem_stateIndex {t : Tree A} (V : Fin (Fintype.card Q) → Set (Node t))
    (hV : StatePartition V) (p : Node t) : p ∈ V (stateIndex V hV p) :=
  Classical.choose_spec (hV p) |>.1

theorem stateIndex_eq {t : Tree A} (V : Fin (Fintype.card Q) → Set (Node t))
    (hV : StatePartition V) (p : Node t) (qi : Fin (Fintype.card Q))
    (hqi : p ∈ V qi) : qi = stateIndex V hV p :=
  Classical.choose_spec (hV p) |>.2 qi hqi

noncomputable def stateLabel {t : Tree A}
    (V : Fin (Fintype.card Q) → Set (Node t))
    (hV : StatePartition V) (p : Node t) : Q :=
  enum Q (stateIndex V hV p)

theorem runValuation_to_labeling (M : Automaton A Q) (t : Tree A)
    (V : Fin (Fintype.card Q) → Set (Node t)) (hV : RunValuation M t V) :
    AcceptingLabeling M t (stateLabel V hV.1) := by
  classical
  rcases hV with ⟨hpart, htrans, haccept⟩
  constructor
  · intro p
    let ai := (enum A.Symbol).symm p.label
    have ha : enum A.Symbol ai = p.label := (enum A.Symbol).apply_symm_apply _
    have hp := htrans p ai ha.symm
    rw [ha] at hp
    rcases hp with ⟨qi, si, hpV, hstep, hchildren⟩
    let qs : Fin (A.rank p.label) → Q := enum (Fin (A.rank p.label) → Q) si
    have hqi : qi = stateIndex V hpart p := stateIndex_eq V hpart p qi hpV
    have hchildStates : (fun i => stateLabel V hpart (Node.child p i)) = qs := by
      funext i
      have hmem := hchildren i (Node.child p i)
        (Lax53Proofs.TreeNodes.childAt_childNode p i)
      have hi := stateIndex_eq V hpart (Node.child p i) ((enum Q).symm (qs i)) hmem
      simp [stateLabel, ← hi]
    change M.transition p.label (stateLabel V hpart p)
      (fun i => stateLabel V hpart (Node.child p i)) = true
    rw [hchildStates]
    simpa [stateLabel, hqi, qs] using hstep
  · obtain ⟨qi, hrootV, haccept⟩ :=
      haccept (Node.rootOf t) ((isRoot_iff_eq_root t _).mpr rfl)
    have hqi := stateIndex_eq V hpart (Node.rootOf t) qi hrootV
    simpa [stateLabel, hqi] using haccept

theorem labeling_to_runValuation (M : Automaton A Q) (t : Tree A)
    (r : Node t → Q) (hr : AcceptingLabeling M t r) :
    ∃ V : Fin (Fintype.card Q) → Set (Node t), RunValuation M t V := by
  classical
  let V : Fin (Fintype.card Q) → Set (Node t) :=
    fun qi => {p | enum Q qi = r p}
  refine ⟨V, ?_, ?_, ?_⟩
  · intro p
    refine ⟨(enum Q).symm (r p), by simp [V], ?_⟩
    intro qi hqi
    exact (enum Q).injective (by simpa [V] using hqi)
  · intro p ai hlabel
    let qs : Fin (A.rank p.label) → Q := fun i => r (Node.child p i)
    have witness :
        ∃ qi : Fin (Fintype.card Q),
          ∃ si : Fin (Fintype.card (Fin (A.rank p.label) → Q)),
            let childStates := enum (Fin (A.rank p.label) → Q) si
            p ∈ V qi ∧ M.transition p.label (enum Q qi) childStates = true ∧
              ∀ (i : Fin (A.rank p.label)) (y : Node t),
                Node.ChildAt (ChildIndex.ofSymbolIndex p.label i) p y →
                  y ∈ V ((enum Q).symm (childStates i)) := by
      refine ⟨(enum Q).symm (r p), (enum (Fin (A.rank p.label) → Q)).symm qs,
        by simp [V], ?_, ?_⟩
      · simpa [qs] using hr.1 p
      · intro i y hy
        have hy' := (Lax53Proofs.TreeNodes.childAt_iff_eq_childNode p y i).mp hy
        subst y
        simp [V, qs]
    rw [← hlabel]
    exact witness
  · intro p hp
    have hproot := (isRoot_iff_eq_root t p).mp hp
    subst p
    refine ⟨(enum Q).symm (r (Node.rootOf t)), by simp [V], ?_⟩
    simpa using hr.2

theorem runValuation_iff_exists_acceptingLabeling (M : Automaton A Q) (t : Tree A) :
    (∃ V : Fin (Fintype.card Q) → Set (Node t), RunValuation M t V) ↔
      ∃ r : Node t → Q, AcceptingLabeling M t r := by
  constructor
  · rintro ⟨V, hV⟩
    exact ⟨stateLabel V hV.1, runValuation_to_labeling M t V hV⟩
  · rintro ⟨r, hr⟩
    exact labeling_to_runValuation M t r hr

omit [Fintype Q] in theorem runsTo_iff_exists_labeling
    (M : Automaton A Q) (t : Tree A) (q : Q) :
    M.RunsTo t q ↔
      ∃ r : Node t → Q,
        r (Node.rootOf t) = q ∧ LocallyCompatible M t r := by
  induction t generalizing q with
  | node a children ih =>
      constructor
      · rintro ⟨childStates, hstep, hruns⟩
        have hwitness : ∀ i : Fin (A.rank a),
            ∃ r : Node (children i) → Q,
              r (Node.rootOf (children i)) = childStates i ∧
                LocallyCompatible M (children i) r := by
          intro i
          exact (ih i (childStates i)).mp (hruns i)
        choose r hroot hlocal using hwitness
        let labeling : Node (.node a children) → Q
          | .root => q
          | .inChild i p => r i p
        refine ⟨labeling, rfl, ?_⟩
        intro p
        cases p with
        | root =>
            change M.transition a q (fun i => r i (Node.rootOf (children i))) = true
            rw [funext hroot]
            exact hstep
        | inChild i p =>
            simpa [labeling, Node.label, Node.child] using hlocal i p
      · rintro ⟨r, hroot, hlocal⟩
        let childStates : Fin (A.rank a) → Q :=
          fun i => r (Node.child (Node.root : Node (.node a children)) i)
        refine ⟨childStates, ?_, ?_⟩
        · have h := hlocal (Node.root : Node (.node a children))
          change r (Node.root : Node (.node a children)) = q at hroot
          rw [hroot] at h
          simpa [childStates, Node.label] using h
        · intro i
          apply (ih i (childStates i)).mpr
          let childLabeling : Node (children i) → Q := fun p => r (Node.inChild i p)
          refine ⟨childLabeling, ?_, ?_⟩
          · rfl
          · intro p
            have h := hlocal (Node.inChild i p)
            simpa [childLabeling, childStates, Node.label, Node.child] using h

omit [Fintype Q] in theorem exists_acceptingLabeling_iff_accepts
    (M : Automaton A Q) (t : Tree A) :
    (∃ r : Node t → Q, AcceptingLabeling M t r) ↔ M.Accepts t := by
  constructor
  · rintro ⟨r, hlocal, haccept⟩
    refine ⟨r (Node.rootOf t), haccept, ?_⟩
    exact (runsTo_iff_exists_labeling M t _).mpr ⟨r, rfl, hlocal⟩
  · rintro ⟨q, haccept, hrun⟩
    obtain ⟨r, hroot, hlocal⟩ := (runsTo_iff_exists_labeling M t q).mp hrun
    refine ⟨r, hlocal, ?_⟩
    rwa [hroot]

theorem runSentence_correct (M : Automaton A Q) (t : Tree A) :
    TreeModels t (runSentence M) ↔ M.Accepts t := by
  rw [realize_runSentence, runValuation_iff_exists_acceptingLabeling,
    exists_acceptingLabeling_iff_accepts]

end RunFormula

open RunFormula

/--
---
conclusion: Lax53.TreeAutomataToMSO.automaton_definable_by_mso
---
-/
theorem automaton_definable_by_mso_proof {A : RankedAlphabet.{u}} {Q : Type v}
    [Fintype Q] (M : Automaton A Q) :
    ∃ phi : MSOSyntax.Sentence (treeSignature A),
      M.language = sentenceLanguage phi := by
  refine ⟨runSentence M, ?_⟩
  ext t
  exact (runSentence_correct M t).symm

end Lax53Proofs.TreeAutomataToMSO
