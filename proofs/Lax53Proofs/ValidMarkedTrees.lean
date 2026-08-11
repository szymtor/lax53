import Mathlib.Data.Fintype.Pi
import Lax53Proofs.MarkedTrees

namespace Lax53Proofs.ValidMarkedTrees

open Lax53.RankedTree
open Lax53.TreeAutomaton
open Lax53Proofs.MarkedTrees

universe u

/-- The three occurrence counts relevant to first-order marker validity. -/
inductive OccurrenceCount
  | zero
  | one
  | many
  deriving DecidableEq

instance : Fintype OccurrenceCount where
  elems := {.zero, .one, .many}
  complete c := by cases c <;> simp

def NoOccurrence {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (x : Fin n) : Prop :=
  ∀ p : Node t, p.label.2.1 x = false

def OneOccurrence {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (x : Fin n) : Prop :=
  ∃! p : Node t, p.label.2.1 x = true

def Describes {A : RankedAlphabet.{u}} {n m : Nat}
    (c : OccurrenceCount) (t : Tree (MarkedAlphabet A n m)) (x : Fin n) : Prop :=
  match c with
  | .zero => NoOccurrence t x
  | .one => OneOccurrence t x
  | .many => ¬NoOccurrence t x ∧ ¬OneOccurrence t x

def zeroStep {k : Nat} (atRoot : Bool)
    (children : Fin k → OccurrenceCount) : Prop :=
  atRoot = false ∧ ∀ i, children i = .zero

def oneStep {k : Nat} (atRoot : Bool)
    (children : Fin k → OccurrenceCount) : Prop :=
  (atRoot = true ∧ ∀ i, children i = .zero) ∨
    (atRoot = false ∧ ∃ i, children i = .one ∧ ∀ j, j ≠ i → children j = .zero)

def ValidStep {k : Nat} (c : OccurrenceCount) (atRoot : Bool)
    (children : Fin k → OccurrenceCount) : Prop :=
  match c with
  | .zero => zeroStep atRoot children
  | .one => oneStep atRoot children
  | .many => ¬zeroStep atRoot children ∧ ¬oneStep atRoot children

theorem noOccurrence_node_iff {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n m).Symbol)
    (children : Fin ((MarkedAlphabet A n m).rank s) → Tree (MarkedAlphabet A n m))
    (x : Fin n) :
    NoOccurrence (.node s children) x ↔
      s.2.1 x = false ∧ ∀ i, NoOccurrence (children i) x := by
  constructor
  · intro h
    refine ⟨h .root, ?_⟩
    intro i p
    exact h (.inChild i p)
  · rintro ⟨hroot, hchildren⟩ p
    cases p with
    | root => exact hroot
    | inChild i p => exact hchildren i p

theorem oneOccurrence_node_iff {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n m).Symbol)
    (children : Fin ((MarkedAlphabet A n m).rank s) → Tree (MarkedAlphabet A n m))
    (x : Fin n) :
    OneOccurrence (.node s children) x ↔
      (s.2.1 x = true ∧ ∀ i, NoOccurrence (children i) x) ∨
      (s.2.1 x = false ∧
        ∃ i, OneOccurrence (children i) x ∧
          ∀ j, j ≠ i → NoOccurrence (children j) x) := by
  constructor
  · rintro ⟨p, hp, hu⟩
    cases p with
    | root =>
        left
        refine ⟨hp, ?_⟩
        intro i q
        cases hq : q.label.2.1 x with
        | false => rfl
        | true =>
            have := hu (.inChild i q) hq
            contradiction
    | inChild i p =>
        right
        refine ⟨?_, i, ?_, ?_⟩
        · cases hroot : s.2.1 x with
          | false => rfl
          | true =>
              have := hu .root hroot
              contradiction
        · refine ⟨p, hp, ?_⟩
          intro q hq
          have h := hu (.inChild i q) hq
          exact eq_of_heq (Node.inChild.inj h).2
        · intro j hji q
          cases hq : q.label.2.1 x with
          | false => rfl
          | true =>
              have h := hu (.inChild j q) hq
              have hij := Node.inChild.inj h
              exact False.elim (hji hij.1)
  · rintro (hroot | ⟨hroot, i, hi, hothers⟩)
    · refine ⟨Node.root, hroot.1, ?_⟩
      intro p hp
      cases p with
      | root => rfl
      | inChild i p =>
          have hfalse := hroot.2 i p
          have : false = true := hfalse.symm.trans hp
          exact False.elim (Bool.noConfusion this)
    · rcases hi with ⟨p, hp, hu⟩
      refine ⟨Node.inChild i p, hp, ?_⟩
      intro q hq
      cases q with
      | root =>
          have : false = true := hroot.symm.trans hq
          exact False.elim (Bool.noConfusion this)
      | inChild j q =>
          by_cases hji : j = i
          · subst j
            exact congrArg (Node.inChild i) (hu q hq)
          · have hfalse := hothers j hji q
            have : false = true := hfalse.symm.trans hq
            exact False.elim (Bool.noConfusion this)

noncomputable def classify {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (x : Fin n) : OccurrenceCount := by
  classical
  exact if NoOccurrence t x then .zero else if OneOccurrence t x then .one else .many

theorem describes_classify {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (x : Fin n) :
    Describes (classify t x) t x := by
  classical
  by_cases hzero : NoOccurrence t x
  · simp [classify, hzero, Describes]
  · by_cases hone : OneOccurrence t x
    · simp [classify, hzero, hone, Describes]
    · simp [classify, hzero, hone, Describes]

theorem one_not_noOccurrence {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} {x : Fin n}
    (hone : OneOccurrence t x) (hzero : NoOccurrence t x) : False := by
  rcases hone with ⟨p, hp, _⟩
  have : false = true := (hzero p).symm.trans hp
  exact Bool.noConfusion this

theorem describes_eq_zero_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} {x : Fin n} {c : OccurrenceCount}
    (hc : Describes c t x) : c = .zero ↔ NoOccurrence t x := by
  cases c with
  | zero => exact ⟨fun _ => hc, fun _ => rfl⟩
  | one => exact ⟨OccurrenceCount.noConfusion, fun hz => False.elim (one_not_noOccurrence hc hz)⟩
  | many => exact ⟨OccurrenceCount.noConfusion, fun hz => False.elim (hc.1 hz)⟩

theorem describes_eq_one_iff {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} {x : Fin n} {c : OccurrenceCount}
    (hc : Describes c t x) : c = .one ↔ OneOccurrence t x := by
  cases c with
  | zero => exact ⟨OccurrenceCount.noConfusion, fun ho => False.elim (one_not_noOccurrence ho hc)⟩
  | one => exact ⟨fun _ => hc, fun _ => rfl⟩
  | many => exact ⟨OccurrenceCount.noConfusion, fun ho => False.elim (hc.2 ho)⟩

theorem describes_node_iff_step {A : RankedAlphabet.{u}} {n m : Nat}
    (s : (MarkedAlphabet A n m).Symbol)
    (children : Fin ((MarkedAlphabet A n m).rank s) → Tree (MarkedAlphabet A n m))
    (childCounts : Fin ((MarkedAlphabet A n m).rank s) → OccurrenceCount)
    (x : Fin n) (hchildren : ∀ i, Describes (childCounts i) (children i) x)
    (c : OccurrenceCount) :
    Describes c (.node s children) x ↔ ValidStep c (s.2.1 x) (fun i => childCounts i) := by
  cases c with
  | zero =>
      rw [show Describes .zero (.node s children) x = NoOccurrence (.node s children) x by rfl]
      rw [noOccurrence_node_iff]
      simp only [ValidStep, zeroStep]
      apply and_congr Iff.rfl
      apply forall_congr'
      intro i
      exact (describes_eq_zero_iff (hchildren i)).symm
  | one =>
      rw [show Describes .one (.node s children) x = OneOccurrence (.node s children) x by rfl]
      rw [oneOccurrence_node_iff]
      simp only [ValidStep, oneStep]
      constructor
      · rintro (h | ⟨hroot, i, hi, hothers⟩)
        · left
          exact ⟨h.1, fun i => (describes_eq_zero_iff (hchildren i)).mpr (h.2 i)⟩
        · right
          refine ⟨hroot, i, ?_, ?_⟩
          · exact (describes_eq_one_iff (hchildren i)).mpr hi
          · intro j hji
            exact (describes_eq_zero_iff (hchildren j)).mpr (hothers j hji)
      · rintro (h | ⟨hroot, i, hi, hothers⟩)
        · left
          refine ⟨h.1, ?_⟩
          intro i
          exact (describes_eq_zero_iff (hchildren i)).mp (h.2 i)
        · right
          refine ⟨hroot, i, ?_, ?_⟩
          · exact (describes_eq_one_iff (hchildren i)).mp hi
          · intro j hji
            exact (describes_eq_zero_iff (hchildren j)).mp (hothers j hji)
  | many =>
      change (¬NoOccurrence (.node s children) x ∧
        ¬OneOccurrence (.node s children) x) ↔ _
      have hz : NoOccurrence (.node s children) x ↔
          zeroStep (s.2.1 x) (fun i => childCounts i) := by
        rw [noOccurrence_node_iff]
        exact and_congr Iff.rfl (forall_congr' fun i =>
          (describes_eq_zero_iff (hchildren i)).symm)
      have ho : OneOccurrence (.node s children) x ↔
          oneStep (s.2.1 x) (fun i => childCounts i) := by
        rw [oneOccurrence_node_iff]
        simp only [oneStep]
        constructor
        · rintro (h | ⟨hroot, i, hi, hothers⟩)
          · exact Or.inl ⟨h.1, fun i =>
              (describes_eq_zero_iff (hchildren i)).mpr (h.2 i)⟩
          · exact Or.inr ⟨hroot, i,
              (describes_eq_one_iff (hchildren i)).mpr hi,
              fun j hji => (describes_eq_zero_iff (hchildren j)).mpr (hothers j hji)⟩
        · rintro (h | ⟨hroot, i, hi, hothers⟩)
          · exact Or.inl ⟨h.1, fun i =>
              (describes_eq_zero_iff (hchildren i)).mp (h.2 i)⟩
          · exact Or.inr ⟨hroot, i,
              (describes_eq_one_iff (hchildren i)).mp hi,
              fun j hji => (describes_eq_zero_iff (hchildren j)).mp (hothers j hji)⟩
      simp only [ValidStep]
      rw [hz, ho]

/-- The bottom-up counter automaton for valid first-order marker tracks. -/
noncomputable def validMarkedAutomaton (A : RankedAlphabet.{u}) (n m : Nat) :
    Automaton (MarkedAlphabet A n m) (Fin n → OccurrenceCount) := by
  classical
  exact
    { transition := fun s parent children =>
        decide (∀ x, ValidStep (parent x) (s.2.1 x) (fun i => children i x))
      accept := fun state => decide (∀ x, state x = .one) }

theorem validMarked_runsTo_iff {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) (state : Fin n → OccurrenceCount) :
    (validMarkedAutomaton A n m).RunsTo t state ↔
      ∀ x, Describes (state x) t x := by
  classical
  induction t generalizing state with
  | node s children ih =>
      constructor
      · rintro ⟨childStates, hstep, hruns⟩ x
        have hs : ∀ x, ValidStep (state x) (s.2.1 x)
            (fun i => childStates i x) := by
          simpa [validMarkedAutomaton] using hstep
        apply (describes_node_iff_step s children (fun i => childStates i x) x
          (fun i => (ih i (childStates i)).mp (hruns i) x) (state x)).mpr
        exact hs x
      · intro hstate
        let childStates : Fin ((MarkedAlphabet A n m).rank s) →
            (Fin n → OccurrenceCount) := fun i x => classify (children i) x
        refine ⟨childStates, ?_, ?_⟩
        · change decide (∀ x, ValidStep (state x) (s.2.1 x)
            (fun i => childStates i x)) = true
          simp only [decide_eq_true_eq]
          intro x
          apply (describes_node_iff_step s children (fun i => childStates i x) x
            (fun i => describes_classify (children i) x) (state x)).mp
          exact hstate x
        · intro i
          apply (ih i (childStates i)).mpr
          exact fun x => describes_classify (children i) x

theorem represents_iff_oneOccurrence {A : RankedAlphabet.{u}} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) :
    (∃ (v : Fin n → Node t) (V : Fin m → Set (Node t)), Represents t v V) ↔
      ∀ x, OneOccurrence t x := by
  classical
  constructor
  · rintro ⟨v, V, hv, hV⟩ x
    refine ⟨v x, (hv (v x) x).mpr rfl, ?_⟩
    intro p hp
    exact (hv p x).mp hp |>.symm
  · intro h
    let v : Fin n → Node t := fun x => Classical.choose (h x)
    let V : Fin m → Set (Node t) := fun X => {p | p.label.2.2 X = true}
    refine ⟨v, V, ?_, ?_⟩
    · intro p x
      constructor
      · exact fun hp => (Classical.choose_spec (h x)).2 p hp |>.symm
      · rintro rfl
        exact Classical.choose_spec (h x) |>.1
    · intro p X
      rfl

theorem validMarkedAutomaton_correct (A : RankedAlphabet.{u}) (n m : Nat) :
    (validMarkedAutomaton A n m).language = validMarkedLanguage A n m := by
  ext t
  change (validMarkedAutomaton A n m).Accepts t ↔ _
  change (validMarkedAutomaton A n m).Accepts t ↔
    ∃ (v : Fin n → Node t) (V : Fin m → Set (Node t)), Represents t v V
  rw [represents_iff_oneOccurrence]
  constructor
  · rintro ⟨state, haccept, hrun⟩ x
    have hs : ∀ x, state x = .one := by
      simpa [validMarkedAutomaton] using haccept
    have hd := (validMarked_runsTo_iff t state).mp hrun x
    simpa [hs x, Describes] using hd
  · intro h
    let state : Fin n → OccurrenceCount := fun _ => .one
    refine ⟨state, by simp [validMarkedAutomaton, state], ?_⟩
    apply (validMarked_runsTo_iff t state).mpr
    intro x
    simpa [state, Describes] using h x

theorem validMarked_recognizable (A : RankedAlphabet.{u}) (n m : Nat) :
    Recognizable (validMarkedLanguage A n m) :=
  ⟨Fin n → OccurrenceCount, inferInstance, validMarkedAutomaton A n m,
    validMarkedAutomaton_correct A n m⟩

end Lax53Proofs.ValidMarkedTrees
