import Lax842588Proofs.FiniteWordStates
import Lax842588Proofs.MarkedAlphabetEncoding
import Lax842588Proofs.AtomicMarkedTrees

namespace Lax842588Proofs.EncodedAtomicAutomata

open Lax842588.ValueTranslations
open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588Proofs.FiniteAutomatonEncoding
open Lax842588Proofs.FiniteWordStates
open Lax842588Proofs.MarkedAlphabetEncoding
open Lax842588Proofs.MarkedTrees
open Lax842588Proofs.ValidMarkedTrees
open Lax842588Proofs.AtomicMarkedTrees
open Lax842588Proofs.EncodedProjection

def occurrenceFin : OccurrenceCount ≃ Fin 3 where
  toFun
    | .zero => 0
    | .one => 1
    | .many => 2
  invFun i := if i = 0 then .zero else if i = 1 then .one else .many
  left_inv c := by cases c <;> rfl
  right_inv i := by
    rcases i with ⟨i, hi⟩
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> rfl

abbrev ValidState (n : Nat) := WordState 3 n
abbrev EdgeCodeState (n : Nat) := WordState 2 (n + 1)

def validStateEquiv (n : Nat) :
    ValidState n ≃ (Fin n → OccurrenceCount) :=
  (wordStateEquiv 3 n).trans
    (Equiv.arrowCongr (Equiv.refl _) occurrenceFin.symm)

def splitLastEquiv (n : Nat) :
    (Fin (n + 1) → Bool) ≃ (Fin n → Bool) × Bool where
  toFun f := (fun i => f i.castSucc, f (Fin.last n))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv p := by
    ext i <;> simp

def edgeStateEquiv (n : Nat) : EdgeCodeState n ≃ EdgeState n :=
  (wordStateEquiv 2 (n + 1)).trans <|
    (Equiv.arrowCongr (Equiv.refl _) boolFin.symm).trans (splitLastEquiv n)

def fin? (i n : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨i, h⟩ else none

instance {k : Nat} (c : OccurrenceCount) (atRoot : Bool)
    (children : Fin k → OccurrenceCount) : Decidable (ValidStep c atRoot children) := by
  cases c <;> simp only [ValidStep, zeroStep, oneStep] <;> infer_instance

@[simp] theorem fin?_fin {n : Nat} (i : Fin n) : fin? i.val n = some i := by
  simp [fin?, i.isLt]

def validCode (alphabet : RankedAlphabetCode) (n m : Nat) : AutomatonCode :=
  FiniteAutomatonEncoding.encode (code alphabet n m) (words 3 n).length
      (fun a q children =>
      match fin? a (code alphabet n m).length,
          fin? q (words 3 n).length with
      | some a, some q =>
          if hlen : children.length =
              (code alphabet n m).toRankedAlphabet.rank a then
            decide (∀ x, ValidStep ((validStateEquiv n q) x)
              ((fromCodeSymbol alphabet n m a).2.1 x)
              (fun (i : Fin ((code alphabet n m).toRankedAlphabet.rank a)) =>
                match fin? (children.get (Fin.cast hlen.symm i)) (words 3 n).length with
                | some child => (validStateEquiv n child) x
                | none => .many))
          else false
        | _, _ => false)
      (fun q =>
        match fin? q (words 3 n).length with
        | some q => decide (∀ x, validStateEquiv n q x = .one)
        | none => false)

def somewhereCode (alphabet : RankedAlphabetCode) (n m : Nat)
    (pred : MarkedSymbol alphabet n m → Bool) : AutomatonCode :=
  FiniteAutomatonEncoding.encode (code alphabet n m) 2
      (fun a q children =>
      match fin? a (code alphabet n m).length with
      | some a => decide (q = (pred (fromCodeSymbol alphabet n m a) ||
          children.any (fun child => child = 1)).toNat)
      | none => false)
    (fun q => q = 1)

def edgeCode (alphabet : RankedAlphabetCode) (n m slot x y : Nat) : AutomatonCode :=
  FiniteAutomatonEncoding.encode
      (code alphabet n m) (words 2 (n + 1)).length
      (fun a q children =>
      match fin? a (code alphabet n m).length,
          fin? q (words 2 (n + 1)).length with
      | some a, some q =>
          if hn : x < n ∧ y < n then
            if hlen : children.length =
                (code alphabet n m).toRankedAlphabet.rank a then
              let s := fromCodeSymbol alphabet n m a
              let parent := edgeStateEquiv n q
              let hasDone := children.any fun child =>
                match fin? child (words 2 (n + 1)).length with
                | some child => (edgeStateEquiv n child).2
                | none => false
              let hasEdge :=
                match children[slot]? with
                | some child =>
                    match fin? child (words 2 (n + 1)).length with
                    | some child => (edgeStateEquiv n child).1 ⟨y, hn.2⟩
                    | none => false
                | none => false
              decide (parent.1 = s.2.1) &&
                decide (parent.2 = (hasDone || (s.2.1 ⟨x, hn.1⟩ && hasEdge)))
            else false
          else false
        | _, _ => false)
      (fun q =>
        match fin? q (words 2 (n + 1)).length with
        | some q => (edgeStateEquiv n q).2
        | none => false)

def codeTree (alphabet : RankedAlphabetCode) (n m : Nat) :
    Tree (MarkedAlphabet alphabet.toRankedAlphabet n m) →
      Tree (code alphabet n m).toRankedAlphabet :=
  relabelTree (toCodeSymbol alphabet n m) (rank_toCodeSymbol alphabet n m)

theorem somewhere_transition (alphabet : RankedAlphabetCode) (n m : Nat)
    (pred : MarkedSymbol alphabet n m → Bool)
    (a : MarkedSymbol alphabet n m) (parent : Bool)
    (children : Fin ((MarkedAlphabet alphabet.toRankedAlphabet n m).rank a) → Bool) :
    ((somewhereCode alphabet n m pred).toAutomaton (code alphabet n m)).transition
        (toCodeSymbol alphabet n m a) (boolFin parent)
        (fun i => boolFin (children
          (Fin.cast (rank_toCodeSymbol alphabet n m a) i))) =
      (somewhereAutomaton pred).transition a parent children := by
  unfold somewhereCode
  rw [transition_encode]
  change (match fin? (toCodeSymbol alphabet n m a).val
      (code alphabet n m).length with
    | some a' => decide ((boolFin parent).val =
        (pred (fromCodeSymbol alphabet n m a') ||
          (List.ofFn fun i =>
            (boolFin (children (Fin.cast
              (rank_toCodeSymbol alphabet n m a) i))).val).any
              (fun child => child = 1)).toNat)
    | none => false) = _
  rw [show fin? (toCodeSymbol alphabet n m a).val
      (code alphabet n m).length = some (toCodeSymbol alphabet n m a) by
    exact fin?_fin _]
  simp only [Option.some.injEq]
  rw [from_to]
  change decide ((boolFin parent).val =
      (pred a || (List.ofFn fun i =>
        (boolFin (children (Fin.cast
          (rank_toCodeSymbol alphabet n m a) i))).val).any
            (fun child => child = 1)).toNat) =
    decide (parent = (pred a || decide (∃ i, children i = true)))
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, decide_eq_true_eq]
  have hparent : (boolFin parent).val = parent.toNat := by cases parent <;> rfl
  have hchildren : (List.ofFn fun i =>
      (boolFin (children (Fin.cast
        (rank_toCodeSymbol alphabet n m a) i))).val).any
          (fun child => child = 1) = decide (∃ i, children i = true) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨v, hv, hvone⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      refine ⟨Fin.cast (rank_toCodeSymbol alphabet n m a) i, ?_⟩
      cases hc : children (Fin.cast (rank_toCodeSymbol alphabet n m a) i)
      · simp [boolFin, hc] at hvone
      · rfl
    · rintro ⟨i, hi⟩
      let j := Fin.cast (rank_toCodeSymbol alphabet n m a).symm i
      refine ⟨1, List.mem_ofFn.mpr ⟨j, ?_⟩, rfl⟩
      simp [j, hi, boolFin]
  rw [hparent]
  rw [hchildren]
  generalize decide (∃ i, children i = true) = b
  cases parent <;> cases pred a <;> cases b <;> decide

theorem somewhere_accept (alphabet : RankedAlphabetCode) (n m : Nat)
    (pred : MarkedSymbol alphabet n m → Bool) (q : Bool) :
    ((somewhereCode alphabet n m pred).toAutomaton (code alphabet n m)).accept
        (boolFin q) = (somewhereAutomaton pred).accept q := by
  unfold somewhereCode
  rw [accept_encode]
  cases q <;> rfl

theorem somewhereCode_accepts_iff (alphabet : RankedAlphabetCode) (n m : Nat)
    (pred : MarkedSymbol alphabet n m → Bool)
    (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)) :
    ((somewhereCode alphabet n m pred).toAutomaton (code alphabet n m)).Accepts
        (codeTree alphabet n m t) ↔ Somewhere pred t := by
  rw [← somewhere_accepts_iff pred t]
  exact relabelTree_accepts_iff (toCodeSymbol alphabet n m)
    (rank_toCodeSymbol alphabet n m) boolFin
    (somewhereAutomaton pred)
    ((somewhereCode alphabet n m pred).toAutomaton (code alphabet n m))
    (somewhere_transition alphabet n m pred)
    (somewhere_accept alphabet n m pred) t

theorem valid_transition (alphabet : RankedAlphabetCode) (n m : Nat)
    (a : MarkedSymbol alphabet n m) (parent : Fin n → OccurrenceCount)
    (children : Fin ((MarkedAlphabet alphabet.toRankedAlphabet n m).rank a) →
      (Fin n → OccurrenceCount)) :
    ((validCode alphabet n m).toAutomaton (code alphabet n m)).transition
        (toCodeSymbol alphabet n m a) ((validStateEquiv n).symm parent)
        (fun i => (validStateEquiv n).symm
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))) =
      (validMarkedAutomaton alphabet.toRankedAlphabet n m).transition
        a parent children := by
  unfold validCode
  rw [transition_encode]
  have ha : fin? (toCodeSymbol alphabet n m a).val
      (code alphabet n m).length = some (toCodeSymbol alphabet n m a) := by
    exact fin?_fin _
  have hq : fin? ((validStateEquiv n).symm parent).val
      (words 3 n).length = some ((validStateEquiv n).symm parent) := by
    simp [fin?, ((validStateEquiv n).symm parent).isLt]
  simp only [ha, hq]
  rw [dif_pos (by simp)]
  rw [from_to]
  simp only [validMarkedAutomaton]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change (∀ x, ValidStep
      (validStateEquiv n ((validStateEquiv n).symm parent) x) (a.2.1 x)
      (fun i => match fin? _ _ with
        | some child => validStateEquiv n child x
        | none => .many)) ↔
    (∀ x, ValidStep (parent x) (a.2.1 x) (fun i => children i x))
  constructor <;> intro h x
  · have hx := h x
    rw [Equiv.apply_symm_apply] at hx
    change ValidStep (parent x) (a.2.1 x) _
    convert hx using 1
    · exact (rank_toCodeSymbol alphabet n m a).symm
    · refine Function.hfunext (congrArg Fin (rank_toCodeSymbol alphabet n m a).symm) ?_
      intro i j hij
      have hj : j = Fin.cast (rank_toCodeSymbol alphabet n m a).symm i := by
        exact Fin.ext (Fin.val_eq_val_of_heq hij).symm
      subst j
      have hchild : fin? (((validStateEquiv n).symm
          (children i)).val) (words 3 n).length =
          some ((validStateEquiv n).symm (children i)) := by
        simp [fin?, ((validStateEquiv n).symm (children i)).isLt]
      simpa [hchild] using congrFun
        ((validStateEquiv n).apply_symm_apply (children i)) x
  · have hx := h x
    change ValidStep _ _ _
    rw [Equiv.apply_symm_apply]
    convert hx using 1
    · exact rank_toCodeSymbol alphabet n m a
    · refine Function.hfunext (congrArg Fin (rank_toCodeSymbol alphabet n m a)) ?_
      intro i j hij
      have hj : j = Fin.cast (rank_toCodeSymbol alphabet n m a) i := by
        exact Fin.ext (Fin.val_eq_val_of_heq hij).symm
      subst j
      have hchild : fin? (((validStateEquiv n).symm
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))).val)
          (words 3 n).length =
          some ((validStateEquiv n).symm
            (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))) := by
        simp [fin?, ((validStateEquiv n).symm
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))).isLt]
      simpa [hchild] using congrFun
        ((validStateEquiv n).apply_symm_apply
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))) x

theorem valid_accept (alphabet : RankedAlphabetCode) (n m : Nat)
    (q : Fin n → OccurrenceCount) :
    ((validCode alphabet n m).toAutomaton (code alphabet n m)).accept
        ((validStateEquiv n).symm q) =
      (validMarkedAutomaton alphabet.toRankedAlphabet n m).accept q := by
  unfold validCode
  rw [accept_encode]
  have hq : fin? ((validStateEquiv n).symm q).val (words 3 n).length =
      some ((validStateEquiv n).symm q) := by
    simp [fin?, ((validStateEquiv n).symm q).isLt]
  simp only [hq]
  change decide (∀ x, validStateEquiv n ((validStateEquiv n).symm q) x = .one) =
    decide (∀ x, q x = .one)
  simp

theorem validCode_accepts_iff (alphabet : RankedAlphabetCode) (n m : Nat)
    (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)) :
    ((validCode alphabet n m).toAutomaton (code alphabet n m)).Accepts
        (codeTree alphabet n m t) ↔
      t ∈ validMarkedLanguage alphabet.toRankedAlphabet n m := by
  rw [← validMarkedAutomaton_correct alphabet.toRankedAlphabet n m]
  exact relabelTree_accepts_iff (toCodeSymbol alphabet n m)
    (rank_toCodeSymbol alphabet n m) (validStateEquiv n).symm
    (validMarkedAutomaton alphabet.toRankedAlphabet n m)
    ((validCode alphabet n m).toAutomaton (code alphabet n m))
    (valid_transition alphabet n m) (valid_accept alphabet n m) t

theorem edge_transition (alphabet : RankedAlphabetCode) (n m : Nat)
    (slot : ChildIndex alphabet.toRankedAlphabet) (x y : Fin n)
    (a : MarkedSymbol alphabet n m) (parent : EdgeState n)
    (children : Fin ((MarkedAlphabet alphabet.toRankedAlphabet n m).rank a) →
      EdgeState n) :
    ((edgeCode alphabet n m slot.val x.val y.val).toAutomaton
      (code alphabet n m)).transition
        (toCodeSymbol alphabet n m a) ((edgeStateEquiv n).symm parent)
        (fun i => (edgeStateEquiv n).symm
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))) =
      (edgeAutomaton (m := m) slot x y).transition a parent children := by
  unfold edgeCode
  rw [transition_encode]
  simp only [fin?_fin]
  rw [dif_pos ⟨x.isLt, y.isLt⟩]
  rw [dif_pos (by simp)]
  rw [from_to]
  simp only [edgeAutomaton]
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  rw [decide_eq_true_eq]
  rw [(edgeStateEquiv n).apply_symm_apply]
  apply and_congr Iff.rfl
  let codedChildren := List.ofFn fun i => ((edgeStateEquiv n).symm
    (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))).val
  have hdone : (codedChildren.any fun child =>
      match fin? child (words 2 (n + 1)).length with
      | some child => (edgeStateEquiv n child).2
      | none => false) = true ↔ ∃ i, (children i).2 = true := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨_, hc, htrue⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      let j := Fin.cast (rank_toCodeSymbol alphabet n m a) i
      refine ⟨j, ?_⟩
      have hfin : fin? (((edgeStateEquiv n).symm (children j)).val)
          (words 2 (n + 1)).length =
          some ((edgeStateEquiv n).symm (children j)) := fin?_fin _
      simpa [codedChildren, j, hfin] using htrue
    · rintro ⟨j, hj⟩
      let i := Fin.cast (rank_toCodeSymbol alphabet n m a).symm j
      refine ⟨((edgeStateEquiv n).symm (children j)).val, ?_, ?_⟩
      · exact List.mem_ofFn.mpr ⟨i, by simp [codedChildren, i]⟩
      · rw [fin?_fin]
        simpa
  have hedge : (match codedChildren[slot.val]? with
      | some child =>
          match fin? child (words 2 (n + 1)).length with
          | some child => (edgeStateEquiv n child).1 y
          | none => false
      | none => false) = true ↔
      ∃ i, i.val = slot.val ∧ (children i).1 y = true := by
    by_cases hs : slot.val < codedChildren.length
    · let ci : Fin ((code alphabet n m).toRankedAlphabet.rank
          (toCodeSymbol alphabet n m a)) := ⟨slot.val, by simpa [codedChildren] using hs⟩
      let j := Fin.cast (rank_toCodeSymbol alphabet n m a) ci
      have hget : codedChildren[slot.val]? =
          some (((edgeStateEquiv n).symm (children j)).val) := by
        rw [List.getElem?_eq_getElem hs]
        simp [codedChildren, j, ci]
      rw [hget]
      change ((match fin? (((edgeStateEquiv n).symm (children j)).val)
          (words 2 (n + 1)).length with
        | some child => (edgeStateEquiv n child).1 y
        | none => false) = true ↔ _)
      rw [fin?_fin]
      constructor
      · intro hchild
        exact ⟨j, by simp [j, ci], by simpa using hchild⟩
      · rintro ⟨i, hi, hchild⟩
        have hij : i = j := by
          apply Fin.ext
          simpa [j, ci] using hi
        subst i
        simpa using hchild
    · have hget : codedChildren[slot.val]? = none := by
        exact List.getElem?_eq_none (by simpa using hs)
      rw [hget]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨i, hi, -⟩
      apply hs
      have hi' : i.val < (code alphabet n m).toRankedAlphabet.rank
          (toCodeSymbol alphabet n m a) := by
        rw [rank_toCodeSymbol]
        exact i.isLt
      have hi'' : slot.val < (code alphabet n m).toRankedAlphabet.rank
          (toCodeSymbol alphabet n m a) := hi ▸ hi'
      simpa [codedChildren] using hi''
  have hcondition :
      ((codedChildren.any fun child =>
          match fin? child (words 2 (n + 1)).length with
          | some child => (edgeStateEquiv n child).2
          | none => false) ||
        a.2.1 x && (match codedChildren[slot.val]? with
          | some child =>
              match fin? child (words 2 (n + 1)).length with
              | some child => (edgeStateEquiv n child).1 y
              | none => false
          | none => false)) = true ↔
        (∃ i, (children i).2 = true) ∨
          (a.2.1 x = true ∧ ∃ i, i.val = slot.val ∧ (children i).1 y = true) := by
    rw [Bool.or_eq_true, Bool.and_eq_true]
    exact or_congr hdone (and_congr Iff.rfl hedge)
  change parent.2 = _ ↔ (parent.2 = true ↔ _)
  constructor
  · intro heq
    rw [heq]
    simpa [codedChildren] using hcondition
  · intro h
    apply Bool.eq_iff_iff.mpr
    exact h.trans (by simpa [codedChildren] using hcondition.symm)

theorem edge_accept (alphabet : RankedAlphabetCode) (n m : Nat)
    (slot : ChildIndex alphabet.toRankedAlphabet) (x y : Fin n)
    (q : EdgeState n) :
    ((edgeCode alphabet n m slot.val x.val y.val).toAutomaton
      (code alphabet n m)).accept ((edgeStateEquiv n).symm q) =
      (edgeAutomaton (m := m) slot x y).accept q := by
  unfold edgeCode
  rw [accept_encode]
  rw [fin?_fin]
  simp only [edgeAutomaton]
  rw [(edgeStateEquiv n).apply_symm_apply]

theorem edgeCode_accepts_iff (alphabet : RankedAlphabetCode) (n m : Nat)
    (slot : ChildIndex alphabet.toRankedAlphabet) (x y : Fin n)
    (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)) :
    ((edgeCode alphabet n m slot.val x.val y.val).toAutomaton
      (code alphabet n m)).Accepts (codeTree alphabet n m t) ↔
      EdgeSomewhere (m := m) slot x y t := by
  rw [← edge_accepts_iff (m := m) slot x y t]
  exact relabelTree_accepts_iff (toCodeSymbol alphabet n m)
    (rank_toCodeSymbol alphabet n m) (edgeStateEquiv n).symm
    (edgeAutomaton (m := m) slot x y)
    ((edgeCode alphabet n m slot.val x.val y.val).toAutomaton
      (code alphabet n m))
    (edge_transition alphabet n m slot x y)
    (edge_accept alphabet n m slot x y) t

end Lax842588Proofs.EncodedAtomicAutomata
