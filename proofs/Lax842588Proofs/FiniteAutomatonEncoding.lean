import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD
import Lax842588.ValueTranslations

set_option backward.isDefEq.respectTransparency false

namespace Lax842588Proofs.FiniteAutomatonEncoding

open Lax842588.ValueTranslations
open Lax842588.RankedTree
open Lax842588.TreeAutomaton

/-- All words of length `k` with entries below `n`. -/
def words (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range n).flatMap fun q => (words n k).map (q :: ·)

theorem words_length (base length : Nat) :
    (words base length).length = base ^ length := by
  induction length with
  | zero => rfl
  | succ length ih => simp [words, ih, pow_succ, Nat.mul_comm]

/-- The word at a numeric row index, written most-significant digit first in
base `base` and padded to exactly `length` digits.  This arithmetic view is
the one used by charged RAM compilers; it does not materialize `words`. -/
def radixWord (base : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | length + 1, state =>
      state / base ^ length ::
        radixWord base length (state % base ^ length)

@[simp] theorem radixWord_length (base length state : Nat) :
    (radixWord base length state).length = length := by
  induction length generalizing state with
  | zero => rfl
  | succ length ih => simp [radixWord, ih]

private def wordsVector (base : Nat) : (length : Nat) →
    Vector (List Nat) (base ^ length)
  | 0 => #v[[]]
  | length + 1 =>
      ((Vector.range base).flatMap fun q =>
        (wordsVector base length).map (q :: ·)).cast
          (by simp [pow_succ, Nat.mul_comm])

private theorem wordsVector_succ (base length : Nat) :
    wordsVector base (length + 1) =
      ((Vector.range base).flatMap fun q =>
        (wordsVector base length).map (q :: ·)).cast
          (by simp [pow_succ, Nat.mul_comm]) := by
  rfl

private theorem wordsVector_toList (base length : Nat) :
    (wordsVector base length).toArray.toList = words base length := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [wordsVector_succ]
      simp only [Vector.toArray_cast]
      rw [← Vector.flatMap_toArray]
      simp [words, ih]

private theorem wordsVector_get_eq_radixWord (base length state : Nat)
    (hstate : state < base ^ length) :
    (wordsVector base length)[state] = radixWord base length state := by
  induction length generalizing state with
  | zero =>
      have hzero : state = 0 := by
        simpa using hstate
      subst state
      rfl
  | succ length ih =>
      rw [wordsVector_succ]
      simp only [Vector.getElem_cast, Vector.getElem_flatMap]
      simp only [Vector.getElem_map, Vector.getElem_range]
      rw [ih]
      rfl

/-- Arithmetic radix decoding agrees exactly with the canonical enumeration
used by `encode`.  Thus an implementation can compute a row from its index
without receiving the exponentially large enumeration as advice. -/
theorem words_getD_eq_radixWord (base length state : Nat)
    (hstate : state < base ^ length) :
    (words base length).getD state [] = radixWord base length state := by
  rw [← wordsVector_toList base length]
  have hi : state < (wordsVector base length).toArray.toList.length := by
    simpa using hstate
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  change (wordsVector base length)[state] = _
  exact wordsVector_get_eq_radixWord base length state hstate

theorem mem_words_iff {n k : Nat} {xs : List Nat} :
    xs ∈ words n k ↔ xs.length = k ∧ ∀ q ∈ xs, q < n := by
  induction k generalizing xs with
  | zero =>
      constructor
      · intro h
        have hx : xs = [] := by simpa [words] using h
        subst xs
        simp
      · rintro ⟨hlen, -⟩
        simpa [words] using List.eq_nil_of_length_eq_zero hlen
  | succ k ih =>
      simp only [words, List.mem_flatMap, List.mem_range, List.mem_map]
      constructor
      · rintro ⟨q, hq, ys, hys, rfl⟩
        rw [ih] at hys
        refine ⟨by simp [hys.1], ?_⟩
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hq
        · exact hys.2 r hr
      · rintro ⟨hlen, hbound⟩
        rcases xs with _ | ⟨q, ys⟩
        · simp at hlen
        · refine ⟨q, hbound q (by simp), ys, ?_, rfl⟩
          rw [ih]
          exact ⟨by simpa using hlen, fun r hr => hbound r (by simp [hr])⟩

theorem radixWord_mem_words (base length state : Nat)
    (hstate : state < base ^ length) :
    radixWord base length state ∈ words base length := by
  have hindex : state < (words base length).length := by
    simpa [words_length] using hstate
  rw [← words_getD_eq_radixWord base length state hstate]
  rw [List.getD_eq_getElem (l := words base length) (d := []) hindex]
  exact List.getElem_mem _

theorem radixWord_value_lt {base length state value : Nat}
    (hstate : state < base ^ length)
    (hvalue : value ∈ radixWord base length state) : value < base := by
  exact (mem_words_iff.mp (radixWord_mem_words base length state hstate)).2
    value hvalue

/-- Numeric value of a most-significant-first radix word. -/
def radixValue (base : Nat) : List Nat → Nat
  | [] => 0
  | digit :: digits =>
      digit * base ^ digits.length + radixValue base digits

theorem radixValue_lt_pow {base : Nat} {digits : List Nat}
    (hbase : 0 < base) (hdigits : ∀ digit ∈ digits, digit < base) :
    radixValue base digits < base ^ digits.length := by
  induction digits with
  | nil => simp [radixValue]
  | cons digit digits ih =>
      have hdigit : digit < base := hdigits digit (by simp)
      have htail : ∀ value ∈ digits, value < base := by
        intro value hvalue
        exact hdigits value (by simp [hvalue])
      have hih := ih htail
      have hpowerPos : 0 < base ^ digits.length := pow_pos hbase _
      calc
        radixValue base (digit :: digits) =
            digit * base ^ digits.length + radixValue base digits := rfl
        _ < digit * base ^ digits.length + base ^ digits.length := by omega
        _ = (digit + 1) * base ^ digits.length := by
          simp [Nat.add_mul]
        _ ≤ base * base ^ digits.length :=
          Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hdigit)
        _ = base ^ (digit :: digits).length := by
          simp [pow_succ, Nat.mul_comm]

theorem radixValue_radixWord (base length state : Nat)
    (hbase : 0 < base) (hstate : state < base ^ length) :
    radixValue base (radixWord base length state) = state := by
  induction length generalizing state with
  | zero =>
      have : state = 0 := by simpa using hstate
      subst state
      rfl
  | succ length ih =>
      have hpowerPos : 0 < base ^ length := pow_pos hbase _
      have hremainder : state % base ^ length < base ^ length :=
        Nat.mod_lt _ hpowerPos
      simp only [radixWord, radixValue, radixWord_length]
      rw [ih (state % base ^ length) hremainder]
      simpa [Nat.mul_comm] using
        (Nat.div_add_mod state (base ^ length))

theorem radixWord_radixValue (base : Nat) (digits : List Nat)
    (hbase : 0 < base) (hdigits : ∀ digit ∈ digits, digit < base) :
    radixWord base digits.length (radixValue base digits) = digits := by
  induction digits with
  | nil => rfl
  | cons digit digits ih =>
      have hdigit : digit < base := hdigits digit (by simp)
      have htail : ∀ value ∈ digits, value < base := by
        intro value hvalue
        exact hdigits value (by simp [hvalue])
      have hvalueLt := radixValue_lt_pow hbase htail
      have hpowerPos : 0 < base ^ digits.length := pow_pos hbase _
      have hdiv :
          (digit * base ^ digits.length + radixValue base digits) /
              base ^ digits.length = digit := by
        rw [Nat.mul_comm digit, Nat.mul_add_div hpowerPos,
          Nat.div_eq_of_lt hvalueLt]
        simp
      have hmod :
          (digit * base ^ digits.length + radixValue base digits) %
              base ^ digits.length = radixValue base digits := by
        rw [Nat.mul_comm digit, Nat.mul_add_mod,
          Nat.mod_eq_of_lt hvalueLt]
      simp only [List.length_cons, radixValue, radixWord]
      rw [hdiv, hmod, ih htail]

theorem ofFn_mem_words {n k : Nat} (f : Fin k → Fin n) :
    List.ofFn (fun i => (f i).val) ∈ words n k := by
  rw [mem_words_iff]
  exact ⟨by simp, fun q hq => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact (f i).isLt⟩

/-- Enumerate the complete transition table of a finite automaton whose
states and alphabet symbols are canonically numbered. -/
def encode (alphabet : RankedAlphabetCode) (states : Nat)
    (transition : (a q : Nat) → List Nat → Bool)
    (accept : Nat → Bool) : AutomatonCode :=
  (states,
    (List.range alphabet.length).flatMap fun a =>
      (List.range states).flatMap fun q =>
        ((words states (alphabet.getD a 0)).filter
          (transition a q)).map fun children => (a, q, children),
    (List.range states).filter accept)

theorem transition_encode (alphabet : RankedAlphabetCode) (states : Nat)
    (transition : (a q : Nat) → List Nat → Bool)
    (accept : Nat → Bool) (a : alphabet.toRankedAlphabet.Symbol)
    (q : Fin states)
    (children : Fin (alphabet.toRankedAlphabet.rank a) → Fin states) :
    ((encode alphabet states transition accept).toAutomaton alphabet).transition
      a q children = transition a.val q.val (List.ofFn fun i => (children i).val) := by
  simp only [AutomatonCode.toAutomaton, encode]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨tr, htr, hmatch⟩
    simp only [List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter] at htr
    obtain ⟨a', ha', q', hq', cs, ⟨hcs, hstep⟩, rfl⟩ := htr
    simp only [decide_eq_true_eq] at hmatch
    rcases hmatch with ⟨rfl, rfl, hchildren⟩
    simpa [hchildren] using hstep
  · intro hstep
    let cs := List.ofFn fun i => (children i).val
    refine ⟨(a.val, q.val, cs), ?_, ?_⟩
    · simp only [List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter]
      refine ⟨a.val, a.isLt, q.val, q.isLt, cs, ⟨?_, ?_⟩, rfl⟩
      have hrank : alphabet.getD a.val 0 = alphabet.get a := by
        simp [List.getD_eq_getElem?_getD]
      rw [hrank]
      exact ofFn_mem_words children
      · exact hstep
    · simp [cs]

theorem accept_encode (alphabet : RankedAlphabetCode) (states : Nat)
    (transition : (a q : Nat) → List Nat → Bool)
    (accept : Nat → Bool) (q : Fin states) :
    ((encode alphabet states transition accept).toAutomaton alphabet).accept q =
      accept q.val := by
  simp [AutomatonCode.toAutomaton, encode]

theorem toAutomaton_encode (alphabet : RankedAlphabetCode) (states : Nat)
    (transition : (a q : Nat) → List Nat → Bool)
    (accept : Nat → Bool) :
    (encode alphabet states transition accept).toAutomaton alphabet =
      ({ transition := fun a q children =>
          transition a.val q.val (List.ofFn fun i => (children i).val)
         accept := fun q => accept q.val } :
        Automaton alphabet.toRankedAlphabet (Fin states)) := by
  let lhs := (encode alphabet states transition accept).toAutomaton alphabet
  let rhs : Automaton alphabet.toRankedAlphabet (Fin states) :=
    { transition := fun a q children =>
        transition a.val q.val (List.ofFn fun i => (children i).val)
      accept := fun q => accept q.val }
  have ht : lhs.transition = rhs.transition := by
    funext a q children
    exact transition_encode alphabet states transition accept a q children
  have ha : lhs.accept = rhs.accept := by
    funext q
    exact accept_encode alphabet states transition accept q
  change lhs = rhs
  rcases lhs with ⟨lt, la⟩
  rcases rhs with ⟨rt, ra⟩
  exact congrArg₂ Automaton.mk ht ha

theorem words_prim : Primrec₂ words := by
  let next : Nat → Nat × List (List Nat) → List (List Nat) := fun n p =>
    (List.range n).flatMap fun q => p.2.map (q :: ·)
  have hnext : Primrec₂ next := by
    apply Primrec.list_flatMap (Primrec.list_range.comp Primrec.fst)
    have hmap : Primrec₂ fun (p : Nat × (Nat × List (List Nat)))
        (q : Nat) => p.2.2.map (q :: ·) := by
      apply Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      exact Primrec.list_cons.comp₂
        (Primrec.snd.comp Primrec.fst |>.to₂) Primrec₂.right
    exact hmap
  refine (Primrec.nat_rec (Primrec.const [[]]) hnext).of_eq ?_
  intro n k
  induction k with
  | zero => rfl
  | succ k ih => simp [words, next, ih]

theorem encode_prim
    {X : Type*} [Primcodable X]
    (alphabet : X → RankedAlphabetCode) (states : X → Nat)
    (transition : X → Nat → Nat → List Nat → Bool)
    (accept : X → Nat → Bool)
    (halphabet : Primrec alphabet) (hstates : Primrec states)
    (htransition : Primrec fun p : X × Nat × Nat × List Nat =>
      transition p.1 p.2.1 p.2.2.1 p.2.2.2)
    (haccept : Primrec fun p : X × Nat => accept p.1 p.2) :
    Primrec fun x => encode (alphabet x) (states x) (transition x) (accept x) := by
  unfold encode
  apply Primrec.pair hstates
  apply Primrec.pair
  · apply Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp halphabet))
    apply Primrec.list_flatMap (Primrec.list_range.comp (hstates.comp Primrec.fst) |>.to₂)
    apply Primrec.list_map
    · have hpred : PrimrecRel fun
          (children : List Nat) (ctx : X × Nat × Nat) =>
          transition ctx.1 ctx.2.1 ctx.2.2 children = true := by
        exact (Primrec.eq.comp
          (htransition.comp
            (Primrec.pair (Primrec.fst.comp Primrec.snd)
              (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
                (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
                  Primrec.fst))))
          (Primrec.const true)).primrecRel
      let childrenWords : (X × Nat) × Nat → List (List Nat) := fun a =>
        words (states a.1.1) ((alphabet a.1.1).getD a.1.2 0)
      have hchildrenWords : Primrec childrenWords := by
        exact words_prim.comp
          (hstates.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.list_getD 0 |>.comp
            (halphabet.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.snd.comp Primrec.fst))
      let context : (X × Nat) × Nat → X × Nat × Nat := fun a =>
        (a.1.1, a.1.2, a.2)
      have hcontext : Primrec context :=
        Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
      refine (hpred.listFilter.comp hchildrenWords hcontext).of_eq ?_
      intro a
      simp [childrenWords, context]
    · exact Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  · have hp : PrimrecRel fun (q : Nat) (x : X) => accept x q = true := by
      exact (Primrec.eq.comp
        (haccept.comp (Primrec.pair Primrec.snd Primrec.fst))
        (Primrec.const true)).primrecRel
    refine (hp.listFilter.comp (Primrec.list_range.comp hstates) Primrec.id).of_eq ?_
    intro x
    apply List.filter_congr
    intro q hq
    simp

end Lax842588Proofs.FiniteAutomatonEncoding
