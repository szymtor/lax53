import Lax53Proofs.FiniteWordStates
import Lax53Proofs.EncodedAutomataOperations
import Lax53Proofs.EncodedPrimitiveAtomicAutomata
import Lax53Proofs.MSORamCompilerProgram
import Lax53Proofs.MSORamCompilerTransition
import Lax53Proofs.ImpArrayLengths
import Mathlib.Data.List.GetD

/-!
An arithmetic enumeration of binary child-state words for the charged
compiler.

The existing mathematical automata use `FiniteAutomatonEncoding.words`.  A
RAM program must not receive that complete exponential list as advice.  The
recursion below computes the same row directly from its numeric index by
successive quotient and remainder operations.  We also choose an equivalent
sparse transition ordering for the two-state "somewhere" automaton: one record
per child row, with its uniquely determined parent state.  This is the order a
single numeric RAM loop will generate.
-/

namespace Lax53Proofs.MSORamCompilerBinaryWord

open Lax53.ValueTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.EncodedAutomataOperations
open Lax53Proofs.FiniteAutomatonEncoding
open Lax53Proofs.FiniteWordStates
open Lax53Proofs.AutomatonRamArenaSegments
open Lax53Proofs.MSORamCompilerProgram
open Lax53Proofs.MSORamCompilerTransition
open Lax53Proofs.MSORamCompilerStorage
open Lax53Proofs.MSORamCompilerHeap
open Lax13Proofs.Imp
open Lax13Proofs.Reasoning

/-- The binary word with canonical numeric index `state`, most significant
digit first.  Only indices below `2 ^ length` are used by the compiler. -/
def binaryWord : Nat → Nat → List Nat
  | 0, _ => []
  | length + 1, state =>
      state / 2 ^ length :: binaryWord length (state % 2 ^ length)

/-- Direct arithmetic generation agrees exactly with the canonical word
enumeration used by the mathematical finite-automaton development. -/
theorem wordsTwo_getD_eq_binaryWord (length state : Nat)
    (hstate : state < 2 ^ length) :
    (words 2 length).getD state [] = binaryWord length state := by
  induction length generalizing state with
  | zero =>
      have hzero : state = 0 := by omega
      subst state
      rfl
  | succ length ih =>
      have hblock : (words 2 length).length = 2 ^ length :=
        words_length 2 length
      have htotal : state < (words 2 (length + 1)).length := by
        simpa [words_length] using hstate
      rw [List.getD_eq_getElem (l := words 2 (length + 1)) (d := []) htotal]
      simp only [words, show List.range 2 = [0, 1] by decide,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      by_cases hfirst : state < (words 2 length).length
      · rw [List.getElem_append_left (by simpa using hfirst)]
        rw [List.getElem_map]
        have hsmall : state < 2 ^ length := by simpa [hblock] using hfirst
        have hget : (words 2 length)[state] = binaryWord length state := by
          have hi := ih state hsmall
          rw [List.getD_eq_getElem (l := words 2 length) (d := []) hfirst] at hi
          exact hi
        simp [binaryWord, Nat.div_eq_of_lt hsmall,
          Nat.mod_eq_of_lt hsmall, hget]
      · have hge : 2 ^ length ≤ state := by
          simpa [hblock] using Nat.le_of_not_gt hfirst
        have hupper : state < 2 * 2 ^ length := by
          simpa [pow_succ, Nat.mul_comm] using hstate
        have hsub : state - 2 ^ length < 2 ^ length := by omega
        rw [List.getElem_append_right (by
          simpa using Nat.le_of_not_gt hfirst)]
        rw [List.getElem_map]
        have hdiv : state / 2 ^ length = 1 := by
          apply Nat.div_eq_of_lt_le
          · simpa using hge
          · simpa using hupper
        have hmod : state % 2 ^ length = state - 2 ^ length := by
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]
        have hsubIndex : state - 2 ^ length < (words 2 length).length := by
          simpa [hblock] using hsub
        have hget : (words 2 length)[state - 2 ^ length] =
            binaryWord length (state - 2 ^ length) := by
          have hi := ih (state - 2 ^ length) hsub
          rw [List.getD_eq_getElem (l := words 2 length) (d := [])
            hsubIndex] at hi
          exact hi
        simp [binaryWord, hblock, hdiv, hmod, hget]

@[simp] theorem binaryWord_length (length state : Nat) :
    (binaryWord length state).length = length := by
  induction length generalizing state with
  | zero => rfl
  | succ length ih => simp [binaryWord, ih]

theorem binaryWord_any_one (length state : Nat)
    (hstate : state < 2 ^ length) :
    (binaryWord length state).any (fun child => child = 1) =
      decide (state ≠ 0) := by
  induction length generalizing state with
  | zero =>
      have hzero : state = 0 := by omega
      subst state
      decide
  | succ length ih =>
      have hpow : 0 < 2 ^ length := pow_pos (by omega) _
      have hquot : state / 2 ^ length < 2 := by
        rw [Nat.div_lt_iff_lt_mul hpow]
        simpa [pow_succ, Nat.mul_comm] using hstate
      have hmod : state % 2 ^ length < 2 ^ length := Nat.mod_lt _ hpow
      rw [binaryWord]
      simp only [List.any_cons]
      rw [ih (state % 2 ^ length) hmod]
      by_cases hzero : state = 0
      · subst state
        simp
      · have hsplit : state / 2 ^ length = 1 ∨
            state % 2 ^ length ≠ 0 := by
          by_cases hq : state / 2 ^ length = 0
          · right
            intro hr
            have hdecomp := Nat.div_add_mod state (2 ^ length)
            simp [hq, hr] at hdecomp
            exact hzero hdecomp.symm
          · left
            have hqpos : 0 < state / 2 ^ length := Nat.pos_of_ne_zero hq
            omega
        rcases hsplit with hq | hr
        · simp [hq, hzero]
        · simp [hr, hzero]

theorem binaryWord_mem_words (length state : Nat)
    (hstate : state < 2 ^ length) :
    binaryWord length state ∈ words 2 length := by
  have hindex : state < (words 2 length).length := by
    simpa [words_length] using hstate
  rw [← wordsTwo_getD_eq_binaryWord length state hstate]
  rw [List.getD_eq_getElem (l := words 2 length) (d := []) hindex]
  exact List.getElem_mem _

theorem binaryWord_value_lt_two {length state value : Nat}
    (hstate : state < 2 ^ length)
    (hvalue : value ∈ binaryWord length state) : value < 2 := by
  exact (mem_words_iff.mp (binaryWord_mem_words length state hstate)).2
    value hvalue

/-- Parent state computed from a predicate bit and a numeric child-row index.
For a binary row, a nonzero index is exactly the presence of a child in state
`1`. -/
def binaryParent (predicate : Bool) (state : Nat) : Nat :=
  (predicate || decide (state ≠ 0)).toNat

def generatedBinaryTransition (symbol length state : Nat)
    (predicate : Bool) : TransitionCode :=
  (symbol, binaryParent predicate state, binaryWord length state)

theorem generatedBinaryTransition_eq (symbol length state : Nat)
    (predicate : Bool) (hstate : state < 2 ^ length) :
    generatedBinaryTransition symbol length state predicate =
      (symbol,
        (predicate || (binaryWord length state).any
          fun child => child = 1).toNat,
        binaryWord length state) := by
  simp [generatedBinaryTransition, binaryParent,
    binaryWord_any_one length state hstate]

/-- Fixed-width transition words emitted before row index `state` for one
symbol. This prefix is the semantic object tracked by the counted inner
loop. -/
def binaryRowsPrefix (maximumRank symbol length : Nat) (predicate : Bool)
    (state : Nat) : List Nat :=
  (List.range state).flatMap fun row =>
    encodeTransitionFixed maximumRank
      (generatedBinaryTransition symbol length row predicate)

@[simp] theorem binaryRowsPrefix_zero
    (maximumRank symbol length : Nat) (predicate : Bool) :
    binaryRowsPrefix maximumRank symbol length predicate 0 = [] := by
  simp [binaryRowsPrefix]

theorem binaryRowsPrefix_succ
    (maximumRank symbol length state : Nat) (predicate : Bool) :
    binaryRowsPrefix maximumRank symbol length predicate (state + 1) =
      binaryRowsPrefix maximumRank symbol length predicate state ++
        encodeTransitionFixed maximumRank
          (generatedBinaryTransition symbol length state predicate) := by
  simp [binaryRowsPrefix, List.range_succ]

@[simp] theorem binaryRowsPrefix_length
    (maximumRank symbol length : Nat) (predicate : Bool) (state : Nat) :
    (binaryRowsPrefix maximumRank symbol length predicate state).length =
      state * (maximumRank + 3) := by
  simp [binaryRowsPrefix, encodeTransitionFixed, List.length_flatMap]

/-- An operationally convenient code for the two-state automaton that records
whether the predicate has occurred somewhere below the current node.  It is
extensionally the usual `somewhere` automaton, but lists transitions in child
row order so a RAM loop need not construct or filter an exponential list. -/
def binarySomewhereCode (alphabet : RankedAlphabetCode)
    (pred : Nat → Bool) : AutomatonCode :=
  (2,
    (List.range alphabet.length).flatMap fun a =>
      (List.range (2 ^ alphabet.getD a 0)).map fun state =>
        let children := binaryWord (alphabet.getD a 0) state
        (a, (pred a || children.any fun child => child = 1).toNat, children),
    [1])

theorem step_binarySomewhereCode (alphabet : RankedAlphabetCode)
    (pred : Nat → Bool) (a q : Nat) (children : List Nat)
    (ha : a < alphabet.length)
    (hchildren : children ∈ words 2 (alphabet.getD a 0)) :
    step (binarySomewhereCode alphabet pred) a q children =
      decide (q = (pred a || children.any fun child => child = 1).toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [step, binarySomewhereCode, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨transition, htransition, rfl⟩
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at htransition
    obtain ⟨a', ha', state, hstate, heq⟩ := htransition
    rcases Prod.ext_iff.mp heq with ⟨haeq, hrest⟩
    change a' = a at haeq
    subst a'
    rcases Prod.ext_iff.mp hrest with ⟨hq, hrow⟩
    change (pred a || (binaryWord (alphabet.getD a 0) state).any
      fun child => child = 1).toNat = q at hq
    change binaryWord (alphabet.getD a 0) state = children at hrow
    rw [← hrow]
    exact hq.symm
  · intro hq
    let state := (words 2 (alphabet.getD a 0)).idxOf children
    have hstateWords : state < (words 2 (alphabet.getD a 0)).length :=
      List.idxOf_lt_length_iff.mpr hchildren
    have hstate : state < 2 ^ alphabet.getD a 0 := by
      simpa [words_length] using hstateWords
    have hrow : binaryWord (alphabet.getD a 0) state = children := by
      rw [← wordsTwo_getD_eq_binaryWord _ state hstate]
      rw [List.getD_eq_getElem (l := words 2 (alphabet.getD a 0))
        (d := []) hstateWords]
      exact List.idxOf_get hstateWords
    refine ⟨(a, q, children), ?_, rfl⟩
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨a, ha, state, hstate, ?_⟩
    change (a,
      (pred a || (binaryWord (alphabet.getD a 0) state).any
        fun child => child = 1).toNat,
      binaryWord (alphabet.getD a 0) state) = (a, q, children)
    rw [hrow, ← hq]

theorem binarySomewhere_transition (alphabet : RankedAlphabetCode)
    (pred : Nat → Bool)
    (a : alphabet.toRankedAlphabet.Symbol) (q : Fin 2)
    (children : Fin (alphabet.toRankedAlphabet.rank a) → Fin 2) :
    ((binarySomewhereCode alphabet pred).toAutomaton alphabet).transition
        a q children =
      decide (q.val = (pred a.val ||
        (List.ofFn fun i => (children i).val).any
          fun child => child = 1).toNat) := by
  rw [← step_eq_transition]
  apply step_binarySomewhereCode
  · exact a.isLt
  · have hrank : alphabet.getD a.val 0 = alphabet.get a := by
      simp [List.getD_eq_getElem?_getD, a.isLt]
    rw [hrank]
    exact ofFn_mem_words children

@[simp] theorem binarySomewhere_accept (alphabet : RankedAlphabetCode)
    (pred : Nat → Bool) (q : Fin 2) :
    ((binarySomewhereCode alphabet pred).toAutomaton alphabet).accept q =
      (q.val = 1) := by
  simp [binarySomewhereCode, AutomatonCode.toAutomaton]

/-- The sparse row order emitted by the RAM is semantically identical to the
original complete-enumerator presentation of the mathematical "somewhere"
automaton.  Exact transition-list order is deliberately not part of the
compiler's semantic interface. -/
theorem binarySomewhere_toAutomaton_eq_somewhereCodeP
    (alphabet : RankedAlphabetCode) (n m : Nat) (pred : Nat → Bool) :
    (binarySomewhereCode (MarkedAlphabetEncoding.code alphabet n m) pred).toAutomaton
        (MarkedAlphabetEncoding.code alphabet n m) =
      (EncodedPrimitiveAtomicAutomata.somewhereCodeP alphabet n m pred).toAutomaton
        (MarkedAlphabetEncoding.code alphabet n m) := by
  let left :=
    (binarySomewhereCode (MarkedAlphabetEncoding.code alphabet n m) pred).toAutomaton
      (MarkedAlphabetEncoding.code alphabet n m)
  let right :=
    (EncodedPrimitiveAtomicAutomata.somewhereCodeP alphabet n m pred).toAutomaton
      (MarkedAlphabetEncoding.code alphabet n m)
  change left = right
  have ht : left.transition = right.transition := by
    funext a q children
    change
      ((binarySomewhereCode (MarkedAlphabetEncoding.code alphabet n m) pred).toAutomaton
          (MarkedAlphabetEncoding.code alphabet n m)).transition a q children =
        ((EncodedPrimitiveAtomicAutomata.somewhereCodeP alphabet n m pred).toAutomaton
          (MarkedAlphabetEncoding.code alphabet n m)).transition a q children
    rw [binarySomewhere_transition]
    unfold EncodedPrimitiveAtomicAutomata.somewhereCodeP
    rw [FiniteAutomatonEncoding.transition_encode]
  have ha : left.accept = right.accept := by
    funext q
    change
      ((binarySomewhereCode (MarkedAlphabetEncoding.code alphabet n m) pred).toAutomaton
          (MarkedAlphabetEncoding.code alphabet n m)).accept q =
        ((EncodedPrimitiveAtomicAutomata.somewhereCodeP alphabet n m pred).toAutomaton
          (MarkedAlphabetEncoding.code alphabet n m)).accept q
    simp [binarySomewhereCode,
      EncodedPrimitiveAtomicAutomata.somewhereCodeP,
      AutomatonCode.toAutomaton]
    simp [FiniteAutomatonEncoding.encode]
    omega
  rcases left with ⟨lt, la⟩
  rcases right with ⟨rt, ra⟩
  exact congrArg₂ Lax53.TreeAutomaton.Automaton.mk ht ha

theorem binarySomewhere_accepts_iff_somewhereCodeP
    (alphabet : RankedAlphabetCode) (n m : Nat) (pred : Nat → Bool)
    (t : Lax53.RankedTree.Tree
      (MarkedAlphabetEncoding.code alphabet n m).toRankedAlphabet) :
    ((binarySomewhereCode (MarkedAlphabetEncoding.code alphabet n m) pred).toAutomaton
        (MarkedAlphabetEncoding.code alphabet n m)).Accepts t ↔
      ((EncodedPrimitiveAtomicAutomata.somewhereCodeP alphabet n m pred).toAutomaton
        (MarkedAlphabetEncoding.code alphabet n m)).Accepts t := by
  rw [binarySomewhere_toAutomaton_eq_somewhereCodeP]
  rfl

/-! ### Charged materialization of one binary child row -/

def BinaryWordReady (B length state maximumRank : Nat) (sigma : Env) : Prop :=
  sigma.vars "binaryLength" = length ∧
    sigma.vars "binaryState" = state ∧
    state < 2 ^ length ∧
    2 ^ length < B ∧
    length < B ∧
    length ≤ (sigma.arrs "NewTransitionChildren").length ∧
    (sigma.arrs "NewTransitionChildren").length < B ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    length ≤ maximumRank ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank ∧
    maximumRank < B

/-- The already written prefix is exact.  The unread suffix is still the
same quotient/remainder recursion, so one loop iteration follows by unfolding
`binaryWord`; the machine never consults an exponential word table. -/
def BinaryWordInv (B length state maximumRank : Nat) (sigma : Env) : Prop :=
  let index := sigma.vars "binaryIndex"
  index ≤ length ∧
    sigma.vars "binaryLength" = length ∧
    sigma.vars "binaryState" = state ∧
    state < 2 ^ length ∧
    2 ^ length < B ∧
    length < B ∧
    length ≤ (sigma.arrs "NewTransitionChildren").length ∧
    (sigma.arrs "NewTransitionChildren").length < B ∧
    WordsAt (sigma.arrs "NewTransitionChildren") 0
      ((binaryWord length state).take index) ∧
    (binaryWord length state).drop index =
      binaryWord (length - index) (sigma.vars "binaryRemainder") ∧
    sigma.vars "binaryRemainder" < B ∧
    sigma.vars "binaryDivisor" < B ∧
    (index < length → sigma.vars "binaryDivisor" =
      2 ^ (length - index - 1)) ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    length ≤ maximumRank ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank ∧
    maximumRank < B

theorem beginBinaryWord_spec (B length state maximumRank : Nat) :
    Spec B (BinaryWordReady B length state maximumRank) beginBinaryWord
      (fun _ sigma' => BinaryWordInv B length state maximumRank sigma') 40 := by
  intro sigma hready
  rcases hready with ⟨hlength, hstateVar, hstate, hpowerB, hlengthB,
    hspace, harrayB, hmaximumRank, hlengthMaximumRank,
    hmaximumRankSpace, hmaximumRankB⟩
  have honeB : 1 < B :=
    lt_of_le_of_lt (Nat.one_le_pow length 2 (by omega)) hpowerB
  have hdivisorB : 2 ^ (length - 1) < B := by
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (Nat.sub_le length 1))
      hpowerB
  unfold beginBinaryWord Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [BinaryWordInv, WordsAt]
  all_goals try exact lt_trans hstate hpowerB

theorem binaryWordBody_spec (B length state maximumRank : Nat) :
    Spec B
      (fun sigma => BinaryWordInv B length state maximumRank sigma ∧
        sigma.vars "binaryIndex" < length)
      binaryWordBody
      (fun sigma sigma' => BinaryWordInv B length state maximumRank sigma' ∧
        sigma'.vars "binaryIndex" = sigma.vars "binaryIndex" + 1)
      100 := by
  intro sigma hready
  rcases hready with ⟨hinv, hindexLt⟩
  simp only [BinaryWordInv] at hinv
  rcases hinv with ⟨hindexLe, hlengthVar, hstateVar, hstate,
    hpowerB, hlengthB, hspace, harrayB, hwords, hsuffix,
    hremainderB, hdivisorB, hdivisor, hmaximumRank,
    hlengthMaximumRank, hmaximumRankSpace, hmaximumRankB⟩
  let index := sigma.vars "binaryIndex"
  let remainder := sigma.vars "binaryRemainder"
  let target := binaryWord length state
  have htargetLength : target.length = length := by
    simp [target]
  have htargetIndex : index < target.length := by
    simpa [index, htargetLength] using hindexLt
  have hremainingPos : 0 < length - index := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hremainingPos)
  have hdivisorEq : sigma.vars "binaryDivisor" = 2 ^ k := by
    rw [hdivisor hindexLt, hk]
    simp
  have hsuffix' : target.drop index = binaryWord (k + 1) remainder := by
    simpa [target, index, remainder, hk] using hsuffix
  rw [List.drop_eq_getElem_cons htargetIndex] at hsuffix'
  simp only [binaryWord] at hsuffix'
  have hdigit : target[index] = remainder / 2 ^ k :=
    List.cons.inj hsuffix' |>.1
  have htail : target.drop (index + 1) =
      binaryWord k (remainder % 2 ^ k) :=
    List.cons.inj hsuffix' |>.2
  have htargetMem := binaryWord_mem_words length state hstate
  have hdigitTwo : target[index] < 2 := by
    exact (mem_words_iff.mp htargetMem).2 _ (List.getElem_mem _)
  have htwoB : 2 < B := by
    have hlengthPos : 0 < length := by omega
    have htwoPower : 2 ≤ 2 ^ length := by
      cases length with
      | zero => omega
      | succ n =>
          simp only [pow_succ]
          simpa [Nat.mul_comm] using
            Nat.le_mul_of_pos_right 2 (Nat.two_pow_pos n)
    omega
  have hdigitB : remainder / 2 ^ k < B := by
    rw [← hdigit]
    exact lt_trans hdigitTwo htwoB
  have hslot : index < (sigma.arrs "NewTransitionChildren").length := by
    omega
  have hprefixLength : (target.take index).length = index := by
    rw [List.length_take, htargetLength, Nat.min_eq_left hindexLe]
  have hwordsTarget : WordsAt (sigma.arrs "NewTransitionChildren") 0
      (target.take index) := by
    simpa [target, index] using hwords
  have hwords' := wordsAt_set_append
    (value := remainder / 2 ^ k) hwordsTarget (by
      simpa [hprefixLength] using hslot)
  have htake : target.take (index + 1) =
      target.take index ++ [remainder / 2 ^ k] := by
    rw [List.take_succ_eq_append_getElem htargetIndex, hdigit]
  have hwordsNext : WordsAt
      ((sigma.arrs "NewTransitionChildren").set index (remainder / 2 ^ k))
      0 (target.take (index + 1)) := by
    simpa [hprefixLength, htake] using hwords'
  have hremainderEq :
      remainder - 2 ^ k * (remainder / 2 ^ k) = remainder % 2 ^ k := by
    exact Nat.mod_eq_sub_mul_div.symm
  have hremainderNextB :
      remainder - 2 ^ k * (remainder / 2 ^ k) < B :=
    lt_of_le_of_lt (Nat.sub_le remainder _) hremainderB
  have hproductB : 2 ^ k * (remainder / 2 ^ k) < B :=
    lt_of_le_of_lt (Nat.mul_div_le remainder (2 ^ k)) hremainderB
  have hdivisorNextB : 2 ^ k / 2 < B :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by simpa [hdivisorEq] using hdivisorB)
  have hsuffixNext : target.drop (index + 1) =
      binaryWord (length - (index + 1))
        (remainder - 2 ^ k * (remainder / 2 ^ k)) := by
    rw [hremainderEq]
    have hlenNext : length - (index + 1) = k := by omega
    rw [hlenNext]
    exact htail
  have hdivisorNext : index + 1 < length →
      2 ^ k / 2 = 2 ^ (length - (index + 1) - 1) := by
    intro hnext
    have hkpos : 0 < k := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    simp [pow_succ, Nat.mul_comm]
    omega
  unfold binaryWordBody Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [BinaryWordInv, index, remainder, target]

def binaryWordLoopCost (length : Nat) : Nat := 104 * length + 4

theorem binaryWordLoop_spec (B length state maximumRank : Nat) :
    Spec B (BinaryWordInv B length state maximumRank) binaryWordLoop
      (fun _ sigma' => BinaryWordInv B length state maximumRank sigma' ∧
        sigma'.vars "binaryIndex" = length)
      (binaryWordLoopCost length) := by
  unfold binaryWordLoop
  exact Spec.forRange "binaryIndex" "binaryLength"
    (BinaryWordInv B length state maximumRank) length 100
      (binaryWordLoopCost length)
    (by
      intro sigma hinv
      exact lt_of_le_of_lt hinv.1 hinv.2.2.2.2.2.1)
    (by
      intro sigma hinv
      rw [hinv.2.1]
      exact hinv.2.2.2.2.2.1)
    (by intro _ hinv; exact hinv.2.1)
    (by intro _ hinv; exact hinv.1)
    (binaryWordBody_spec B length state maximumRank)
    (fun _ h => h)
    (by
      intro sigma _
      unfold binaryWordLoopCost
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 104
          (Nat.sub_le length (sigma.vars "binaryIndex"))) 4)

def prepareBinaryWordCost (length : Nat) : Nat :=
  40 + binaryWordLoopCost length

theorem prepareBinaryWord_spec (B length state maximumRank : Nat) :
    Spec B (BinaryWordReady B length state maximumRank) prepareBinaryWord
      (fun _ sigma' => BinaryWordInv B length state maximumRank sigma' ∧
        sigma'.vars "binaryIndex" = length)
      (prepareBinaryWordCost length) := by
  unfold prepareBinaryWord prepareBinaryWordCost
  exact Spec.seq (beginBinaryWord_spec B length state maximumRank)
    (binaryWordLoop_spec B length state maximumRank)
    (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

theorem binaryWordInv_complete {B length state maximumRank : Nat} {sigma : Env}
    (hinv : BinaryWordInv B length state maximumRank sigma)
    (hdone : sigma.vars "binaryIndex" = length) :
    WordsAt (sigma.arrs "NewTransitionChildren") 0
      (binaryWord length state) := by
  have hwords := hinv.2.2.2.2.2.2.2.2.1
  rw [hdone] at hwords
  have htake : (binaryWord length state).take length =
      binaryWord length state := by
    have h : (binaryWord length state).take
        (binaryWord length state).length = binaryWord length state :=
      List.take_length
    rw [binaryWord_length] at h
    exact h
  rw [htake] at hwords
  exact hwords

def paddedBinaryWord (maximumRank length state : Nat) : List Nat :=
  binaryWord length state ++ List.replicate (maximumRank - length) 0

@[simp] theorem paddedBinaryWord_length {maximumRank length state : Nat}
    (hlength : length ≤ maximumRank) :
    (paddedBinaryWord maximumRank length state).length = maximumRank := by
  simp [paddedBinaryWord]
  omega

theorem preparedChildren_binaryWord (maximumRank length state symbol parent : Nat)
    (hlength : length ≤ maximumRank) :
    preparedChildren maximumRank (symbol, parent, binaryWord length state) =
      paddedBinaryWord maximumRank length state := by
  simpa [paddedBinaryWord, binaryWord_length] using
    preparedChildren_eq_append_replicate maximumRank
      (symbol, parent, binaryWord length state) (by
        simpa [binaryWord_length] using hlength)

private theorem replicate_succ_eq_append (n value : Nat) :
    List.replicate (n + 1) value = List.replicate n value ++ [value] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        List.replicate (n + 1 + 1) value =
            value :: List.replicate (n + 1) value := List.replicate_succ
        _ = value :: (List.replicate n value ++ [value]) := by rw [ih]
        _ = List.replicate (n + 1) value ++ [value] := by
          rw [List.replicate_succ]
          rfl

def BinaryPaddingInv (B length state maximumRank : Nat) (sigma : Env) : Prop :=
  let index := sigma.vars "binaryIndex"
  length ≤ index ∧ index ≤ maximumRank ∧
    sigma.vars "binaryLength" = length ∧
    sigma.vars "binaryState" = state ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    length ≤ maximumRank ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank ∧
    maximumRank < B ∧
    WordsAt (sigma.arrs "NewTransitionChildren") 0
      (binaryWord length state ++ List.replicate (index - length) 0)

theorem binaryWordInv_to_padding {B length state maximumRank : Nat}
    {sigma : Env}
    (hinv : BinaryWordInv B length state maximumRank sigma)
    (hdone : sigma.vars "binaryIndex" = length) :
    BinaryPaddingInv B length state maximumRank sigma := by
  have hwords := binaryWordInv_complete hinv hdone
  simp only [BinaryWordInv] at hinv
  rcases hinv with ⟨_, hlength, hstate, _, _, _, _, _, _, _, _, _, _,
    hmaximumRank, hlengthMaximumRank, harrayLength, hmaximumRankB⟩
  simp [BinaryPaddingInv, hdone, hlength, hstate, hmaximumRank,
    hlengthMaximumRank, harrayLength, hmaximumRankB, hwords]

theorem binaryPaddingBody_spec (B length state maximumRank : Nat) :
    Spec B
      (fun sigma => BinaryPaddingInv B length state maximumRank sigma ∧
        sigma.vars "binaryIndex" < maximumRank)
      binaryPaddingBody
      (fun sigma sigma' =>
        BinaryPaddingInv B length state maximumRank sigma' ∧
          sigma'.vars "binaryIndex" = sigma.vars "binaryIndex" + 1)
      30 := by
  intro sigma hready
  rcases hready with ⟨hinv, hindexLt⟩
  simp only [BinaryPaddingInv] at hinv
  rcases hinv with ⟨hlengthIndex, hindexMaximumRank, hlength,
    hstate, hmaximumRank, hlengthMaximumRank, harrayLength,
    hmaximumRankB, hwords⟩
  let index := sigma.vars "binaryIndex"
  have hindexB : index < B := by omega
  have hzeroB : 0 < B := by omega
  have hslot : index < (sigma.arrs "NewTransitionChildren").length := by
    simpa [index, harrayLength] using hindexLt
  have hprefixLength :
      (binaryWord length state ++ List.replicate (index - length) 0).length =
        index := by
    simp [binaryWord_length]
    omega
  have hwords' := wordsAt_set_append (value := 0) hwords (by
    simpa [hprefixLength, index] using hslot)
  have hcount : index + 1 - length = (index - length) + 1 := by omega
  have hnextWords :
      binaryWord length state ++ List.replicate (index + 1 - length) 0 =
        (binaryWord length state ++ List.replicate (index - length) 0) ++
          [0] := by
    rw [hcount, replicate_succ_eq_append]
    simp [List.append_assoc]
  unfold binaryPaddingBody Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [BinaryPaddingInv, index]
  all_goals omega

def binaryPaddingLoopCost (maximumRank : Nat) : Nat :=
  34 * maximumRank + 4

theorem binaryPaddingLoop_spec (B length state maximumRank : Nat) :
    Spec B (BinaryPaddingInv B length state maximumRank) binaryPaddingLoop
      (fun _ sigma' => BinaryPaddingInv B length state maximumRank sigma' ∧
        sigma'.vars "binaryIndex" = maximumRank)
      (binaryPaddingLoopCost maximumRank) := by
  unfold binaryPaddingLoop
  exact Spec.forRange "binaryIndex" "transitionMaximumRank"
    (BinaryPaddingInv B length state maximumRank) maximumRank 30
    (binaryPaddingLoopCost maximumRank)
    (by
      intro sigma hinv
      exact lt_of_le_of_lt hinv.2.1 hinv.2.2.2.2.2.2.2.1)
    (by
      intro sigma hinv
      rw [hinv.2.2.2.2.1]
      exact hinv.2.2.2.2.2.2.2.1)
    (by intro _ hinv; exact hinv.2.2.2.2.1)
    (by intro _ hinv; exact hinv.2.1)
    (binaryPaddingBody_spec B length state maximumRank)
    (fun _ h => h)
    (by
      intro sigma _
      unfold binaryPaddingLoopCost
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 34
          (Nat.sub_le maximumRank (sigma.vars "binaryIndex"))) 4)

def preparePaddedBinaryWordCost (length maximumRank : Nat) : Nat :=
  prepareBinaryWordCost length + binaryPaddingLoopCost maximumRank

private theorem eq_of_wordsAt_zero {array words : List Nat}
    (hwords : WordsAt array 0 words)
    (hlength : array.length = words.length) : array = words := by
  apply List.ext_get
  · exact hlength
  · intro i harray hword
    have hi := hwords i hword
    simp only [Nat.zero_add] at hi
    rw [List.getD_eq_getElem (l := array) (d := 0) harray,
      List.getD_eq_getElem (l := words) (d := 0) hword] at hi
    exact hi

theorem preparePaddedBinaryWord_spec (B length state maximumRank : Nat) :
    Spec B (BinaryWordReady B length state maximumRank)
      preparePaddedBinaryWord
      (fun _ sigma' =>
        sigma'.arrs "NewTransitionChildren" =
          paddedBinaryWord maximumRank length state ∧
        sigma'.vars "binaryIndex" = maximumRank)
      (preparePaddedBinaryWordCost length maximumRank) := by
  unfold preparePaddedBinaryWord preparePaddedBinaryWordCost
  refine (Spec.seq (prepareBinaryWord_spec B length state maximumRank)
    (binaryPaddingLoop_spec B length state maximumRank)
    (fun _ _ _ h => binaryWordInv_to_padding h.1 h.2)
    (fun _ _ _ _ _ h => h)).post ?_
  intro _ sigma' _ hpost
  refine ⟨?_, hpost.2⟩
  have hwords := hpost.1.2.2.2.2.2.2.2.2
  rw [hpost.2] at hwords
  have harrayLength := hpost.1.2.2.2.2.2.2.1
  apply eq_of_wordsAt_zero hwords
  rw [harrayLength]
  exact (paddedBinaryWord_length hpost.1.2.2.2.2.2.1).symm

private theorem preparePaddedBinaryWord_storageAgrees {sigma sigma' : Env}
    (hvars : ∀ y, y ∉ preparePaddedBinaryWord.wvars →
      sigma'.vars y = sigma.vars y)
    (harrs : ∀ a, a ∉ preparePaddedBinaryWord.warrs →
      sigma'.arrs a = sigma.arrs a) :
    CompilerStorageAgrees sigma sigma' := by
  refine ⟨hvars _ (by decide), hvars _ (by decide), hvars _ (by decide),
    harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide)⟩

def CompilerPaddedBinaryWordReady (B length state maximumRank : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  BinaryWordReady B length state maximumRank sigma ∧
    CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma

/-- Framed form used by automaton constructors: preparing the child row does
not disturb the append-only compiler heaps or descriptor stack. -/
theorem preparePaddedBinaryWord_compiler_spec
    (B length state maximumRank : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (CompilerPaddedBinaryWordReady B length state maximumRank stack
        transitionPrefix acceptingPrefix)
      preparePaddedBinaryWord
      (fun _ sigma' =>
        sigma'.arrs "NewTransitionChildren" =
            paddedBinaryWord maximumRank length state ∧
          sigma'.vars "binaryIndex" = maximumRank ∧
          CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep transitionPrefix sigma' ∧
          AcceptingHeapRep acceptingPrefix sigma')
      (preparePaddedBinaryWordCost length maximumRank) := by
  refine ((preparePaddedBinaryWord_spec B length state maximumRank).pre
    (fun _ h => h.1)).frame.post ?_
  intro sigma sigma' hpre hpost
  rcases hpre with ⟨hready, hstack, htransitionHeap, hacceptingHeap⟩
  rcases hpost with ⟨hrow, hvars, harrs, _, _⟩
  have hagrees := preparePaddedBinaryWord_storageAgrees hvars harrs
  exact ⟨hrow.1, hrow.2, compilerStackRep_of_agrees hagrees hstack,
    transitionHeapRep_of_agrees hagrees htransitionHeap,
    acceptingHeapRep_of_agrees hagrees hacceptingHeap⟩

def BinaryTransitionHeaderReady (B symbol length state : Nat)
    (predicate : Bool) (sigma : Env) : Prop :=
  sigma.vars "binarySymbol" = symbol ∧
    sigma.vars "binaryLength" = length ∧
    sigma.vars "binaryState" = state ∧
    sigma.vars "binaryPredicate" = predicate.toNat ∧
    symbol < B ∧ length < B ∧ state < B ∧ 1 < B

def BinaryTransitionHeaderPrepared (symbol length state : Nat)
    (predicate : Bool) (sigma : Env) : Prop :=
  sigma.vars "newTransitionSymbol" = symbol ∧
    sigma.vars "newTransitionParent" = binaryParent predicate state ∧
    sigma.vars "newTransitionArity" = length

theorem prepareBinaryTransitionHeader_spec (B symbol length state : Nat)
    (predicate : Bool) :
    Spec B (BinaryTransitionHeaderReady B symbol length state predicate)
      prepareBinaryTransitionHeader
      (fun _ sigma' =>
        BinaryTransitionHeaderPrepared symbol length state predicate sigma')
      50 := by
  intro sigma hready
  have hzeroB : 0 < B := by
    rcases hready with ⟨_, _, _, _, _, _, _, honeB⟩
    omega
  have honeB : 1 < B := by
    exact hready.2.2.2.2.2.2.2
  unfold prepareBinaryTransitionHeader
    Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [BinaryTransitionHeaderReady,
    BinaryTransitionHeaderPrepared, binaryParent]
  all_goals cases predicate <;> simp_all

def BinaryTransitionReady (B maximumRank : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol parent length state : Nat) (sigma : Env) : Prop :=
  CompilerPaddedBinaryWordReady B length state maximumRank stack
      transitionPrefix acceptingPrefix sigma ∧
    sigma.vars "newTransitionSymbol" = symbol ∧
    sigma.vars "newTransitionParent" = parent ∧
    sigma.vars "newTransitionArity" = length ∧
    symbol < B ∧ parent < B ∧
    (∀ value ∈ paddedBinaryWord maximumRank length state, value < B) ∧
    transitionPrefix.length + 3 + maximumRank < B ∧
    transitionPrefix.length + 3 + maximumRank ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

def appendBinaryTransitionRecordCost (length maximumRank : Nat) : Nat :=
  preparePaddedBinaryWordCost length maximumRank +
    transitionRecordCost maximumRank

/-- One complete transition is now generated and appended inside the charged
execution.  The semantic child list is the arithmetic binary word; padding is
identified with `preparedChildren`, so the generic exact-record theorem
applies without an advice array or an uncharged Lean conversion. -/
theorem appendBinaryTransitionRecord_spec
    (B maximumRank : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol parent length state : Nat) (h0 : 0 < B) :
    Spec B
      (BinaryTransitionReady B maximumRank stack transitionPrefix
        acceptingPrefix symbol parent length state)
      appendBinaryTransitionRecord
      (fun _ sigma' =>
        CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep
            (transitionPrefix ++ encodeTransitionFixed maximumRank
              (symbol, parent, binaryWord length state)) sigma' ∧
          AcceptingHeapRep acceptingPrefix sigma' ∧
          sigma'.arrs "NewTransitionChildren" =
            paddedBinaryWord maximumRank length state)
      (appendBinaryTransitionRecordCost length maximumRank) := by
  unfold appendBinaryTransitionRecord appendBinaryTransitionRecordCost
  refine Spec.seq
    ((preparePaddedBinaryWord_compiler_spec B length state maximumRank stack
      transitionPrefix acceptingPrefix).pre (fun _ h => h.1) |>.frame)
    (appendEncodedTransition_spec B maximumRank stack transitionPrefix
      (symbol, parent, binaryWord length state) h0 |>.frame)
    ?_ ?_
  intro sigma sigma' hpre hpost
  rcases hpre with ⟨hcompilerReady, hsymbol, hparent, harity,
    hsymbolB, hparentB, hvaluesB, hrecordB, hcapacity, hheapLengthB⟩
  rcases hpost with ⟨hprepared, hvars, harrs, _, _⟩
  rcases hprepared with ⟨hrow, hindex, hstack, htransitionHeap,
    hacceptingHeap⟩
  rcases hcompilerReady.1 with ⟨hlength, hstate, hstateBound,
    hpowerB, hlengthB, hlengthSpace, hrowLengthB, hmaximumRank,
    hlengthMaximumRank, hrowLength, hmaximumRankB⟩
  have hsymbol' : sigma'.vars "newTransitionSymbol" = symbol :=
    (hvars _ (by decide)).trans hsymbol
  have hparent' : sigma'.vars "newTransitionParent" = parent :=
    (hvars _ (by decide)).trans hparent
  have harity' : sigma'.vars "newTransitionArity" = length :=
    (hvars _ (by decide)).trans harity
  have hmaximumRank' : sigma'.vars "transitionMaximumRank" = maximumRank :=
    (hvars _ (by decide)).trans hmaximumRank
  have htransitionArray := harrs "CompiledTransitions" (by decide)
  have hcapacity' : transitionPrefix.length + 3 + maximumRank ≤
      (sigma'.arrs "CompiledTransitions").length := by
    rw [htransitionArray]
    exact hcapacity
  have hheapLengthB' : (sigma'.arrs "CompiledTransitions").length < B := by
    rw [htransitionArray]
    exact hheapLengthB
  show EncodedTransitionReady B maximumRank stack transitionPrefix
    (symbol, parent, binaryWord length state) sigma'
  simp only [EncodedTransitionReady, TransitionRecordReady]
  refine ⟨hstack, htransitionHeap, hsymbol', hparent', (by
      simpa using harity'), ?_, ?_,
    hmaximumRank', hsymbolB, hparentB, (by simpa using hlengthB), ?_, hrecordB,
    hcapacity', hheapLengthB'⟩
  · rw [preparedChildren_binaryWord maximumRank length state symbol parent
      hlengthMaximumRank]
    exact hrow
  · rw [preparedChildren_binaryWord maximumRank length state symbol parent
      hlengthMaximumRank]
    exact paddedBinaryWord_length hlengthMaximumRank
  · intro value hvalue
    exact hvaluesB value (by
      rwa [preparedChildren_binaryWord maximumRank length state symbol parent
        hlengthMaximumRank] at hvalue)
  intro _ sigma' sigma'' _ hprepared hfinal
  rcases hprepared with ⟨hpreparedCore, _, _, _, _⟩
  rcases hpreparedCore with ⟨hrowPrepared, _, _, _, hacceptingHeap⟩
  rcases hfinal with
    ⟨⟨hstackFinal, htransitionFinal⟩, hvarsFinal, harrsFinal, _, _⟩
  have hacceptingFinal : AcceptingHeapRep acceptingPrefix sigma'' := by
    have hcursor := hvarsFinal "compiledAcceptingWords" (by decide)
    have harray := harrsFinal "CompiledAccepting" (by decide)
    exact ⟨hcursor.trans hacceptingHeap.1, by
      rw [harray]
      exact hacceptingHeap.2⟩
  have hrowFinal : sigma''.arrs "NewTransitionChildren" =
      paddedBinaryWord maximumRank length state :=
    (harrsFinal "NewTransitionChildren" (by decide)).trans hrowPrepared
  exact ⟨hstackFinal, htransitionFinal, hacceptingFinal, hrowFinal⟩

def CountedBinaryTransitionReady (B maximumRank : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol length state : Nat) (predicate : Bool) (count : Nat)
    (sigma : Env) : Prop :=
  BinaryTransitionReady B maximumRank stack transitionPrefix acceptingPrefix
      symbol (binaryParent predicate state) length state sigma ∧
    sigma.vars "newTransitionCount" = count ∧ count + 1 < B

def appendCountedBinaryTransitionRecordCost
    (length maximumRank : Nat) : Nat :=
  appendBinaryTransitionRecordCost length maximumRank + 4

private theorem incrementTransitionCount_spec (B count : Nat) :
    Spec B
      (fun sigma => sigma.vars "newTransitionCount" = count ∧ count + 1 < B)
      (.assign "newTransitionCount"
        (.add (.var "newTransitionCount") (.lit 1)))
      (fun _ sigma' => sigma'.vars "newTransitionCount" = count + 1)
      4 := by
  intro sigma hready
  run_vcg
  all_goals simp_all

private theorem incrementBinaryState_spec (B state : Nat) :
    Spec B
      (fun sigma => sigma.vars "binaryState" = state ∧ state + 1 < B)
      (.assign "binaryState" (.add (.var "binaryState") (.lit 1)))
      (fun _ sigma' => sigma'.vars "binaryState" = state + 1)
      4 := by
  intro sigma hready
  run_vcg
  all_goals simp_all

/-- Counted wrapper used by the inner row loop. The heap suffix grows by one
exact semantic transition, and the accepting heap remains untouched. -/
theorem appendCountedBinaryTransitionRecord_spec
    (B maximumRank : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol length state : Nat) (predicate : Bool) (count : Nat)
    (h0 : 0 < B) :
    Spec B
      (CountedBinaryTransitionReady B maximumRank stack transitionPrefix
        acceptingPrefix symbol length state predicate count)
      appendCountedBinaryTransitionRecord
      (fun _ sigma' =>
        CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep
            (transitionPrefix ++ encodeTransitionFixed maximumRank
              (generatedBinaryTransition symbol length state predicate)) sigma' ∧
          AcceptingHeapRep acceptingPrefix sigma' ∧
          sigma'.arrs "NewTransitionChildren" =
            paddedBinaryWord maximumRank length state ∧
          sigma'.vars "newTransitionCount" = count + 1)
      (appendCountedBinaryTransitionRecordCost length maximumRank) := by
  unfold appendCountedBinaryTransitionRecord
    appendCountedBinaryTransitionRecordCost
  refine Spec.seq
    ((appendBinaryTransitionRecord_spec B maximumRank stack transitionPrefix
      acceptingPrefix symbol (binaryParent predicate state) length state h0).pre
        (fun _ h => h.1) |>.frame)
    ((incrementTransitionCount_spec B count).frame)
    ?_ ?_
  · intro _ sigma' hpre hpost
    rcases hpre with ⟨_, hcount, hcountB⟩
    rcases hpost with ⟨_, hvars, _, _, _⟩
    exact ⟨(hvars "newTransitionCount" (by decide)).trans hcount,
      hcountB⟩
  · intro _ sigma' sigma'' _ hrecord hincrement
    rcases hrecord with ⟨hrecordCore, _, _, _, _⟩
    rcases hrecordCore with ⟨hstack, htransition, haccepting, hrow⟩
    rcases hincrement with ⟨hcount, hvars, harrs, _, _⟩
    have hagrees : CompilerStorageAgrees sigma' sigma'' := by
      exact ⟨hvars _ (by decide), hvars _ (by decide),
        hvars _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide), harrs _ (by decide)⟩
    exact ⟨compilerStackRep_of_agrees hagrees hstack,
      transitionHeapRep_of_agrees hagrees htransition,
      acceptingHeapRep_of_agrees hagrees haccepting,
      (harrs "NewTransitionChildren" (by decide)).trans hrow, hcount⟩

theorem binaryParent_lt (predicate : Bool) (state B : Nat) (h1 : 1 < B) :
    binaryParent predicate state < B := by
  by_cases hstate : state = 0 <;> cases predicate <;>
    simp [binaryParent, hstate] <;> omega

theorem paddedBinaryWord_value_lt_two {maximumRank length state value : Nat}
    (hstate : state < 2 ^ length)
    (hvalue : value ∈ paddedBinaryWord maximumRank length state) :
    value < 2 := by
  simp only [paddedBinaryWord, List.mem_append, List.mem_replicate] at hvalue
  rcases hvalue with hvalue | ⟨_, rfl⟩
  · exact binaryWord_value_lt_two hstate hvalue
  · omega

def BinaryRowBodyReady (B maximumRank : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol length state : Nat) (predicate : Bool) (count : Nat)
    (sigma : Env) : Prop :=
  CompilerPaddedBinaryWordReady B length state maximumRank stack
      transitionPrefix acceptingPrefix sigma ∧
    BinaryTransitionHeaderReady B symbol length state predicate sigma ∧
    sigma.vars "newTransitionCount" = count ∧ count + 1 < B ∧
    transitionPrefix.length + 3 + maximumRank < B ∧
    transitionPrefix.length + 3 + maximumRank ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

private theorem headerStorageAgrees {sigma sigma' : Env}
    (hvars : ∀ y, y ∉ prepareBinaryTransitionHeader.wvars →
      sigma'.vars y = sigma.vars y)
    (harrs : ∀ a, a ∉ prepareBinaryTransitionHeader.warrs →
      sigma'.arrs a = sigma.arrs a) :
    CompilerStorageAgrees sigma sigma' := by
  exact ⟨hvars _ (by decide), hvars _ (by decide), hvars _ (by decide),
    harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide)⟩

private theorem compilerPaddedReady_after_header
    {B length state maximumRank : Nat} {stack : List AutomatonCode}
    {transitionPrefix acceptingPrefix : List Nat} {sigma sigma' : Env}
    (hready : CompilerPaddedBinaryWordReady B length state maximumRank stack
      transitionPrefix acceptingPrefix sigma)
    (hvars : ∀ y, y ∉ prepareBinaryTransitionHeader.wvars →
      sigma'.vars y = sigma.vars y)
    (harrs : ∀ a, a ∉ prepareBinaryTransitionHeader.warrs →
      sigma'.arrs a = sigma.arrs a) :
    CompilerPaddedBinaryWordReady B length state maximumRank stack
      transitionPrefix acceptingPrefix sigma' := by
  rcases hready with
    ⟨⟨hlength, hstate, hstateBound, hpowerB, hlengthB, hspace,
      hchildrenB, hmaximumRank, hlengthRank, hchildrenLength,
      hmaximumRankB⟩, hstack, htransition, haccepting⟩
  have hagrees := headerStorageAgrees hvars harrs
  refine ⟨⟨(hvars _ (by decide)).trans hlength,
    (hvars _ (by decide)).trans hstate, hstateBound, hpowerB, hlengthB,
    ?_, ?_, (hvars _ (by decide)).trans hmaximumRank, hlengthRank,
    ?_, hmaximumRankB⟩, compilerStackRep_of_agrees hagrees hstack,
    transitionHeapRep_of_agrees hagrees htransition,
    acceptingHeapRep_of_agrees hagrees haccepting⟩
  · rw [harrs _ (by decide)]
    exact hspace
  · rw [harrs _ (by decide)]
    exact hchildrenB
  · rw [harrs _ (by decide)]
    exact hchildrenLength

def binaryRowsBodyCost (length maximumRank : Nat) : Nat :=
  (50 + appendCountedBinaryTransitionRecordCost length maximumRank) + 4

/-- One inner-loop iteration emits the exact transition associated with the
current numeric binary row, increments the descriptor count, and advances to
the next row. -/
theorem binaryRowsBody_spec
    (B maximumRank : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol length state : Nat) (predicate : Bool) (count : Nat)
    (h0 : 0 < B) :
    Spec B
      (BinaryRowBodyReady B maximumRank stack transitionPrefix
        acceptingPrefix symbol length state predicate count)
      binaryRowsBody
      (fun _ sigma' =>
        CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep
            (transitionPrefix ++ encodeTransitionFixed maximumRank
              (generatedBinaryTransition symbol length state predicate)) sigma' ∧
          AcceptingHeapRep acceptingPrefix sigma' ∧
          sigma'.arrs "NewTransitionChildren" =
            paddedBinaryWord maximumRank length state ∧
          sigma'.vars "newTransitionCount" = count + 1 ∧
          sigma'.vars "binaryState" = state + 1)
      (binaryRowsBodyCost length maximumRank) := by
  unfold binaryRowsBody binaryRowsBodyCost
  have hheaderAppend : Spec B
      (BinaryRowBodyReady B maximumRank stack transitionPrefix
        acceptingPrefix symbol length state predicate count)
      (.seq prepareBinaryTransitionHeader
        appendCountedBinaryTransitionRecord)
      (fun _ sigma' =>
        (CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep
            (transitionPrefix ++ encodeTransitionFixed maximumRank
              (generatedBinaryTransition symbol length state predicate)) sigma' ∧
          AcceptingHeapRep acceptingPrefix sigma' ∧
          sigma'.arrs "NewTransitionChildren" =
            paddedBinaryWord maximumRank length state ∧
          sigma'.vars "newTransitionCount" = count + 1) ∧
          sigma'.vars "binaryState" = state)
      (50 + appendCountedBinaryTransitionRecordCost length maximumRank) := by
    refine Spec.seq
      ((prepareBinaryTransitionHeader_spec B symbol length state predicate).pre
        (fun _ h => h.2.1) |>.frame)
      ((appendCountedBinaryTransitionRecord_spec B maximumRank stack
        transitionPrefix acceptingPrefix symbol length state predicate count
        h0).frame)
      ?_ ?_
    · intro _ sigma' hpre hheader
      rcases hpre with
        ⟨hcompiler, hheaderReady, hcount, hcountB, hrecordB, hcapacity,
          hheapLengthB⟩
      rcases hheader with ⟨hprepared, hvars, harrs, _, _⟩
      have hcompiler' := compilerPaddedReady_after_header hcompiler hvars harrs
      have hcount' := (hvars "newTransitionCount" (by decide)).trans hcount
      have htransitionArray := harrs "CompiledTransitions" (by decide)
      have hcapacity' : transitionPrefix.length + 3 + maximumRank ≤
          (sigma'.arrs "CompiledTransitions").length := by
        rw [htransitionArray]
        exact hcapacity
      have hheapLengthB' :
          (sigma'.arrs "CompiledTransitions").length < B := by
        rw [htransitionArray]
        exact hheapLengthB
      refine ⟨?_, hcount', hcountB⟩
      rcases hcompiler'.1 with ⟨_, _, hstateBound, _, _, _, _, _, _, _, _⟩
      refine ⟨hcompiler', hprepared.1, hprepared.2.1, hprepared.2.2,
        hheaderReady.2.2.2.2.1,
        binaryParent_lt predicate state B hheaderReady.2.2.2.2.2.2.2,
        ?_, hrecordB, hcapacity', hheapLengthB'⟩
      intro value hvalue
      have hvalueTwo := paddedBinaryWord_value_lt_two hstateBound hvalue
      omega
    · intro sigma sigma' sigma'' hpre hheader happended
      rcases hpre with ⟨hcompiler, -⟩
      rcases hheader with ⟨_, hheaderVars, _, _, _⟩
      rcases happended with ⟨happendCore, happendVars, _, _, _⟩
      have hstateHeader : sigma'.vars "binaryState" = state :=
        (hheaderVars "binaryState" (by decide)).trans hcompiler.1.2.1
      have hstateFinal : sigma''.vars "binaryState" = state :=
        (happendVars "binaryState" (by decide)).trans hstateHeader
      exact ⟨happendCore, hstateFinal⟩
  refine Spec.seq hheaderAppend
    ((incrementBinaryState_spec B state).frame)
    ?_ ?_
  · intro _ _ hpre hpost
    exact ⟨hpost.2, by
      have hstateBound := hpre.1.1.2.2.1
      have hrowLimitB := hpre.1.1.2.2.2.1
      omega⟩
  · intro _ sigma' sigma'' _ hrecord hincrement
    rcases hrecord with ⟨hrecordCore, _⟩
    rcases hrecordCore with ⟨hstack, htransition, haccepting, hrow, hcount⟩
    rcases hincrement with ⟨hstate, hvars, harrs, _, _⟩
    have hagrees : CompilerStorageAgrees sigma' sigma'' := by
      exact ⟨hvars _ (by decide), hvars _ (by decide),
        hvars _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide), harrs _ (by decide)⟩
    exact ⟨compilerStackRep_of_agrees hagrees hstack,
      transitionHeapRep_of_agrees hagrees htransition,
      acceptingHeapRep_of_agrees hagrees haccepting,
      (harrs "NewTransitionChildren" (by decide)).trans hrow,
      (hvars "newTransitionCount" (by decide)).trans hcount, hstate⟩

/-- Complete invariant for enumerating all binary child rows of one symbol.
The only dynamic mathematical prefix is indexed by `binaryState`; the final
capacity assumptions reserve the whole remaining fixed-width segment once. -/
def BinaryRowsInv (B maximumRank : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol length : Nat) (predicate : Bool) (count : Nat)
    (sigma : Env) : Prop :=
  let state := sigma.vars "binaryState"
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++
        binaryRowsPrefix maximumRank symbol length predicate state) sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "binarySymbol" = symbol ∧
    sigma.vars "binaryLength" = length ∧
    sigma.vars "binaryRowLimit" = 2 ^ length ∧
    sigma.vars "binaryPredicate" = predicate.toNat ∧
    sigma.vars "newTransitionCount" = count + state ∧
    state ≤ 2 ^ length ∧ 2 ^ length < B ∧
    length ≤ maximumRank ∧ maximumRank < B ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    symbol < B ∧ 1 < B ∧ count + 2 ^ length < B ∧
    transitionPrefix.length + 2 ^ length * (maximumRank + 3) < B ∧
    transitionPrefix.length + 2 ^ length * (maximumRank + 3) ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

private theorem binaryRowsInv_bodyReady
    {B maximumRank : Nat} {stack : List AutomatonCode}
    {transitionPrefix acceptingPrefix : List Nat}
    {symbol length : Nat} {predicate : Bool} {count : Nat} {sigma : Env}
    (hinv : BinaryRowsInv B maximumRank stack transitionPrefix
      acceptingPrefix symbol length predicate count sigma)
    (hstateLt : sigma.vars "binaryState" < 2 ^ length) :
    BinaryRowBodyReady B maximumRank stack
      (transitionPrefix ++ binaryRowsPrefix maximumRank symbol length predicate
        (sigma.vars "binaryState"))
      acceptingPrefix symbol length (sigma.vars "binaryState") predicate
      (count + sigma.vars "binaryState") sigma := by
  let state := sigma.vars "binaryState"
  rcases hinv with ⟨hstack, htransition, haccepting, hsymbol, hlength,
    hlimit, hpredicate, hcount, hstateLe, hlimitB, hlengthRank,
    hmaximumRankB, hchildrenLength, hmaximumRank, hsymbolB, honeB,
    hcountLimitB, hwordsLimitB, hcapacity, hheapLengthB⟩
  have hlengthB : length < B := lt_of_le_of_lt hlengthRank hmaximumRankB
  have hstateB : state < B := lt_trans hstateLt hlimitB
  have hchildrenB : (sigma.arrs "NewTransitionChildren").length < B := by
    rw [hchildrenLength]
    exact hmaximumRankB
  have hlengthSpace : length ≤
      (sigma.arrs "NewTransitionChildren").length := by
    rw [hchildrenLength]
    exact hlengthRank
  have hcountNextB : count + state + 1 < B := by
    have hnextLe : state + 1 ≤ 2 ^ length := Nat.succ_le_iff.mpr hstateLt
    omega
  have hnextLe : state + 1 ≤ 2 ^ length := Nat.succ_le_iff.mpr hstateLt
  have hmulLe : (state + 1) * (maximumRank + 3) ≤
      2 ^ length * (maximumRank + 3) :=
    Nat.mul_le_mul_right (maximumRank + 3) hnextLe
  let currentWords := transitionPrefix ++
    binaryRowsPrefix maximumRank symbol length predicate state
  have hrecordLength : currentWords.length + 3 + maximumRank =
      transitionPrefix.length + (state + 1) * (maximumRank + 3) := by
    simp [currentWords]
    ring
  have hrecordB : currentWords.length + 3 + maximumRank < B := by
    rw [hrecordLength]
    omega
  have hrecordCapacity : currentWords.length + 3 + maximumRank ≤
      (sigma.arrs "CompiledTransitions").length := by
    rw [hrecordLength]
    omega
  refine ⟨?_, ?_, hcount, hcountNextB, hrecordB, hrecordCapacity,
    hheapLengthB⟩
  · refine ⟨⟨hlength, rfl, hstateLt, hlimitB, hlengthB,
      hlengthSpace, hchildrenB, hmaximumRank, hlengthRank,
      hchildrenLength, hmaximumRankB⟩, hstack, ?_, haccepting⟩
    simpa [currentWords] using htransition
  · exact ⟨hsymbol, hlength, rfl, hpredicate, hsymbolB,
      hlengthB, hstateB, honeB⟩

def binaryRowsLoopCost (length maximumRank : Nat) : Nat :=
  (binaryRowsBodyCost length maximumRank + 4) * 2 ^ length + 4

/-- The complete inner loop emits every binary row for one symbol, in the
same order as the pure automaton code. -/
theorem binaryRowsLoop_spec
    (B maximumRank : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol length : Nat) (predicate : Bool) (count : Nat)
    (h0 : 0 < B) :
    Spec B
      (BinaryRowsInv B maximumRank stack transitionPrefix acceptingPrefix
        symbol length predicate count)
      binaryRowsLoop
      (fun _ sigma' =>
        BinaryRowsInv B maximumRank stack transitionPrefix acceptingPrefix
            symbol length predicate count sigma' ∧
          sigma'.vars "binaryState" = 2 ^ length)
      (binaryRowsLoopCost length maximumRank) := by
  unfold binaryRowsLoop
  apply Spec.forRange "binaryState" "binaryRowLimit"
    (BinaryRowsInv B maximumRank stack transitionPrefix acceptingPrefix
      symbol length predicate count)
    (2 ^ length) (binaryRowsBodyCost length maximumRank)
    (binaryRowsLoopCost length maximumRank)
  · intro sigma hinv
    rcases hinv with ⟨_, _, _, _, _, _, _, _, hstateLe, hlimitB, -⟩
    omega
  · intro _ hinv
    rcases hinv with ⟨_, _, _, _, _, hlimit, _, _, _, hlimitB, -⟩
    rw [hlimit]
    exact hlimitB
  · intro _ hinv
    rcases hinv with ⟨_, _, _, _, _, hlimit, -⟩
    exact hlimit
  · intro _ hinv
    rcases hinv with ⟨_, _, _, _, _, _, _, _, hstateLe, -⟩
    exact hstateLe
  · intro sigma hpre
    let state := sigma.vars "binaryState"
    have hstateLt := hpre.2
    have hready := binaryRowsInv_bodyReady hpre.1 hstateLt
    rcases hpre.1 with ⟨_, _, _, hsymbol0, hlength0, hlimit0,
      hpredicate0, _, _, hlimitB0, hlengthRank0, hmaximumRankB0,
      _, hmaximumRank0, hsymbolB0, honeB0, hcountLimitB0,
      hwordsLimitB0, hcapacity0, hheapLengthB0⟩
    obtain ⟨sigma', run, hframed, htableLength⟩ :=
      (Lax53Proofs.spec_arrayLength_eq
        ((binaryRowsBody_spec B maximumRank stack
          (transitionPrefix ++ binaryRowsPrefix maximumRank symbol length
            predicate state)
          acceptingPrefix symbol length state predicate (count + state)
          h0).frame)
        "CompiledTransitions").run hready
    rcases hframed with ⟨hbody, hvars, _, _, _⟩
    rcases hbody with
      ⟨hstack, htransition, haccepting, hrow, hcount, hstate⟩
    have htransition' : TransitionHeapRep
        (transitionPrefix ++ binaryRowsPrefix maximumRank symbol length
          predicate (state + 1)) sigma' := by
      rw [binaryRowsPrefix_succ]
      simpa [List.append_assoc] using htransition
    have hchildrenLength :
        (sigma'.arrs "NewTransitionChildren").length = maximumRank := by
      rw [hrow, paddedBinaryWord_length hlengthRank0]
    have hcount' : sigma'.vars "newTransitionCount" = count + (state + 1) := by
      omega
    have hstateLe : state + 1 ≤ 2 ^ length := Nat.succ_le_iff.mpr hstateLt
    have htransitionFinal : TransitionHeapRep
        (transitionPrefix ++ binaryRowsPrefix maximumRank symbol length
          predicate (sigma'.vars "binaryState")) sigma' := by
      rw [hstate]
      exact htransition'
    have hcountFinal :
        sigma'.vars "newTransitionCount" =
          count + sigma'.vars "binaryState" := by
      rw [hstate]
      exact hcount'
    have hstateLeFinal : sigma'.vars "binaryState" ≤ 2 ^ length := by
      rw [hstate]
      exact hstateLe
    have hsymbol := (hvars "binarySymbol" (by decide)).trans hsymbol0
    have hlength := (hvars "binaryLength" (by decide)).trans hlength0
    have hlimit := (hvars "binaryRowLimit" (by decide)).trans hlimit0
    have hpredicate :=
      (hvars "binaryPredicate" (by decide)).trans hpredicate0
    have hmaximumRank :=
      (hvars "transitionMaximumRank" (by decide)).trans hmaximumRank0
    refine ⟨sigma', run, ?_, hstate⟩
    change BinaryRowsInv B maximumRank stack transitionPrefix acceptingPrefix
      symbol length predicate count sigma'
    refine ⟨hstack, htransitionFinal, haccepting, hsymbol, hlength, hlimit,
      hpredicate, hcountFinal, hstateLeFinal, hlimitB0, hlengthRank0,
      hmaximumRankB0, hchildrenLength, hmaximumRank, hsymbolB0,
      honeB0, hcountLimitB0, hwordsLimitB0, ?_, ?_⟩
    · rw [htableLength]
      exact hcapacity0
    · rw [htableLength]
      exact hheapLengthB0
  · intro _ h
    exact h
  · intro sigma _
    unfold binaryRowsLoopCost
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left (binaryRowsBodyCost length maximumRank + 4)
        (Nat.sub_le (2 ^ length) (sigma.vars "binaryState"))) 4

def BinaryRowsStartReady (B maximumRank : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol length : Nat) (predicate : Bool) (count : Nat)
    (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "binarySymbol" = symbol ∧
    sigma.vars "binaryLength" = length ∧
    sigma.vars "binaryPredicate" = predicate.toNat ∧
    sigma.vars "newTransitionCount" = count ∧
    2 ^ length < B ∧ length ≤ maximumRank ∧ maximumRank < B ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    symbol < B ∧ 1 < B ∧ count + 2 ^ length < B ∧
    transitionPrefix.length + 2 ^ length * (maximumRank + 3) < B ∧
    transitionPrefix.length + 2 ^ length * (maximumRank + 3) ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

private theorem beginBinaryRows_scalars_spec (B length : Nat) :
    Spec B
      (fun sigma => sigma.vars "binaryLength" = length ∧
        length < B ∧ 2 ^ length < B ∧ 1 < B)
      beginBinaryRows
      (fun _ sigma' => sigma'.vars "binaryState" = 0 ∧
        sigma'.vars "binaryRowLimit" = 2 ^ length)
      20 := by
  intro sigma hready
  unfold beginBinaryRows Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all

private theorem beginBinaryRows_storageAgrees {sigma sigma' : Env}
    (hvars : ∀ y, y ∉ beginBinaryRows.wvars →
      sigma'.vars y = sigma.vars y)
    (harrs : ∀ a, a ∉ beginBinaryRows.warrs →
      sigma'.arrs a = sigma.arrs a) :
    CompilerStorageAgrees sigma sigma' := by
  exact ⟨hvars _ (by decide), hvars _ (by decide), hvars _ (by decide),
    harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide)⟩

theorem beginBinaryRows_spec
    (B maximumRank : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol length : Nat) (predicate : Bool) (count : Nat) :
    Spec B
      (BinaryRowsStartReady B maximumRank stack transitionPrefix
        acceptingPrefix symbol length predicate count)
      beginBinaryRows
      (fun _ sigma' => BinaryRowsInv B maximumRank stack transitionPrefix
        acceptingPrefix symbol length predicate count sigma')
      20 := by
  refine ((beginBinaryRows_scalars_spec B length).pre ?_ |>.frame).post ?_
  · intro _ hready
    rcases hready with ⟨_, _, _, _, hlength, _, _, hlimitB,
      hlengthRank, hmaximumRankB, _, _, _, honeB, -⟩
    exact ⟨hlength, lt_of_le_of_lt hlengthRank hmaximumRankB,
      hlimitB, honeB⟩
  · intro sigma sigma' hpre hpost
    rcases hpre with ⟨hstack, htransition, haccepting, hsymbol, hlength,
      hpredicate, hcount, hlimitB, hlengthRank, hmaximumRankB,
      hchildrenLength, hmaximumRank, hsymbolB, honeB, hcountLimitB,
      hwordsLimitB, hcapacity, hheapLengthB⟩
    rcases hpost with ⟨⟨hstate, hlimit⟩, hvars, harrs, _, _⟩
    have hagrees := beginBinaryRows_storageAgrees hvars harrs
    have htransition' : TransitionHeapRep
        (transitionPrefix ++
          binaryRowsPrefix maximumRank symbol length predicate 0) sigma' := by
      simpa using transitionHeapRep_of_agrees hagrees htransition
    have htransitionFinal : TransitionHeapRep
        (transitionPrefix ++
          binaryRowsPrefix maximumRank symbol length predicate
            (sigma'.vars "binaryState")) sigma' := by
      rw [hstate]
      exact htransition'
    have hchildrenLength' :
        (sigma'.arrs "NewTransitionChildren").length = maximumRank := by
      rw [harrs "NewTransitionChildren" (by decide)]
      exact hchildrenLength
    have hcapacity' :
        transitionPrefix.length + 2 ^ length * (maximumRank + 3) ≤
          (sigma'.arrs "CompiledTransitions").length := by
      rw [harrs "CompiledTransitions" (by decide)]
      exact hcapacity
    have hheapLengthB' :
        (sigma'.arrs "CompiledTransitions").length < B := by
      rw [harrs "CompiledTransitions" (by decide)]
      exact hheapLengthB
    change BinaryRowsInv B maximumRank stack transitionPrefix acceptingPrefix
      symbol length predicate count sigma'
    refine ⟨compilerStackRep_of_agrees hagrees hstack, htransitionFinal,
      acceptingHeapRep_of_agrees hagrees haccepting,
      (hvars "binarySymbol" (by decide)).trans hsymbol,
      (hvars "binaryLength" (by decide)).trans hlength, hlimit,
      (hvars "binaryPredicate" (by decide)).trans hpredicate, ?_, ?_,
      hlimitB, hlengthRank, hmaximumRankB, hchildrenLength',
      (hvars "transitionMaximumRank" (by decide)).trans hmaximumRank,
      hsymbolB, honeB, hcountLimitB, hwordsLimitB, hcapacity',
      hheapLengthB'⟩
    · rw [hstate, (hvars "newTransitionCount" (by decide)).trans hcount]
      omega
    · rw [hstate]
      exact Nat.zero_le _

def compileBinarySymbolCost (length maximumRank : Nat) : Nat :=
  20 + binaryRowsLoopCost length maximumRank

/-- Complete construction of all transitions for one symbol. -/
theorem compileBinarySymbol_spec
    (B maximumRank : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (symbol length : Nat) (predicate : Bool) (count : Nat)
    (h0 : 0 < B) :
    Spec B
      (BinaryRowsStartReady B maximumRank stack transitionPrefix
        acceptingPrefix symbol length predicate count)
      compileBinarySymbol
      (fun _ sigma' =>
        CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep
            (transitionPrefix ++ binaryRowsPrefix maximumRank symbol length
              predicate (2 ^ length)) sigma' ∧
          AcceptingHeapRep acceptingPrefix sigma' ∧
          sigma'.vars "newTransitionCount" = count + 2 ^ length ∧
          sigma'.vars "binaryState" = 2 ^ length)
      (compileBinarySymbolCost length maximumRank) := by
  unfold compileBinarySymbol compileBinarySymbolCost
  refine Spec.seq
    (beginBinaryRows_spec B maximumRank stack transitionPrefix acceptingPrefix
      symbol length predicate count)
    (binaryRowsLoop_spec B maximumRank stack transitionPrefix acceptingPrefix
      symbol length predicate count h0)
    (fun _ _ _ h => h) ?_
  intro _ _ _ _ _ hdone
  rcases hdone with ⟨hinv, hstate⟩
  have hstack := hinv.1
  have htransition := hinv.2.1
  have haccepting := hinv.2.2.1
  have hcount := hinv.2.2.2.2.2.2.2.1
  rw [hstate] at htransition hcount
  exact ⟨hstack, htransition, haccepting, hcount, hstate⟩

end Lax53Proofs.MSORamCompilerBinaryWord
