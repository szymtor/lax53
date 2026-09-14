import Lax842588Proofs.MSORamCompilerBinaryWord
import Lax842588Proofs.MSORamCompilerBuild
import Lax842588Proofs.AutomatonRamArenaAlphabet

/-!
The outer structural-alphabet layer for the charged two-state "somewhere"
automata.

The decoded original alphabet is already present as the rank prefix of `P`.
Packed marked symbols are enumerated arithmetically.  For each one, the
machine recovers its original symbol, reads that symbol's rank, computes the
formula-specific predicate bit, and invokes the checked binary-row loop.
No marked-alphabet rank word or transition table is supplied as advice.
-/

namespace Lax842588Proofs.MSORamCompilerSomewhere

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.AutomatonTableEncoding
open Lax842588Proofs.EncodedPrimitiveAtomicAutomata
open Lax842588Proofs.FiniteAutomatonEncoding
open Lax842588Proofs.MarkedAlphabetEncoding
open Lax842588Proofs.MSORamCompilerBinaryWord
open Lax842588Proofs.MSORamCompilerBuild
open Lax842588Proofs.MSORamCompilerHeap
open Lax842588Proofs.MSORamCompilerProgram
open Lax842588Proofs.MSORamCompilerStorage

/-- The base-symbol projection of a well-formed packed marked symbol is a
valid index into the original alphabet. -/
theorem baseSymbol_lt (alphabet : RankedAlphabetCode) (n m symbol : Nat)
    (hsymbol : symbol < symbolCount alphabet n m) :
    baseSymbol n m symbol < alphabet.length := by
  have hn : 0 < 2 ^ n := pow_pos (by omega) _
  have hm : 0 < 2 ^ m := pow_pos (by omega) _
  have hsymbol' : symbol < alphabet.length * 2 ^ n * 2 ^ m := by
    simpa [symbolCount, words_length] using hsymbol
  have hfirst : symbol / 2 ^ m < alphabet.length * 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul hm]
    simpa [Nat.mul_assoc] using hsymbol'
  unfold baseSymbol binaryWordCount
  simp only [words_length]
  rw [Nat.div_lt_iff_lt_mul hn]
  simpa [Nat.mul_assoc] using hfirst

/-- The rank at a packed marked-symbol index is exactly the rank of its base
symbol. -/
theorem markedCode_getD_eq_baseRank (alphabet : RankedAlphabetCode)
    (n m symbol : Nat) (hsymbol : symbol < symbolCount alphabet n m) :
    (code alphabet n m).getD symbol 0 =
      alphabet.getD (baseSymbol n m symbol) 0 := by
  rw [code_eq_numeric]
  simp [numericCode, hsymbol]

/-- Arithmetic bit extraction agrees with the corresponding digit of the
canonical most-significant-first binary word. -/
theorem binaryWord_getD_eq_testBit (length state position : Nat)
    (hstate : state < 2 ^ length) (hposition : position < length) :
    (binaryWord length state).getD position 0 =
      (Nat.testBit state (length - position - 1)).toNat := by
  induction length generalizing state position with
  | zero => omega
  | succ length ih =>
      cases position with
      | zero =>
          have hpow : 0 < 2 ^ length := pow_pos (by omega) _
          have hquot : state / 2 ^ length < 2 := by
            rw [Nat.div_lt_iff_lt_mul hpow]
            simpa [pow_succ, Nat.mul_comm] using hstate
          simp only [binaryWord, List.getD_cons_zero]
          rw [Nat.toNat_testBit]
          change state / 2 ^ length = state / 2 ^ length % 2
          exact (Nat.mod_eq_of_lt hquot).symm
      | succ position =>
          have hposition' : position < length := by omega
          have hpow : 0 < 2 ^ length := pow_pos (by omega) _
          have hstate' : state % 2 ^ length < 2 ^ length :=
            Nat.mod_lt _ hpow
          simp only [binaryWord, List.getD_cons_succ]
          rw [ih (state % 2 ^ length) position hstate' hposition']
          have hindex : length - position - 1 < length := by omega
          have hindexEq : length + 1 - (position + 1) - 1 =
              length - position - 1 := by omega
          rw [hindexEq]
          rw [Nat.testBit_mod_two_pow]
          simp [hindex]

theorem wordDigit_two_eq_testBit (length state position : Nat)
    (hstate : state < 2 ^ length) (hposition : position < length) :
    wordDigit 2 length state position =
      (Nat.testBit state (length - position - 1)).toNat := by
  unfold wordDigit
  rw [wordsTwo_getD_eq_binaryWord length state hstate]
  exact binaryWord_getD_eq_testBit length state position hstate hposition

theorem foWord_lt_two_pow (n m symbol : Nat) :
    foWord n m symbol < 2 ^ n := by
  unfold foWord binaryWordCount
  simp only [words_length]
  exact Nat.mod_lt _ (pow_pos (by omega) _)

theorem soWord_lt_two_pow (m symbol : Nat) :
    symbol % 2 ^ m < 2 ^ m :=
  Nat.mod_lt _ (pow_pos (by omega) _)

theorem foMarked_eq_testBit (n m symbol x : Nat) (hx : x < n) :
    foMarked n m symbol x =
      Nat.testBit (foWord n m symbol) (n - x - 1) := by
  unfold foMarked
  rw [wordDigit_two_eq_testBit n (foWord n m symbol) x
    (foWord_lt_two_pow n m symbol) hx]
  cases Nat.testBit (foWord n m symbol) (n - x - 1) <;> simp

theorem soMarked_eq_testBit (m symbol X : Nat) (hX : X < m) :
    soMarked m symbol X =
      Nat.testBit (symbol % 2 ^ m) (m - X - 1) := by
  unfold soMarked binaryWordCount
  simp only [words_length]
  rw [wordDigit_two_eq_testBit m (symbol % 2 ^ m) X
    (soWord_lt_two_pow m symbol) hX]
  cases Nat.testBit (symbol % 2 ^ m) (m - X - 1) <;> simp

def markerBitValue (length state index : Nat) : Nat :=
  (Nat.testBit state (length - index - 1)).toNat

theorem foMarkerBitValue_eq (n m symbol x : Nat) (hx : x < n) :
    markerBitValue n (foWord n m symbol) x =
      (foMarked n m symbol x).toNat := by
  rw [foMarked_eq_testBit n m symbol x hx]
  rfl

theorem soMarkerBitValue_eq (m symbol X : Nat) (hX : X < m) :
    markerBitValue m (symbol % 2 ^ m) X =
      (soMarked m symbol X).toNat := by
  rw [soMarked_eq_testBit m symbol X hX]
  rfl

/-- Exact fixed-width transition-heap prefix contributed by the first
`symbol` packed symbols. -/
def binaryAlphabetRowsPrefix (maximumRank : Nat)
    (alphabet : RankedAlphabetCode) (pred : Nat → Bool)
    (symbol : Nat) : List Nat :=
  (List.range symbol).flatMap fun a =>
    binaryRowsPrefix maximumRank a (alphabet.getD a 0) (pred a)
      (2 ^ alphabet.getD a 0)

@[simp] theorem binaryAlphabetRowsPrefix_zero (maximumRank : Nat)
    (alphabet : RankedAlphabetCode) (pred : Nat → Bool) :
    binaryAlphabetRowsPrefix maximumRank alphabet pred 0 = [] := by
  simp [binaryAlphabetRowsPrefix]

theorem binaryAlphabetRowsPrefix_succ (maximumRank : Nat)
    (alphabet : RankedAlphabetCode) (pred : Nat → Bool) (symbol : Nat) :
    binaryAlphabetRowsPrefix maximumRank alphabet pred (symbol + 1) =
      binaryAlphabetRowsPrefix maximumRank alphabet pred symbol ++
        binaryRowsPrefix maximumRank symbol (alphabet.getD symbol 0)
          (pred symbol) (2 ^ alphabet.getD symbol 0) := by
  simp [binaryAlphabetRowsPrefix, List.range_succ]

theorem binaryRowsPrefix_complete (maximumRank symbol length : Nat)
    (predicate : Bool) :
    binaryRowsPrefix maximumRank symbol length predicate (2 ^ length) =
      (List.range (2 ^ length)).flatMap fun state =>
        encodeTransitionFixed maximumRank
          (symbol,
            (predicate || (binaryWord length state).any
              fun child => child = 1).toNat,
            binaryWord length state) := by
  unfold binaryRowsPrefix
  apply List.flatMap_congr
  intro state hstate
  rw [generatedBinaryTransition_eq]
  simpa using hstate

/-- On completing the outer loop, the physical fixed-width prefix is exactly
the transition segment of the pure sparse automaton code. -/
theorem binaryAlphabetRowsPrefix_complete (maximumRank : Nat)
    (alphabet : RankedAlphabetCode) (pred : Nat → Bool) :
    binaryAlphabetRowsPrefix maximumRank alphabet pred alphabet.length =
      transitionWords maximumRank (binarySomewhereCode alphabet pred) := by
  unfold binaryAlphabetRowsPrefix transitionWords binarySomewhereCode
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro symbol _
  exact binaryRowsPrefix_complete maximumRank symbol
    (alphabet.getD symbol 0) (pred symbol)

/-- Number of semantic transition records contributed by the first packed
symbols.  This is a proof-side counter model, not a runtime table. -/
def binaryAlphabetRowCount (alphabet : RankedAlphabetCode)
    (symbol : Nat) : Nat :=
  ((List.range symbol).map fun a => 2 ^ alphabet.getD a 0).sum

@[simp] theorem binaryAlphabetRowCount_zero
    (alphabet : RankedAlphabetCode) :
    binaryAlphabetRowCount alphabet 0 = 0 := by
  simp [binaryAlphabetRowCount]

theorem binaryAlphabetRowCount_succ (alphabet : RankedAlphabetCode)
    (symbol : Nat) :
    binaryAlphabetRowCount alphabet (symbol + 1) =
      binaryAlphabetRowCount alphabet symbol +
        2 ^ alphabet.getD symbol 0 := by
  simp [binaryAlphabetRowCount, List.range_succ]

@[simp] theorem binarySomewhereCode_transition_length
    (alphabet : RankedAlphabetCode) (pred : Nat → Bool) :
    (binarySomewhereCode alphabet pred).2.1.length =
      binaryAlphabetRowCount alphabet alphabet.length := by
  simp [binarySomewhereCode, binaryAlphabetRowCount,
    List.length_flatMap]

/-- Compiling a row of smaller rank is no more expensive than compiling a
maximum-rank row. -/
theorem compileBinarySymbolCost_mono_length {length maximumRank : Nat}
    (hlength : length ≤ maximumRank) :
    compileBinarySymbolCost length maximumRank ≤
      compileBinarySymbolCost maximumRank maximumRank := by
  have hpower : 2 ^ length ≤ 2 ^ maximumRank :=
    Nat.pow_le_pow_right (by omega) hlength
  have hbody : binaryRowsBodyCost length maximumRank ≤
      binaryRowsBodyCost maximumRank maximumRank := by
    unfold binaryRowsBodyCost appendCountedBinaryTransitionRecordCost
      appendBinaryTransitionRecordCost preparePaddedBinaryWordCost
      prepareBinaryWordCost binaryWordLoopCost binaryPaddingLoopCost
    omega
  unfold compileBinarySymbolCost binaryRowsLoopCost
  exact Nat.add_le_add_left
    (Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.add_le_add_right hbody 4) hpower) 4) 20

def BinarySymbolRankReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol : Nat) (sigma : Env) : Prop :=
  sigma.vars "binarySymbol" = symbol ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    sigma.vars "foMarkerWords" = 2 ^ n ∧
    symbol < symbolCount alphabet n m ∧
    symbol < B ∧
    2 ^ m < B ∧ 2 ^ n < B ∧
    alphabet.length + 1 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    AlphabetPrefixEq (sigma.arrs "P") alphabet ∧
    maximumRank alphabet < B

def BinarySymbolRankPrepared (alphabet : RankedAlphabetCode)
    (n m symbol : Nat) (sigma : Env) : Prop :=
  sigma.vars "binaryBaseSymbol" = baseSymbol n m symbol ∧
    sigma.vars "binaryLength" = (code alphabet n m).getD symbol 0 ∧
    sigma.vars "binarySymbol" = symbol

/-- Charged rank preparation for one packed marked symbol.  The compiler
storage frame is exported explicitly for composition with the append-only
heap invariants. -/
theorem prepareBinarySymbolRank_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m symbol : Nat) :
    Spec B (BinarySymbolRankReady B alphabet n m symbol)
      prepareBinarySymbolRank
      (fun sigma sigma' =>
        BinarySymbolRankPrepared alphabet n m symbol sigma' ∧
          CompilerStorageAgrees sigma sigma')
      20 := by
  refine (show Spec B (BinarySymbolRankReady B alphabet n m symbol)
      prepareBinarySymbolRank
      (fun _ sigma' => BinarySymbolRankPrepared alphabet n m symbol sigma')
      20 by
    intro sigma hready
    rcases hready with ⟨hsymbol, hso, hfo, hsymbolCount, hsymbolB,
      hsoB, hfoB, hPspace, hPlengthB, hprefix, hmaximumRankB⟩
    have hbase := baseSymbol_lt alphabet n m symbol hsymbolCount
    have hbaseB : baseSymbol n m symbol < B := by omega
    have hindex : baseSymbol n m symbol + 1 <
        (sigma.arrs "P").length := by
      omega
    have hrankEq := hprefix (baseSymbol n m symbol) hbase
    have hrankLe : alphabet.getD (baseSymbol n m symbol) 0 ≤
        maximumRank alphabet :=
      maximumRank_ge alphabet _ hbase
    have hrankB : alphabet.getD (baseSymbol n m symbol) 0 < B := by
      omega
    have hcodeRank :=
      markedCode_getD_eq_baseRank alphabet n m symbol hsymbolCount
    have hlookup : (sigma.arrs "P")[baseSymbol n m symbol + 1]? =
        some (alphabet.getD (baseSymbol n m symbol) 0) := by
      rw [List.getElem?_eq_getElem hindex]
      rw [← List.getD_eq_getElem (sigma.arrs "P") 0 hindex]
      exact congrArg some hrankEq
    have hdivOne : symbol / 2 ^ m < B :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hsymbolB
    unfold prepareBinarySymbolRank
      Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg
    all_goals simp_all [BinarySymbolRankPrepared, baseSymbol,
      binaryWordCount, words_length]
    all_goals omega) |>.frame.post ?_
  intro sigma sigma' _ hpost
  rcases hpost with ⟨hprepared, hvars, harrs, _, _⟩
  refine ⟨hprepared, ?_⟩
  exact ⟨hvars _ (by decide), hvars _ (by decide),
    hvars _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide), harrs _ (by decide)⟩

def FOMarkerStateReady (B n m symbol : Nat) (sigma : Env) : Prop :=
  sigma.vars "binarySymbol" = symbol ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    sigma.vars "foMarkerWords" = 2 ^ n ∧
    symbol < B ∧ 2 ^ m < B ∧ 2 ^ n < B ∧ 1 < B

theorem prepareFOMarkerState_spec (B n m symbol : Nat) :
    Spec B (FOMarkerStateReady B n m symbol) prepareFOMarkerState
      (fun _ sigma' => sigma'.vars "foMarkerState" = foWord n m symbol)
      20 := by
  intro sigma hready
  rcases hready with ⟨hsymbol, hso, hfo, hsymbolB, hsoB, hfoB, honeB⟩
  have hquotB : symbol / 2 ^ m < B :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hsymbolB
  have hmaskB : 2 ^ n - 1 < B :=
    lt_of_le_of_lt (Nat.sub_le _ _) hfoB
  have hresultB : symbol / 2 ^ m % 2 ^ n < B :=
    lt_trans (Nat.mod_lt _ (pow_pos (by omega) _)) hfoB
  unfold prepareFOMarkerState
  run_vcg
  all_goals simp_all [foWord, binaryWordCount, words_length,
    Nat.and_two_pow_sub_one_eq_mod]

def SOMarkerStateReady (B m symbol : Nat) (sigma : Env) : Prop :=
  sigma.vars "binarySymbol" = symbol ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    symbol < B ∧ 2 ^ m < B ∧ 1 < B

theorem prepareSOMarkerState_spec (B m symbol : Nat) :
    Spec B (SOMarkerStateReady B m symbol) prepareSOMarkerState
      (fun _ sigma' => sigma'.vars "soMarkerState" = symbol % 2 ^ m)
      20 := by
  intro sigma hready
  rcases hready with ⟨hsymbol, hso, hsymbolB, hsoB, honeB⟩
  have hmaskB : 2 ^ m - 1 < B :=
    lt_of_le_of_lt (Nat.sub_le _ _) hsoB
  have hresultB : symbol % 2 ^ m < B :=
    lt_trans (Nat.mod_lt _ (pow_pos (by omega) _)) hsoB
  unfold prepareSOMarkerState
  run_vcg
  all_goals simp_all [Nat.and_two_pow_sub_one_eq_mod]

def MarkerBitReady (B length state index : Nat) (source : String)
    (sigma : Env) : Prop :=
  sigma.vars source = state ∧
    sigma.vars "markerLength" = length ∧
    sigma.vars "markerIndex" = index ∧
    index < length ∧ state < 2 ^ length ∧
    state < B ∧ length < B ∧ index < B ∧ 1 < B

theorem prepareFOMarkerBit_spec (B length state index : Nat) :
    Spec B (MarkerBitReady B length state index "foMarkerState")
      prepareFOMarkerBit
      (fun _ sigma' => sigma'.vars "markerBit" =
        markerBitValue length state index)
      20 := by
  intro sigma hready
  rcases hready with ⟨hstate, hlength, hindex, hindexLength,
    hstatePower, hstateB, hlengthB, hindexB, honeB⟩
  have hshiftB : length - index - 1 < B := by omega
  have hquotB : state / 2 ^ (length - index - 1) < B :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hstateB
  have hbitB : markerBitValue length state index < B := by
    unfold markerBitValue
    cases Nat.testBit state (length - index - 1) <;> simp <;> omega
  unfold prepareFOMarkerBit
  run_vcg
  all_goals simp_all [markerBitValue, Nat.and_one_is_mod,
    Nat.toNat_testBit]

theorem prepareSOMarkerBit_spec (B length state index : Nat) :
    Spec B (MarkerBitReady B length state index "soMarkerState")
      prepareSOMarkerBit
      (fun _ sigma' => sigma'.vars "markerBit" =
        markerBitValue length state index)
      20 := by
  intro sigma hready
  rcases hready with ⟨hstate, hlength, hindex, hindexLength,
    hstatePower, hstateB, hlengthB, hindexB, honeB⟩
  have hshiftB : length - index - 1 < B := by omega
  have hquotB : state / 2 ^ (length - index - 1) < B :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hstateB
  have hbitB : markerBitValue length state index < B := by
    unfold markerBitValue
    cases Nat.testBit state (length - index - 1) <;> simp <;> omega
  unfold prepareSOMarkerBit
  run_vcg
  all_goals simp_all [markerBitValue, Nat.and_one_is_mod,
    Nat.toNat_testBit]

theorem land_bool_toNat (left right : Bool) :
    Nat.land left.toNat right.toNat = (left && right).toNat := by
  cases left <;> cases right <;> decide

/-- The portion of `Spec.frame` needed by the shared outer-symbol proof. -/
def PredicatePrepared (command : Com) (predicate : Bool)
    (sigma sigma' : Env) : Prop :=
  sigma'.vars "binaryPredicate" = predicate.toNat ∧
    (∀ y, y ∉ command.wvars → sigma'.vars y = sigma.vars y) ∧
    (∀ a, a ∉ command.warrs → sigma'.arrs a = sigma.arrs a)

def EqualPredicateReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x y : Nat) (sigma : Env) : Prop :=
  BinarySymbolRankPrepared alphabet n m symbol sigma ∧
    sigma.vars "currentFO" = n ∧
    sigma.vars "atomicLeft" = x ∧
    sigma.vars "atomicRight" = y ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    sigma.vars "foMarkerWords" = 2 ^ n ∧
    x < n ∧ y < n ∧ symbol < B ∧
    2 ^ m < B ∧ 2 ^ n < B ∧ n < B ∧
    x < B ∧ y < B ∧ 1 < B

/-- Charged equality-atom predicate computation.  Both marker bits are
extracted directly from the packed symbol; the machine receives no bit
vector. -/
theorem prepareEqualPredicate_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m symbol x y : Nat) :
    Spec B (EqualPredicateReady B alphabet n m symbol x y)
      prepareEqualPredicate
      (PredicatePrepared prepareEqualPredicate
        (foMarked n m symbol x && foMarked n m symbol y))
      100 := by
  refine (show Spec B (EqualPredicateReady B alphabet n m symbol x y)
      prepareEqualPredicate
      (fun _ sigma' => sigma'.vars "binaryPredicate" =
        (foMarked n m symbol x && foMarked n m symbol y).toNat)
      100 by
    intro sigma hready
    rcases hready with ⟨hrank, hn, hx, hy, hso, hfo, hxn, hyn,
      hsymbolB, hsoB, hfoB, hnB, hxB, hyB, honeB⟩
    have hsymbol : sigma.vars "binarySymbol" = symbol := hrank.2.2
    have hfoState :
        Nat.land (symbol / 2 ^ m) (2 ^ n - 1) = foWord n m symbol := by
      simp [foWord, binaryWordCount, words_length,
        Nat.and_two_pow_sub_one_eq_mod]
    have hfoStateB : foWord n m symbol < B :=
      lt_trans (foWord_lt_two_pow n m symbol) hfoB
    have hsymbolQuotB : symbol / 2 ^ m < B :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hsymbolB
    have hxShiftB : n - x - 1 < B := by omega
    have hyShiftB : n - y - 1 < B := by omega
    have hxQuotB : foWord n m symbol / 2 ^ (n - x - 1) < B :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hfoStateB
    have hyQuotB : foWord n m symbol / 2 ^ (n - y - 1) < B :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hfoStateB
    have hxBit :
        Nat.land (foWord n m symbol / 2 ^ (n - x - 1)) 1 =
          (foMarked n m symbol x).toNat := by
      calc
        _ = foWord n m symbol / 2 ^ (n - x - 1) % 2 :=
          Nat.and_one_is_mod _
        _ = (Nat.testBit (foWord n m symbol) (n - x - 1)).toNat :=
          (Nat.toNat_testBit _ _).symm
        _ = _ := congrArg Bool.toNat
          (foMarked_eq_testBit n m symbol x hxn).symm
    have hyBit :
        Nat.land (foWord n m symbol / 2 ^ (n - y - 1)) 1 =
          (foMarked n m symbol y).toNat := by
      calc
        _ = foWord n m symbol / 2 ^ (n - y - 1) % 2 :=
          Nat.and_one_is_mod _
        _ = (Nat.testBit (foWord n m symbol) (n - y - 1)).toNat :=
          (Nat.toNat_testBit _ _).symm
        _ = _ := congrArg Bool.toNat
          (foMarked_eq_testBit n m symbol y hyn).symm
    have hxBitB : (foMarked n m symbol x).toNat < B := by
      cases foMarked n m symbol x <;> simp <;> omega
    have hyBitB : (foMarked n m symbol y).toNat < B := by
      cases foMarked n m symbol y <;> simp <;> omega
    have hpredicateB :
        (foMarked n m symbol x && foMarked n m symbol y).toNat < B := by
      cases foMarked n m symbol x <;>
        cases foMarked n m symbol y <;> simp <;> omega
    have hpredicateLand : Nat.land
        (foMarked n m symbol x).toNat
        (foMarked n m symbol y).toNat =
          (foMarked n m symbol x && foMarked n m symbol y).toNat :=
      land_bool_toNat _ _
    unfold prepareEqualPredicate prepareFOMarkerState prepareFOMarkerBit
      Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg
    all_goals simp_all) |>.frame.post ?_
  intro sigma sigma' _ hpost
  exact ⟨hpost.1, hpost.2.1, hpost.2.2.1⟩

def LabelPredicateReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x label : Nat) (sigma : Env) : Prop :=
  BinarySymbolRankPrepared alphabet n m symbol sigma ∧
    sigma.vars "currentFO" = n ∧
    sigma.vars "atomicLeft" = x ∧
    sigma.vars "atomicLabel" = label ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    sigma.vars "foMarkerWords" = 2 ^ n ∧
    x < n ∧ symbol < B ∧ 2 ^ m < B ∧ 2 ^ n < B ∧
    n < B ∧ x < B ∧ label < B ∧
    baseSymbol n m symbol < B ∧ 1 < B

/-- Charged label-atom predicate computation. -/
theorem prepareLabelPredicate_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m symbol x label : Nat) :
    Spec B (LabelPredicateReady B alphabet n m symbol x label)
      prepareLabelPredicate
      (PredicatePrepared prepareLabelPredicate
        (decide (baseSymbol n m symbol = label) && foMarked n m symbol x))
      100 := by
  refine (show Spec B (LabelPredicateReady B alphabet n m symbol x label)
      prepareLabelPredicate
      (fun _ sigma' => sigma'.vars "binaryPredicate" =
        (decide (baseSymbol n m symbol = label) &&
          foMarked n m symbol x).toNat)
      100 by
    intro sigma hready
    rcases hready with ⟨hrank, hn, hx, hlabel, hso, hfo, hxn,
      hsymbolB, hsoB, hfoB, hnB, hxB, hlabelB, hbaseB, honeB⟩
    have hsymbol : sigma.vars "binarySymbol" = symbol := hrank.2.2
    have hbase : sigma.vars "binaryBaseSymbol" = baseSymbol n m symbol :=
      hrank.1
    have hfoState :
        Nat.land (symbol / 2 ^ m) (2 ^ n - 1) = foWord n m symbol := by
      simp [foWord, binaryWordCount, words_length,
        Nat.and_two_pow_sub_one_eq_mod]
    have hfoStateB : foWord n m symbol < B :=
      lt_trans (foWord_lt_two_pow n m symbol) hfoB
    have hsymbolQuotB : symbol / 2 ^ m < B :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hsymbolB
    have hxShiftB : n - x - 1 < B := by omega
    have hxQuotB : foWord n m symbol / 2 ^ (n - x - 1) < B :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hfoStateB
    have hxBit :
        Nat.land (foWord n m symbol / 2 ^ (n - x - 1)) 1 =
          (foMarked n m symbol x).toNat := by
      calc
        _ = foWord n m symbol / 2 ^ (n - x - 1) % 2 :=
          Nat.and_one_is_mod _
        _ = (Nat.testBit (foWord n m symbol) (n - x - 1)).toNat :=
          (Nat.toNat_testBit _ _).symm
        _ = _ := congrArg Bool.toNat
          (foMarked_eq_testBit n m symbol x hxn).symm
    have hxBitB : (foMarked n m symbol x).toNat < B := by
      cases foMarked n m symbol x <;> simp <;> omega
    by_cases hmatches : baseSymbol n m symbol = label
    · unfold prepareLabelPredicate prepareFOMarkerState prepareFOMarkerBit
        Lax842588Proofs.AutomatonRamProgram.seqs
      run_vcg
      all_goals simp_all
    · unfold prepareLabelPredicate prepareFOMarkerState prepareFOMarkerBit
        Lax842588Proofs.AutomatonRamProgram.seqs
      run_vcg
      all_goals simp_all) |>.frame.post ?_
  intro sigma sigma' _ hpost
  exact ⟨hpost.1, hpost.2.1, hpost.2.2.1⟩

def MembershipPredicateReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x X : Nat) (sigma : Env) : Prop :=
  BinarySymbolRankPrepared alphabet n m symbol sigma ∧
    sigma.vars "currentFO" = n ∧ sigma.vars "currentSO" = m ∧
    sigma.vars "atomicLeft" = x ∧ sigma.vars "atomicSet" = X ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    sigma.vars "foMarkerWords" = 2 ^ n ∧
    x < n ∧ X < m ∧ symbol < B ∧
    2 ^ m < B ∧ 2 ^ n < B ∧ n < B ∧ m < B ∧
    x < B ∧ X < B ∧ 1 < B

/-- Charged membership-atom predicate computation. -/
theorem prepareMembershipPredicate_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m symbol x X : Nat) :
    Spec B (MembershipPredicateReady B alphabet n m symbol x X)
      prepareMembershipPredicate
      (PredicatePrepared prepareMembershipPredicate
        (foMarked n m symbol x && soMarked m symbol X))
      150 := by
  refine (show Spec B (MembershipPredicateReady B alphabet n m symbol x X)
      prepareMembershipPredicate
      (fun _ sigma' => sigma'.vars "binaryPredicate" =
        (foMarked n m symbol x && soMarked m symbol X).toNat)
      150 by
    intro sigma hready
    rcases hready with ⟨hrank, hn, hm, hx, hX, hso, hfo, hxn, hXm,
      hsymbolB, hsoB, hfoB, hnB, hmB, hxB, hXB, honeB⟩
    have hsymbol : sigma.vars "binarySymbol" = symbol := hrank.2.2
    have hfoState :
        Nat.land (symbol / 2 ^ m) (2 ^ n - 1) = foWord n m symbol := by
      simp [foWord, binaryWordCount, words_length,
        Nat.and_two_pow_sub_one_eq_mod]
    have hsoState : Nat.land symbol (2 ^ m - 1) = symbol % 2 ^ m := by
      simp [Nat.and_two_pow_sub_one_eq_mod]
    have hfoStateB : foWord n m symbol < B :=
      lt_trans (foWord_lt_two_pow n m symbol) hfoB
    have hsoStateB : symbol % 2 ^ m < B :=
      lt_trans (soWord_lt_two_pow m symbol) hsoB
    have hsymbolQuotB : symbol / 2 ^ m < B :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hsymbolB
    have hxShiftB : n - x - 1 < B := by omega
    have hXShiftB : m - X - 1 < B := by omega
    have hxQuotB : foWord n m symbol / 2 ^ (n - x - 1) < B :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hfoStateB
    have hXQuotB : (symbol % 2 ^ m) / 2 ^ (m - X - 1) < B :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hsoStateB
    have hxBit : Nat.land
        (foWord n m symbol / 2 ^ (n - x - 1)) 1 =
          (foMarked n m symbol x).toNat := by
      calc
        _ = foWord n m symbol / 2 ^ (n - x - 1) % 2 :=
          Nat.and_one_is_mod _
        _ = (Nat.testBit (foWord n m symbol) (n - x - 1)).toNat :=
          (Nat.toNat_testBit _ _).symm
        _ = _ := congrArg Bool.toNat
          (foMarked_eq_testBit n m symbol x hxn).symm
    have hXBit : Nat.land
        ((symbol % 2 ^ m) / 2 ^ (m - X - 1)) 1 =
          (soMarked m symbol X).toNat := by
      calc
        _ = (symbol % 2 ^ m) / 2 ^ (m - X - 1) % 2 :=
          Nat.and_one_is_mod _
        _ = (Nat.testBit (symbol % 2 ^ m) (m - X - 1)).toNat :=
          (Nat.toNat_testBit _ _).symm
        _ = _ := congrArg Bool.toNat
          (soMarked_eq_testBit m symbol X hXm).symm
    have hxBitB : (foMarked n m symbol x).toNat < B := by
      cases foMarked n m symbol x <;> simp <;> omega
    have hXBitB : (soMarked m symbol X).toNat < B := by
      cases soMarked m symbol X <;> simp <;> omega
    have hpredicateB :
        (foMarked n m symbol x && soMarked m symbol X).toNat < B := by
      cases foMarked n m symbol x <;>
        cases soMarked m symbol X <;> simp <;> omega
    have hpredicateLand : Nat.land (foMarked n m symbol x).toNat
        (soMarked m symbol X).toNat =
          (foMarked n m symbol x && soMarked m symbol X).toNat :=
      land_bool_toNat _ _
    unfold prepareMembershipPredicate prepareFOMarkerState
      prepareSOMarkerState prepareFOMarkerBit prepareSOMarkerBit
      Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg
    all_goals simp_all) |>.frame.post ?_
  intro sigma sigma' _ hpost
  exact ⟨hpost.1, hpost.2.1, hpost.2.2.1⟩

theorem predicatePrepared_storageAgrees {command : Com} {predicate : Bool}
    {sigma sigma' : Env}
    (h : PredicatePrepared command predicate sigma sigma')
    (hdepth : "automatonDepth" ∉ command.wvars)
    (htransitionCursor : "compiledTransitionWords" ∉ command.wvars)
    (hacceptingCursor : "compiledAcceptingWords" ∉ command.wvars)
    (htransitionHeap : "CompiledTransitions" ∉ command.warrs)
    (hacceptingHeap : "CompiledAccepting" ∉ command.warrs)
    (hstates : "AutomatonStatesStack" ∉ command.warrs)
    (htransitionBase : "AutomatonTransitionBaseStack" ∉ command.warrs)
    (htransitionCount : "AutomatonTransitionCountStack" ∉ command.warrs)
    (hacceptingBase : "AutomatonAcceptingBaseStack" ∉ command.warrs)
    (hacceptingCount : "AutomatonAcceptingCountStack" ∉ command.warrs) :
    CompilerStorageAgrees sigma sigma' := by
  exact ⟨h.2.1 _ hdepth, h.2.1 _ htransitionCursor,
    h.2.1 _ hacceptingCursor, h.2.2 _ htransitionHeap,
    h.2.2 _ hacceptingHeap, h.2.2 _ hstates,
    h.2.2 _ htransitionBase, h.2.2 _ htransitionCount,
    h.2.2 _ hacceptingBase, h.2.2 _ hacceptingCount⟩

theorem compilerStorageAgrees_trans {sigma sigma' sigma'' : Env}
    (h₁ : CompilerStorageAgrees sigma sigma')
    (h₂ : CompilerStorageAgrees sigma' sigma'') :
    CompilerStorageAgrees sigma sigma'' := by
  rcases h₁ with ⟨hdepth₁, htransitionCursor₁, hacceptingCursor₁,
    htransitionHeap₁, hacceptingHeap₁, hstates₁, htransitionBase₁,
    htransitionCount₁, hacceptingBase₁, hacceptingCount₁⟩
  rcases h₂ with ⟨hdepth₂, htransitionCursor₂, hacceptingCursor₂,
    htransitionHeap₂, hacceptingHeap₂, hstates₂, htransitionBase₂,
    htransitionCount₂, hacceptingBase₂, hacceptingCount₂⟩
  exact ⟨hdepth₂.trans hdepth₁,
    htransitionCursor₂.trans htransitionCursor₁,
    hacceptingCursor₂.trans hacceptingCursor₁,
    htransitionHeap₂.trans htransitionHeap₁,
    hacceptingHeap₂.trans hacceptingHeap₁, hstates₂.trans hstates₁,
    htransitionBase₂.trans htransitionBase₁,
    htransitionCount₂.trans htransitionCount₁,
    hacceptingBase₂.trans hacceptingBase₁,
    hacceptingCount₂.trans hacceptingCount₁⟩

def EqualSymbolReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x y count : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  BinarySymbolRankReady B alphabet n m symbol sigma ∧
    CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "currentFO" = n ∧
    sigma.vars "atomicLeft" = x ∧
    sigma.vars "atomicRight" = y ∧
    x < n ∧ y < n ∧ n < B ∧ x < B ∧ y < B ∧
    symbol + 1 < B ∧
    sigma.vars "newTransitionCount" = count ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank alphabet ∧
    sigma.vars "transitionMaximumRank" = maximumRank alphabet ∧
    1 < B ∧
    count + 2 ^ (code alphabet n m).getD symbol 0 < B ∧
    transitionPrefix.length +
        2 ^ (code alphabet n m).getD symbol 0 *
          (maximumRank alphabet + 3) < B ∧
    transitionPrefix.length +
        2 ^ (code alphabet n m).getD symbol 0 *
          (maximumRank alphabet + 3) ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

/-- Rank decoding followed by the equality predicate leaves the compiler
heaps untouched and establishes exactly the precondition of the checked
inner binary-row construction. -/
theorem prepareEqualSymbol_spec (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x y count : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (EqualSymbolReady B alphabet n m symbol x y count stack
        transitionPrefix acceptingPrefix)
      (.seq prepareBinarySymbolRank prepareEqualPredicate)
      (fun _ sigma' => BinaryRowsStartReady B (maximumRank alphabet) stack
        transitionPrefix acceptingPrefix symbol
        ((code alphabet n m).getD symbol 0)
        (foMarked n m symbol x && foMarked n m symbol y) count sigma')
      120 := by
  refine Spec.seq
    (((prepareBinarySymbolRank_spec B alphabet n m symbol).pre
      (fun _ h => h.1)).frame)
    (prepareEqualPredicate_spec B alphabet n m symbol x y)
    ?_ ?_
  · intro sigma sigma' hready hpost
    rcases hready with ⟨hrankReady, hstack, htransition, haccepting,
      hn, hx, hy, hxn, hyn, hnB, hxB, hyB, hnextSymbolB, hcount,
      hchildren, hmaximumRank, honeB, hcountB, hwordsB, hcapacity,
      hheapLengthB⟩
    rcases hpost with ⟨⟨hrankPrepared, hstorage⟩, hvars, harrs, _, _⟩
    rcases hrankReady with ⟨hsymbol, hso, hfo, hsymbolCount, hsymbolB,
      hsoB, hfoB, hPspace, hPlengthB, hprefix, hmaximumRankB⟩
    exact ⟨hrankPrepared, (hvars "currentFO" (by decide)).trans hn,
      (hvars "atomicLeft" (by decide)).trans hx,
      (hvars "atomicRight" (by decide)).trans hy,
      (hvars "soMarkerWords" (by decide)).trans hso,
      (hvars "foMarkerWords" (by decide)).trans hfo,
      hxn, hyn, hsymbolB,
      hsoB, hfoB, hnB, hxB, hyB, honeB⟩
  · intro sigma sigma' sigma'' hready hrankPost hpredicate
    rcases hready with ⟨hrankReady, hstack, htransition, haccepting,
      hn, hx, hy, hxn, hyn, hnB, hxB, hyB, hnextSymbolB, hcount,
      hchildren, hmaximumRank, honeB, hcountB, hwordsB, hcapacity,
      hheapLengthB⟩
    rcases hrankPost with ⟨⟨hrankPrepared, hrankStorage⟩,
      hrankVars, hrankArrs, _, _⟩
    have hpredicateStorage : CompilerStorageAgrees sigma' sigma'' :=
      predicatePrepared_storageAgrees hpredicate
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    have hstorage := compilerStorageAgrees_trans hrankStorage hpredicateStorage
    rcases hrankReady with ⟨hsymbol0, hso0, hfo0, hsymbolCount,
      hsymbolB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
      hmaximumRankB⟩
    have hlengthRank : (code alphabet n m).getD symbol 0 ≤
        maximumRank alphabet := by
      rw [markedCode_getD_eq_baseRank alphabet n m symbol hsymbolCount]
      exact maximumRank_ge alphabet _
        (baseSymbol_lt alphabet n m symbol hsymbolCount)
    have hlimitB : 2 ^ (code alphabet n m).getD symbol 0 < B := by
      omega
    refine ⟨compilerStackRep_of_agrees hstorage hstack,
      transitionHeapRep_of_agrees hstorage htransition,
      acceptingHeapRep_of_agrees hstorage haccepting,
      (hpredicate.2.1 "binarySymbol" (by decide)).trans
        hrankPrepared.2.2,
      (hpredicate.2.1 "binaryLength" (by decide)).trans
        hrankPrepared.2.1,
      hpredicate.1,
      (hpredicate.2.1 "newTransitionCount" (by decide)).trans
        ((hrankVars "newTransitionCount" (by decide)).trans hcount),
      hlimitB, hlengthRank, hmaximumRankB,
      ?_, ?_, hsymbolB, honeB, hcountB, hwordsB, ?_, ?_⟩
    · rw [hpredicate.2.2 "NewTransitionChildren" (by decide),
        hrankArrs "NewTransitionChildren" (by decide)]
      exact hchildren
    · exact (hpredicate.2.1 "transitionMaximumRank" (by decide)).trans
        ((hrankVars "transitionMaximumRank" (by decide)).trans hmaximumRank)
    · rw [hpredicate.2.2 "CompiledTransitions" (by decide),
        hrankArrs "CompiledTransitions" (by decide)]
      exact hcapacity
    · rw [hpredicate.2.2 "CompiledTransitions" (by decide),
        hrankArrs "CompiledTransitions" (by decide)]
      exact hheapLengthB

def LabelSymbolReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x label count : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  BinarySymbolRankReady B alphabet n m symbol sigma ∧
    CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "currentFO" = n ∧ sigma.vars "atomicLeft" = x ∧
    sigma.vars "atomicLabel" = label ∧
    x < n ∧ n < B ∧ x < B ∧ label < B ∧ symbol + 1 < B ∧
    sigma.vars "newTransitionCount" = count ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank alphabet ∧
    sigma.vars "transitionMaximumRank" = maximumRank alphabet ∧
    1 < B ∧
    count + 2 ^ (code alphabet n m).getD symbol 0 < B ∧
    transitionPrefix.length +
        2 ^ (code alphabet n m).getD symbol 0 *
          (maximumRank alphabet + 3) < B ∧
    transitionPrefix.length +
        2 ^ (code alphabet n m).getD symbol 0 *
          (maximumRank alphabet + 3) ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

theorem prepareLabelSymbol_spec (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x label count : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (LabelSymbolReady B alphabet n m symbol x label count stack
        transitionPrefix acceptingPrefix)
      (.seq prepareBinarySymbolRank prepareLabelPredicate)
      (fun _ sigma' => BinaryRowsStartReady B (maximumRank alphabet) stack
        transitionPrefix acceptingPrefix symbol
        ((code alphabet n m).getD symbol 0)
        (decide (baseSymbol n m symbol = label) && foMarked n m symbol x)
        count sigma')
      120 := by
  refine Spec.seq
    (((prepareBinarySymbolRank_spec B alphabet n m symbol).pre
      (fun _ h => h.1)).frame)
    (prepareLabelPredicate_spec B alphabet n m symbol x label) ?_ ?_
  · intro sigma sigma' hready hpost
    rcases hready with ⟨hrankReady, hstack, htransition, haccepting,
      hn, hx, hlabel, hxn, hnB, hxB, hlabelB, hnextSymbolB, hcount,
      hchildren, hmaximumRank, honeB, hcountB, hwordsB, hcapacity,
      hheapLengthB⟩
    rcases hpost with ⟨⟨hrankPrepared, hstorage⟩, hvars, harrs, _, _⟩
    rcases hrankReady with ⟨hsymbol, hso, hfo, hsymbolCount, hsymbolB,
      hsoB, hfoB, hPspace, hPlengthB, hprefix, hmaximumRankB⟩
    have hbaseB : baseSymbol n m symbol < B := by
      have hbase := baseSymbol_lt alphabet n m symbol hsymbolCount
      omega
    exact ⟨hrankPrepared, (hvars "currentFO" (by decide)).trans hn,
      (hvars "atomicLeft" (by decide)).trans hx,
      (hvars "atomicLabel" (by decide)).trans hlabel,
      (hvars "soMarkerWords" (by decide)).trans hso,
      (hvars "foMarkerWords" (by decide)).trans hfo,
      hxn, hsymbolB, hsoB, hfoB, hnB, hxB, hlabelB, hbaseB, honeB⟩
  · intro sigma sigma' sigma'' hready hrankPost hpredicate
    rcases hready with ⟨hrankReady, hstack, htransition, haccepting,
      hn, hx, hlabel, hxn, hnB, hxB, hlabelB, hnextSymbolB, hcount,
      hchildren, hmaximumRank, honeB, hcountB, hwordsB, hcapacity,
      hheapLengthB⟩
    rcases hrankPost with ⟨⟨hrankPrepared, hrankStorage⟩,
      hrankVars, hrankArrs, _, _⟩
    have hpredicateStorage : CompilerStorageAgrees sigma' sigma'' :=
      predicatePrepared_storageAgrees hpredicate
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    have hstorage := compilerStorageAgrees_trans hrankStorage hpredicateStorage
    rcases hrankReady with ⟨hsymbol0, hso0, hfo0, hsymbolCount,
      hsymbolB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
      hmaximumRankB⟩
    have hlengthRank : (code alphabet n m).getD symbol 0 ≤
        maximumRank alphabet := by
      rw [markedCode_getD_eq_baseRank alphabet n m symbol hsymbolCount]
      exact maximumRank_ge alphabet _
        (baseSymbol_lt alphabet n m symbol hsymbolCount)
    have hlimitB : 2 ^ (code alphabet n m).getD symbol 0 < B := by
      omega
    refine ⟨compilerStackRep_of_agrees hstorage hstack,
      transitionHeapRep_of_agrees hstorage htransition,
      acceptingHeapRep_of_agrees hstorage haccepting,
      (hpredicate.2.1 "binarySymbol" (by decide)).trans
        hrankPrepared.2.2,
      (hpredicate.2.1 "binaryLength" (by decide)).trans
        hrankPrepared.2.1,
      hpredicate.1,
      (hpredicate.2.1 "newTransitionCount" (by decide)).trans
        ((hrankVars "newTransitionCount" (by decide)).trans hcount),
      hlimitB, hlengthRank, hmaximumRankB, ?_, ?_, hsymbolB, honeB,
      hcountB, hwordsB, ?_, ?_⟩
    · rw [hpredicate.2.2 "NewTransitionChildren" (by decide),
        hrankArrs "NewTransitionChildren" (by decide)]
      exact hchildren
    · exact (hpredicate.2.1 "transitionMaximumRank" (by decide)).trans
        ((hrankVars "transitionMaximumRank" (by decide)).trans hmaximumRank)
    · rw [hpredicate.2.2 "CompiledTransitions" (by decide),
        hrankArrs "CompiledTransitions" (by decide)]
      exact hcapacity
    · rw [hpredicate.2.2 "CompiledTransitions" (by decide),
        hrankArrs "CompiledTransitions" (by decide)]
      exact hheapLengthB

def MembershipSymbolReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x X count : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  BinarySymbolRankReady B alphabet n m symbol sigma ∧
    CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "currentFO" = n ∧ sigma.vars "currentSO" = m ∧
    sigma.vars "atomicLeft" = x ∧ sigma.vars "atomicSet" = X ∧
    x < n ∧ X < m ∧ n < B ∧ m < B ∧ x < B ∧ X < B ∧
    symbol + 1 < B ∧ sigma.vars "newTransitionCount" = count ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank alphabet ∧
    sigma.vars "transitionMaximumRank" = maximumRank alphabet ∧
    1 < B ∧
    count + 2 ^ (code alphabet n m).getD symbol 0 < B ∧
    transitionPrefix.length +
        2 ^ (code alphabet n m).getD symbol 0 *
          (maximumRank alphabet + 3) < B ∧
    transitionPrefix.length +
        2 ^ (code alphabet n m).getD symbol 0 *
          (maximumRank alphabet + 3) ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

theorem prepareMembershipSymbol_spec (B : Nat)
    (alphabet : RankedAlphabetCode)
    (n m symbol x X count : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (MembershipSymbolReady B alphabet n m symbol x X count stack
        transitionPrefix acceptingPrefix)
      (.seq prepareBinarySymbolRank prepareMembershipPredicate)
      (fun _ sigma' => BinaryRowsStartReady B (maximumRank alphabet) stack
        transitionPrefix acceptingPrefix symbol
        ((code alphabet n m).getD symbol 0)
        (foMarked n m symbol x && soMarked m symbol X) count sigma')
      170 := by
  refine Spec.seq
    (((prepareBinarySymbolRank_spec B alphabet n m symbol).pre
      (fun _ h => h.1)).frame)
    (prepareMembershipPredicate_spec B alphabet n m symbol x X) ?_ ?_
  · intro sigma sigma' hready hpost
    rcases hready with ⟨hrankReady, hstack, htransition, haccepting,
      hn, hm, hx, hX, hxn, hXm, hnB, hmB, hxB, hXB,
      hnextSymbolB, hcount, hchildren, hmaximumRank, honeB,
      hcountB, hwordsB, hcapacity, hheapLengthB⟩
    rcases hpost with ⟨⟨hrankPrepared, hstorage⟩, hvars, harrs, _, _⟩
    rcases hrankReady with ⟨hsymbol, hso, hfo, hsymbolCount, hsymbolB,
      hsoB, hfoB, hPspace, hPlengthB, hprefix, hmaximumRankB⟩
    exact ⟨hrankPrepared, (hvars "currentFO" (by decide)).trans hn,
      (hvars "currentSO" (by decide)).trans hm,
      (hvars "atomicLeft" (by decide)).trans hx,
      (hvars "atomicSet" (by decide)).trans hX,
      (hvars "soMarkerWords" (by decide)).trans hso,
      (hvars "foMarkerWords" (by decide)).trans hfo,
      hxn, hXm, hsymbolB, hsoB, hfoB, hnB, hmB, hxB, hXB, honeB⟩
  · intro sigma sigma' sigma'' hready hrankPost hpredicate
    rcases hready with ⟨hrankReady, hstack, htransition, haccepting,
      hn, hm, hx, hX, hxn, hXm, hnB, hmB, hxB, hXB,
      hnextSymbolB, hcount, hchildren, hmaximumRank, honeB,
      hcountB, hwordsB, hcapacity, hheapLengthB⟩
    rcases hrankPost with ⟨⟨hrankPrepared, hrankStorage⟩,
      hrankVars, hrankArrs, _, _⟩
    have hpredicateStorage : CompilerStorageAgrees sigma' sigma'' :=
      predicatePrepared_storageAgrees hpredicate
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    have hstorage := compilerStorageAgrees_trans hrankStorage hpredicateStorage
    rcases hrankReady with ⟨hsymbol0, hso0, hfo0, hsymbolCount,
      hsymbolB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
      hmaximumRankB⟩
    have hlengthRank : (code alphabet n m).getD symbol 0 ≤
        maximumRank alphabet := by
      rw [markedCode_getD_eq_baseRank alphabet n m symbol hsymbolCount]
      exact maximumRank_ge alphabet _
        (baseSymbol_lt alphabet n m symbol hsymbolCount)
    have hlimitB : 2 ^ (code alphabet n m).getD symbol 0 < B := by
      omega
    refine ⟨compilerStackRep_of_agrees hstorage hstack,
      transitionHeapRep_of_agrees hstorage htransition,
      acceptingHeapRep_of_agrees hstorage haccepting,
      (hpredicate.2.1 "binarySymbol" (by decide)).trans
        hrankPrepared.2.2,
      (hpredicate.2.1 "binaryLength" (by decide)).trans
        hrankPrepared.2.1,
      hpredicate.1,
      (hpredicate.2.1 "newTransitionCount" (by decide)).trans
        ((hrankVars "newTransitionCount" (by decide)).trans hcount),
      hlimitB, hlengthRank, hmaximumRankB, ?_, ?_, hsymbolB, honeB,
      hcountB, hwordsB, ?_, ?_⟩
    · rw [hpredicate.2.2 "NewTransitionChildren" (by decide),
        hrankArrs "NewTransitionChildren" (by decide)]
      exact hchildren
    · exact (hpredicate.2.1 "transitionMaximumRank" (by decide)).trans
        ((hrankVars "transitionMaximumRank" (by decide)).trans hmaximumRank)
    · rw [hpredicate.2.2 "CompiledTransitions" (by decide),
        hrankArrs "CompiledTransitions" (by decide)]
      exact hcapacity
    · rw [hpredicate.2.2 "CompiledTransitions" (by decide),
        hrankArrs "CompiledTransitions" (by decide)]
      exact hheapLengthB

theorem advanceBinarySymbol_spec (B symbol : Nat) :
    Spec B
      (fun sigma => sigma.vars "binarySymbol" = symbol ∧ symbol + 1 < B)
      advanceBinarySymbol
      (fun _ sigma' => sigma'.vars "binarySymbol" = symbol + 1)
      10 := by
  intro sigma hready
  unfold advanceBinarySymbol
  run_vcg
  all_goals simp_all

/-- Intermediate result before the packed-symbol counter is advanced. -/
def SomewhereSymbolCompiled (maximumRank symbol length count : Nat)
    (predicate : Bool) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++ binaryRowsPrefix maximumRank symbol length
        predicate (2 ^ length)) sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "newTransitionCount" = count + 2 ^ length ∧
    sigma.vars "binaryState" = 2 ^ length ∧
    sigma.vars "binarySymbol" = symbol

/-- Semantic result of compiling every child-state row for one packed symbol
and advancing to the next symbol. -/
def SomewhereSymbolDone (maximumRank symbol length count : Nat)
    (predicate : Bool) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++ binaryRowsPrefix maximumRank symbol length
        predicate (2 ^ length)) sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "newTransitionCount" = count + 2 ^ length ∧
    sigma.vars "binaryState" = 2 ^ length ∧
    sigma.vars "binarySymbol" = symbol + 1

/-- All row generation, heap writes, counting, and counter advancement after
an atom-specific predicate fragment have a single shared proof. -/
theorem somewhereSymbolBody_spec (B maximumRank symbol length count : Nat)
    (predicate : Bool) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (preparePredicate : Com) (P : Env → Prop) (prepareCost : Nat)
    (h0 : 0 < B)
    (hprepare : Spec B P
      (.seq prepareBinarySymbolRank preparePredicate)
      (fun _ sigma' => BinaryRowsStartReady B maximumRank stack
        transitionPrefix acceptingPrefix symbol length predicate count sigma')
      prepareCost)
    (hnext : ∀ sigma, P sigma →
      sigma.vars "binarySymbol" = symbol ∧ symbol + 1 < B) :
    Spec B
      P
      (binarySymbolsBody preparePredicate)
      (fun _ sigma' =>
        SomewhereSymbolDone maximumRank symbol length count predicate
          stack transitionPrefix acceptingPrefix sigma')
      (prepareCost + compileBinarySymbolCost length maximumRank + 10) := by
  unfold binarySymbolsBody
  refine Spec.seq
    (show Spec B
        P
        ((Com.seq prepareBinarySymbolRank preparePredicate).seq
          compileBinarySymbol)
        (fun _ sigma' =>
          SomewhereSymbolCompiled maximumRank symbol length count predicate
            stack transitionPrefix acceptingPrefix sigma')
        (prepareCost + compileBinarySymbolCost length maximumRank) by
      refine Spec.seq
        hprepare
        ((compileBinarySymbol_spec B maximumRank stack transitionPrefix
          acceptingPrefix symbol length predicate count h0).frame)
        (fun _ _ _ h => h) ?_
      intro sigma sigma' sigma'' hready hrows hcompiled
      rcases hrows with ⟨_, _, _, hsymbol, -⟩
      rcases hcompiled with ⟨hdone, hvars, harrs, _, _⟩
      exact ⟨hdone.1, hdone.2.1, hdone.2.2.1, hdone.2.2.2.1,
        hdone.2.2.2.2, (hvars "binarySymbol" (by decide)).trans hsymbol⟩)
    ((advanceBinarySymbol_spec B symbol).frame)
    ?_ ?_
  · intro sigma sigma' hready hcompiled
    rcases hcompiled with ⟨_, _, _, _, _, hsymbol⟩
    exact ⟨hsymbol, (hnext sigma hready).2⟩
  · intro sigma sigma' sigma'' hready hcompiled hadvanced
    rcases hcompiled with ⟨hstack, htransition, haccepting, hcount,
      hstate, hsymbol⟩
    rcases hadvanced with ⟨hnext, hvars, harrs, _, _⟩
    have hagrees : CompilerStorageAgrees sigma' sigma'' :=
      ⟨hvars _ (by decide), hvars _ (by decide), hvars _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide)⟩
    exact ⟨compilerStackRep_of_agrees hagrees hstack,
      transitionHeapRep_of_agrees hagrees htransition,
      acceptingHeapRep_of_agrees hagrees haccepting,
      (hvars "newTransitionCount" (by decide)).trans hcount,
      (hvars "binaryState" (by decide)).trans hstate, hnext⟩

/-- Equality instantiates only the predicate-preparation boundary; the rest
of the symbol lifecycle is the shared theorem above. -/
theorem equalitySymbolBody_spec (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x y count : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (h0 : 0 < B) :
    Spec B
      (EqualSymbolReady B alphabet n m symbol x y count stack
        transitionPrefix acceptingPrefix)
      (binarySymbolsBody prepareEqualPredicate)
      (fun _ sigma' =>
        SomewhereSymbolDone (maximumRank alphabet) symbol
          ((code alphabet n m).getD symbol 0) count
          (foMarked n m symbol x && foMarked n m symbol y)
          stack transitionPrefix acceptingPrefix sigma')
      (120 + compileBinarySymbolCost
        ((code alphabet n m).getD symbol 0) (maximumRank alphabet) + 10) := by
  apply somewhereSymbolBody_spec B (maximumRank alphabet) symbol
    ((code alphabet n m).getD symbol 0) count
    (foMarked n m symbol x && foMarked n m symbol y) stack
    transitionPrefix acceptingPrefix prepareEqualPredicate
    (EqualSymbolReady B alphabet n m symbol x y count stack
      transitionPrefix acceptingPrefix) 120 h0
  · exact prepareEqualSymbol_spec B alphabet n m symbol x y count stack
      transitionPrefix acceptingPrefix
  · intro sigma hready
    rcases hready with ⟨hrank, hstack, htransition, haccepting,
      hn, hx, hy, hxn, hyn, hnB, hxB, hyB, hnextSymbolB, -⟩
    exact ⟨hrank.1, hnextSymbolB⟩

theorem labelSymbolBody_spec (B : Nat) (alphabet : RankedAlphabetCode)
    (n m symbol x label count : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (h0 : 0 < B) :
    Spec B
      (LabelSymbolReady B alphabet n m symbol x label count stack
        transitionPrefix acceptingPrefix)
      (binarySymbolsBody prepareLabelPredicate)
      (fun _ sigma' =>
        SomewhereSymbolDone (maximumRank alphabet) symbol
          ((code alphabet n m).getD symbol 0) count
          (decide (baseSymbol n m symbol = label) &&
            foMarked n m symbol x)
          stack transitionPrefix acceptingPrefix sigma')
      (120 + compileBinarySymbolCost
        ((code alphabet n m).getD symbol 0) (maximumRank alphabet) + 10) := by
  apply somewhereSymbolBody_spec B (maximumRank alphabet) symbol
    ((code alphabet n m).getD symbol 0) count
    (decide (baseSymbol n m symbol = label) && foMarked n m symbol x)
    stack transitionPrefix acceptingPrefix prepareLabelPredicate
    (LabelSymbolReady B alphabet n m symbol x label count stack
      transitionPrefix acceptingPrefix) 120 h0
  · exact prepareLabelSymbol_spec B alphabet n m symbol x label count stack
      transitionPrefix acceptingPrefix
  · intro sigma hready
    rcases hready with ⟨hrank, hstack, htransition, haccepting,
      hn, hx, hlabel, hxn, hnB, hxB, hlabelB, hnextSymbolB, -⟩
    exact ⟨hrank.1, hnextSymbolB⟩

theorem membershipSymbolBody_spec (B : Nat)
    (alphabet : RankedAlphabetCode)
    (n m symbol x X count : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (h0 : 0 < B) :
    Spec B
      (MembershipSymbolReady B alphabet n m symbol x X count stack
        transitionPrefix acceptingPrefix)
      (binarySymbolsBody prepareMembershipPredicate)
      (fun _ sigma' =>
        SomewhereSymbolDone (maximumRank alphabet) symbol
          ((code alphabet n m).getD symbol 0) count
          (foMarked n m symbol x && soMarked m symbol X)
          stack transitionPrefix acceptingPrefix sigma')
      (170 + compileBinarySymbolCost
        ((code alphabet n m).getD symbol 0) (maximumRank alphabet) + 10) := by
  apply somewhereSymbolBody_spec B (maximumRank alphabet) symbol
    ((code alphabet n m).getD symbol 0) count
    (foMarked n m symbol x && soMarked m symbol X)
    stack transitionPrefix acceptingPrefix prepareMembershipPredicate
    (MembershipSymbolReady B alphabet n m symbol x X count stack
      transitionPrefix acceptingPrefix) 170 h0
  · exact prepareMembershipSymbol_spec B alphabet n m symbol x X count stack
      transitionPrefix acceptingPrefix
  · intro sigma hready
    rcases hready with ⟨hrank, hstack, htransition, haccepting,
      hn, hm, hx, hX, hxn, hXm, hnB, hmB, hxB, hXB,
      hnextSymbolB, -⟩
    exact ⟨hrank.1, hnextSymbolB⟩

/-- Common outer-loop invariant for every two-state "somewhere" atom.  The
only atom-specific component is `atomContext`; all structural traversal,
heap, count, and capacity facts are shared. -/
def SomewhereSymbolsInv (B : Nat) (alphabet : RankedAlphabetCode)
    (n m initialCount : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (atomContext : Env → Prop)
    (sigma : Env) : Prop :=
  let markedAlphabet := code alphabet n m
  let symbol := sigma.vars "binarySymbol"
  symbol ≤ symbolCount alphabet n m ∧
    sigma.vars "markedSymbols" = symbolCount alphabet n m ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    sigma.vars "foMarkerWords" = 2 ^ n ∧
    symbolCount alphabet n m < B ∧ 2 ^ m < B ∧ 2 ^ n < B ∧
    alphabet.length + 1 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    AlphabetPrefixEq (sigma.arrs "P") alphabet ∧
    maximumRank alphabet < B ∧
    CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++ binaryAlphabetRowsPrefix
        (maximumRank alphabet) markedAlphabet predicate symbol) sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧ atomContext sigma ∧
    sigma.vars "newTransitionCount" =
      initialCount + binaryAlphabetRowCount markedAlphabet symbol ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank alphabet ∧
    sigma.vars "transitionMaximumRank" = maximumRank alphabet ∧ 1 < B ∧
    (∀ a, a < symbolCount alphabet n m →
      initialCount + binaryAlphabetRowCount markedAlphabet a +
        2 ^ markedAlphabet.getD a 0 < B) ∧
    (∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) < B) ∧
    (∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) ≤
          (sigma.arrs "CompiledTransitions").length) ∧
    (sigma.arrs "CompiledTransitions").length < B

def somewhereSymbolBodyCost (prepareCost maximumRank : Nat) : Nat :=
  prepareCost + compileBinarySymbolCost maximumRank maximumRank + 10

/-- Generic outer-loop step.  Callers provide only their predicate-specific
symbol readiness theorem and a syntactic frame proof for their operand
context. -/
theorem somewhereSymbolsBody_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m initialCount : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (preparePredicate : Com)
    (atomContext : Env → Prop)
    (Ready : Nat → Nat → List Nat → Env → Prop) (prepareCost : Nat)
    (hmakeReady : ∀ sigma,
      SomewhereSymbolsInv B alphabet n m initialCount stack
        transitionPrefix acceptingPrefix predicate atomContext sigma →
      sigma.vars "binarySymbol" < symbolCount alphabet n m →
      Ready (sigma.vars "binarySymbol")
        (initialCount + binaryAlphabetRowCount (code alphabet n m)
          (sigma.vars "binarySymbol"))
        (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) (code alphabet n m) predicate
          (sigma.vars "binarySymbol")) sigma)
    (hsymbol : ∀ symbol count priorWords, 0 < B →
      Spec B (Ready symbol count priorWords)
        (binarySymbolsBody preparePredicate)
        (fun _ sigma' => SomewhereSymbolDone (maximumRank alphabet) symbol
          ((code alphabet n m).getD symbol 0) count (predicate symbol)
          stack priorWords acceptingPrefix sigma')
        (prepareCost + compileBinarySymbolCost
          ((code alphabet n m).getD symbol 0) (maximumRank alphabet) + 10))
    (hcontextFrame : ∀ sigma sigma', atomContext sigma →
      (∀ y, y ∉ (binarySymbolsBody preparePredicate).wvars →
        sigma'.vars y = sigma.vars y) →
      (∀ a, a ∉ (binarySymbolsBody preparePredicate).warrs →
        sigma'.arrs a = sigma.arrs a) → atomContext sigma')
    (hmarkedFrame : "markedSymbols" ∉
      (binarySymbolsBody preparePredicate).wvars)
    (hsoFrame : "soMarkerWords" ∉
      (binarySymbolsBody preparePredicate).wvars)
    (hfoFrame : "foMarkerWords" ∉
      (binarySymbolsBody preparePredicate).wvars)
    (hmaximumRankFrame : "transitionMaximumRank" ∉
      (binarySymbolsBody preparePredicate).wvars)
    (hPFrame : "P" ∉ (binarySymbolsBody preparePredicate).warrs) :
    Spec B
      (fun sigma =>
        SomewhereSymbolsInv B alphabet n m initialCount stack
          transitionPrefix acceptingPrefix predicate atomContext sigma ∧
        sigma.vars "binarySymbol" < symbolCount alphabet n m)
      (binarySymbolsBody preparePredicate)
      (fun sigma sigma' =>
        SomewhereSymbolsInv B alphabet n m initialCount stack
          transitionPrefix acceptingPrefix predicate atomContext sigma' ∧
        sigma'.vars "binarySymbol" = sigma.vars "binarySymbol" + 1)
      (somewhereSymbolBodyCost prepareCost (maximumRank alphabet)) := by
  intro sigma hpre
  let symbol := sigma.vars "binarySymbol"
  let markedAlphabet := code alphabet n m
  have hready := hmakeReady sigma hpre.1 hpre.2
  simp only [SomewhereSymbolsInv] at hpre
  rcases hpre.1 with ⟨hsymbolLe, hmarkedSymbols, hso, hfo,
    hsymbolCountB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
    hmaximumRankB, hstack, htransition, haccepting, hatom, hcount,
    hchildren, hmaximumRank, honeB, hcountBounds, hwordBounds,
    hcapacityBounds, hheapLengthB⟩
  have h0 : 0 < B := by omega
  obtain ⟨sigma', run, hframed, harrayLength⟩ :=
    (Lax842588Proofs.spec_arrayLength_eq
      ((hsymbol symbol
        (initialCount + binaryAlphabetRowCount markedAlphabet symbol)
        (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate symbol)
        h0).frame) "CompiledTransitions").run hready
  rcases hframed with ⟨hdone, hvars, harrs, _, _⟩
  have hbase := baseSymbol_lt alphabet n m symbol hpre.2
  have hrankLe : markedAlphabet.getD symbol 0 ≤ maximumRank alphabet := by
    dsimp [markedAlphabet]
    rw [markedCode_getD_eq_baseRank alphabet n m symbol hpre.2]
    exact maximumRank_ge alphabet _ hbase
  have hcost : prepareCost +
        compileBinarySymbolCost (markedAlphabet.getD symbol 0)
          (maximumRank alphabet) + 10 ≤
      somewhereSymbolBodyCost prepareCost (maximumRank alphabet) := by
    unfold somewhereSymbolBodyCost
    have := compileBinarySymbolCost_mono_length hrankLe
    omega
  refine ⟨sigma', run.mono hcost, ?_⟩
  rcases hdone with ⟨hstack', htransition', haccepting', hcount',
    hstate', hsymbol'⟩
  have htransitionFinal : TransitionHeapRep
      (transitionPrefix ++ binaryAlphabetRowsPrefix
        (maximumRank alphabet) markedAlphabet predicate (symbol + 1))
      sigma' := by
    rw [binaryAlphabetRowsPrefix_succ, ← List.append_assoc]
    exact htransition'
  have hcountFinal : sigma'.vars "newTransitionCount" =
      initialCount + binaryAlphabetRowCount markedAlphabet (symbol + 1) := by
    rw [binaryAlphabetRowCount_succ, ← Nat.add_assoc]
    exact hcount'
  have htransitionInvariant : TransitionHeapRep
      (transitionPrefix ++ binaryAlphabetRowsPrefix
        (maximumRank alphabet) (code alphabet n m) predicate
        (sigma'.vars "binarySymbol")) sigma' := by
    simpa [markedAlphabet, hsymbol'] using htransitionFinal
  have hcountInvariant : sigma'.vars "newTransitionCount" =
      initialCount + binaryAlphabetRowCount (code alphabet n m)
        (sigma'.vars "binarySymbol") := by
    simpa [markedAlphabet, hsymbol'] using hcountFinal
  have hP : sigma'.arrs "P" = sigma.arrs "P" :=
    harrs "P" hPFrame
  have hchildrenLength :
      (sigma'.arrs "NewTransitionChildren").length =
        maximumRank alphabet := by
    rw [Lax842588Proofs.Run.arrayLength_eq run "NewTransitionChildren"]
    exact hchildren
  have hcapacityBounds' : ∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) ≤
          (sigma'.arrs "CompiledTransitions").length := by
    intro a ha
    rw [harrayLength]
    exact hcapacityBounds a ha
  have hheapLengthB' :
      (sigma'.arrs "CompiledTransitions").length < B := by
    rw [harrayLength]
    exact hheapLengthB
  refine ⟨?_, hsymbol'⟩
  simp only [SomewhereSymbolsInv]
  refine ⟨by omega,
    (hvars "markedSymbols" hmarkedFrame).trans hmarkedSymbols,
    (hvars "soMarkerWords" hsoFrame).trans hso,
    (hvars "foMarkerWords" hfoFrame).trans hfo,
    hsymbolCountB, hsoB, hfoB, ?_, ?_, ?_, hmaximumRankB,
    hstack', htransitionInvariant, haccepting',
    hcontextFrame sigma sigma' hatom hvars harrs,
    hcountInvariant, hchildrenLength,
    (hvars "transitionMaximumRank" hmaximumRankFrame).trans hmaximumRank,
    honeB, hcountBounds, hwordBounds, hcapacityBounds', hheapLengthB'⟩
  · rw [hP]
    exact hPspace
  · rw [hP]
    exact hPlengthB
  · rw [hP]
    exact hprefix

def somewhereSymbolsLoopCost (alphabet : RankedAlphabetCode) (n m : Nat)
    (prepareCost : Nat) : Nat :=
  (somewhereSymbolBodyCost prepareCost (maximumRank alphabet) + 4) *
      symbolCount alphabet n m + 4

theorem somewhereSymbolsLoop_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m initialCount : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (preparePredicate : Com)
    (atomContext : Env → Prop)
    (Ready : Nat → Nat → List Nat → Env → Prop) (prepareCost : Nat)
    (hmakeReady : ∀ sigma,
      SomewhereSymbolsInv B alphabet n m initialCount stack
        transitionPrefix acceptingPrefix predicate atomContext sigma →
      sigma.vars "binarySymbol" < symbolCount alphabet n m →
      Ready (sigma.vars "binarySymbol")
        (initialCount + binaryAlphabetRowCount (code alphabet n m)
          (sigma.vars "binarySymbol"))
        (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) (code alphabet n m) predicate
          (sigma.vars "binarySymbol")) sigma)
    (hsymbol : ∀ symbol count priorWords, 0 < B →
      Spec B (Ready symbol count priorWords)
        (binarySymbolsBody preparePredicate)
        (fun _ sigma' => SomewhereSymbolDone (maximumRank alphabet) symbol
          ((code alphabet n m).getD symbol 0) count (predicate symbol)
          stack priorWords acceptingPrefix sigma')
        (prepareCost + compileBinarySymbolCost
          ((code alphabet n m).getD symbol 0) (maximumRank alphabet) + 10))
    (hcontextFrame : ∀ sigma sigma', atomContext sigma →
      (∀ y, y ∉ (binarySymbolsBody preparePredicate).wvars →
        sigma'.vars y = sigma.vars y) →
      (∀ a, a ∉ (binarySymbolsBody preparePredicate).warrs →
        sigma'.arrs a = sigma.arrs a) → atomContext sigma')
    (hmarkedFrame : "markedSymbols" ∉
      (binarySymbolsBody preparePredicate).wvars)
    (hsoFrame : "soMarkerWords" ∉
      (binarySymbolsBody preparePredicate).wvars)
    (hfoFrame : "foMarkerWords" ∉
      (binarySymbolsBody preparePredicate).wvars)
    (hmaximumRankFrame : "transitionMaximumRank" ∉
      (binarySymbolsBody preparePredicate).wvars)
    (hPFrame : "P" ∉ (binarySymbolsBody preparePredicate).warrs) :
    Spec B
      (SomewhereSymbolsInv B alphabet n m initialCount stack
        transitionPrefix acceptingPrefix predicate atomContext)
      (binarySymbolsLoop preparePredicate)
      (fun _ sigma' =>
        SomewhereSymbolsInv B alphabet n m initialCount stack
          transitionPrefix acceptingPrefix predicate atomContext sigma' ∧
        sigma'.vars "binarySymbol" = symbolCount alphabet n m)
      (somewhereSymbolsLoopCost alphabet n m prepareCost) := by
  unfold binarySymbolsLoop
  apply Spec.forRange "binarySymbol" "markedSymbols"
    (SomewhereSymbolsInv B alphabet n m initialCount stack
      transitionPrefix acceptingPrefix predicate atomContext)
    (symbolCount alphabet n m)
    (somewhereSymbolBodyCost prepareCost (maximumRank alphabet))
    (somewhereSymbolsLoopCost alphabet n m prepareCost)
  · intro sigma hinv
    simp only [SomewhereSymbolsInv] at hinv
    omega
  · intro sigma hinv
    simp only [SomewhereSymbolsInv] at hinv
    omega
  · intro sigma hinv
    exact hinv.2.1
  · intro sigma hinv
    exact hinv.1
  · exact somewhereSymbolsBody_spec B alphabet n m initialCount stack
      transitionPrefix acceptingPrefix predicate preparePredicate atomContext
      Ready prepareCost hmakeReady hsymbol hcontextFrame hmarkedFrame
      hsoFrame hfoFrame hmaximumRankFrame hPFrame
  · intro _ h
    exact h
  · intro sigma _
    unfold somewhereSymbolsLoopCost
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left
        (somewhereSymbolBodyCost prepareCost (maximumRank alphabet) + 4)
        (Nat.sub_le (symbolCount alphabet n m)
          (sigma.vars "binarySymbol"))) 4

def LabelAtomContext (B n x label : Nat) (sigma : Env) : Prop :=
  sigma.vars "currentFO" = n ∧ sigma.vars "atomicLeft" = x ∧
    sigma.vars "atomicLabel" = label ∧
    x < n ∧ n < B ∧ x < B ∧ label < B

def LabelSymbolsInv (B : Nat) (alphabet : RankedAlphabetCode)
    (n m x label initialCount : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  SomewhereSymbolsInv B alphabet n m initialCount stack transitionPrefix
    acceptingPrefix
    (fun symbol => decide (baseSymbol n m symbol = label) &&
      foMarked n m symbol x)
    (LabelAtomContext B n x label) sigma

private theorem labelSymbolsInv_bodyReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x label initialCount : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env)
    (hinv : LabelSymbolsInv B alphabet n m x label initialCount stack
      transitionPrefix acceptingPrefix sigma)
    (hsymbolLt : sigma.vars "binarySymbol" < symbolCount alphabet n m) :
    LabelSymbolReady B alphabet n m (sigma.vars "binarySymbol") x label
      (initialCount + binaryAlphabetRowCount (code alphabet n m)
        (sigma.vars "binarySymbol")) stack
      (transitionPrefix ++ binaryAlphabetRowsPrefix (maximumRank alphabet)
        (code alphabet n m)
        (fun symbol => decide (baseSymbol n m symbol = label) &&
          foMarked n m symbol x)
        (sigma.vars "binarySymbol")) acceptingPrefix sigma := by
  simp only [LabelSymbolsInv, SomewhereSymbolsInv] at hinv
  rcases hinv with ⟨hsymbolLe, hmarkedSymbols, hso, hfo,
    hsymbolCountB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
    hmaximumRankB, hstack, htransition, haccepting, hatom, hcount,
    hchildren, hmaximumRank, honeB, hcountBounds, hwordBounds,
    hcapacityBounds, hheapLengthB⟩
  rcases hatom with ⟨hn, hx, hlabel, hxn, hnB, hxB, hlabelB⟩
  have hsymbolB : sigma.vars "binarySymbol" < B := by omega
  have hnextSymbolB : sigma.vars "binarySymbol" + 1 < B := by omega
  exact ⟨⟨rfl, hso, hfo, hsymbolLt, hsymbolB, hsoB, hfoB,
      hPspace, hPlengthB, hprefix, hmaximumRankB⟩,
    hstack, htransition, haccepting, hn, hx, hlabel, hxn, hnB,
    hxB, hlabelB, hnextSymbolB, hcount, hchildren, hmaximumRank,
    honeB, hcountBounds _ hsymbolLt, hwordBounds _ hsymbolLt,
    hcapacityBounds _ hsymbolLt, hheapLengthB⟩

private theorem labelAtomContext_frame (B n x label : Nat)
    (sigma sigma' : Env) (h : LabelAtomContext B n x label sigma)
    (hvars : ∀ y, y ∉
      (binarySymbolsBody prepareLabelPredicate).wvars →
        sigma'.vars y = sigma.vars y)
    (_harrs : ∀ a, a ∉
      (binarySymbolsBody prepareLabelPredicate).warrs →
        sigma'.arrs a = sigma.arrs a) :
    LabelAtomContext B n x label sigma' := by
  rcases h with ⟨hn, hx, hlabel, hxn, hnB, hxB, hlabelB⟩
  exact ⟨(hvars "currentFO" (by decide)).trans hn,
    (hvars "atomicLeft" (by decide)).trans hx,
    (hvars "atomicLabel" (by decide)).trans hlabel,
    hxn, hnB, hxB, hlabelB⟩

theorem labelSymbolsLoop_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x label initialCount : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (LabelSymbolsInv B alphabet n m x label initialCount stack
        transitionPrefix acceptingPrefix)
      (binarySymbolsLoop prepareLabelPredicate)
      (fun _ sigma' =>
        LabelSymbolsInv B alphabet n m x label initialCount stack
          transitionPrefix acceptingPrefix sigma' ∧
        sigma'.vars "binarySymbol" = symbolCount alphabet n m)
      (somewhereSymbolsLoopCost alphabet n m 120) := by
  exact somewhereSymbolsLoop_spec B alphabet n m initialCount stack
    transitionPrefix acceptingPrefix
    (fun symbol => decide (baseSymbol n m symbol = label) &&
      foMarked n m symbol x)
    prepareLabelPredicate (LabelAtomContext B n x label)
    (fun symbol count priorWords sigma =>
      LabelSymbolReady B alphabet n m symbol x label count stack
        priorWords acceptingPrefix sigma)
    120
    (labelSymbolsInv_bodyReady B alphabet n m x label initialCount stack
      transitionPrefix acceptingPrefix)
    (fun symbol count priorWords h0 =>
      labelSymbolBody_spec B alphabet n m symbol x label count stack
        priorWords acceptingPrefix h0)
    (labelAtomContext_frame B n x label)
    (by decide) (by decide) (by decide) (by decide) (by decide)

def MembershipAtomContext (B n m x X : Nat) (sigma : Env) : Prop :=
  sigma.vars "currentFO" = n ∧ sigma.vars "currentSO" = m ∧
    sigma.vars "atomicLeft" = x ∧ sigma.vars "atomicSet" = X ∧
    x < n ∧ X < m ∧ n < B ∧ m < B ∧ x < B ∧ X < B

def MembershipSymbolsInv (B : Nat) (alphabet : RankedAlphabetCode)
    (n m x X initialCount : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  SomewhereSymbolsInv B alphabet n m initialCount stack transitionPrefix
    acceptingPrefix
    (fun symbol => foMarked n m symbol x && soMarked m symbol X)
    (MembershipAtomContext B n m x X) sigma

private theorem membershipSymbolsInv_bodyReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x X initialCount : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env)
    (hinv : MembershipSymbolsInv B alphabet n m x X initialCount stack
      transitionPrefix acceptingPrefix sigma)
    (hsymbolLt : sigma.vars "binarySymbol" < symbolCount alphabet n m) :
    MembershipSymbolReady B alphabet n m (sigma.vars "binarySymbol") x X
      (initialCount + binaryAlphabetRowCount (code alphabet n m)
        (sigma.vars "binarySymbol")) stack
      (transitionPrefix ++ binaryAlphabetRowsPrefix (maximumRank alphabet)
        (code alphabet n m)
        (fun symbol => foMarked n m symbol x && soMarked m symbol X)
        (sigma.vars "binarySymbol")) acceptingPrefix sigma := by
  simp only [MembershipSymbolsInv, SomewhereSymbolsInv] at hinv
  rcases hinv with ⟨hsymbolLe, hmarkedSymbols, hso, hfo,
    hsymbolCountB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
    hmaximumRankB, hstack, htransition, haccepting, hatom, hcount,
    hchildren, hmaximumRank, honeB, hcountBounds, hwordBounds,
    hcapacityBounds, hheapLengthB⟩
  rcases hatom with ⟨hn, hm, hx, hX, hxn, hXm, hnB, hmB, hxB, hXB⟩
  have hsymbolB : sigma.vars "binarySymbol" < B := by omega
  have hnextSymbolB : sigma.vars "binarySymbol" + 1 < B := by omega
  exact ⟨⟨rfl, hso, hfo, hsymbolLt, hsymbolB, hsoB, hfoB,
      hPspace, hPlengthB, hprefix, hmaximumRankB⟩,
    hstack, htransition, haccepting, hn, hm, hx, hX, hxn, hXm,
    hnB, hmB, hxB, hXB, hnextSymbolB, hcount, hchildren,
    hmaximumRank, honeB, hcountBounds _ hsymbolLt,
    hwordBounds _ hsymbolLt, hcapacityBounds _ hsymbolLt, hheapLengthB⟩

private theorem membershipAtomContext_frame (B n m x X : Nat)
    (sigma sigma' : Env) (h : MembershipAtomContext B n m x X sigma)
    (hvars : ∀ y, y ∉
      (binarySymbolsBody prepareMembershipPredicate).wvars →
        sigma'.vars y = sigma.vars y)
    (_harrs : ∀ a, a ∉
      (binarySymbolsBody prepareMembershipPredicate).warrs →
        sigma'.arrs a = sigma.arrs a) :
    MembershipAtomContext B n m x X sigma' := by
  rcases h with ⟨hn, hm, hx, hX, hxn, hXm, hnB, hmB, hxB, hXB⟩
  exact ⟨(hvars "currentFO" (by decide)).trans hn,
    (hvars "currentSO" (by decide)).trans hm,
    (hvars "atomicLeft" (by decide)).trans hx,
    (hvars "atomicSet" (by decide)).trans hX,
    hxn, hXm, hnB, hmB, hxB, hXB⟩

theorem membershipSymbolsLoop_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x X initialCount : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (MembershipSymbolsInv B alphabet n m x X initialCount stack
        transitionPrefix acceptingPrefix)
      (binarySymbolsLoop prepareMembershipPredicate)
      (fun _ sigma' =>
        MembershipSymbolsInv B alphabet n m x X initialCount stack
          transitionPrefix acceptingPrefix sigma' ∧
        sigma'.vars "binarySymbol" = symbolCount alphabet n m)
      (somewhereSymbolsLoopCost alphabet n m 170) := by
  exact somewhereSymbolsLoop_spec B alphabet n m initialCount stack
    transitionPrefix acceptingPrefix
    (fun symbol => foMarked n m symbol x && soMarked m symbol X)
    prepareMembershipPredicate (MembershipAtomContext B n m x X)
    (fun symbol count priorWords sigma =>
      MembershipSymbolReady B alphabet n m symbol x X count stack
        priorWords acceptingPrefix sigma)
    170
    (membershipSymbolsInv_bodyReady B alphabet n m x X initialCount stack
      transitionPrefix acceptingPrefix)
    (fun symbol count priorWords h0 =>
      membershipSymbolBody_spec B alphabet n m symbol x X count stack
        priorWords acceptingPrefix h0)
    (membershipAtomContext_frame B n m x X)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Exact invariant for the outer equality-atom alphabet loop.  The quantified
bounds are static capacity obligations; the runtime state carries only the
counter and the append-only heaps. -/
def EqualitySymbolsInv (B : Nat) (alphabet : RankedAlphabetCode)
    (n m x y initialCount : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  let markedAlphabet := code alphabet n m
  let predicate := fun symbol =>
    foMarked n m symbol x && foMarked n m symbol y
  let symbol := sigma.vars "binarySymbol"
  symbol ≤ symbolCount alphabet n m ∧
    sigma.vars "markedSymbols" = symbolCount alphabet n m ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    sigma.vars "foMarkerWords" = 2 ^ n ∧
    symbolCount alphabet n m < B ∧
    2 ^ m < B ∧ 2 ^ n < B ∧
    alphabet.length + 1 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    AlphabetPrefixEq (sigma.arrs "P") alphabet ∧
    maximumRank alphabet < B ∧
    CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++ binaryAlphabetRowsPrefix
        (maximumRank alphabet) markedAlphabet predicate symbol) sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "currentFO" = n ∧
    sigma.vars "atomicLeft" = x ∧
    sigma.vars "atomicRight" = y ∧
    x < n ∧ y < n ∧ n < B ∧ x < B ∧ y < B ∧
    sigma.vars "newTransitionCount" =
      initialCount + binaryAlphabetRowCount markedAlphabet symbol ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank alphabet ∧
    sigma.vars "transitionMaximumRank" = maximumRank alphabet ∧
    1 < B ∧
    (∀ a, a < symbolCount alphabet n m →
      initialCount + binaryAlphabetRowCount markedAlphabet a +
        2 ^ markedAlphabet.getD a 0 < B) ∧
    (∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) < B) ∧
    (∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) ≤
          (sigma.arrs "CompiledTransitions").length) ∧
    (sigma.arrs "CompiledTransitions").length < B

private theorem equalitySymbolsInv_bodyReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y initialCount : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env)
    (hinv : EqualitySymbolsInv B alphabet n m x y initialCount stack
      transitionPrefix acceptingPrefix sigma)
    (hsymbolLt : sigma.vars "binarySymbol" < symbolCount alphabet n m) :
    EqualSymbolReady B alphabet n m (sigma.vars "binarySymbol") x y
      (initialCount + binaryAlphabetRowCount (code alphabet n m)
        (sigma.vars "binarySymbol")) stack
      (transitionPrefix ++ binaryAlphabetRowsPrefix (maximumRank alphabet)
        (code alphabet n m)
        (fun symbol => foMarked n m symbol x && foMarked n m symbol y)
        (sigma.vars "binarySymbol")) acceptingPrefix sigma := by
  simp only [EqualitySymbolsInv] at hinv
  rcases hinv with ⟨hsymbolLe, hmarkedSymbols, hso, hfo,
    hsymbolCountB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
    hmaximumRankB, hstack, htransition, haccepting, hn, hx, hy,
    hxn, hyn, hnB, hxB, hyB, hcount, hchildren, hmaximumRank,
    honeB, hcountBounds, hwordBounds, hcapacityBounds, hheapLengthB⟩
  have hsymbolB : sigma.vars "binarySymbol" < B := by omega
  have hnextSymbolB : sigma.vars "binarySymbol" + 1 < B := by omega
  exact ⟨⟨rfl, hso, hfo, hsymbolLt, hsymbolB, hsoB, hfoB,
      hPspace, hPlengthB, hprefix, hmaximumRankB⟩,
    hstack, htransition, haccepting, hn, hx, hy, hxn, hyn, hnB,
    hxB, hyB, hnextSymbolB, hcount, hchildren, hmaximumRank, honeB,
    hcountBounds _ hsymbolLt, hwordBounds _ hsymbolLt,
    hcapacityBounds _ hsymbolLt, hheapLengthB⟩

def equalitySymbolBodyCost (maximumRank : Nat) : Nat :=
  120 + compileBinarySymbolCost maximumRank maximumRank + 10

/-- The shared outer-loop body specialized to an equality atom preserves the
complete semantic prefix invariant and advances exactly one packed symbol. -/
theorem equalitySymbolsBody_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y initialCount : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (fun sigma =>
        EqualitySymbolsInv B alphabet n m x y initialCount stack
          transitionPrefix acceptingPrefix sigma ∧
        sigma.vars "binarySymbol" < symbolCount alphabet n m)
      (binarySymbolsBody prepareEqualPredicate)
      (fun sigma sigma' =>
        EqualitySymbolsInv B alphabet n m x y initialCount stack
          transitionPrefix acceptingPrefix sigma' ∧
        sigma'.vars "binarySymbol" = sigma.vars "binarySymbol" + 1)
      (equalitySymbolBodyCost (maximumRank alphabet)) := by
  intro sigma hpre
  let symbol := sigma.vars "binarySymbol"
  let markedAlphabet := code alphabet n m
  let predicate := fun a => foMarked n m a x && foMarked n m a y
  have hready := equalitySymbolsInv_bodyReady B alphabet n m x y
    initialCount stack transitionPrefix acceptingPrefix sigma hpre.1 hpre.2
  have h0 : 0 < B := by
    simp only [EqualitySymbolsInv] at hpre
    omega
  obtain ⟨sigma', run, hframed, harrayLength⟩ :=
    (Lax842588Proofs.spec_arrayLength_eq
      ((equalitySymbolBody_spec B alphabet n m symbol x y
        (initialCount + binaryAlphabetRowCount markedAlphabet symbol)
        stack
        (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate symbol)
        acceptingPrefix h0).frame)
      "CompiledTransitions").run hready
  rcases hframed with ⟨hdone, hvars, harrs, _, _⟩
  simp only [EqualitySymbolsInv] at hpre
  rcases hpre.1 with ⟨hsymbolLe, hmarkedSymbols, hso, hfo,
    hsymbolCountB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
    hmaximumRankB, hstack, htransition, haccepting, hn, hx, hy,
    hxn, hyn, hnB, hxB, hyB, hcount, hchildren, hmaximumRank,
    honeB, hcountBounds, hwordBounds, hcapacityBounds, hheapLengthB⟩
  have hbase := baseSymbol_lt alphabet n m symbol hpre.2
  have hrankLe : markedAlphabet.getD symbol 0 ≤ maximumRank alphabet := by
    dsimp [markedAlphabet]
    rw [markedCode_getD_eq_baseRank alphabet n m symbol hpre.2]
    exact maximumRank_ge alphabet _ hbase
  have hcost :
      120 + compileBinarySymbolCost (markedAlphabet.getD symbol 0)
          (maximumRank alphabet) + 10 ≤
        equalitySymbolBodyCost (maximumRank alphabet) := by
    unfold equalitySymbolBodyCost
    have := compileBinarySymbolCost_mono_length hrankLe
    omega
  refine ⟨sigma', run.mono hcost, ?_⟩
  rcases hdone with ⟨hstack', htransition', haccepting', hcount',
    hstate', hsymbol'⟩
  have htransitionFinal : TransitionHeapRep
      (transitionPrefix ++ binaryAlphabetRowsPrefix
        (maximumRank alphabet) markedAlphabet predicate (symbol + 1))
      sigma' := by
    rw [binaryAlphabetRowsPrefix_succ, ← List.append_assoc]
    exact htransition'
  have hcountFinal : sigma'.vars "newTransitionCount" =
      initialCount + binaryAlphabetRowCount markedAlphabet (symbol + 1) := by
    rw [binaryAlphabetRowCount_succ, ← Nat.add_assoc]
    exact hcount'
  have htransitionInvariant : TransitionHeapRep
      (transitionPrefix ++ binaryAlphabetRowsPrefix
        (maximumRank alphabet) (code alphabet n m)
        (fun a => foMarked n m a x && foMarked n m a y)
        (sigma'.vars "binarySymbol")) sigma' := by
    simpa [markedAlphabet, predicate, hsymbol'] using htransitionFinal
  have hcountInvariant : sigma'.vars "newTransitionCount" =
      initialCount + binaryAlphabetRowCount (code alphabet n m)
        (sigma'.vars "binarySymbol") := by
    simpa [markedAlphabet, hsymbol'] using hcountFinal
  have hP : sigma'.arrs "P" = sigma.arrs "P" :=
    harrs "P" (by decide)
  have hchildrenLength :
      (sigma'.arrs "NewTransitionChildren").length =
        maximumRank alphabet := by
    rw [Lax842588Proofs.Run.arrayLength_eq run "NewTransitionChildren"]
    exact hchildren
  have hcapacityBounds' : ∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) ≤
          (sigma'.arrs "CompiledTransitions").length := by
    intro a ha
    rw [harrayLength]
    exact hcapacityBounds a ha
  have hheapLengthB' :
      (sigma'.arrs "CompiledTransitions").length < B := by
    rw [harrayLength]
    exact hheapLengthB
  refine ⟨?_, hsymbol'⟩
  simp only [EqualitySymbolsInv]
  refine ⟨by omega,
    (hvars "markedSymbols" (by decide)).trans hmarkedSymbols,
    (hvars "soMarkerWords" (by decide)).trans hso,
    (hvars "foMarkerWords" (by decide)).trans hfo,
    hsymbolCountB, hsoB, hfoB, ?_, ?_, ?_, hmaximumRankB,
    hstack', htransitionInvariant, haccepting',
    (hvars "currentFO" (by decide)).trans hn,
    (hvars "atomicLeft" (by decide)).trans hx,
    (hvars "atomicRight" (by decide)).trans hy,
    hxn, hyn, hnB, hxB, hyB, hcountInvariant, hchildrenLength,
    (hvars "transitionMaximumRank" (by decide)).trans hmaximumRank,
    honeB, hcountBounds, hwordBounds, hcapacityBounds', hheapLengthB'⟩
  · rw [hP]
    exact hPspace
  · rw [hP]
    exact hPlengthB
  · rw [hP]
    exact hprefix

def equalitySymbolsLoopCost (alphabet : RankedAlphabetCode) (n m : Nat) : Nat :=
  (equalitySymbolBodyCost (maximumRank alphabet) + 4) *
      symbolCount alphabet n m + 4

/-- Complete counted traversal of the structurally defined marked alphabet
for an equality atom. -/
theorem equalitySymbolsLoop_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y initialCount : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (EqualitySymbolsInv B alphabet n m x y initialCount stack
        transitionPrefix acceptingPrefix)
      (binarySymbolsLoop prepareEqualPredicate)
      (fun _ sigma' =>
        EqualitySymbolsInv B alphabet n m x y initialCount stack
          transitionPrefix acceptingPrefix sigma' ∧
        sigma'.vars "binarySymbol" = symbolCount alphabet n m)
      (equalitySymbolsLoopCost alphabet n m) := by
  unfold binarySymbolsLoop
  apply Spec.forRange "binarySymbol" "markedSymbols"
    (EqualitySymbolsInv B alphabet n m x y initialCount stack
      transitionPrefix acceptingPrefix)
    (symbolCount alphabet n m)
    (equalitySymbolBodyCost (maximumRank alphabet))
    (equalitySymbolsLoopCost alphabet n m)
  · intro sigma hinv
    simp only [EqualitySymbolsInv] at hinv
    omega
  · intro sigma hinv
    simp only [EqualitySymbolsInv] at hinv
    omega
  · intro sigma hinv
    exact hinv.2.1
  · intro sigma hinv
    exact hinv.1
  · exact equalitySymbolsBody_spec B alphabet n m x y initialCount stack
      transitionPrefix acceptingPrefix
  · intro _ h
    exact h
  · intro sigma _
    unfold equalitySymbolsLoopCost
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left
        (equalitySymbolBodyCost (maximumRank alphabet) + 4)
        (Nat.sub_le (symbolCount alphabet n m)
          (sigma.vars "binarySymbol"))) 4

/-- Static and storage obligations needed to open the equality automaton.
They are intentionally proof-private; the eventual RAM theorem discharges
them from its single word-width/workspace hypothesis. -/
def EqualityAutomatonStartReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  let markedAlphabet := code alphabet n m
  let predicate := fun symbol =>
    foMarked n m symbol x && foMarked n m symbol y
  CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "markedSymbols" = symbolCount alphabet n m ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    sigma.vars "foMarkerWords" = 2 ^ n ∧
    symbolCount alphabet n m < B ∧
    2 ^ m < B ∧ 2 ^ n < B ∧
    alphabet.length + 1 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    AlphabetPrefixEq (sigma.arrs "P") alphabet ∧
    maximumRank alphabet < B ∧
    sigma.vars "currentFO" = n ∧
    sigma.vars "atomicLeft" = x ∧
    sigma.vars "atomicRight" = y ∧
    x < n ∧ y < n ∧ n < B ∧ x < B ∧ y < B ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank alphabet ∧
    sigma.vars "transitionMaximumRank" = maximumRank alphabet ∧
    2 < B ∧ transitionPrefix.length < B ∧ acceptingPrefix.length < B ∧
    (∀ a, a < symbolCount alphabet n m →
      binaryAlphabetRowCount markedAlphabet a +
        2 ^ markedAlphabet.getD a 0 < B) ∧
    (∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) < B) ∧
    (∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) ≤
          (sigma.arrs "CompiledTransitions").length) ∧
    (sigma.arrs "CompiledTransitions").length < B

private theorem prepareTwoStates_spec (B : Nat) :
    Spec B (fun _ => 2 < B) (.assign "newStates" (.lit 2))
      (fun _ sigma' => sigma'.vars "newStates" = 2) 10 := by
  intro sigma htwoB
  run_vcg
  all_goals simp_all

private theorem beginBinarySymbolZero_spec (B : Nat) :
    Spec B (fun _ => 0 < B) (.assign "binarySymbol" (.lit 0))
      (fun _ sigma' => sigma'.vars "binarySymbol" = 0) 10 := by
  intro sigma hzeroB
  run_vcg
  all_goals simp_all

/-- A freshly opened two-state segment together with the equality-loop
invariant. -/
def EqualityAutomatonRowsReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m x y : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  EqualitySymbolsInv B alphabet n m x y 0 stack transitionPrefix
      acceptingPrefix sigma ∧
    sigma.vars "newStates" = 2 ∧
    sigma.vars "newTransitionBase" = transitionPrefix.length ∧
    sigma.vars "newAcceptingBase" = acceptingPrefix.length ∧
    sigma.vars "newAcceptingCount" = 0 ∧
    2 < B

/-- Charged initialization of a fresh equality-automaton segment. -/
theorem beginEqualityAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (EqualityAutomatonStartReady B alphabet n m x y stack
        transitionPrefix acceptingPrefix)
      beginBinarySomewhere
      (fun _ sigma' => EqualityAutomatonRowsReady B alphabet n m x y stack
        transitionPrefix acceptingPrefix sigma')
      70 := by
  intro sigma hready
  simp only [EqualityAutomatonStartReady] at hready
  rcases hready with ⟨hstack, htransition, haccepting, hmarkedSymbols,
    hso, hfo, hsymbolCountB, hsoB, hfoB, hPspace, hPlengthB,
    hprefix, hmaximumRankB, hn, hx, hy, hxn, hyn, hnB, hxB, hyB,
    hchildren, hmaximumRank, htwoB, htransitionPrefixB,
    hacceptingPrefixB, hcountBounds, hwordBounds, hcapacityBounds,
    hheapLengthB⟩
  obtain ⟨sigma₁, run₁, hstates, hvars₁, harrs₁, _, _⟩ :=
    (prepareTwoStates_spec B).frame.run (σ := sigma) htwoB
  have hagrees₁ : CompilerStorageAgrees sigma sigma₁ :=
    ⟨hvars₁ _ (by decide), hvars₁ _ (by decide), hvars₁ _ (by decide),
      harrs₁ _ (by decide), harrs₁ _ (by decide), harrs₁ _ (by decide),
      harrs₁ _ (by decide), harrs₁ _ (by decide), harrs₁ _ (by decide),
      harrs₁ _ (by decide)⟩
  have hbeginReady : AutomatonBuildStartReady B (maximumRank alphabet)
      stack transitionPrefix acceptingPrefix 2 sigma₁ := by
    refine ⟨compilerStackRep_of_agrees hagrees₁ hstack,
      transitionHeapRep_of_agrees hagrees₁ htransition,
      acceptingHeapRep_of_agrees hagrees₁ haccepting, hstates, htwoB,
      htransitionPrefixB, hacceptingPrefixB, by omega⟩
  obtain ⟨sigma₂, run₂, hstarted, hvars₂, harrs₂, _, _⟩ :=
    (beginCompiledAutomaton_spec B (maximumRank alphabet) stack
      transitionPrefix acceptingPrefix 2).frame.run hbeginReady
  obtain ⟨sigma₃, run₃, hzero, hvars₃, harrs₃, _, _⟩ :=
    (beginBinarySymbolZero_spec B).frame.run (σ := sigma₂) (by omega)
  refine ⟨sigma₃, Run.seq (Run.seq run₁ run₂) run₃, ?_⟩
  rcases hstarted with ⟨hstack₂, htransition₂, haccepting₂, hdescriptor⟩
  have hagrees₃ : CompilerStorageAgrees sigma₂ sigma₃ :=
    ⟨hvars₃ _ (by decide), hvars₃ _ (by decide), hvars₃ _ (by decide),
      harrs₃ _ (by decide), harrs₃ _ (by decide), harrs₃ _ (by decide),
      harrs₃ _ (by decide), harrs₃ _ (by decide), harrs₃ _ (by decide),
      harrs₃ _ (by decide)⟩
  have hP : sigma₃.arrs "P" = sigma.arrs "P" :=
    (harrs₃ "P" (by decide)).trans
      ((harrs₂ "P" (by decide)).trans (harrs₁ "P" (by decide)))
  have hcompiledLength : (sigma₃.arrs "CompiledTransitions").length =
      (sigma.arrs "CompiledTransitions").length := by
    rw [harrs₃ "CompiledTransitions" (by decide),
      harrs₂ "CompiledTransitions" (by decide),
      harrs₁ "CompiledTransitions" (by decide)]
  have hchildrenLength :
      (sigma₃.arrs "NewTransitionChildren").length =
        maximumRank alphabet := by
    rw [harrs₃ "NewTransitionChildren" (by decide),
      harrs₂ "NewTransitionChildren" (by decide),
      harrs₁ "NewTransitionChildren" (by decide)]
    exact hchildren
  have preserveVar (name : String)
      (h₁ : name ∉ (.assign "newStates" (.lit 2) : Com).wvars)
      (h₂ : name ∉ beginCompiledAutomaton.wvars)
      (h₃ : name ∉ (.assign "binarySymbol" (.lit 0) : Com).wvars) :
      sigma₃.vars name = sigma.vars name := by
    exact (hvars₃ name h₃).trans ((hvars₂ name h₂).trans (hvars₁ name h₁))
  simp only [EqualityAutomatonRowsReady, EqualitySymbolsInv]
  refine ⟨?_, ?_, ?_, ?_, ?_, htwoB⟩
  · refine ⟨by omega,
      (preserveVar "markedSymbols" (by decide) (by decide) (by decide)).trans
        hmarkedSymbols,
      (preserveVar "soMarkerWords" (by decide) (by decide) (by decide)).trans
        hso,
      (preserveVar "foMarkerWords" (by decide) (by decide) (by decide)).trans
        hfo,
      hsymbolCountB, hsoB, hfoB, ?_, ?_, ?_, hmaximumRankB,
      compilerStackRep_of_agrees hagrees₃ hstack₂, ?_,
      acceptingHeapRep_of_agrees hagrees₃ haccepting₂,
      (preserveVar "currentFO" (by decide) (by decide) (by decide)).trans hn,
      (preserveVar "atomicLeft" (by decide) (by decide) (by decide)).trans hx,
      (preserveVar "atomicRight" (by decide) (by decide) (by decide)).trans hy,
      hxn, hyn, hnB, hxB, hyB, ?_, hchildrenLength,
      (preserveVar "transitionMaximumRank" (by decide) (by decide)
        (by decide)).trans hmaximumRank,
      by omega, (by simpa using hcountBounds), hwordBounds, ?_, ?_⟩
    · rw [hP]
      exact hPspace
    · rw [hP]
      exact hPlengthB
    · rw [hP]
      exact hprefix
    · have htransition₃ := transitionHeapRep_of_agrees hagrees₃ htransition₂
      simpa [hzero] using htransition₃
    · have hcount₃ : sigma₃.vars "newTransitionCount" = 0 :=
        (hvars₃ "newTransitionCount" (by decide)).trans
          (congrArg Descriptor.transitionCount hdescriptor)
      simpa [hzero] using hcount₃
    · intro a ha
      rw [hcompiledLength]
      exact hcapacityBounds a ha
    · rw [hcompiledLength]
      exact hheapLengthB
  · exact (hvars₃ "newStates" (by decide)).trans
      (congrArg Descriptor.states hdescriptor)
  · exact (hvars₃ "newTransitionBase" (by decide)).trans
      (congrArg Descriptor.transitionBase hdescriptor)
  · exact (hvars₃ "newAcceptingBase" (by decide)).trans
      (congrArg Descriptor.acceptingBase hdescriptor)
  · exact (hvars₃ "newAcceptingCount" (by decide)).trans
      (congrArg Descriptor.acceptingCount hdescriptor)

/-- Exact result after all equality-automaton transition rows have been
materialized, before its sole accepting state is appended. -/
def EqualityAutomatonRowsBuilt (alphabet : RankedAlphabetCode)
    (n m x y : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  let markedAlphabet := code alphabet n m
  let predicate := fun symbol =>
    foMarked n m symbol x && foMarked n m symbol y
  let M := binarySomewhereCode markedAlphabet predicate
  CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++ transitionWords (maximumRank alphabet) M) sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    preparedDescriptor sigma = {
      states := 2
      transitionBase := transitionPrefix.length
      transitionCount := M.2.1.length
      acceptingBase := acceptingPrefix.length
      acceptingCount := 0 }

/-- The completed outer loop has built exactly the transition segment of the
pure sparse equality automaton, with no transition advice in the input. -/
theorem equalityAutomatonRows_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (EqualityAutomatonRowsReady B alphabet n m x y stack
        transitionPrefix acceptingPrefix)
      (binarySymbolsLoop prepareEqualPredicate)
      (fun _ sigma' => EqualityAutomatonRowsBuilt alphabet n m x y stack
        transitionPrefix acceptingPrefix sigma')
      (equalitySymbolsLoopCost alphabet n m) := by
  refine (((equalitySymbolsLoop_spec B alphabet n m x y 0 stack
    transitionPrefix acceptingPrefix).pre (fun _ h => h.1)).frame).post ?_
  intro sigma sigma' hready hpost
  rcases hready with ⟨hinv0, hstates, htransitionBase,
    hacceptingBase, hacceptingCount, htwoB⟩
  rcases hpost with ⟨⟨hinv, hsymbol⟩, hvars, harrs, _, _⟩
  simp only [EqualitySymbolsInv] at hinv
  rcases hinv with ⟨hsymbolLe, hmarkedSymbols, hso, hfo,
    hsymbolCountB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
    hmaximumRankB, hstack, htransition, haccepting, hn, hx, hy,
    hxn, hyn, hnB, hxB, hyB, hcount, hchildren, hmaximumRank,
    honeB, hcountBounds, hwordBounds, hcapacityBounds, hheapLengthB⟩
  let markedAlphabet := code alphabet n m
  let predicate := fun symbol =>
    foMarked n m symbol x && foMarked n m symbol y
  let M := binarySomewhereCode markedAlphabet predicate
  have hmarkedLength : markedAlphabet.length = symbolCount alphabet n m := by
    exact code_length alphabet n m
  have htransitionFinal : TransitionHeapRep
      (transitionPrefix ++ transitionWords (maximumRank alphabet) M) sigma' := by
    rw [show transitionWords (maximumRank alphabet) M =
        binaryAlphabetRowsPrefix (maximumRank alphabet) markedAlphabet
          predicate markedAlphabet.length by
      exact (binaryAlphabetRowsPrefix_complete
        (maximumRank alphabet) markedAlphabet predicate).symm]
    rw [hmarkedLength]
    simpa [markedAlphabet, predicate, hsymbol] using htransition
  have hcountFinal : sigma'.vars "newTransitionCount" = M.2.1.length := by
    rw [show M.2.1.length =
        binaryAlphabetRowCount markedAlphabet markedAlphabet.length by
      exact binarySomewhereCode_transition_length markedAlphabet predicate]
    rw [hmarkedLength]
    simpa [markedAlphabet, hsymbol] using hcount
  simp only [EqualityAutomatonRowsBuilt]
  refine ⟨hstack, htransitionFinal, haccepting, ?_⟩
  apply Descriptor.ext
  · exact (hvars "newStates" (by decide)).trans hstates
  · exact (hvars "newTransitionBase" (by decide)).trans htransitionBase
  · simpa [preparedDescriptor, M, markedAlphabet, predicate] using hcountFinal
  · exact (hvars "newAcceptingBase" (by decide)).trans hacceptingBase
  · exact (hvars "newAcceptingCount" (by decide)).trans hacceptingCount

def EqualityAutomatonFinishReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  EqualityAutomatonRowsBuilt alphabet n m x y stack transitionPrefix
      acceptingPrefix sigma ∧
    1 < B ∧ acceptingPrefix.length + 1 < B ∧
    acceptingPrefix.length < (sigma.arrs "CompiledAccepting").length ∧
    (sigma.arrs "CompiledAccepting").length < B

def EqualityAcceptingAppended (alphabet : RankedAlphabetCode)
    (n m x y : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  let markedAlphabet := code alphabet n m
  let predicate := fun symbol =>
    foMarked n m symbol x && foMarked n m symbol y
  let M := binarySomewhereCode markedAlphabet predicate
  CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++ transitionWords (maximumRank alphabet) M) sigma ∧
    AcceptingHeapRep (acceptingPrefix ++ [1]) sigma ∧
    preparedDescriptor sigma = {
      states := 2
      transitionBase := transitionPrefix.length
      transitionCount := M.2.1.length
      acceptingBase := acceptingPrefix.length
      acceptingCount := 0 }

private theorem prepareAcceptingOne_spec (B : Nat) :
    Spec B (fun _ => 1 < B)
      (.assign "newAcceptingWord" (.lit 1))
      (fun _ sigma' => sigma'.vars "newAcceptingWord" = 1) 10 := by
  intro sigma honeB
  run_vcg
  all_goals simp_all

private theorem setAcceptingCountOne_spec (B : Nat) :
    Spec B (fun _ => 1 < B)
      (.assign "newAcceptingCount" (.lit 1))
      (fun _ sigma' => sigma'.vars "newAcceptingCount" = 1) 10 := by
  intro sigma honeB
  run_vcg
  all_goals simp_all

private theorem appendEqualityAccepting_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (EqualityAutomatonFinishReady B alphabet n m x y stack
        transitionPrefix acceptingPrefix)
      (.seq (.assign "newAcceptingWord" (.lit 1)) appendAcceptingWord)
      (fun _ sigma' => EqualityAcceptingAppended alphabet n m x y stack
        transitionPrefix acceptingPrefix sigma')
      40 := by
  refine Spec.seq
    ((prepareAcceptingOne_spec B).pre (fun _ h => h.2.1) |>.frame)
    ((appendAcceptingWord_spec B (maximumRank alphabet) stack
      acceptingPrefix 1).frame) ?_ ?_
  · intro sigma sigma' hready hprepared
    rcases hready with ⟨hrows, honeB, hnextB, hslot, hlengthB⟩
    rcases hprepared with ⟨hone, hvars, harrs, _, _⟩
    simp only [EqualityAutomatonRowsBuilt] at hrows
    rcases hrows with ⟨hstack, htransition, haccepting, hdescriptor⟩
    have hagrees : CompilerStorageAgrees sigma sigma' :=
      ⟨hvars _ (by decide), hvars _ (by decide), hvars _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide)⟩
    refine ⟨compilerStackRep_of_agrees hagrees hstack,
      acceptingHeapRep_of_agrees hagrees haccepting, hone, ?_, hnextB, ?_, ?_⟩
    · omega
    · rw [harrs "CompiledAccepting" (by decide)]
      exact hslot
    · rw [harrs "CompiledAccepting" (by decide)]
      exact hlengthB
  · intro sigma sigma' sigma'' hready hprepared happended
    rcases hready with ⟨hrows, honeB, hnextB, hslot, hlengthB⟩
    rcases hprepared with ⟨hone, hvars₁, harrs₁, _, _⟩
    rcases happended with ⟨happend, hvars₂, harrs₂, _, _⟩
    rcases happend with ⟨hstack, haccepting, hacceptingLength⟩
    simp only [EqualityAutomatonRowsBuilt] at hrows
    rcases hrows with ⟨hstack0, htransition, haccepting0, hdescriptor⟩
    have htransition' : TransitionHeapRep
        (transitionPrefix ++ transitionWords (maximumRank alphabet)
          (binarySomewhereCode (code alphabet n m)
            (fun symbol => foMarked n m symbol x && foMarked n m symbol y)))
        sigma'' := by
      rcases htransition with ⟨hcursor, hwords⟩
      constructor
      · exact (hvars₂ "compiledTransitionWords" (by decide)).trans
          ((hvars₁ "compiledTransitionWords" (by decide)).trans hcursor)
      · rw [harrs₂ "CompiledTransitions" (by decide),
          harrs₁ "CompiledTransitions" (by decide)]
        exact hwords
    have hdescriptor' : preparedDescriptor sigma'' = {
        states := 2
        transitionBase := transitionPrefix.length
        transitionCount :=
          (binarySomewhereCode (code alphabet n m)
            (fun symbol => foMarked n m symbol x &&
              foMarked n m symbol y)).2.1.length
        acceptingBase := acceptingPrefix.length
        acceptingCount := 0 } := by
      apply Descriptor.ext
      · exact (hvars₂ "newStates" (by decide)).trans
          ((hvars₁ "newStates" (by decide)).trans
            (congrArg Descriptor.states hdescriptor))
      · exact (hvars₂ "newTransitionBase" (by decide)).trans
          ((hvars₁ "newTransitionBase" (by decide)).trans
            (congrArg Descriptor.transitionBase hdescriptor))
      · exact (hvars₂ "newTransitionCount" (by decide)).trans
          ((hvars₁ "newTransitionCount" (by decide)).trans
            (congrArg Descriptor.transitionCount hdescriptor))
      · exact (hvars₂ "newAcceptingBase" (by decide)).trans
          ((hvars₁ "newAcceptingBase" (by decide)).trans
            (congrArg Descriptor.acceptingBase hdescriptor))
      · exact (hvars₂ "newAcceptingCount" (by decide)).trans
          ((hvars₁ "newAcceptingCount" (by decide)).trans
            (congrArg Descriptor.acceptingCount hdescriptor))
    simp only [EqualityAcceptingAppended]
    exact ⟨hstack, htransition', haccepting, hdescriptor'⟩

/-- Appending accepting state `1` and setting its descriptor count turns the
completed transition rows into the generic `BuiltAutomaton` contract. -/
theorem finishEqualityAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (EqualityAutomatonFinishReady B alphabet n m x y stack
        transitionPrefix acceptingPrefix)
      finishBinarySomewhere
      (fun _ sigma' => BuiltAutomaton (maximumRank alphabet) stack
        transitionPrefix acceptingPrefix
        (binarySomewhereCode (code alphabet n m)
          (fun symbol => foMarked n m symbol x && foMarked n m symbol y))
        sigma')
      50 := by
  unfold finishBinarySomewhere
  refine Spec.seq
    (appendEqualityAccepting_spec B alphabet n m x y stack
      transitionPrefix acceptingPrefix)
    ((setAcceptingCountOne_spec B).frame) ?_ ?_
  · intro sigma sigma' hready happended
    exact hready.2.1
  · intro sigma sigma' sigma'' hready happended hcount
    rcases happended with ⟨hstack, htransition, haccepting, hdescriptor⟩
    rcases hcount with ⟨hcount, hvars, harrs, _, _⟩
    let M := binarySomewhereCode (code alphabet n m)
      (fun symbol => foMarked n m symbol x && foMarked n m symbol y)
    have hagrees : CompilerStorageAgrees sigma' sigma'' :=
      ⟨hvars _ (by decide), hvars _ (by decide), hvars _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide)⟩
    have hdescriptor' : preparedDescriptor sigma'' = {
        states := M.1
        transitionBase := transitionPrefix.length
        transitionCount := M.2.1.length
        acceptingBase := acceptingPrefix.length
        acceptingCount := M.2.2.length } := by
      apply Descriptor.ext
      · simpa [M, preparedDescriptor] using
          (hvars "newStates" (by decide)).trans
            (congrArg Descriptor.states hdescriptor)
      · exact (hvars "newTransitionBase" (by decide)).trans
          (congrArg Descriptor.transitionBase hdescriptor)
      · simpa [M, preparedDescriptor] using
          (hvars "newTransitionCount" (by decide)).trans
            (congrArg Descriptor.transitionCount hdescriptor)
      · exact (hvars "newAcceptingBase" (by decide)).trans
          (congrArg Descriptor.acceptingBase hdescriptor)
      · simpa [M] using hcount
    change BuiltAutomaton (maximumRank alphabet) stack transitionPrefix
      acceptingPrefix M sigma''
    refine ⟨compilerStackRep_of_agrees hagrees hstack,
      transitionHeapRep_of_agrees hagrees htransition, ?_, hdescriptor'⟩
    have haccepting' := acceptingHeapRep_of_agrees hagrees haccepting
    simpa [M, binarySomewhereCode] using haccepting'

def EqualityAutomatonPushReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  let M := binarySomewhereCode (code alphabet n m)
    (fun symbol => foMarked n m symbol x && foMarked n m symbol y)
  EqualityAutomatonFinishReady B alphabet n m x y stack transitionPrefix
      acceptingPrefix sigma ∧
    M.1 < B ∧ transitionPrefix.length < B ∧ M.2.1.length < B ∧
    acceptingPrefix.length < B ∧ M.2.2.length < B ∧
    stack.length + 1 < B ∧
    stack.length < (sigma.arrs "AutomatonStatesStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionCountStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingCountStack").length ∧
    (sigma.arrs "AutomatonStatesStack").length < B ∧
    (sigma.arrs "AutomatonTransitionBaseStack").length < B ∧
    (sigma.arrs "AutomatonTransitionCountStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingBaseStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingCountStack").length < B

/-- Finish the immutable segment and push its descriptor onto the compiler
stack. -/
theorem finishAndPushEqualityAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    let M := binarySomewhereCode (code alphabet n m)
      (fun symbol => foMarked n m symbol x && foMarked n m symbol y)
    Spec B
      (EqualityAutomatonPushReady B alphabet n m x y stack
        transitionPrefix acceptingPrefix)
      finishAndPushBinarySomewhere
      (fun _ sigma' => CompilerStackRep (maximumRank alphabet)
        (M :: stack) sigma')
      150 := by
  dsimp only
  let M := binarySomewhereCode (code alphabet n m)
    (fun symbol => foMarked n m symbol x && foMarked n m symbol y)
  unfold finishAndPushBinarySomewhere
  refine Spec.seq
    ((finishEqualityAutomaton_spec B alphabet n m x y stack
      transitionPrefix acceptingPrefix).pre (fun _ h => h.1) |>.frame)
    (pushBuiltAutomaton_spec B (maximumRank alphabet) stack
      transitionPrefix acceptingPrefix M) ?_ ?_
  · intro sigma sigma' hready hfinished
    simp only [EqualityAutomatonPushReady] at hready
    rcases hready with ⟨hfinishReady, hstatesB, htransitionBaseB,
      htransitionCountB, hacceptingBaseB, hacceptingCountB, hdepthB,
      hstatesSpace, htransitionBaseSpace, htransitionCountSpace,
      hacceptingBaseSpace, hacceptingCountSpace, hstatesLengthB,
      htransitionBaseLengthB, htransitionCountLengthB,
      hacceptingBaseLengthB, hacceptingCountLengthB⟩
    rcases hfinished with ⟨hbuilt, hvars, harrs, _, _⟩
    refine ⟨hbuilt, hstatesB, htransitionBaseB, htransitionCountB,
      hacceptingBaseB, hacceptingCountB, hdepthB, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [harrs "AutomatonStatesStack" (by decide)]
      exact hstatesSpace
    · rw [harrs "AutomatonTransitionBaseStack" (by decide)]
      exact htransitionBaseSpace
    · rw [harrs "AutomatonTransitionCountStack" (by decide)]
      exact htransitionCountSpace
    · rw [harrs "AutomatonAcceptingBaseStack" (by decide)]
      exact hacceptingBaseSpace
    · rw [harrs "AutomatonAcceptingCountStack" (by decide)]
      exact hacceptingCountSpace
    · rw [harrs "AutomatonStatesStack" (by decide)]
      exact hstatesLengthB
    · rw [harrs "AutomatonTransitionBaseStack" (by decide)]
      exact htransitionBaseLengthB
    · rw [harrs "AutomatonTransitionCountStack" (by decide)]
      exact htransitionCountLengthB
    · rw [harrs "AutomatonAcceptingBaseStack" (by decide)]
      exact hacceptingBaseLengthB
    · rw [harrs "AutomatonAcceptingCountStack" (by decide)]
      exact hacceptingCountLengthB
  · intro sigma sigma' sigma'' hready hfinished hpushed
    exact hpushed

def EqualityAtomicReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m x y : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  let M := binarySomewhereCode (code alphabet n m)
    (fun symbol => foMarked n m symbol x && foMarked n m symbol y)
  EqualityAutomatonStartReady B alphabet n m x y stack transitionPrefix
      acceptingPrefix sigma ∧
    acceptingPrefix.length + 1 < B ∧
    acceptingPrefix.length < (sigma.arrs "CompiledAccepting").length ∧
    (sigma.arrs "CompiledAccepting").length < B ∧
    M.2.1.length < B ∧ stack.length + 1 < B ∧
    stack.length < (sigma.arrs "AutomatonStatesStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionCountStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingCountStack").length ∧
    (sigma.arrs "AutomatonStatesStack").length < B ∧
    (sigma.arrs "AutomatonTransitionBaseStack").length < B ∧
    (sigma.arrs "AutomatonTransitionCountStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingBaseStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingCountStack").length < B

def equalityAtomicAutomatonCost (alphabet : RankedAlphabetCode)
    (n m : Nat) : Nat :=
  70 + equalitySymbolsLoopCost alphabet n m + 150

/-- End-to-end charged construction of the equality atomic automaton.  The
postcondition is a logical compiler-stack entry for the pure sparse automaton;
all constructor tags, counters, row arithmetic, heap writes, and descriptor
updates remain behind this proof-package theorem. -/
theorem compileEqualAtomicAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x y : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    let M := binarySomewhereCode (code alphabet n m)
      (fun symbol => foMarked n m symbol x && foMarked n m symbol y)
    Spec B
      (EqualityAtomicReady B alphabet n m x y stack transitionPrefix
        acceptingPrefix)
      compileEqualAtomicAutomaton
      (fun _ sigma' => CompilerStackRep (maximumRank alphabet)
        (M :: stack) sigma')
      (equalityAtomicAutomatonCost alphabet n m) := by
  dsimp only
  let M := binarySomewhereCode (code alphabet n m)
    (fun symbol => foMarked n m symbol x && foMarked n m symbol y)
  unfold compileEqualAtomicAutomaton compileSomewhereAtomicAutomaton
    equalityAtomicAutomatonCost
  refine Spec.seq
    (show Spec B
        (EqualityAtomicReady B alphabet n m x y stack transitionPrefix
          acceptingPrefix)
        (.seq beginBinarySomewhere
          (binarySymbolsLoop prepareEqualPredicate))
        (fun _ sigma' => EqualityAutomatonPushReady B alphabet n m x y stack
          transitionPrefix acceptingPrefix sigma')
        (70 + equalitySymbolsLoopCost alphabet n m) by
      refine Spec.seq
        ((beginEqualityAutomaton_spec B alphabet n m x y stack
          transitionPrefix acceptingPrefix).pre (fun _ h => h.1) |>.frame)
        ((equalityAutomatonRows_spec B alphabet n m x y stack
          transitionPrefix acceptingPrefix).frame)
        (fun _ _ _ h => h.1) ?_
      intro sigma sigma' sigma'' hready hbegun hrows
      simp only [EqualityAtomicReady] at hready
      rcases hready with ⟨hstart, hacceptingNextB, hacceptingSpace,
        hacceptingLengthB, htransitionCountB, hdepthB,
        hstatesSpace, htransitionBaseSpace, htransitionCountSpace,
        hacceptingBaseSpace, hacceptingCountSpace, hstatesLengthB,
        htransitionBaseLengthB, htransitionCountLengthB,
        hacceptingBaseLengthB, hacceptingCountLengthB⟩
      rcases hbegun with ⟨hbegunCore, hvars₁, harrs₁, _, _⟩
      rcases hrows with ⟨hrowsCore, hvars₂, harrs₂, _, _⟩
      simp only [EqualityAutomatonStartReady] at hstart
      rcases hstart with ⟨hstack0, htransition0, haccepting0,
        hmarkedSymbols, hso, hfo, hsymbolCountB, hsoB, hfoB,
        hPspace, hPlengthB, hprefix, hmaximumRankB, hn, hx, hy,
        hxn, hyn, hnB, hxB, hyB, hchildren, hmaximumRank,
        htwoB, htransitionPrefixB, hacceptingPrefixB, hcountBounds,
        hwordBounds, hcapacityBounds, hcompiledLengthB⟩
      have arrayEq (name : String)
          (h₁ : name ∉ beginBinarySomewhere.warrs)
          (h₂ : name ∉ (binarySymbolsLoop prepareEqualPredicate).warrs) :
          sigma''.arrs name = sigma.arrs name :=
        (harrs₂ name h₂).trans (harrs₁ name h₁)
      have hacceptingSpace' : acceptingPrefix.length <
          (sigma''.arrs "CompiledAccepting").length := by
        rw [arrayEq "CompiledAccepting" (by decide) (by decide)]
        exact hacceptingSpace
      have hacceptingLengthB' :
          (sigma''.arrs "CompiledAccepting").length < B := by
        rw [arrayEq "CompiledAccepting" (by decide) (by decide)]
        exact hacceptingLengthB
      simp only [EqualityAutomatonPushReady]
      refine ⟨⟨hrowsCore, by omega, hacceptingNextB,
          hacceptingSpace', hacceptingLengthB'⟩,
        ?_, htransitionPrefixB, htransitionCountB,
        hacceptingPrefixB, ?_, hdepthB, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · simp [binarySomewhereCode]
        omega
      · simp [binarySomewhereCode]
        omega
      · rw [arrayEq "AutomatonStatesStack" (by decide) (by decide)]
        exact hstatesSpace
      · rw [arrayEq "AutomatonTransitionBaseStack" (by decide) (by decide)]
        exact htransitionBaseSpace
      · rw [arrayEq "AutomatonTransitionCountStack" (by decide) (by decide)]
        exact htransitionCountSpace
      · rw [arrayEq "AutomatonAcceptingBaseStack" (by decide) (by decide)]
        exact hacceptingBaseSpace
      · rw [arrayEq "AutomatonAcceptingCountStack" (by decide) (by decide)]
        exact hacceptingCountSpace
      · rw [arrayEq "AutomatonStatesStack" (by decide) (by decide)]
        exact hstatesLengthB
      · rw [arrayEq "AutomatonTransitionBaseStack" (by decide) (by decide)]
        exact htransitionBaseLengthB
      · rw [arrayEq "AutomatonTransitionCountStack" (by decide) (by decide)]
        exact htransitionCountLengthB
      · rw [arrayEq "AutomatonAcceptingBaseStack" (by decide) (by decide)]
        exact hacceptingBaseLengthB
      · rw [arrayEq "AutomatonAcceptingCountStack" (by decide) (by decide)]
        exact hacceptingCountLengthB)
    (finishAndPushEqualityAutomaton_spec B alphabet n m x y stack
      transitionPrefix acceptingPrefix)
    (fun _ _ _ h => h) ?_
  intro sigma sigma' sigma'' hready hfinishReady hdone
  exact hdone

/-! ## Shared end-to-end lifecycle for two-state atomic automata -/

/-- Predicate-independent storage and capacity obligations for opening a
two-state atomic automaton.  `atomContext` contains only the operand registers
and their static bounds; `predicate` determines the exact transition suffix. -/
def SomewhereAutomatonStartReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (atomContext : Env → Prop)
    (sigma : Env) : Prop :=
  let markedAlphabet := code alphabet n m
  CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "markedSymbols" = symbolCount alphabet n m ∧
    sigma.vars "soMarkerWords" = 2 ^ m ∧
    sigma.vars "foMarkerWords" = 2 ^ n ∧
    symbolCount alphabet n m < B ∧ 2 ^ m < B ∧ 2 ^ n < B ∧
    alphabet.length + 1 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    AlphabetPrefixEq (sigma.arrs "P") alphabet ∧
    maximumRank alphabet < B ∧ atomContext sigma ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank alphabet ∧
    sigma.vars "transitionMaximumRank" = maximumRank alphabet ∧
    2 < B ∧ transitionPrefix.length < B ∧ acceptingPrefix.length < B ∧
    (∀ a, a < symbolCount alphabet n m →
      binaryAlphabetRowCount markedAlphabet a +
        2 ^ markedAlphabet.getD a 0 < B) ∧
    (∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) < B) ∧
    (∀ a, a < symbolCount alphabet n m →
      (transitionPrefix ++ binaryAlphabetRowsPrefix
          (maximumRank alphabet) markedAlphabet predicate a).length +
        2 ^ markedAlphabet.getD a 0 * (maximumRank alphabet + 3) ≤
          (sigma.arrs "CompiledTransitions").length) ∧
    (sigma.arrs "CompiledTransitions").length < B

def SomewhereAutomatonRowsReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (atomContext : Env → Prop)
    (sigma : Env) : Prop :=
  SomewhereSymbolsInv B alphabet n m 0 stack transitionPrefix
      acceptingPrefix predicate atomContext sigma ∧
    sigma.vars "newStates" = 2 ∧
    sigma.vars "newTransitionBase" = transitionPrefix.length ∧
    sigma.vars "newAcceptingBase" = acceptingPrefix.length ∧
    sigma.vars "newAcceptingCount" = 0 ∧ 2 < B

/-- The segment-opening proof is independent of the atomic predicate.  Its
only parameterized obligation says that the fixed opener preserves the
operand context. -/
theorem beginSomewhereAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (atomContext : Env → Prop)
    (hcontextFrame : ∀ {sigma sigma' K}, atomContext sigma →
      Run B beginBinarySomewhere sigma sigma' K → atomContext sigma') :
    Spec B
      (SomewhereAutomatonStartReady B alphabet n m stack
        transitionPrefix acceptingPrefix predicate atomContext)
      beginBinarySomewhere
      (fun _ sigma' => SomewhereAutomatonRowsReady B alphabet n m stack
        transitionPrefix acceptingPrefix predicate atomContext sigma')
      70 := by
  intro sigma hready
  simp only [SomewhereAutomatonStartReady] at hready
  rcases hready with ⟨hstack, htransition, haccepting, hmarkedSymbols,
    hso, hfo, hsymbolCountB, hsoB, hfoB, hPspace, hPlengthB,
    hprefix, hmaximumRankB, hatom, hchildren, hmaximumRank, htwoB,
    htransitionPrefixB, hacceptingPrefixB, hcountBounds, hwordBounds,
    hcapacityBounds, hheapLengthB⟩
  obtain ⟨sigma₁, run₁, hstates, hvars₁, harrs₁, _, _⟩ :=
    (prepareTwoStates_spec B).frame.run (σ := sigma) htwoB
  have hagrees₁ : CompilerStorageAgrees sigma sigma₁ :=
    ⟨hvars₁ _ (by decide), hvars₁ _ (by decide), hvars₁ _ (by decide),
      harrs₁ _ (by decide), harrs₁ _ (by decide), harrs₁ _ (by decide),
      harrs₁ _ (by decide), harrs₁ _ (by decide), harrs₁ _ (by decide),
      harrs₁ _ (by decide)⟩
  have hbeginReady : AutomatonBuildStartReady B (maximumRank alphabet)
      stack transitionPrefix acceptingPrefix 2 sigma₁ := by
    refine ⟨compilerStackRep_of_agrees hagrees₁ hstack,
      transitionHeapRep_of_agrees hagrees₁ htransition,
      acceptingHeapRep_of_agrees hagrees₁ haccepting, hstates, htwoB,
      htransitionPrefixB, hacceptingPrefixB, by omega⟩
  obtain ⟨sigma₂, run₂, hstarted, hvars₂, harrs₂, _, _⟩ :=
    (beginCompiledAutomaton_spec B (maximumRank alphabet) stack
      transitionPrefix acceptingPrefix 2).frame.run hbeginReady
  obtain ⟨sigma₃, run₃, hzero, hvars₃, harrs₃, _, _⟩ :=
    (beginBinarySymbolZero_spec B).frame.run (σ := sigma₂) (by omega)
  have run : Run B beginBinarySomewhere sigma sigma₃ 70 :=
    Run.seq (Run.seq run₁ run₂) run₃
  refine ⟨sigma₃, run, ?_⟩
  rcases hstarted with ⟨hstack₂, htransition₂, haccepting₂, hdescriptor⟩
  have hagrees₃ : CompilerStorageAgrees sigma₂ sigma₃ :=
    ⟨hvars₃ _ (by decide), hvars₃ _ (by decide), hvars₃ _ (by decide),
      harrs₃ _ (by decide), harrs₃ _ (by decide), harrs₃ _ (by decide),
      harrs₃ _ (by decide), harrs₃ _ (by decide), harrs₃ _ (by decide),
      harrs₃ _ (by decide)⟩
  have hP : sigma₃.arrs "P" = sigma.arrs "P" :=
    run.frame_arr "P" (by decide)
  have hcompiledLength : (sigma₃.arrs "CompiledTransitions").length =
      (sigma.arrs "CompiledTransitions").length := by
    rw [run.frame_arr "CompiledTransitions" (by decide)]
  have hchildrenLength :
      (sigma₃.arrs "NewTransitionChildren").length =
        maximumRank alphabet := by
    rw [run.frame_arr "NewTransitionChildren" (by decide)]
    exact hchildren
  simp only [SomewhereAutomatonRowsReady, SomewhereSymbolsInv]
  refine ⟨?_, ?_, ?_, ?_, ?_, htwoB⟩
  · refine ⟨by omega,
      (run.frame_var "markedSymbols" (by decide)).trans hmarkedSymbols,
      (run.frame_var "soMarkerWords" (by decide)).trans hso,
      (run.frame_var "foMarkerWords" (by decide)).trans hfo,
      hsymbolCountB, hsoB, hfoB, ?_, ?_, ?_, hmaximumRankB,
      compilerStackRep_of_agrees hagrees₃ hstack₂, ?_,
      acceptingHeapRep_of_agrees hagrees₃ haccepting₂,
      hcontextFrame hatom run, ?_, hchildrenLength,
      (run.frame_var "transitionMaximumRank" (by decide)).trans hmaximumRank,
      by omega, (by simpa using hcountBounds), hwordBounds, ?_, ?_⟩
    · rw [hP]
      exact hPspace
    · rw [hP]
      exact hPlengthB
    · rw [hP]
      exact hprefix
    · have htransition₃ := transitionHeapRep_of_agrees hagrees₃ htransition₂
      simpa [hzero] using htransition₃
    · have hcount₃ : sigma₃.vars "newTransitionCount" = 0 :=
        (hvars₃ "newTransitionCount" (by decide)).trans
          (congrArg Descriptor.transitionCount hdescriptor)
      simpa [hzero] using hcount₃
    · intro a ha
      rw [hcompiledLength]
      exact hcapacityBounds a ha
    · rw [hcompiledLength]
      exact hheapLengthB
  · exact (hvars₃ "newStates" (by decide)).trans
      (congrArg Descriptor.states hdescriptor)
  · exact (hvars₃ "newTransitionBase" (by decide)).trans
      (congrArg Descriptor.transitionBase hdescriptor)
  · exact (hvars₃ "newAcceptingBase" (by decide)).trans
      (congrArg Descriptor.acceptingBase hdescriptor)
  · exact (hvars₃ "newAcceptingCount" (by decide)).trans
      (congrArg Descriptor.acceptingCount hdescriptor)

def SomewhereAutomatonRowsBuilt (alphabet : RankedAlphabetCode)
    (n m : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (sigma : Env) : Prop :=
  let markedAlphabet := code alphabet n m
  let M := binarySomewhereCode markedAlphabet predicate
  CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++ transitionWords (maximumRank alphabet) M) sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    preparedDescriptor sigma = {
      states := 2
      transitionBase := transitionPrefix.length
      transitionCount := M.2.1.length
      acceptingBase := acceptingPrefix.length
      acceptingCount := 0 }

/-- Any verified structural-alphabet loop plugs into the same proof that its
completed row prefix is precisely the transition segment of
`binarySomewhereCode`. -/
theorem somewhereAutomatonRows_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (preparePredicate : Com)
    (atomContext : Env → Prop) (prepareCost : Nat)
    (hloop : Spec B
      (SomewhereSymbolsInv B alphabet n m 0 stack transitionPrefix
        acceptingPrefix predicate atomContext)
      (binarySymbolsLoop preparePredicate)
      (fun _ sigma' =>
        SomewhereSymbolsInv B alphabet n m 0 stack transitionPrefix
          acceptingPrefix predicate atomContext sigma' ∧
        sigma'.vars "binarySymbol" = symbolCount alphabet n m)
      (somewhereSymbolsLoopCost alphabet n m prepareCost))
    (hstatesFrame : "newStates" ∉
      (binarySymbolsLoop preparePredicate).wvars)
    (htransitionBaseFrame : "newTransitionBase" ∉
      (binarySymbolsLoop preparePredicate).wvars)
    (hacceptingBaseFrame : "newAcceptingBase" ∉
      (binarySymbolsLoop preparePredicate).wvars)
    (hacceptingCountFrame : "newAcceptingCount" ∉
      (binarySymbolsLoop preparePredicate).wvars) :
    Spec B
      (SomewhereAutomatonRowsReady B alphabet n m stack
        transitionPrefix acceptingPrefix predicate atomContext)
      (binarySymbolsLoop preparePredicate)
      (fun _ sigma' => SomewhereAutomatonRowsBuilt alphabet n m stack
        transitionPrefix acceptingPrefix predicate sigma')
      (somewhereSymbolsLoopCost alphabet n m prepareCost) := by
  refine ((hloop.pre (fun _ h => h.1)).frame).post ?_
  intro sigma sigma' hready hpost
  rcases hready with ⟨hinv0, hstates, htransitionBase,
    hacceptingBase, hacceptingCount, htwoB⟩
  rcases hpost with ⟨⟨hinv, hsymbol⟩, hvars, harrs, _, _⟩
  simp only [SomewhereSymbolsInv] at hinv
  rcases hinv with ⟨hsymbolLe, hmarkedSymbols, hso, hfo,
    hsymbolCountB, hsoB, hfoB, hPspace, hPlengthB, hprefix,
    hmaximumRankB, hstack, htransition, haccepting, hatom, hcount,
    hchildren, hmaximumRank, honeB, hcountBounds, hwordBounds,
    hcapacityBounds, hheapLengthB⟩
  let markedAlphabet := code alphabet n m
  let M := binarySomewhereCode markedAlphabet predicate
  have hmarkedLength : markedAlphabet.length = symbolCount alphabet n m :=
    code_length alphabet n m
  have htransitionFinal : TransitionHeapRep
      (transitionPrefix ++ transitionWords (maximumRank alphabet) M) sigma' := by
    rw [show transitionWords (maximumRank alphabet) M =
        binaryAlphabetRowsPrefix (maximumRank alphabet) markedAlphabet
          predicate markedAlphabet.length by
      exact (binaryAlphabetRowsPrefix_complete
        (maximumRank alphabet) markedAlphabet predicate).symm]
    rw [hmarkedLength]
    simpa [markedAlphabet, hsymbol] using htransition
  have hcountFinal : sigma'.vars "newTransitionCount" = M.2.1.length := by
    rw [show M.2.1.length =
        binaryAlphabetRowCount markedAlphabet markedAlphabet.length by
      exact binarySomewhereCode_transition_length markedAlphabet predicate]
    rw [hmarkedLength]
    simpa [markedAlphabet, hsymbol] using hcount
  simp only [SomewhereAutomatonRowsBuilt]
  refine ⟨hstack, htransitionFinal, haccepting, ?_⟩
  apply Descriptor.ext
  · exact (hvars "newStates" hstatesFrame).trans hstates
  · exact (hvars "newTransitionBase" htransitionBaseFrame).trans
      htransitionBase
  · simpa [preparedDescriptor, M, markedAlphabet] using hcountFinal
  · exact (hvars "newAcceptingBase" hacceptingBaseFrame).trans hacceptingBase
  · exact (hvars "newAcceptingCount" hacceptingCountFrame).trans
      hacceptingCount

def SomewhereAutomatonFinishReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (sigma : Env) : Prop :=
  SomewhereAutomatonRowsBuilt alphabet n m stack transitionPrefix
      acceptingPrefix predicate sigma ∧
    1 < B ∧ acceptingPrefix.length + 1 < B ∧
    acceptingPrefix.length < (sigma.arrs "CompiledAccepting").length ∧
    (sigma.arrs "CompiledAccepting").length < B

def SomewhereAcceptingAppended (alphabet : RankedAlphabetCode)
    (n m : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (sigma : Env) : Prop :=
  let M := binarySomewhereCode (code alphabet n m) predicate
  CompilerStackRep (maximumRank alphabet) stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++ transitionWords (maximumRank alphabet) M) sigma ∧
    AcceptingHeapRep (acceptingPrefix ++ [1]) sigma ∧
    preparedDescriptor sigma = {
      states := 2
      transitionBase := transitionPrefix.length
      transitionCount := M.2.1.length
      acceptingBase := acceptingPrefix.length
      acceptingCount := 0 }

private theorem appendSomewhereAccepting_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) :
    Spec B
      (SomewhereAutomatonFinishReady B alphabet n m stack
        transitionPrefix acceptingPrefix predicate)
      (.seq (.assign "newAcceptingWord" (.lit 1)) appendAcceptingWord)
      (fun _ sigma' => SomewhereAcceptingAppended alphabet n m stack
        transitionPrefix acceptingPrefix predicate sigma')
      40 := by
  refine Spec.seq
    ((prepareAcceptingOne_spec B).pre (fun _ h => h.2.1) |>.frame)
    ((appendAcceptingWord_spec B (maximumRank alphabet) stack
      acceptingPrefix 1).frame) ?_ ?_
  · intro sigma sigma' hready hprepared
    rcases hready with ⟨hrows, honeB, hnextB, hslot, hlengthB⟩
    rcases hprepared with ⟨hone, hvars, harrs, _, _⟩
    simp only [SomewhereAutomatonRowsBuilt] at hrows
    rcases hrows with ⟨hstack, htransition, haccepting, hdescriptor⟩
    have hagrees : CompilerStorageAgrees sigma sigma' :=
      ⟨hvars _ (by decide), hvars _ (by decide), hvars _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide)⟩
    refine ⟨compilerStackRep_of_agrees hagrees hstack,
      acceptingHeapRep_of_agrees hagrees haccepting, hone, ?_, hnextB, ?_, ?_⟩
    · omega
    · rw [harrs "CompiledAccepting" (by decide)]
      exact hslot
    · rw [harrs "CompiledAccepting" (by decide)]
      exact hlengthB
  · intro sigma sigma' sigma'' hready hprepared happended
    rcases hready with ⟨hrows, honeB, hnextB, hslot, hlengthB⟩
    rcases hprepared with ⟨hone, hvars₁, harrs₁, _, _⟩
    rcases happended with ⟨happend, hvars₂, harrs₂, _, _⟩
    rcases happend with ⟨hstack, haccepting, hacceptingLength⟩
    simp only [SomewhereAutomatonRowsBuilt] at hrows
    rcases hrows with ⟨hstack0, htransition, haccepting0, hdescriptor⟩
    have htransition' : TransitionHeapRep
        (transitionPrefix ++ transitionWords (maximumRank alphabet)
          (binarySomewhereCode (code alphabet n m) predicate)) sigma'' := by
      rcases htransition with ⟨hcursor, hwords⟩
      constructor
      · exact (hvars₂ "compiledTransitionWords" (by decide)).trans
          ((hvars₁ "compiledTransitionWords" (by decide)).trans hcursor)
      · rw [harrs₂ "CompiledTransitions" (by decide),
          harrs₁ "CompiledTransitions" (by decide)]
        exact hwords
    have hdescriptor' : preparedDescriptor sigma'' = {
        states := 2
        transitionBase := transitionPrefix.length
        transitionCount :=
          (binarySomewhereCode (code alphabet n m) predicate).2.1.length
        acceptingBase := acceptingPrefix.length
        acceptingCount := 0 } := by
      apply Descriptor.ext
      · exact (hvars₂ "newStates" (by decide)).trans
          ((hvars₁ "newStates" (by decide)).trans
            (congrArg Descriptor.states hdescriptor))
      · exact (hvars₂ "newTransitionBase" (by decide)).trans
          ((hvars₁ "newTransitionBase" (by decide)).trans
            (congrArg Descriptor.transitionBase hdescriptor))
      · exact (hvars₂ "newTransitionCount" (by decide)).trans
          ((hvars₁ "newTransitionCount" (by decide)).trans
            (congrArg Descriptor.transitionCount hdescriptor))
      · exact (hvars₂ "newAcceptingBase" (by decide)).trans
          ((hvars₁ "newAcceptingBase" (by decide)).trans
            (congrArg Descriptor.acceptingBase hdescriptor))
      · exact (hvars₂ "newAcceptingCount" (by decide)).trans
          ((hvars₁ "newAcceptingCount" (by decide)).trans
            (congrArg Descriptor.acceptingCount hdescriptor))
    simp only [SomewhereAcceptingAppended]
    exact ⟨hstack, htransition', haccepting, hdescriptor'⟩

theorem finishSomewhereAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) :
    Spec B
      (SomewhereAutomatonFinishReady B alphabet n m stack
        transitionPrefix acceptingPrefix predicate)
      finishBinarySomewhere
      (fun _ sigma' => BuiltAutomaton (maximumRank alphabet) stack
        transitionPrefix acceptingPrefix
        (binarySomewhereCode (code alphabet n m) predicate) sigma')
      50 := by
  unfold finishBinarySomewhere
  refine Spec.seq
    (appendSomewhereAccepting_spec B alphabet n m stack transitionPrefix
      acceptingPrefix predicate)
    ((setAcceptingCountOne_spec B).frame) ?_ ?_
  · intro sigma sigma' hready happended
    exact hready.2.1
  · intro sigma sigma' sigma'' hready happended hcount
    rcases happended with ⟨hstack, htransition, haccepting, hdescriptor⟩
    rcases hcount with ⟨hcount, hvars, harrs, _, _⟩
    let M := binarySomewhereCode (code alphabet n m) predicate
    have hagrees : CompilerStorageAgrees sigma' sigma'' :=
      ⟨hvars _ (by decide), hvars _ (by decide), hvars _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
        harrs _ (by decide)⟩
    have hdescriptor' : preparedDescriptor sigma'' = {
        states := M.1
        transitionBase := transitionPrefix.length
        transitionCount := M.2.1.length
        acceptingBase := acceptingPrefix.length
        acceptingCount := M.2.2.length } := by
      apply Descriptor.ext
      · simpa [M, preparedDescriptor] using
          (hvars "newStates" (by decide)).trans
            (congrArg Descriptor.states hdescriptor)
      · exact (hvars "newTransitionBase" (by decide)).trans
          (congrArg Descriptor.transitionBase hdescriptor)
      · simpa [M, preparedDescriptor] using
          (hvars "newTransitionCount" (by decide)).trans
            (congrArg Descriptor.transitionCount hdescriptor)
      · exact (hvars "newAcceptingBase" (by decide)).trans
          (congrArg Descriptor.acceptingBase hdescriptor)
      · simpa [M] using hcount
    change BuiltAutomaton (maximumRank alphabet) stack transitionPrefix
      acceptingPrefix M sigma''
    refine ⟨compilerStackRep_of_agrees hagrees hstack,
      transitionHeapRep_of_agrees hagrees htransition, ?_, hdescriptor'⟩
    have haccepting' := acceptingHeapRep_of_agrees hagrees haccepting
    simpa [M, binarySomewhereCode] using haccepting'

def SomewhereAutomatonPushReady (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (sigma : Env) : Prop :=
  let M := binarySomewhereCode (code alphabet n m) predicate
  SomewhereAutomatonFinishReady B alphabet n m stack transitionPrefix
      acceptingPrefix predicate sigma ∧
    M.1 < B ∧ transitionPrefix.length < B ∧ M.2.1.length < B ∧
    acceptingPrefix.length < B ∧ M.2.2.length < B ∧
    stack.length + 1 < B ∧
    stack.length < (sigma.arrs "AutomatonStatesStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionCountStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingCountStack").length ∧
    (sigma.arrs "AutomatonStatesStack").length < B ∧
    (sigma.arrs "AutomatonTransitionBaseStack").length < B ∧
    (sigma.arrs "AutomatonTransitionCountStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingBaseStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingCountStack").length < B

theorem finishAndPushSomewhereAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) :
    let M := binarySomewhereCode (code alphabet n m) predicate
    Spec B
      (SomewhereAutomatonPushReady B alphabet n m stack transitionPrefix
        acceptingPrefix predicate)
      finishAndPushBinarySomewhere
      (fun _ sigma' => CompilerStackRep (maximumRank alphabet)
        (M :: stack) sigma')
      150 := by
  dsimp only
  let M := binarySomewhereCode (code alphabet n m) predicate
  unfold finishAndPushBinarySomewhere
  refine Spec.seq
    ((finishSomewhereAutomaton_spec B alphabet n m stack transitionPrefix
      acceptingPrefix predicate).pre (fun _ h => h.1) |>.frame)
    (pushBuiltAutomaton_spec B (maximumRank alphabet) stack
      transitionPrefix acceptingPrefix M) ?_ ?_
  · intro sigma sigma' hready hfinished
    simp only [SomewhereAutomatonPushReady] at hready
    rcases hready with ⟨hfinishReady, hstatesB, htransitionBaseB,
      htransitionCountB, hacceptingBaseB, hacceptingCountB, hdepthB,
      hstatesSpace, htransitionBaseSpace, htransitionCountSpace,
      hacceptingBaseSpace, hacceptingCountSpace, hstatesLengthB,
      htransitionBaseLengthB, htransitionCountLengthB,
      hacceptingBaseLengthB, hacceptingCountLengthB⟩
    rcases hfinished with ⟨hbuilt, hvars, harrs, _, _⟩
    refine ⟨hbuilt, hstatesB, htransitionBaseB, htransitionCountB,
      hacceptingBaseB, hacceptingCountB, hdepthB, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [harrs "AutomatonStatesStack" (by decide)]
      exact hstatesSpace
    · rw [harrs "AutomatonTransitionBaseStack" (by decide)]
      exact htransitionBaseSpace
    · rw [harrs "AutomatonTransitionCountStack" (by decide)]
      exact htransitionCountSpace
    · rw [harrs "AutomatonAcceptingBaseStack" (by decide)]
      exact hacceptingBaseSpace
    · rw [harrs "AutomatonAcceptingCountStack" (by decide)]
      exact hacceptingCountSpace
    · rw [harrs "AutomatonStatesStack" (by decide)]
      exact hstatesLengthB
    · rw [harrs "AutomatonTransitionBaseStack" (by decide)]
      exact htransitionBaseLengthB
    · rw [harrs "AutomatonTransitionCountStack" (by decide)]
      exact htransitionCountLengthB
    · rw [harrs "AutomatonAcceptingBaseStack" (by decide)]
      exact hacceptingBaseLengthB
    · rw [harrs "AutomatonAcceptingCountStack" (by decide)]
      exact hacceptingCountLengthB
  · intro sigma sigma' sigma'' hready hfinished hpushed
    exact hpushed

def SomewhereAtomicReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (atomContext : Env → Prop)
    (sigma : Env) : Prop :=
  let M := binarySomewhereCode (code alphabet n m) predicate
  SomewhereAutomatonStartReady B alphabet n m stack transitionPrefix
      acceptingPrefix predicate atomContext sigma ∧
    acceptingPrefix.length + 1 < B ∧
    acceptingPrefix.length < (sigma.arrs "CompiledAccepting").length ∧
    (sigma.arrs "CompiledAccepting").length < B ∧
    M.2.1.length < B ∧ stack.length + 1 < B ∧
    stack.length < (sigma.arrs "AutomatonStatesStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionCountStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingCountStack").length ∧
    (sigma.arrs "AutomatonStatesStack").length < B ∧
    (sigma.arrs "AutomatonTransitionBaseStack").length < B ∧
    (sigma.arrs "AutomatonTransitionCountStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingBaseStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingCountStack").length < B

def somewhereAtomicAutomatonCost (alphabet : RankedAlphabetCode)
    (n m prepareCost : Nat) : Nat :=
  70 + somewhereSymbolsLoopCost alphabet n m prepareCost + 150

/-- Complete predicate-parametric implementation theorem for a two-state
"somewhere" atom.  Concrete atoms provide only their operand-context frame,
their checked predicate loop, and syntactic non-write certificates. -/
theorem compileSomewhereAtomicAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (predicate : Nat → Bool) (preparePredicate : Com)
    (atomContext : Env → Prop) (prepareCost : Nat)
    (hcontextFrame : ∀ {sigma sigma' K}, atomContext sigma →
      Run B beginBinarySomewhere sigma sigma' K → atomContext sigma')
    (hloop : Spec B
      (SomewhereSymbolsInv B alphabet n m 0 stack transitionPrefix
        acceptingPrefix predicate atomContext)
      (binarySymbolsLoop preparePredicate)
      (fun _ sigma' =>
        SomewhereSymbolsInv B alphabet n m 0 stack transitionPrefix
          acceptingPrefix predicate atomContext sigma' ∧
        sigma'.vars "binarySymbol" = symbolCount alphabet n m)
      (somewhereSymbolsLoopCost alphabet n m prepareCost))
    (hstatesFrame : "newStates" ∉
      (binarySymbolsLoop preparePredicate).wvars)
    (htransitionBaseFrame : "newTransitionBase" ∉
      (binarySymbolsLoop preparePredicate).wvars)
    (hacceptingBaseFrame : "newAcceptingBase" ∉
      (binarySymbolsLoop preparePredicate).wvars)
    (hacceptingCountFrame : "newAcceptingCount" ∉
      (binarySymbolsLoop preparePredicate).wvars)
    (hcompiledAcceptingFrame : "CompiledAccepting" ∉
      (binarySymbolsLoop preparePredicate).warrs)
    (hstatesStackFrame : "AutomatonStatesStack" ∉
      (binarySymbolsLoop preparePredicate).warrs)
    (htransitionBaseStackFrame : "AutomatonTransitionBaseStack" ∉
      (binarySymbolsLoop preparePredicate).warrs)
    (htransitionCountStackFrame : "AutomatonTransitionCountStack" ∉
      (binarySymbolsLoop preparePredicate).warrs)
    (hacceptingBaseStackFrame : "AutomatonAcceptingBaseStack" ∉
      (binarySymbolsLoop preparePredicate).warrs)
    (hacceptingCountStackFrame : "AutomatonAcceptingCountStack" ∉
      (binarySymbolsLoop preparePredicate).warrs) :
    let M := binarySomewhereCode (code alphabet n m) predicate
    Spec B
      (SomewhereAtomicReady B alphabet n m stack transitionPrefix
        acceptingPrefix predicate atomContext)
      (compileSomewhereAtomicAutomaton preparePredicate)
      (fun _ sigma' => CompilerStackRep (maximumRank alphabet)
        (M :: stack) sigma')
      (somewhereAtomicAutomatonCost alphabet n m prepareCost) := by
  dsimp only
  let M := binarySomewhereCode (code alphabet n m) predicate
  unfold compileSomewhereAtomicAutomaton somewhereAtomicAutomatonCost
  refine Spec.seq
    (show Spec B
        (SomewhereAtomicReady B alphabet n m stack transitionPrefix
          acceptingPrefix predicate atomContext)
        (.seq beginBinarySomewhere
          (binarySymbolsLoop preparePredicate))
        (fun _ sigma' => SomewhereAutomatonPushReady B alphabet n m stack
          transitionPrefix acceptingPrefix predicate sigma')
        (70 + somewhereSymbolsLoopCost alphabet n m prepareCost) by
      refine Spec.seq
        ((beginSomewhereAutomaton_spec B alphabet n m stack
          transitionPrefix acceptingPrefix predicate atomContext
          hcontextFrame).pre (fun _ h => h.1) |>.frame)
        ((somewhereAutomatonRows_spec B alphabet n m stack
          transitionPrefix acceptingPrefix predicate preparePredicate
          atomContext prepareCost hloop hstatesFrame htransitionBaseFrame
          hacceptingBaseFrame hacceptingCountFrame).frame)
        (fun _ _ _ h => h.1) ?_
      intro sigma sigma' sigma'' hready hbegun hrows
      simp only [SomewhereAtomicReady] at hready
      rcases hready with ⟨hstart, hacceptingNextB, hacceptingSpace,
        hacceptingLengthB, htransitionCountB, hdepthB,
        hstatesSpace, htransitionBaseSpace, htransitionCountSpace,
        hacceptingBaseSpace, hacceptingCountSpace, hstatesLengthB,
        htransitionBaseLengthB, htransitionCountLengthB,
        hacceptingBaseLengthB, hacceptingCountLengthB⟩
      rcases hbegun with ⟨hbegunCore, hvars₁, harrs₁, _, _⟩
      rcases hrows with ⟨hrowsCore, hvars₂, harrs₂, _, _⟩
      simp only [SomewhereAutomatonStartReady] at hstart
      rcases hstart with ⟨hstack0, htransition0, haccepting0,
        hmarkedSymbols, hso, hfo, hsymbolCountB, hsoB, hfoB,
        hPspace, hPlengthB, hprefix, hmaximumRankB, hatom,
        hchildren, hmaximumRank, htwoB, htransitionPrefixB,
        hacceptingPrefixB, hcountBounds, hwordBounds,
        hcapacityBounds, hcompiledLengthB⟩
      have arrayEq (name : String)
          (h₁ : name ∉ beginBinarySomewhere.warrs)
          (h₂ : name ∉ (binarySymbolsLoop preparePredicate).warrs) :
          sigma''.arrs name = sigma.arrs name :=
        (harrs₂ name h₂).trans (harrs₁ name h₁)
      have hacceptingSpace' : acceptingPrefix.length <
          (sigma''.arrs "CompiledAccepting").length := by
        rw [arrayEq "CompiledAccepting" (by decide)
          hcompiledAcceptingFrame]
        exact hacceptingSpace
      have hacceptingLengthB' :
          (sigma''.arrs "CompiledAccepting").length < B := by
        rw [arrayEq "CompiledAccepting" (by decide)
          hcompiledAcceptingFrame]
        exact hacceptingLengthB
      simp only [SomewhereAutomatonPushReady]
      refine ⟨⟨hrowsCore, by omega, hacceptingNextB,
          hacceptingSpace', hacceptingLengthB'⟩,
        ?_, htransitionPrefixB, htransitionCountB,
        hacceptingPrefixB, ?_, hdepthB, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · simp [binarySomewhereCode]
        omega
      · simp [binarySomewhereCode]
        omega
      · rw [arrayEq "AutomatonStatesStack" (by decide) hstatesStackFrame]
        exact hstatesSpace
      · rw [arrayEq "AutomatonTransitionBaseStack" (by decide)
          htransitionBaseStackFrame]
        exact htransitionBaseSpace
      · rw [arrayEq "AutomatonTransitionCountStack" (by decide)
          htransitionCountStackFrame]
        exact htransitionCountSpace
      · rw [arrayEq "AutomatonAcceptingBaseStack" (by decide)
          hacceptingBaseStackFrame]
        exact hacceptingBaseSpace
      · rw [arrayEq "AutomatonAcceptingCountStack" (by decide)
          hacceptingCountStackFrame]
        exact hacceptingCountSpace
      · rw [arrayEq "AutomatonStatesStack" (by decide) hstatesStackFrame]
        exact hstatesLengthB
      · rw [arrayEq "AutomatonTransitionBaseStack" (by decide)
          htransitionBaseStackFrame]
        exact htransitionBaseLengthB
      · rw [arrayEq "AutomatonTransitionCountStack" (by decide)
          htransitionCountStackFrame]
        exact htransitionCountLengthB
      · rw [arrayEq "AutomatonAcceptingBaseStack" (by decide)
          hacceptingBaseStackFrame]
        exact hacceptingBaseLengthB
      · rw [arrayEq "AutomatonAcceptingCountStack" (by decide)
          hacceptingCountStackFrame]
        exact hacceptingCountLengthB)
    (finishAndPushSomewhereAutomaton_spec B alphabet n m stack
      transitionPrefix acceptingPrefix predicate)
    (fun _ _ _ h => h) ?_
  intro sigma sigma' sigma'' hready hfinishReady hdone
  exact hdone

private theorem labelAtomContext_begin_frame (B n x label : Nat)
    {sigma sigma' : Env} {K : Nat}
    (h : LabelAtomContext B n x label sigma)
    (run : Run B beginBinarySomewhere sigma sigma' K) :
    LabelAtomContext B n x label sigma' := by
  rcases h with ⟨hn, hx, hlabel, hxn, hnB, hxB, hlabelB⟩
  exact ⟨(run.frame_var "currentFO" (by decide)).trans hn,
    (run.frame_var "atomicLeft" (by decide)).trans hx,
    (run.frame_var "atomicLabel" (by decide)).trans hlabel,
    hxn, hnB, hxB, hlabelB⟩

def LabelAtomicReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m x label : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  SomewhereAtomicReady B alphabet n m stack transitionPrefix acceptingPrefix
    (fun symbol => decide (baseSymbol n m symbol = label) &&
      foMarked n m symbol x)
    (LabelAtomContext B n x label) sigma

def labelAtomicAutomatonCost (alphabet : RankedAlphabetCode)
    (n m : Nat) : Nat :=
  somewhereAtomicAutomatonCost alphabet n m 120

/-- Charged end-to-end construction of the label atomic automaton from the
packed marked alphabet, with no predicate table supplied as input. -/
theorem compileLabelAtomicAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x label : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    let M := binarySomewhereCode (code alphabet n m)
      (fun symbol => decide (baseSymbol n m symbol = label) &&
        foMarked n m symbol x)
    Spec B
      (LabelAtomicReady B alphabet n m x label stack transitionPrefix
        acceptingPrefix)
      compileLabelAtomicAutomaton
      (fun _ sigma' => CompilerStackRep (maximumRank alphabet)
        (M :: stack) sigma')
      (labelAtomicAutomatonCost alphabet n m) := by
  have hloop : Spec B
      (SomewhereSymbolsInv B alphabet n m 0 stack transitionPrefix
        acceptingPrefix
        (fun symbol => decide (baseSymbol n m symbol = label) &&
          foMarked n m symbol x)
        (LabelAtomContext B n x label))
      (binarySymbolsLoop prepareLabelPredicate)
      (fun _ sigma' =>
        SomewhereSymbolsInv B alphabet n m 0 stack transitionPrefix
          acceptingPrefix
          (fun symbol => decide (baseSymbol n m symbol = label) &&
            foMarked n m symbol x)
          (LabelAtomContext B n x label) sigma' ∧
        sigma'.vars "binarySymbol" = symbolCount alphabet n m)
      (somewhereSymbolsLoopCost alphabet n m 120) := by
    simpa only [LabelSymbolsInv] using
      labelSymbolsLoop_spec B alphabet n m x label 0 stack
        transitionPrefix acceptingPrefix
  simpa only [LabelAtomicReady, compileLabelAtomicAutomaton,
      labelAtomicAutomatonCost] using
    (compileSomewhereAtomicAutomaton_spec B alphabet n m stack
      transitionPrefix acceptingPrefix
      (fun symbol => decide (baseSymbol n m symbol = label) &&
        foMarked n m symbol x)
      prepareLabelPredicate (LabelAtomContext B n x label) 120
      (labelAtomContext_begin_frame B n x label) hloop
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))

private theorem membershipAtomContext_begin_frame (B n m x X : Nat)
    {sigma sigma' : Env} {K : Nat}
    (h : MembershipAtomContext B n m x X sigma)
    (run : Run B beginBinarySomewhere sigma sigma' K) :
    MembershipAtomContext B n m x X sigma' := by
  rcases h with ⟨hn, hm, hx, hX, hxn, hXm, hnB, hmB, hxB, hXB⟩
  exact ⟨(run.frame_var "currentFO" (by decide)).trans hn,
    (run.frame_var "currentSO" (by decide)).trans hm,
    (run.frame_var "atomicLeft" (by decide)).trans hx,
    (run.frame_var "atomicSet" (by decide)).trans hX,
    hxn, hXm, hnB, hmB, hxB, hXB⟩

def MembershipAtomicReady (B : Nat) (alphabet : RankedAlphabetCode)
    (n m x X : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  SomewhereAtomicReady B alphabet n m stack transitionPrefix acceptingPrefix
    (fun symbol => foMarked n m symbol x && soMarked m symbol X)
    (MembershipAtomContext B n m x X) sigma

def membershipAtomicAutomatonCost (alphabet : RankedAlphabetCode)
    (n m : Nat) : Nat :=
  somewhereAtomicAutomatonCost alphabet n m 170

/-- Charged end-to-end construction of the membership atomic automaton from
the packed marked alphabet, again without predicate advice. -/
theorem compileMembershipAtomicAutomaton_spec (B : Nat)
    (alphabet : RankedAlphabetCode) (n m x X : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    let M := binarySomewhereCode (code alphabet n m)
      (fun symbol => foMarked n m symbol x && soMarked m symbol X)
    Spec B
      (MembershipAtomicReady B alphabet n m x X stack transitionPrefix
        acceptingPrefix)
      compileMembershipAtomicAutomaton
      (fun _ sigma' => CompilerStackRep (maximumRank alphabet)
        (M :: stack) sigma')
      (membershipAtomicAutomatonCost alphabet n m) := by
  have hloop : Spec B
      (SomewhereSymbolsInv B alphabet n m 0 stack transitionPrefix
        acceptingPrefix
        (fun symbol => foMarked n m symbol x && soMarked m symbol X)
        (MembershipAtomContext B n m x X))
      (binarySymbolsLoop prepareMembershipPredicate)
      (fun _ sigma' =>
        SomewhereSymbolsInv B alphabet n m 0 stack transitionPrefix
          acceptingPrefix
          (fun symbol => foMarked n m symbol x && soMarked m symbol X)
          (MembershipAtomContext B n m x X) sigma' ∧
        sigma'.vars "binarySymbol" = symbolCount alphabet n m)
      (somewhereSymbolsLoopCost alphabet n m 170) := by
    simpa only [MembershipSymbolsInv] using
      membershipSymbolsLoop_spec B alphabet n m x X 0 stack
        transitionPrefix acceptingPrefix
  simpa only [MembershipAtomicReady, compileMembershipAtomicAutomaton,
      membershipAtomicAutomatonCost] using
    (compileSomewhereAtomicAutomaton_spec B alphabet n m stack
      transitionPrefix acceptingPrefix
      (fun symbol => foMarked n m symbol x && soMarked m symbol X)
      prepareMembershipPredicate (MembershipAtomContext B n m x X) 170
      (membershipAtomContext_begin_frame B n m x X) hloop
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))

end Lax842588Proofs.MSORamCompilerSomewhere
