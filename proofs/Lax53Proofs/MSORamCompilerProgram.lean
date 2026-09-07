import Lax53Proofs.MSORamCompilerStorage
import Lax53Proofs.MSORamArenaProgram

/-! IMP+ fragments for the charged postorder compiler. -/

namespace Lax53Proofs.MSORamCompilerProgram

open Lax13Proofs.Imp
open Lax53Proofs.AutomatonRamProgram

private abbrev lit (n : Nat) : Expr := .lit n
private abbrev var (x : String) : Expr := .var x
private abbrev get (a : String) (i : Expr) : Expr := .get a i
private abbrev add (x y : Expr) : Expr := .add x y
private abbrev sub (x y : Expr) : Expr := .sub x y
private abbrev mul (x y : Expr) : Expr := .mul x y
private abbrev div (x y : Expr) : Expr := .div x y
private abbrev band (x y : Expr) : Expr := .and x y
private abbrev shiftl (x y : Expr) : Expr := .shiftl x y
private abbrev shiftr (x y : Expr) : Expr := .shiftr x y
private abbrev lt (x y : Expr) : Cond := .lt x y

/-- Start with empty immutable heaps and an empty automaton stack. -/
def initializeCompiler : Com := seqs [
  .assign "compilerIndex" (lit 0),
  .assign "automatonDepth" (lit 0),
  .assign "compiledTransitionWords" (lit 0),
  .assign "compiledAcceptingWords" (lit 0)]

/-- Start a new immutable automaton segment at the live heap cursors.  Its
state count has already been computed in `newStates`. -/
def beginCompiledAutomaton : Com := seqs [
  .assign "newTransitionBase" (var "compiledTransitionWords"),
  .assign "newTransitionCount" (lit 0),
  .assign "newAcceptingBase" (var "compiledAcceptingWords"),
  .assign "newAcceptingCount" (lit 0)]

/-- Append one already-computed word to the transition heap. -/
def appendTransitionWord : Com := seqs [
  .store "CompiledTransitions" (var "compiledTransitionWords")
    (var "newTransitionWord"),
  .assign "compiledTransitionWords"
    (add (var "compiledTransitionWords") (lit 1))]

/-- Append one already-computed accepting state to the accepting heap. -/
def appendAcceptingWord : Com := seqs [
  .store "CompiledAccepting" (var "compiledAcceptingWords")
    (var "newAcceptingWord"),
  .assign "compiledAcceptingWords"
    (add (var "compiledAcceptingWords") (lit 1))]

/-- Append the next cell of a fixed-width, already prepared child-state row. -/
def appendTransitionChildBody : Com := seqs [
  .store "CompiledTransitions" (var "compiledTransitionWords")
    (get "NewTransitionChildren" (var "transitionChildIndex")),
  .assign "compiledTransitionWords"
    (add (var "compiledTransitionWords") (lit 1)),
  .assign "transitionChildIndex"
    (add (var "transitionChildIndex") (lit 1))]

def appendTransitionChildrenLoop : Com :=
  .while (lt (var "transitionChildIndex") (var "transitionMaximumRank"))
    appendTransitionChildBody

/-- Append the three fixed header words of one transition and reset the child
copy counter. -/
def beginTransitionRecord : Com := seqs [
  .store "CompiledTransitions" (var "compiledTransitionWords")
    (var "newTransitionSymbol"),
  .assign "compiledTransitionWords"
    (add (var "compiledTransitionWords") (lit 1)),
  .store "CompiledTransitions" (var "compiledTransitionWords")
    (var "newTransitionParent"),
  .assign "compiledTransitionWords"
    (add (var "compiledTransitionWords") (lit 1)),
  .store "CompiledTransitions" (var "compiledTransitionWords")
    (var "newTransitionArity"),
  .assign "compiledTransitionWords"
    (add (var "compiledTransitionWords") (lit 1)),
  .assign "transitionChildIndex" (lit 0)]

def appendTransitionRecord : Com :=
  .seq beginTransitionRecord appendTransitionChildrenLoop

/-- Initialize direct arithmetic decoding of a canonical binary word.  The
word length and numeric state are already held in `binaryLength` and
`binaryState`; no table of all words is supplied to the machine. -/
def beginBinaryWord : Com := seqs [
  .assign "binaryIndex" (lit 0),
  .assign "binaryRemainder" (var "binaryState"),
  .assign "binaryDivisor"
    (shiftl (lit 1) (sub (var "binaryLength") (lit 1)))]

/-- Materialize the next most-significant binary digit and advance the
quotient/remainder decoder. -/
def binaryWordBody : Com := seqs [
  .assign "binaryDigit"
    (div (var "binaryRemainder") (var "binaryDivisor")),
  .store "NewTransitionChildren" (var "binaryIndex")
    (var "binaryDigit"),
  .assign "binaryRemainder"
    (sub (var "binaryRemainder")
      (mul (var "binaryDivisor") (var "binaryDigit"))),
  .assign "binaryDivisor" (div (var "binaryDivisor") (lit 2)),
  .assign "binaryIndex" (add (var "binaryIndex") (lit 1))]

def binaryWordLoop : Com :=
  .while (lt (var "binaryIndex") (var "binaryLength")) binaryWordBody

def prepareBinaryWord : Com := .seq beginBinaryWord binaryWordLoop

/-- Zero-fill the unused suffix of the fixed-width child buffer after the
actual binary word has been materialized. -/
def binaryPaddingBody : Com := seqs [
  .store "NewTransitionChildren" (var "binaryIndex") (lit 0),
  .assign "binaryIndex" (add (var "binaryIndex") (lit 1))]

def binaryPaddingLoop : Com :=
  .while (lt (var "binaryIndex") (var "transitionMaximumRank"))
    binaryPaddingBody

def preparePaddedBinaryWord : Com :=
  .seq prepareBinaryWord binaryPaddingLoop

/-! Generic radix child-row decoding.  Unlike the binary specialization,
the initial divisor is built by a charged multiplication loop because IMP+
has no exponentiation instruction. -/

def initializeRadixWord : Com := seqs [
  .assign "radixIndex" (lit 0),
  .assign "radixRemainder" (var "radixState"),
  .assign "radixPowerIndex" (lit 0),
  .assign "radixDivisor" (lit 1),
  .assign "radixPowerLimit"
    (sub (var "radixLength") (lit 1))]

def radixPowerBody : Com := seqs [
  .assign "radixDivisor"
    (mul (var "radixDivisor") (var "radixBase")),
  .assign "radixPowerIndex"
    (add (var "radixPowerIndex") (lit 1))]

def radixPowerLoop : Com :=
  .while (lt (var "radixPowerIndex") (var "radixPowerLimit"))
    radixPowerBody

def beginRadixWord : Com :=
  .seq initializeRadixWord radixPowerLoop

def radixWordBody : Com := seqs [
  .assign "radixDigit"
    (div (var "radixRemainder") (var "radixDivisor")),
  .store "NewTransitionChildren" (var "radixIndex")
    (var "radixDigit"),
  .assign "radixRemainder"
    (sub (var "radixRemainder")
      (mul (var "radixDivisor") (var "radixDigit"))),
  .assign "radixDivisor"
    (div (var "radixDivisor") (var "radixBase")),
  .assign "radixIndex" (add (var "radixIndex") (lit 1))]

def radixWordLoop : Com :=
  .while (lt (var "radixIndex") (var "radixLength")) radixWordBody

def prepareRadixWord : Com := .seq beginRadixWord radixWordLoop

def radixPaddingBody : Com := seqs [
  .store "NewTransitionChildren" (var "radixIndex") (lit 0),
  .assign "radixIndex" (add (var "radixIndex") (lit 1))]

def radixPaddingLoop : Com :=
  .while (lt (var "radixIndex") (var "transitionMaximumRank"))
    radixPaddingBody

def preparePaddedRadixWord : Com :=
  .seq prepareRadixWord radixPaddingLoop

/-- Materialize and pad one arbitrary-radix child row, then append the
already prepared transition header and row as one fixed-width record. -/
def appendRadixTransitionRecord : Com :=
  .seq preparePaddedRadixWord appendTransitionRecord

/-! Charged computation of the number of child rows `base ^ rank` for one
symbol. -/

def initializeRadixRows : Com := seqs [
  .assign "radixState" (lit 0),
  .assign "radixRowLimit" (lit 1),
  .assign "radixRowPowerIndex" (lit 0)]

def radixRowPowerBody : Com := seqs [
  .assign "radixRowLimit"
    (mul (var "radixRowLimit") (var "radixBase")),
  .assign "radixRowPowerIndex"
    (add (var "radixRowPowerIndex") (lit 1))]

def radixRowPowerLoop : Com :=
  .while (lt (var "radixRowPowerIndex") (var "radixLength"))
    radixRowPowerBody

def beginRadixRows : Com :=
  .seq initializeRadixRows radixRowPowerLoop

/-- Prepare the three semantic header registers for the current binary row.
The row has parent state `1` precisely when the predicate already holds at
the symbol or the numeric child-row index is nonzero. -/
def prepareBinaryTransitionHeader : Com := seqs [
  .assign "newTransitionSymbol" (var "binarySymbol"),
  .ite (.eq (var "binaryState") (lit 0))
    (.assign "newTransitionParent" (var "binaryPredicate"))
    (.assign "newTransitionParent" (lit 1)),
  .assign "newTransitionArity" (var "binaryLength")]

/-- Materialize and pad one binary child row, then append the corresponding
fixed-width transition record whose header registers are already prepared. -/
def appendBinaryTransitionRecord : Com :=
  .seq preparePaddedBinaryWord appendTransitionRecord

/-- Append one generated binary transition and account for the new semantic
record in the descriptor currently under construction. -/
def appendCountedBinaryTransitionRecord : Com :=
  .seq appendBinaryTransitionRecord
    (.assign "newTransitionCount"
      (add (var "newTransitionCount") (lit 1)))

/-- Generate, append, count, and advance past the current binary row. -/
def binaryRowsBody : Com :=
  .seq (.seq prepareBinaryTransitionHeader
      appendCountedBinaryTransitionRecord)
    (.assign "binaryState" (add (var "binaryState") (lit 1)))

def binaryRowsLoop : Com :=
  .while (lt (var "binaryState") (var "binaryRowLimit")) binaryRowsBody

/-- Initialize the row counter and its exponential bound for the current
symbol. The shift is part of the charged execution. -/
def beginBinaryRows : Com := seqs [
  .assign "binaryState" (lit 0),
  .assign "binaryRowLimit" (shiftl (lit 1) (var "binaryLength"))]

def compileBinarySymbol : Com :=
  .seq beginBinaryRows binaryRowsLoop

/-- Recover the underlying alphabet symbol of the current packed marked
symbol and load its rank from the structurally decoded alphabet prefix.
`soMarkerWords` and `foMarkerWords` are powers of two computed by the charged
occurrence loader. -/
def prepareBinarySymbolRank : Com := seqs [
  .assign "binaryBaseSymbol"
    (div (div (var "binarySymbol") (var "soMarkerWords"))
      (var "foMarkerWords")),
  .assign "binaryLength"
    (get "P" (add (var "binaryBaseSymbol") (lit 1)))]

/-- Advance the packed-symbol counter after every row for the current symbol
has been emitted. -/
def advanceBinarySymbol : Com :=
  .assign "binarySymbol" (add (var "binarySymbol") (lit 1))

/-- Shared body of the structural marked-alphabet traversal.  The supplied
fragment computes the formula-specific predicate bit from the current packed
symbol.  It is fixed as part of the overall compiler program; it is not input
data or an advice table. -/
def binarySymbolsBody (preparePredicate : Com) : Com :=
  .seq (.seq (.seq prepareBinarySymbolRank preparePredicate)
      compileBinarySymbol)
    advanceBinarySymbol

def binarySymbolsLoop (preparePredicate : Com) : Com :=
  .while (lt (var "binarySymbol") (var "markedSymbols"))
    (binarySymbolsBody preparePredicate)

/-- Append the sole accepting state of a two-state "somewhere" automaton and
finish the descriptor count. -/
def finishBinarySomewhere : Com :=
  .seq (.seq (.assign "newAcceptingWord" (lit 1)) appendAcceptingWord)
    (.assign "newAcceptingCount" (lit 1))

/-- Open a fresh two-state segment and start its packed-symbol counter. -/
def beginBinarySomewhere : Com :=
  .seq (.seq (.assign "newStates" (lit 2)) beginCompiledAutomaton)
    (.assign "binarySymbol" (lit 0))

/-- Extract the packed first-order marker word for the current marked
symbol. -/
def prepareFOMarkerState : Com :=
  .assign "foMarkerState"
    (band (div (var "binarySymbol") (var "soMarkerWords"))
      (sub (var "foMarkerWords") (lit 1)))

/-- Extract the packed second-order marker word for the current marked
symbol. -/
def prepareSOMarkerState : Com :=
  .assign "soMarkerState"
    (band (var "binarySymbol")
      (sub (var "soMarkerWords") (lit 1)))

/-- Read one bit of the packed first-order marker word.  `markerIndex` and
`markerLength` are registers selected by the surrounding atomic-constructor
branch. -/
def prepareFOMarkerBit : Com :=
  .assign "markerBit"
    (band
      (shiftr (var "foMarkerState")
        (sub (sub (var "markerLength") (var "markerIndex")) (lit 1)))
      (lit 1))

/-- Read one bit of the packed second-order marker word. -/
def prepareSOMarkerBit : Com :=
  .assign "markerBit"
    (band
      (shiftr (var "soMarkerState")
        (sub (sub (var "markerLength") (var "markerIndex")) (lit 1)))
      (lit 1))

/-- Predicate preparation for equality of the two first-order variables
loaded in `atomicLeft` and `atomicRight`. -/
def prepareEqualPredicate : Com := seqs [
  prepareFOMarkerState,
  .assign "markerLength" (var "currentFO"),
  .assign "markerIndex" (var "atomicLeft"),
  prepareFOMarkerBit,
  .assign "atomicLeftBit" (var "markerBit"),
  .assign "markerIndex" (var "atomicRight"),
  prepareFOMarkerBit,
  .assign "binaryPredicate"
    (band (var "atomicLeftBit") (var "markerBit"))]

/-- Predicate preparation for a label atom: the base symbol must be the
loaded label and the selected first-order marker must be present. -/
def prepareLabelPredicate : Com := seqs [
  prepareFOMarkerState,
  .assign "markerLength" (var "currentFO"),
  .assign "markerIndex" (var "atomicLeft"),
  prepareFOMarkerBit,
  .ite (.eq (var "binaryBaseSymbol") (var "atomicLabel"))
    (.assign "binaryPredicate" (var "markerBit"))
    (.assign "binaryPredicate" (lit 0))]

/-- Predicate preparation for membership of the selected first-order node in
the selected second-order set. -/
def prepareMembershipPredicate : Com := seqs [
  prepareFOMarkerState,
  .assign "markerLength" (var "currentFO"),
  .assign "markerIndex" (var "atomicLeft"),
  prepareFOMarkerBit,
  .assign "atomicLeftBit" (var "markerBit"),
  prepareSOMarkerState,
  .assign "markerLength" (var "currentSO"),
  .assign "markerIndex" (var "atomicSet"),
  prepareSOMarkerBit,
  .assign "binaryPredicate"
    (band (var "atomicLeftBit") (var "markerBit"))]

/-- Load one verified postorder occurrence and compute the size of its marked
alphabet.  Powers of two are word-RAM shifts, so this arithmetic is charged
inside the same run rather than performed by Lean preprocessing. -/
def loadCompilerOccurrence : Com := seqs [
  .assign "currentFormula"
    (get "FormulaOrder" (var "compilerIndex")),
  .assign "currentFO"
    (get "FormulaFOOrder" (var "compilerIndex")),
  .assign "currentSO"
    (get "FormulaSOOrder" (var "compilerIndex")),
  .assign "formulaNameRoot"
    (get "Arena" (add (var "currentFormula") (lit 1))),
  .assign "formulaTag"
    (get "Arena" (add (var "formulaNameRoot") (lit 1))),
  .assign "foMarkerWords" (shiftl (lit 1) (var "currentFO")),
  .assign "soMarkerWords" (shiftl (lit 1) (var "currentSO")),
  .assign "markedSymbols"
    (mul (mul (var "A") (var "foMarkerWords"))
      (var "soMarkerWords")),
  .assign "compilerIndex" (add (var "compilerIndex") (lit 1))]

/-- Push the descriptor whose five components have been prepared in scalar
registers.  The pointed-to heap segments are immutable and are not copied. -/
def pushAutomatonDescriptor : Com := seqs [
  .store "AutomatonStatesStack" (var "automatonDepth")
    (var "newStates"),
  .store "AutomatonTransitionBaseStack" (var "automatonDepth")
    (var "newTransitionBase"),
  .store "AutomatonTransitionCountStack" (var "automatonDepth")
    (var "newTransitionCount"),
  .store "AutomatonAcceptingBaseStack" (var "automatonDepth")
    (var "newAcceptingBase"),
  .store "AutomatonAcceptingCountStack" (var "automatonDepth")
    (var "newAcceptingCount"),
  .assign "automatonDepth" (add (var "automatonDepth") (lit 1))]

def finishAndPushBinarySomewhere : Com :=
  .seq finishBinarySomewhere pushAutomatonDescriptor

def compileSomewhereAtomicAutomaton (preparePredicate : Com) : Com :=
  .seq (.seq beginBinarySomewhere
      (binarySymbolsLoop preparePredicate))
    finishAndPushBinarySomewhere

def compileEqualAtomicAutomaton : Com :=
  compileSomewhereAtomicAutomaton prepareEqualPredicate

def compileLabelAtomicAutomaton : Com :=
  compileSomewhereAtomicAutomaton prepareLabelPredicate

def compileMembershipAtomicAutomaton : Com :=
  compileSomewhereAtomicAutomaton prepareMembershipPredicate

/-- Descriptor for the one-state automaton with no transitions and no
accepting states.  Empty segments begin at the current heap cursors. -/
def prepareEmptyAutomatonDescriptor : Com := seqs [
  .assign "newStates" (lit 1),
  .assign "newTransitionBase" (var "compiledTransitionWords"),
  .assign "newTransitionCount" (lit 0),
  .assign "newAcceptingBase" (var "compiledAcceptingWords"),
  .assign "newAcceptingCount" (lit 0)]

def pushEmptyAutomaton : Com :=
  .seq prepareEmptyAutomatonDescriptor pushAutomatonDescriptor

/-- Load and remove the logical top descriptor.  The immutable automaton heap
segments and the physical descriptor cells remain untouched. -/
def popAutomatonDescriptor : Com := seqs [
  .assign "poppedAutomatonIndex" (sub (var "automatonDepth") (lit 1)),
  .assign "poppedStates"
    (get "AutomatonStatesStack" (var "poppedAutomatonIndex")),
  .assign "poppedTransitionBase"
    (get "AutomatonTransitionBaseStack" (var "poppedAutomatonIndex")),
  .assign "poppedTransitionCount"
    (get "AutomatonTransitionCountStack" (var "poppedAutomatonIndex")),
  .assign "poppedAcceptingBase"
    (get "AutomatonAcceptingBaseStack" (var "poppedAutomatonIndex")),
  .assign "poppedAcceptingCount"
    (get "AutomatonAcceptingCountStack" (var "poppedAutomatonIndex")),
  .assign "automatonDepth" (var "poppedAutomatonIndex")]

end Lax53Proofs.MSORamCompilerProgram
