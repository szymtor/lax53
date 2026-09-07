import Lax53Proofs.AutomatonRamProgram

/-!
Concrete proof-only front end from the distinguished Lax-58 arena to the
working arrays consumed by the verified sparse evaluator.

The public Lax-53 concepts expose none of this layout. Every command below is
part of the single measured Lax-13 execution.
-/

namespace Lax53Proofs.AutomatonRamArenaProgram

open Lax13.Ram
open Lax13Proofs.Imp
open Lax13Proofs.Compile
open Lax53Proofs.ArrayInput
open Lax53Proofs.AutomatonRamProgram

private abbrev lit (n : Nat) : Expr := .lit n
private abbrev var (x : String) : Expr := .var x
private abbrev get (a : String) (i : Expr) : Expr := .get a i
private abbrev add (x y : Expr) : Expr := .add x y
private abbrev sub (x y : Expr) : Expr := .sub x y
private abbrev mul (x y : Expr) : Expr := .mul x y
private abbrev eq (x y : Expr) : Cond := .eq x y
private abbrev lt (x y : Expr) : Cond := .lt x y
private abbrev inc (x : String) : Com := .assign x (add (var x) (lit 1))

/-- Read the root word, infer the dense arena length from the fact that the
root is its final block, and copy the arena words into scratch memory. -/
def readArena : Com := seqs [
  .read "root",
  .assign "arenaLen" (add (var "root") (lit 3)),
  readArr "Arena" "arenaRead" "arenaLen" "arenaValue"]

/-- Follow the fixed top-level constructor and its two-field spine. -/
def openInstance : Com := seqs [
  .assign "instanceFields" (get "Arena" (add (var "root") (lit 2))),
  .assign "automatonRoot"
    (get "Arena" (add (var "instanceFields") (lit 1))),
  .assign "treeFieldTail"
    (get "Arena" (add (var "instanceFields") (lit 2))),
  .assign "treeRoot"
    (get "Arena" (add (var "treeFieldTail") (lit 1))),
  .assign "alphabetCursor"
    (get "Arena" (add (var "automatonRoot") (lit 1))),
  .assign "bodyRoot"
    (get "Arena" (add (var "automatonRoot") (lit 2)))]

/-- Decode one cons cell of the structurally represented ranked alphabet. -/
def alphabetBody : Com := seqs [
  .assign "valueRoot"
    (get "Arena" (add (var "alphabetCursor") (lit 1))),
  .assign "rank" (get "Arena" (add (var "valueRoot") (lit 1))),
  .store "P" (add (var "A") (lit 1)) (var "rank"),
  .ite (lt (var "R") (var "rank"))
    (.assign "R" (var "rank")) .skip,
  .assign "alphabetCursor"
    (get "Arena" (add (var "alphabetCursor") (lit 2))),
  inc "A"]

def alphabetCondition : Cond :=
  eq (get "Arena" (var "alphabetCursor")) (lit 1)

def alphabetLoop : Com := .while alphabetCondition alphabetBody

/-- Decode the alphabet and initialize the fixed-width table header. -/
def readAlphabet : Com := seqs [
  .assign "A" (lit 0),
  .assign "R" (lit 0),
  alphabetLoop,
  .store "P" (lit 0) (var "A"),
  .assign "width" (add (var "R") (lit 3)),
  .assign "records" (add (var "A") (lit 4))]

/-- Decode the non-list part of the automaton body and locate its two lists. -/
def openAutomatonBody : Com := seqs [
  .assign "valueRoot" (get "Arena" (add (var "bodyRoot") (lit 1))),
  .assign "Q" (get "Arena" (add (var "valueRoot") (lit 1))),
  .assign "bodyTail" (get "Arena" (add (var "bodyRoot") (lit 2))),
  .assign "transitionCursor"
    (get "Arena" (add (var "bodyTail") (lit 1))),
  .assign "acceptCursor"
    (get "Arena" (add (var "bodyTail") (lit 2))),
  .store "P" (add (var "A") (lit 1)) (var "Q")]

/-- Decode one child-state cons cell. Only the first `R` child states are
stored, exactly matching the old fixed-width padding/truncation convention;
the full list length is still counted in `arity`. -/
def transitionChildBody : Com := seqs [
  .assign "valueRoot"
    (get "Arena" (add (var "childCursor") (lit 1))),
  .assign "childState" (get "Arena" (add (var "valueRoot") (lit 1))),
  .ite (lt (var "arity") (var "R"))
    (.store "P" (add (add (var "transitionBase") (lit 3)) (var "arity"))
      (var "childState")) .skip,
  .assign "childCursor"
    (get "Arena" (add (var "childCursor") (lit 2))),
  inc "arity"]

def transitionChildLoop : Com :=
  .while (eq (get "Arena" (var "childCursor")) (lit 1)) transitionChildBody

/-- Materialize the `getD` zero padding used by the evaluator's fixed-width
record convention. This makes each record independent of the prior contents
of the scratch array. -/
def transitionPaddingBody : Com := seqs [
  .store "P" (add (add (var "transitionBase") (lit 3)) (var "padding"))
    (lit 0),
  inc "padding"]

def transitionPaddingLoop : Com :=
  .while (lt (var "padding") (var "R")) transitionPaddingBody

/-- Open one represented transition and materialize its symbol and parent
fields. Child scanning and finalization are separate verified phases. -/
def openTransition : Com := seqs [
  .assign "transitionRoot"
    (get "Arena" (add (var "transitionCursor") (lit 1))),
  .assign "valueRoot"
    (get "Arena" (add (var "transitionRoot") (lit 1))),
  .assign "transitionSymbol"
    (get "Arena" (add (var "valueRoot") (lit 1))),
  .assign "transitionTail"
    (get "Arena" (add (var "transitionRoot") (lit 2))),
  .assign "valueRoot"
    (get "Arena" (add (var "transitionTail") (lit 1))),
  .assign "transitionParent"
    (get "Arena" (add (var "valueRoot") (lit 1))),
  .assign "childCursor"
    (get "Arena" (add (var "transitionTail") (lit 2))),
  .assign "transitionBase"
    (add (var "records") (mul (var "T") (var "width"))),
  .store "P" (var "transitionBase") (var "transitionSymbol"),
  .store "P" (add (var "transitionBase") (lit 1)) (var "transitionParent"),
  .assign "arity" (lit 0)]

/-- Finish one transition record and advance the represented transition-list
cursor. -/
def finishTransition : Com := seqs [
  .store "P" (add (var "transitionBase") (lit 2)) (var "arity"),
  .assign "transitionCursor"
    (get "Arena" (add (var "transitionCursor") (lit 2))),
  inc "T"]

/-- Scan and pad the children of an already opened transition. -/
def processTransitionChildren : Com := seqs [
  transitionChildLoop,
  .assign "padding" (var "arity"),
  transitionPaddingLoop]

/-- Decode one transition and append its fixed-width record to `P`. -/
def transitionBody : Com := seqs [
  openTransition,
  processTransitionChildren,
  finishTransition]

def transitionLoop : Com :=
  .while (eq (get "Arena" (var "transitionCursor")) (lit 1)) transitionBody

/-- Decode every transition and finish the table header. -/
def readTransitions : Com := seqs [
  .assign "T" (lit 0),
  transitionLoop,
  .store "P" (add (var "A") (lit 2)) (var "T"),
  .store "P" (add (var "A") (lit 3)) (var "R"),
  .assign "acceptBase"
    (add (var "records") (mul (var "T") (var "width")))]

/-- Decode one accepting-state cons cell. -/
def acceptingBody : Com := seqs [
  .assign "valueRoot" (get "Arena" (add (var "acceptCursor") (lit 1))),
  .assign "acceptState" (get "Arena" (add (var "valueRoot") (lit 1))),
  .store "P" (add (add (var "acceptBase") (lit 1)) (var "F"))
    (var "acceptState"),
  .assign "acceptCursor" (get "Arena" (add (var "acceptCursor") (lit 2))),
  inc "F"]

def acceptingLoop : Com :=
  .while (eq (get "Arena" (var "acceptCursor")) (lit 1)) acceptingBody

/-- Decode the accepting list and finish the working automaton table. -/
def readAccepting : Com := seqs [
  .assign "F" (lit 0),
  acceptingLoop,
  .store "P" (var "acceptBase") (var "F")]

/-- Open one ranked-tree node at the current traversal-stack depth. -/
def pushTreeNode : Com := seqs [
  .assign "treeFields" (get "Arena" (add (var "currentTree") (lit 2))),
  .assign "valueRoot" (get "Arena" (add (var "treeFields") (lit 1))),
  .assign "treeSymbol" (get "Arena" (add (var "valueRoot") (lit 1))),
  .assign "childCursor" (get "Arena" (add (var "treeFields") (lit 2))),
  .store "TreeSymbolStack" (var "treeDepth") (var "treeSymbol"),
  .store "TreeTailStack" (var "treeDepth") (var "childCursor"),
  inc "treeDepth"]

/-- Finish the current node after all children have been traversed. -/
def finishTreeNode : Com := seqs [
  .assign "treeSymbol" (get "TreeSymbolStack" (var "treeIndex")),
  .store "W" (var "n") (var "treeSymbol"),
  inc "n",
  .assign "treeDepth" (var "treeIndex")]

/-- Advance to the next child and push it onto the explicit DFS stack. -/
def descendTreeNode : Com := seqs [
  .assign "currentTree" (get "Arena" (add (var "childCursor") (lit 1))),
  .assign "nextChildTail" (get "Arena" (add (var "childCursor") (lit 2))),
  .store "TreeTailStack" (var "treeIndex") (var "nextChildTail"),
  pushTreeNode]

def treeTraversalBody : Com := seqs [
  .assign "treeIndex" (sub (var "treeDepth") (lit 1)),
  .assign "childCursor" (get "TreeTailStack" (var "treeIndex")),
  .assign "arenaTag" (get "Arena" (var "childCursor")),
  .ite (eq (var "arenaTag") (lit 0)) finishTreeNode descendTreeNode]

def treeTraversalLoop : Com :=
  .while (lt (lit 0) (var "treeDepth")) treeTraversalBody

/-- Initialize the explicit traversal stack with the represented root. -/
def initializeTreeTraversal : Com :=
  .seq (.assign "n" (lit 0))
    (.seq (.assign "treeDepth" (lit 0))
      (.seq (.assign "currentTree" (var "treeRoot")) pushTreeNode))

/-- Produce the old evaluator's postorder symbol word in `W`. -/
def readTree : Com :=
  .seq initializeTreeTraversal (.seq treeTraversalLoop .skip)

/-- Entire charged structural front end. -/
def prepare : Com := seqs [readArena, openInstance, readAlphabet,
  openAutomatonBody, readTransitions, readAccepting, readTree]

/-- Uniform evaluator on the distinguished structural input. -/
def evaluator : Com := seqs [prepare,
  AutomatonRamProgram.evaluateTree,
  AutomatonRamProgram.scanAccepting]

/-- All storage used by the structural front end and evaluator. -/
def layout : Layout where
  scalars := AutomatonRamProgram.layout.scalars ++ [
    "root", "arenaLen", "arenaRead", "arenaValue", "instanceFields",
    "automatonRoot", "treeFieldTail", "treeRoot", "alphabetCursor",
    "bodyRoot", "valueRoot", "rank", "bodyTail", "transitionCursor",
    "acceptCursor", "transitionRoot", "transitionTail", "transitionSymbol",
    "transitionParent", "childCursor", "childState", "transitionBase",
    "padding",
    "treeFields", "treeSymbol", "treeDepth", "treeIndex", "currentTree",
    "nextChildTail", "arenaTag"]
  arrays := ["Arena", "P", "W", "TreeSymbolStack", "TreeTailStack",
    "S", "L", "O"]
  temps := 8

def program : Program := compileProgram layout evaluator

theorem evaluator_ok : Com.Ok layout evaluator := by
  simp [evaluator, prepare, readArena, openInstance, readAlphabet,
    alphabetLoop, alphabetCondition, alphabetBody, openAutomatonBody, readTransitions,
    transitionLoop, transitionBody, openTransition, processTransitionChildren,
    finishTransition,
    transitionChildLoop, transitionChildBody,
    transitionPaddingLoop, transitionPaddingBody,
    readAccepting, acceptingLoop, acceptingBody, readTree,
    initializeTreeTraversal, pushTreeNode,
    treeTraversalLoop, treeTraversalBody, finishTreeNode, descendTreeNode,
    AutomatonRamProgram.evaluateTree, AutomatonRamProgram.evaluateTreeLoop,
    AutomatonRamProgram.evaluateTreeBody,
    AutomatonRamProgram.scanAccepting,
    AutomatonRamProgram.scanAcceptingOuterLoop,
    AutomatonRamProgram.scanAcceptingOuterBody,
    AutomatonRamProgram.scanAcceptingInnerLoop,
    AutomatonRamProgram.scanAcceptingInnerBody,
    AutomatonRamProgram.scanTransitions,
    AutomatonRamProgram.scanTransitionsLoop,
    AutomatonRamProgram.scanTransitionsBody,
    AutomatonRamProgram.installParent,
    AutomatonRamProgram.installParentLoop,
    AutomatonRamProgram.installParentBody,
    AutomatonRamProgram.checkTransition,
    AutomatonRamProgram.loadTransition,
    AutomatonRamProgram.validateTransition,
    AutomatonRamProgram.appendParent,
    AutomatonRamProgram.checkChildren,
    AutomatonRamProgram.checkChildrenLoop,
    AutomatonRamProgram.checkChildrenBody,
    AutomatonRamProgram.searchChild,
    AutomatonRamProgram.searchStateLoop,
    AutomatonRamProgram.searchStateBody,
    readArr, Lax13Proofs.Reasoning.Lib.Fill.put,
    AutomatonRamProgram.seqs, seqs, inc, layout, AutomatonRamProgram.layout,
    Com.Ok, Cond.Ok, Expr.Ok, condExpr]

end Lax53Proofs.AutomatonRamArenaProgram
