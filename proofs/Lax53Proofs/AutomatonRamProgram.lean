import Lax13Proofs.Transfer
import Lax53Proofs.ArrayInput
import Lax53Proofs.EncodedAutomatonWordEvaluation

namespace Lax53Proofs.AutomatonRamProgram

open Lax13.Ram
open Lax13Proofs.Imp
open Lax13Proofs.Compile
open Lax53Proofs.ArrayInput

/-- Right-associated sequencing, used only to keep the concrete evaluator
readable. -/
def seqs : List Com → Com
  | [] => .skip
  | c :: cs => .seq c (seqs cs)

private abbrev lit (n : Nat) : Expr := .lit n
private abbrev var (x : String) : Expr := .var x
private abbrev get (a : String) (i : Expr) : Expr := .get a i
private abbrev add (x y : Expr) : Expr := .add x y
private abbrev sub (x y : Expr) : Expr := .sub x y
private abbrev mul (x y : Expr) : Expr := .mul x y
private abbrev eq (x y : Expr) : Cond := .eq x y
private abbrev lt (x y : Expr) : Cond := .lt x y

private abbrev inc (x : String) : Com := .assign x (add (var x) (lit 1))

/-- Copy the length-prefixed parameter block into random-access storage. -/
def readParameter : Com :=
  .seq (.read "plen") (readArr "P" "i" "plen" "v")

/-- Recover the fixed-width automaton-table header from `P` and read the
length of the following tree block. -/
def readHeader : Com := seqs [
  .assign "A" (get "P" (lit 0)),
  .assign "Q" (get "P" (add (var "A") (lit 1))),
  .assign "T" (get "P" (add (var "A") (lit 2))),
  .assign "R" (get "P" (add (var "A") (lit 3))),
  .assign "width" (add (var "R") (lit 3)),
  .assign "records" (add (var "A") (lit 4)),
  .assign "acceptBase"
    (add (var "records") (mul (var "T") (var "width"))),
  .assign "F" (get "P" (var "acceptBase")),
  .read "n"]

/-- Copy the postorder symbol word into random-access storage. This remains
part of the proof-only legacy framing; the structural-arena front end below
will populate the same array directly. -/
def readTreeWord : Com := readArr "W" "wi" "n" "wv"

/-- Search the reachable-state list of the current `j`-th child for the
transition state `cq`. -/
def searchStateBody : Com := seqs [
  .assign "addr" (add (mul (var "childRow") (var "T")) (var "z")),
  .assign "state" (get "S" (var "addr")),
  .ite (eq (var "state") (var "cq"))
    (.assign "found" (lit 1)) .skip,
  inc "z"]

def searchStateLoop : Com :=
  .while (lt (var "z") (var "childLen")) searchStateBody

def searchChild : Com := seqs [
  .assign "cq" (get "P" (add (add (var "base") (lit 3)) (var "j"))),
  .assign "childRow" (add (sub (var "depth") (var "k")) (var "j")),
  .assign "childLen" (get "L" (var "childRow")),
  .assign "z" (lit 0),
  .assign "found" (lit 0),
  searchStateLoop,
  .ite (eq (var "found") (lit 0))
    (.assign "valid" (lit 0)) .skip]

/-- Check the ordered child states of one transition. -/
def checkChildrenBody : Com := seqs [
  .ite (eq (var "valid") (lit 1)) searchChild .skip,
  inc "j"]

def checkChildrenLoop : Com :=
  .while (lt (var "j") (var "k")) checkChildrenBody

def checkChildren : Com := seqs [
  .assign "j" (lit 0),
  checkChildrenLoop]

/-- Load one fixed-width transition record and initialize its validity flag. -/
def loadTransition : Com := seqs [
  .assign "base"
    (add (var "records") (mul (var "tr") (var "width"))),
  .assign "tsym" (get "P" (var "base")),
  .assign "parent" (get "P" (add (var "base") (lit 1))),
  .assign "arity" (get "P" (add (var "base") (lit 2))),
  .assign "valid" (lit 1)]

/-- Check the non-recursive fields of the loaded transition record. -/
def validateTransition : Com := seqs [
  .ite (eq (var "tsym") (var "sym")) .skip
    (.assign "valid" (lit 0)),
  .ite (lt (var "parent") (var "Q")) .skip
    (.assign "valid" (lit 0)),
  .ite (eq (var "arity") (var "k")) .skip
    (.assign "valid" (lit 0))]

/-- Append the loaded parent state exactly when the record remains valid. -/
def appendParent : Com :=
  .ite (eq (var "valid") (lit 1)) (seqs [
    .store "O" (var "scratchLen") (var "parent"),
    inc "scratchLen"]) .skip

/-- Check the symbol, parent bound, arity, and child states of one fixed-width
transition record. A matching parent state is appended to the scratch row. -/
def checkTransition : Com := seqs [
  loadTransition,
  validateTransition,
  checkChildren,
  appendParent]

/-- Scan every transition for the current node. -/
def scanTransitionsBody : Com := seqs [checkTransition, inc "tr"]

def scanTransitionsLoop : Com :=
  .while (lt (var "tr") (var "T")) scanTransitionsBody

def scanTransitions : Com := seqs [
  .assign "scratchLen" (lit 0),
  .assign "tr" (lit 0),
  scanTransitionsLoop]

/-- Move the scratch reachable-state list into the stack row replacing the
ordered children. -/
def installParentBody : Com := seqs [
  .assign "dst" (add (mul (var "target") (var "T")) (var "z")),
  .assign "state" (get "O" (var "z")),
  .store "S" (var "dst") (var "state"),
  inc "z"]

def installParentLoop : Com :=
  .while (lt (var "z") (var "scratchLen")) installParentBody

def installParent : Com := seqs [
  .assign "target" (sub (var "depth") (var "k")),
  .assign "z" (lit 0),
  installParentLoop,
  .store "L" (var "target") (var "scratchLen"),
  .assign "depth" (add (var "target") (lit 1))]

/-- Process all `n` symbols of the postorder tree block. -/
def evaluateTreeBody : Com := seqs [
  .assign "sym" (get "W" (var "node")),
  .assign "k" (get "P" (add (var "sym") (lit 1))),
  scanTransitions,
  installParent,
  inc "node"]

def evaluateTreeLoop : Com :=
  .while (lt (var "node") (var "n")) evaluateTreeBody

def evaluateTree : Com := seqs [
  .assign "node" (lit 0),
  .assign "depth" (lit 0),
  evaluateTreeLoop]

/-- Test whether a state in stack row zero occurs in the accepting-state
block of the encoded automaton. -/
def scanAcceptingInnerBody : Com := seqs [
  .assign "acceptState"
    (get "P" (add (add (var "acceptBase") (lit 1)) (var "f"))),
  .ite (eq (var "state") (var "acceptState"))
    (.assign "answer" (lit 1)) .skip,
  inc "f"]

def scanAcceptingInnerLoop : Com :=
  .while (lt (var "f") (var "F")) scanAcceptingInnerBody

def scanAcceptingOuterBody : Com := seqs [
  .assign "state" (get "S" (var "z")),
  .assign "f" (lit 0),
  scanAcceptingInnerLoop,
  inc "z"]

def scanAcceptingOuterLoop : Com :=
  .while (lt (var "z") (var "rootLen")) scanAcceptingOuterBody

def scanAccepting : Com := seqs [
  .assign "answer" (lit 0),
  .assign "rootLen" (get "L" (lit 0)),
  .assign "z" (lit 0),
  scanAcceptingOuterLoop,
  .write (var "answer")]

/-- Uniform IMP+ implementation of sparse bottom-up evaluation. -/
def evaluator : Com := seqs [readParameter, readHeader, readTreeWord,
  evaluateTree, scanAccepting]

/-- The evaluator uses one parameter array, one reachable-state array, and one
stack-row-length array. -/
def layout : Layout where
  scalars := ["plen", "i", "v", "A", "Q", "T", "R", "width", "records",
    "acceptBase", "F", "n", "node", "depth", "sym", "k", "scratchLen", "tr",
    "base", "tsym", "parent", "arity", "valid", "j", "cq", "childRow",
    "childLen", "z", "found", "addr", "state", "target", "src", "dst",
    "answer", "rootLen", "f", "acceptState", "wi", "wv"]
  arrays := ["P", "W", "S", "L", "O"]
  temps := 8

/-- The concrete uniform word-RAM program. -/
def program : Program := compileProgram layout evaluator

theorem evaluator_ok : Com.Ok layout evaluator := by
  simp [evaluator, readParameter, readHeader, readTreeWord, evaluateTree, scanAccepting,
    evaluateTreeLoop, evaluateTreeBody, scanAcceptingOuterLoop,
    scanAcceptingOuterBody, scanAcceptingInnerLoop, scanAcceptingInnerBody,
    scanTransitions, scanTransitionsLoop, scanTransitionsBody,
    installParent, installParentLoop, installParentBody,
    checkTransition, loadTransition, validateTransition, appendParent,
    checkChildren, checkChildrenLoop, checkChildrenBody,
    searchChild, searchStateLoop, searchStateBody,
    readArr, Lax13Proofs.Reasoning.Lib.Fill.put, seqs, inc, layout, Com.Ok,
    Cond.Ok, Expr.Ok, condExpr]

end Lax53Proofs.AutomatonRamProgram
