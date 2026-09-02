import Lax53.EffectiveTranslations

/-!
---
title: Word encodings for model checking on ranked trees
type: definition
---

For algorithmic model checking, a ranked tree over an encoded alphabet is
written in postorder, using one natural-number token per node: all children
occur before their parent, and a node is represented by the number of its
symbol. Since the alphabet code prescribes every symbol's rank, this word
determines the tree uniquely whenever it is well formed. Its length is exactly
the number of nodes of the tree.

For the word-RAM theorem, an automaton is laid out as a table with fixed-width
transition records, and both that table and the tree word are put in
self-delimiting blocks. This specialized natural-word layout is a refinement
of the neutral constructor-structural baseline supplied by `lax-58`: its field
positions are exposed because constant-time random access is part of the
algorithm and its complexity proof. It is not the generic representation of
ranked trees or formulas.
-/

namespace Lax53.TreeModelCheckingEncoding

open Lax53.RankedTree
open Lax53.EffectiveTranslations

/-- Prefix a word by its length. -/
def block (x : CodeString) : CodeString := x.length :: x

/-- The largest rank appearing in an encoded alphabet. -/
def maximumRank (alphabet : RankedAlphabetCode) : Nat :=
  alphabet.foldl max 0

/-- Pad a transition's child-state word to the alphabet's maximum rank. The
original length remains in the record, so malformed transitions retain their
semantics (they never match a symbol of a different rank). -/
def encodeTransitionFixed (maximumRank : Nat)
    (tr : TransitionCode) : CodeString :=
  tr.1 :: tr.2.1 :: tr.2.2.length ::
    (List.range maximumRank).map fun i => tr.2.2.getD i 0

/-- Lay out an encoded alphabet together with an automaton body. Transitions
use fixed-width records of `maximumRank + 3` words. This representation is
equivalent to the ordinary variable-width transition lists, but permits
constant-time field addressing in the word-RAM evaluator. -/
def encodeAutomaton (input : EncodedAutomaton) : CodeString :=
  let maximumRank := maximumRank input.1
  input.1.length :: input.1 ++
    [input.2.1, input.2.2.1.length, maximumRank] ++
    input.2.2.1.flatMap (encodeTransitionFixed maximumRank) ++
    block input.2.2.2

/-- The postorder word of a ranked tree. There is exactly one output token
per node. -/
def encodeTree (alphabet : RankedAlphabetCode) :
    Tree alphabet.toRankedAlphabet → CodeString
  | .node a children =>
      (List.ofFn (fun i => encodeTree alphabet (children i))).flatten ++ [a.val]

/-- The size of a ranked tree is its number of nodes, equivalently the length
of its postorder encoding. -/
def treeSize {alphabet : RankedAlphabetCode}
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  (encodeTree alphabet t).length

/-- Put self-delimiting parameter and postorder-tree blocks next to each
other. The tree-length word is necessary because exhaustion of the input tape
halts the archive's word RAM rather than returning an end-of-input value. -/
def modelCheckingInput (parameter tree : CodeString) : CodeString :=
  block parameter ++ block tree

/-- The physical word supplied for automaton model checking. -/
def automatonInput (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : CodeString :=
  modelCheckingInput (encodeAutomaton M) (encodeTree M.1 t)

end Lax53.TreeModelCheckingEncoding
