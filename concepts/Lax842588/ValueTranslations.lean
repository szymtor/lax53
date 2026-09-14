import Lax146103.MSOSyntax
import Lax842588.RankedTree
import Lax842588.TreeStructure
import Lax842588.TreeAutomaton

/-!
---
title: Value-level translations between MSO and tree automata
type: theorem
---

A finite ranked alphabet is described by the finite list of its symbol ranks;
symbols are numbered by their positions in that list. Automata use finite
lists of numbered transitions, while MSO formulas are represented directly by
their inductive syntax.

There are mathematical translations between finite automaton values and the
intrinsically scoped MSO sentences of `lax-52`. The ranked alphabet is an
explicit parameter shared by source and target, so preservation of it is
enforced by the types. This statement is deliberately independent of
computability, serialization, memory layout, and a machine model; its
algorithmic realization and word-RAM execution are stated separately.
-/

namespace Lax842588.ValueTranslations

open Lax146103.MSOSyntax
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.TreeAutomaton

/-- A finite sequence of natural-number words. This is a carrier type, not a
serialization contract. -/
abbrev CodeString := List Nat

/-- A finite ranked alphabet is described by listing the ranks of its symbols.
The symbol in position `i` has rank `code[i]`. -/
abbrev RankedAlphabetCode := List Nat

namespace RankedAlphabetCode

/-- The canonical ranked alphabet represented by a rank string. -/
def toRankedAlphabet (code : RankedAlphabetCode) : RankedAlphabet where
  Symbol := Fin code.length
  symbolsFintype := inferInstance
  symbolsDecidableEq := inferInstance
  rank i := code.get i

end RankedAlphabetCode

/-- A finite transition consists of a symbol number, a parent-state number,
and the ordered list of child-state numbers. -/
abbrev TransitionCode := Nat × Nat × List Nat

/-- An automaton body consists of its number of states, transition list, and
accepting-state list. Its ranked alphabet is supplied separately. -/
abbrev AutomatonCode := Nat × List TransitionCode × List Nat

/-- A represented automaton packages its ranked alphabet with its body. -/
abbrev EncodedAutomaton := RankedAlphabetCode × AutomatonCode

namespace AutomatonCode

/-- The tree automaton denoted by an automaton body over an encoded
ranked alphabet. Out-of-range states and malformed transitions are ignored. -/
def toAutomaton (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    Automaton alphabet.toRankedAlphabet (Fin M.1) where
  transition a q childStates :=
    M.2.1.any fun tr =>
      decide (tr.1 = a.val ∧ tr.2.1 = q.val ∧
        tr.2.2 = List.ofFn (fun i => (childStates i).val))
  accept q := M.2.2.contains q.val

/-- The ranked-tree language denoted by an automaton body over an encoded
ranked alphabet. -/
def language (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    TreeLanguage alphabet.toRankedAlphabet :=
  (M.toAutomaton alphabet).language

end AutomatonCode

/-- Value-level translations preserve the alphabet and denoted language in
both directions. Their domains are finite automaton values and the existing
intrinsic sentence syntax, not a second formula datatype. No physical
representation or algorithmic claim is part of this mathematical statement. -/
axiom language_equivalence :
  (∃ automatonToMSO : (alphabet : RankedAlphabetCode) → AutomatonCode →
      Sentence (treeSignature alphabet.toRankedAlphabet),
    ∀ alphabet M,
      AutomatonCode.language alphabet M =
        sentenceLanguage (automatonToMSO alphabet M)) ∧
  (∃ msoToAutomaton : (alphabet : RankedAlphabetCode) →
      Sentence (treeSignature alphabet.toRankedAlphabet) → AutomatonCode,
    ∀ alphabet phi,
      AutomatonCode.language alphabet (msoToAutomaton alphabet phi) =
        sentenceLanguage phi)

end Lax842588.ValueTranslations
