import Lax52.MSOSyntax
import Lax53.RankedTree
import Lax53.TreeStructure
import Lax53.TreeAutomaton

/-!
---
title: Uniform equivalence of MSO and finite tree automata
type: theorem
---

A finite ranked alphabet is described by the finite list of its symbol ranks;
symbols are numbered by their positions in that list. Automata use finite
lists of numbered transitions, while MSO formulas are represented directly by
their inductive syntax.

There are uniform mathematical translations between these finite values in
both directions. They preserve the ranked-alphabet component and the denoted
tree language. This statement is deliberately independent of serialization,
memory layout, and a machine model; effective realization and word-RAM
execution are stated separately.
-/

namespace Lax53.EffectiveTranslations

open Lax52.MSOSyntax
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.TreeAutomaton

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

/-- A uniform automaton input includes its ranked-alphabet string. -/
abbrev EncodedAutomaton := RankedAlphabetCode × AutomatonCode

namespace AutomatonCode

/-- The finite tree automaton denoted by an automaton body over an encoded
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

/-- Raw, extrinsically scoped MSO syntax. First-order and monadic variables,
label symbols, and child slots are represented by natural-number indices. -/
inductive RawFormula
  | falsum
  | equal (x y : Nat)
  | label (symbol x : Nat)
  | child (slot x y : Nat)
  | mem (x X : Nat)
  | or (phi psi : RawFormula)
  | neg (phi : RawFormula)
  | exFO (phi : RawFormula)
  | exSO (phi : RawFormula)

namespace RawFormula

def fin? (i n : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨i, h⟩ else none

def childIndex? (alphabet : RankedAlphabetCode) (slot : Nat) :
    Option (ChildIndex alphabet.toRankedAlphabet) :=
  if h : ∃ a : alphabet.toRankedAlphabet.Symbol,
      slot < alphabet.toRankedAlphabet.rank a then
    some ⟨slot, h⟩
  else none

/-- Check scopes and alphabet indices and elaborate raw syntax into the
intrinsically scoped MSO syntax of `lax-52`. -/
def elaborate (alphabet : RankedAlphabetCode) :
    (n m : Nat) → RawFormula →
      Option (Formula (treeSignature alphabet.toRankedAlphabet) n m)
  | _, _, .falsum => some .falsum
  | n, _, .equal x y => do
      let x ← fin? x n
      let y ← fin? y n
      pure (.equal (.var x) (.var y))
  | n, _, .label symbol x => do
      let symbol ← fin? symbol alphabet.length
      let x ← fin? x n
      pure (.rel (.label symbol) (fun _ => .var x))
  | n, _, .child slot x y => do
      let slot ← childIndex? alphabet slot
      let x ← fin? x n
      let y ← fin? y n
      pure (.rel (.child slot) (fun i => Fin.cases (.var x) (fun _ => .var y) i))
  | n, m, .mem x X => do
      let x ← fin? x n
      let X ← fin? X m
      pure (.mem (.var x) X)
  | n, m, .or phi psi => do
      let phi ← elaborate alphabet n m phi
      let psi ← elaborate alphabet n m psi
      pure (.or phi psi)
  | n, m, .neg phi => do
      let phi ← elaborate alphabet n m phi
      pure (.neg phi)
  | n, m, .exFO phi => do
      let phi ← elaborate alphabet (n + 1) m phi
      pure (.exFO phi)
  | n, m, .exSO phi => do
      let phi ← elaborate alphabet n (m + 1) phi
      pure (.exSO phi)

end RawFormula

/-- The finite syntactic body of an MSO sentence. -/
abbrev FormulaCode := RawFormula

/-- A uniform MSO input includes its ranked-alphabet string. -/
abbrev EncodedSentence := RankedAlphabetCode × FormulaCode

namespace FormulaCode

/-- Interpret raw formula syntax over a finite ranked alphabet. Ill-scoped
variable, symbol, or child-slot indices denote the empty language. -/
def language (alphabet : RankedAlphabetCode) (code : FormulaCode) :
    TreeLanguage alphabet.toRankedAlphabet :=
  match RawFormula.elaborate alphabet 0 0 code with
  | some phi => sentenceLanguage phi
  | none => ∅

end FormulaCode

/-- Uniform value-level translations preserve the alphabet and denoted
language in both directions. No physical representation is part of this
mathematical statement. -/
axiom uniform_language_equivalence :
  (∃ automatonToMSO : EncodedAutomaton → EncodedSentence,
    ∀ input,
      (automatonToMSO input).1 = input.1 ∧
      AutomatonCode.language input.1 input.2 =
        FormulaCode.language input.1 (automatonToMSO input).2) ∧
  (∃ msoToAutomaton : EncodedSentence → EncodedAutomaton,
    ∀ input,
      (msoToAutomaton input).1 = input.1 ∧
      AutomatonCode.language input.1 (msoToAutomaton input).2 =
        FormulaCode.language input.1 input.2)

end Lax53.EffectiveTranslations
