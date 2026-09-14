import Lax842588.StructuralRepresentations

/-!
---
title: Distinguished structural inputs for tree-automaton evaluation
type: definition and theorem
---

An automaton together with a ranked tree is represented by one fixed
constructor whose two fields use the certified structural presentations of
automata and trees. This complete equation determines the entire represented
content and therefore permits no compiled table, traversal order, semantic
annotation, or other advice.

The physical word-RAM input is the distinguished `lax-58` input tape of this
structural value: its root word followed by its immutable arena. The exact
input length is three words per structural node plus the root word. No
specialized evaluator layout is part of this concept.
-/

namespace Lax842588.TreeModelCheckingEncoding

open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax560851.StructuralPresentation
open Lax560851.StructuralPresentation.Presentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- Number of constructor occurrences in a ranked tree. -/
def treeSize {A : RankedAlphabet} : Tree A → Nat
  | .node _ children =>
      1 + (List.ofFn fun i => treeSize (children i)).sum

/-- Structural size of the certified automaton representation. -/
def automatonSize (M : EncodedAutomaton) : Nat :=
  StructuralRepresentations.automatonPresentation.structuralSize M

/-- Largest symbol rank in a finite encoded alphabet. This is mathematical
alphabet data, independently of any evaluator representation. -/
def maximumRank (alphabet : RankedAlphabetCode) : Nat :=
  alphabet.foldl max 0

/-- A runtime instance for uniform tree-automaton acceptance. Bundling the
dependent tree with its automaton makes the complete input an ordinary type
that can be passed to reusable complexity predicates. -/
structure AutomatonAcceptanceInstance where
  automaton : EncodedAutomaton
  tree : Tree automaton.1.toRankedAlphabet

/-- Complete advice-free structural content of an automaton-evaluation
instance. Both fields use named, constructor-certified presentations. -/
def automatonTreeRaw (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Raw :=
  Raw.constructor "automatonAcceptance"
    [StructuralRepresentations.automatonPresentation.toRaw M,
      StructuralRepresentations.treeStructure M.1 t]

/-- The complete certified content of a bundled uniform acceptance input. -/
def automatonAcceptanceRaw (input : AutomatonAcceptanceInstance) : Raw :=
  automatonTreeRaw input.automaton input.tree

/-- Explicit presentation used by the uniform reusable RAM predicate. Its
encoder is exactly `automatonTreeRaw`; no evaluator-specific data is added. -/
noncomputable def automatonAcceptancePresentation :
    Presentation AutomatonAcceptanceInstance :=
  presentationOf automatonAcceptanceRaw

/-- Explicit presentation for the old fixed-automaton input convention. The
fixed automaton remains physically present, exactly as in `automatonInput`. -/
noncomputable def fixedAutomatonPresentation (M : EncodedAutomaton) :
    Presentation (Tree M.1.toRankedAlphabet) :=
  presentationOf (automatonTreeRaw M)

/-- Structural size of the complete runtime input. -/
def inputStructuralSize (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Nat :=
  (automatonTreeRaw M t).nodes

/-- All primitive natural payloads in the complete runtime input fit in one
`w`-bit word. -/
def InputPayloadsFitInWord (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (w : Nat) : Prop :=
  (automatonTreeRaw M t).PayloadsFitInWord w

/-- Largest primitive natural payload in the complete structural input. -/
def inputPayloadMax (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Nat :=
  (automatonTreeRaw M t).maxNat

/-- The unique machine input admitted by the runtime theorem. -/
def automatonInput (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : List Nat :=
  (encodeRaw (automatonTreeRaw M t)).toInput

/-- Exact footprint of the distinguished structural machine input. -/
axiom automatonInput_length (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    (automatonInput M t).length = 3 * inputStructuralSize M t + 1

end Lax842588.TreeModelCheckingEncoding
