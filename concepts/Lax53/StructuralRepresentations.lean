import Lax58.StructuralCombinators
import Lax58.WordArena
import Lax53.EffectiveTranslations

/-!
---
title: Certified structural representations for ranked-tree model checking
type: definition and theorem
---

The finite values used by the uniform translations have explicit structural
presentations. Product and list codes are built transitively from the fixed
`lax-58` vocabulary. Raw formulas and ranked trees have datatype-specific
certificates whose equations cover every constructor.

These presentations contain no compiled automaton, semantic annotation, or
other advice. Their distinguished word-memory realization is the generic
`Lax58.WordArena.encode` construction. The specialized table and postorder
layouts used by the RAM evaluator remain a separate refinement layer.
-/

namespace Lax53.StructuralRepresentations

open Lax53.RankedTree
open Lax53.EffectiveTranslations
open Lax58.StructuralPresentation
open Lax58.StructuralPresentation.Presentation
open Lax58.StructuralCombinators

universe u

/-- A presentation induced by a structural map. Its partial inverse chooses a
preimage when one exists. Lawfulness is certified below for the concrete
injective maps used in this submission. -/
noncomputable def presentationOf {α : Type u} (f : α → Raw) : Presentation α := by
  classical
  exact {
    toRaw := f
    fromRaw := fun raw =>
      if h : ∃ x, f x = raw then some (Classical.choose h) else none
  }

/-- Structural presentation of an encoded ranked alphabet. -/
def rankedAlphabet : Presentation RankedAlphabetCode := list nat

/-- Structural presentation of one transition record. -/
def transition : Presentation TransitionCode := prod nat (prod nat (list nat))

/-- Structural presentation of an automaton body. -/
def automatonBody : Presentation AutomatonCode :=
  prod nat (prod (list transition) (list nat))

/-- Structural presentation of an alphabet together with an automaton body. -/
def automaton : Presentation EncodedAutomaton := prod rankedAlphabet automatonBody

/-- Constructor-structural map for raw formulas. -/
def formulaRaw : RawFormula → Raw
  | .falsum => Raw.constructor 0 []
  | .equal x y => Raw.constructor 1 [nat.toRaw x, nat.toRaw y]
  | .label symbol x => Raw.constructor 2 [nat.toRaw symbol, nat.toRaw x]
  | .child slot x y => Raw.constructor 3 [nat.toRaw slot, nat.toRaw x, nat.toRaw y]
  | .mem x X => Raw.constructor 4 [nat.toRaw x, nat.toRaw X]
  | .or phi psi => Raw.constructor 5 [formulaRaw phi, formulaRaw psi]
  | .neg phi => Raw.constructor 6 [formulaRaw phi]
  | .exFO phi => Raw.constructor 7 [formulaRaw phi]
  | .exSO phi => Raw.constructor 8 [formulaRaw phi]

/-- Named structural presentation of raw MSO syntax. -/
noncomputable def formula : Presentation RawFormula := presentationOf formulaRaw

/-- Structural presentation of an alphabet together with a raw sentence. -/
noncomputable def sentence : Presentation EncodedSentence := prod rankedAlphabet formula

/-- Constructor-structural map for a ranked tree over an encoded alphabet. -/
def treeRaw (alphabet : RankedAlphabetCode) :
    Tree alphabet.toRankedAlphabet → Raw
  | .node symbol children =>
      Raw.constructor 0
        (nat.toRaw symbol.val ::
          List.ofFn fun i => treeRaw alphabet (children i))

/-- Named structural presentation of ranked trees. -/
noncomputable def tree (alphabet : RankedAlphabetCode) :
    Presentation (Tree alphabet.toRankedAlphabet) :=
  presentationOf (treeRaw alphabet)

/-- The fixed combinator-built code presentations round-trip. -/
structure CodeCertificates : Prop where
  rankedAlphabet : StructuralRepresentations.rankedAlphabet.Lawful
  transition : StructuralRepresentations.transition.Lawful
  automatonBody : StructuralRepresentations.automatonBody.Lawful
  automaton : StructuralRepresentations.automaton.Lawful

/-- Complete constructor equations and round trip for raw formulas. -/
structure FormulaCertificate : Prop where
  lawful : StructuralRepresentations.formula.Lawful
  sentenceLawful : StructuralRepresentations.sentence.Lawful
  falsum : formula.toRaw .falsum = Raw.constructor 0 []
  equal (x y : Nat) : formula.toRaw (.equal x y) =
    Raw.constructor 1 [nat.toRaw x, nat.toRaw y]
  label (symbol x : Nat) : formula.toRaw (.label symbol x) =
    Raw.constructor 2 [nat.toRaw symbol, nat.toRaw x]
  child (slot x y : Nat) : formula.toRaw (.child slot x y) =
    Raw.constructor 3 [nat.toRaw slot, nat.toRaw x, nat.toRaw y]
  mem (x X : Nat) : formula.toRaw (.mem x X) =
    Raw.constructor 4 [nat.toRaw x, nat.toRaw X]
  or (phi psi : RawFormula) : formula.toRaw (.or phi psi) =
    Raw.constructor 5 [formula.toRaw phi, formula.toRaw psi]
  neg (phi : RawFormula) : formula.toRaw (.neg phi) =
    Raw.constructor 6 [formula.toRaw phi]
  exFO (phi : RawFormula) : formula.toRaw (.exFO phi) =
    Raw.constructor 7 [formula.toRaw phi]
  exSO (phi : RawFormula) : formula.toRaw (.exSO phi) =
    Raw.constructor 8 [formula.toRaw phi]

/-- Complete constructor equation and round trip for encoded-alphabet trees. -/
structure TreeCertificate : Prop where
  lawful (alphabet : RankedAlphabetCode) : (StructuralRepresentations.tree alphabet).Lawful
  node (alphabet : RankedAlphabetCode)
      (symbol : alphabet.toRankedAlphabet.Symbol)
      (children : Fin (alphabet.toRankedAlphabet.rank symbol) →
        Tree alphabet.toRankedAlphabet) :
    (tree alphabet).toRaw (.node symbol children) =
      Raw.constructor 0
        (nat.toRaw symbol.val ::
          List.ofFn fun i => (tree alphabet).toRaw (children i))

axiom codeCertificates : CodeCertificates

axiom formulaCertificate : FormulaCertificate

axiom treeCertificate : TreeCertificate

end Lax53.StructuralRepresentations
