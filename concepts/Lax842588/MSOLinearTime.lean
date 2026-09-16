import Mathlib.Computability.Partrec
import Lax560851.RamComplexity
import Lax842588.StructuralRepresentations
import Lax842588.TreeModelCheckingEncoding

/-!
---
title: Uniform word-RAM model checking for intrinsic MSO sentences
type: definition and theorem
---

One fixed word-RAM program decides monadic second-order satisfaction when the
ranked alphabet, the intrinsically scoped Lax-52 sentence, and the ranked tree
are all supplied at runtime. Their sole machine input is the distinguished
constructor-certified Lax560851 arena. The actual Lax808846 instruction bound
includes all sentence-to-automaton compilation and tree-automaton evaluation.

The resource coefficients are computable functions only of the constructor
size of the alphabet and sentence and of the largest symbol rank. This leaves
the unavoidable nonelementary dependence on the sentence abstract while
stating the uniform runtime in terms of mathematical sizes rather than a
serialization. For a fixed alphabet and sentence, a separate companion
program receives only the tree and runs linearly in its number of nodes.

The reusable Lax560851 predicate packages the single program, every sufficient
word width, and the payload/address/capacity premises. No constructor tags,
arena offsets, compiled automata, or intermediate syntax belong to this
concept.
-/

namespace Lax842588.MSOLinearTime

open Lax146103.MSOSyntax
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax842588.TreeModelCheckingEncoding
open Lax560851.StructuralPresentation
open Lax560851.StructuralPresentation.Presentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena
open Lax560851.RamComplexity

/-- Constructor size of an intrinsic MSO sentence, including its term and
relation fields but excluding any physical arena layout. -/
def sentenceSize (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) : Nat :=
  (formulaStructure alphabet phi).nodes

/-- Mathematical parameter size controlling the formula-dependent part of
the uniform algorithm. Symbol arity is explicit because one natural payload
can prescribe an arbitrarily large finite family. -/
def parameterSize (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) : Nat :=
  (derivedPresentation : Presentation RankedAlphabetCode).structuralSize alphabet +
    sentenceSize alphabet phi + maximumRank alphabet

/-- A complete dependent model-checking input, bundled as one ordinary type
for use with the reusable Lax560851 RAM-complexity predicate. -/
structure ModelCheckingInstance where
  alphabet : RankedAlphabetCode
  sentence : Sentence (treeSignature alphabet.toRankedAlphabet)
  tree : Tree alphabet.toRankedAlphabet

/-- Complete constructor-derived content of one uniform model-checking
instance. The dependent typing of the sentence and tree is enforced before
this representation is formed. -/
def msoTreeRaw (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Raw :=
  Raw.constructor "msoModelChecking"
    [(derivedPresentation : Presentation RankedAlphabetCode).toRaw alphabet,
      formulaStructure alphabet phi,
      treeStructure alphabet t]

/-- Exact structural content of a bundled uniform model-checking input. -/
def modelCheckingInstanceRaw (input : ModelCheckingInstance) : Raw :=
  msoTreeRaw input.alphabet input.sentence input.tree

/-- Presentation used by the reusable RAM predicate. Its encoder is exactly
`msoTreeRaw`, so bundling introduces no tags, advice, or alternate layout. -/
noncomputable def modelCheckingPresentation :
    Presentation ModelCheckingInstance :=
  presentationOf modelCheckingInstanceRaw

/-- Structural size of the complete uniform runtime input. -/
def inputStructuralSize (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  (msoTreeRaw alphabet phi t).nodes

/-- Largest primitive natural payload in the complete uniform input. -/
def inputPayloadMax (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  (msoTreeRaw alphabet phi t).maxNat

/-- Primitive payloads in the complete uniform input fit in a `w`-bit word. -/
def InputPayloadsFitInWord (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) (w : Nat) : Prop :=
  (msoTreeRaw alphabet phi t).PayloadsFitInWord w

/-- Distinguished Lax808846 input containing the alphabet, intrinsic sentence,
and tree. -/
def modelCheckingInput (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : List Nat :=
  (encodeRaw (msoTreeRaw alphabet phi t)).toInput

/-- Exact footprint of the uniform model-checking input. -/
axiom modelCheckingInput_length (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    (modelCheckingInput alphabet phi t).length =
      3 * inputStructuralSize alphabet phi t + 1

/-- The actual instruction allowance for the uniform model checker. The
computable coefficient absorbs sentence compilation and the automaton
workload; the remaining dependence is linear in tree nodes. -/
def uniformTimeBound (coefficient : Nat → Nat)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  coefficient (parameterSize alphabet phi) * (treeSize t + 1)

/-- Public word-resource allowance for the uniform implementation. -/
def uniformWordBound (coefficient : Nat → Nat)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  coefficient (parameterSize alphabet phi) *
    (inputStructuralSize alphabet phi t + inputPayloadMax alphabet phi t + 1)

open Classical in
/-- A single program handles every alphabet, intrinsic sentence, tree, and
sufficient word width. Formula compilation is part of this measured run. -/
axiom exists_uniform_msoModelChecking :
  ∃ timeCoefficient wordCoefficient : Nat → Nat,
    Computable timeCoefficient ∧ Computable wordCoefficient ∧
    RamComputableWithinUsing modelCheckingPresentation natOutput
      (fun input => if input.tree ∈ sentenceLanguage input.sentence then 1 else 0)
      (fun input => uniformTimeBound timeCoefficient input.alphabet
        input.sentence input.tree)
      (fun input => uniformWordBound wordCoefficient input.alphabet
        input.sentence input.tree)

/-- Structural size of a tree-only fixed-parameter input. -/
def treeStructuralSize (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  (treeStructure alphabet t).nodes

/-- Largest primitive payload in a tree-only fixed-parameter input. -/
def treePayloadMax (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  (treeStructure alphabet t).maxNat

/-- Primitive tree payloads fit in a `w`-bit word. -/
def TreePayloadsFitInWord (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) (w : Nat) : Prop :=
  (treeStructure alphabet t).PayloadsFitInWord w

/-- Distinguished tree-only input for a program specialized to a fixed
alphabet and sentence. -/
def treeInput (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) : List Nat :=
  (encodeRaw (treeStructure alphabet t)).toInput

open Classical in
/-- Once the alphabet and sentence are fixed before program choice, the
specialized program receives only a tree and has linear tree-node time. This
existential statement makes no effective program-generation claim. -/
axiom exists_fixed_sentence_modelChecking
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) :
  ∃ timeCoefficient wordCoefficient : Nat,
    RamComputableWithinUsing (treePresentation alphabet) natOutput
      (fun t => if t ∈ sentenceLanguage phi then 1 else 0)
      (fun t => timeCoefficient * (treeSize t + 1))
      (fun t => wordCoefficient * inputMagnitudeUsing
        (treePresentation alphabet) t)

end Lax842588.MSOLinearTime
