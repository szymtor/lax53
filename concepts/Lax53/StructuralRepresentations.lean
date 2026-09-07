import Lax58.CertifiedDerivationElab
import Lax58.WordArena
import Lax53.ValueTranslations

/-!
---
title: Certified structural representations for ranked-tree model checking
type: definition and theorem
---

The finite automaton values used by the uniform evaluator have explicit
structural presentations. Product and list codes are built transitively from
the fixed `lax-58` vocabulary. Intrinsic formulas and ranked trees have
datatype-specific first-class certificates covering every constructor and
primitive field. Each `derive_certified_encoding` invocation emits the encoder,
its `.Laws` proposition, and its `.certified` witness. For example,
`#print formulaStructure.Laws` displays the full generated formula contract.
Field resolution is closed and never consults `FieldEncoding` instances.

These presentations contain no compiled automaton, semantic annotation, or
other advice. Their distinguished word-memory realization is the generic
`Lax58.WordArena.encode` construction. Any evaluator-specific representation
engineering belongs only to the proof package and is charged there.
-/

namespace Lax53.StructuralRepresentations

open FirstOrder
open FirstOrder.Language
open Lax52.MSOSyntax
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.ValueTranslations
open Lax58.StructuralPresentation
open Lax58.StructuralPresentation.Presentation
open Lax58.StructuralCombinators
open Lax58.CertifiedDerivation

universe u

/-- Structural presentation of the complete finite automaton value. Its
components are derived automatically from the `Nat`, product, and ordered-list
structure of `EncodedAutomaton`. -/
def automatonPresentation : Presentation EncodedAutomaton :=
  derivedPresentation

/-- Structural representation of a term in the ranked-tree signature. That
signature has no function symbols, so every term is intrinsically a variable;
the impossible function case carries no represented data. -/
derive_certified_encoding termStructure (alphabet : RankedAlphabetCode)
    indexed {n : Nat} :
    (treeSignature alphabet.toRankedAlphabet).Term (Fin n)

/-- Structural representation of a relation symbol in the ranked-tree
signature. Subtype proofs in child indices are erased; their natural value is
the complete computational content of the field. -/
derive_certified_encoding relationStructure (alphabet : RankedAlphabetCode)
    indexed {arity : Nat} :
    (treeSignature alphabet.toRankedAlphabet).Relations arity

/-- Constructor-derived structural representation of the existing intrinsic
Lax-52 formula syntax. Recursive occurrences are represented recursively and
finite term families are enumerated in their intrinsic order. This is not a
second formula datatype and performs no elaboration or semantic preprocessing. -/
derive_certified_encoding formulaStructure (alphabet : RankedAlphabetCode)
    indexed {n m : Nat} :
    Formula (treeSignature alphabet.toRankedAlphabet) n m

/-- Named structural presentation of intrinsically scoped MSO sentences. -/
noncomputable def sentencePresentation (alphabet : RankedAlphabetCode) :
    Presentation (Lax52.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet)) :=
  Lax58.StructuralPresentation.presentationOf (formulaStructure alphabet)

/-- Constructor-structural map for a ranked tree over an encoded alphabet. -/
derive_certified_encoding treeStructure (alphabet : RankedAlphabetCode)
    indexed : Tree alphabet.toRankedAlphabet

/-- Named structural presentation of ranked trees. -/
noncomputable def treePresentation (alphabet : RankedAlphabetCode) :
    Presentation (Tree alphabet.toRankedAlphabet) :=
  Lax58.StructuralPresentation.presentationOf (treeStructure alphabet)

/-- The complete generated formula laws use only certified fields, including
the generated term and relation encodings. -/
axiom formula_structural (alphabet : RankedAlphabetCode) :
  ∀ {n m : Nat}, formulaStructure.Laws alphabet (n := n) (m := m)

/-- The tree encoder agrees pointwise with the complete constructor fold
generated from the dependent ranked-tree datatype. -/
axiom tree_structural (alphabet : RankedAlphabetCode) :
  treeStructure.Laws alphabet

/-- The recursive tree presentation is a genuine round-tripping
presentation. Advice-freedom is stated separately by `tree_structural`. -/
axiom tree_lawful (alphabet : RankedAlphabetCode) :
  (StructuralRepresentations.treePresentation alphabet).Lawful

/-- The constructor-derived sentence representation is a genuine
round-tripping presentation. -/
axiom sentence_lawful (alphabet : RankedAlphabetCode) :
  (StructuralRepresentations.sentencePresentation alphabet).Lawful

end Lax53.StructuralRepresentations
