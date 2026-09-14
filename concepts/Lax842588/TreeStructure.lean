import Lax146103.MSOSyntax
import Lax146103.MSOSemantics
import Lax842588.RankedTree

/-!
---
title: Ranked trees as finite relational structures
type: definition
---

A ranked tree is viewed as a relational structure on its nodes. For every
alphabet symbol there is a unary predicate selecting the nodes carrying that
symbol. For every child slot up to the maximum rank of the alphabet there is a
binary relation connecting a node to its child in that slot.

The label and child relations directly define the canonical structure of each
tree. An MSO sentence defines the language of all ranked trees whose canonical
structure satisfies it.
-/

namespace Lax842588.TreeStructure

open FirstOrder
open FirstOrder.Language
open Lax842588.RankedTree

universe u

/-- Relation symbols for ranked trees. -/
inductive TreeRelation (A : RankedAlphabet.{u}) : Nat → Type u
  | label (a : A.Symbol) : TreeRelation A 1
  | child (i : ChildIndex A) : TreeRelation A 2

/-- The first-order language of ranked trees over `A`. -/
def treeSignature (A : RankedAlphabet.{u}) : FirstOrder.Language.{0, u} where
  Functions := fun _ => Empty
  Relations := TreeRelation A

/-- The canonical first-order structure of a ranked tree. -/
@[implicit_reducible]
def treeStructure {A : RankedAlphabet.{u}} (t : Tree A) :
    (treeSignature A).Structure (Node t) where
  funMap f := nomatch f
  RelMap
    | .label a, xs => Node.label (xs 0) = a
    | .child i, xs => Node.ChildAt i (xs 0) (xs 1)

/-- Satisfaction of a closed MSO sentence by the canonical structure of a
ranked tree. -/
def TreeModels {A : RankedAlphabet.{u}} (t : Tree A)
    (phi : Lax146103.MSOSyntax.Sentence (treeSignature A)) : Prop :=
  @Lax146103.MSOSemantics.Realize (treeSignature A) (Node t) (treeStructure t) 0 0 phi
    (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)

/-- The ranked-tree language defined by an MSO sentence. -/
def sentenceLanguage {A : RankedAlphabet.{u}}
    (phi : Lax146103.MSOSyntax.Sentence (treeSignature A)) : TreeLanguage A :=
  {t | TreeModels t phi}

end Lax842588.TreeStructure
