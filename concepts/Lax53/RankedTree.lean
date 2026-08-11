import Mathlib.Data.Fintype.Basic

/-!
---
title: Finite ranked trees
type: definition
---

A ranked alphabet is a finite type of symbols together with a natural-number
rank for every symbol. A tree over a ranked alphabet is a finite term: a node
labelled by a symbol of rank $k$ has exactly $k$ ordered children.

Nodes are occurrences of symbols in a particular tree. They carry their
labels and their indexed immediate-child relation intrinsically, independently
of any logical presentation of trees.

-/

namespace Lax53.RankedTree

universe u

/-- A finite alphabet whose symbols have prescribed arities. -/
structure RankedAlphabet where
  Symbol : Type u
  [symbolsFintype : Fintype Symbol]
  [symbolsDecidableEq : DecidableEq Symbol]
  rank : Symbol → Nat

attribute [instance] RankedAlphabet.symbolsFintype
attribute [instance] RankedAlphabet.symbolsDecidableEq

/-- Finite terms over a ranked alphabet. A node labelled by `a` has one
ordered child for each element of `Fin (A.rank a)`. -/
inductive Tree (A : RankedAlphabet.{u}) : Type u
  | node (a : A.Symbol) (children : Fin (A.rank a) → Tree A) : Tree A

/-- The set of child slots occurring in the alphabet. Its zero-based index
`i` represents the slot customarily numbered `i+1`. -/
def ChildIndex (A : RankedAlphabet.{u}) : Type :=
  {i : Nat // ∃ a : A.Symbol, i < A.rank a}

namespace ChildIndex

/-- Regard a child slot of a particular symbol as a child slot of the whole
alphabet. -/
def ofSymbolIndex {A : RankedAlphabet.{u}} (a : A.Symbol)
    (i : Fin (A.rank a)) : ChildIndex A :=
  ⟨i, ⟨a, i.isLt⟩⟩

end ChildIndex

/-- The nodes occurring in a particular ranked tree. -/
inductive Node {A : RankedAlphabet.{u}} : Tree A → Type u
  | root {a : A.Symbol} {children : Fin (A.rank a) → Tree A} :
      Node (.node a children)
  | inChild {a : A.Symbol} {children : Fin (A.rank a) → Tree A}
      (i : Fin (A.rank a)) (p : Node (children i)) :
      Node (.node a children)

namespace Node

/-- The root node of a tree. -/
def rootOf {A : RankedAlphabet.{u}} : (t : Tree A) → Node t
  | .node _ _ => .root

/-- The symbol labelling a node. -/
def label {A : RankedAlphabet.{u}} : {t : Tree A} → Node t → A.Symbol
  | .node a _, .root => a
  | .node _ _, .inChild _ p => label p

/-- The `i`th child of a node, as a node of the same ambient tree. -/
def child {A : RankedAlphabet.{u}} :
    {t : Tree A} → (p : Node t) → Fin (A.rank p.label) → Node t
  | .node _ children, .root, i => .inChild i (rootOf (children i))
  | .node _ _, .inChild j p, i => .inChild j (child p i)

/-- `ChildAt i p q` says that `q` is the immediate child of `p` in the
alphabet-wide child slot `i`. -/
def ChildAt {A : RankedAlphabet.{u}} (i : ChildIndex A) {t : Tree A}
    (p q : Node t) : Prop :=
  ∃ j : Fin (A.rank p.label),
    ChildIndex.ofSymbolIndex p.label j = i ∧ q = child p j

end Node

/-- A language of ranked trees. -/
abbrev TreeLanguage (A : RankedAlphabet.{u}) := Set (Tree A)

end Lax53.RankedTree
