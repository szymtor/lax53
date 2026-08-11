import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec
import Lax52.MSOSyntax
import Lax53.RankedTree
import Lax53.TreeStructure
import Lax53.TreeAutomaton

/-!
---
title: Effective equivalence of MSO and finite tree automata
type: theorem
---

Finite tree automata have a canonical finite presentation: states are numbered
from zero, transitions are finite lists of a symbol, a parent state, and the
ordered list of child states, and accepting states are listed explicitly.

Uniform computable translations convert these presentations into monadic
second-order sentences and conversely. In both directions, the translation
preserves the language of finite ranked trees.
-/

namespace Lax53.EffectiveTranslations

open Lax52.MSOSyntax
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.TreeAutomaton

universe u

/-- A transition encoded by its symbol, parent state number, and ordered child
state numbers. -/
abbrev TransitionCode (A : RankedAlphabet.{u}) := A.Symbol × Nat × List Nat

/-- A canonical finite presentation of a tree automaton: the number of states,
the transition list, and the accepting-state list. -/
abbrev FiniteAutomatonCode (A : RankedAlphabet.{u}) :=
  Nat × List (TransitionCode A) × List Nat

namespace FiniteAutomatonCode

/-- The finite tree automaton denoted by a canonical presentation. State
numbers outside the declared range and malformed transition tuples are simply
ignored. -/
def toAutomaton {A : RankedAlphabet.{u}} (M : FiniteAutomatonCode A) :
    Automaton A (Fin M.1) where
  transition a q childStates :=
    M.2.1.any fun tr =>
      decide (tr.1 = a ∧ tr.2.1 = q.val ∧
        tr.2.2 = List.ofFn (fun i => (childStates i).val))
  accept q := M.2.2.contains q.val

/-- The ranked-tree language denoted by a canonical finite-automaton
presentation. -/
def language {A : RankedAlphabet.{u}} (M : FiniteAutomatonCode A) : TreeLanguage A :=
  M.toAutomaton.language

end FiniteAutomatonCode

/-- There are computable, language-preserving translations in both directions
between canonical finite tree-automaton presentations and MSO sentences. -/
axiom effective_equivalence {A : RankedAlphabet.{u}}
    [Primcodable A.Symbol]
    [Primcodable (Lax52.MSOSyntax.Sentence (treeSignature A))] :
  (∃ automatonToMSO : FiniteAutomatonCode A →
      Lax52.MSOSyntax.Sentence (treeSignature A),
    Computable automatonToMSO ∧
      ∀ M, M.language = sentenceLanguage (automatonToMSO M)) ∧
  (∃ msoToAutomaton : Lax52.MSOSyntax.Sentence (treeSignature A) →
      FiniteAutomatonCode A,
    Computable msoToAutomaton ∧
      ∀ phi, (msoToAutomaton phi).language = sentenceLanguage phi)

end Lax53.EffectiveTranslations
