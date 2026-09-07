import Lax53.RankedTree

/-!
---
title: Bottom-up tree automata
type: definition
---

A bottom-up tree automaton over a ranked alphabet has a set of states, a
Boolean acceptance test, and a Boolean transition test. For a symbol of rank
$k$, the transition test decides whether a proposed state at the node and the
ordered $k$-tuple of states at its children form a transition. This includes
rank-zero transitions for constants.

A run to a state is defined recursively at every node by the same transition
rule. A tree is accepted when it has a run to an accepting state. A language is
recognizable when it is the language of such an automaton with finitely many
states. The automaton is deterministic when every symbol and tuple of child
states has exactly one possible state at the parent.
-/

namespace Lax53.TreeAutomaton

open Lax53.RankedTree

universe u v

/-- A bottom-up tree automaton with state type `Q`. This basic structure allows
arbitrary state types; recognizable languages and the main theorems explicitly
require finitely many states. -/
structure Automaton (A : RankedAlphabet.{u}) (Q : Type v) where
  transition : (a : A.Symbol) → Q → (Fin (A.rank a) → Q) → Bool
  accept : Q → Bool

namespace Automaton

/-- A run of `M` on `t` leading to state `q`. -/
def RunsTo {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q) :
    Tree A → Q → Prop
  | .node a children, q =>
      ∃ childStates : Fin (A.rank a) → Q,
        M.transition a q childStates = true ∧
          ∀ i : Fin (A.rank a), M.RunsTo (children i) (childStates i)

/-- A tree is accepted if some run leads to an accepting state. -/
def Accepts {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q)
    (t : Tree A) : Prop :=
  ∃ q : Q, M.accept q = true ∧ M.RunsTo t q

/-- The language accepted by a tree automaton. -/
def language {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q) :
    TreeLanguage A :=
  {t | M.Accepts t}

/-- A bottom-up tree automaton is deterministic when every symbol and ordered
tuple of child states has a unique resulting parent state. -/
def Deterministic {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q) : Prop :=
  ∀ (a : A.Symbol) (childStates : Fin (A.rank a) → Q),
    ∃! q : Q, M.transition a q childStates = true

end Automaton

/-- Recognizability by a tree automaton with finitely many states. -/
def Recognizable {A : RankedAlphabet.{u}} (L : TreeLanguage A) : Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : Automaton A Q, M.language = L

end Lax53.TreeAutomaton
