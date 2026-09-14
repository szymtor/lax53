import Lax842588.RankedTree
import Lax842588.TreeAutomaton

/-!
---
title: Determinization of tree automata
type: theorem
---

Every bottom-up tree automaton with finitely many states has an equivalent
deterministic tree automaton with finitely many states over the same ranked
alphabet.
-/

namespace Lax842588.Determinization

open Lax842588.RankedTree
open Lax842588.TreeAutomaton

universe u v

axiom exists_deterministic_equivalent {A : RankedAlphabet.{u}} {Q : Type v}
    [Fintype Q] (M : Automaton A Q) :
  ∃ Q' : Type v, ∃ _ : Fintype Q', ∃ D : Automaton A Q',
    D.Deterministic ∧ D.language = M.language

end Lax842588.Determinization
