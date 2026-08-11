import Lax53.RankedTree
import Lax53.TreeAutomaton

/-!
---
title: Determinization of finite tree automata
type: theorem
---

Every bottom-up finite tree automaton has an equivalent deterministic finite
tree automaton over the same ranked alphabet.
-/

namespace Lax53.Determinization

open Lax53.RankedTree
open Lax53.TreeAutomaton

universe u v

axiom exists_deterministic_equivalent {A : RankedAlphabet.{u}} {Q : Type v}
    [Fintype Q] (M : Automaton A Q) :
  ∃ Q' : Type v, ∃ _ : Fintype Q', ∃ D : Automaton A Q',
    D.Deterministic ∧ D.language = M.language

end Lax53.Determinization
