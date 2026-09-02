import Lax13.Ram
import Lax53.TreeModelCheckingEncoding

/-!
---
title: Linear-time model checking for finite tree automata
type: theorem
---

Acceptance by a finite bottom-up tree automaton is decidable in linear time in
the number of nodes of the input tree on a word RAM. The algorithm is uniform:
the encoded ranked alphabet and automaton are part of the input. There are one
word-RAM program and one absolute constant `C` such that, for every encoded
automaton `M` and ranked tree `t`, the program decides acceptance within
`C (|M| + 1)² |t|` instructions. Thus the constant multiplying the tree size
is explicitly quadratic in the length of the automaton's word representation.

The word-length hypothesis explicitly ensures that the input entries,
addresses, and claimed running time fit into machine words. The program is
chosen before the word length and works at every word length satisfying this
hypothesis.
-/

namespace Lax53.AutomatonLinearTime

open Lax13.Ram
open Lax53.RankedTree
open Lax53.TreeAutomaton
open Lax53.EffectiveTranslations
open Lax53.TreeModelCheckingEncoding

open Classical in
/-- One uniform word-RAM program decides acceptance in time quadratic in the
automaton representation times the number of tree nodes. -/
axiom exists_uniform_linearTime_automatonAcceptance :
  ∃ (program : Program) (constant : Nat),
    ∀ (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) (w : Nat),
      let parameterSize := (encodeAutomaton M).length
      let c := constant * (parameterSize + 1) ^ 2
      let input := automatonInput M t
      (∀ v ∈ input, c * (input.length + v + 1) ≤ 2 ^ w) →
        ∃ time ≤ c * treeSize t,
          RunsTo w program input
            (if M.2.toAutomaton M.1 |>.Accepts t then [1] else [0]) time

end Lax53.AutomatonLinearTime
