import Lax52.MSOSyntax
import Lax53.RankedTree
import Lax53.TreeAutomaton
import Lax53.TreeStructure

/-!
---
title: Finite tree automata are MSO-definable
type: theorem
---

The language accepted by every bottom-up finite tree automaton over a ranked
alphabet is defined by a monadic second-order sentence over the corresponding
label and indexed-child signature.
-/

namespace Lax53.TreeAutomataToMSO

open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.TreeAutomaton

universe u v

axiom automaton_definable_by_mso {A : RankedAlphabet.{u}} {Q : Type v}
    [Fintype Q] (M : Automaton A Q) :
  ∃ phi : Lax52.MSOSyntax.Sentence (treeSignature A), M.language = sentenceLanguage phi

end Lax53.TreeAutomataToMSO
