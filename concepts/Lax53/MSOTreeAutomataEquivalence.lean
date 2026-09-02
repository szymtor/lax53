import Lax52.MSOSyntax
import Lax53.RankedTree
import Lax53.TreeStructure
import Lax53.TreeAutomaton
import Lax53.TreeAutomataToMSO
import Lax53.MSOToTreeAutomata

/-!
---
title: Thatcher–Wright–Doner theorem for finite ranked trees
type: theorem
---

Over a finite ranked alphabet, a language of finite ranked trees is recognizable
by a bottom-up finite tree automaton if and only if it is definable by a monadic
second-order sentence in the relational tree structure with unary label
predicates and indexed child relations. This is the ranked-tree
automata--MSO characterization proved by Thatcher and Wright (1968) and,
independently, by Doner (1970).
-/

namespace Lax53.MSOTreeAutomataEquivalence

open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.TreeAutomaton

universe u

axiom recognizable_iff_msoDefinable {A : RankedAlphabet.{u}}
    (L : TreeLanguage A) :
  Recognizable L ↔
    ∃ phi : Lax52.MSOSyntax.Sentence (treeSignature A), L = sentenceLanguage phi

end Lax53.MSOTreeAutomataEquivalence
