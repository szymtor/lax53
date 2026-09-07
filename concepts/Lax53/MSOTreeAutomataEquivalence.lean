import Lax52.MSOSyntax
import Lax53.RankedTree
import Lax53.TreeStructure
import Lax53.TreeAutomaton

/-!
---
title: Thatcher–Wright–Doner theorem for finite ranked trees
type: theorem
---

Over a finite ranked alphabet, a language of finite ranked trees is recognizable
by a bottom-up tree automaton with finitely many states if and only if it is
definable by a monadic second-order sentence in the relational tree structure
with unary label predicates and indexed child relations. This is the ranked-tree
automata--MSO characterization proved by Thatcher and Wright (1968) and,
independently, by Doner (1970).

The two directions are stated explicitly here as well: every automaton has
an equivalent MSO sentence, and every MSO sentence defines a recognizable
language.
-/

namespace Lax53.MSOTreeAutomataEquivalence

open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.TreeAutomaton

universe u v

/-- Every tree automaton with finitely many states has an equivalent MSO sentence. -/
axiom automaton_definable_by_mso {A : RankedAlphabet.{u}} {Q : Type v}
    [Fintype Q] (M : Automaton A Q) :
  ∃ phi : Lax52.MSOSyntax.Sentence (treeSignature A), M.language = sentenceLanguage phi

/-- Every MSO sentence defines a recognizable ranked-tree language. -/
axiom mso_definable_is_recognizable {A : RankedAlphabet.{u}}
    (phi : Lax52.MSOSyntax.Sentence (treeSignature A)) :
  Recognizable (sentenceLanguage phi)

/-- Recognizability and MSO definability characterize the same languages. -/
axiom recognizable_iff_msoDefinable {A : RankedAlphabet.{u}}
    (L : TreeLanguage A) :
  Recognizable L ↔
    ∃ phi : Lax52.MSOSyntax.Sentence (treeSignature A), L = sentenceLanguage phi

end Lax53.MSOTreeAutomataEquivalence
