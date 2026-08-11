import Lax52.MSOSyntax
import Lax53.RankedTree
import Lax53.TreeAutomaton
import Lax53.TreeStructure

/-!
---
title: MSO-definable ranked-tree languages are recognizable
type: theorem
---

Every monadic second-order sentence over finite ranked trees defines a language
recognized by a bottom-up finite tree automaton.
-/

namespace Lax53.MSOToTreeAutomata

open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.TreeAutomaton

universe u

axiom mso_definable_is_recognizable {A : RankedAlphabet.{u}}
    (phi : Lax52.MSOSyntax.Sentence (treeSignature A)) :
  Recognizable (sentenceLanguage phi)

end Lax53.MSOToTreeAutomata
