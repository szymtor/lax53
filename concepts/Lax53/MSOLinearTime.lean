import Lax13.Ram
import Lax53.EffectiveTranslations
import Lax53.TreeModelCheckingEncoding

/-!
---
title: Linear-time model checking for MSO on ranked trees
type: theorem
---

Monadic second-order model checking on finite ranked trees is linear in the
number of tree nodes for every fixed sentence. A finite alphabet and raw
sentence are first translated to a finite tree automaton. One uniform
word-RAM program then evaluates that fixed compiled parameter together with
the input tree within `f(φ) |t|` instructions.

Unlike the automaton case, no polynomial bound is claimed for `f`. The
sentence is fixed outside the measured execution, so its compilation time is
not charged to the linear scan of the runtime tree. If the sentence were
instead supplied at runtime, its preprocessing cost would have to be charged.
Ill-scoped raw syntax denotes the empty language. This theorem does not impose
a cost model on formula compilation.
-/

namespace Lax53.MSOLinearTime

open Lax13.Ram
open Lax53.RankedTree
open Lax53.EffectiveTranslations
open Lax53.TreeModelCheckingEncoding

open Classical in
/-- MSO sentences translate to fixed automaton parameters consumed by one
uniform word-RAM evaluator. The measured execution is linear in the tree size
with a sentence-dependent coefficient. -/
axiom exists_uniform_linearTime_msoModelChecking :
  ∃ (compiler : EncodedSentence → AutomatonCode) (program : Program)
      (coefficient : EncodedSentence → Nat),
    (∀ phi,
      AutomatonCode.language phi.1 (compiler phi) =
        FormulaCode.language phi.1 phi.2) ∧
    ∀ (phi : EncodedSentence) (t : Tree phi.1.toRankedAlphabet) (w : Nat),
      let M : EncodedAutomaton := (phi.1, compiler phi)
      let c := coefficient phi
      let input := automatonInput M t
      (∀ v ∈ input, c * (input.length + v + 1) ≤ 2 ^ w) →
        ∃ time ≤ c * treeSize t,
          RunsTo w program input
            (if t ∈ FormulaCode.language phi.1 phi.2 then [1] else [0]) time

end Lax53.MSOLinearTime
