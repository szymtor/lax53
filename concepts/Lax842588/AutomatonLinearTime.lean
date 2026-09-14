import Lax560851.RamComplexity
import Lax842588.TreeModelCheckingEncoding

/-!
---
title: Word-RAM evaluation of tree automata
type: theorem
---

Finite bottom-up tree-automaton acceptance has one uniform implementation on
the Lax word RAM. The program is chosen before the automaton, tree, and word
width. Its actual machine instruction count is bounded by a fixed constant
times a quadratic function of the automaton workload and a linear function of
the number of tree nodes. The workload is the certified constructor size plus
the largest symbol rank; the latter is relevant because a node may have that
many ordered children even though a rank is one primitive natural payload.

The only physical input admitted by the theorem is the distinguished
constructor-certified `lax-58` arena input. Lax560851's reusable complexity
predicate supplies the program quantifier and requires correctness at every
word width satisfying payload, arena-address, and implementation-capacity
bounds. The natural output is one word: zero for rejection and one for
acceptance.
-/

namespace Lax842588.AutomatonLinearTime

open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax560851.RamComplexity

/-- Intrinsic workload of an automaton for the simple uniform evaluator. It
keeps constructor count separate from the magnitude of its largest arity. -/
def automatonWorkSize (M : EncodedAutomaton) : Nat :=
  automatonSize M + maximumRank M.1

/-- Public instruction bound for the uniform evaluator. -/
def uniformTimeBound (constant : Nat) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Nat :=
  constant * (automatonWorkSize M + 1) ^ 2 * (treeSize t + 1)

/-- Explicit word-resource bound. Besides structural workload it includes the
largest primitive payload because machine values and the fixed compiler layout
must both fit in one word. -/
def uniformWordBound (constant : Nat) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Nat :=
  constant * (automatonWorkSize M + 1) ^ 2 *
    (inputStructuralSize M t + inputPayloadMax M t + 1)

open Classical in
/-- One program handles every certified automaton/tree input and every
sufficiently large word width. The reusable predicate contains the program
and width quantifiers and all three input/resource-fit premises. -/
axiom exists_uniform_automatonAcceptance :
  ∃ timeConstant wordConstant : Nat,
    RamComputableWithinUsing automatonAcceptancePresentation natOutput
      (fun input => if input.automaton.2.toAutomaton input.automaton.1 |>.Accepts
        input.tree then 1 else 0)
      (fun input => uniformTimeBound timeConstant input.automaton input.tree)
      (fun input => uniformWordBound wordConstant input.automaton input.tree)

open Classical in
/-- With the automaton fixed before program choice, acceptance is linear in
the number of tree nodes. This existential specialization claim does not
assert an effective program-producing function. -/
axiom exists_fixed_automatonAcceptance (M : EncodedAutomaton) :
  ∃ timeCoefficient wordCoefficient : Nat,
    RamComputableWithinUsing (fixedAutomatonPresentation M) natOutput
      (fun t => if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0)
      (fun t => timeCoefficient * (treeSize t + 1))
      (fun t => wordCoefficient * inputMagnitudeUsing
        (fixedAutomatonPresentation M) t)

end Lax842588.AutomatonLinearTime
