import Lax842588.TreeModelCheckingEncoding

/-!
Proof-only working layouts used by the existing verified IMP+ evaluator.

These definitions are deliberately absent from the Lax-53 concept package.
The public input is the distinguished Lax-58 arena. A charged preprocessing
phase will derive these arrays from that arena before the evaluator runs.
-/

namespace Lax842588Proofs

open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding

/-- Proof-only length-delimited block. -/
def block (x : CodeString) : CodeString := x.length :: x

/-- Proof-only fixed-width transition row. -/
def encodeTransitionFixed (maximumRank : Nat)
    (tr : TransitionCode) : CodeString :=
  tr.1 :: tr.2.1 :: tr.2.2.length ::
    (List.range maximumRank).map fun i => tr.2.2.getD i 0

/-- Evaluator-specific random-access automaton table. -/
def encodeAutomaton (input : EncodedAutomaton) : CodeString :=
  let maximumRank := maximumRank input.1
  input.1.length :: input.1 ++
    [input.2.1, input.2.2.1.length, maximumRank] ++
    input.2.2.1.flatMap (encodeTransitionFixed maximumRank) ++
    block input.2.2.2

/-- Evaluator-specific postorder symbol word. -/
def encodeTree (alphabet : RankedAlphabetCode) :
    Tree alphabet.toRankedAlphabet → CodeString
  | .node symbol children =>
      (List.ofFn (fun i => encodeTree alphabet (children i))).flatten ++
        [symbol.val]

@[simp] theorem encodeTree_length (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) :
    (encodeTree alphabet t).length = treeSize t := by
  induction t with
  | node symbol children ih =>
      simp [encodeTree, treeSize, List.length_flatten, ih, List.map_ofFn,
        Function.comp_def]
      omega

/-- Old evaluator framing, retained only as a proof intermediate. -/
def modelCheckingInput (parameter tree : CodeString) : CodeString :=
  block parameter ++ block tree

/-- Input consumed by the old evaluator before the charged arena front-end is
added. It is not an admissible public input. -/
def specializedInput (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : CodeString :=
  modelCheckingInput (encodeAutomaton M) (encodeTree M.1 t)

end Lax842588Proofs
