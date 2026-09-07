import Lax53Proofs.EncodedAutomatonEvaluation
import Lax53Proofs.RuntimeLayout

namespace Lax53Proofs.EncodedAutomatonWordEvaluation

open Lax53.RankedTree
open Lax53.ValueTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.EncodedAutomatonEvaluation

/-- The reachable-state list computed above one postorder symbol, assuming
the ordered child-state lists have already been recovered. -/
def parentStates (M : AutomatonCode) (symbol : Nat)
    (childReachable : List CodeString) : CodeString :=
  M.2.1.filterMap fun tr =>
    if tr.1 = symbol && tr.2.1 < M.1 &&
        ChildrenAgree tr.2.2 childReachable then
      some tr.2.1
    else none

/-- Process one symbol of a postorder tree word. The top `rank(symbol)`
entries of the stack are the children, in reverse order. -/
def pushSymbol (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (stack : List CodeString) (symbol : Nat) : List CodeString :=
  let k := alphabet.getD symbol 0
  let childReachable := (stack.take k).reverse
  parentStates M symbol childReachable :: stack.drop k

/-- Execute the sparse bottom-up evaluator on a word, starting with an
arbitrary forest stack. -/
def evalWord (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (word : CodeString) (stack : List CodeString := []) : List CodeString :=
  word.foldl (pushSymbol alphabet M) stack

theorem evalWord_append (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (xs ys : CodeString) (stack : List CodeString) :
    evalWord alphabet M (xs ++ ys) stack =
      evalWord alphabet M ys (evalWord alphabet M xs stack) := by
  simp [evalWord, List.foldl_append]

theorem alphabet_getD_symbol (alphabet : RankedAlphabetCode)
    (a : alphabet.toRankedAlphabet.Symbol) :
    alphabet.getD a.val 0 = alphabet.toRankedAlphabet.rank a := by
  simp [RankedAlphabetCode.toRankedAlphabet, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem, a.isLt]

theorem parentStates_eq_reachable_node (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (a : alphabet.toRankedAlphabet.Symbol)
    (children : Fin (alphabet.toRankedAlphabet.rank a) →
      Tree alphabet.toRankedAlphabet) :
    parentStates M a.val
        (List.ofFn fun i => reachable alphabet M (children i)) =
      reachable alphabet M (.node a children) := by
  rfl

/-- Concatenating postorder encodings of a forest pushes its reachable-state
lists in reverse order. This is the stack discipline used at a parent node. -/
theorem evalWord_forest (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (trees : List (Tree alphabet.toRankedAlphabet))
    (h : ∀ t ∈ trees, ∀ stack,
      evalWord alphabet M (encodeTree alphabet t) stack =
        reachable alphabet M t :: stack)
    (stack : List CodeString) :
    evalWord alphabet M
        (trees.flatMap (encodeTree alphabet)) stack =
      (trees.map (reachable alphabet M)).reverse ++ stack := by
  induction trees generalizing stack with
  | nil => simp [evalWord]
  | cons t trees ih =>
      rw [List.flatMap_cons, evalWord_append, h t (by simp)]
      rw [ih]
      · simp
      · intro u hu
        exact h u (by simp [hu])

/-- On the canonical postorder word of a tree, word evaluation pushes exactly
the same reachable-state list as the recursive tree evaluator. -/
theorem evalWord_encodeTree (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (stack : List CodeString) :
    evalWord alphabet M (encodeTree alphabet t) stack =
      reachable alphabet M t :: stack := by
  induction t generalizing stack with
  | node a children ih =>
      rw [encodeTree, evalWord_append]
      have hforest := evalWord_forest alphabet M (List.ofFn children) (by
        intro u hu s
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
        exact ih i s) stack
      rw [show List.flatten (List.ofFn fun i => encodeTree alphabet (children i)) =
          (List.ofFn children).flatMap (encodeTree alphabet) by
        rw [List.flatMap_def]
        simp [List.map_ofFn, Function.comp_def]]
      rw [hforest]
      change pushSymbol alphabet M
        ((List.map (reachable alphabet M) (List.ofFn children)).reverse ++ stack)
        a.val = reachable alphabet M (.node a children) :: stack
      unfold pushSymbol
      rw [alphabet_getD_symbol]
      simp only [List.map_ofFn, Function.comp_apply]
      rw [show List.ofFn (reachable alphabet M ∘ children) =
          List.ofFn (fun i => reachable alphabet M (children i)) by rfl]
      have hlen :
          (List.ofFn fun i => reachable alphabet M (children i)).reverse.length =
            alphabet.toRankedAlphabet.rank a := by simp
      rw [List.take_append_of_le_length (le_of_eq hlen.symm),
        List.drop_append_of_le_length (le_of_eq hlen.symm)]
      rw [List.take_of_length_le (le_of_eq hlen),
        List.drop_eq_nil_of_le (le_of_eq hlen)]
      simp only [List.nil_append, List.reverse_reverse]
      exact congrArg (fun states => states :: stack)
        (parentStates_eq_reachable_node alphabet M a children)

/-- The final stack of a canonical tree word is a singleton. -/
theorem evalWord_encodeTree_nil (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) :
    evalWord alphabet M (encodeTree alphabet t) =
      [reachable alphabet M t] := by
  simpa using evalWord_encodeTree alphabet M t []

/-- Acceptance read from the final word-evaluation stack. -/
def acceptsWord (M : AutomatonCode) (stack : List CodeString) : Bool :=
  (stack.getD 0 []).any fun q => M.2.2.contains q

theorem acceptsWord_encodeTree_eq_true_iff (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (t : Tree alphabet.toRankedAlphabet) :
    acceptsWord M (evalWord alphabet M (encodeTree alphabet t)) = true ↔
      (M.toAutomaton alphabet).Accepts t := by
  rw [evalWord_encodeTree_nil]
  simpa [acceptsWord, accepts] using accepts_eq_true_iff alphabet M t

end Lax53Proofs.EncodedAutomatonWordEvaluation
