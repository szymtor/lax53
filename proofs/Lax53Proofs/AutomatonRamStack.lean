import Lax53Proofs.AutomatonRamSemantics

namespace Lax53Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1000000
open Classical

open Lax53.RankedTree
open Lax53.ValueTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.EncodedAutomatonEvaluation
open Lax53Proofs.EncodedAutomatonWordEvaluation

theorem childRows_reverse (stack : List (List Nat)) (k : Nat)
    (hk : k ≤ stack.length) :
    childRows stack.reverse stack.length k = (stack.take k).reverse := by
  have hchildDrop : childRows stack.reverse stack.length k =
      stack.reverse.drop (stack.length - k) := by
    apply List.ext_getElem
    · simp [childRows]
      omega
    · intro i hiLeft hiRight
      have hi : i < k := by simpa [childRows] using hiLeft
      have hindex : stack.length - k + i < stack.reverse.length := by
        simp
        omega
      simp only [childRows, List.getElem_ofFn, List.getElem_drop]
      rw [List.getD_eq_getElem _ _ hindex]
  rw [hchildDrop, List.drop_reverse]
  congr 2
  omega

theorem collapseRows_reverse (stack : List (List Nat)) (k : Nat)
    (output : List Nat) :
    collapseRows stack.reverse k output = (output :: stack.drop k).reverse := by
  simp [collapseRows, List.reverse_drop]

theorem collapseRows_pushSymbol (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (stack : List CodeString) (symbol : Nat)
    (hk : alphabet.getD symbol 0 ≤ stack.length) :
    collapseRows stack.reverse (alphabet.getD symbol 0)
        (parentStates M symbol
          (childRows stack.reverse stack.length (alphabet.getD symbol 0))) =
      (pushSymbol alphabet M stack symbol).reverse := by
  rw [childRows_reverse stack _ hk]
  simp [collapseRows_reverse, pushSymbol]

/-- Every symbol can consume the required number of stack rows as a word is
evaluated from left to right. -/
def SafeEval (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    CodeString → List CodeString → Prop
  | [], _ => True
  | symbol :: rest, stack =>
      alphabet.getD symbol 0 ≤ stack.length ∧
        SafeEval alphabet M rest (pushSymbol alphabet M stack symbol)

theorem evalWord_cons (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (symbol : Nat) (rest : CodeString) (stack : List CodeString) :
    evalWord alphabet M (symbol :: rest) stack =
      evalWord alphabet M rest (pushSymbol alphabet M stack symbol) := rfl

theorem safeEval_append (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (xs ys : CodeString) (stack : List CodeString)
    (hxs : SafeEval alphabet M xs stack)
    (hys : SafeEval alphabet M ys (evalWord alphabet M xs stack)) :
    SafeEval alphabet M (xs ++ ys) stack := by
  induction xs generalizing stack with
  | nil => simpa [SafeEval, evalWord] using hys
  | cons symbol xs ih =>
      rcases hxs with ⟨hconsume, hsafe⟩
      exact ⟨hconsume, ih _ hsafe (by simpa [evalWord_cons] using hys)⟩

theorem safeEval_forest (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (trees : List (Tree alphabet.toRankedAlphabet))
    (h : ∀ t ∈ trees, ∀ stack, SafeEval alphabet M (encodeTree alphabet t) stack)
    (stack : List CodeString) :
    SafeEval alphabet M (trees.flatMap (encodeTree alphabet)) stack := by
  induction trees generalizing stack with
  | nil => simp [SafeEval]
  | cons t trees ih =>
      rw [List.flatMap_cons]
      apply safeEval_append
      · exact h t (by simp) stack
      · apply ih
        intro u hu s
        exact h u (by simp [hu]) s

theorem safeEval_encodeTree (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (stack : List CodeString) :
    SafeEval alphabet M (encodeTree alphabet t) stack := by
  induction t generalizing stack with
  | node a children ih =>
      rw [encodeTree]
      let forest := List.ofFn children
      have hforest :
          SafeEval alphabet M (forest.flatMap (encodeTree alphabet)) stack :=
        safeEval_forest alphabet M forest (by
          intro u hu s
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
          exact ih i s) stack
      have hflatten :
          List.flatten (List.ofFn fun i => encodeTree alphabet (children i)) =
            forest.flatMap (encodeTree alphabet) := by
        rw [List.flatMap_def]
        simp [forest, List.map_ofFn, Function.comp_def]
      rw [hflatten]
      apply safeEval_append alphabet M _ [a.val] stack hforest
      have heval := evalWord_forest alphabet M forest (by
        intro u hu s
        exact evalWord_encodeTree alphabet M u s) stack
      rw [heval]
      change alphabet.getD a.val 0 ≤
          ((forest.map (reachable alphabet M)).reverse ++ stack).length ∧ True
      constructor
      · rw [alphabet_getD_symbol]
        simp [forest]
      · trivial

/-- Sum of the ranks carried by a word of symbol codes. -/
def rankSum (alphabet : RankedAlphabetCode) (word : CodeString) : Nat :=
  (word.map fun symbol => alphabet.getD symbol 0).sum

theorem rankSum_append (alphabet : RankedAlphabetCode) (xs ys : CodeString) :
    rankSum alphabet (xs ++ ys) = rankSum alphabet xs + rankSum alphabet ys := by
  simp [rankSum, List.map_append, List.sum_append]

theorem rankSum_flatMap_trees (alphabet : RankedAlphabetCode)
    (trees : List (Tree alphabet.toRankedAlphabet)) :
    rankSum alphabet (trees.flatMap (encodeTree alphabet)) =
      (trees.map fun t => rankSum alphabet (encodeTree alphabet t)).sum := by
  induction trees with
  | nil => simp [rankSum]
  | cons t trees ih => simp [rankSum_append, ih]

theorem sum_map_add_one {alpha : Type} (xs : List alpha) (f g : alpha → Nat)
    (h : ∀ x ∈ xs, f x + 1 = g x) :
    (xs.map f).sum + xs.length = (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hx := h x (by simp)
      have htail := ih (fun y hy => h y (by simp [hy]))
      omega

/-- The sum of ranks in a tree's postorder word is one less than its node
count. This is the amortization identity for the outer evaluator loop. -/
theorem rankSum_encodeTree_add_one (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) :
    rankSum alphabet (encodeTree alphabet t) + 1 = treeSize t := by
  induction t with
  | node a children ih =>
      let forest := List.ofFn children
      have hflatten :
          List.flatten (List.ofFn fun i => encodeTree alphabet (children i)) =
            forest.flatMap (encodeTree alphabet) := by
        rw [List.flatMap_def]
        simp [forest, List.map_ofFn, Function.comp_def]
      have hsum :
          (forest.map fun u => rankSum alphabet (encodeTree alphabet u)).sum +
              forest.length =
            (forest.map fun u => treeSize u).sum :=
        sum_map_add_one forest _ _ (by
          intro u hu
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
          exact ih i)
      unfold treeSize
      rw [encodeTree, hflatten, rankSum_append, rankSum_flatMap_trees]
      simp only [rankSum, List.map_singleton, List.sum_singleton,
        List.length_append, List.length_singleton, List.length_flatMap]
      rw [alphabet_getD_symbol]
      have hforestLen : forest.length = alphabet.toRankedAlphabet.rank a := by
        simp [forest]
      have hforestSum :
          (forest.map fun u => treeSize u).sum =
            (List.ofFn fun i => treeSize (children i)).sum := by
        simp [forest, List.map_ofFn, Function.comp_def]
      unfold rankSum at hsum
      omega

end Lax53Proofs.AutomatonRamCorrectness
