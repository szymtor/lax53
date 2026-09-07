import Lax53Proofs.AutomatonRamArenaReadAccepting

/-!
Pure mathematical model of the explicit depth-first traversal used by the
charged arena frontend. Costs are not assigned to these definitions; they
serve only as the semantic invariant for the verified IMP+ loop.
-/

namespace Lax53Proofs.AutomatonRamArenaTreeModel

open Lax53.RankedTree
open Lax53.ValueTranslations
open Lax53.TreeModelCheckingEncoding

/-- One active tree node, together with the ordered children still awaiting
traversal. Frames are listed from the innermost/current node outward. -/
structure TraversalFrame (alphabet : RankedAlphabetCode) where
  symbol : Fin alphabet.length
  rest : List (Tree alphabet.toRankedAlphabet)

/-- Postorder word of an ordered forest. -/
def forestWord (alphabet : RankedAlphabetCode)
    (trees : List (Tree alphabet.toRankedAlphabet)) : List Nat :=
  trees.flatMap (encodeTree alphabet)

@[simp] theorem forestWord_length (alphabet : RankedAlphabetCode)
    (trees : List (Tree alphabet.toRankedAlphabet)) :
    (forestWord alphabet trees).length = (trees.map treeSize).sum := by
  simp [forestWord, encodeTree_length]

/-- Output still owed by one active frame. -/
def framePending (alphabet : RankedAlphabetCode)
    (frame : TraversalFrame alphabet) : List Nat :=
  forestWord alphabet frame.rest ++ [frame.symbol.val]

/-- Output still owed by the current frame and then each enclosing frame. -/
def pending (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) : List Nat :=
  frames.flatMap (framePending alphabet)

/-- Initial frame obtained by opening a mathematical tree node. -/
def initialFrame (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet) : TraversalFrame alphabet :=
  match tree with
  | .node symbol children => ⟨symbol, List.ofFn children⟩

/-- One pure traversal transition. The imperative loop implements this
function with its two branches. -/
def traversalStep (alphabet : RankedAlphabetCode)
    (state : List Nat × List (TraversalFrame alphabet)) :
    List Nat × List (TraversalFrame alphabet) :=
  match state.2 with
  | [] => state
  | ⟨symbol, []⟩ :: outer => (state.1 ++ [symbol.val], outer)
  | ⟨symbol, child :: rest⟩ :: outer =>
      (state.1, initialFrame alphabet child :: ⟨symbol, rest⟩ :: outer)

/-- Exact number of remaining loop iterations represented by one frame. -/
def frameWork (alphabet : RankedAlphabetCode)
    (frame : TraversalFrame alphabet) : Nat :=
  1 + 2 * (frame.rest.map treeSize).sum

/-- Exact number of remaining loop iterations in a nonempty traversal stack. -/
def traversalWork (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) : Nat :=
  (frames.map (frameWork alphabet)).sum

/-- The traversal work is twice the number of pending output symbols, less
one unit for every already-open frame. -/
theorem traversalWork_add_depth (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) :
    traversalWork alphabet frames + frames.length =
      2 * (pending alphabet frames).length := by
  induction frames with
  | nil => simp [traversalWork, pending]
  | cons frame frames ih =>
      rcases frame with ⟨symbol, rest⟩
      simp [traversalWork, pending, frameWork, framePending] at ih ⊢
      omega

theorem encodeTree_eq_forest (alphabet : RankedAlphabetCode)
    (symbol : Fin alphabet.length)
    (children : Fin (alphabet.toRankedAlphabet.rank symbol) →
      Tree alphabet.toRankedAlphabet) :
    encodeTree alphabet (.node symbol children) =
      forestWord alphabet (List.ofFn children) ++ [symbol.val] := by
  simp [encodeTree, forestWord, List.flatMap_def, List.map_ofFn,
    Function.comp_def]

@[simp] theorem framePending_initial (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet) :
    framePending alphabet (initialFrame alphabet tree) =
      encodeTree alphabet tree := by
  cases tree with
  | node symbol children =>
      exact (encodeTree_eq_forest alphabet symbol children).symm

@[simp] theorem pending_initial (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet) :
    pending alphabet [initialFrame alphabet tree] = encodeTree alphabet tree := by
  simp [pending]

theorem traversalStep_preserves_pending (alphabet : RankedAlphabetCode)
    (produced : List Nat) (frames : List (TraversalFrame alphabet)) :
    (traversalStep alphabet (produced, frames)).1 ++
        pending alphabet (traversalStep alphabet (produced, frames)).2 =
      produced ++ pending alphabet frames := by
  cases frames with
  | nil => simp [traversalStep, pending]
  | cons frame outer =>
      cases frame with
      | mk symbol rest =>
          cases rest with
          | nil => simp [traversalStep, pending, framePending,
              forestWord, List.append_assoc]
          | cons child rest =>
              simp only [traversalStep, pending, List.flatMap_cons]
              rw [framePending_initial]
              simp [framePending, forestWord, List.append_assoc]

theorem traversalStep_preserves_target (alphabet : RankedAlphabetCode)
    (target produced : List Nat) (frames : List (TraversalFrame alphabet))
    (hinv : produced ++ pending alphabet frames = target) :
    (traversalStep alphabet (produced, frames)).1 ++
        pending alphabet (traversalStep alphabet (produced, frames)).2 = target := by
  rw [traversalStep_preserves_pending]
  exact hinv

theorem initialFrame_work (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet) :
    frameWork alphabet (initialFrame alphabet tree) + 1 = 2 * treeSize tree := by
  cases tree with
  | node symbol children =>
      simp [frameWork, initialFrame, treeSize, List.map_ofFn,
        Function.comp_def]
      omega

theorem traversalStep_work (alphabet : RankedAlphabetCode)
    (produced : List Nat) (frame : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) :
    traversalWork alphabet
        (traversalStep alphabet (produced, frame :: outer)).2 + 1 =
      traversalWork alphabet (frame :: outer) := by
  cases frame with
  | mk symbol rest =>
      cases rest with
      | nil => simp [traversalStep, traversalWork, frameWork, Nat.add_comm]
      | cons child rest =>
          cases child with
          | node childSymbol childChildren =>
              simp [traversalStep, traversalWork, frameWork, initialFrame,
                treeSize, List.map_ofFn, Function.comp_def]
              omega

theorem traversalStep_decreases (alphabet : RankedAlphabetCode)
    (produced : List Nat) (frame : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) :
    traversalWork alphabet
        (traversalStep alphabet (produced, frame :: outer)).2 <
      traversalWork alphabet (frame :: outer) := by
  have h := traversalStep_work alphabet produced frame outer
  omega

theorem completed_eq_target (alphabet : RankedAlphabetCode)
    (target produced : List Nat)
    (hinv : produced ++ pending alphabet [] = target) :
    produced = target := by
  simpa [pending] using hinv

end Lax53Proofs.AutomatonRamArenaTreeModel
