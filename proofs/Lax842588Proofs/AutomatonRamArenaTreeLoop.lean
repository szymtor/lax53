import Lax842588Proofs.AutomatonRamArenaTreeBody

/-!
Counted-loop verification for the complete postorder traversal of a certified
ranked-tree arena.
-/

namespace Lax842588Proofs.AutomatonRamArenaTreeLoop

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.AutomatonRamArenaTreeModel
open Lax842588Proofs.AutomatonRamArenaTreeInvariant
open Lax842588Proofs.AutomatonRamArenaTreeBody
open Lax560851.WordArena

/-- An environment-only form of the exact remaining traversal work.  Under
`TreeLoopState` it equals `traversalWork` for the represented logical stack. -/
def treePotential (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet) (sigma : Env) : Nat :=
  2 * (treeSize tree - sigma.vars "n") - sigma.vars "treeDepth"

theorem TreeLoopState.potential_eq {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode} {tree : Tree alphabet.toRankedAlphabet}
    {produced : List Nat} {frames : List (TraversalFrame alphabet)}
    {sigma : Env} (h : TreeLoopState B I alphabet tree produced frames sigma) :
    treePotential alphabet tree sigma = traversalWork alphabet frames := by
  have hlength := h.target_length
  have hwork := traversalWork_add_depth alphabet frames
  rcases h with
    ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
      hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
      htarget⟩
  unfold treePotential
  rw [hn, hdepth]
  omega

private theorem treeTraversalBody_decreases (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (halphabetB : alphabet.length < B) :
    Spec B
      (fun sigma => TreeLoopInv B I alphabet tree sigma ∧
        treeLoopCondition.evalB B sigma = some true)
      treeTraversalBody
      (fun sigma sigma' =>
        TreeLoopInv B I alphabet tree sigma' ∧
          treePotential alphabet tree sigma' < treePotential alphabet tree sigma)
      250 := by
  intro sigma hpre
  rcases hpre.1 with ⟨produced, frames, hstate⟩
  have hcondition := treeLoopCondition_value B I alphabet tree produced frames
    sigma hstate
  cases frames with
  | nil =>
      have hfalse : treeLoopCondition.evalB B sigma = some false := by
        simpa using hcondition
      rw [hpre.2] at hfalse
      contradiction
  | cons frame outer =>
      have hbody := treeTraversalBody_spec B I alphabet tree produced frame outer
        h1 hmemB hvaluesB halphabetB
      obtain ⟨sigma', hrun, hstate'⟩ := hbody.run hstate
      refine ⟨sigma', hrun,
        ⟨(traversalStep alphabet (produced, frame :: outer)).1,
          (traversalStep alphabet (produced, frame :: outer)).2, hstate'⟩,
        ?_⟩
      rw [TreeLoopState.potential_eq hstate,
        TreeLoopState.potential_eq hstate']
      exact traversalStep_decreases alphabet produced frame outer

/-- Conservative total cost for the exact `2 * treeSize - 1` traversal
steps, rounded up to `2 * treeSize`. -/
def treeTraversalLoopCost (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet) : Nat :=
  (1 + treeLoopCondition.size + 250) * (2 * treeSize tree) +
    1 + treeLoopCondition.size

theorem treeTraversalLoop_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (halphabetB : alphabet.length < B) :
    Spec B (TreeLoopInv B I alphabet tree) treeTraversalLoop
      (fun _ sigma' =>
        TreeLoopInv B I alphabet tree sigma' ∧
          treeLoopCondition.evalB B sigma' = some false)
      (treeTraversalLoopCost alphabet tree) := by
  unfold treeTraversalLoop treeTraversalLoopCost
  refine Spec.while_count
    (TreeLoopInv B I alphabet tree)
    (treePotential alphabet tree) 250
    (treeLoopCondition_defined B I alphabet tree)
    (treeTraversalBody_decreases B I alphabet tree h1 hmemB hvaluesB
      halphabetB)
    (fun _ hInv => hInv) ?_
  intro sigma hInv
  have hpotential : treePotential alphabet tree sigma ≤ 2 * treeSize tree := by
    unfold treePotential
    omega
  have hmul := Nat.mul_le_mul_left
    (1 + treeLoopCondition.size + 250) hpotential
  simpa only [Nat.add_assoc] using
    Nat.add_le_add_right hmul (1 + treeLoopCondition.size)

/-- On loop exit the postorder word is complete and the logical traversal
stack is empty. -/
theorem treeTraversalLoop_completed_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (halphabetB : alphabet.length < B) :
    Spec B (TreeLoopInv B I alphabet tree) treeTraversalLoop
      (fun _ sigma' =>
        TreeLoopInv B I alphabet tree sigma' ∧
          sigma'.vars "n" = treeSize tree ∧
          sigma'.vars "treeDepth" = 0 ∧
          WordsAt (sigma'.arrs "W") 0 (encodeTree alphabet tree))
      (treeTraversalLoopCost alphabet tree) := by
  refine (treeTraversalLoop_spec B I alphabet tree h1 hmemB hvaluesB
    halphabetB).post ?_
  intro sigma sigma' hpre hpost
  rcases hpost.1 with ⟨produced, frames, hstate⟩
  have hcondition := treeLoopCondition_value B I alphabet tree produced frames
    sigma' hstate
  have hempty : frames = [] := by
    cases frames with
    | nil => rfl
    | cons frame outer =>
        have htrue : treeLoopCondition.evalB B sigma' = some true := by
          simpa using hcondition
        rw [hpost.2] at htrue
        contradiction
  subst frames
  rcases hstate with
    ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
      hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
      htarget⟩
  have hproduced : produced = encodeTree alphabet tree :=
    completed_eq_target alphabet (encodeTree alphabet tree) produced htarget
  subst produced
  refine ⟨⟨encodeTree alphabet tree, [], hloaded, hTreeB, hTreeW,
      hTreeSymbolStack, hTreeTailStack, hWB, hSymbolStackB, hTailStackB,
      hn, hdepth, hWords, hstack, htarget⟩, ?_, ?_, hWords⟩
  · simpa [encodeTree_length] using hn
  · simpa using hdepth

end Lax842588Proofs.AutomatonRamArenaTreeLoop
