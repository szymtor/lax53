import Lax842588Proofs.AutomatonRamArenaTreeLoop

/-!
Initialization and completion of the charged structural-tree reader.
-/

namespace Lax842588Proofs.AutomatonRamArenaReadTree

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.AutomatonRamArenaTreeModel
open Lax842588Proofs.AutomatonRamArenaTreeStack
open Lax842588Proofs.AutomatonRamArenaTreeInvariant
open Lax842588Proofs.AutomatonRamArenaTreeLoop
open Lax560851.WordArena

/-- Preconditions supplied by the already-opened structural instance and the
proof-private workspace allocation. -/
def TreeReadReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (root : Nat) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "treeRoot" = root ∧
    I.Represents root (treeStructure alphabet tree) ∧
    treeSize tree < B ∧
    alphabet.length < B ∧
    treeSize tree ≤ (sigma.arrs "W").length ∧
    treeSize tree ≤ (sigma.arrs "TreeSymbolStack").length ∧
    treeSize tree ≤ (sigma.arrs "TreeTailStack").length ∧
    (sigma.arrs "W").length < B ∧
    (sigma.arrs "TreeSymbolStack").length < B ∧
    (sigma.arrs "TreeTailStack").length < B

/-- Initialize `n`, the physical stack depth, and the root frame. -/
theorem initializeTreeTraversal_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (root : Nat) (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B (TreeReadReady B I alphabet tree root) initializeTreeTraversal
      (fun _ sigma' => TreeLoopInv B I alphabet tree sigma') 120 := by
  intro sigma hready
  rcases hready with
    ⟨hloaded, htreeRoot, htreeRep, hTreeB, halphabetB, hTreeW,
      hTreeSymbolStack, hTreeTailStack, hWB, hSymbolStackB, hTailStackB⟩
  have hrootValid := Lax842588Proofs.ArenaSemantics.Represents.valid htreeRep
  have hrootLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hrootValid
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hrootB : root < B := by omega
  have hstackEmpty : TreeStackRep I alphabet []
      (sigma.arrs "TreeSymbolStack") (sigma.arrs "TreeTailStack") := by
    exact ⟨[], .nil, by simp [frameSymbols, WordsAt], by simp [WordsAt]⟩
  have hsymbolSpace : 0 < (sigma.arrs "TreeSymbolStack").length := by
    have := treeSize_pos tree
    omega
  have htailSpace : 0 < (sigma.arrs "TreeTailStack").length := by
    have := treeSize_pos tree
    omega
  have hpush := (pushTreeNode_spec B I alphabet tree [] h1 hmemB
    hvaluesB).frame
  have hpushN : Spec B
      (fun tau => TreePushReady B I alphabet tree [] tau ∧
        tau.vars "n" = 0)
      pushTreeNode
      (fun _ sigma' => TreePushed B I alphabet tree [] sigma' ∧
        sigma'.vars "n" = 0) 100 := by
    refine hpush.conseq (fun _ h => h.1) ?_ le_rfl
    intro tau tau' hpre hpost
    exact ⟨hpost.1, (hpost.2.1 "n" (by decide)).trans hpre.2⟩
  have hcore : Spec B (fun tau => tau = sigma) initializeTreeTraversal
      (fun _ sigma' => TreePushed B I alphabet tree [] sigma' ∧
        sigma'.vars "n" = 0) 120 := by
    unfold initializeTreeTraversal
    run_vcg [hpushN]
    all_goals simp_all [TreePushReady, ArenaLoaded]
  obtain ⟨sigma', hrun, hpost⟩ := hcore.frame.run rfl
  rcases hpost.1.1 with
    ⟨hloaded', hdepth', hSymbolStackB', hTailStackB', hstack'⟩
  have hWfinal : sigma'.arrs "W" = sigma.arrs "W" :=
    hpost.2.2.1 "W" (by decide)
  have hWlength := Lax842588Proofs.Run.arrayLength_eq hrun "W"
  have hSymbolLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun "TreeSymbolStack"
  have hTailLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun "TreeTailStack"
  refine ⟨sigma', hrun, [], [initialFrame alphabet tree], hloaded',
    hTreeB, ?_, ?_, ?_, ?_, hSymbolStackB', hTailStackB', ?_, hdepth',
    ?_, hstack', ?_⟩
  · rwa [hWlength]
  · rwa [hSymbolLength]
  · rwa [hTailLength]
  · rwa [hWlength]
  · simpa using hpost.1.2
  · simp [WordsAt]
  · simp [pending_initial]

/-- Complete cost of initializing and traversing the represented tree. -/
def readTreeCost (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet) : Nat :=
  120 + treeTraversalLoopCost alphabet tree + 1

/-- `readTree` materializes exactly the old evaluator's postorder symbol word
from the certified tree presentation, with the traversal cost charged. -/
theorem readTree_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (root : Nat) (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (halphabetB : alphabet.length < B) :
    Spec B (TreeReadReady B I alphabet tree root) readTree
      (fun _ sigma' =>
        TreeLoopInv B I alphabet tree sigma' ∧
          sigma'.vars "n" = treeSize tree ∧
          sigma'.vars "treeDepth" = 0 ∧
          WordsAt (sigma'.arrs "W") 0 (encodeTree alphabet tree))
      (readTreeCost alphabet tree) := by
  have hinit := initializeTreeTraversal_spec B I alphabet tree root h1 hmemB
    hvaluesB
  have hloop := treeTraversalLoop_completed_spec B I alphabet tree h1 hmemB
    hvaluesB halphabetB
  have hloop' : Spec B (TreeLoopInv B I alphabet tree)
      (.while treeLoopCondition treeTraversalBody)
      (fun _ sigma' =>
        TreeLoopInv B I alphabet tree sigma' ∧
          sigma'.vars "n" = treeSize tree ∧
          sigma'.vars "treeDepth" = 0 ∧
          WordsAt (sigma'.arrs "W") 0 (encodeTree alphabet tree))
      (treeTraversalLoopCost alphabet tree) := by
    simpa [treeTraversalLoop, treeLoopCondition] using hloop
  unfold readTree readTreeCost
  run_vcg [hinit, hloop']
  all_goals assumption

end Lax842588Proofs.AutomatonRamArenaReadTree
