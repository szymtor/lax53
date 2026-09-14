import Lax842588Proofs.AutomatonRamArenaTreeFinish

/-!
Verification of the descent branch of the charged structural-tree traversal.
It advances the current frame's represented child-list cursor and then reuses
the separately verified node-opening routine to push the child.
-/

namespace Lax842588Proofs.AutomatonRamArenaTreeDescend

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
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- Descending consumes one represented child-list cell, replaces the current
frame by its tail, and pushes the represented child node. -/
theorem descendTreeNode_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (produced : List Nat) (symbol : Fin alphabet.length)
    (child : Tree alphabet.toRankedAlphabet)
    (rest : List (Tree alphabet.toRankedAlphabet))
    (outer : List (TraversalFrame alphabet)) (cursor : Nat)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B
      (fun sigma =>
        TreeLoopState B I alphabet tree produced
            (⟨symbol, child :: rest⟩ :: outer) sigma ∧
          sigma.vars "treeIndex" = outer.length ∧
          sigma.vars "childCursor" = cursor ∧
          I.Represents cursor
            (Raw.fields ((child :: rest).map (treeStructure alphabet))))
      descendTreeNode
      (fun _ sigma' =>
        TreeLoopState B I alphabet tree produced
          (initialFrame alphabet child :: ⟨symbol, rest⟩ :: outer) sigma')
      150 := by
  intro sigma hpre
  rcases hpre.1 with
    ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
      hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
      htarget⟩
  obtain ⟨childAddress, restAddress, hcursorTag, hchildWord, hrestWord,
      hchildRep, hrestRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.fields_cons hpre.2.2.2
  have hcursorValid :=
    Lax842588Proofs.ArenaSemantics.Represents.valid hpre.2.2.2
  have hchildValid :=
    Lax842588Proofs.ArenaSemantics.Represents.valid hchildRep
  have hrestValid :=
    Lax842588Proofs.ArenaSemantics.Represents.valid hrestRep
  have hcursorLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hcursorValid
  have hchildLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hchildValid
  have hrestLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hrestValid
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hgetB (i : Nat) : (arenaWords I).getD i 0 < B :=
    Lax842588Proofs.AutomatonRamCorrectness.getD_lt_of_mem_bound
      (by omega) hvaluesB
  have hgetOptB (i : Nat) : ((arenaWords I)[i]?).getD 0 < B := by
    simpa [List.getD_eq_getElem?_getD] using hgetB i
  have hchildGetD : ((arenaWords I)[cursor + 1]?).getD 0 = childAddress := by
    simpa [List.getD_eq_getElem?_getD] using hchildWord
  have hrestGetD : ((arenaWords I)[cursor + 2]?).getD 0 = restAddress := by
    simpa [List.getD_eq_getElem?_getD] using hrestWord
  have hchildGetDB := hgetOptB (cursor + 1)
  have hrestGetDB := hgetOptB (cursor + 2)
  have htailSpace : outer.length < (sigma.arrs "TreeTailStack").length := by
    have hframes := TreeLoopState.frames_le_treeSize
      ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
        hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
        htarget⟩
    simp only [List.length_cons] at hframes
    omega
  have hframesLtTree :
      (⟨symbol, child :: rest⟩ :: outer : List (TraversalFrame alphabet)).length <
        treeSize tree :=
    TreeLoopState.stack_has_space_for_child
      ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
        hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
        htarget⟩
  have hsymbolSpace :
      (⟨symbol, rest⟩ :: outer : List (TraversalFrame alphabet)).length <
        (sigma.arrs "TreeSymbolStack").length := by
    simp only [List.length_cons] at hframesLtTree ⊢
    omega
  have htailPushSpace :
      (⟨symbol, rest⟩ :: outer : List (TraversalFrame alphabet)).length <
        (sigma.arrs "TreeTailStack").length := by
    simp only [List.length_cons] at hframesLtTree ⊢
    omega
  have hparentStack : TreeStackRep I alphabet (⟨symbol, rest⟩ :: outer)
      (sigma.arrs "TreeSymbolStack")
      ((sigma.arrs "TreeTailStack").set outer.length restAddress) :=
    treeStackRep_replaceCurrent restAddress hstack hrestRep htailSpace
  have hpush := (pushTreeNode_spec B I alphabet child
    (⟨symbol, rest⟩ :: outer) h1 hmemB hvaluesB).frame
  have hcore : Spec B (fun tau => tau = sigma) descendTreeNode
      (fun _ sigma' => TreePushed B I alphabet child
        (⟨symbol, rest⟩ :: outer) sigma') 150 := by
    unfold descendTreeNode Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg [hpush]
    all_goals simp_all [TreePushReady, ArenaLoaded]
    all_goals (try omega)
  obtain ⟨sigma', hrun, hpushed⟩ := hcore.frame.run rfl
  rcases hpushed.1 with
    ⟨hloaded', hdepth', hSymbolStackB', hTailStackB', hstack'⟩
  have hWfinal : sigma'.arrs "W" = sigma.arrs "W" :=
    hpushed.2.2.1 "W" (by decide)
  have hnfinal : sigma'.vars "n" = sigma.vars "n" :=
    hpushed.2.1 "n" (by decide)
  have hWlength := Lax842588Proofs.Run.arrayLength_eq hrun "W"
  have hSymbolLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun "TreeSymbolStack"
  have hTailLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun "TreeTailStack"
  have htarget' := traversalStep_preserves_target alphabet
    (encodeTree alphabet tree) produced
    (⟨symbol, child :: rest⟩ :: outer) htarget
  refine ⟨sigma', hrun, hloaded', hTreeB, ?_, ?_, ?_, ?_,
    hSymbolStackB', hTailStackB', ?_, hdepth', ?_, hstack', ?_⟩
  · rwa [hWlength]
  · rwa [hSymbolLength]
  · rwa [hTailLength]
  · rwa [hWlength]
  · exact hnfinal.trans hn
  · rwa [hWfinal]
  · simpa [traversalStep] using htarget'

end Lax842588Proofs.AutomatonRamArenaTreeDescend
