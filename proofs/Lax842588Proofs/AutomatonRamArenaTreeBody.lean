import Lax842588Proofs.AutomatonRamArenaTreeDescend

/-!
Verification of one complete structural-tree traversal iteration.  The proof
reads the certified top stack cell and dispatches to the separately verified
finish or descent phase according to the represented child-list constructor.
-/

namespace Lax842588Proofs.AutomatonRamArenaTreeBody

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
open Lax842588Proofs.AutomatonRamArenaTreeFinish
open Lax842588Proofs.AutomatonRamArenaTreeDescend
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- One loop iteration implements exactly one transition of the pure
postorder-traversal model. -/
theorem treeTraversalBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (produced : List Nat) (frame : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (halphabetB : alphabet.length < B) :
    Spec B
      (TreeLoopState B I alphabet tree produced (frame :: outer))
      treeTraversalBody
      (fun _ sigma' =>
        TreeLoopState B I alphabet tree
          (traversalStep alphabet (produced, frame :: outer)).1
          (traversalStep alphabet (produced, frame :: outer)).2 sigma')
      250 := by
  intro sigma hstate
  rcases hstate with
    ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
      hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
      htarget⟩
  obtain ⟨cursor, hsymbol, htail, hcursor⟩ :=
    treeStackRep_current frame outer hstack
  have hframes := TreeLoopState.frames_le_treeSize
    ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
      hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
      htarget⟩
  have htailIndex : outer.length < (sigma.arrs "TreeTailStack").length := by
    simp only [List.length_cons] at hframes
    omega
  have htailGet : (sigma.arrs "TreeTailStack")[outer.length]? = some cursor := by
    rw [List.getElem?_eq_getElem htailIndex]
    rw [← List.getD_eq_getElem (sigma.arrs "TreeTailStack") 0 htailIndex]
    exact congrArg some htail
  have hcursorValid := Lax842588Proofs.ArenaSemantics.Represents.valid hcursor
  have hcursorLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hcursorValid
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hcursorB : cursor < B := by omega
  have hdepthB : (frame :: outer).length < B := by
    omega
  cases frame with
  | mk symbol rest =>
      cases rest with
      | nil =>
          have htag :=
            Lax842588Proofs.ArenaSemantics.Represents.fields_nil hcursor
          have htagGet : (arenaWords I)[cursor]? = some WordImage.natTag := by
            rw [List.getElem?_eq_getElem (by omega)]
            rw [← List.getD_eq_getElem (arenaWords I) 0 (by omega)]
            exact congrArg some htag
          have hfinish := finishTreeNode_spec B I alphabet tree produced
            symbol outer halphabetB
          have hcore : Spec B (fun tau => tau = sigma) treeTraversalBody
              (fun _ sigma' => TreeLoopState B I alphabet tree
                (produced ++ [symbol.val]) outer sigma') 250 := by
            unfold treeTraversalBody
              Lax842588Proofs.AutomatonRamProgram.seqs
            run_vcg [hfinish]
            all_goals simp_all [TreeLoopState, ArenaLoaded,
              WordImage.natTag]
            all_goals (try omega)
          obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
          exact ⟨sigma', hrun, by simpa [traversalStep] using hpost⟩
      | cons child rest =>
          obtain ⟨childAddress, restAddress, htag, hchildWord, hrestWord,
              hchildRep, hrestRep⟩ :=
            Lax842588Proofs.ArenaSemantics.Represents.fields_cons hcursor
          have htagGet : (arenaWords I)[cursor]? = some WordImage.pairTag := by
            rw [List.getElem?_eq_getElem (by omega)]
            rw [← List.getD_eq_getElem (arenaWords I) 0 (by omega)]
            exact congrArg some htag
          have hdescend := descendTreeNode_spec B I alphabet tree produced
            symbol child rest outer cursor h1 hmemB hvaluesB
          have hcore : Spec B (fun tau => tau = sigma) treeTraversalBody
              (fun _ sigma' => TreeLoopState B I alphabet tree produced
                (initialFrame alphabet child :: ⟨symbol, rest⟩ :: outer)
                sigma') 250 := by
            unfold treeTraversalBody
              Lax842588Proofs.AutomatonRamProgram.seqs
            run_vcg [hdescend]
            all_goals simp_all [TreeLoopState, ArenaLoaded,
              WordImage.pairTag]
            all_goals (try omega)
          obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
          exact ⟨sigma', hrun, by simpa [traversalStep] using hpost⟩

end Lax842588Proofs.AutomatonRamArenaTreeBody
