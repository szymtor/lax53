import Lax842588Proofs.AutomatonRamArenaTreeInvariant

/-!
Verification of the leaf/finished-node branch of the charged structural-tree
traversal.  The physical traversal stacks need not be cleared when their
logical occupied prefix shrinks.
-/

namespace Lax842588Proofs.AutomatonRamArenaTreeFinish

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.AutomatonRamArenaTreeModel
open Lax842588Proofs.AutomatonRamArenaTreeStack
open Lax842588Proofs.AutomatonRamArenaTreeInvariant
open Lax560851.WordArena

/-- Finishing a frame with no remaining children appends precisely its symbol
to the postorder word and pops the logical traversal stack. -/
theorem finishTreeNode_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (produced : List Nat) (symbol : Fin alphabet.length)
    (outer : List (TraversalFrame alphabet))
    (halphabetB : alphabet.length < B) :
    Spec B
      (fun sigma =>
        TreeLoopState B I alphabet tree produced (⟨symbol, []⟩ :: outer) sigma ∧
          sigma.vars "treeIndex" = outer.length)
      finishTreeNode
      (fun _ sigma' =>
        TreeLoopState B I alphabet tree (produced ++ [symbol.val]) outer sigma')
      50 := by
  intro sigma hpre
  rcases hpre.1 with
    ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
      hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
      htarget⟩
  have hproducedLt : produced.length < treeSize tree :=
    TreeLoopState.produced_lt_of_nonempty
      ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
        hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
        htarget⟩
  have hWslot : produced.length < (sigma.arrs "W").length := by
    omega
  obtain ⟨cursor, hsymbol, htail, hcursor⟩ :=
    treeStackRep_current (current := (⟨symbol, []⟩ : TraversalFrame alphabet))
      outer hstack
  have hindex : outer.length < (sigma.arrs "TreeSymbolStack").length := by
    have hframes := TreeLoopState.frames_le_treeSize
      ⟨hloaded, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
        hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
        htarget⟩
    simp only [List.length_cons] at hframes
    omega
  have hsymbolGet : (sigma.arrs "TreeSymbolStack")[outer.length]? =
      some symbol.val := by
    rw [List.getElem?_eq_getElem hindex]
    rw [← List.getD_eq_getElem (sigma.arrs "TreeSymbolStack") 0 hindex]
    exact congrArg some hsymbol
  have hWords' : WordsAt
      ((sigma.arrs "W").set produced.length symbol.val) 0
      (produced ++ [symbol.val]) := by
    simpa using wordsAt_set_append (value := symbol.val) hWords
      (by simpa using hWslot)
  have hstack' : TreeStackRep I alphabet outer
      (sigma.arrs "TreeSymbolStack") (sigma.arrs "TreeTailStack") :=
    treeStackRep_pop hstack
  have htarget' :
      (produced ++ [symbol.val]) ++ pending alphabet outer =
        encodeTree alphabet tree := by
    simpa [pending, framePending, forestWord, List.append_assoc] using htarget
  unfold finishTreeNode Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [TreeLoopState, ArenaLoaded]
  all_goals (try omega)

end Lax842588Proofs.AutomatonRamArenaTreeFinish
