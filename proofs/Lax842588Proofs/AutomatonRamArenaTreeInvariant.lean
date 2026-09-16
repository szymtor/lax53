import Lax842588Proofs.AutomatonRamArenaTreeStack

/-!
Semantic invariant connecting the produced postorder prefix, the certified
physical traversal stack, and the pure pending-output model.
-/

namespace Lax842588Proofs.AutomatonRamArenaTreeInvariant

set_option maxHeartbeats 3000000
open Classical

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
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
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

theorem treeSize_pos {alphabet : RankedAlphabetCode}
    (tree : Tree alphabet.toRankedAlphabet) : 0 < treeSize tree := by
  cases tree
  simp [treeSize]

theorem pending_length_ge_frames (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) :
    frames.length ≤ (pending alphabet frames).length := by
  induction frames with
  | nil => simp [pending]
  | cons frame frames ih =>
      simp [pending, framePending]
      omega

theorem pending_length_gt_frames_of_child (alphabet : RankedAlphabetCode)
    (symbol : Fin alphabet.length)
    (child : Tree alphabet.toRankedAlphabet)
    (rest : List (Tree alphabet.toRankedAlphabet))
    (outer : List (TraversalFrame alphabet)) :
    (⟨symbol, child :: rest⟩ :: outer : List (TraversalFrame alphabet)).length <
      (pending alphabet (⟨symbol, child :: rest⟩ :: outer)).length := by
  have houter := pending_length_ge_frames alphabet outer
  have hchild := treeSize_pos child
  simp [pending, framePending, forestWord, encodeTree_length]
  omega

/-- Reading the last occupied physical stack cell yields the current logical
frame and its certified remaining-child cursor. -/
theorem treeStackRep_current {I : WordImage}
    {alphabet : RankedAlphabetCode} (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet))
    {symbolStack tailStack : List Nat}
    (hstack : TreeStackRep I alphabet (current :: outer)
      symbolStack tailStack) :
    ∃ cursor,
      symbolStack.getD outer.length 0 = current.symbol.val ∧
      tailStack.getD outer.length 0 = cursor ∧
      I.Represents cursor
        (Raw.fields (current.rest.map (treeStructure alphabet))) := by
  rcases hstack with ⟨cursors, hcursors, hsymbols, htails⟩
  cases hcursors with
  | @cons cursor representedFrame outerCursors representedOuter hcursor houter =>
      have hcursorLength := houter.length_eq
      have hsymbol := hsymbols outer.length (by simp [frameSymbols])
      have htail := htails outer.length (by simp [hcursorLength])
      refine ⟨cursor, ?_, ?_, hcursor⟩
      · simpa [frameSymbols, List.reverse_cons, List.map_append] using hsymbol
      · simpa [List.reverse_cons, hcursorLength] using htail

/-- A fully related imperative/pure traversal state. -/
def TreeLoopState (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (produced : List Nat) (frames : List (TraversalFrame alphabet))
    (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    treeSize tree < B ∧
    treeSize tree ≤ (sigma.arrs "W").length ∧
    treeSize tree ≤ (sigma.arrs "TreeSymbolStack").length ∧
    treeSize tree ≤ (sigma.arrs "TreeTailStack").length ∧
    (sigma.arrs "W").length < B ∧
    (sigma.arrs "TreeSymbolStack").length < B ∧
    (sigma.arrs "TreeTailStack").length < B ∧
    sigma.vars "n" = produced.length ∧
    sigma.vars "treeDepth" = frames.length ∧
    WordsAt (sigma.arrs "W") 0 produced ∧
    TreeStackRep I alphabet frames
      (sigma.arrs "TreeSymbolStack") (sigma.arrs "TreeTailStack") ∧
    produced ++ pending alphabet frames = encodeTree alphabet tree

def TreeLoopInv (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (sigma : Env) : Prop :=
  ∃ produced frames, TreeLoopState B I alphabet tree produced frames sigma

theorem TreeLoopState.target_length {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode} {tree : Tree alphabet.toRankedAlphabet}
    {produced : List Nat} {frames : List (TraversalFrame alphabet)}
    {sigma : Env} (h : TreeLoopState B I alphabet tree produced frames sigma) :
    produced.length + (pending alphabet frames).length = treeSize tree := by
  have hlength := congrArg List.length h.2.2.2.2.2.2.2.2.2.2.2.2
  simpa [encodeTree_length] using hlength

theorem TreeLoopState.frames_le_treeSize {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode} {tree : Tree alphabet.toRankedAlphabet}
    {produced : List Nat} {frames : List (TraversalFrame alphabet)}
    {sigma : Env} (h : TreeLoopState B I alphabet tree produced frames sigma) :
    frames.length ≤ treeSize tree := by
  have hpending := pending_length_ge_frames alphabet frames
  have hlength := h.target_length
  omega

theorem TreeLoopState.produced_lt_of_nonempty {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode} {tree : Tree alphabet.toRankedAlphabet}
    {produced : List Nat} {frame : TraversalFrame alphabet}
    {outer : List (TraversalFrame alphabet)} {sigma : Env}
    (h : TreeLoopState B I alphabet tree produced (frame :: outer) sigma) :
    produced.length < treeSize tree := by
  have hpending := pending_length_ge_frames alphabet (frame :: outer)
  have hlength := h.target_length
  simp only [List.length_cons] at hpending
  omega

theorem TreeLoopState.stack_has_space_for_child {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode} {tree : Tree alphabet.toRankedAlphabet}
    {produced : List Nat} {symbol : Fin alphabet.length}
    {child : Tree alphabet.toRankedAlphabet}
    {rest : List (Tree alphabet.toRankedAlphabet)}
    {outer : List (TraversalFrame alphabet)} {sigma : Env}
    (h : TreeLoopState B I alphabet tree produced
      (⟨symbol, child :: rest⟩ :: outer) sigma) :
    (⟨symbol, child :: rest⟩ :: outer : List (TraversalFrame alphabet)).length <
      treeSize tree := by
  have hpending := pending_length_gt_frames_of_child alphabet symbol child rest outer
  have hlength := h.target_length
  omega

/-- Proof-local name for the concrete nonempty-stack loop guard. -/
def treeLoopCondition : Cond := .lt (.lit 0) (.var "treeDepth")

theorem treeLoopCondition_value (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet)
    (produced : List Nat) (frames : List (TraversalFrame alphabet))
    (sigma : Env)
    (hstate : TreeLoopState B I alphabet tree produced frames sigma) :
    treeLoopCondition.evalB B sigma = some (!frames.isEmpty) := by
  rcases hstate with
    ⟨hArena, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
      hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack, htarget⟩
  have hdepthB : frames.length < B :=
    (TreeLoopState.frames_le_treeSize
      ⟨hArena, hTreeB, hTreeW, hTreeSymbolStack, hTreeTailStack,
        hWB, hSymbolStackB, hTailStackB, hn, hdepth, hWords, hstack,
        htarget⟩).trans_lt hTreeB
  have hvar : (Expr.var "treeDepth").evalB B sigma = some frames.length := by
    rw [evalB_var_iff]
    exact ⟨hdepth.symm, by simpa [hdepth] using hdepthB⟩
  cases frames with
  | nil =>
      simpa [treeLoopCondition] using
        (evalB_condLt (evalB_lit (by omega : 0 < B)) hvar)
  | cons frame outer =>
      simpa [treeLoopCondition] using
        (evalB_condLt (evalB_lit (by omega : 0 < B)) hvar)

theorem treeLoopCondition_defined (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (tree : Tree alphabet.toRankedAlphabet) :
    ∀ sigma, TreeLoopInv B I alphabet tree sigma →
      ∃ value, treeLoopCondition.evalB B sigma = some value := by
  intro sigma hInv
  rcases hInv with ⟨produced, frames, hstate⟩
  exact ⟨!frames.isEmpty,
    treeLoopCondition_value B I alphabet tree produced frames sigma hstate⟩

end Lax842588Proofs.AutomatonRamArenaTreeInvariant
