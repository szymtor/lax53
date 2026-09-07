import Lax53Proofs.AutomatonRamArenaTreeModel

/-!
Certified correspondence between the logical traversal stack and the two
proof-only RAM arrays, together with verification of `pushTreeNode`.
-/

namespace Lax53Proofs.AutomatonRamArenaTreeStack

set_option maxHeartbeats 3000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53Proofs.ArrayInput
open Lax53.RankedTree
open Lax53.ValueTranslations
open Lax53.StructuralRepresentations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.ArenaSemantics
open Lax53Proofs.AutomatonRamArenaProgram
open Lax53Proofs.AutomatonRamArenaSegments
open Lax53Proofs.AutomatonRamArenaCorrectness
open Lax53Proofs.AutomatonRamCorrectness
open Lax53Proofs.AutomatonRamArenaTreeModel
open Lax58.StructuralPresentation
open Lax58.StructuralCombinators
open Lax58.WordArena

/-- Certified arena cursors aligned with logical frames, from the current
frame outward. -/
inductive CursorsRepresent (I : WordImage) (alphabet : RankedAlphabetCode) :
    List Nat → List (TraversalFrame alphabet) → Prop
  | nil : CursorsRepresent I alphabet [] []
  | cons {cursor : Nat} {frame : TraversalFrame alphabet}
      {cursors : List Nat} {frames : List (TraversalFrame alphabet)} :
      I.Represents cursor
        (Raw.fields (frame.rest.map (treeStructure alphabet))) →
      CursorsRepresent I alphabet cursors frames →
      CursorsRepresent I alphabet (cursor :: cursors) (frame :: frames)

theorem CursorsRepresent.length_eq {I : WordImage}
    {alphabet : RankedAlphabetCode} {cursors : List Nat}
    {frames : List (TraversalFrame alphabet)}
    (h : CursorsRepresent I alphabet cursors frames) :
    cursors.length = frames.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Physical symbol-stack order is outermost to innermost, the reverse of
the semantic frame order. -/
def frameSymbols (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) : List Nat :=
  frames.reverse.map fun frame => frame.symbol.val

@[simp] theorem frameSymbols_length (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) :
    (frameSymbols alphabet frames).length = frames.length := by
  simp [frameSymbols]

/-- Pointwise physical realization of a logical traversal stack. -/
def TreeStackRep (I : WordImage) (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet))
    (symbolStack tailStack : List Nat) : Prop :=
  ∃ cursors,
    CursorsRepresent I alphabet cursors frames ∧
    WordsAt symbolStack 0 (frameSymbols alphabet frames) ∧
    WordsAt tailStack 0 cursors.reverse

private theorem wordsAt_prefix {parameter xs ys : List Nat} {start : Nat}
    (h : WordsAt parameter start (xs ++ ys)) :
    WordsAt parameter start xs := by
  intro i hi
  calc
    parameter.getD (start + i) 0 = (xs ++ ys).getD i 0 :=
      h i (by simp; omega)
    _ = xs.getD i 0 := by rw [List.getD_append]; exact hi

theorem treeStackRep_push {I : WordImage} {alphabet : RankedAlphabetCode}
    {frames : List (TraversalFrame alphabet)}
    {symbolStack tailStack : List Nat}
    (frame : TraversalFrame alphabet) (cursor : Nat)
    (hstack : TreeStackRep I alphabet frames symbolStack tailStack)
    (hcursor : I.Represents cursor
      (Raw.fields (frame.rest.map (treeStructure alphabet))))
    (hsymbolSpace : frames.length < symbolStack.length)
    (htailSpace : frames.length < tailStack.length) :
    TreeStackRep I alphabet (frame :: frames)
      (symbolStack.set frames.length frame.symbol.val)
      (tailStack.set frames.length cursor) := by
  rcases hstack with ⟨cursors, hcursors, hsymbols, htails⟩
  have hcursorLength := hcursors.length_eq
  refine ⟨cursor :: cursors, .cons hcursor hcursors, ?_, ?_⟩
  · have happend := wordsAt_set_append (value := frame.symbol.val) hsymbols
      (by simpa using hsymbolSpace)
    simpa [frameSymbols, List.reverse_cons, List.map_append,
      List.append_assoc] using happend
  · have happend := wordsAt_set_append (value := cursor) htails (by
      simpa [hcursorLength] using htailSpace)
    simpa [List.reverse_cons, List.append_assoc, hcursorLength] using happend

/-- Replacing the current frame's remaining-child cursor changes only the
last occupied physical tail-stack cell. -/
theorem treeStackRep_replaceCurrent {I : WordImage}
    {alphabet : RankedAlphabetCode} {symbol : Fin alphabet.length}
    {oldRest newRest : List (Tree alphabet.toRankedAlphabet)}
    {outer : List (TraversalFrame alphabet)}
    {symbolStack tailStack : List Nat} (newCursor : Nat)
    (hstack : TreeStackRep I alphabet
      (⟨symbol, oldRest⟩ :: outer) symbolStack tailStack)
    (hcursor : I.Represents newCursor
      (Raw.fields (newRest.map (treeStructure alphabet))))
    (htailSpace : outer.length < tailStack.length) :
    TreeStackRep I alphabet
      (⟨symbol, newRest⟩ :: outer) symbolStack
      (tailStack.set outer.length newCursor) := by
  rcases hstack with ⟨cursors, hcursors, hsymbols, htails⟩
  cases hcursors with
  | @cons oldCursor oldFrame outerCursors outerFrames hold houter =>
      have hcursorLength := houter.length_eq
      have htailPrefix : WordsAt tailStack 0 outerCursors.reverse := by
        apply wordsAt_prefix (ys := [oldCursor])
        simpa [List.reverse_cons] using htails
      have htails' := wordsAt_set_append (value := newCursor) htailPrefix (by
        simpa [hcursorLength] using htailSpace)
      refine ⟨newCursor :: outerCursors, .cons hcursor houter, ?_, ?_⟩
      · simpa [frameSymbols] using hsymbols
      · simpa [List.reverse_cons, hcursorLength] using htails'

/-- Popping the current logical frame merely shortens the occupied prefixes;
the physical arrays themselves need not be modified. -/
theorem treeStackRep_pop {I : WordImage} {alphabet : RankedAlphabetCode}
    {frame : TraversalFrame alphabet}
    {outer : List (TraversalFrame alphabet)}
    {symbolStack tailStack : List Nat}
    (hstack : TreeStackRep I alphabet (frame :: outer)
      symbolStack tailStack) :
    TreeStackRep I alphabet outer symbolStack tailStack := by
  rcases hstack with ⟨cursors, hcursors, hsymbols, htails⟩
  cases hcursors with
  | @cons cursor current outerCursors outerFrames hcurrent houter =>
      refine ⟨outerCursors, houter, ?_, ?_⟩
      · apply wordsAt_prefix (ys := [frame.symbol.val])
        simpa [frameSymbols, List.reverse_cons, List.map_append] using hsymbols
      · apply wordsAt_prefix (ys := [cursor])
        simpa [List.reverse_cons] using htails

/-- Preconditions needed to open and push one represented tree node. -/
def TreePushReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet)
    (frames : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    I.Represents (sigma.vars "currentTree") (treeStructure alphabet tree) ∧
    sigma.vars "treeDepth" = frames.length ∧
    frames.length < (sigma.arrs "TreeSymbolStack").length ∧
    frames.length < (sigma.arrs "TreeTailStack").length ∧
    (sigma.arrs "TreeSymbolStack").length < B ∧
    (sigma.arrs "TreeTailStack").length < B ∧
    TreeStackRep I alphabet frames
      (sigma.arrs "TreeSymbolStack") (sigma.arrs "TreeTailStack")

def TreePushed (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet)
    (frames : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "treeDepth" = (initialFrame alphabet tree :: frames).length ∧
    (sigma.arrs "TreeSymbolStack").length < B ∧
    (sigma.arrs "TreeTailStack").length < B ∧
    TreeStackRep I alphabet (initialFrame alphabet tree :: frames)
      (sigma.arrs "TreeSymbolStack") (sigma.arrs "TreeTailStack")

theorem pushTreeNode_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (tree : Tree alphabet.toRankedAlphabet)
    (frames : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B (TreePushReady B I alphabet tree frames) pushTreeNode
      (fun _ sigma' => TreePushed B I alphabet tree frames sigma') 100 := by
  intro sigma hready
  rcases hready with ⟨hloaded, htreeRep, hdepth, hsymbolSpace, htailSpace,
    hsymbolLenB, htailLenB, hstack⟩
  cases tree with
  | node symbol children =>
      have htreeRep' : I.Represents (sigma.vars "currentTree")
          (Raw.constructor "node"
            (nat.toRaw symbol.val ::
              List.ofFn fun i => treeStructure alphabet (children i))) := by
        simpa [treeStructure] using htreeRep
      obtain ⟨nameAddress, fieldsAddress, htreeTag, hnameWord, hfieldsWord,
          hnameRep, hfieldsRep⟩ :=
        Lax53Proofs.ArenaSemantics.Represents.pair_words htreeRep'
      obtain ⟨symbolAddress, childCursor, hfieldsTag, hsymbolWord,
          hchildrenWord, hsymbolRep, hchildrenRep⟩ :=
        Lax53Proofs.ArenaSemantics.Represents.fields_cons hfieldsRep
      have hsymbolPayload :=
        Lax53Proofs.ArenaSemantics.Represents.nat_payload hsymbolRep
      have htreeValid :=
        Lax53Proofs.ArenaSemantics.Represents.valid htreeRep'
      have hfieldsValid :=
        Lax53Proofs.ArenaSemantics.Represents.valid hfieldsRep
      have hsymbolValid :=
        Lax53Proofs.ArenaSemantics.Represents.valid hsymbolRep
      have htreeLen :=
        Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length htreeValid
      have hfieldsLen :=
        Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hfieldsValid
      have hsymbolLen :=
        Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hsymbolValid
      have harenaLength : (arenaWords I).length = I.memoryWords := by
        simp [arenaWords, WordImage.memoryWords]
      have hgetB (i : Nat) : (arenaWords I).getD i 0 < B :=
        getD_lt_of_mem_bound (by omega) hvaluesB
      have hgetOptB (i : Nat) : ((arenaWords I)[i]?).getD 0 < B := by
        simpa [List.getD_eq_getElem?_getD] using hgetB i
      have hfieldsGetD :
          ((arenaWords I)[sigma.vars "currentTree" + 2]?).getD 0 =
            fieldsAddress := by
        simpa [List.getD_eq_getElem?_getD] using hfieldsWord
      have hsymbolAddressGetD :
          ((arenaWords I)[fieldsAddress + 1]?).getD 0 = symbolAddress := by
        simpa [List.getD_eq_getElem?_getD] using hsymbolWord
      have hsymbolGetD : ((arenaWords I)[symbolAddress + 1]?).getD 0 =
          symbol.val := by
        simpa [List.getD_eq_getElem?_getD] using hsymbolPayload
      have hchildrenGetD : ((arenaWords I)[fieldsAddress + 2]?).getD 0 =
          childCursor := by
        simpa [List.getD_eq_getElem?_getD] using hchildrenWord
      have hfieldsGetDB := hgetOptB (sigma.vars "currentTree" + 2)
      have hsymbolAddressGetDB := hgetOptB (fieldsAddress + 1)
      have hsymbolGetDB := hgetOptB (symbolAddress + 1)
      have hchildrenGetDB := hgetOptB (fieldsAddress + 2)
      have hchildrenRep' : I.Represents childCursor
          (Raw.fields ((List.ofFn children).map (treeStructure alphabet))) := by
        simpa [List.map_ofFn, Function.comp_def] using hchildrenRep
      have hstack' := treeStackRep_push
        (frame := initialFrame alphabet (.node symbol children))
        (cursor := childCursor) hstack (by
          simpa [initialFrame] using hchildrenRep') hsymbolSpace htailSpace
      unfold pushTreeNode Lax53Proofs.AutomatonRamProgram.seqs
      run_vcg
      all_goals simp_all [TreePushed, ArenaLoaded, initialFrame]
      all_goals (try omega)

end Lax53Proofs.AutomatonRamArenaTreeStack
