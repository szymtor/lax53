import Lax53Proofs.FormulaArenaTraversalModel
import Lax53Proofs.AutomatonRamArenaSegments
import Lax53Proofs.ArenaSemantics

/-!
Logical/physical correspondence for the four proof-private formula traversal
stacks. Stack entries retain arena addresses and intrinsic scope indices; the
formula value itself remains the original Lax-52 value in the specification.
-/

namespace Lax53Proofs.FormulaArenaTraversalStack

open FirstOrder
open Lax52.MSOSyntax
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.ValueTranslations
open Lax53.StructuralRepresentations
open Lax53Proofs.AutomatonRamArenaSegments
open Lax53Proofs.FormulaArenaTraversalModel
open Lax58.WordArena

/-- Arena roots aligned with semantic frames, from the current frame outward. -/
inductive RootsRepresent (I : WordImage) (alphabet : RankedAlphabetCode) :
    List Nat → List (TraversalFrame alphabet) → Prop
  | nil : RootsRepresent I alphabet [] []
  | cons {root : Nat} {frame : TraversalFrame alphabet}
      {roots : List Nat} {frames : List (TraversalFrame alphabet)} :
      I.Represents root frame.occurrence.raw →
      RootsRepresent I alphabet roots frames →
      RootsRepresent I alphabet (root :: roots) (frame :: frames)

theorem RootsRepresent.length_eq {I : WordImage}
    {alphabet : RankedAlphabetCode} {roots : List Nat}
    {frames : List (TraversalFrame alphabet)}
    (h : RootsRepresent I alphabet roots frames) :
    roots.length = frames.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

def frameFOs (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) : List Nat :=
  frames.reverse.map fun frame => frame.occurrence.fo

def frameSOs (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) : List Nat :=
  frames.reverse.map fun frame => frame.occurrence.so

def framePhases (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) : List Nat :=
  frames.reverse.map fun frame => frame.phase

@[simp] theorem frameFOs_length (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) :
    (frameFOs alphabet frames).length = frames.length := by simp [frameFOs]

@[simp] theorem frameSOs_length (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) :
    (frameSOs alphabet frames).length = frames.length := by simp [frameSOs]

@[simp] theorem framePhases_length (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) :
    (framePhases alphabet frames).length = frames.length := by
  simp [framePhases]

/-- Pointwise physical realization. Arrays are ordered outermost to current,
the reverse of the semantic frame list. -/
def FormulaStackRep (I : WordImage) (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet))
    (rootStack foStack soStack phaseStack : List Nat) : Prop :=
  ∃ roots,
    RootsRepresent I alphabet roots frames ∧
    WordsAt rootStack 0 roots.reverse ∧
    WordsAt foStack 0 (frameFOs alphabet frames) ∧
    WordsAt soStack 0 (frameSOs alphabet frames) ∧
    WordsAt phaseStack 0 (framePhases alphabet frames)

theorem formulaStackRep_nil (I : WordImage) (alphabet : RankedAlphabetCode)
    (rootStack foStack soStack phaseStack : List Nat) :
    FormulaStackRep I alphabet [] rootStack foStack soStack phaseStack := by
  exact ⟨[], .nil, wordsAt_nil _ _, wordsAt_nil _ _, wordsAt_nil _ _,
    wordsAt_nil _ _⟩

private theorem wordsAt_prefix {parameter xs ys : List Nat} {start : Nat}
    (h : WordsAt parameter start (xs ++ ys)) :
    WordsAt parameter start xs := by
  intro i hi
  calc
    parameter.getD (start + i) 0 = (xs ++ ys).getD i 0 :=
      h i (by simp; omega)
    _ = xs.getD i 0 := by rw [List.getD_append]; exact hi

/-- Reading the last occupied cells yields the current semantic frame and a
certified arena root for its original intrinsic formula occurrence. -/
theorem formulaStackRep_current {I : WordImage}
    {alphabet : RankedAlphabetCode} (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet))
    {rootStack foStack soStack phaseStack : List Nat}
    (hstack : FormulaStackRep I alphabet (current :: outer)
      rootStack foStack soStack phaseStack) :
    ∃ root,
      rootStack.getD outer.length 0 = root ∧
      foStack.getD outer.length 0 = current.occurrence.fo ∧
      soStack.getD outer.length 0 = current.occurrence.so ∧
      phaseStack.getD outer.length 0 = current.phase ∧
      I.Represents root current.occurrence.raw := by
  rcases hstack with ⟨roots, hroots, hrootWords, hfoWords, hsoWords,
    hphaseWords⟩
  cases hroots with
  | @cons root representedCurrent outerRoots representedOuter hroot houter =>
      have hrootsLength := houter.length_eq
      have hrootWord := hrootWords outer.length (by
        simp [List.reverse_cons, hrootsLength])
      have hfoWord := hfoWords outer.length (by simp [frameFOs])
      have hsoWord := hsoWords outer.length (by simp [frameSOs])
      have hphaseWord := hphaseWords outer.length (by simp [framePhases])
      refine ⟨root, ?_, ?_, ?_, ?_, hroot⟩
      · simpa [List.reverse_cons, hrootsLength] using hrootWord
      · simpa [frameFOs, List.reverse_cons, List.map_append] using hfoWord
      · simpa [frameSOs, List.reverse_cons, List.map_append] using hsoWord
      · simpa [framePhases, List.reverse_cons, List.map_append] using hphaseWord

theorem formulaStackRep_push {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {frames : List (TraversalFrame alphabet)}
    {rootStack foStack soStack phaseStack : List Nat}
    (frame : TraversalFrame alphabet) (root : Nat)
    (hstack : FormulaStackRep I alphabet frames rootStack foStack soStack
      phaseStack)
    (hroot : I.Represents root frame.occurrence.raw)
    (hrootSpace : frames.length < rootStack.length)
    (hfoSpace : frames.length < foStack.length)
    (hsoSpace : frames.length < soStack.length)
    (hphaseSpace : frames.length < phaseStack.length) :
    FormulaStackRep I alphabet (frame :: frames)
      (rootStack.set frames.length root)
      (foStack.set frames.length frame.occurrence.fo)
      (soStack.set frames.length frame.occurrence.so)
      (phaseStack.set frames.length frame.phase) := by
  rcases hstack with ⟨roots, hroots, hrootWords, hfoWords, hsoWords,
    hphaseWords⟩
  have hrootsLength := hroots.length_eq
  refine ⟨root :: roots, .cons hroot hroots, ?_, ?_, ?_, ?_⟩
  · have h := wordsAt_set_append (value := root) hrootWords (by
      simpa [hrootsLength] using hrootSpace)
    simpa [List.reverse_cons, List.length_reverse, hrootsLength] using h
  · have h := wordsAt_set_append (value := frame.occurrence.fo) hfoWords
      (by simpa using hfoSpace)
    simpa [frameFOs, List.reverse_cons, List.map_append] using h
  · have h := wordsAt_set_append (value := frame.occurrence.so) hsoWords
      (by simpa using hsoSpace)
    simpa [frameSOs, List.reverse_cons, List.map_append] using h
  · have h := wordsAt_set_append (value := frame.phase) hphaseWords
      (by simpa using hphaseSpace)
    simpa [framePhases, List.reverse_cons, List.map_append] using h

/-- Updating the phase of the current semantic frame changes only the last
occupied physical phase cell. -/
theorem formulaStackRep_replacePhase {I : WordImage}
    {alphabet : RankedAlphabetCode} {occurrence : Occurrence alphabet}
    {oldPhase newPhase : Nat} {outer : List (TraversalFrame alphabet)}
    {rootStack foStack soStack phaseStack : List Nat}
    (hstack : FormulaStackRep I alphabet
      (⟨occurrence, oldPhase⟩ :: outer)
      rootStack foStack soStack phaseStack)
    (hphaseSpace : outer.length < phaseStack.length) :
    FormulaStackRep I alphabet
      (⟨occurrence, newPhase⟩ :: outer)
      rootStack foStack soStack
      (phaseStack.set outer.length newPhase) := by
  rcases hstack with ⟨roots, hroots, hrootWords, hfoWords, hsoWords,
    hphaseWords⟩
  cases hroots with
  | @cons root current roots frames hroot houter =>
      have hrootsLength := houter.length_eq
      have hphasePrefix : WordsAt phaseStack 0 (framePhases alphabet outer) := by
        apply wordsAt_prefix (ys := [oldPhase])
        simpa [framePhases, List.reverse_cons, List.map_append] using hphaseWords
      have hphaseWords' := wordsAt_set_append (value := newPhase) hphasePrefix
        (by simpa using hphaseSpace)
      refine ⟨root :: roots, .cons hroot houter, ?_, ?_, ?_, ?_⟩
      · simpa [List.reverse_cons, hrootsLength] using hrootWords
      · simpa [frameFOs] using hfoWords
      · simpa [frameSOs] using hsoWords
      · simpa [framePhases, List.reverse_cons, List.map_append] using hphaseWords'

/-- Popping a frame only shortens the occupied prefixes. -/
theorem formulaStackRep_pop {I : WordImage}
    {alphabet : RankedAlphabetCode} {frame : TraversalFrame alphabet}
    {outer : List (TraversalFrame alphabet)}
    {rootStack foStack soStack phaseStack : List Nat}
    (hstack : FormulaStackRep I alphabet (frame :: outer)
      rootStack foStack soStack phaseStack) :
    FormulaStackRep I alphabet outer rootStack foStack soStack phaseStack := by
  rcases hstack with ⟨roots, hroots, hrootWords, hfoWords, hsoWords,
    hphaseWords⟩
  cases hroots with
  | @cons root current roots frames hroot houter =>
      refine ⟨roots, houter, ?_, ?_, ?_, ?_⟩
      · apply wordsAt_prefix (ys := [root])
        simpa [List.reverse_cons] using hrootWords
      · apply wordsAt_prefix (ys := [frame.occurrence.fo])
        simpa [frameFOs, List.reverse_cons, List.map_append] using hfoWords
      · apply wordsAt_prefix (ys := [frame.occurrence.so])
        simpa [frameSOs, List.reverse_cons, List.map_append] using hsoWords
      · apply wordsAt_prefix (ys := [frame.phase])
        simpa [framePhases, List.reverse_cons, List.map_append] using hphaseWords

end Lax53Proofs.FormulaArenaTraversalStack
