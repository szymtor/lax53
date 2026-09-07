import Lax53Proofs.FormulaArenaTraversalUnary

/-!
Verification of the two disjunction-child phases in the charged intrinsic
formula traversal.
-/

namespace Lax53Proofs.FormulaArenaTraversalOr

set_option maxHeartbeats 3000000
open Classical

open FirstOrder
open Lax52.MSOSyntax
open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.ValueTranslations
open Lax53.StructuralRepresentations
open Lax53Proofs.ArenaSemantics
open Lax53Proofs.AutomatonRamArenaCorrectness
open Lax53Proofs.FormulaArenaTraversalModel
open Lax53Proofs.FormulaArenaTraversalStack
open Lax53Proofs.FormulaArenaTraversalLoad
open Lax53Proofs.MSORamArenaProgram
open Lax58.StructuralPresentation
open Lax58.StructuralCombinators
open Lax58.WordArena

def OrLeftReady (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 0⟩
  FormulaFrameLoaded B I alphabet current outer sigma ∧
    (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaPhaseStack").length

def OrLeftPushed (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 1⟩
  let frames := initialFrame alphabet left :: current :: outer
  ArenaLoaded I sigma ∧ sigma.vars "formulaDepth" = frames.length ∧
    (sigma.arrs "FormulaRootStack").length < B ∧
    (sigma.arrs "FormulaFOStack").length < B ∧
    (sigma.arrs "FormulaSOStack").length < B ∧
    (sigma.arrs "FormulaPhaseStack").length < B ∧
    FormulaStackRep I alphabet frames
      (sigma.arrs "FormulaRootStack") (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack") (sigma.arrs "FormulaPhaseStack")

theorem pushOrLeft_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B) :
    Spec B (OrLeftReady B I alphabet left right outer) pushOrLeft
      (fun _ sigma' => OrLeftPushed B I alphabet left right outer sigma')
      150 := by
  intro sigma hready
  let current0 : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 0⟩
  let current1 : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 1⟩
  rcases hready with ⟨hloadedFrame, hrootSpace, hfoSpace, hsoSpace,
    hphaseSpace⟩
  rcases hloadedFrame with ⟨hframeReady, formulaRoot, hformulaRootB,
    hindex, hcurrentRoot, hcurrentFO, hcurrentSO, hphase, htag,
    htagB, hformulaRep⟩
  rcases hframeReady with ⟨hloaded, hdepth, hrootCapacity, hfoCapacity,
    hsoCapacity, hphaseCapacity, hrootLenB, hfoLenB, hsoLenB,
    hphaseLenB, hnB, hmB, hzeroB, hstack⟩
  have hformulaRep' : I.Represents formulaRoot
      (Raw.constructor "or"
        [formulaStructure alphabet left, formulaStructure alphabet right]) := by
    simpa [current0, Occurrence.raw, formulaStructure] using hformulaRep
  obtain ⟨_, fieldsRoot, _, _, hfieldsWord, _, hfieldsRep⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.pair_words hformulaRep'
  obtain ⟨leftRoot, _, _, hleftWord, _, hleftRep, _⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.fields_cons hfieldsRep
  have hformulaLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hformulaRep')
  have hfieldsLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hfieldsRep)
  have hleftLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hleftRep)
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hfieldsGetD : ((arenaWords I)[formulaRoot + 2]?).getD 0 = fieldsRoot := by
    simpa [List.getD_eq_getElem?_getD] using hfieldsWord
  have hleftGetD : ((arenaWords I)[fieldsRoot + 1]?).getD 0 = leftRoot := by
    simpa [List.getD_eq_getElem?_getD] using hleftWord
  have hleftRootB : leftRoot < B := by omega
  have hphaseSlot : outer.length <
      (sigma.arrs "FormulaPhaseStack").length := by
    calc
      outer.length < (current0 :: outer).length := by simp
      _ < (sigma.arrs "FormulaPhaseStack").length := hphaseSpace
  have hphaseReplaced : FormulaStackRep I alphabet (current1 :: outer)
      (sigma.arrs "FormulaRootStack") (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack")
      ((sigma.arrs "FormulaPhaseStack").set outer.length 1) :=
    formulaStackRep_replacePhase (newPhase := 1) hstack hphaseSlot
  have hstack' := formulaStackRep_push
    (frame := initialFrame alphabet left) (root := leftRoot)
    hphaseReplaced (by simpa [Occurrence.raw, initialFrame] using hleftRep)
    hrootSpace hfoSpace hsoSpace (by simpa [current1] using hphaseSpace)
  unfold pushOrLeft openFormulaFields
    Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [OrLeftPushed, current1, ArenaLoaded, initialFrame]
  all_goals try omega

def OrRightReady (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 1⟩
  FormulaFrameLoaded B I alphabet current outer sigma ∧
    (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaPhaseStack").length

def OrRightPushed (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 2⟩
  let frames := initialFrame alphabet right :: current :: outer
  ArenaLoaded I sigma ∧ sigma.vars "formulaDepth" = frames.length ∧
    (sigma.arrs "FormulaRootStack").length < B ∧
    (sigma.arrs "FormulaFOStack").length < B ∧
    (sigma.arrs "FormulaSOStack").length < B ∧
    (sigma.arrs "FormulaPhaseStack").length < B ∧
    FormulaStackRep I alphabet frames
      (sigma.arrs "FormulaRootStack") (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack") (sigma.arrs "FormulaPhaseStack")

theorem pushOrRight_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B) :
    Spec B (OrRightReady B I alphabet left right outer) pushOrRight
      (fun _ sigma' => OrRightPushed B I alphabet left right outer sigma')
      175 := by
  intro sigma hready
  let current1 : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 1⟩
  let current2 : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 2⟩
  rcases hready with ⟨hloadedFrame, hrootSpace, hfoSpace, hsoSpace,
    hphaseSpace⟩
  rcases hloadedFrame with ⟨hframeReady, formulaRoot, hformulaRootB,
    hindex, hcurrentRoot, hcurrentFO, hcurrentSO, hphase, htag,
    htagB, hformulaRep⟩
  rcases hframeReady with ⟨hloaded, hdepth, hrootCapacity, hfoCapacity,
    hsoCapacity, hphaseCapacity, hrootLenB, hfoLenB, hsoLenB,
    hphaseLenB, hnB, hmB, honeB, hstack⟩
  have hformulaRep' : I.Represents formulaRoot
      (Raw.constructor "or"
        [formulaStructure alphabet left, formulaStructure alphabet right]) := by
    simpa [current1, Occurrence.raw, formulaStructure] using hformulaRep
  obtain ⟨_, fieldsRoot, _, _, hfieldsWord, _, hfieldsRep⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.pair_words hformulaRep'
  obtain ⟨_, rightTail, _, _, hrightTailWord, _, hrightTailRep⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.fields_cons hfieldsRep
  obtain ⟨rightRoot, _, _, hrightWord, _, hrightRep, _⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.fields_cons hrightTailRep
  have hformulaLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hformulaRep')
  have hfieldsLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hfieldsRep)
  have hrightTailLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hrightTailRep)
  have hrightLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hrightRep)
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hfieldsGetD : ((arenaWords I)[formulaRoot + 2]?).getD 0 = fieldsRoot := by
    simpa [List.getD_eq_getElem?_getD] using hfieldsWord
  have hrightTailGetD : ((arenaWords I)[fieldsRoot + 2]?).getD 0 =
      rightTail := by
    simpa [List.getD_eq_getElem?_getD] using hrightTailWord
  have hrightGetD : ((arenaWords I)[rightTail + 1]?).getD 0 = rightRoot := by
    simpa [List.getD_eq_getElem?_getD] using hrightWord
  have hrightRootB : rightRoot < B := by omega
  have hphaseSlot : outer.length <
      (sigma.arrs "FormulaPhaseStack").length := by
    calc
      outer.length < (current1 :: outer).length := by simp
      _ < (sigma.arrs "FormulaPhaseStack").length := hphaseSpace
  have hphaseReplaced : FormulaStackRep I alphabet (current2 :: outer)
      (sigma.arrs "FormulaRootStack") (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack")
      ((sigma.arrs "FormulaPhaseStack").set outer.length 2) :=
    formulaStackRep_replacePhase (newPhase := 2) hstack hphaseSlot
  have hstack' := formulaStackRep_push
    (frame := initialFrame alphabet right) (root := rightRoot)
    hphaseReplaced (by simpa [Occurrence.raw, initialFrame] using hrightRep)
    hrootSpace hfoSpace hsoSpace (by simpa [current2] using hphaseSpace)
  unfold pushOrRight openFormulaFields
    Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [OrRightPushed, current2, ArenaLoaded, initialFrame]
  all_goals try omega

end Lax53Proofs.FormulaArenaTraversalOr
