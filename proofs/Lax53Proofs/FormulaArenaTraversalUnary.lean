import Lax53Proofs.FormulaArenaTraversalEmit

/-!
Verification of unary-formula descent in the charged phase-stack traversal.
-/

namespace Lax53Proofs.FormulaArenaTraversalUnary

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

def NegPushReady (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .neg body⟩, 0⟩
  FormulaFrameLoaded B I alphabet current outer sigma ∧
    (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaPhaseStack").length

def NegPushed (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .neg body⟩, 1⟩
  let frames := initialFrame alphabet body :: current :: outer
  ArenaLoaded I sigma ∧
    sigma.vars "formulaDepth" = frames.length ∧
    (sigma.arrs "FormulaRootStack").length < B ∧
    (sigma.arrs "FormulaFOStack").length < B ∧
    (sigma.arrs "FormulaSOStack").length < B ∧
    (sigma.arrs "FormulaPhaseStack").length < B ∧
    FormulaStackRep I alphabet frames
      (sigma.arrs "FormulaRootStack")
      (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack")
      (sigma.arrs "FormulaPhaseStack")

theorem pushNegBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B) :
    Spec B (NegPushReady B I alphabet body outer)
      (pushUnaryBody (.var "currentFO") (.var "currentSO"))
      (fun _ sigma' => NegPushed B I alphabet body outer sigma') 150 := by
  intro sigma hready
  let current0 : TraversalFrame alphabet := ⟨⟨n, m, .neg body⟩, 0⟩
  let current1 : TraversalFrame alphabet := ⟨⟨n, m, .neg body⟩, 1⟩
  rcases hready with ⟨hloadedFrame, hrootSpace, hfoSpace, hsoSpace,
    hphaseSpace⟩
  rcases hloadedFrame with ⟨hframeReady, formulaRoot, hformulaRootB,
    hindex, hcurrentRoot, hcurrentFO, hcurrentSO, hphase, htag,
    htagB, hformulaRep⟩
  rcases hframeReady with ⟨hloaded, hdepth, hrootCapacity, hfoCapacity,
    hsoCapacity, hphaseCapacity, hrootLenB, hfoLenB, hsoLenB,
    hphaseLenB, hnB, hmB, hzeroB, hstack⟩
  have hformulaRep' : I.Represents formulaRoot
      (Raw.constructor "neg" [formulaStructure alphabet body]) := by
    simpa [current0, Occurrence.raw, formulaStructure] using hformulaRep
  obtain ⟨_, fieldsRoot, _, _, hfieldsWord, _, hfieldsRep⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.pair_words hformulaRep'
  obtain ⟨bodyRoot, _, _, hbodyWord, _, hbodyRep, _⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.fields_cons hfieldsRep
  have hformulaLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hformulaRep')
  have hfieldsLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hfieldsRep)
  have hbodyLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hbodyRep)
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hfieldsGetD : ((arenaWords I)[formulaRoot + 2]?).getD 0 = fieldsRoot := by
    simpa [List.getD_eq_getElem?_getD] using hfieldsWord
  have hbodyGetD : ((arenaWords I)[fieldsRoot + 1]?).getD 0 = bodyRoot := by
    simpa [List.getD_eq_getElem?_getD] using hbodyWord
  have hbodyRootB : bodyRoot < B := by omega
  have hphaseSlot : outer.length <
      (sigma.arrs "FormulaPhaseStack").length := by
    calc
      outer.length < (current0 :: outer).length := by simp
      _ < (sigma.arrs "FormulaPhaseStack").length := hphaseSpace
  have hphaseReplaced : FormulaStackRep I alphabet (current1 :: outer)
      (sigma.arrs "FormulaRootStack")
      (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack")
      ((sigma.arrs "FormulaPhaseStack").set outer.length 1) := by
    exact formulaStackRep_replacePhase (newPhase := 1) hstack hphaseSlot
  have hstack' := formulaStackRep_push
    (frame := initialFrame alphabet body) (root := bodyRoot)
    hphaseReplaced (by simpa [Occurrence.raw, initialFrame] using hbodyRep)
    hrootSpace hfoSpace hsoSpace (by
      simpa [current1] using hphaseSpace)
  unfold pushUnaryBody openFormulaFields
    Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [NegPushed, current1, ArenaLoaded,
    initialFrame]
  all_goals try omega

def ExFOPushReady (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .exFO body⟩, 0⟩
  FormulaFrameLoaded B I alphabet current outer sigma ∧ n + 1 < B ∧
    (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaPhaseStack").length

def ExFOPushed (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .exFO body⟩, 1⟩
  let frames := initialFrame alphabet body :: current :: outer
  ArenaLoaded I sigma ∧ sigma.vars "formulaDepth" = frames.length ∧
    (sigma.arrs "FormulaRootStack").length < B ∧
    (sigma.arrs "FormulaFOStack").length < B ∧
    (sigma.arrs "FormulaSOStack").length < B ∧
    (sigma.arrs "FormulaPhaseStack").length < B ∧
    FormulaStackRep I alphabet frames
      (sigma.arrs "FormulaRootStack") (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack") (sigma.arrs "FormulaPhaseStack")

theorem pushExFOBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B) :
    Spec B (ExFOPushReady B I alphabet body outer)
      (pushUnaryBody (.add (.var "currentFO") (.lit 1)) (.var "currentSO"))
      (fun _ sigma' => ExFOPushed B I alphabet body outer sigma') 150 := by
  intro sigma hready
  let current0 : TraversalFrame alphabet := ⟨⟨n, m, .exFO body⟩, 0⟩
  let current1 : TraversalFrame alphabet := ⟨⟨n, m, .exFO body⟩, 1⟩
  rcases hready with ⟨hloadedFrame, hnSuccB, hrootSpace, hfoSpace,
    hsoSpace, hphaseSpace⟩
  rcases hloadedFrame with ⟨hframeReady, formulaRoot, hformulaRootB,
    hindex, hcurrentRoot, hcurrentFO, hcurrentSO, hphase, htag,
    htagB, hformulaRep⟩
  rcases hframeReady with ⟨hloaded, hdepth, hrootCapacity, hfoCapacity,
    hsoCapacity, hphaseCapacity, hrootLenB, hfoLenB, hsoLenB,
    hphaseLenB, hnB, hmB, hzeroB, hstack⟩
  have hformulaRep' : I.Represents formulaRoot
      (Raw.constructor "exFO" [formulaStructure alphabet body]) := by
    simpa [current0, Occurrence.raw, formulaStructure] using hformulaRep
  obtain ⟨_, fieldsRoot, _, _, hfieldsWord, _, hfieldsRep⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.pair_words hformulaRep'
  obtain ⟨bodyRoot, _, _, hbodyWord, _, hbodyRep, _⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.fields_cons hfieldsRep
  have hformulaLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hformulaRep')
  have hfieldsLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hfieldsRep)
  have hbodyLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hbodyRep)
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hfieldsGetD : ((arenaWords I)[formulaRoot + 2]?).getD 0 = fieldsRoot := by
    simpa [List.getD_eq_getElem?_getD] using hfieldsWord
  have hbodyGetD : ((arenaWords I)[fieldsRoot + 1]?).getD 0 = bodyRoot := by
    simpa [List.getD_eq_getElem?_getD] using hbodyWord
  have hbodyRootB : bodyRoot < B := by omega
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
    (frame := initialFrame alphabet body) (root := bodyRoot)
    hphaseReplaced (by simpa [Occurrence.raw, initialFrame] using hbodyRep)
    hrootSpace hfoSpace hsoSpace (by simpa [current1] using hphaseSpace)
  unfold pushUnaryBody openFormulaFields
    Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [ExFOPushed, current1, ArenaLoaded, initialFrame]
  all_goals try omega

def ExSOPushReady (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n (m + 1))
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .exSO body⟩, 0⟩
  FormulaFrameLoaded B I alphabet current outer sigma ∧ m + 1 < B ∧
    (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
    (current :: outer).length < (sigma.arrs "FormulaPhaseStack").length

def ExSOPushed (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n (m + 1))
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  let current : TraversalFrame alphabet := ⟨⟨n, m, .exSO body⟩, 1⟩
  let frames := initialFrame alphabet body :: current :: outer
  ArenaLoaded I sigma ∧ sigma.vars "formulaDepth" = frames.length ∧
    (sigma.arrs "FormulaRootStack").length < B ∧
    (sigma.arrs "FormulaFOStack").length < B ∧
    (sigma.arrs "FormulaSOStack").length < B ∧
    (sigma.arrs "FormulaPhaseStack").length < B ∧
    FormulaStackRep I alphabet frames
      (sigma.arrs "FormulaRootStack") (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack") (sigma.arrs "FormulaPhaseStack")

theorem pushExSOBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n (m + 1))
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B) :
    Spec B (ExSOPushReady B I alphabet body outer)
      (pushUnaryBody (.var "currentFO")
        (.add (.var "currentSO") (.lit 1)))
      (fun _ sigma' => ExSOPushed B I alphabet body outer sigma') 150 := by
  intro sigma hready
  let current0 : TraversalFrame alphabet := ⟨⟨n, m, .exSO body⟩, 0⟩
  let current1 : TraversalFrame alphabet := ⟨⟨n, m, .exSO body⟩, 1⟩
  rcases hready with ⟨hloadedFrame, hmSuccB, hrootSpace, hfoSpace,
    hsoSpace, hphaseSpace⟩
  rcases hloadedFrame with ⟨hframeReady, formulaRoot, hformulaRootB,
    hindex, hcurrentRoot, hcurrentFO, hcurrentSO, hphase, htag,
    htagB, hformulaRep⟩
  rcases hframeReady with ⟨hloaded, hdepth, hrootCapacity, hfoCapacity,
    hsoCapacity, hphaseCapacity, hrootLenB, hfoLenB, hsoLenB,
    hphaseLenB, hnB, hmB, hzeroB, hstack⟩
  have hformulaRep' : I.Represents formulaRoot
      (Raw.constructor "exSO" [formulaStructure alphabet body]) := by
    simpa [current0, Occurrence.raw, formulaStructure] using hformulaRep
  obtain ⟨_, fieldsRoot, _, _, hfieldsWord, _, hfieldsRep⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.pair_words hformulaRep'
  obtain ⟨bodyRoot, _, _, hbodyWord, _, hbodyRep, _⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.fields_cons hfieldsRep
  have hformulaLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hformulaRep')
  have hfieldsLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hfieldsRep)
  have hbodyLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hbodyRep)
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hfieldsGetD : ((arenaWords I)[formulaRoot + 2]?).getD 0 = fieldsRoot := by
    simpa [List.getD_eq_getElem?_getD] using hfieldsWord
  have hbodyGetD : ((arenaWords I)[fieldsRoot + 1]?).getD 0 = bodyRoot := by
    simpa [List.getD_eq_getElem?_getD] using hbodyWord
  have hbodyRootB : bodyRoot < B := by omega
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
    (frame := initialFrame alphabet body) (root := bodyRoot)
    hphaseReplaced (by simpa [Occurrence.raw, initialFrame] using hbodyRep)
    hrootSpace hfoSpace hsoSpace (by simpa [current1] using hphaseSpace)
  unfold pushUnaryBody openFormulaFields
    Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [ExSOPushed, current1, ArenaLoaded, initialFrame]
  all_goals try omega

end Lax53Proofs.FormulaArenaTraversalUnary
