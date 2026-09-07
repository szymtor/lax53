import Lax53Proofs.FormulaArenaTraversalInit

/-!
Verification of the charged frame-loading phase of intrinsic-formula
traversal.
-/

namespace Lax53Proofs.FormulaArenaTraversalLoad

set_option maxHeartbeats 3000000
open Classical

open FirstOrder
open Lax52.MSOSyntax
open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53.RankedTree
open Lax53.ValueTranslations
open Lax53Proofs.ArenaSemantics
open Lax53Proofs.AutomatonRamArenaCorrectness
open Lax53Proofs.AutomatonRamCorrectness
open Lax53Proofs.FormulaArenaTraversalModel
open Lax53Proofs.FormulaArenaTraversalStack
open Lax53Proofs.MSORamArenaProgram
open Lax58.StructuralCombinators
open Lax58.WordArena

def FormulaFrameReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "formulaDepth" = (current :: outer).length ∧
    (current :: outer).length ≤ (sigma.arrs "FormulaRootStack").length ∧
    (current :: outer).length ≤ (sigma.arrs "FormulaFOStack").length ∧
    (current :: outer).length ≤ (sigma.arrs "FormulaSOStack").length ∧
    (current :: outer).length ≤ (sigma.arrs "FormulaPhaseStack").length ∧
    (sigma.arrs "FormulaRootStack").length < B ∧
    (sigma.arrs "FormulaFOStack").length < B ∧
    (sigma.arrs "FormulaSOStack").length < B ∧
    (sigma.arrs "FormulaPhaseStack").length < B ∧
    current.occurrence.fo < B ∧ current.occurrence.so < B ∧
    current.phase < B ∧
    FormulaStackRep I alphabet (current :: outer)
      (sigma.arrs "FormulaRootStack")
      (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack")
      (sigma.arrs "FormulaPhaseStack")

def FormulaFrameLoaded (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  FormulaFrameReady B I alphabet current outer sigma ∧
    ∃ root,
      root < B ∧
      sigma.vars "formulaIndex" = outer.length ∧
      sigma.vars "currentFormula" = root ∧
      sigma.vars "currentFO" = current.occurrence.fo ∧
      sigma.vars "currentSO" = current.occurrence.so ∧
      sigma.vars "formulaPhase" = current.phase ∧
      sigma.vars "formulaTag" =
        Raw.constructorNameCode (constructorName current.occurrence.formula) ∧
      Raw.constructorNameCode (constructorName current.occurrence.formula) < B ∧
      I.Represents root current.occurrence.raw

theorem loadFormulaFrame_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B (FormulaFrameReady B I alphabet current outer)
      loadFormulaFrame
      (fun _ sigma' => FormulaFrameLoaded B I alphabet current outer sigma')
      100 := by
  intro sigma hready
  rcases hready with ⟨hloaded, hdepth, hrootCapacity, hfoCapacity,
    hsoCapacity, hphaseCapacity, hrootLenB, hfoLenB, hsoLenB,
    hphaseLenB, hfoB, hsoB, hphaseB, hstack⟩
  obtain ⟨formulaRoot, hrootWord, hfoWord, hsoWord, hphaseWord,
      hformulaRep⟩ := formulaStackRep_current current outer hstack
  obtain ⟨fields, hstructure⟩ :=
    formulaStructure_is_constructor current.occurrence.formula
  have hformulaRep' : I.Represents formulaRoot
      (Raw.constructor (constructorName current.occurrence.formula) fields) := by
    simpa [Occurrence.raw, hstructure] using hformulaRep
  obtain ⟨nameRoot, fieldsRoot, _, hnameWord, _, hnameRep, _⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.pair_words hformulaRep'
  have htagWord :=
    Lax53Proofs.ArenaSemantics.Represents.nat_payload hnameRep
  have h0 : 0 < B := by omega
  have hgetB (i : Nat) : (arenaWords I).getD i 0 < B :=
    getD_lt_of_mem_bound h0 hvaluesB
  have hgetOptB (i : Nat) : ((arenaWords I)[i]?).getD 0 < B := by
    simpa [List.getD_eq_getElem?_getD] using hgetB i
  have hrootStackGetD :
      ((sigma.arrs "FormulaRootStack")[outer.length]?).getD 0 = formulaRoot := by
    simpa [List.getD_eq_getElem?_getD] using hrootWord
  have hfoStackGetD :
      ((sigma.arrs "FormulaFOStack")[outer.length]?).getD 0 =
        current.occurrence.fo := by
    simpa [List.getD_eq_getElem?_getD] using hfoWord
  have hsoStackGetD :
      ((sigma.arrs "FormulaSOStack")[outer.length]?).getD 0 =
        current.occurrence.so := by
    simpa [List.getD_eq_getElem?_getD] using hsoWord
  have hphaseStackGetD :
      ((sigma.arrs "FormulaPhaseStack")[outer.length]?).getD 0 =
        current.phase := by
    simpa [List.getD_eq_getElem?_getD] using hphaseWord
  have hnameGetD : ((arenaWords I)[formulaRoot + 1]?).getD 0 = nameRoot := by
    simpa [List.getD_eq_getElem?_getD] using hnameWord
  have htagGetD : ((arenaWords I)[nameRoot + 1]?).getD 0 =
      Raw.constructorNameCode (constructorName current.occurrence.formula) := by
    simpa [List.getD_eq_getElem?_getD] using htagWord
  have hformulaRootLen : formulaRoot + 2 < (arenaWords I).length :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hformulaRep)
  have hnameRootLen : nameRoot + 2 < (arenaWords I).length :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hnameRep)
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hformulaRootB : formulaRoot < B := by
    omega
  have hnameRootB : nameRoot < B := by
    omega
  have htagB :
      Raw.constructorNameCode (constructorName current.occurrence.formula) < B := by
    have := hgetOptB (nameRoot + 1)
    rw [htagGetD] at this
    exact this
  unfold loadFormulaFrame Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [FormulaFrameLoaded, FormulaFrameReady, ArenaLoaded]
  all_goals try omega

end Lax53Proofs.FormulaArenaTraversalLoad
