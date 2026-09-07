import Lax53Proofs.MSORamArenaRead
import Lax53Proofs.FormulaArenaTraversalStack

/-!
Verified initialization of the charged intrinsic-formula traversal.
-/

namespace Lax53Proofs.FormulaArenaTraversalInit

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
open Lax53Proofs.MSORamArenaProgram
open Lax58.WordArena

def FormulaTraversalReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Lax52.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet))
    (formulaRoot : Nat) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "formulaRoot" = formulaRoot ∧
    I.Represents formulaRoot (formulaStructure alphabet phi) ∧
    0 < (sigma.arrs "FormulaRootStack").length ∧
    0 < (sigma.arrs "FormulaFOStack").length ∧
    0 < (sigma.arrs "FormulaSOStack").length ∧
    0 < (sigma.arrs "FormulaPhaseStack").length ∧
    (sigma.arrs "FormulaRootStack").length < B ∧
    (sigma.arrs "FormulaFOStack").length < B ∧
    (sigma.arrs "FormulaSOStack").length < B ∧
    (sigma.arrs "FormulaPhaseStack").length < B

def FormulaTraversalInitialized (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Lax52.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet))
    (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "formulaCount" = 0 ∧
    sigma.vars "formulaSteps" = 0 ∧
    sigma.vars "formulaDepth" = 1 ∧
    (sigma.arrs "FormulaRootStack").length < B ∧
    (sigma.arrs "FormulaFOStack").length < B ∧
    (sigma.arrs "FormulaSOStack").length < B ∧
    (sigma.arrs "FormulaPhaseStack").length < B ∧
    FormulaStackRep I alphabet [initialFrame alphabet phi]
      (sigma.arrs "FormulaRootStack")
      (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack")
      (sigma.arrs "FormulaPhaseStack")

theorem initializeFormulaTraversal_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Lax52.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet))
    (formulaRoot : Nat) (h1 : 1 < B) (hmemB : I.memoryWords < B) :
    Spec B (FormulaTraversalReady B I alphabet phi formulaRoot)
      initializeFormulaTraversal
      (fun _ sigma' => FormulaTraversalInitialized B I alphabet phi sigma')
      50 := by
  intro sigma hready
  rcases hready with ⟨hloaded, hformulaRoot, hformulaRep,
    hrootSpace, hfoSpace, hsoSpace, hphaseSpace,
    hrootLenB, hfoLenB, hsoLenB, hphaseLenB⟩
  have hformulaRootB : formulaRoot < B := by
    have hvalid := Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hformulaRep)
    have harenaLength : (arenaWords I).length = I.memoryWords := by
      simp [arenaWords, WordImage.memoryWords]
    omega
  have hempty := formulaStackRep_nil I alphabet
    (sigma.arrs "FormulaRootStack") (sigma.arrs "FormulaFOStack")
    (sigma.arrs "FormulaSOStack") (sigma.arrs "FormulaPhaseStack")
  have hstack := formulaStackRep_push
    (frame := initialFrame alphabet phi) (root := formulaRoot)
    hempty (by simpa [Occurrence.raw, initialFrame] using hformulaRep)
    hrootSpace hfoSpace hsoSpace hphaseSpace
  have hstack' : FormulaStackRep I alphabet [initialFrame alphabet phi]
      ((sigma.arrs "FormulaRootStack").set 0 formulaRoot)
      ((sigma.arrs "FormulaFOStack").set 0 0)
      ((sigma.arrs "FormulaSOStack").set 0 0)
      ((sigma.arrs "FormulaPhaseStack").set 0 0) := by
    simpa only [initialFrame] using hstack
  unfold initializeFormulaTraversal
    Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [FormulaTraversalInitialized, ArenaLoaded]

end Lax53Proofs.FormulaArenaTraversalInit
