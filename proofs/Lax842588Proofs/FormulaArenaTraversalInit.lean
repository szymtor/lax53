import Lax842588Proofs.MSORamArenaRead
import Lax842588Proofs.FormulaArenaTraversalStack

/-!
Verified initialization of the charged intrinsic-formula traversal.
-/

namespace Lax842588Proofs.FormulaArenaTraversalInit

set_option maxHeartbeats 3000000
open Classical

open FirstOrder
open Lax146103.MSOSyntax
open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.FormulaArenaTraversalModel
open Lax842588Proofs.FormulaArenaTraversalStack
open Lax842588Proofs.MSORamArenaProgram
open Lax560851.WordArena

def FormulaTraversalReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Lax146103.MSOSyntax.Sentence
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
    (phi : Lax146103.MSOSyntax.Sentence
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
    (phi : Lax146103.MSOSyntax.Sentence
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
    have hvalid := Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax842588Proofs.ArenaSemantics.Represents.valid hformulaRep)
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
    simpa only [initialFrame] using! hstack
  unfold initializeFormulaTraversal
    Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [FormulaTraversalInitialized, ArenaLoaded]

end Lax842588Proofs.FormulaArenaTraversalInit
