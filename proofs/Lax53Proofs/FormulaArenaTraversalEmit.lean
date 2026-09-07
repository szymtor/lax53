import Lax53Proofs.FormulaArenaTraversalLoad
import Lax53Proofs.FormulaArenaTraversalOrder
import Lax53Proofs.ImpArrayLengths

/-!
Verification of the formula traversal's postorder emit/pop branch.
-/

namespace Lax53Proofs.FormulaArenaTraversalEmit

set_option maxHeartbeats 3000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53.RankedTree
open Lax53.ValueTranslations
open Lax53Proofs.ArenaSemantics
open Lax53Proofs.AutomatonRamArenaCorrectness
open Lax53Proofs.FormulaArenaTraversalModel
open Lax53Proofs.FormulaArenaTraversalStack
open Lax53Proofs.FormulaArenaTraversalOrder
open Lax53Proofs.FormulaArenaTraversalLoad
open Lax53Proofs.MSORamArenaProgram
open Lax58.WordArena

def FormulaEmitReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  FormulaFrameLoaded B I alphabet current outer sigma ∧
    sigma.vars "formulaCount" = produced.length ∧
    produced.length + 1 < B ∧
    produced.length < (sigma.arrs "FormulaOrder").length ∧
    produced.length < (sigma.arrs "FormulaFOOrder").length ∧
    produced.length < (sigma.arrs "FormulaSOOrder").length ∧
    (sigma.arrs "FormulaOrder").length < B ∧
    (sigma.arrs "FormulaFOOrder").length < B ∧
    (sigma.arrs "FormulaSOOrder").length < B ∧
    FormulaOrderRep I alphabet produced
      (sigma.arrs "FormulaOrder")
      (sigma.arrs "FormulaFOOrder")
      (sigma.arrs "FormulaSOOrder")

def FormulaEmitted (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "formulaCount" = (produced ++ [current.occurrence]).length ∧
    sigma.vars "formulaDepth" = outer.length ∧
    (sigma.arrs "FormulaRootStack").length < B ∧
    (sigma.arrs "FormulaFOStack").length < B ∧
    (sigma.arrs "FormulaSOStack").length < B ∧
    (sigma.arrs "FormulaPhaseStack").length < B ∧
    (sigma.arrs "FormulaOrder").length < B ∧
    (sigma.arrs "FormulaFOOrder").length < B ∧
    (sigma.arrs "FormulaSOOrder").length < B ∧
    FormulaStackRep I alphabet outer
      (sigma.arrs "FormulaRootStack")
      (sigma.arrs "FormulaFOStack")
      (sigma.arrs "FormulaSOStack")
      (sigma.arrs "FormulaPhaseStack") ∧
    FormulaOrderRep I alphabet (produced ++ [current.occurrence])
      (sigma.arrs "FormulaOrder")
      (sigma.arrs "FormulaFOOrder")
      (sigma.arrs "FormulaSOOrder")

theorem emitFormula_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) :
    Spec B (FormulaEmitReady B I alphabet produced current outer)
      emitFormula
      (fun _ sigma' => FormulaEmitted B I alphabet produced current outer sigma')
      50 := by
  intro sigma hready
  rcases hready with ⟨hloadedFrame, hcount, hcountB,
    hrootOrderSpace, hfoOrderSpace, hsoOrderSpace,
    hrootOrderLenB, hfoOrderLenB, hsoOrderLenB, horder⟩
  rcases hloadedFrame with ⟨hframeReady, formulaRoot, hrootB, hindex,
    hcurrentRoot, hcurrentFO, hcurrentSO, hphase, htag, htagB, hformulaRep⟩
  rcases hframeReady with ⟨hloaded, hdepth, hrootCapacity, hfoCapacity,
    hsoCapacity, hphaseCapacity, hrootStackLenB, hfoStackLenB,
    hsoStackLenB, hphaseStackLenB, hfoB, hsoB, hphaseB, hstack⟩
  have hstack' := formulaStackRep_pop hstack
  have horder' := formulaOrderRep_append current.occurrence formulaRoot horder
    hformulaRep hrootOrderSpace hfoOrderSpace hsoOrderSpace
  unfold emitFormula Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [FormulaEmitted, ArenaLoaded]
  all_goals try omega

end Lax53Proofs.FormulaArenaTraversalEmit
