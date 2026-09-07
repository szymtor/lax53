import Lax53Proofs.AutomatonRamArenaTransitionOpen

/-!
Composition of the charged represented-child scan and explicit padding phase
for one already opened transition.
-/

namespace Lax53Proofs.AutomatonRamArenaCorrectness

set_option maxHeartbeats 3000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53.ValueTranslations
open Lax53Proofs.ArenaSemantics
open Lax53Proofs.AutomatonRamArenaProgram
open Lax53Proofs.AutomatonRamArenaSegments
open Lax58.StructuralPresentation
open Lax58.StructuralCombinators
open Lax58.WordArena

def TransitionChildrenDone (B : Nat) (I : WordImage) (base R : Nat)
    (transition : TransitionCode) (rest : List TransitionCode)
    (prefixBefore header : List Nat) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "R" = R ∧
    base + R + 3 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    SameBefore (sigma.arrs "P") header (base + 3) ∧
    SameBefore header prefixBefore base ∧
    WordsAt header base [transition.1, transition.2.1] ∧
    sigma.vars "transitionBase" = base ∧
    sigma.vars "arity" = transition.2.2.length ∧
    WordsAt (sigma.arrs "P") (base + 3)
      (transitionPaddingWords transition.2.2 R R) ∧
    ∃ cursor,
      sigma.vars "transitionCursor" = cursor ∧
      I.Represents cursor
        ((derivedPresentation : Presentation (List TransitionCode)).toRaw
          (transition :: rest))

def processTransitionChildrenCost (R : Nat) (children : List Nat) : Nat :=
  transitionChildLoopCost children + transitionPaddingLoopCost R + 10

theorem processTransitionChildren_spec (B : Nat) (I : WordImage)
    (base R : Nat) (transition : TransitionCode)
    (rest : List TransitionCode) (prefixBefore : List Nat)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : transition.2.2.length < B) :
    Spec B (TransitionOpened B I base R transition rest prefixBefore)
      processTransitionChildren
      (fun sigma sigma' =>
        TransitionChildrenDone B I base R transition rest prefixBefore
          (sigma.arrs "P") sigma')
      (processTransitionChildrenCost R transition.2.2) := by
  intro sigma hopened
  have hchildFrame := (transitionChildLoop_completed_spec B I base R
    transition.2.2 (sigma.arrs "P") h1 hmemB hvaluesB hchildrenB).frame
  have hchild : Spec B
      (TransitionChildLoopInv B I base R transition.2.2 (sigma.arrs "P"))
      transitionChildLoop
      (fun tau tau' =>
        (ArenaLoaded I tau' ∧
          tau'.vars "transitionBase" = base ∧
          tau'.vars "R" = R ∧
          base + 3 + R ≤ (tau'.arrs "P").length ∧
          (tau'.arrs "P").length < B ∧
          SameBefore (tau'.arrs "P") (sigma.arrs "P") (base + 3) ∧
          tau'.vars "arity" = transition.2.2.length ∧
          WordsAt (tau'.arrs "P") (base + 3) (transition.2.2.take R)) ∧
        tau'.vars "transitionCursor" = tau.vars "transitionCursor")
      (transitionChildLoopCost transition.2.2) := hchildFrame.post (by
    intro tau tau' hpre hpost
    exact ⟨hpost.1, hpost.2.1 "transitionCursor" (by decide)⟩)
  have hpaddingFrame := (transitionPaddingLoop_completed_spec B I base R
    transition.2.2 (sigma.arrs "P")).frame
  have hpadding : Spec B
      (TransitionPaddingLoopInv B I base R transition.2.2 (sigma.arrs "P"))
      transitionPaddingLoop
      (fun tau tau' =>
        (ArenaLoaded I tau' ∧
          tau'.vars "transitionBase" = base ∧
          tau'.vars "R" = R ∧
          base + 3 + R ≤ (tau'.arrs "P").length ∧
          (tau'.arrs "P").length < B ∧
          SameBefore (tau'.arrs "P") (sigma.arrs "P") (base + 3) ∧
          tau'.vars "arity" = transition.2.2.length ∧
          WordsAt (tau'.arrs "P") (base + 3)
            (transitionPaddingWords transition.2.2 R R)) ∧
        tau'.vars "transitionCursor" = tau.vars "transitionCursor")
      (transitionPaddingLoopCost R) := hpaddingFrame.post (by
    intro tau tau' hpre hpost
    exact ⟨hpost.1, hpost.2.1 "transitionCursor" (by decide)⟩)
  unfold processTransitionChildren processTransitionChildrenCost
    AutomatonRamProgram.seqs
  run_vcg [hchild, hpadding]
  all_goals (try exact
    transitionOpened_childInv B I base R transition rest prefixBefore sigma hopened)
  all_goals simp_all [TransitionOpened, TransitionPaddingLoopInv,
    TransitionChildrenDone, ArenaLoaded]
  all_goals (try omega)

end Lax53Proofs.AutomatonRamArenaCorrectness
