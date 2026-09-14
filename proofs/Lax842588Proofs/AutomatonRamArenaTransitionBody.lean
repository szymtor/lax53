import Lax842588Proofs.AutomatonRamArenaTransitionFinish

/-!
Composition of the three verified phases that materialize one transition
record from the distinguished structural arena.
-/

namespace Lax842588Proofs.AutomatonRamArenaCorrectness

set_option maxHeartbeats 3000000

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.ValueTranslations
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax560851.WordArena

/-- Conservative charged cost of decoding one represented transition. -/
def transitionBodyCost (R : Nat) (transition : TransitionCode) : Nat :=
  140 + processTransitionChildrenCost R transition.2.2 + 50 + 10

theorem transitionBody_spec (B : Nat) (I : WordImage)
    (base R oldT : Nat) (transition : TransitionCode)
    (rest : List TransitionCode) (prefixBefore : List Nat)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : transition.2.2.length < B)
    (hTsuccB : oldT + 1 < B) :
    Spec B
      (fun sigma =>
        TransitionReady B I base R transition rest prefixBefore sigma ∧
          sigma.vars "T" = oldT)
      transitionBody
      (fun _ sigma' =>
        TransitionFinished B I base R oldT transition rest prefixBefore sigma')
      (transitionBodyCost R transition) := by
  have hopen : Spec B
      (fun sigma =>
        TransitionReady B I base R transition rest prefixBefore sigma ∧
          sigma.vars "T" = oldT)
      openTransition
      (fun _ sigma' =>
        TransitionOpened B I base R transition rest prefixBefore sigma' ∧
          sigma'.vars "T" = oldT)
      140 :=
    ((openTransition_spec B I base R transition rest prefixBefore
      (by omega) hmemB hvaluesB).frame).conseq
      (fun _ hpre => hpre.1)
      (fun sigma sigma' hpre hpost => by
        refine ⟨hpost.1, ?_⟩
        rw [hpost.2.1 "T" (by decide), hpre.2])
      le_rfl
  have hchildren : Spec B
      (fun sigma =>
        TransitionOpened B I base R transition rest prefixBefore sigma ∧
          sigma.vars "T" = oldT)
      processTransitionChildren
      (fun _ sigma' =>
        (∃ header,
          TransitionChildrenDone B I base R transition rest prefixBefore
            header sigma') ∧
          sigma'.vars "T" = oldT)
      (processTransitionChildrenCost R transition.2.2) :=
    ((processTransitionChildren_spec B I base R transition rest prefixBefore
      h1 hmemB hvaluesB hchildrenB).frame).conseq
      (fun _ hpre => hpre.1)
      (fun sigma sigma' hpre hpost => by
        refine ⟨⟨sigma.arrs "P", hpost.1⟩, ?_⟩
        rw [hpost.2.1 "T" (by decide), hpre.2])
      le_rfl
  have hfinish : Spec B
      (fun sigma =>
        (∃ header,
          TransitionChildrenDone B I base R transition rest prefixBefore
            header sigma) ∧
          sigma.vars "T" = oldT)
      finishTransition
      (fun _ sigma' =>
        TransitionFinished B I base R oldT transition rest prefixBefore sigma')
      50 := by
    intro sigma hpre
    rcases hpre.1 with ⟨header, hchildrenDone⟩
    exact (finishTransition_spec B I base R oldT transition rest prefixBefore
      header (by omega) hmemB hvaluesB hchildrenB hTsuccB).run
        ⟨hchildrenDone, hpre.2⟩
  have hfinishSkip : Spec B
      (fun sigma =>
        (∃ header,
          TransitionChildrenDone B I base R transition rest prefixBefore
            header sigma) ∧
          sigma.vars "T" = oldT)
      (.seq finishTransition .skip)
      (fun _ sigma' =>
        TransitionFinished B I base R oldT transition rest prefixBefore sigma')
      51 :=
    Spec.seq hfinish Spec.skip
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ hpost hskip => by simpa [hskip] using hpost)
  have htail : Spec B
      (fun sigma =>
        TransitionOpened B I base R transition rest prefixBefore sigma ∧
          sigma.vars "T" = oldT)
      (.seq processTransitionChildren (.seq finishTransition .skip))
      (fun _ sigma' =>
        TransitionFinished B I base R oldT transition rest prefixBefore sigma')
      (processTransitionChildrenCost R transition.2.2 + 51) :=
    Spec.seq hchildren hfinishSkip
      (fun _ _ _ hpost => hpost)
      (fun _ _ _ _ _ hpost => hpost)
  have hall : Spec B
      (fun sigma =>
        TransitionReady B I base R transition rest prefixBefore sigma ∧
          sigma.vars "T" = oldT)
      (.seq openTransition
        (.seq processTransitionChildren (.seq finishTransition .skip)))
      (fun _ sigma' =>
        TransitionFinished B I base R oldT transition rest prefixBefore sigma')
      (140 + (processTransitionChildrenCost R transition.2.2 + 51)) :=
    Spec.seq hopen htail
      (fun _ _ _ hpost => hpost)
      (fun _ _ _ _ _ hpost => hpost)
  simpa [transitionBody, Lax842588Proofs.AutomatonRamProgram.seqs] using
    hall.mono (by unfold transitionBodyCost; omega)

end Lax842588Proofs.AutomatonRamArenaCorrectness
