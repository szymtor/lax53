import Lax53Proofs.AutomatonRamArenaTransitionPadding

/-!
Verification of the structural opening and fixed-header writes for one
represented transition.
-/

namespace Lax53Proofs.AutomatonRamArenaCorrectness

set_option maxHeartbeats 3000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53Proofs.ArrayInput
open Lax53.ValueTranslations
open Lax53Proofs.ArenaSemantics
open Lax53Proofs.AutomatonRamArenaProgram
open Lax53Proofs.AutomatonRamCorrectness
open Lax53Proofs.AutomatonRamArenaSegments
open Lax58.StructuralPresentation
open Lax58.StructuralCombinators
open Lax58.WordArena

def TransitionReady (B : Nat) (I : WordImage) (base R : Nat)
    (transition : TransitionCode) (rest : List TransitionCode)
    (prefixBefore : List Nat) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "R" = R ∧
    sigma.vars "T" < B ∧
    sigma.vars "width" < B ∧
    sigma.vars "records" + sigma.vars "T" * sigma.vars "width" = base ∧
    base + R + 3 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    SameBefore (sigma.arrs "P") prefixBefore base ∧
    ∃ cursor,
      sigma.vars "transitionCursor" = cursor ∧
      I.Represents cursor
        ((derivedPresentation : Presentation (List TransitionCode)).toRaw
          (transition :: rest))

def TransitionOpened (B : Nat) (I : WordImage) (base R : Nat)
    (transition : TransitionCode) (rest : List TransitionCode)
    (prefixBefore : List Nat) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "R" = R ∧
    base + R + 3 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    SameBefore (sigma.arrs "P") prefixBefore base ∧
    sigma.vars "transitionBase" = base ∧
    sigma.vars "arity" = 0 ∧
    WordsAt (sigma.arrs "P") base [transition.1, transition.2.1] ∧
    ∃ cursor childCursor,
      sigma.vars "transitionCursor" = cursor ∧
      I.Represents cursor
        ((derivedPresentation : Presentation (List TransitionCode)).toRaw
          (transition :: rest)) ∧
      sigma.vars "childCursor" = childCursor ∧
      I.Represents childCursor
        ((derivedPresentation : Presentation (List Nat)).toRaw transition.2.2)

theorem openTransition_spec (B : Nat) (I : WordImage) (base R : Nat)
    (transition : TransitionCode) (rest : List TransitionCode)
    (prefixBefore : List Nat) (h0 : 0 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B (TransitionReady B I base R transition rest prefixBefore)
      openTransition
      (fun _ sigma' =>
        TransitionOpened B I base R transition rest prefixBefore sigma')
      140 := by
  intro sigma hready
  rcases hready with ⟨hloaded, hR, hTB, hwidthB, hbase, hcapacity, hPlenB,
    hsame, cursor, hcursor, hrep⟩
  obtain ⟨transitionRoot, restCursor, hcursorTag, htransitionWord, hrestWord,
      htransitionRep, hrestRep⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.list_cons hrep
  have htransitionRep' : I.Represents transitionRoot
      ((prod nat (prod nat (list nat))).toRaw transition) := by
    simpa [derivedPresentation] using htransitionRep
  obtain ⟨symbolAddress, transitionTail, htransitionTag, hsymbolWord,
      htailWord, hsymbolRep, htailRep⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.prod_fields htransitionRep'
  obtain ⟨parentAddress, childAddress, htailTag, hparentWord, hchildWord,
      hparentRep, hchildRep⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.prod_fields htailRep
  have hsymbolPayload :=
    Lax53Proofs.ArenaSemantics.Represents.nat_payload hsymbolRep
  have hparentPayload :=
    Lax53Proofs.ArenaSemantics.Represents.nat_payload hparentRep
  have hchildRep' : I.Represents childAddress
      ((derivedPresentation : Presentation (List Nat)).toRaw transition.2.2) := by
    simpa [derivedPresentation] using hchildRep
  have hcursorValid := Lax53Proofs.ArenaSemantics.Represents.valid hrep
  have htransitionValid :=
    Lax53Proofs.ArenaSemantics.Represents.valid htransitionRep
  have htailValid := Lax53Proofs.ArenaSemantics.Represents.valid htailRep
  have hsymbolValid := Lax53Proofs.ArenaSemantics.Represents.valid hsymbolRep
  have hparentValid := Lax53Proofs.ArenaSemantics.Represents.valid hparentRep
  have hcursorLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hcursorValid
  have htransitionLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length htransitionValid
  have htailLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length htailValid
  have hsymbolLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hsymbolValid
  have hparentLen :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hparentValid
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hgetB (i : Nat) : (arenaWords I).getD i 0 < B :=
    getD_lt_of_mem_bound h0 hvaluesB
  have hgetOptB (i : Nat) : ((arenaWords I)[i]?).getD 0 < B := by
    simpa [List.getD_eq_getElem?_getD] using hgetB i
  have htransitionGetD : ((arenaWords I)[cursor + 1]?).getD 0 =
      transitionRoot := by
    simpa [List.getD_eq_getElem?_getD] using htransitionWord
  have hsymbolAddressGetD :
      ((arenaWords I)[transitionRoot + 1]?).getD 0 = symbolAddress := by
    simpa [List.getD_eq_getElem?_getD] using hsymbolWord
  have hsymbolGetD : ((arenaWords I)[symbolAddress + 1]?).getD 0 =
      transition.1 := by
    simpa [List.getD_eq_getElem?_getD] using hsymbolPayload
  have htailGetD : ((arenaWords I)[transitionRoot + 2]?).getD 0 =
      transitionTail := by
    simpa [List.getD_eq_getElem?_getD] using htailWord
  have hparentAddressGetD :
      ((arenaWords I)[transitionTail + 1]?).getD 0 = parentAddress := by
    simpa [List.getD_eq_getElem?_getD] using hparentWord
  have hparentGetD : ((arenaWords I)[parentAddress + 1]?).getD 0 =
      transition.2.1 := by
    simpa [List.getD_eq_getElem?_getD] using hparentPayload
  have hchildGetD : ((arenaWords I)[transitionTail + 2]?).getD 0 =
      childAddress := by
    simpa [List.getD_eq_getElem?_getD] using hchildWord
  have htransitionGetDB := hgetOptB (cursor + 1)
  have hsymbolAddressGetDB := hgetOptB (transitionRoot + 1)
  have hsymbolGetDB := hgetOptB (symbolAddress + 1)
  have htailGetDB := hgetOptB (transitionRoot + 2)
  have hparentAddressGetDB := hgetOptB (transitionTail + 1)
  have hparentGetDB := hgetOptB (parentAddress + 1)
  have hchildGetDB := hgetOptB (transitionTail + 2)
  have hslot0 : base < (sigma.arrs "P").length := by omega
  have hwords0 := wordsAt_set_singleton (value := transition.1) hslot0
  have hsame0 := sameBefore_set_after (index := base) (value := transition.1)
    hsame (Nat.le_refl _) hslot0
  have hslot1 : base + [transition.1].length <
      ((sigma.arrs "P").set base transition.1).length := by
    simp
    omega
  have hwords1 := wordsAt_set_append (value := transition.2.1) hwords0 hslot1
  have hsame1 := sameBefore_set_after
    (index := base + 1) (value := transition.2.1) hsame0 (by omega) (by simpa using hslot1)
  unfold openTransition AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [TransitionOpened, ArenaLoaded]
  all_goals (try omega)

/-- The freshly opened transition supplies the initial invariant for its
represented child scan, using the current header array as the preservation
reference. -/
theorem transitionOpened_childInv (B : Nat) (I : WordImage) (base R : Nat)
    (transition : TransitionCode) (rest : List TransitionCode)
    (prefixBefore : List Nat) (sigma : Env)
    (hopened : TransitionOpened B I base R transition rest prefixBefore sigma) :
    TransitionChildLoopInv B I base R transition.2.2 (sigma.arrs "P") sigma := by
  rcases hopened with ⟨hloaded, hR, hcapacity, hPlenB, hsame, hbase, harity,
    hheader, cursor, childCursor, hcursor, hrep, hchildCursor, hchildRep⟩
  refine ⟨hloaded, hbase, hR, ?_, hPlenB,
    sameBefore_refl _ _, [], transition.2.2, childCursor, ?_⟩
  · omega
  · simp [hchildCursor, hchildRep, harity, wordsAt_nil]

end Lax53Proofs.AutomatonRamArenaCorrectness
