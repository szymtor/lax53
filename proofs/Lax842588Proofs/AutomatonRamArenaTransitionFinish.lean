import Lax842588Proofs.AutomatonRamArenaTransitionChildren

/-!
Verification of finalizing one fixed-width transition record and advancing the
represented transition-list cursor.
-/

namespace Lax842588Proofs.AutomatonRamArenaCorrectness

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588Proofs.ArrayInput
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamCorrectness
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

private theorem transitionPaddingWords_length_full (children : List Nat)
    (R : Nat) :
    (transitionPaddingWords children R R).length = R := by
  simp only [transitionPaddingWords, List.length_append, List.length_take,
    List.length_replicate, Nat.min_self]
  omega

private theorem transitionPaddingWords_eq_getDMap (children : List Nat)
    (R : Nat) :
    transitionPaddingWords children R R =
      (List.range R).map fun i => children.getD i 0 := by
  have hleft := transitionPaddingWords_length_full children R
  have hright : ((List.range R).map fun i => children.getD i 0).length = R := by
    simp
  apply List.ext_getElem (hleft.trans hright.symm)
  intro i hli hri
  have hi : i < R := by simpa [hleft] using hli
  rw [← List.getD_eq_getElem _ 0 hli]
  rw [transitionPaddingWords_getD children R i hi]
  simp

private theorem encodeTransitionFixed_eq_padding (R : Nat)
    (transition : TransitionCode) :
    encodeTransitionFixed R transition =
      [transition.1, transition.2.1, transition.2.2.length] ++
        transitionPaddingWords transition.2.2 R R := by
  rw [transitionPaddingWords_eq_getDMap]
  rfl

def TransitionFinished (B : Nat) (I : WordImage) (base R oldT : Nat)
    (transition : TransitionCode) (rest : List TransitionCode)
    (prefixBefore : List Nat) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "R" = R ∧
    base + R + 3 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    SameBefore (sigma.arrs "P") prefixBefore base ∧
    WordsAt (sigma.arrs "P") base (encodeTransitionFixed R transition) ∧
    sigma.vars "T" = oldT + 1 ∧
    I.Represents (sigma.vars "transitionCursor")
      ((derivedPresentation : Presentation (List TransitionCode)).toRaw rest)

theorem finishTransition_spec (B : Nat) (I : WordImage)
    (base R oldT : Nat) (transition : TransitionCode)
    (rest : List TransitionCode) (prefixBefore header : List Nat)
    (h0 : 0 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : transition.2.2.length < B)
    (hTsuccB : oldT + 1 < B) :
    Spec B
      (fun sigma =>
        TransitionChildrenDone B I base R transition rest prefixBefore header sigma ∧
          sigma.vars "T" = oldT)
      finishTransition
      (fun _ sigma' =>
        TransitionFinished B I base R oldT transition rest prefixBefore sigma')
      50 := by
  intro sigma hpre
  rcases hpre.1 with ⟨hloaded, hR, hcapacity, hPlenB, hsameHeader,
    hheaderPrefix, hheaderWords, hbase, harity, hchildrenWords,
    cursor, hcursor, hrep⟩
  obtain ⟨transitionRoot, restCursor, hcursorTag, htransitionWord, hrestWord,
      htransitionRep, hrestRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.list_cons hrep
  have hrestRep' : I.Represents restCursor
      ((derivedPresentation : Presentation (List TransitionCode)).toRaw rest) := by
    simpa [derivedPresentation] using! hrestRep
  have hcursorValid := Lax842588Proofs.ArenaSemantics.Represents.valid hrep
  have hcursorLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hcursorValid
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hgetB (i : Nat) : (arenaWords I).getD i 0 < B :=
    getD_lt_of_mem_bound h0 hvaluesB
  have hgetOptB (i : Nat) : ((arenaWords I)[i]?).getD 0 < B := by
    simpa [List.getD_eq_getElem?_getD] using hgetB i
  have hrestGetD : ((arenaWords I)[cursor + 2]?).getD 0 = restCursor := by
    simpa [List.getD_eq_getElem?_getD] using hrestWord
  have hrestGetDB := hgetOptB (cursor + 2)
  have hheaderCurrent :
      WordsAt (sigma.arrs "P") base
        [transition.1, transition.2.1] := by
    apply wordsAt_of_sameBefore hsameHeader hheaderWords
    simp
  have hslot2 : base + [transition.1, transition.2.1].length <
      (sigma.arrs "P").length := by
    simp
    omega
  have hheaderFinal := wordsAt_set_append
    (value := transition.2.2.length) hheaderCurrent hslot2
  have hchildrenSpace : base + 3 +
      (transitionPaddingWords transition.2.2 R R).length ≤
        (sigma.arrs "P").length := by
    rw [transitionPaddingWords_length_full]
    omega
  have hchildrenFinal := wordsAt_set_before
    (index := base + 2) (value := transition.2.2.length)
    hchildrenWords hchildrenSpace (by omega)
  have hrecordPadding := wordsAt_append hheaderFinal hchildrenFinal
  have hrecord : WordsAt
      ((sigma.arrs "P").set (base + 2) transition.2.2.length)
      base (encodeTransitionFixed R transition) := by
    rw [encodeTransitionFixed_eq_padding]
    simpa using hrecordPadding
  have hsameCurrent : SameBefore (sigma.arrs "P") prefixBefore base := by
    intro i hi
    exact (hsameHeader i (by omega)).trans (hheaderPrefix i hi)
  have hsameFinal := sameBefore_set_after
    (index := base + 2) (value := transition.2.2.length)
    hsameCurrent (by omega) (by omega)
  unfold finishTransition AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [TransitionFinished, ArenaLoaded]

end Lax842588Proofs.AutomatonRamArenaCorrectness
