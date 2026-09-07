import Lax53Proofs.AutomatonRamArenaBody
import Lax53Proofs.AutomatonRamArenaList
import Lax53Proofs.AutomatonRamArenaSegments

/-!
Verification of the represented child-state scan for one transition record.
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

def TransitionChildLoopInv (B : Nat) (I : WordImage) (base R : Nat)
    (children : List Nat) (prefixBefore : List Nat) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "transitionBase" = base ∧
    sigma.vars "R" = R ∧
    base + 3 + R ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    SameBefore (sigma.arrs "P") prefixBefore (base + 3) ∧
    ∃ done rest cursor,
      children = done ++ rest ∧
      sigma.vars "childCursor" = cursor ∧
      I.Represents cursor
        ((derivedPresentation : Presentation (List Nat)).toRaw rest) ∧
      sigma.vars "arity" = done.length ∧
      WordsAt (sigma.arrs "P") (base + 3) (done.take R)

private theorem take_append_singleton_of_lt (xs : List Nat) (x R : Nat)
    (h : xs.length < R) :
    (xs ++ [x]).take R = xs.take R ++ [x] := by
  rw [List.take_append]
  have htake : xs.take R = xs := (List.take_eq_self_iff xs).mpr (by omega)
  have hsub : 0 < R - xs.length := Nat.sub_pos_of_lt h
  cases hdiff : R - xs.length with
  | zero => simp_all
  | succ n => simp [htake]

private theorem take_append_singleton_of_le (xs : List Nat) (x R : Nat)
    (h : R ≤ xs.length) :
    (xs ++ [x]).take R = xs.take R := by
  rw [List.take_append]
  simp [Nat.sub_eq_zero_of_le h]

theorem transitionChildCondition_value (B : Nat) (I : WordImage)
    (rest : List Nat) (cursor : Nat) (sigma : Env)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hloaded : ArenaLoaded I sigma)
    (hcursor : sigma.vars "childCursor" = cursor)
    (hrep : I.Represents cursor
      ((derivedPresentation : Presentation (List Nat)).toRaw rest)) :
    (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).evalB B sigma =
      some (!rest.isEmpty) := by
  simpa [representedListCondition, WordImage.pairTag, derivedPresentation] using
    (representedListCondition_value B I nat rest cursor "childCursor" sigma
      h1 hmemB hloaded hcursor (by simpa [derivedPresentation] using hrep))

theorem transitionChildCondition_defined (B : Nat) (I : WordImage)
    (base R : Nat) (children prefixBefore : List Nat)
    (h1 : 1 < B) (hmemB : I.memoryWords < B) :
    ∀ sigma, TransitionChildLoopInv B I base R children prefixBefore sigma →
      ∃ value,
        (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).evalB B sigma =
          some value := by
  intro sigma hInv
  rcases hInv.2.2.2.2.2.2 with
    ⟨done, rest, cursor, hchildren, hcursor, hrep, harity, hwords⟩
  exact ⟨!rest.isEmpty,
    transitionChildCondition_value B I rest cursor sigma h1 hmemB hInv.1 hcursor hrep⟩

theorem transitionChildBody_spec (B : Nat) (I : WordImage)
    (base R : Nat) (children prefixBefore : List Nat)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : children.length < B) :
    Spec B
      (fun sigma => TransitionChildLoopInv B I base R children prefixBefore sigma ∧
        (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).evalB B sigma =
          some true)
      transitionChildBody
      (fun sigma sigma' =>
        TransitionChildLoopInv B I base R children prefixBefore sigma' ∧
          sigma'.vars "arity" = sigma.vars "arity" + 1)
      100 := by
  intro sigma hpre
  rcases hpre.1 with ⟨hloaded, hbase, hR, hcapacity, hPlenB, hsame,
    done, rest, cursor, hchildren, hcursor, hrep, harity, hwords⟩
  have hcondition := transitionChildCondition_value B I rest cursor sigma h1 hmemB
    hloaded hcursor hrep
  cases rest with
  | nil =>
      have hfalse :
          (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).evalB B sigma =
            some false := by
        simpa only [List.isEmpty_nil, Bool.not_true] using hcondition
      have htrue := hpre.2
      rw [hfalse] at htrue
      contradiction
  | cons child rest =>
      obtain ⟨valueAddress, restAddress, hcursorTag, hvalueWord, hrestWord,
          hvalueRep, hrestRep⟩ :=
        Lax53Proofs.ArenaSemantics.Represents.list_cons hrep
      have hcursorValid := Lax53Proofs.ArenaSemantics.Represents.valid hrep
      have hvalueValid := Lax53Proofs.ArenaSemantics.Represents.valid hvalueRep
      have hrestValid := Lax53Proofs.ArenaSemantics.Represents.valid hrestRep
      have hcursorLen :=
        Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hcursorValid
      have hvalueLen :=
        Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hvalueValid
      have hrestLen :=
        Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hrestValid
      have harenaLength : (arenaWords I).length = I.memoryWords := by
        simp [arenaWords, WordImage.memoryWords]
      have hgetB (i : Nat) : (arenaWords I).getD i 0 < B :=
        getD_lt_of_mem_bound (by omega) hvaluesB
      have hgetOptB (i : Nat) : ((arenaWords I)[i]?).getD 0 < B := by
        simpa [List.getD_eq_getElem?_getD] using hgetB i
      have hvalueGetD : ((arenaWords I)[cursor + 1]?).getD 0 = valueAddress := by
        simpa [List.getD_eq_getElem?_getD] using hvalueWord
      have hrestGetD : ((arenaWords I)[cursor + 2]?).getD 0 = restAddress := by
        simpa [List.getD_eq_getElem?_getD] using hrestWord
      have hchildWord :=
        Lax53Proofs.ArenaSemantics.Represents.nat_payload hvalueRep
      have hchildGetD : ((arenaWords I)[valueAddress + 1]?).getD 0 = child := by
        simpa [List.getD_eq_getElem?_getD] using hchildWord
      have hvalueGetDB := hgetOptB (cursor + 1)
      have hrestGetDB := hgetOptB (cursor + 2)
      have hchildGetDB := hgetOptB (valueAddress + 1)
      have hrestRep' : I.Represents restAddress
          ((derivedPresentation : Presentation (List Nat)).toRaw rest) := by
        simpa [derivedPresentation] using hrestRep
      have hdoneLength : done.length < children.length := by
        have hlength := congrArg List.length hchildren
        simp only [List.length_append, List.length_cons] at hlength
        omega
      by_cases hstore : done.length < R
      · have htakeLength : (done.take R).length = done.length := by
          simp only [List.length_take]
          omega
        have hslot : base + 3 + (done.take R).length <
            (sigma.arrs "P").length := by
          rw [htakeLength]
          omega
        have hwords' := wordsAt_set_append (value := child) hwords hslot
        have htake := take_append_singleton_of_lt done child R hstore
        have hsame' := sameBefore_set_after
          (index := base + 3 + (done.take R).length) (value := child)
          hsame (by omega) hslot
        have hwordsFinal :
            WordsAt ((sigma.arrs "P").set (base + 3 + done.length) child)
              (base + 3) ((done ++ [child]).take R) := by
          rw [htake]
          simpa [htakeLength] using hwords'
        have hsameFinal :
            SameBefore ((sigma.arrs "P").set (base + 3 + done.length) child)
              prefixBefore (base + 3) := by
          simpa [htakeLength] using hsame'
        unfold transitionChildBody AutomatonRamProgram.seqs
        run_vcg
        all_goals simp_all [TransitionChildLoopInv, ArenaLoaded]
        all_goals (try omega)
        all_goals
          refine ⟨done ++ [child], rest, ?_⟩
          simp_all
      · have htake := take_append_singleton_of_le done child R
          (Nat.le_of_not_gt hstore)
        have hwords' : WordsAt (sigma.arrs "P") (base + 3)
            ((done ++ [child]).take R) := by
          rw [htake]
          exact hwords
        unfold transitionChildBody AutomatonRamProgram.seqs
        run_vcg
        all_goals simp_all [TransitionChildLoopInv, ArenaLoaded]
        all_goals (try omega)
        all_goals
          refine ⟨done ++ [child], rest, ?_⟩
          simp_all

end Lax53Proofs.AutomatonRamArenaCorrectness
