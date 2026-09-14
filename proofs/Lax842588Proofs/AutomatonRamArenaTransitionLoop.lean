import Lax842588Proofs.AutomatonRamArenaTransitionBody

/-!
Counted-loop verification for materializing the complete fixed-width
transition table from its certified structural list.
-/

namespace Lax842588Proofs.AutomatonRamArenaCorrectness

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.AutomatonTableEncoding
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- Proof-local name for the concrete list-cursor guard used by
`transitionLoop`. -/
def transitionCondition : Cond :=
  .eq (.get "Arena" (.var "transitionCursor")) (.lit 1)

/-- The consecutive evaluator rows belonging to a transition-list prefix. -/
def transitionRows (R : Nat) (transitions : List TransitionCode) : List Nat :=
  transitions.flatMap (encodeTransitionFixed R)

@[simp] theorem transitionRows_length (R : Nat)
    (transitions : List TransitionCode) :
    (transitionRows R transitions).length = transitions.length * (R + 3) := by
  simp [transitionRows, List.length_flatMap, encodeTransitionFixed_length]

@[simp] theorem transitionRows_append (R : Nat)
    (xs ys : List TransitionCode) :
    transitionRows R (xs ++ ys) = transitionRows R xs ++ transitionRows R ys := by
  simp [transitionRows]

/-- The prefix already consumed by the transition cursor occupies exactly the
corresponding consecutive fixed-width rows. -/
def TransitionLoopInv (B : Nat) (I : WordImage) (R records : Nat)
    (transitions : List TransitionCode) (prefixBefore : List Nat)
    (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "R" = R ∧
    sigma.vars "width" = R + 3 ∧
    sigma.vars "records" = records ∧
    transitions.length < B ∧
    R + 3 < B ∧
    records + transitions.length * (R + 3) ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    SameBefore (sigma.arrs "P") prefixBefore records ∧
    ∃ done rest cursor,
      transitions = done ++ rest ∧
      sigma.vars "T" = done.length ∧
      sigma.vars "transitionCursor" = cursor ∧
      I.Represents cursor
        ((derivedPresentation : Presentation (List TransitionCode)).toRaw rest) ∧
      WordsAt (sigma.arrs "P") records (transitionRows R done)

theorem transitionCondition_value (B : Nat) (I : WordImage)
    (rest : List TransitionCode) (cursor : Nat) (sigma : Env)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hloaded : ArenaLoaded I sigma)
    (hcursor : sigma.vars "transitionCursor" = cursor)
    (hrep : I.Represents cursor
      ((derivedPresentation : Presentation (List TransitionCode)).toRaw rest)) :
    transitionCondition.evalB B sigma = some (!rest.isEmpty) := by
  simpa [transitionCondition, representedListCondition, WordImage.pairTag,
    derivedPresentation] using
    (representedListCondition_value B I
      (derivedPresentation : Presentation TransitionCode) rest cursor
      "transitionCursor" sigma h1 hmemB hloaded hcursor
      (by simpa [derivedPresentation] using hrep))

theorem transitionCondition_defined (B : Nat) (I : WordImage)
    (R records : Nat) (transitions : List TransitionCode)
    (prefixBefore : List Nat)
    (h1 : 1 < B) (hmemB : I.memoryWords < B) :
    ∀ sigma, TransitionLoopInv B I R records transitions prefixBefore sigma →
      ∃ value, transitionCondition.evalB B sigma = some value := by
  intro sigma hInv
  rcases hInv.2.2.2.2.2.2.2.2.2 with
    ⟨done, rest, cursor, htransitions, hT, hcursor, hrep, hrows⟩
  exact ⟨!rest.isEmpty,
    transitionCondition_value B I rest cursor sigma h1 hmemB hInv.1 hcursor hrep⟩

/-- A caller-chosen uniform upper bound for any one represented transition
keeps the counted-loop rule independent of how the final global polynomial
bound is packaged. -/
def transitionLoopCost (transitions : List TransitionCode)
    (stepBudget : Nat) : Nat :=
  (1 + transitionCondition.size + stepBudget) * transitions.length +
    1 + transitionCondition.size

private theorem transitionBody_decreases (B : Nat) (I : WordImage)
    (R records : Nat) (transitions : List TransitionCode)
    (prefixBefore : List Nat)
    (stepBudget : Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : ∀ transition ∈ transitions,
      transition.2.2.length < B)
    (hstep : ∀ transition ∈ transitions,
      transitionBodyCost R transition ≤ stepBudget) :
    Spec B
      (fun sigma =>
        TransitionLoopInv B I R records transitions prefixBefore sigma ∧
        transitionCondition.evalB B sigma = some true)
      transitionBody
      (fun sigma sigma' =>
        TransitionLoopInv B I R records transitions prefixBefore sigma' ∧
          transitions.length - sigma'.vars "T" <
            transitions.length - sigma.vars "T")
      stepBudget := by
  intro sigma hpre
  rcases hpre.1 with ⟨hloaded, hR, hwidth, hrecords, htransitionsB,
    hwidthB, hcapacity, hPlenB, hprefix, done, rest, cursor, htransitions,
    hT, hcursor, hrep, hrows⟩
  have hcondition := transitionCondition_value B I rest cursor sigma h1 hmemB
    hloaded hcursor hrep
  cases rest with
  | nil =>
      have hfalse : transitionCondition.evalB B sigma = some false := by
        simpa only [List.isEmpty_nil, Bool.not_true] using hcondition
      rw [hpre.2] at hfalse
      contradiction
  | cons transition rest =>
      have htransitionMem : transition ∈ transitions := by
        rw [htransitions]
        simp
      have hdoneLt : done.length < transitions.length := by
        have hlength := congrArg List.length htransitions
        simp only [List.length_append, List.length_cons] at hlength
        omega
      let base := records + done.length * (R + 3)
      have hready : TransitionReady B I base R transition rest
          (sigma.arrs "P") sigma := by
        refine ⟨hloaded, hR, ?_, ?_, ?_, ?_, hPlenB,
          sameBefore_refl _ _, cursor, hcursor, hrep⟩
        · rw [hT]
          omega
        · rw [hwidth]
          exact hwidthB
        · simp [base, hT, hwidth, hrecords]
        · have hlength := congrArg List.length htransitions
          simp only [List.length_append, List.length_cons] at hlength
          calc
            base + R + 3 = records + (done.length + 1) * (R + 3) := by
              simp [base, Nat.add_mul]
              omega
            _ ≤ records + transitions.length * (R + 3) :=
              Nat.add_le_add_left
                (Nat.mul_le_mul_right (R + 3) (by omega)) records
            _ ≤ (sigma.arrs "P").length := hcapacity
      have hone := (transitionBody_spec B I base R done.length transition rest
        (sigma.arrs "P") h1 hmemB hvaluesB (hchildrenB _ htransitionMem)
        (by omega)).frame
      obtain ⟨sigma', hrun, hpost⟩ := hone.run ⟨hready, hT⟩
      rcases hpost.1 with ⟨hloaded', hR', hrecordCapacity, hPlenB', hsame,
        hrecord, hT', hrestRep⟩
      have hrecords' : sigma'.vars "records" = records := by
        rw [hpost.2.1 "records" (by decide), hrecords]
      have hwidth' : sigma'.vars "width" = R + 3 := by
        rw [hpost.2.1 "width" (by decide), hwidth]
      have hprior : WordsAt (sigma'.arrs "P") records
          (transitionRows R done) := by
        apply wordsAt_of_sameBefore hsame hrows
        simp [base]
      have hrows' : WordsAt (sigma'.arrs "P") records
          (transitionRows R (done ++ [transition])) := by
        rw [transitionRows_append]
        apply wordsAt_append hprior
        rw [transitionRows_length]
        simpa [transitionRows, base] using hrecord
      have hPlength : (sigma'.arrs "P").length =
          (sigma.arrs "P").length :=
        Lax842588Proofs.Run.arrayLength_eq hrun "P"
      have hprefix' : SameBefore (sigma'.arrs "P") prefixBefore records := by
        apply sameBefore_trans
          (second := sigma.arrs "P")
          (third := prefixBefore)
        · intro i hi
          apply hsame i
          dsimp [base]
          omega
        · exact hprefix
      have hInv' :
          TransitionLoopInv B I R records transitions prefixBefore sigma' := by
        refine ⟨hloaded', hR', hwidth', hrecords', htransitionsB, hwidthB,
          ?_, hPlenB', hprefix', done ++ [transition], rest,
          sigma'.vars "transitionCursor", ?_⟩
        · rw [hPlength]
          exact hcapacity
        · refine ⟨?_, ?_, rfl, hrestRep, hrows'⟩
          · simpa [List.append_assoc] using htransitions
          · simpa using hT'
      refine ⟨sigma', hrun.mono (hstep _ htransitionMem), hInv', ?_⟩
      rw [hT', hT]
      omega

theorem transitionLoop_spec (B : Nat) (I : WordImage)
    (R records : Nat) (transitions : List TransitionCode)
    (prefixBefore : List Nat)
    (stepBudget : Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : ∀ transition ∈ transitions,
      transition.2.2.length < B)
    (hstep : ∀ transition ∈ transitions,
      transitionBodyCost R transition ≤ stepBudget) :
    Spec B (TransitionLoopInv B I R records transitions prefixBefore)
      transitionLoop
      (fun _ sigma' =>
        TransitionLoopInv B I R records transitions prefixBefore sigma' ∧
          transitionCondition.evalB B sigma' = some false)
      (transitionLoopCost transitions stepBudget) := by
  unfold transitionLoop transitionLoopCost
  refine Spec.while_count
    (TransitionLoopInv B I R records transitions prefixBefore)
    (fun sigma => transitions.length - sigma.vars "T")
    stepBudget
    (transitionCondition_defined B I R records transitions prefixBefore h1 hmemB)
    (transitionBody_decreases B I R records transitions prefixBefore stepBudget h1 hmemB
      hvaluesB hchildrenB hstep)
    (fun _ hInv => hInv) ?_
  intro sigma hInv
  have hsub : transitions.length - sigma.vars "T" ≤ transitions.length :=
    Nat.sub_le _ _
  have hmul := Nat.mul_le_mul_left
    (1 + transitionCondition.size + stepBudget) hsub
  simpa only [Nat.add_assoc] using
    Nat.add_le_add_right hmul (1 + transitionCondition.size)

/-- On exit, the entire represented transition list has become the exact
fixed-width table segment expected by the evaluator. -/
theorem transitionLoop_completed_spec (B : Nat) (I : WordImage)
    (R records : Nat) (transitions : List TransitionCode)
    (prefixBefore : List Nat)
    (stepBudget : Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : ∀ transition ∈ transitions,
      transition.2.2.length < B)
    (hstep : ∀ transition ∈ transitions,
      transitionBodyCost R transition ≤ stepBudget) :
    Spec B (TransitionLoopInv B I R records transitions prefixBefore)
      transitionLoop
      (fun _ sigma' =>
        TransitionLoopInv B I R records transitions prefixBefore sigma' ∧
          sigma'.vars "T" = transitions.length ∧
          WordsAt (sigma'.arrs "P") records (transitionRows R transitions))
      (transitionLoopCost transitions stepBudget) := by
  refine (transitionLoop_spec B I R records transitions prefixBefore stepBudget h1 hmemB
    hvaluesB hchildrenB hstep).post ?_
  intro sigma sigma' hpre hpost
  rcases hpost.1.2.2.2.2.2.2.2.2.2 with
    ⟨done, rest, cursor, htransitions, hT, hcursor, hrep, hrows⟩
  have hcondition := transitionCondition_value B I rest cursor sigma' h1
    hmemB hpost.1.1 hcursor hrep
  have hempty : rest = [] := by
    cases rest with
    | nil => rfl
    | cons transition rest =>
        have htrue : transitionCondition.evalB B sigma' = some true := by
          simpa only [List.isEmpty_cons, Bool.not_false] using hcondition
        rw [hpost.2] at htrue
        contradiction
  subst rest
  simp only [List.append_nil] at htransitions
  subst done
  exact ⟨hpost.1, hT, hrows⟩

end Lax842588Proofs.AutomatonRamArenaCorrectness
