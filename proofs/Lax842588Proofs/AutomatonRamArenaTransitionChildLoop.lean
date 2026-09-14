import Lax842588Proofs.AutomatonRamArenaTransitionChild

/-!
Counted-loop verification for the represented child-state scan of one
transition record.
-/

namespace Lax842588Proofs.AutomatonRamArenaCorrectness

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.ValueTranslations
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- Conservative instruction budget for scanning the represented child list
of one transition. -/
def transitionChildLoopCost (children : List Nat) : Nat :=
  (1 + (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).size + 100) *
      children.length +
    1 + (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).size

private theorem transitionChildBody_decreases (B : Nat) (I : WordImage)
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
          children.length - sigma'.vars "arity" <
            children.length - sigma.vars "arity")
      100 := by
  refine (transitionChildBody_spec B I base R children prefixBefore h1 hmemB
    hvaluesB hchildrenB).post ?_
  intro sigma sigma' hpre hpost
  refine ⟨hpost.1, ?_⟩
  rcases hpre.1.2.2.2.2.2.2 with
    ⟨done, rest, cursor, hchildren, hcursor, hrep, harity, hwords⟩
  have hcondition := transitionChildCondition_value B I rest cursor sigma h1
    hmemB hpre.1.1 hcursor hrep
  cases rest with
  | nil =>
      have hfalse :
          (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).evalB B sigma =
            some false := by
        simpa only [List.isEmpty_nil, Bool.not_true] using hcondition
      rw [hpre.2] at hfalse
      contradiction
  | cons child rest =>
      have hlength := congrArg List.length hchildren
      simp only [List.length_append, List.length_cons] at hlength
      rw [hpost.2, harity]
      omega

theorem transitionChildLoop_spec (B : Nat) (I : WordImage)
    (base R : Nat) (children prefixBefore : List Nat)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : children.length < B) :
    Spec B (TransitionChildLoopInv B I base R children prefixBefore)
      transitionChildLoop
      (fun _ sigma' =>
        TransitionChildLoopInv B I base R children prefixBefore sigma' ∧
          (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).evalB B sigma' =
            some false)
      (transitionChildLoopCost children) := by
  unfold transitionChildLoop transitionChildLoopCost
  refine Spec.while_count
    (TransitionChildLoopInv B I base R children prefixBefore)
    (fun sigma => children.length - sigma.vars "arity")
    100
    (transitionChildCondition_defined B I base R children prefixBefore h1 hmemB)
    (transitionChildBody_decreases B I base R children prefixBefore h1 hmemB
      hvaluesB hchildrenB)
    (fun _ hInv => hInv) ?_
  intro sigma hInv
  have hsub : children.length - sigma.vars "arity" ≤ children.length :=
    Nat.sub_le _ _
  have hmul := Nat.mul_le_mul_left
    (1 + (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).size + 100)
    hsub
  simpa [Nat.add_assoc] using Nat.add_le_add_right hmul
    (1 + (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).size)

/-- On loop exit all represented children have been consumed, while precisely
the first `R` states have been materialized in the transition record. -/
theorem transitionChildLoop_completed_spec (B : Nat) (I : WordImage)
    (base R : Nat) (children prefixBefore : List Nat)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : children.length < B) :
    Spec B (TransitionChildLoopInv B I base R children prefixBefore)
      transitionChildLoop
      (fun _ sigma' =>
        ArenaLoaded I sigma' ∧
          sigma'.vars "transitionBase" = base ∧
          sigma'.vars "R" = R ∧
          base + 3 + R ≤ (sigma'.arrs "P").length ∧
          (sigma'.arrs "P").length < B ∧
          SameBefore (sigma'.arrs "P") prefixBefore (base + 3) ∧
          sigma'.vars "arity" = children.length ∧
          WordsAt (sigma'.arrs "P") (base + 3) (children.take R))
      (transitionChildLoopCost children) := by
  refine (transitionChildLoop_spec B I base R children prefixBefore h1 hmemB
    hvaluesB hchildrenB).post ?_
  intro sigma sigma' hpre hpost
  rcases hpost.1 with ⟨hloaded, hbase, hR, hcapacity, hPlenB, hsame,
    done, rest, cursor, hchildren, hcursor, hrep, harity, hwords⟩
  have hcondition := transitionChildCondition_value B I rest cursor sigma' h1
    hmemB hloaded hcursor hrep
  have hempty : rest = [] := by
    cases rest with
    | nil => rfl
    | cons child rest =>
        have htrue :
            (Cond.eq (.get "Arena" (.var "childCursor")) (.lit 1)).evalB B sigma' =
              some true := by
          simpa only [List.isEmpty_cons, Bool.not_false] using hcondition
        rw [hpost.2] at htrue
        contradiction
  subst rest
  simp only [List.append_nil] at hchildren
  subst children
  exact ⟨hloaded, hbase, hR, hcapacity, hPlenB, hsame, harity, hwords⟩

end Lax842588Proofs.AutomatonRamArenaCorrectness
