import Lax53Proofs.AutomatonRamArenaTransitionChildLoop

/-!
Verification of the explicit zero-padding phase for one fixed-width transition
record. This phase realizes the evaluator's `List.getD` convention without
assuming anything about the previous contents of its private workspace.
-/

namespace Lax53Proofs.AutomatonRamArenaCorrectness

set_option maxHeartbeats 3000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53Proofs.ArenaSemantics
open Lax53Proofs.AutomatonRamArenaProgram
open Lax53Proofs.AutomatonRamArenaSegments
open Lax58.WordArena

/-- The already materialized child prefix followed by all zero slots written
up to `padding`. -/
def transitionPaddingWords (children : List Nat) (R padding : Nat) : List Nat :=
  children.take R ++
    List.replicate (min padding R - min children.length R) 0

@[simp] theorem transitionPaddingWords_start (children : List Nat) (R : Nat) :
    transitionPaddingWords children R children.length = children.take R := by
  simp [transitionPaddingWords]

theorem transitionPaddingWords_getD (children : List Nat) (R i : Nat)
    (hi : i < R) :
    (transitionPaddingWords children R R).getD i 0 = children.getD i 0 := by
  unfold transitionPaddingWords
  simp only [Nat.min_self]
  by_cases hchild : i < children.length
  · have htake : i < (children.take R).length := by
      simp only [List.length_take]
      omega
    rw [List.getD_append _ _ _ _ htake]
    rw [List.getD_eq_getElem _ _ htake]
    rw [List.getD_eq_getElem _ _ hchild]
    simp
  · have hchildrenR : children.length < R := by omega
    have hright : (children.take R).length ≤ i := by
      simp only [List.length_take]
      rw [Nat.min_eq_right (Nat.le_of_lt hchildrenR)]
      omega
    rw [List.getD_append_right _ _ _ _ hright]
    have hoffset : i - (children.take R).length <
        R - min children.length R := by
      simp only [List.length_take]
      rw [Nat.min_eq_right (Nat.le_of_lt hchildrenR)]
      rw [Nat.min_eq_left (Nat.le_of_lt hchildrenR)]
      omega
    rw [List.getD_replicate (x := 0) (y := 0) hoffset]
    rw [List.getD_eq_default children 0 (Nat.le_of_not_gt hchild)]

def TransitionPaddingLoopInv (B : Nat) (I : WordImage) (base R : Nat)
    (children : List Nat) (prefixBefore : List Nat) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "transitionBase" = base ∧
    sigma.vars "R" = R ∧
    base + 3 + R ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    SameBefore (sigma.arrs "P") prefixBefore (base + 3) ∧
    sigma.vars "arity" = children.length ∧
    ∃ padding,
      sigma.vars "padding" = padding ∧
      children.length ≤ padding ∧
      padding < B ∧
      WordsAt (sigma.arrs "P") (base + 3)
        (transitionPaddingWords children R padding)

private theorem transitionPaddingWords_length_of_lt (children : List Nat)
    (R padding : Nat) (hchildren : children.length ≤ padding)
    (hpadding : padding < R) :
    (transitionPaddingWords children R padding).length = padding := by
  have hchildrenR : children.length < R := hchildren.trans_lt hpadding
  simp only [transitionPaddingWords, List.length_append, List.length_take,
    List.length_replicate]
  rw [Nat.min_eq_right (Nat.le_of_lt hchildrenR)]
  rw [Nat.min_eq_left (Nat.le_of_lt hpadding)]
  rw [Nat.min_eq_left (Nat.le_of_lt hchildrenR)]
  omega

private theorem transitionPaddingWords_succ (children : List Nat)
    (R padding : Nat) (hchildren : children.length ≤ padding)
    (hpadding : padding < R) :
    transitionPaddingWords children R (padding + 1) =
      transitionPaddingWords children R padding ++ [0] := by
  have hchildrenR : children.length < R := hchildren.trans_lt hpadding
  have hpaddingSucc : padding + 1 ≤ R := by omega
  unfold transitionPaddingWords
  rw [Nat.min_eq_left hpaddingSucc]
  rw [Nat.min_eq_left (Nat.le_of_lt hpadding)]
  rw [Nat.min_eq_left (Nat.le_of_lt hchildrenR)]
  have hsub : padding + 1 - children.length =
      (padding - children.length) + 1 := by omega
  rw [hsub, List.replicate_add]
  simp

theorem transitionPaddingCondition_value (B : Nat) (base R : Nat)
    (children prefixBefore : List Nat) (I : WordImage) (sigma : Env)
    (hInv : TransitionPaddingLoopInv B I base R children prefixBefore sigma) :
    (Cond.lt (.var "padding") (.var "R")).evalB B sigma =
      some (decide (sigma.vars "padding" < sigma.vars "R")) := by
  rcases hInv with ⟨hloaded, hbase, hR, hcapacity, hPlenB, hsame, harity,
    padding, hpadding, hchildren, hpaddingB, hwords⟩
  have hRB : R < B := by omega
  have hpaddingVarB : sigma.vars "padding" < B := by
    rw [hpadding]
    exact hpaddingB
  have hRVarB : sigma.vars "R" < B := by
    rw [hR]
    exact hRB
  simp only [Cond.evalB, Expr.evalB]
  rw [fit_self hpaddingVarB, fit_self hRVarB]
  rfl

theorem transitionPaddingCondition_defined (B : Nat) (I : WordImage)
    (base R : Nat) (children prefixBefore : List Nat) :
    ∀ sigma, TransitionPaddingLoopInv B I base R children prefixBefore sigma →
      ∃ value,
        (Cond.lt (.var "padding") (.var "R")).evalB B sigma = some value := by
  intro sigma hInv
  exact ⟨decide (sigma.vars "padding" < sigma.vars "R"),
    transitionPaddingCondition_value B base R children prefixBefore I sigma hInv⟩

theorem transitionPaddingBody_spec (B : Nat) (I : WordImage)
    (base R : Nat) (children prefixBefore : List Nat) :
    Spec B
      (fun sigma => TransitionPaddingLoopInv B I base R children prefixBefore sigma ∧
        (Cond.lt (.var "padding") (.var "R")).evalB B sigma = some true)
      transitionPaddingBody
      (fun sigma sigma' =>
        TransitionPaddingLoopInv B I base R children prefixBefore sigma' ∧
          sigma'.vars "padding" = sigma.vars "padding" + 1)
      30 := by
  intro sigma hpre
  rcases hpre.1 with ⟨hloaded, hbase, hR, hcapacity, hPlenB, hsame,
    harity, padding, hpadding, hchildren, hpaddingB, hwords⟩
  have hcondition := transitionPaddingCondition_value B base R children
    prefixBefore I sigma hpre.1
  have hpaddingR : padding < R := by
    have htrue := hpre.2
    rw [hcondition] at htrue
    simpa [hpadding, hR] using htrue
  have hprefixLength := transitionPaddingWords_length_of_lt children R padding
    hchildren hpaddingR
  have hslot : base + 3 + (transitionPaddingWords children R padding).length <
      (sigma.arrs "P").length := by
    rw [hprefixLength]
    omega
  have hwords' := wordsAt_set_append (value := 0) hwords hslot
  have hstep := transitionPaddingWords_succ children R padding hchildren hpaddingR
  have hsame' := sameBefore_set_after
    (index := base + 3 + padding) (value := 0) hsame (by omega) (by omega)
  have hpaddingSuccB : padding + 1 < B := by omega
  unfold transitionPaddingBody AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [TransitionPaddingLoopInv, ArenaLoaded]
  all_goals (try omega)

/-- Conservative instruction budget for writing all missing fixed-width child
slots of one transition. -/
def transitionPaddingLoopCost (R : Nat) : Nat :=
  (1 + (Cond.lt (.var "padding") (.var "R")).size + 30) * R +
    1 + (Cond.lt (.var "padding") (.var "R")).size

private theorem transitionPaddingBody_decreases (B : Nat) (I : WordImage)
    (base R : Nat) (children prefixBefore : List Nat) :
    Spec B
      (fun sigma => TransitionPaddingLoopInv B I base R children prefixBefore sigma ∧
        (Cond.lt (.var "padding") (.var "R")).evalB B sigma = some true)
      transitionPaddingBody
      (fun sigma sigma' =>
        TransitionPaddingLoopInv B I base R children prefixBefore sigma' ∧
          R - sigma'.vars "padding" < R - sigma.vars "padding")
      30 := by
  refine (transitionPaddingBody_spec B I base R children prefixBefore).post ?_
  intro sigma sigma' hpre hpost
  refine ⟨hpost.1, ?_⟩
  have hcondition := transitionPaddingCondition_value B base R children
    prefixBefore I sigma hpre.1
  have hlt : sigma.vars "padding" < sigma.vars "R" := by
    have htrue := hpre.2
    rw [hcondition] at htrue
    simpa using htrue
  rw [hpost.2]
  rcases hpre.1 with ⟨hloaded, hbase, hR, hcapacity, hPlenB, hsame,
    harity, padding, hpadding, hchildren, hpaddingB, hwords⟩
  rw [hR] at hlt
  omega

theorem transitionPaddingLoop_spec (B : Nat) (I : WordImage)
    (base R : Nat) (children prefixBefore : List Nat) :
    Spec B (TransitionPaddingLoopInv B I base R children prefixBefore)
      transitionPaddingLoop
      (fun _ sigma' =>
        TransitionPaddingLoopInv B I base R children prefixBefore sigma' ∧
          (Cond.lt (.var "padding") (.var "R")).evalB B sigma' = some false)
      (transitionPaddingLoopCost R) := by
  unfold transitionPaddingLoop transitionPaddingLoopCost
  refine Spec.while_count
    (TransitionPaddingLoopInv B I base R children prefixBefore)
    (fun sigma => R - sigma.vars "padding")
    30
    (transitionPaddingCondition_defined B I base R children prefixBefore)
    (transitionPaddingBody_decreases B I base R children prefixBefore)
    (fun _ hInv => hInv) ?_
  intro sigma hInv
  have hsub : R - sigma.vars "padding" ≤ R := Nat.sub_le _ _
  have hmul := Nat.mul_le_mul_left
    (1 + (Cond.lt (.var "padding") (.var "R")).size + 30) hsub
  simpa [Nat.add_assoc] using Nat.add_le_add_right hmul
    (1 + (Cond.lt (.var "padding") (.var "R")).size)

/-- At loop exit every one of the `R` child slots has its canonical `getD`
value: a represented child state where present, and zero otherwise. -/
theorem transitionPaddingLoop_completed_spec (B : Nat) (I : WordImage)
    (base R : Nat) (children prefixBefore : List Nat) :
    Spec B (TransitionPaddingLoopInv B I base R children prefixBefore)
      transitionPaddingLoop
      (fun _ sigma' =>
        ArenaLoaded I sigma' ∧
          sigma'.vars "transitionBase" = base ∧
          sigma'.vars "R" = R ∧
          base + 3 + R ≤ (sigma'.arrs "P").length ∧
          (sigma'.arrs "P").length < B ∧
          SameBefore (sigma'.arrs "P") prefixBefore (base + 3) ∧
          sigma'.vars "arity" = children.length ∧
          WordsAt (sigma'.arrs "P") (base + 3)
            (transitionPaddingWords children R R))
      (transitionPaddingLoopCost R) := by
  refine (transitionPaddingLoop_spec B I base R children prefixBefore).post ?_
  intro sigma sigma' hpre hpost
  rcases hpost.1 with ⟨hloaded, hbase, hR, hcapacity, hPlenB, hsame,
    harity, padding, hpadding, hchildren, hpaddingB, hwords⟩
  have hcondition := transitionPaddingCondition_value B base R children
    prefixBefore I sigma' hpost.1
  have hRpadding : R ≤ padding := by
    by_contra hnot
    have hlt : padding < R := Nat.lt_of_not_ge hnot
    have htrue :
        (Cond.lt (.var "padding") (.var "R")).evalB B sigma' = some true := by
      rw [hcondition]
      simp [hpadding, hR, hlt]
    rw [hpost.2] at htrue
    contradiction
  have hmin : min padding R = R := Nat.min_eq_right hRpadding
  refine ⟨hloaded, hbase, hR, hcapacity, hPlenB, hsame, harity, ?_⟩
  simpa [transitionPaddingWords, hmin] using hwords

end Lax53Proofs.AutomatonRamArenaCorrectness
