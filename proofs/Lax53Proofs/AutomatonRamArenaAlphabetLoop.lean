import Lax53Proofs.AutomatonRamArenaAlphabet

/-!
Counted-loop verification for the alphabet phase of the charged structural
front end.
-/

namespace Lax53Proofs.AutomatonRamArenaCorrectness

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53.ValueTranslations
open Lax53Proofs.ArenaSemantics
open Lax53Proofs.AutomatonRamArenaProgram
open Lax53Proofs.AutomatonRamCorrectness
open Lax58.StructuralPresentation
open Lax58.StructuralCombinators
open Lax58.WordArena

/-- Exact conservative budget used for the counted alphabet scan. -/
def alphabetLoopCost (alphabet : RankedAlphabetCode) : Nat :=
  (1 + alphabetCondition.size + 100) * alphabet.length +
    1 + alphabetCondition.size

private theorem alphabetBody_decreases (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords I, v < B) :
    Spec B
      (fun sigma => AlphabetLoopInv B I alphabet sigma ∧
        alphabetCondition.evalB B sigma = some true)
      alphabetBody
      (fun sigma sigma' => AlphabetLoopInv B I alphabet sigma' ∧
        alphabet.length - sigma'.vars "A" <
          alphabet.length - sigma.vars "A")
      100 := by
  refine (alphabetBody_spec B I alphabet h1 hmemB hvaluesB).post ?_
  intro sigma sigma' hpre hpost
  refine ⟨hpost.1, ?_⟩
  rcases hpre.1.2.2.2 with ⟨done, rest, cursor, halphabet, hcursor,
    hrep, hA, hR, hmaximumB, hprefix⟩
  have hcondition := alphabetCondition_value B I rest cursor sigma h1 hmemB
    hpre.1.1 hcursor hrep
  cases rest with
  | nil =>
      simp at hcondition
      rw [hcondition] at hpre
      simp at hpre
  | cons rank rest =>
      have hlength := congrArg List.length halphabet
      simp only [List.length_append, List.length_cons] at hlength
      rw [hpost.2, hA]
      omega

theorem alphabetLoop_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords I, v < B) :
    Spec B (AlphabetLoopInv B I alphabet) alphabetLoop
      (fun _ sigma' => AlphabetLoopInv B I alphabet sigma' ∧
        alphabetCondition.evalB B sigma' = some false)
      (alphabetLoopCost alphabet) := by
  unfold alphabetLoop alphabetLoopCost
  refine Spec.while_count
    (AlphabetLoopInv B I alphabet)
    (fun sigma => alphabet.length - sigma.vars "A")
    100
    (alphabetCondition_defined B I alphabet h1 hmemB)
    (alphabetBody_decreases B I alphabet h1 hmemB hvaluesB)
    (fun _ hInv => hInv) ?_
  intro sigma hInv
  have hsub : alphabet.length - sigma.vars "A" ≤ alphabet.length :=
    Nat.sub_le _ _
  have hmul := Nat.mul_le_mul_left
    (1 + alphabetCondition.size + 100) hsub
  simpa [Nat.add_assoc] using
    Nat.add_le_add_right hmul (1 + alphabetCondition.size)

/-- On loop exit the entire alphabet has been materialized. -/
theorem alphabetLoop_completed_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords I, v < B) :
    Spec B (AlphabetLoopInv B I alphabet) alphabetLoop
      (fun _ sigma' => AlphabetLoopInv B I alphabet sigma' ∧
        sigma'.vars "A" = alphabet.length)
      (alphabetLoopCost alphabet) := by
  refine (alphabetLoop_spec B I alphabet h1 hmemB hvaluesB).post ?_
  intro sigma sigma' hpre hpost
  refine ⟨hpost.1, ?_⟩
  rcases hpost.1.2.2.2 with ⟨done, rest, cursor, halphabet, hcursor,
    hrep, hA, hR, hmaximumB, hprefix⟩
  have hcondition := alphabetCondition_value B I rest cursor sigma' h1 hmemB
    hpost.1.1 hcursor hrep
  have hempty : rest = [] := by
    cases rest with
    | nil => rfl
    | cons rank rest =>
        simp at hcondition
        rw [hpost.2] at hcondition
        contradiction
  subst rest
  have hlength := congrArg List.length halphabet
  simp only [List.append_nil] at halphabet
  simpa [halphabet] using hA

end Lax53Proofs.AutomatonRamArenaCorrectness
