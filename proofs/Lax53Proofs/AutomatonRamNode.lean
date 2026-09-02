import Lax53Proofs.AutomatonRamStack

namespace Lax53Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53.EffectiveTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.AutomatonRamProgram
open Lax53Proofs.EncodedAutomatonWordEvaluation

theorem parentStates_length_le (M : AutomatonCode) (symbol : Nat)
    (children : List CodeString) :
    (parentStates M symbol children).length ≤ M.2.1.length := by
  unfold parentStates
  exact List.length_filterMap_le _ _

theorem mem_parentStates_lt (M : AutomatonCode) (symbol q : Nat)
    (children : List CodeString) (hq : q ∈ parentStates M symbol children) :
    q < M.1 := by
  simp only [parentStates, List.mem_filterMap] at hq
  obtain ⟨transition, _, htransition⟩ := hq
  split at htransition
  · rename_i hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    have heq : transition.2.1 = q := by
      simpa only [Option.some.injEq] using htransition
    simpa [heq] using hvalid.1.2
  · simp at htransition

theorem writePrefix_values_lt {array values : List Nat} {base upto B : Nat}
    (h0 : 0 < B) (harray : ∀ v ∈ array, v < B)
    (hvalues : ∀ v ∈ values, v < B) :
    ∀ v ∈ writePrefix array base values upto, v < B := by
  induction upto with
  | zero => simpa using harray
  | succ upto ih =>
      intro v hv
      rcases List.mem_or_eq_of_mem_set hv with hv | rfl
      · exact ih v hv
      · exact getD_lt_of_mem_bound h0 hvalues

theorem set_values_lt {array : List Nat} {i value B : Nat}
    (harray : ∀ v ∈ array, v < B) (hvalue : value < B) :
    ∀ v ∈ array.set i value, v < B := by
  intro v hv
  rcases List.mem_or_eq_of_mem_set hv with hv | rfl
  · exact harray v hv
  · exact hvalue

/-- Exact cost bound already established for a complete transition scan. -/
def transitionScanCost (M : EncodedAutomaton) (k : Nat) : Nat :=
  (((70 * (M.2.2.1.length + 1) + 4) * k + 160 + 4) *
      M.2.2.1.length + 4) + 10

/-- Cost of transition scanning followed by installing the parent row. -/
def nodeCoreCost (M : EncodedAutomaton) (k : Nat) : Nat :=
  transitionScanCost M k + (34 * M.2.2.1.length + 30)

end Lax53Proofs.AutomatonRamCorrectness
