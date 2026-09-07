import Mathlib.Data.List.GetD
import Lax53Proofs.RuntimeLayout

namespace Lax53Proofs.AutomatonTableEncoding

open Lax53.ValueTranslations
open Lax53.TreeModelCheckingEncoding

theorem encodeTransitionFixed_length (R : Nat) (tr : TransitionCode) :
    (encodeTransitionFixed R tr).length = R + 3 := by
  simp [encodeTransitionFixed]

theorem getD_flatMap_fixed {α β : Type} (xs : List α) (f : α → List β)
    (width : Nat) (fallback : β)
    (hlen : ∀ x ∈ xs, (f x).length = width)
    (i j : Nat) (hi : i < xs.length) (hj : j < width) :
    (xs.flatMap f).getD (i * width + j) fallback =
      (f xs[i]).getD j fallback := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          rw [List.flatMap_cons]
          rw [List.getD_append]
          · simp
          · simpa [hlen x (by simp)] using hj
      | succ i =>
          rw [Nat.succ_mul]
          rw [List.flatMap_cons]
          rw [List.getD_append_right]
          · rw [hlen x (by simp)]
            rw [show i * width + width + j - width = i * width + j by omega]
            rw [ih (fun y hy => hlen y (by simp [hy])) i (by simpa using hi)]
            simp
          · rw [hlen x (by simp)]
            omega

theorem fixedRecord_symbol (R : Nat) (tr : TransitionCode) :
    (encodeTransitionFixed R tr).getD 0 0 = tr.1 := by
  rfl

theorem fixedRecord_parent (R : Nat) (tr : TransitionCode) :
    (encodeTransitionFixed R tr).getD 1 0 = tr.2.1 := by
  rfl

theorem fixedRecord_arity (R : Nat) (tr : TransitionCode) :
    (encodeTransitionFixed R tr).getD 2 0 = tr.2.2.length := by
  rfl

theorem fixedRecord_child (R : Nat) (tr : TransitionCode) (j : Nat)
    (hj : j < R) :
    (encodeTransitionFixed R tr).getD (3 + j) 0 = tr.2.2.getD j 0 := by
  have hindex : 3 + j = ((j + 1) + 1) + 1 := by omega
  rw [hindex]
  simp only [encodeTransitionFixed, List.getD_cons_succ]
  rw [List.getD_eq_getElem]
  · simp
  · simpa using hj

theorem maximumRank_ge (alphabet : RankedAlphabetCode) (i : Nat)
    (hi : i < alphabet.length) : alphabet.getD i 0 ≤ maximumRank alphabet := by
  rw [List.getD_eq_getElem alphabet 0 hi]
  simp only [maximumRank]
  rw [List.foldl_max]
  have hne : alphabet ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hi)
  rw [List.max?_eq_some_max hne]
  simp only [Option.getD_some]
  exact (List.le_max_of_mem (List.getElem_mem hi)).trans (Nat.le_max_right _ _)

theorem encodeAutomaton_length (M : EncodedAutomaton) :
    (encodeAutomaton M).length =
      M.1.length + M.2.2.1.length * (maximumRank M.1 + 3) +
        M.2.2.2.length + 5 := by
  simp [encodeAutomaton, block, encodeTransitionFixed_length,
    List.length_flatMap]
  omega

theorem encodeAutomaton_eq (M : EncodedAutomaton) :
    encodeAutomaton M =
      [M.1.length] ++ M.1 ++ [M.2.1, M.2.2.1.length, maximumRank M.1] ++
        M.2.2.1.flatMap (encodeTransitionFixed (maximumRank M.1)) ++
          [M.2.2.2.length] ++ M.2.2.2 := by
  simp [encodeAutomaton, block]

theorem getD_append_length {α : Type} (pref suffix : List α)
    (i : Nat) (fallback : α) :
    (pref ++ suffix).getD (pref.length + i) fallback =
      suffix.getD i fallback := by
  rw [List.getD_append_right]
  · simp
  · omega

theorem fixedRecords_length (M : EncodedAutomaton) :
    (M.2.2.1.flatMap (encodeTransitionFixed (maximumRank M.1))).length =
      M.2.2.1.length * (maximumRank M.1 + 3) := by
  simp [List.length_flatMap, encodeTransitionFixed_length]

theorem encodeAutomaton_A (M : EncodedAutomaton) :
    (encodeAutomaton M).getD 0 0 = M.1.length := by
  rw [encodeAutomaton_eq]
  simp only [List.append_assoc]
  rfl

theorem encodeAutomaton_rank (M : EncodedAutomaton) (i : Nat)
    (hi : i < M.1.length) :
    (encodeAutomaton M).getD (i + 1) 0 = M.1.getD i 0 := by
  rw [encodeAutomaton_eq]
  simp only [List.append_assoc]
  rw [show i + 1 = [M.1.length].length + i by simp [Nat.add_comm]]
  rw [getD_append_length]
  rw [List.getD_append]
  exact hi

theorem encodeAutomaton_Q (M : EncodedAutomaton) :
    (encodeAutomaton M).getD (M.1.length + 1) 0 = M.2.1 := by
  rw [encodeAutomaton_eq]
  simp only [List.append_assoc]
  rw [show M.1.length + 1 = [M.1.length].length + M.1.length by simp [Nat.add_comm]]
  rw [getD_append_length]
  rw [show M.1.length = M.1.length + 0 by simp]
  rw [getD_append_length]
  rfl

theorem encodeAutomaton_T (M : EncodedAutomaton) :
    (encodeAutomaton M).getD (M.1.length + 2) 0 = M.2.2.1.length := by
  rw [encodeAutomaton_eq]
  simp only [List.append_assoc]
  rw [show M.1.length + 2 = [M.1.length].length + (M.1.length + 1) by simp; omega]
  rw [getD_append_length]
  rw [show M.1.length + 1 = M.1.length + 1 by rfl]
  rw [getD_append_length]
  rfl

theorem encodeAutomaton_R (M : EncodedAutomaton) :
    (encodeAutomaton M).getD (M.1.length + 3) 0 = maximumRank M.1 := by
  rw [encodeAutomaton_eq]
  simp only [List.append_assoc]
  rw [show M.1.length + 3 = [M.1.length].length + (M.1.length + 2) by simp; omega]
  rw [getD_append_length]
  rw [show M.1.length + 2 = M.1.length + 2 by rfl]
  rw [getD_append_length]
  rfl

theorem encodeAutomaton_record (M : EncodedAutomaton) (i field : Nat)
    (hi : i < M.2.2.1.length) (hfield : field < maximumRank M.1 + 3) :
    (encodeAutomaton M).getD
        (M.1.length + 4 + i * (maximumRank M.1 + 3) + field) 0 =
      (encodeTransitionFixed (maximumRank M.1) M.2.2.1[i]).getD field 0 := by
  rw [encodeAutomaton_eq]
  simp only [List.append_assoc]
  rw [show M.1.length + 4 + i * (maximumRank M.1 + 3) + field =
    [M.1.length].length +
      (M.1.length + (3 + (i * (maximumRank M.1 + 3) + field))) by simp; omega]
  rw [getD_append_length]
  rw [getD_append_length]
  rw [show 3 + (i * (maximumRank M.1 + 3) + field) =
    [M.2.1, M.2.2.1.length, maximumRank M.1].length +
      (i * (maximumRank M.1 + 3) + field) by simp]
  rw [getD_append_length]
  rw [List.getD_append]
  · exact getD_flatMap_fixed M.2.2.1
      (encodeTransitionFixed (maximumRank M.1))
      (maximumRank M.1 + 3) 0
      (fun x _ => encodeTransitionFixed_length _ x) i field hi hfield
  · rw [fixedRecords_length]
    calc
      i * (maximumRank M.1 + 3) + field <
          i * (maximumRank M.1 + 3) + (maximumRank M.1 + 3) :=
        Nat.add_lt_add_left hfield _
      _ = (i + 1) * (maximumRank M.1 + 3) := by
        rw [Nat.add_mul]
        simp
      _ ≤ M.2.2.1.length * (maximumRank M.1 + 3) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hi)

theorem encodeAutomaton_acceptCount (M : EncodedAutomaton) :
    (encodeAutomaton M).getD
        (M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3)) 0 =
      M.2.2.2.length := by
  rw [encodeAutomaton_eq]
  simp only [List.append_assoc]
  rw [show M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) =
    [M.1.length].length + (M.1.length +
      (3 + M.2.2.1.length * (maximumRank M.1 + 3))) by simp; omega]
  rw [getD_append_length]
  rw [getD_append_length]
  rw [show 3 + M.2.2.1.length * (maximumRank M.1 + 3) =
    [M.2.1, M.2.2.1.length, maximumRank M.1].length +
      M.2.2.1.length * (maximumRank M.1 + 3) by simp]
  rw [getD_append_length]
  rw [show M.2.2.1.length * (maximumRank M.1 + 3) =
    (M.2.2.1.flatMap (encodeTransitionFixed (maximumRank M.1))).length + 0 by
      rw [fixedRecords_length]; omega]
  rw [getD_append_length]
  rfl

theorem encodeAutomaton_accept (M : EncodedAutomaton) (i : Nat) :
    (encodeAutomaton M).getD
        (M.1.length + 5 + M.2.2.1.length * (maximumRank M.1 + 3) + i) 0 =
      M.2.2.2.getD i 0 := by
  rw [encodeAutomaton_eq]
  simp only [List.append_assoc]
  rw [show M.1.length + 5 + M.2.2.1.length * (maximumRank M.1 + 3) + i =
    [M.1.length].length + (M.1.length + (3 +
      (M.2.2.1.length * (maximumRank M.1 + 3) + (1 + i)))) by simp; omega]
  rw [getD_append_length]
  rw [getD_append_length]
  rw [show 3 + (M.2.2.1.length * (maximumRank M.1 + 3) + (1 + i)) =
    [M.2.1, M.2.2.1.length, maximumRank M.1].length +
      (M.2.2.1.length * (maximumRank M.1 + 3) + (1 + i)) by simp]
  rw [getD_append_length]
  rw [show M.2.2.1.length * (maximumRank M.1 + 3) + (1 + i) =
    (M.2.2.1.flatMap (encodeTransitionFixed (maximumRank M.1))).length + (1 + i) by
      rw [fixedRecords_length]]
  rw [getD_append_length]
  rw [show 1 + i = [M.2.2.2.length].length + i by simp]
  rw [getD_append_length]

end Lax53Proofs.AutomatonTableEncoding
