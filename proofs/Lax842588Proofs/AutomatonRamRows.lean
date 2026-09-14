import Lax842588Proofs.AutomatonRamInstallCopy

namespace Lax842588Proofs.AutomatonRamCorrectness

open Classical

theorem writePrefix_getD_inside (array values : List Nat) (base upto i : Nat)
    (hi : i < upto) (hspan : base + upto ≤ array.length) :
    (writePrefix array base values upto).getD (base + i) 0 = values.getD i 0 := by
  induction upto with
  | zero => omega
  | succ upto ih =>
      rw [writePrefix_succ]
      by_cases hii : i = upto
      · subst i
        rw [List.getD_eq_getElem]
        · rw [List.getElem_set_self]
        · simp only [List.length_set]
          rw [writePrefix_length]
          omega
      · have hi' : i < upto := by omega
        have hlen :
            (writePrefix array base values upto).length = array.length :=
          writePrefix_length array base values upto
        rw [List.getD_eq_getElem]
        · rw [List.getElem_set_ne (by omega)]
          rw [← List.getD_eq_getElem
            (writePrefix array base values upto) 0 (by rw [hlen]; omega)]
          exact ih hi' (by omega)
        · simp only [List.length_set]
          rw [hlen]
          omega

theorem writePrefix_getD_before (array values : List Nat) (base upto i : Nat)
    (hi : i < base) (hspan : base + upto ≤ array.length) :
    (writePrefix array base values upto).getD i 0 = array.getD i 0 := by
  induction upto with
  | zero => rfl
  | succ upto ih =>
      rw [writePrefix_succ]
      have hlen :
          (writePrefix array base values upto).length = array.length :=
        writePrefix_length array base values upto
      rw [List.getD_eq_getElem]
      · rw [List.getElem_set_ne (by omega)]
        rw [← List.getD_eq_getElem
          (writePrefix array base values upto) 0 (by rw [hlen]; omega)]
        exact (ih (by omega)).trans rfl
      · simp [hlen]
        omega

theorem rowsRep_seenState_iff {states lengths : List Nat} {width : Nat}
    {rows : List (List Nat)} (hrep : RowsRep states lengths width rows)
    {row q : Nat} (hrow : row < rows.length) :
    SeenState states row width q (lengths.getD row 0) ↔
      q ∈ rows.getD row [] := by
  have hinfo := hrep.2 row hrow
  constructor
  · rintro ⟨i, hi, hq⟩
    have hi' : i < (rows.getD row []).length := by rw [← hinfo.1]; exact hi
    have hvalue := hinfo.2.2 i hi'
    rw [hvalue] at hq
    have hmem : (rows.getD row []).getD i 0 ∈ rows.getD row [] := by
      rw [List.getD_eq_getElem _ _ hi']
      exact List.getElem_mem hi'
    exact hq ▸ hmem
  · intro hq
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hq
    refine ⟨i, ?_, ?_⟩
    · rw [hinfo.1]
      exact hi
    · rw [hinfo.2.2 i hi]
      rw [List.getD_eq_getElem]
      exact heq

def collapseRows (rows : List (List Nat)) (k : Nat) (output : List Nat) :
    List (List Nat) :=
  rows.take (rows.length - k) ++ [output]

theorem rowsRep_after_install {states lengths : List Nat} {width k : Nat}
    {rows : List (List Nat)} {output : List Nat}
    (hrep : RowsRep states lengths width rows)
    (hk : k ≤ rows.length)
    (hroom : rows.length - k < lengths.length)
    (houtput : output.length ≤ width)
    (hspan : (rows.length - k) * width + output.length ≤ states.length) :
    RowsRep
      (writePrefix states ((rows.length - k) * width) output output.length)
      (lengths.set (rows.length - k) output.length) width
      (collapseRows rows k output) := by
  let target := rows.length - k
  have htargetRows : target ≤ rows.length := by dsimp [target]; omega
  have hcollapseLen : (collapseRows rows k output).length = target + 1 := by
    simp [collapseRows, target, List.length_take_of_le htargetRows]
  constructor
  · rw [hcollapseLen]
    simp only [List.length_set]
    omega
  · intro row hrow
    have hrowLe : row ≤ target := by rw [hcollapseLen] at hrow; omega
    by_cases hrt : row = target
    · subst row
      have htargetList :
          (collapseRows rows k output).getD target [] = output := by
        change (rows.take target ++ [output]).getD target [] = output
        rw [List.getD_append_right]
        · simp [List.length_take_of_le htargetRows]
        · simp [List.length_take_of_le htargetRows]
      constructor
      · rw [List.getD_eq_getElem]
        · rw [List.getElem_set_self]
          exact congrArg List.length htargetList.symm
        · simpa using hroom
      · rw [htargetList]
        refine ⟨houtput, ?_⟩
        intro i hi
        exact writePrefix_getD_inside states output (target * width)
          output.length i hi hspan
    · have hrlt : row < target := by omega
      have hrRows : row < rows.length := lt_of_lt_of_le hrlt htargetRows
      have hold := hrep.2 row hrRows
      have hrowList :
          (collapseRows rows k output).getD row [] = rows.getD row [] := by
        change (rows.take target ++ [output]).getD row [] = rows.getD row []
        rw [List.getD_append]
        · rw [List.getD_eq_getElem]
          · rw [List.getElem_take]
            rw [← List.getD_eq_getElem rows [] hrRows]
          · simp [List.length_take_of_le htargetRows]
            exact hrlt
        · simp [collapseRows, List.length_take_of_le htargetRows]
          exact hrlt
      constructor
      · rw [List.getD_eq_getElem]
        · rw [List.getElem_set_ne (by omega)]
          rw [← List.getD_eq_getElem lengths 0 (lt_of_lt_of_le hrRows hrep.1)]
          rw [hold.1, hrowList]
        · simpa only [List.length_set] using lt_of_lt_of_le hrRows hrep.1
      · rw [hrowList]
        refine ⟨hold.2.1, ?_⟩
        intro i hi
        rw [writePrefix_getD_before states output (target * width)
          output.length (row * width + i) ?_ hspan]
        exact hold.2.2 i hi
        have hiwidth := lt_of_lt_of_le hi hold.2.1
        nlinarith

end Lax842588Proofs.AutomatonRamCorrectness
