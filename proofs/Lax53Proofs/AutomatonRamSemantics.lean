import Lax53Proofs.AutomatonRamRows

namespace Lax53Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1000000
open Classical

open Lax53.EffectiveTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.AutomatonTableEncoding
open Lax53Proofs.EncodedAutomatonEvaluation
open Lax53Proofs.EncodedAutomatonWordEvaluation

/-- The ordered child rows consumed at a node, read from a bottom-to-top row
stack. -/
def childRows (rows : List (List Nat)) (depth k : Nat) : List (List Nat) :=
  List.ofFn fun i : Fin k => rows.getD (depth - k + i.val) []

theorem encodeAutomaton_childField (M : EncodedAutomaton) (tr j : Nat)
    (htr : tr < M.2.2.1.length) (hj : j < maximumRank M.1) :
    (encodeAutomaton M).getD
        (M.1.length + 4 + tr * (maximumRank M.1 + 3) + 3 + j) 0 =
      (M.2.2.1.getD tr (0, 0, [])).2.2.getD j 0 := by
  rw [show M.1.length + 4 + tr * (maximumRank M.1 + 3) + 3 + j =
    M.1.length + 4 + tr * (maximumRank M.1 + 3) + (3 + j) by omega]
  rw [encodeAutomaton_record M tr (3 + j) htr (by omega)]
  rw [fixedRecord_child _ _ _ hj]
  rw [List.getD_eq_getElem M.2.2.1 (0, 0, []) htr]

theorem childPresent_iff_row_mem {states lengths : List Nat} {width : Nat}
    {rows : List (List Nat)} (hrep : RowsRep states lengths width rows)
    {depth k j q : Nat} (hdepth : depth = rows.length)
    (hk : k ≤ depth) (hj : j < k) :
    ChildPresent states lengths depth k width j q ↔
      q ∈ rows.getD (depth - k + j) [] := by
  unfold ChildPresent
  apply rowsRep_seenState_iff hrep
  omega

theorem childrenPrefix_iff_childrenAgree (M : EncodedAutomaton)
    {states lengths : List Nat} {rows : List (List Nat)}
    {depth k tr : Nat}
    (hrep : RowsRep states lengths M.2.2.1.length rows)
    (hdepth : depth = rows.length) (hk : k ≤ depth)
    (hkR : k ≤ maximumRank M.1) (htr : tr < M.2.2.1.length)
    (harity : (M.2.2.1.getD tr (0, 0, [])).2.2.length = k) :
    ChildrenPrefix (encodeAutomaton M) states lengths
        (M.1.length + 4 + tr * (maximumRank M.1 + 3)) depth k
        M.2.2.1.length k ↔
      ChildrenAgree (M.2.2.1.getD tr (0, 0, [])).2.2
        (childRows rows depth k) = true := by
  let transition := M.2.2.1.getD tr (0, 0, [])
  have hagree := childrenAgree_iff transition.2.2
    (fun i : Fin k => rows.getD (depth - k + i.val) []) harity
  change ChildrenPrefix (encodeAutomaton M) states lengths
      (M.1.length + 4 + tr * (maximumRank M.1 + 3)) depth k
      M.2.2.1.length k ↔
    ChildrenAgree transition.2.2
      (List.ofFn fun i : Fin k => rows.getD (depth - k + i.val) []) = true
  rw [hagree]
  constructor
  · intro hp i
    have hj := i.isLt
    have hpj := hp i.val hj
    rw [childPresent_iff_row_mem hrep hdepth hk hj] at hpj
    have hfield := encodeAutomaton_childField M tr i.val htr
      (lt_of_lt_of_le hj hkR)
    rw [hfield] at hpj
    have hiChild : i.val < transition.2.2.length := by
      rw [harity]
      exact hj
    rw [List.getD_eq_getElem _ _ hiChild] at hpj
    exact hpj
  · intro ha j hj
    rw [childPresent_iff_row_mem hrep hdepth hk hj]
    have hm := ha ⟨j, hj⟩
    have hfield := encodeAutomaton_childField M tr j htr
      (lt_of_lt_of_le hj hkR)
    rw [hfield]
    have hjChild : j < transition.2.2.length := by
      rw [harity]
      exact hj
    rw [List.getD_eq_getElem _ _ hjChild]
    exact hm

theorem transitionMatchesAt_iff (M : EncodedAutomaton)
    {states lengths : List Nat} {rows : List (List Nat)}
    {depth k symbol tr : Nat}
    (hrep : RowsRep states lengths M.2.2.1.length rows)
    (hdepth : depth = rows.length) (hk : k ≤ depth)
    (hkR : k ≤ maximumRank M.1) (htr : tr < M.2.2.1.length) :
    TransitionMatchesAt M states lengths depth k symbol tr ↔
      let transition := M.2.2.1.getD tr (0, 0, [])
      transition.1 = symbol ∧ transition.2.1 < M.2.1 ∧
        transition.2.2.length = k ∧
        ChildrenAgree transition.2.2 (childRows rows depth k) = true := by
  let transition := M.2.2.1.getD tr (0, 0, [])
  unfold TransitionMatchesAt
  dsimp only
  constructor
  · rintro ⟨hs, hq, harity, hc⟩
    exact ⟨hs, hq, harity,
      (childrenPrefix_iff_childrenAgree M hrep hdepth hk hkR htr harity).mp hc⟩
  · rintro ⟨hs, hq, harity, hc⟩
    exact ⟨hs, hq, harity,
      (childrenPrefix_iff_childrenAgree M hrep hdepth hk hkR htr harity).mpr hc⟩

theorem transitionOutputAt_eq_option (M : EncodedAutomaton)
    {states lengths : List Nat} {rows : List (List Nat)}
    {depth k symbol tr : Nat}
    (hrep : RowsRep states lengths M.2.2.1.length rows)
    (hdepth : depth = rows.length) (hk : k ≤ depth)
    (hkR : k ≤ maximumRank M.1) (htr : tr < M.2.2.1.length) :
    transitionOutputAt M states lengths depth k symbol tr =
      (if (M.2.2.1[tr].1 = symbol) && (M.2.2.1[tr].2.1 < M.2.1) &&
          ChildrenAgree M.2.2.1[tr].2.2 (childRows rows depth k) then
        some M.2.2.1[tr].2.1 else none).toList := by
  rw [transitionOutputAt]
  rw [transitionMatchesAt_iff M hrep hdepth hk hkR htr]
  rw [List.getD_eq_getElem M.2.2.1 (0, 0, []) htr]
  dsimp only
  let matchProp := M.2.2.1[tr].1 = symbol ∧
      M.2.2.1[tr].2.1 < M.2.1 ∧
      M.2.2.1[tr].2.2.length = k ∧
      ChildrenAgree M.2.2.1[tr].2.2 (childRows rows depth k) = true
  let matchBool := (M.2.2.1[tr].1 = symbol) &&
      (M.2.2.1[tr].2.1 < M.2.1) &&
      ChildrenAgree M.2.2.1[tr].2.2 (childRows rows depth k)
  have hequiv : matchProp ↔ matchBool = true := by
    dsimp [matchProp, matchBool]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hs, hq, _, ha⟩
      exact ⟨⟨hs, hq⟩, ha⟩
    · rintro ⟨⟨hs, hq⟩, ha⟩
      have hlen : M.2.2.1[tr].2.2.length = k := by
        have := (Bool.and_eq_true_iff.mp ha).1
        simpa [childRows] using beq_iff_eq.mp this
      exact ⟨hs, hq, hlen, ha⟩
  dsimp [matchProp, matchBool] at hequiv
  by_cases hp : M.2.2.1[tr].1 = symbol ∧
      M.2.2.1[tr].2.1 < M.2.1 ∧
      M.2.2.1[tr].2.2.length = k ∧
      ChildrenAgree M.2.2.1[tr].2.2 (childRows rows depth k) = true
  · have hb := hequiv.mp hp
    rw [if_pos hp, if_pos hb]
    rfl
  · have hb : ((M.2.2.1[tr].1 = symbol) &&
        (M.2.2.1[tr].2.1 < M.2.1) &&
        ChildrenAgree M.2.2.1[tr].2.2 (childRows rows depth k)) ≠ true :=
      fun h => hp (hequiv.mpr h)
    rw [if_neg hp, if_neg hb]
    rfl

theorem transitionOutputs_eq_parentStates (M : EncodedAutomaton)
    {states lengths : List Nat} {rows : List (List Nat)}
    {depth k symbol : Nat}
    (hrep : RowsRep states lengths M.2.2.1.length rows)
    (hdepth : depth = rows.length) (hk : k ≤ depth)
    (hkR : k ≤ maximumRank M.1) :
    transitionOutputs M states lengths depth k symbol M.2.2.1.length =
      parentStates M.2 symbol (childRows rows depth k) := by
  have hpref : ∀ upto ≤ M.2.2.1.length,
      transitionOutputs M states lengths depth k symbol upto =
        (M.2.2.1.take upto).filterMap fun transition =>
          if transition.1 = symbol && transition.2.1 < M.2.1 &&
              ChildrenAgree transition.2.2 (childRows rows depth k) then
            some transition.2.1 else none := by
    intro upto hupto
    induction upto with
    | zero => simp [transitionOutputs]
    | succ upto ih =>
        have htr : upto < M.2.2.1.length := by omega
        rw [transitionOutputs_succ, List.take_succ_eq_append_getElem htr]
        simp only [List.filterMap_append]
        rw [ih (by omega)]
        rw [transitionOutputAt_eq_option M hrep hdepth hk hkR htr]
        by_cases hmatch :
            (M.2.2.1[upto].1 = symbol ∧ M.2.2.1[upto].2.1 < M.2.1) ∧
              ChildrenAgree M.2.2.1[upto].2.2 (childRows rows depth k) = true
        · simp [hmatch]
        · simp [hmatch]
  rw [hpref M.2.2.1.length le_rfl, List.take_length]
  rfl

end Lax53Proofs.AutomatonRamCorrectness
