import Lax53Proofs.AutomatonRamScan

namespace Lax53Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax13Proofs.Codegen
open Lax53.EffectiveTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.AutomatonRamProgram

theorem scanTransitions_spec (B : Nat) (M : EncodedAutomaton)
    (states lengths : List Nat) (depth k symbol : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hlengthsB : ∀ v ∈ lengths, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hstatesLenB : states.length < B) (hlengthsLenB : lengths.length < B)
    (hkR : k ≤ maximumRank M.1) (hkdepth : k ≤ depth)
    (hdepthRows : depth ≤ lengths.length)
    (hwidthB : maximumRank M.1 + 3 < B) (hdepthB : depth < B)
    (hkB : k < B) (hsymbolB : symbol < B)
    (hQB : M.2.1 < B) (hTB : M.2.2.1.length < B)
    (hlenLe : ∀ row < depth, lengths.getD row 0 ≤ M.2.2.1.length)
    (hspan : ∀ j < k, (depth - k + j) * M.2.2.1.length +
      lengths.getD (depth - k + j) 0 ≤ states.length)
    (haddrB : ∀ j < k, (depth - k + j) * M.2.2.1.length +
      lengths.getD (depth - k + j) 0 < B)
    (hworkB : M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) +
      (maximumRank M.1 + 3) < B) :
    Spec B
      (ScanStaticContext M states lengths depth k symbol)
      scanTransitions
      (fun _ σ' => ScanInv M states lengths depth k symbol σ' ∧
        σ'.vars "tr" = M.2.2.1.length)
      (((((70 * (M.2.2.1.length + 1) + 4) * k + 160) + 4) *
        M.2.2.1.length + 4) + 10) := by
  have hbody := scanTransitionsBody_spec B M states lengths depth k symbol h0 h1
    hparameterB hstatesB hlengthsB hparameterLenB hstatesLenB hlengthsLenB
    hkR hkdepth hdepthRows hwidthB hdepthB hkB hsymbolB hQB hTB hlenLe hspan
    haddrB hworkB
  have hloop := scanTransitionsLoop_spec B M states lengths depth k symbol hbody hTB
  have hloop' : Spec B (ScanInv M states lengths depth k symbol)
      scanTransitionsLoop
      (fun _ σ' => ScanStaticContext M states lengths depth k symbol σ' ∧
        σ'.vars "scratchLen" =
          (transitionOutputs M states lengths depth k symbol M.2.2.1.length).length ∧
        PrefixEq (σ'.arrs "O")
          (transitionOutputs M states lengths depth k symbol M.2.2.1.length) ∧
        σ'.vars "tr" = M.2.2.1.length)
      (((70 * (M.2.2.1.length + 1) + 4) * k + 160 + 4) *
        M.2.2.1.length + 4) := hloop.post (by
    rintro τ τ' _ ⟨⟨hstatic, _, hscratch, hprefix⟩, htr⟩
    rw [htr] at hscratch hprefix
    exact ⟨hstatic, hscratch, hprefix, htr⟩)
  have hzero : transitionOutputs M states lengths depth k symbol 0 = [] := by
    simp [transitionOutputs]
  intro σ hσ
  unfold scanTransitions seqs
  run_vcg [hloop']
  all_goals simp_all [ScanInv, ScanStaticContext, prefixEq_nil, hzero]
  all_goals omega

/-- The prefix of a fixed-width state row contains exactly `values`. -/
def RowEq (states : List Nat) (width row : Nat) (values : List Nat) : Prop :=
  values.length ≤ width ∧
    ∀ i < values.length,
      states.getD (row * width + i) 0 = values.getD i 0

/-- A list of rows in bottom-to-top order is represented by the flat state
array and the parallel row-length array. -/
def RowsRep (states lengths : List Nat) (width : Nat)
    (rows : List (List Nat)) : Prop :=
  rows.length ≤ lengths.length ∧
    ∀ row < rows.length,
      lengths.getD row 0 = (rows.getD row []).length ∧
        RowEq states width row (rows.getD row [])

theorem rowsRep_length_le {states lengths : List Nat} {width : Nat}
    {rows : List (List Nat)} (h : RowsRep states lengths width rows) :
    rows.length ≤ lengths.length := h.1

theorem rowsRep_row_length_le {states lengths : List Nat} {width row : Nat}
    {rows : List (List Nat)} (h : RowsRep states lengths width rows)
    (hrow : row < rows.length) :
    lengths.getD row 0 ≤ width := by
  rw [(h.2 row hrow).1]
  exact (h.2 row hrow).2.1

theorem rowsRep_state_at {states lengths : List Nat} {width row i : Nat}
    {rows : List (List Nat)} (h : RowsRep states lengths width rows)
    (hrow : row < rows.length) (hi : i < (rows.getD row []).length) :
    states.getD (row * width + i) 0 = (rows.getD row []).getD i 0 :=
  (h.2 row hrow).2.2 i hi

end Lax53Proofs.AutomatonRamCorrectness
