import Lax842588Proofs.AutomatonRamArenaPrepare
import Lax842588Proofs.AutomatonRamAccept

/-!
The existing verified bottom-up evaluator and accepting-state scan, factored
as the proof-private backend consumed by the structural arena frontend.
-/

namespace Lax842588Proofs.AutomatonRamBackend

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamProgram
open Lax842588Proofs.AutomatonRamCorrectness
open Lax842588Proofs.AutomatonTableEncoding
open Lax842588Proofs.EncodedAutomatonEvaluation
open Lax842588Proofs.EncodedAutomatonWordEvaluation

/-- The suffix of the combined program after structural materialization. -/
def automatonBackend : Com :=
  .seq evaluateTree (.seq scanAccepting .skip)

def automatonBackendCost (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Nat :=
  (nodeCoefficient M *
      (treeSize t + rankSum M.1 (encodeTree M.1 t)) + 20) +
    ((39 * M.2.2.2.length + 34) * M.2.2.1.length + 30) + 1

/-- The already-verified evaluator backend decides acceptance from the exact
working arrays produced by the charged frontend. -/
theorem automatonBackend_spec (B : Nat) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hwordLenB : treeSize t < B)
    (hstatesCapacityB : treeSize t * M.2.2.1.length < B)
    (hwidthB : maximumRank M.1 + 3 < B) (hQB : M.2.1 < B)
    (hTB : M.2.2.1.length < B)
    (hworkB : M.1.length + 4 +
      M.2.2.1.length * (maximumRank M.1 + 3) +
        (maximumRank M.1 + 3) < B) :
    Spec B (EvaluateTreeContext B M (encodeTree M.1 t)) automatonBackend
      (fun sigma sigma' => sigma'.out = sigma.out ++
        [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0])
      (automatonBackendCost M t) := by
  let word := encodeTree M.1 t
  have hwordLenB' : word.length < B := by
    simpa [word, encodeTree_length] using hwordLenB
  have hstatesCapacityB' : word.length * M.2.2.1.length < B := by
    simpa [word, encodeTree_length] using hstatesCapacityB
  have heval := (evaluateTree_spec B M word h0 h1 hparameterB
    hparameterLenB hwordLenB' hstatesCapacityB'
    (encodeTree_symbols_lt M.1 t) hwidthB hQB hTB hworkB
    (safeEval_encodeTree M.1 M.2 t [])).frame
  intro sigma hcontext
  obtain ⟨sigma3, hrun3,
      ⟨⟨hinv, hnodeDone⟩, hevalVars, hevalArrs, hevalInp,
        hevalOut⟩⟩ := heval.run (by simpa [word] using hcontext)
  rcases hinv with ⟨processed, remaining, stack, states, lengths,
    hword, hnode, hW, hfields, hstorage, hstack, hsafe, hstackLen,
    hstatesLen, hlengthsLen, hstatesB, hlengthsB⟩
  have hremainingLen : remaining.length = 0 := by
    have hlen := congrArg List.length hword
    simp only [List.length_append] at hlen
    omega
  have hremaining : remaining = [] := List.eq_nil_of_length_eq_zero hremainingLen
  have hprocessed : processed = word := by
    simpa [hremaining] using hword.symm
  subst remaining
  subst processed
  have hstackRoot : stack = [reachable M.1 M.2 t] := by
    exact hstack.trans (evalWord_encodeTree_nil M.1 M.2 t)
  rcases hstorage with ⟨hS3, hL3, hO3, hdepth3, hrep⟩
  have hrepRoot : RowsRep states lengths M.2.2.1.length
      [reachable M.1 M.2 t] := by
    simpa [hstackRoot] using hrep
  let rootLen := lengths.getD 0 0
  have hwordPos : 0 < word.length := by
    simpa [word, encodeTree_length] using
      Lax842588Proofs.AutomatonRamCorrectness.treeSize_pos M.1 t
  have hlengthsNonempty : 0 < lengths.length := by
    rw [hlengthsLen]
    exact hwordPos
  have hrootLenLeT : rootLen ≤ M.2.2.1.length :=
    rowsRep_row_length_le hrepRoot (by simp)
  have hTleStates : M.2.2.1.length ≤ states.length := by
    rw [hstatesLen]
    have hone : 1 ≤ word.length := hwordPos
    simpa [Nat.one_mul] using Nat.mul_le_mul_right M.2.2.1.length hone
  have hrootSpan : rootLen ≤ states.length := hrootLenLeT.trans hTleStates
  have hrootLenB : rootLen < B := hrootLenLeT.trans_lt hTB
  have hstatesLenB : states.length < B := by
    rw [hstatesLen]
    exact hstatesCapacityB'
  have hlengthsLenB : lengths.length < B := by
    rw [hlengthsLen]
    exact hwordLenB'
  have hFB : M.2.2.2.length < B := by
    have h := getD_lt_of_mem_bound
      (i := M.1.length + 4 +
        M.2.2.1.length * (maximumRank M.1 + 3)) h0 hparameterB
    rwa [encodeAutomaton_acceptCount] at h
  have hscan := scanAccepting_spec B M states lengths rootLen h0 h1
    hparameterB hstatesB hlengthsB hparameterLenB hstatesLenB
    hlengthsLenB hlengthsNonempty hrootSpan hrootLenB hFB
  have hscanPre : ScanAcceptContext M states lengths rootLen sigma3 := by
    rcases hfields with ⟨hP3, hA3, hQ3, hT3, hR3, hwidth3, hrecords3,
      hacceptBase3, hF3, hn3⟩
    exact ⟨hP3, hS3, hL3, hacceptBase3, hF3, rfl⟩
  obtain ⟨sigma4, hrun4, hscanPost⟩ := hscan.run hscanPre
  have haccept : RootAcceptingSeen states M.2.2.2 rootLen ↔
      (M.2.toAutomaton M.1).Accepts t := by
    calc
      RootAcceptingSeen states M.2.2.2 rootLen ↔
          ∃ q ∈ reachable M.1 M.2 t, q ∈ M.2.2.2 :=
        rootAcceptingSeen_rowsRep_iff states lengths M.2.2.1.length
          (reachable M.1 M.2 t) M.2.2.2 hrepRoot
      _ ↔ EncodedAutomatonEvaluation.accepts M.1 M.2 t = true := by
        constructor
        · rintro ⟨q, hq, haccepting⟩
          exact List.any_eq_true.mpr
            ⟨q, hq, List.contains_iff_mem.mpr haccepting⟩
        · rw [EncodedAutomatonEvaluation.accepts, List.any_eq_true]
          rintro ⟨q, hq, haccepting⟩
          exact ⟨q, hq, List.contains_iff_mem.mp haccepting⟩
      _ ↔ (M.2.toAutomaton M.1).Accepts t := accepts_eq_true_iff M.1 M.2 t
  have hrun : Run B automatonBackend sigma sigma4
      (automatonBackendCost M t) := by
    have hrunExact := hrun3.seq (hrun4.seq Run.skip)
    unfold automatonBackend automatonBackendCost
    apply hrunExact.mono
    have hacceptCost := Nat.mul_le_mul_left
      (39 * M.2.2.2.length + 34) hrootLenLeT
    dsimp [word] at hrunExact ⊢
    simp only [encodeTree_length] at hrunExact ⊢
    omega
  refine ⟨sigma4, hrun, ?_⟩
  change sigma4.out = sigma.out ++
    [if (M.2.toAutomaton M.1).Accepts t then 1 else 0]
  rw [hscanPost, hevalOut (by decide), haccept]

end Lax842588Proofs.AutomatonRamBackend
