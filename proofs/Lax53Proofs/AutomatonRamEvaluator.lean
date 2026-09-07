import Lax53Proofs.AutomatonRamAccept

namespace Lax53Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 2000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53Proofs.ArrayInput
open Lax53.RankedTree
open Lax53.ValueTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.AutomatonRamProgram
open Lax53Proofs.AutomatonTableEncoding
open Lax53Proofs.EncodedAutomatonEvaluation
open Lax53Proofs.EncodedAutomatonWordEvaluation

/-- The array extents required by the uniform evaluator before it starts. -/
def EvaluatorInitial (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (sigma : Env) : Prop :=
  (sigma.arrs "P").length = (encodeAutomaton M).length ∧
    (sigma.arrs "W").length = treeSize t ∧
    sigma.arrs "S" =
      List.replicate (treeSize t * M.2.2.1.length) 0 ∧
    sigma.arrs "L" = List.replicate (treeSize t) 0 ∧
    (sigma.arrs "O").length = M.2.2.1.length ∧
    sigma.inp = specializedInput M t

/-- IMP+ cost before compilation. The first summand marshals the automaton,
the middle summand evaluates the postorder word, and the last scans the
accepting states in the root row. -/
def evaluatorImpCost (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Nat :=
  (12 * (encodeAutomaton M).length + 7) + 100 +
    (12 * treeSize t + 6) +
    (nodeCoefficient M *
      (treeSize t + rankSum M.1 (encodeTree M.1 t)) + 20) +
    ((39 * M.2.2.2.length + 34) * M.2.2.1.length + 30) + 1

/-- End-to-end correctness of the uniform IMP+ evaluator, under the explicit
value bounds needed by the bounded semantics. -/
theorem evaluator_spec (B : Nat) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hwordLenB : treeSize t < B)
    (hstatesCapacityB : treeSize t * M.2.2.1.length < B)
    (hwidthB : maximumRank M.1 + 3 < B) (hQB : M.2.1 < B)
    (hTB : M.2.2.1.length < B)
    (hheaderWorkB : M.1.length + M.2.1 + M.2.2.1.length +
      maximumRank M.1 + M.2.2.1.length * (maximumRank M.1 + 3) +
        M.2.2.2.length + treeSize t + 20 < B)
    (hworkB : M.1.length + 4 +
      M.2.2.1.length * (maximumRank M.1 + 3) +
        (maximumRank M.1 + 3) < B) :
    Spec B (EvaluatorInitial M t) evaluator
      (fun sigma sigma' => sigma'.out = sigma.out ++
        [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0])
      (evaluatorImpCost M t) := by
  intro sigma hsigma
  let parameter := encodeAutomaton M
  let word := encodeTree M.1 t
  have hwordLenB' : word.length < B := by
    simpa [word] using hwordLenB
  have hstatesCapacityB' : word.length * M.2.2.1.length < B := by
    simpa [word] using hstatesCapacityB
  have hinput : specializedInput M t =
      parameter.length :: (parameter ++ (word.length :: word)) := by
    simp [specializedInput, modelCheckingInput, block, parameter, word]
  have hp := (readParameter_spec B parameter (word.length :: word)
    hparameterLenB hparameterB).frame
  have hpPre : (sigma.arrs "P").length = parameter.length ∧
      sigma.inp = parameter.length :: (parameter ++ (word.length :: word)) := by
    exact ⟨hsigma.1, hinput ▸ hsigma.2.2.2.2.2⟩
  obtain ⟨sigma1, hrun1,
      ⟨hpPost, hpVars, hpArrs, hpInp, hpOut⟩⟩ := hp.run hpPre
  rcases hpPost with ⟨hP1, hInp1, hi1⟩
  have hh := (readHeader_spec B M word h0 hparameterB hparameterLenB
    hwordLenB' (by simpa [word] using hheaderWorkB)).frame
  obtain ⟨sigma2, hrun2,
      ⟨hheader, hhVars, hhArrs, hhInp, hhOut⟩⟩ :=
    hh.run ⟨hP1, hInp1⟩
  rcases hheader with ⟨hP2, hInp2, hA2, hQ2, hT2, hR2, hwidth2,
    hrecords2, hacceptBase2, hF2, hn2⟩
  have hW2Len : (sigma2.arrs "W").length = word.length := by
    rw [(hhArrs "W" (by decide)).trans (hpArrs "W" (by decide))]
    simpa [word] using hsigma.2.1
  have hreadW := (readArr_spec B "W" "wi" "n" "wv" word []
    (by decide) (by decide) (by decide) hwordLenB'
    (fun v hv => lt_trans (encodeTree_symbols_lt M.1 t v (by simpa [word] using hv))
      (by omega))).frame
  obtain ⟨sigma2w, hrun2w,
      ⟨⟨hW2w, hInp2w, hwi2w⟩, hreadWVars, hreadWArrs,
        hreadWInp, hreadWOut⟩⟩ :=
    hreadW.run ⟨hW2Len, hn2, by simpa using hInp2⟩
  have hS2 : sigma2.arrs "S" =
      List.replicate (word.length * M.2.2.1.length) 0 := by
    rw [(hhArrs "S" (by decide)).trans (hpArrs "S" (by decide))]
    simpa [word] using hsigma.2.2.1
  have hL2 : sigma2.arrs "L" = List.replicate word.length 0 := by
    rw [(hhArrs "L" (by decide)).trans (hpArrs "L" (by decide))]
    simpa [word] using hsigma.2.2.2.1
  have hO2 : (sigma2.arrs "O").length = M.2.2.1.length := by
    rw [(hhArrs "O" (by decide)).trans (hpArrs "O" (by decide))]
    exact hsigma.2.2.2.2.1
  have hS2w : sigma2w.arrs "S" =
      List.replicate (word.length * M.2.2.1.length) 0 :=
    (hreadWArrs "S" (by decide)).trans hS2
  have hL2w : sigma2w.arrs "L" = List.replicate word.length 0 :=
    (hreadWArrs "L" (by decide)).trans hL2
  have hO2w : (sigma2w.arrs "O").length = M.2.2.1.length := by
    rw [hreadWArrs "O" (by decide)]
    exact hO2
  have heval := (evaluateTree_spec B M word h0 h1 hparameterB
    hparameterLenB hwordLenB' hstatesCapacityB'
    (encodeTree_symbols_lt M.1 t) hwidthB hQB hTB hworkB
    (safeEval_encodeTree M.1 M.2 t [])).frame
  have hevalPre : EvaluateTreeContext B M word sigma2w := by
    exact ⟨⟨(hreadWArrs "P" (by decide)).trans hP2,
      (hreadWVars "A" (by decide)).trans hA2,
      (hreadWVars "Q" (by decide)).trans hQ2,
      (hreadWVars "T" (by decide)).trans hT2,
      (hreadWVars "R" (by decide)).trans hR2,
      (hreadWVars "width" (by decide)).trans hwidth2,
      (hreadWVars "records" (by decide)).trans hrecords2,
      (hreadWVars "acceptBase" (by decide)).trans hacceptBase2,
      (hreadWVars "F" (by decide)).trans hF2,
      (hreadWVars "n" (by decide)).trans hn2⟩,
      hW2w, hS2w, hL2w, hO2w, by rw [hW2w]; exact hstatesCapacityB'⟩
  obtain ⟨sigma3, hrun3,
      ⟨⟨hinv, hnodeDone⟩, hevalVars, hevalArrs, hevalInp, hevalOut⟩⟩ :=
    heval.run hevalPre
  rcases hinv with ⟨processed, remaining, stack, states, lengths,
    hword, hnode, hinp, hfields, hstorage, hstack, hsafe, hstackLen,
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
    simpa [word] using treeSize_pos M.1 t
  have hlengthsNonempty : 0 < lengths.length := by
    rw [hlengthsLen]
    exact hwordPos
  have hrootLenLeT : rootLen ≤ M.2.2.1.length := by
    exact rowsRep_row_length_le hrepRoot (by simp)
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
    hlengthsLenB hlengthsNonempty hrootSpan hrootLenB
    hFB
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
      _ ↔ (M.2.toAutomaton M.1).Accepts t :=
        accepts_eq_true_iff M.1 M.2 t
  have hrun : Run B evaluator sigma sigma4 (evaluatorImpCost M t) := by
    have hrunExact :=
      hrun1.seq (hrun2.seq (hrun2w.seq (hrun3.seq (hrun4.seq Run.skip))))
    have hacceptCost := Nat.mul_le_mul_left
      (39 * M.2.2.2.length + 34) hrootLenLeT
    change Run B
      (.seq readParameter (.seq readHeader (.seq readTreeWord
        (.seq evaluateTree (.seq scanAccepting .skip)))))
      sigma sigma4 (evaluatorImpCost M t)
    apply hrunExact.mono
    unfold evaluatorImpCost
    dsimp [parameter, word] at hrunExact ⊢
    simp only [encodeTree_length] at hrunExact ⊢
    omega
  refine ⟨sigma4, hrun, ?_⟩
  change sigma4.out = sigma.out ++
    [if (M.2.toAutomaton M.1).Accepts t then 1 else 0]
  rw [hscanPost, hevalOut (by decide), hreadWOut (by decide),
    hhOut (by decide), hpOut (by decide)]
  rw [haccept]

end Lax53Proofs.AutomatonRamCorrectness
