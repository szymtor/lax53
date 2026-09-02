import Lax53.AutomatonLinearTime
import Lax53Proofs.AutomatonRamEvaluator

namespace Lax53Proofs.AutomatonLinearTime

set_option maxHeartbeats 3000000
open Classical

open Lax13.Ram
open Lax13Proofs.Imp
open Lax13Proofs.Compile
open Lax13Proofs.Simulation
open Lax13Proofs.Transfer
open Lax53.RankedTree
open Lax53.EffectiveTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.AutomatonRamProgram
open Lax53Proofs.AutomatonRamCorrectness
open Lax53Proofs.AutomatonTableEncoding

/-- Largest word in a finite machine input, with zero as the empty default. -/
def maxEntry (input : List Nat) : Nat := input.max?.getD 0

theorem maxEntry_mem {input : List Nat} (hinput : input ≠ []) :
    maxEntry input ∈ input := by
  cases hmax : input.max? with
  | none =>
      have : input = [] := List.max?_eq_none_iff.mp hmax
      exact (hinput this).elim
  | some m =>
      simpa [maxEntry, hmax] using List.max?_mem hmax

theorem le_maxEntry_of_mem {input : List Nat} {v : Nat} (hv : v ∈ input) :
    v ≤ maxEntry input := by
  cases hmax : input.max? with
  | none =>
      have : input = [] := List.max?_eq_none_iff.mp hmax
      subst input
      simp at hv
  | some m =>
      have hle := (List.max?_eq_some_iff.mp hmax).2 v hv
      simpa [maxEntry, hmax] using hle

/-- Array sizes selected for the four arrays of the evaluator. -/
def evaluatorExt (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (name : String) : Nat :=
  if name = "P" then (encodeAutomaton M).length
  else if name = "S" then treeSize t * M.2.2.1.length
  else if name = "L" then treeSize t
  else if name = "O" then M.2.2.1.length
  else 0

theorem automatonInput_length (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    (automatonInput M t).length =
      (encodeAutomaton M).length + treeSize t + 2 := by
  simp [automatonInput, modelCheckingInput, block, treeSize]
  omega

theorem parameter_mem_automatonInput (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) {v : Nat}
    (hv : v ∈ encodeAutomaton M) : v ∈ automatonInput M t := by
  simp [automatonInput, modelCheckingInput, block, hv]

theorem evaluatorInitial_initEnv (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    EvaluatorInitial M t
      (initEnv (evaluatorExt M t) (automatonInput M t)) := by
  simp [EvaluatorInitial, initEnv, evaluatorExt]

/-- A deliberately loose IMP+ bound exhibiting the quadratic parameter
dependence independently of the machine compiler. -/
theorem evaluatorImpCost_le (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    evaluatorImpCost M t ≤
      1000 * ((encodeAutomaton M).length + 1) ^ 2 * treeSize t := by
  let p := (encodeAutomaton M).length
  let n := treeSize t
  let T := M.2.2.1.length
  let F := M.2.2.2.length
  have hn : 1 ≤ n := by
    dsimp [n]
    exact treeSize_pos M.1 t
  have hpEq : p = M.1.length + T * (maximumRank M.1 + 3) + F + 5 := by
    dsimp [p, T, F]
    exact encodeAutomaton_length M
  have hT : T ≤ p := by
    have hmul : T ≤ T * (maximumRank M.1 + 3) := by
      calc
        T = T * 1 := by omega
        _ ≤ T * (maximumRank M.1 + 3) :=
          Nat.mul_le_mul_left T (by omega)
    omega
  have hF : F ≤ p := by omega
  have hmeasure : n + rankSum M.1 (encodeTree M.1 t) ≤ 2 * n := by
    have hrank := rankSum_encodeTree_add_one M.1 t
    dsimp [n] at hrank ⊢
    omega
  have hsq : (T + 1) ^ 2 ≤ (p + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hnode : nodeCoefficient M *
      (n + rankSum M.1 (encodeTree M.1 t)) ≤
        600 * (p + 1) ^ 2 * n := by
    have hcoef : nodeCoefficient M ≤ 300 * (p + 1) ^ 2 := by
      unfold nodeCoefficient
      exact Nat.mul_le_mul_left 300 hsq
    have h := Nat.mul_le_mul hcoef hmeasure
    nlinarith
  have hacceptCoef : 39 * F + 34 ≤ 73 * (p + 1) := by
    omega
  have haccept : (39 * F + 34) * T ≤ 73 * (p + 1) ^ 2 := by
    have h := Nat.mul_le_mul hacceptCoef (show T ≤ p + 1 by omega)
    nlinarith
  have hacceptN : (39 * F + 34) * T ≤
      73 * (p + 1) ^ 2 * n :=
    haccept.trans (by
      have := Nat.mul_le_mul_left (73 * (p + 1) ^ 2) hn
      simpa using this)
  have hbase : 12 * p + 158 ≤ 200 * (p + 1) ^ 2 * n := by
    nlinarith [sq_nonneg (p : Int)]
  have hcostEq : evaluatorImpCost M t =
      (12 * p + 158) +
        nodeCoefficient M * (n + rankSum M.1 (encodeTree M.1 t)) +
        (39 * F + 34) * T := by
    unfold evaluatorImpCost
    dsimp [p, n, T, F]
    ring
  rw [hcostEq]
  calc
    (12 * p + 158) +
          nodeCoefficient M * (n + rankSum M.1 (encodeTree M.1 t)) +
          (39 * F + 34) * T ≤
        200 * (p + 1) ^ 2 * n + 600 * (p + 1) ^ 2 * n +
          73 * (p + 1) ^ 2 * n :=
      Nat.add_le_add (Nat.add_le_add hbase hnode) hacceptN
    _ ≤ 1000 * (p + 1) ^ 2 * n := by nlinarith

/--
---
conclusion: Lax53.AutomatonLinearTime.exists_uniform_linearTime_automatonAcceptance
---
The fixed compiled evaluator works for every encoded alphabet and automaton.
Its IMP+ execution uses at most `1000 (|M|+1)^2 |t|` cost units; compilation
has a fixed constant overhead. The larger displayed constant also pays for
the four-array address span required by the word-RAM simulation theorem.
-/
theorem exists_uniform_linearTime_automatonAcceptance :
    ∃ (program : Program) (constant : Nat),
      ∀ (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) (w : Nat),
        let parameterSize := (encodeAutomaton M).length
        let c := constant * (parameterSize + 1) ^ 2
        let input := automatonInput M t
        (∀ v ∈ input, c * (input.length + v + 1) ≤ 2 ^ w) →
          ∃ time ≤ c * treeSize t,
            RunsTo w program input
              (if M.2.toAutomaton M.1 |>.Accepts t then [1] else [0]) time := by
  refine ⟨program, 1000000, ?_⟩
  intro M t w
  dsimp only
  intro hword
  let p := (encodeAutomaton M).length
  let n := treeSize t
  let input := automatonInput M t
  let m := maxEntry input
  let scale := input.length + m + 1
  let B := 1000 * (p + 1) ^ 2 * scale
  have hn : 1 ≤ n := by
    dsimp [n]
    exact treeSize_pos M.1 t
  have hinputLen : input.length = p + n + 2 := by
    dsimp [input, p, n]
    exact automatonInput_length M t
  have hinputNe : input ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    rw [hinputLen] at this
    simp at this
  have hmMem : m ∈ input := maxEntry_mem hinputNe
  have hwordMax : 1000000 * (p + 1) ^ 2 * scale ≤ 2 ^ w := by
    simpa [p, input, m, scale] using hword (maxEntry (automatonInput M t))
      (maxEntry_mem (by simp [automatonInput, modelCheckingInput, block]))
  have hscale : 1 ≤ scale := by dsimp [scale]; omega
  have hsq : 1 ≤ (p + 1) ^ 2 := by nlinarith [sq_nonneg (p : Int)]
  have hB1 : 1 < B := by
    dsimp [B]
    nlinarith
  have hinputB : ∀ v ∈ input, v < B := by
    intro v hv
    have hvmax := le_maxEntry_of_mem hv
    dsimp [B, scale]
    nlinarith
  have hparameterB : ∀ v ∈ encodeAutomaton M, v < B := by
    intro v hv
    apply hinputB v
    dsimp [input]
    exact parameter_mem_automatonInput M t hv
  have hpEq : p = M.1.length + M.2.2.1.length *
      (maximumRank M.1 + 3) + M.2.2.2.length + 5 := by
    dsimp [p]
    exact encodeAutomaton_length M
  have hpLtInput : p < input.length := by omega
  have hnLtInput : n < input.length := by omega
  have hpB : p < B := lt_of_lt_of_le hpLtInput (by
    dsimp [B, scale]
    nlinarith)
  have hnB : n < B := lt_of_lt_of_le hnLtInput (by
    dsimp [B, scale]
    nlinarith)
  have hT : M.2.2.1.length ≤ p := by
    have hmul : M.2.2.1.length ≤ M.2.2.1.length *
        (maximumRank M.1 + 3) := by
      calc
        M.2.2.1.length = M.2.2.1.length * 1 := by omega
        _ ≤ M.2.2.1.length * (maximumRank M.1 + 3) :=
          Nat.mul_le_mul_left _ (by omega)
    omega
  have hF : M.2.2.2.length ≤ p := by omega
  have hfixed : M.2.2.1.length * (maximumRank M.1 + 3) ≤ p := by omega
  have hA : M.1.length ≤ p := by omega
  have hentryLe (i : Nat) (hi : i < p) :
      (encodeAutomaton M).getD i 0 ≤ m := by
    apply le_maxEntry_of_mem
    dsimp [input]
    apply parameter_mem_automatonInput M t
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hQ : M.2.1 ≤ m := by
    have hi : M.1.length + 1 < p := by omega
    have h := hentryLe (M.1.length + 1) hi
    rwa [encodeAutomaton_Q] at h
  have hR : maximumRank M.1 ≤ m := by
    have hi : M.1.length + 3 < p := by omega
    have h := hentryLe (M.1.length + 3) hi
    rwa [encodeAutomaton_R] at h
  have hprod : n * M.2.2.1.length ≤ scale * (p + 1) ^ 2 := by
    have hnp : n * M.2.2.1.length ≤ input.length * p :=
      Nat.mul_le_mul (by omega) hT
    have hright : input.length * p ≤ scale * (p + 1) ^ 2 :=
      Nat.mul_le_mul (by dsimp [scale]; omega) (by nlinarith [sq_nonneg (p : Int)])
    exact hnp.trans hright
  have hcapacityB : n * M.2.2.1.length < B := by
    dsimp [B]
    nlinarith
  have hwidthB : maximumRank M.1 + 3 < B := by
    dsimp [B, scale]
    nlinarith
  have hQB : M.2.1 < B := by
    dsimp [B, scale]
    nlinarith
  have hTB : M.2.2.1.length < B := hT.trans_lt hpB
  have hheaderWorkB : M.1.length + M.2.1 + M.2.2.1.length +
      maximumRank M.1 + M.2.2.1.length * (maximumRank M.1 + 3) +
        M.2.2.2.length + n + 20 < B := by
    dsimp [B, scale]
    nlinarith
  have hevalWorkB : M.1.length + 4 +
      M.2.2.1.length * (maximumRank M.1 + 3) +
        (maximumRank M.1 + 3) < B := by
    dsimp [B, scale]
    nlinarith
  have hspec := evaluator_spec B M t (by omega) hB1 hparameterB hpB hnB
    hcapacityB hwidthB hQB hTB hheaderWorkB hevalWorkB
  obtain ⟨sigma', hrun, hout⟩ := hspec.run (evaluatorInitial_initEnv M t)
  obtain ⟨k, hk, hbig⟩ := hrun
  have hfit : layout.FitsWords B w := by
    apply fitsWords_of_max_le hB1
    apply max_le
    · exact le_trans (by
        dsimp [B]
        nlinarith) hwordMax
    · exact le_trans (by
        simp [Layout.span, layout]
        dsimp [B]
        nlinarith) hwordMax
  obtain ⟨time, htime, hruns⟩ := compileProgram_runsTo hfit evaluator_ok
    hinputB hbig
  have himp := evaluatorImpCost_le M t
  have hmachine : layout.const * k ≤
      1000000 * (p + 1) ^ 2 * n := by
    have hk' : k ≤ 1000 * (p + 1) ^ 2 * n := by
      exact hk.trans (by simpa [p, n] using himp)
    simp [Layout.const, Layout.idxLen, layout]
    nlinarith
  refine ⟨time, htime.trans hmachine, ?_⟩
  have houtFinal : sigma'.out =
      [if (M.2.toAutomaton M.1).Accepts t then 1 else 0] := by
    simpa [initEnv] using hout
  have hsingleton :
      [if (M.2.toAutomaton M.1).Accepts t then 1 else 0] =
        (if (M.2.toAutomaton M.1).Accepts t then [1] else [0]) := by
    by_cases h : (M.2.toAutomaton M.1).Accepts t <;> simp [h]
  change RunsTo w (compileProgram layout evaluator) input
    (if (M.2.toAutomaton M.1).Accepts t then [1] else [0]) time
  rw [← hsingleton, ← houtFinal]
  exact hruns

end Lax53Proofs.AutomatonLinearTime
