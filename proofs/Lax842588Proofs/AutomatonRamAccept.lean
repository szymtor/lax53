import Lax842588Proofs.AutomatonRamEvaluateTree

namespace Lax842588Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 2000000
open Classical

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamProgram
open Lax842588Proofs.AutomatonTableEncoding
open Lax842588Proofs.EncodedAutomatonWordEvaluation

def AcceptingSeen (accepting : List Nat) (q upto : Nat) : Prop :=
  ∃ f < upto, accepting.getD f 0 = q

@[simp] theorem not_acceptingSeen_zero (accepting : List Nat) (q : Nat) :
    ¬ AcceptingSeen accepting q 0 := by simp [AcceptingSeen]

theorem acceptingSeen_succ (accepting : List Nat) (q f : Nat) :
    AcceptingSeen accepting q (f + 1) ↔
      AcceptingSeen accepting q f ∨ accepting.getD f 0 = q := by
  constructor
  · rintro ⟨i, hi, heq⟩
    by_cases hif : i < f
    · exact Or.inl ⟨i, hif, heq⟩
    · right
      have : i = f := by omega
      simpa [this] using heq
  · rintro (⟨i, hi, heq⟩ | heq)
    · exact ⟨i, by omega, heq⟩
    · exact ⟨f, by omega, heq⟩

theorem acceptingSeen_length_iff (accepting : List Nat) (q : Nat) :
    AcceptingSeen accepting q accepting.length ↔ q ∈ accepting := by
  constructor
  · rintro ⟨i, hi, heq⟩
    rw [List.getD_eq_getElem _ _ hi] at heq
    exact heq ▸ List.getElem_mem hi
  · intro hq
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hq
    exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact heq⟩

def AcceptInnerInv (M : EncodedAutomaton) (q : Nat) (prior : Prop)
    (sigma : Env) : Prop :=
  sigma.arrs "P" = encodeAutomaton M ∧
    sigma.vars "acceptBase" =
      M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) ∧
    sigma.vars "F" = M.2.2.2.length ∧ sigma.vars "state" = q ∧
    sigma.vars "f" ≤ M.2.2.2.length ∧
    sigma.vars "answer" =
      if prior ∨ AcceptingSeen M.2.2.2 q (sigma.vars "f") then 1 else 0

theorem scanAcceptingInnerBody_spec (B : Nat) (M : EncodedAutomaton)
    (q : Nat) (prior : Prop)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hFB : M.2.2.2.length < B) (hqB : q < B) :
    Spec B
      (fun sigma => AcceptInnerInv M q prior sigma ∧
        sigma.vars "f" < M.2.2.2.length)
      scanAcceptingInnerBody
      (fun sigma sigma' => AcceptInnerInv M q prior sigma' ∧
        sigma'.vars "f" = sigma.vars "f" + 1) 35 := by
  intro sigma hsigma
  let f := sigma.vars "f"
  have hf : f < M.2.2.2.length := hsigma.2
  have haddr : M.1.length + 5 +
      M.2.2.1.length * (maximumRank M.1 + 3) + f <
        (encodeAutomaton M).length := by
    rw [encodeAutomaton_length]
    omega
  have hvalue : (encodeAutomaton M).getD
      (M.1.length + 5 + M.2.2.1.length * (maximumRank M.1 + 3) + f) 0 =
        M.2.2.2.getD f 0 := encodeAutomaton_accept M f
  have hvalueB : M.2.2.2.getD f 0 < B := by
    rw [← hvalue]
    exact getD_lt_of_mem_bound h0 hparameterB
  have hread : (encodeAutomaton M)[M.1.length + 4 +
      M.2.2.1.length * (maximumRank M.1 + 3) + 1 + f]?.getD 0 =
        M.2.2.2.getD f 0 := by
    rw [← List.getD_eq_getElem?_getD]
    rw [show M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) +
      1 + f = M.1.length + 5 +
        M.2.2.1.length * (maximumRank M.1 + 3) + f by omega]
    exact hvalue
  have hseen := acceptingSeen_succ M.2.2.2 q f
  unfold scanAcceptingInnerBody seqs
  run_vcg
  all_goals simp_all [AcceptInnerInv, f, hseen]
  all_goals try exact haddr
  all_goals try exact hvalue
  all_goals try exact hvalueB
  all_goals try exact hread
  all_goals try aesop
  all_goals omega

theorem scanAcceptingInnerLoop_spec (B : Nat) (M : EncodedAutomaton)
    (q : Nat) (prior : Prop)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hFB : M.2.2.2.length < B) (hqB : q < B) :
    Spec B (AcceptInnerInv M q prior) scanAcceptingInnerLoop
      (fun _ sigma' => AcceptInnerInv M q prior sigma' ∧
        sigma'.vars "f" = M.2.2.2.length)
      (39 * M.2.2.2.length + 4) := by
  unfold scanAcceptingInnerLoop
  exact Spec.forRange "f" "F" (AcceptInnerInv M q prior)
    M.2.2.2.length 35 (39 * M.2.2.2.length + 4)
    (by rintro sigma ⟨_, _, hF, _, hf, _⟩; omega)
    (by rintro sigma ⟨_, _, hF, _, _, _⟩; omega)
    (by rintro _ ⟨_, _, hF, _, _, _⟩; exact hF)
    (by rintro _ ⟨_, _, _, _, hf, _⟩; exact hf)
    (scanAcceptingInnerBody_spec B M q prior h0 h1 hparameterB
      hparameterLenB hFB hqB)
    (fun _ h => h)
    (fun _ _ => by omega)

def RootAcceptingSeen (states accepting : List Nat) (upto : Nat) : Prop :=
  ∃ z < upto, states.getD z 0 ∈ accepting

@[simp] theorem not_rootAcceptingSeen_zero (states accepting : List Nat) :
    ¬ RootAcceptingSeen states accepting 0 := by simp [RootAcceptingSeen]

theorem rootAcceptingSeen_succ (states accepting : List Nat) (z : Nat) :
    RootAcceptingSeen states accepting (z + 1) ↔
      RootAcceptingSeen states accepting z ∨ states.getD z 0 ∈ accepting := by
  constructor
  · rintro ⟨i, hi, hmem⟩
    by_cases hiz : i < z
    · exact Or.inl ⟨i, hiz, hmem⟩
    · right
      have : i = z := by omega
      simpa [this] using hmem
  · rintro (⟨i, hi, hmem⟩ | hmem)
    · exact ⟨i, by omega, hmem⟩
    · exact ⟨z, by omega, hmem⟩

theorem rootAcceptingSeen_rowsRep_iff (states lengths : List Nat)
    (width : Nat) (root accepting : List Nat)
    (hrep : RowsRep states lengths width [root]) :
    RootAcceptingSeen states accepting (lengths.getD 0 0) ↔
      ∃ q ∈ root, q ∈ accepting := by
  have hrow := hrep.2 0 (by simp)
  have hlength : lengths.getD 0 0 = root.length := by
    simpa using hrow.1
  have hvalue (i : Nat) (hi : i < root.length) :
      states.getD i 0 = root.getD i 0 := by
    simpa using hrow.2.2 i hi
  constructor
  · rintro ⟨i, hi, haccept⟩
    rw [hlength] at hi
    have hmem : root.getD i 0 ∈ root := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact ⟨root.getD i 0, hmem, (hvalue i hi) ▸ haccept⟩
  · rintro ⟨q, hq, haccept⟩
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hq
    refine ⟨i, ?_, ?_⟩
    · rwa [hlength]
    · rw [hvalue i hi, List.getD_eq_getElem _ _ hi, heq]
      exact haccept

def AcceptOuterInv (M : EncodedAutomaton) (states : List Nat)
    (rootLen : Nat) (sigma : Env) : Prop :=
  sigma.arrs "P" = encodeAutomaton M ∧ sigma.arrs "S" = states ∧
    sigma.vars "acceptBase" =
      M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) ∧
    sigma.vars "F" = M.2.2.2.length ∧ sigma.vars "rootLen" = rootLen ∧
    sigma.vars "z" ≤ rootLen ∧
    sigma.vars "answer" =
      if RootAcceptingSeen states M.2.2.2 (sigma.vars "z") then 1 else 0

theorem scanAcceptingOuterBody_spec (B : Nat) (M : EncodedAutomaton)
    (states : List Nat) (rootLen : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hstatesLenB : states.length < B)
    (hrootSpan : rootLen ≤ states.length)
    (hrootLenB : rootLen < B) (hFB : M.2.2.2.length < B) :
    Spec B
      (fun sigma => AcceptOuterInv M states rootLen sigma ∧
        sigma.vars "z" < rootLen)
      scanAcceptingOuterBody
      (fun sigma sigma' => AcceptOuterInv M states rootLen sigma' ∧
        sigma'.vars "z" = sigma.vars "z" + 1)
      (39 * M.2.2.2.length + 30) := by
  intro sigma hsigma
  let z := sigma.vars "z"
  let q := states.getD z 0
  let prior := RootAcceptingSeen states M.2.2.2 z
  have hz : z < rootLen := hsigma.2
  have hzStates : z < states.length := lt_of_lt_of_le hz hrootSpan
  have hqB : q < B := getD_lt_of_mem_bound h0 hstatesB
  have hinner := scanAcceptingInnerLoop_spec B M q prior h0 h1 hparameterB
    hparameterLenB hFB hqB
  have hinnerF : Spec B
      (fun tau => AcceptInnerInv M q prior tau ∧
        tau.arrs "S" = states ∧ tau.vars "rootLen" = rootLen ∧
        tau.vars "z" = z)
      scanAcceptingInnerLoop
      (fun _ tau' => (AcceptInnerInv M q prior tau' ∧
          tau'.vars "f" = M.2.2.2.length) ∧
        tau'.arrs "S" = states ∧ tau'.vars "rootLen" = rootLen ∧
        tau'.vars "z" = z)
      (39 * M.2.2.2.length + 4) := by
    refine hinner.frame.conseq (fun _ h => h.1) ?_ le_rfl
    rintro tau tau' hpre ⟨hpost, hvars, harrs, hinp, hout⟩
    exact ⟨hpost,
      (harrs "S" (by decide)).trans hpre.2.1,
      (hvars "rootLen" (by decide)).trans hpre.2.2.1,
      (hvars "z" (by decide)).trans hpre.2.2.2⟩
  have hseen := rootAcceptingSeen_succ states M.2.2.2 z
  have hmem : AcceptingSeen M.2.2.2 q M.2.2.2.length ↔
      q ∈ M.2.2.2 := acceptingSeen_length_iff M.2.2.2 q
  unfold scanAcceptingOuterBody seqs
  run_vcg [hinnerF]
  all_goals simp_all [AcceptOuterInv, AcceptInnerInv, z, q, prior, hseen, hmem]
  all_goals try exact hqB
  all_goals try aesop
  all_goals omega

theorem scanAcceptingOuterLoop_spec (B : Nat) (M : EncodedAutomaton)
    (states : List Nat) (rootLen : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hstatesLenB : states.length < B)
    (hrootSpan : rootLen ≤ states.length)
    (hrootLenB : rootLen < B) (hFB : M.2.2.2.length < B) :
    Spec B (AcceptOuterInv M states rootLen) scanAcceptingOuterLoop
      (fun _ sigma' => AcceptOuterInv M states rootLen sigma' ∧
        sigma'.vars "z" = rootLen)
      ((39 * M.2.2.2.length + 34) * rootLen + 4) := by
  unfold scanAcceptingOuterLoop
  exact Spec.forRange "z" "rootLen" (AcceptOuterInv M states rootLen)
    rootLen (39 * M.2.2.2.length + 30)
    ((39 * M.2.2.2.length + 34) * rootLen + 4)
    (by rintro sigma ⟨_, _, _, _, hroot, hz, _⟩; omega)
    (by rintro sigma ⟨_, _, _, _, hroot, _, _⟩; omega)
    (by rintro _ ⟨_, _, _, _, hroot, _, _⟩; exact hroot)
    (by rintro _ ⟨_, _, _, _, _, hz, _⟩; exact hz)
    (scanAcceptingOuterBody_spec B M states rootLen h0 h1 hparameterB
      hstatesB hparameterLenB hstatesLenB hrootSpan hrootLenB hFB)
    (fun _ h => h)
    (fun _ _ => Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)

def ScanAcceptContext (M : EncodedAutomaton) (states lengths : List Nat)
    (rootLen : Nat) (sigma : Env) : Prop :=
  sigma.arrs "P" = encodeAutomaton M ∧ sigma.arrs "S" = states ∧
    sigma.arrs "L" = lengths ∧
    sigma.vars "acceptBase" =
      M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) ∧
    sigma.vars "F" = M.2.2.2.length ∧ lengths[0]?.getD 0 = rootLen

theorem scanAccepting_spec (B : Nat) (M : EncodedAutomaton)
    (states lengths : List Nat) (rootLen : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hlengthsB : ∀ v ∈ lengths, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hstatesLenB : states.length < B) (hlengthsLenB : lengths.length < B)
    (hlengthsNonempty : 0 < lengths.length)
    (hrootSpan : rootLen ≤ states.length)
    (hrootLenB : rootLen < B) (hFB : M.2.2.2.length < B) :
    Spec B (ScanAcceptContext M states lengths rootLen) scanAccepting
      (fun sigma sigma' => sigma'.out = sigma.out ++
        [if RootAcceptingSeen states M.2.2.2 rootLen then 1 else 0])
      ((39 * M.2.2.2.length + 34) * rootLen + 30) := by
  have houter := scanAcceptingOuterLoop_spec B M states rootLen h0 h1
    hparameterB hstatesB hparameterLenB hstatesLenB hrootSpan hrootLenB hFB
  intro sigma hsigma
  have houterF : Spec B
      (fun tau => AcceptOuterInv M states rootLen tau ∧
        tau.out = sigma.out)
      scanAcceptingOuterLoop
      (fun _ tau' => (AcceptOuterInv M states rootLen tau' ∧
          tau'.vars "z" = rootLen) ∧ tau'.out = sigma.out)
      ((39 * M.2.2.2.length + 34) * rootLen + 4) := by
    refine houter.frame.conseq (fun _ h => h.1) ?_ le_rfl
    rintro tau tau' hpre ⟨hpost, hvars, harrs, hinp, hout⟩
    exact ⟨hpost, (hout (by decide)).trans hpre.2⟩
  have hrootValueB : lengths[0] < B :=
    hlengthsB _ (List.getElem_mem hlengthsNonempty)
  unfold scanAccepting seqs
  run_vcg [houterF]
  all_goals simp_all [ScanAcceptContext, AcceptOuterInv]
  all_goals try exact hrootValueB
  all_goals try aesop
  all_goals omega

end Lax842588Proofs.AutomatonRamCorrectness
