import Lax842588Proofs.AutomatonRamTransition

namespace Lax842588Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588Proofs.ArrayInput
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamProgram
open Lax842588Proofs.AutomatonTableEncoding

noncomputable def transitionOutputs (M : EncodedAutomaton)
    (states lengths : List Nat) (depth k symbol upto : Nat) : List Nat :=
  (List.range upto).flatMap
    (transitionOutputAt M states lengths depth k symbol)

theorem transitionOutputAt_length_le_one (M : EncodedAutomaton)
    (states lengths : List Nat) (depth k symbol tr : Nat) :
    (transitionOutputAt M states lengths depth k symbol tr).length ≤ 1 := by
  unfold transitionOutputAt
  split <;> simp

theorem transitionOutputs_length_le (M : EncodedAutomaton)
    (states lengths : List Nat) (depth k symbol upto : Nat) :
    (transitionOutputs M states lengths depth k symbol upto).length ≤ upto := by
  induction upto with
  | zero => simp [transitionOutputs]
  | succ upto ih =>
      unfold transitionOutputs at ih ⊢
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton]
      simp only [List.length_append]
      have := transitionOutputAt_length_le_one M states lengths depth k symbol upto
      omega

theorem transitionOutputs_succ (M : EncodedAutomaton)
    (states lengths : List Nat) (depth k symbol upto : Nat) :
    transitionOutputs M states lengths depth k symbol (upto + 1) =
      transitionOutputs M states lengths depth k symbol upto ++
        transitionOutputAt M states lengths depth k symbol upto := by
  simp [transitionOutputs, List.range_succ, List.flatMap_append]

def ScanStaticContext (M : EncodedAutomaton)
    (states lengths : List Nat) (depth k symbol : Nat) (σ : Env) : Prop :=
  σ.arrs "P" = encodeAutomaton M ∧ σ.arrs "S" = states ∧
    σ.arrs "L" = lengths ∧ (σ.arrs "O").length = M.2.2.1.length ∧
    σ.vars "records" = M.1.length + 4 ∧
    σ.vars "T" = M.2.2.1.length ∧
    σ.vars "R" = maximumRank M.1 ∧
    σ.vars "width" = maximumRank M.1 + 3 ∧
    σ.vars "Q" = M.2.1 ∧ σ.vars "depth" = depth ∧
    σ.vars "k" = k ∧ σ.vars "sym" = symbol

def ScanInv (M : EncodedAutomaton) (states lengths : List Nat)
    (depth k symbol : Nat) (σ : Env) : Prop :=
  ScanStaticContext M states lengths depth k symbol σ ∧
    σ.vars "tr" ≤ M.2.2.1.length ∧
    σ.vars "scratchLen" =
      (transitionOutputs M states lengths depth k symbol (σ.vars "tr")).length ∧
    PrefixEq (σ.arrs "O")
      (transitionOutputs M states lengths depth k symbol (σ.vars "tr"))

theorem scanStatic_of_checkTransition_frame
    (M : EncodedAutomaton) (states lengths : List Nat)
    (depth k symbol : Nat) {σ σ' : Env}
    (hctx : ScanStaticContext M states lengths depth k symbol σ)
    (hOlen : (σ'.arrs "O").length = (σ.arrs "O").length)
    (hvars : ∀ y, y ∉ checkTransition.wvars → σ'.vars y = σ.vars y)
    (harrs : ∀ a, a ∉ checkTransition.warrs → σ'.arrs a = σ.arrs a) :
    ScanStaticContext M states lengths depth k symbol σ' := by
  rcases hctx with ⟨hP, hS, hL, hO, hrecords, hT, hR, hwidth, hQ,
    hdepth, hk, hsym⟩
  exact ⟨(harrs "P" (by decide)).trans hP,
    (harrs "S" (by decide)).trans hS,
    (harrs "L" (by decide)).trans hL,
    hOlen.trans hO,
    (hvars "records" (by decide)).trans hrecords,
    (hvars "T" (by decide)).trans hT,
    (hvars "R" (by decide)).trans hR,
    (hvars "width" (by decide)).trans hwidth,
    (hvars "Q" (by decide)).trans hQ,
    (hvars "depth" (by decide)).trans hdepth,
    (hvars "k" (by decide)).trans hk,
    (hvars "sym" (by decide)).trans hsym⟩

theorem scanTransitionsBody_spec (B : Nat) (M : EncodedAutomaton)
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
      (fun σ => ScanInv M states lengths depth k symbol σ ∧
        σ.vars "tr" < M.2.2.1.length)
      scanTransitionsBody
      (fun σ σ' => ScanInv M states lengths depth k symbol σ' ∧
        σ'.vars "tr" = σ.vars "tr" + 1)
      ((70 * (M.2.2.1.length + 1) + 4) * k + 160) := by
  intro σ hσ
  let tr := σ.vars "tr"
  let output := transitionOutputs M states lengths depth k symbol tr
  let outputArray := σ.arrs "O"
  have htr : tr < M.2.2.1.length := hσ.2
  have houtTr : output.length ≤ tr := transitionOutputs_length_le M states lengths
    depth k symbol tr
  have houtputLen : outputArray.length = M.2.2.1.length := by
    dsimp [outputArray]
    exact hσ.1.1.2.2.2.1
  have hmul : tr * (maximumRank M.1 + 3) + (maximumRank M.1 + 3) ≤
      M.2.2.1.length * (maximumRank M.1 + 3) := by
    calc
      tr * (maximumRank M.1 + 3) + (maximumRank M.1 + 3) =
          (tr + 1) * (maximumRank M.1 + 3) := by rw [Nat.add_mul, one_mul]
      _ ≤ M.2.2.1.length * (maximumRank M.1 + 3) :=
        Nat.mul_le_mul_right _ (by omega)
  have hrecordWork : M.1.length + 4 + tr * (maximumRank M.1 + 3) +
      (maximumRank M.1 + 3) < B := by omega
  have hct0 := checkTransition_spec B M states lengths outputArray output depth k symbol tr
    h0 h1 hparameterB hstatesB hlengthsB hparameterLenB hstatesLenB hlengthsLenB
    houtputLen hσ.1.2.2.2 houtTr htr hkR hkdepth hdepthRows hwidthB hdepthB hkB
    hsymbolB hQB hTB hlenLe hspan haddrB hrecordWork
  have hct : Spec B
      (TransitionContext M states lengths outputArray output depth k symbol tr)
      checkTransition
      (fun τ τ' =>
        let output' := output ++ transitionOutputAt M states lengths depth k symbol tr
        τ'.vars "scratchLen" = output'.length ∧ PrefixEq (τ'.arrs "O") output' ∧
          ScanStaticContext M states lengths depth k symbol τ' ∧
          τ'.vars "tr" = tr)
      ((70 * (M.2.2.1.length + 1) + 4) * k + 150) := hct0.frame.post (by
    rintro τ τ' hpre ⟨hout, hvars, harrs, _⟩
    rcases hpre with ⟨hP, hS, hL, hO, hrecords, hT, hR, hwidth, hQ, htr',
      hdepth, hk, hsym, hscratch⟩
    have hstatic : ScanStaticContext M states lengths depth k symbol τ :=
      ⟨hP, hS, hL, (congrArg List.length hO).trans houtputLen, hrecords, hT, hR, hwidth,
        hQ, hdepth, hk, hsym⟩
    exact ⟨hout.1, hout.2.1,
      scanStatic_of_checkTransition_frame M states lengths depth k symbol
        hstatic (hout.2.2.trans (congrArg List.length hO).symm) hvars harrs,
      (hvars "tr" (by decide)).trans htr'⟩)
  have hpre : TransitionContext M states lengths outputArray output depth k symbol tr σ := by
    rcases hσ.1 with ⟨hstatic, htrLe, hscratch, hprefix⟩
    rcases hstatic with ⟨hP, hS, hL, hO, hrecords, hT, hR, hwidth, hQ,
      hdepth, hk, hsym⟩
    exact ⟨hP, hS, hL, rfl, hrecords, hT, hR, hwidth, hQ, rfl,
      hdepth, hk, hsym, by simpa [output, tr] using hscratch⟩
  unfold scanTransitionsBody seqs
  run_vcg [hct]
  all_goals simp_all [ScanInv, ScanStaticContext, transitionOutputs_succ, tr, output]
  all_goals omega

theorem scanTransitionsLoop_spec (B : Nat) (M : EncodedAutomaton)
    (states lengths : List Nat) (depth k symbol : Nat)
    (hbody : Spec B
      (fun σ => ScanInv M states lengths depth k symbol σ ∧
        σ.vars "tr" < M.2.2.1.length)
      scanTransitionsBody
      (fun σ σ' => ScanInv M states lengths depth k symbol σ' ∧
        σ'.vars "tr" = σ.vars "tr" + 1)
      ((70 * (M.2.2.1.length + 1) + 4) * k + 160))
    (hTB : M.2.2.1.length < B) :
    Spec B (ScanInv M states lengths depth k symbol)
      scanTransitionsLoop
      (fun _ σ' => ScanInv M states lengths depth k symbol σ' ∧
        σ'.vars "tr" = M.2.2.1.length)
      ((((70 * (M.2.2.1.length + 1) + 4) * k + 160) + 4) *
        M.2.2.1.length + 4) := by
  unfold scanTransitionsLoop
  exact Spec.forRange "tr" "T" (ScanInv M states lengths depth k symbol)
    M.2.2.1.length ((70 * (M.2.2.1.length + 1) + 4) * k + 160)
    ((((70 * (M.2.2.1.length + 1) + 4) * k + 160) + 4) *
      M.2.2.1.length + 4)
    (by rintro σ ⟨_, htr, _⟩; omega)
    (by rintro σ ⟨hstatic, _⟩; exact hstatic.2.2.2.2.2.1 ▸ hTB)
    (by rintro σ ⟨hstatic, _⟩; exact hstatic.2.2.2.2.2.1)
    (by rintro _ ⟨_, htr, _⟩; exact htr)
    hbody (fun _ h => h)
    (fun _ _ => Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)

end Lax842588Proofs.AutomatonRamCorrectness
