import Lax53Proofs.AutomatonRamCorrectness

namespace Lax53Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53Proofs.ArrayInput
open Lax53.ValueTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.AutomatonRamProgram
open Lax53Proofs.AutomatonTableEncoding

def PrefixEq (array values : List Nat) : Prop :=
  values.length ≤ array.length ∧
    ∀ i < values.length, array.getD i 0 = values.getD i 0

theorem prefixEq_nil (array : List Nat) : PrefixEq array [] := by
  simp [PrefixEq]

theorem prefixEq_set_append {array values : List Nat} {v : Nat}
    (h : PrefixEq array values) (hlt : values.length < array.length) :
    PrefixEq (array.set values.length v) (values ++ [v]) := by
  constructor
  · simp
    omega
  · intro i hi
    by_cases hii : i < values.length
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]
      rw [List.getElem_set_ne (Nat.ne_of_gt hii)]
      rw [List.getD_eq_getElem _ _ hi]
      rw [List.getElem_append_left hii]
      rw [← List.getD_eq_getElem array 0 (lt_trans hii hlt)]
      rw [← List.getD_eq_getElem values 0 hii]
      exact h.2 i hii
    · have hieq : i = values.length := by simp at hi; omega
      subst i
      rw [List.getD_eq_getElem]
      · rw [List.getElem_set_self]
        simp
      · simp
        exact hlt

def TransitionMatchesAt (M : EncodedAutomaton) (states lengths : List Nat)
    (depth k symbol tr : Nat) : Prop :=
  let recordBase := M.1.length + 4 + tr * (maximumRank M.1 + 3)
  let transition := M.2.2.1.getD tr (0, 0, [])
  transition.1 = symbol ∧ transition.2.1 < M.2.1 ∧
    transition.2.2.length = k ∧
    ChildrenPrefix (encodeAutomaton M) states lengths recordBase depth k
      M.2.2.1.length k

noncomputable def transitionOutputAt (M : EncodedAutomaton) (states lengths : List Nat)
    (depth k symbol tr : Nat) : List Nat :=
  if TransitionMatchesAt M states lengths depth k symbol tr then
    [(M.2.2.1.getD tr (0, 0, [])).2.1]
  else []

def TransitionContext (M : EncodedAutomaton) (states lengths outputArray output : List Nat)
    (depth k symbol tr : Nat) (σ : Env) : Prop :=
  σ.arrs "P" = encodeAutomaton M ∧ σ.arrs "S" = states ∧
    σ.arrs "L" = lengths ∧ σ.arrs "O" = outputArray ∧
    σ.vars "records" = M.1.length + 4 ∧
    σ.vars "T" = M.2.2.1.length ∧
    σ.vars "R" = maximumRank M.1 ∧
    σ.vars "width" = maximumRank M.1 + 3 ∧
    σ.vars "Q" = M.2.1 ∧ σ.vars "tr" = tr ∧
    σ.vars "depth" = depth ∧ σ.vars "k" = k ∧
    σ.vars "sym" = symbol ∧ σ.vars "scratchLen" = output.length

def LoadedTransitionContext (M : EncodedAutomaton)
    (states lengths outputArray output : List Nat) (depth k symbol tr : Nat)
    (transition : TransitionCode) (base : Nat) (σ : Env) : Prop :=
  TransitionContext M states lengths outputArray output depth k symbol tr σ ∧
    σ.vars "base" = base ∧ σ.vars "tsym" = transition.1 ∧
    σ.vars "parent" = transition.2.1 ∧
    σ.vars "arity" = transition.2.2.length ∧ σ.vars "valid" = 1

def TransitionFieldsValid (M : EncodedAutomaton) (transition : TransitionCode)
    (symbol k : Nat) : Prop :=
  transition.1 = symbol ∧ transition.2.1 < M.2.1 ∧
    transition.2.2.length = k

def ValidatedTransitionContext (M : EncodedAutomaton)
    (states lengths outputArray output : List Nat) (depth k symbol tr : Nat)
    (transition : TransitionCode) (base : Nat) (σ : Env) : Prop :=
  TransitionContext M states lengths outputArray output depth k symbol tr σ ∧
    σ.vars "base" = base ∧ σ.vars "tsym" = transition.1 ∧
    σ.vars "parent" = transition.2.1 ∧
    σ.vars "arity" = transition.2.2.length ∧
    σ.vars "valid" = if TransitionFieldsValid M transition symbol k then 1 else 0

theorem loadTransition_spec (B : Nat) (M : EncodedAutomaton)
    (states lengths outputArray output : List Nat) (depth k symbol tr : Nat)
    (transition : TransitionCode) (base : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hsymbol : (encodeAutomaton M).getD base 0 = transition.1)
    (hparent : (encodeAutomaton M).getD (base + 1) 0 = transition.2.1)
    (harity : (encodeAutomaton M).getD (base + 2) 0 = transition.2.2.length)
    (hbaseEq : base = M.1.length + 4 + tr * (maximumRank M.1 + 3))
    (hbase : base + 2 < (encodeAutomaton M).length)
    (hbaseB : base + 2 < B) (htrB : tr < B)
    (hwidthB : maximumRank M.1 + 3 < B) :
    Spec B
      (TransitionContext M states lengths outputArray output depth k symbol tr)
      loadTransition
      (fun _ σ' => LoadedTransitionContext M states lengths outputArray output
        depth k symbol tr transition base σ') 50 := by
  intro σ hσ
  have hbase0 : base < (encodeAutomaton M).length := by omega
  have hbase1 : base + 1 < (encodeAutomaton M).length := by omega
  have hbase2 : base + 2 < (encodeAutomaton M).length := by omega
  have htsymB : transition.1 < B := by
    rw [← hsymbol]
    exact getD_lt_of_mem_bound h0 hparameterB
  have hparentB : transition.2.1 < B := by
    rw [← hparent]
    exact getD_lt_of_mem_bound h0 hparameterB
  have harityB : transition.2.2.length < B := by
    rw [← harity]
    exact getD_lt_of_mem_bound h0 hparameterB
  unfold loadTransition seqs
  run_vcg
  all_goals simp_all [TransitionContext, LoadedTransitionContext]
  all_goals try exact getD_lt_of_mem_bound h0 hparameterB
  all_goals omega

theorem validateTransition_spec (B : Nat) (M : EncodedAutomaton)
    (states lengths outputArray output : List Nat) (depth k symbol tr : Nat)
    (transition : TransitionCode) (base : Nat)
    (h1 : 1 < B) (hsymbolB : symbol < B) (hkB : k < B)
    (hQB : M.2.1 < B) (htsymB : transition.1 < B)
    (hparentB : transition.2.1 < B) (harityB : transition.2.2.length < B) :
    Spec B
      (LoadedTransitionContext M states lengths outputArray output depth k symbol tr
        transition base)
      validateTransition
      (fun _ σ' => ValidatedTransitionContext M states lengths outputArray output
        depth k symbol tr transition base σ') 40 := by
  intro σ hσ
  unfold validateTransition seqs
  run_vcg
  all_goals simp_all [LoadedTransitionContext, ValidatedTransitionContext,
    TransitionContext, TransitionFieldsValid]
  all_goals omega

def ChildrenTransitionContext (M : EncodedAutomaton)
    (states lengths outputArray output : List Nat) (depth k symbol tr : Nat)
    (transition : TransitionCode) (base : Nat) (σ : Env) : Prop :=
  TransitionContext M states lengths outputArray output depth k symbol tr σ ∧
    σ.vars "parent" = transition.2.1 ∧
    σ.vars "valid" =
      if TransitionFieldsValid M transition symbol k ∧
          ChildrenPrefix (encodeAutomaton M) states lengths base depth k
            M.2.2.1.length k then 1 else 0

theorem transitionContext_of_checkChildren_frame
    (M : EncodedAutomaton) (states lengths outputArray output : List Nat)
    (depth k symbol tr : Nat) {σ σ' : Env}
    (hctx : TransitionContext M states lengths outputArray output depth k symbol tr σ)
    (hvars : ∀ y, y ∉ checkChildren.wvars → σ'.vars y = σ.vars y)
    (harrs : ∀ a, a ∉ checkChildren.warrs → σ'.arrs a = σ.arrs a) :
    TransitionContext M states lengths outputArray output depth k symbol tr σ' := by
  rcases hctx with ⟨hP, hS, hL, hO, hrecords, hT, hR, hwidth, hQ, htr,
    hdepth, hk, hsym, hscratch⟩
  exact ⟨(harrs "P" (by decide)).trans hP,
    (harrs "S" (by decide)).trans hS,
    (harrs "L" (by decide)).trans hL,
    (harrs "O" (by decide)).trans hO,
    (hvars "records" (by decide)).trans hrecords,
    (hvars "T" (by decide)).trans hT,
    (hvars "R" (by decide)).trans hR,
    (hvars "width" (by decide)).trans hwidth,
    (hvars "Q" (by decide)).trans hQ,
    (hvars "tr" (by decide)).trans htr,
    (hvars "depth" (by decide)).trans hdepth,
    (hvars "k" (by decide)).trans hk,
    (hvars "sym" (by decide)).trans hsym,
    (hvars "scratchLen" (by decide)).trans hscratch⟩

theorem checkChildren_validated_spec (B : Nat) (M : EncodedAutomaton)
    (states lengths outputArray output : List Nat) (depth k symbol tr : Nat)
    (transition : TransitionCode) (base : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hlengthsB : ∀ v ∈ lengths, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hstatesLenB : states.length < B) (hlengthsLenB : lengths.length < B)
    (hbaseChildren : base + 3 + k ≤ (encodeAutomaton M).length)
    (hkdepth : k ≤ depth) (hdepthRows : depth ≤ lengths.length)
    (hTB : M.2.2.1.length < B) (hdepthB : depth < B) (hkB : k < B)
    (hlenLe : ∀ row < depth, lengths.getD row 0 ≤ M.2.2.1.length)
    (hspan : ∀ j < k, (depth - k + j) * M.2.2.1.length +
      lengths.getD (depth - k + j) 0 ≤ states.length)
    (haddrB : ∀ j < k, (depth - k + j) * M.2.2.1.length +
      lengths.getD (depth - k + j) 0 < B) :
    Spec B
      (ValidatedTransitionContext M states lengths outputArray output depth k symbol tr
        transition base)
      checkChildren
      (fun _ σ' => ChildrenTransitionContext M states lengths outputArray output
        depth k symbol tr transition base σ')
      ((70 * (M.2.2.1.length + 1) + 4) * k + 10) := by
  by_cases hfields : TransitionFieldsValid M transition symbol k
  · have hc0 := checkChildren_spec B (encodeAutomaton M) states lengths base depth k
      M.2.2.1.length h0 h1 hparameterB hstatesB hlengthsB hparameterLenB
      hstatesLenB hlengthsLenB hbaseChildren hkdepth hdepthRows hTB hdepthB hkB
      hlenLe hspan haddrB
    refine hc0.frame.conseq ?_ ?_ le_rfl
    · intro σ hσ
      rcases hσ with ⟨hctx, hbase, htsym, hparent, harity, hvalid⟩
      rcases hctx with ⟨hP, hS, hL, hO, hrecords, hT, hR, hwidth, hQ,
        htr, hdepth, hk, hsym, hscratch⟩
      exact ⟨hP, hS, hL, hbase, hdepth, hk, hT, by simpa [hfields] using hvalid⟩
    · rintro σ σ' hpre ⟨hv, hvars, harrs, _⟩
      rcases hpre with ⟨hctx, _, _, hparent, _, _⟩
      refine ⟨transitionContext_of_checkChildren_frame M states lengths outputArray
        output depth k symbol tr hctx hvars harrs,
        (hvars "parent" (by decide)).trans hparent, ?_⟩
      simpa [hfields] using hv
  · have hd0 := checkChildren_disabled_spec B k h1 hkB
    refine hd0.frame.conseq ?_ ?_ ?_
    · intro σ hσ
      rcases hσ with ⟨hctx, _, _, _, _, hvalid⟩
      rcases hctx with ⟨_, _, _, _, _, _, _, _, _, _, _, hk, _, _⟩
      exact ⟨hk, by simpa [hfields] using hvalid⟩
    · rintro σ σ' hpre ⟨hv, hvars, harrs, _⟩
      rcases hpre with ⟨hctx, _, _, hparent, _, _⟩
      refine ⟨transitionContext_of_checkChildren_frame M states lengths outputArray
        output depth k symbol tr hctx hvars harrs,
        (hvars "parent" (by decide)).trans hparent, ?_⟩
      simp [hfields, hv]
    · have hcoef : 14 ≤ 70 * (M.2.2.1.length + 1) + 4 := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_right k hcoef) 10

theorem appendParent_spec (B : Nat) (M : EncodedAutomaton)
    (states lengths outputArray output : List Nat) (depth k symbol tr : Nat)
    (transition : TransitionCode) (base : Nat)
    (htransitionEq : transition = M.2.2.1.getD tr (0, 0, []))
    (hbaseEq : base = M.1.length + 4 + tr * (maximumRank M.1 + 3))
    (h1 : 1 < B) (hparentB : transition.2.1 < B)
    (hscratchB : output.length < B) (hscratchSuccB : output.length + 1 < B)
    (hscratchO : output.length < outputArray.length)
    (hprefix : PrefixEq outputArray output) :
    Spec B
      (ChildrenTransitionContext M states lengths outputArray output depth k symbol tr
        transition base)
      appendParent
      (fun _ σ' =>
        let output' := output ++ transitionOutputAt M states lengths depth k symbol tr
        σ'.vars "scratchLen" = output'.length ∧ PrefixEq (σ'.arrs "O") output' ∧
          (σ'.arrs "O").length = outputArray.length)
      30 := by
  intro σ hσ
  subst transition
  subst base
  have htotal_iff :
      (TransitionFieldsValid M (M.2.2.1.getD tr (0, 0, [])) symbol k ∧
        ChildrenPrefix (encodeAutomaton M) states lengths
          (M.1.length + 4 + tr * (maximumRank M.1 + 3)) depth k
          M.2.2.1.length k) ↔
        TransitionMatchesAt M states lengths depth k symbol tr := by
    simp [TransitionFieldsValid, TransitionMatchesAt, and_assoc]
  by_cases hmatch : TransitionMatchesAt M states lengths depth k symbol tr
  · have htotal := htotal_iff.mpr hmatch
    unfold appendParent seqs
    run_vcg
    all_goals simp_all [ChildrenTransitionContext, TransitionContext,
      transitionOutputAt, hmatch, htotal]
    all_goals try exact prefixEq_set_append hprefix hscratchO
    all_goals omega
  · have htotal : ¬(TransitionFieldsValid M (M.2.2.1.getD tr (0, 0, [])) symbol k ∧
        ChildrenPrefix (encodeAutomaton M) states lengths
          (M.1.length + 4 + tr * (maximumRank M.1 + 3)) depth k
          M.2.2.1.length k) := fun h => hmatch (htotal_iff.mp h)
    unfold appendParent seqs
    run_vcg
    all_goals simp_all [ChildrenTransitionContext, TransitionContext,
      transitionOutputAt, hmatch, htotal]
    all_goals split_ifs <;> omega

theorem checkTransition_spec (B : Nat) (M : EncodedAutomaton)
    (states lengths outputArray output : List Nat)
    (depth k symbol tr : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hlengthsB : ∀ v ∈ lengths, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hstatesLenB : states.length < B) (hlengthsLenB : lengths.length < B)
    (houtputLen : outputArray.length = M.2.2.1.length)
    (hprefix : PrefixEq outputArray output) (houtTr : output.length ≤ tr)
    (htr : tr < M.2.2.1.length) (hkR : k ≤ maximumRank M.1)
    (hkdepth : k ≤ depth) (hdepthRows : depth ≤ lengths.length)
    (hwidthB : maximumRank M.1 + 3 < B) (hdepthB : depth < B)
    (hkB : k < B) (hsymbolB : symbol < B)
    (hQB : M.2.1 < B) (hTB : M.2.2.1.length < B)
    (hlenLe : ∀ row < depth,
      lengths.getD row 0 ≤ M.2.2.1.length)
    (hspan : ∀ j < k, (depth - k + j) * M.2.2.1.length +
      lengths.getD (depth - k + j) 0 ≤ states.length)
    (haddrB : ∀ j < k, (depth - k + j) * M.2.2.1.length +
      lengths.getD (depth - k + j) 0 < B)
    (hworkB : M.1.length + 4 + tr * (maximumRank M.1 + 3) +
      (maximumRank M.1 + 3) < B) :
    Spec B
      (TransitionContext M states lengths outputArray output depth k symbol tr)
      checkTransition
      (fun _ σ' =>
        let output' := output ++ transitionOutputAt M states lengths depth k symbol tr
        σ'.vars "scratchLen" = output'.length ∧ PrefixEq (σ'.arrs "O") output' ∧
          (σ'.arrs "O").length = outputArray.length)
      ((70 * (M.2.2.1.length + 1) + 4) * k + 150) := by
  intro σ hσ
  let transition := M.2.2.1.getD tr (0, 0, [])
  let base := M.1.length + 4 + tr * (maximumRank M.1 + 3)
  have htransition : transition = M.2.2.1[tr] := by
    dsimp [transition]
    exact List.getD_eq_getElem _ _ htr
  have hsymbol : (encodeAutomaton M).getD base 0 = transition.1 := by
    rw [show base = M.1.length + 4 + tr * (maximumRank M.1 + 3) + 0 by
      simp [base]]
    rw [encodeAutomaton_record M tr 0 htr (by omega)]
    rw [fixedRecord_symbol]
    simp [htransition]
  have hparent : (encodeAutomaton M).getD (base + 1) 0 = transition.2.1 := by
    rw [show base + 1 = M.1.length + 4 + tr * (maximumRank M.1 + 3) + 1 by
      simp [base]]
    rw [encodeAutomaton_record M tr 1 htr (by omega)]
    rw [fixedRecord_parent]
    simp [htransition]
  have harity : (encodeAutomaton M).getD (base + 2) 0 = transition.2.2.length := by
    rw [show base + 2 = M.1.length + 4 + tr * (maximumRank M.1 + 3) + 2 by
      simp [base]]
    rw [encodeAutomaton_record M tr 2 htr (by omega)]
    rw [fixedRecord_arity]
    simp [htransition]
  have hbaseChildren : base + 3 + k ≤ (encodeAutomaton M).length := by
    rw [encodeAutomaton_length]
    dsimp [base]
    have htr' : tr + 1 ≤ M.2.2.1.length := by omega
    calc
      M.1.length + 4 + tr * (maximumRank M.1 + 3) + 3 + k
          ≤ M.1.length + 4 + (tr + 1) * (maximumRank M.1 + 3) := by
            rw [Nat.add_mul]
            omega
      _ ≤ M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_right _ htr') _
      _ ≤ M.1.length + M.2.2.1.length * (maximumRank M.1 + 3) +
          M.2.2.2.length + 5 := by omega
  have hbaseEntries : base + 2 < (encodeAutomaton M).length := by omega
  have hbaseB : base + 2 < B := by
    dsimp [base]
    omega
  have htsymB : transition.1 < B := by
    rw [← hsymbol]
    exact getD_lt_of_mem_bound h0 hparameterB
  have hparentB : transition.2.1 < B := by
    rw [← hparent]
    exact getD_lt_of_mem_bound h0 hparameterB
  have harityB : transition.2.2.length < B := by
    rw [← harity]
    exact getD_lt_of_mem_bound h0 hparameterB
  have hload := loadTransition_spec B M states lengths outputArray output depth k
    symbol tr transition base h0 h1 hparameterB hsymbol hparent harity (by rfl)
    hbaseEntries hbaseB (lt_trans htr hTB) hwidthB
  have hvalidate := validateTransition_spec B M states lengths outputArray output
    depth k symbol tr transition base h1 hsymbolB hkB hQB htsymB hparentB harityB
  have hchildren := checkChildren_validated_spec B M states lengths outputArray output
    depth k symbol tr transition base h0 h1 hparameterB hstatesB hlengthsB
    hparameterLenB hstatesLenB hlengthsLenB hbaseChildren hkdepth hdepthRows hTB
    hdepthB hkB hlenLe hspan haddrB
  have happend := appendParent_spec B M states lengths outputArray output depth k
    symbol tr transition base (by rfl) (by rfl) h1 hparentB (by omega) (by omega)
    (by omega) hprefix
  unfold checkTransition seqs
  run_vcg [hload, hvalidate, hchildren, happend]
  all_goals simp_all [TransitionContext, LoadedTransitionContext,
    ValidatedTransitionContext, ChildrenTransitionContext]
  all_goals omega


end Lax53Proofs.AutomatonRamCorrectness
