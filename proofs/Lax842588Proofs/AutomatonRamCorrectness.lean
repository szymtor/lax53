import Lax865980Proofs.Tactic
import Lax842588Proofs.AutomatonRamProgram
import Lax842588Proofs.AutomatonTableEncoding

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

theorem getD_lt_of_mem_bound {xs : List Nat} {B i : Nat}
    (h0 : 0 < B) (h : ∀ v ∈ xs, v < B) : xs.getD i 0 < B := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem xs 0 hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default xs 0 (Nat.le_of_not_gt hi)]
    exact h0

def HeaderState (M : EncodedAutomaton) (word : CodeString) (σ : Env) : Prop :=
  σ.arrs "P" = encodeAutomaton M ∧ σ.inp = word ∧
  σ.vars "A" = M.1.length ∧ σ.vars "Q" = M.2.1 ∧
  σ.vars "T" = M.2.2.1.length ∧ σ.vars "R" = maximumRank M.1 ∧
  σ.vars "width" = maximumRank M.1 + 3 ∧
  σ.vars "records" = M.1.length + 4 ∧
  σ.vars "acceptBase" =
    M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) ∧
  σ.vars "F" = M.2.2.2.length ∧ σ.vars "n" = word.length

theorem readHeader_spec (B : Nat) (M : EncodedAutomaton) (word : CodeString)
    (h0 : 0 < B) (hparamB : ∀ v ∈ encodeAutomaton M, v < B)
    (hparamLenB : (encodeAutomaton M).length < B)
    (hwordLenB : word.length < B)
    (hworkB : M.1.length + M.2.1 + M.2.2.1.length + maximumRank M.1 +
      M.2.2.1.length * (maximumRank M.1 + 3) + M.2.2.2.length +
        word.length + 20 < B) :
    Spec B
      (fun σ => σ.arrs "P" = encodeAutomaton M ∧
        σ.inp = word.length :: word)
      readHeader
      (fun _ σ' => HeaderState M word σ') 100 := by
  intro σ hσ
  have hget (i : Nat) : (encodeAutomaton M).getD i 0 < B :=
    getD_lt_of_mem_bound h0 hparamB
  have hA := encodeAutomaton_A M
  have hQ := encodeAutomaton_Q M
  have hT := encodeAutomaton_T M
  have hR := encodeAutomaton_R M
  have hF := encodeAutomaton_acceptCount M
  unfold readHeader seqs
  run_vcg
  all_goals
    simp_all [HeaderState, encodeAutomaton_length]
  all_goals try exact hget _
  all_goals omega

def SeenState (states : List Nat) (row width q upto : Nat) : Prop :=
  ∃ z < upto, states.getD (row * width + z) 0 = q

@[simp] theorem not_seenState_zero (states : List Nat) (row width q : Nat) :
    ¬ SeenState states row width q 0 := by
  simp [SeenState]

theorem seenState_succ (states : List Nat) (row width q z : Nat) :
    SeenState states row width q (z + 1) ↔
      SeenState states row width q z ∨
        states.getD (row * width + z) 0 = q := by
  constructor
  · rintro ⟨i, hi, heq⟩
    by_cases hiz : i < z
    · exact Or.inl ⟨i, hiz, heq⟩
    · right
      have : i = z := by omega
      simpa [this] using heq
  · rintro (⟨i, hi, heq⟩ | heq)
    · exact ⟨i, by omega, heq⟩
    · exact ⟨z, by omega, heq⟩

def SearchInv (states : List Nat) (row width q len : Nat) (σ : Env) : Prop :=
  σ.arrs "S" = states ∧ σ.vars "childRow" = row ∧
  σ.vars "T" = width ∧ σ.vars "cq" = q ∧
  σ.vars "childLen" = len ∧ σ.vars "z" ≤ len ∧
  σ.vars "found" = if SeenState states row width q (σ.vars "z") then 1 else 0

theorem searchStateBody_spec (B : Nat) (states : List Nat)
    (row width q len : Nat)
    (h0 : 0 < B) (h1 : 1 < B) (hstatesB : ∀ v ∈ states, v < B)
    (hstatesLenB : states.length < B) (hrowB : row < B)
    (hwidthB : width < B) (hqB : q < B) (hlenB : len < B)
    (hspan : row * width + len ≤ states.length)
    (haddrB : row * width + len < B) :
    Spec B
      (fun σ => SearchInv states row width q len σ ∧ σ.vars "z" < len)
      searchStateBody
      (fun σ σ' => SearchInv states row width q len σ' ∧
        σ'.vars "z" = σ.vars "z" + 1) 40 := by
  intro σ hσ
  have hzaddr : row * width + σ.vars "z" < states.length := by
    omega
  have hstateB : states.getD (row * width + σ.vars "z") 0 < B :=
    getD_lt_of_mem_bound h0 hstatesB
  have hseenSucc : SeenState states row width q (σ.vars "z" + 1) ↔
      SeenState states row width q (σ.vars "z") ∨
        states[row * width + σ.vars "z"] = q := by
    rw [seenState_succ]
    rw [List.getD_eq_getElem states 0 hzaddr]
  unfold searchStateBody seqs
  run_vcg
  all_goals
    simp_all [SearchInv, hseenSucc]
  all_goals try omega
  all_goals aesop

theorem searchStateLoop_spec (B : Nat) (states : List Nat)
    (row width q len : Nat)
    (h0 : 0 < B) (h1 : 1 < B) (hstatesB : ∀ v ∈ states, v < B)
    (hstatesLenB : states.length < B) (hrowB : row < B)
    (hwidthB : width < B) (hqB : q < B) (hlenB : len < B)
    (hspan : row * width + len ≤ states.length)
    (haddrB : row * width + len < B) :
    Spec B (SearchInv states row width q len) searchStateLoop
      (fun _ σ' => SearchInv states row width q len σ' ∧
        σ'.vars "z" = len) (44 * len + 4) := by
  unfold searchStateLoop
  exact Spec.forRange "z" "childLen" (SearchInv states row width q len)
    len 40 (44 * len + 4)
    (by rintro σ ⟨_, _, _, _, hlen, hz, _⟩; omega)
    (by rintro σ ⟨_, _, _, _, hlen, _, _⟩; omega)
    (by rintro _ ⟨_, _, _, _, hlen, _, _⟩; exact hlen)
    (by rintro _ ⟨_, _, _, _, _, hz, _⟩; exact hz)
    (searchStateBody_spec B states row width q len h0 h1 hstatesB hstatesLenB
      hrowB hwidthB hqB hlenB hspan haddrB)
    (fun _ hσ => hσ)
    (fun _ _ => by omega)

def ChildPresent (states lengths : List Nat) (depth k width j q : Nat) : Prop :=
  let row := depth - k + j
  SeenState states row width q (lengths.getD row 0)

theorem searchChild_spec (B : Nat) (parameter states lengths : List Nat)
    (base depth k width j : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ parameter, v < B)
    (hstatesB : ∀ v ∈ states, v < B) (hlengthsB : ∀ v ∈ lengths, v < B)
    (hparameterLenB : parameter.length < B) (hstatesLenB : states.length < B)
    (hlengthsLenB : lengths.length < B)
    (hbase : base + 3 + j < parameter.length)
    (hrow : depth - k + j < lengths.length)
    (hwidthB : width < B) (hdepthB : depth < B) (hkB : k < B)
    (hjB : j < B)
    (hspan : (depth - k + j) * width +
        lengths.getD (depth - k + j) 0 ≤ states.length)
    (haddrB : (depth - k + j) * width +
        lengths.getD (depth - k + j) 0 < B) :
    Spec B
      (fun σ => σ.arrs "P" = parameter ∧ σ.arrs "S" = states ∧
        σ.arrs "L" = lengths ∧ σ.vars "base" = base ∧
        σ.vars "depth" = depth ∧ σ.vars "k" = k ∧
        σ.vars "T" = width ∧ σ.vars "j" = j ∧ σ.vars "valid" = 1)
      searchChild
      (fun _ σ' => σ'.vars "valid" =
        if ChildPresent states lengths depth k width j
          (parameter.getD (base + 3 + j) 0) then 1 else 0)
      (60 * (lengths.getD (depth - k + j) 0 + 1)) := by
  intro σ hσ
  let row := depth - k + j
  let q := parameter.getD (base + 3 + j) 0
  let len := lengths.getD row 0
  have hqB : q < B := getD_lt_of_mem_bound h0 hparameterB
  have hlenB : len < B := getD_lt_of_mem_bound h0 hlengthsB
  have hrowB : row < B := by dsimp [row]; omega
  have hloop0 := searchStateLoop_spec B states row width q len h0 h1 hstatesB
    hstatesLenB hrowB hwidthB hqB hlenB hspan haddrB
  have hloop : Spec B (SearchInv states row width q len) searchStateLoop
      (fun τ τ' => (SearchInv states row width q len τ' ∧
        τ'.vars "z" = len) ∧ τ'.vars "valid" = τ.vars "valid")
      (44 * len + 4) := hloop0.frame.post (by
    rintro τ τ' _ ⟨hq', hvars, _⟩
    exact ⟨hq', hvars "valid" (by decide)⟩)
  dsimp [len, row] at hloop
  unfold searchChild seqs
  run_vcg [hloop]
  all_goals simp_all [SearchInv, ChildPresent, row, q, len]
  all_goals try exact getD_lt_of_mem_bound h0 hparameterB
  all_goals try exact getD_lt_of_mem_bound h0 hlengthsB
  all_goals aesop
  all_goals omega

def ChildrenPrefix (parameter states lengths : List Nat)
    (base depth k width upto : Nat) : Prop :=
  ∀ j < upto, ChildPresent states lengths depth k width j
    (parameter.getD (base + 3 + j) 0)

theorem childrenPrefix_succ (parameter states lengths : List Nat)
    (base depth k width j : Nat) :
    ChildrenPrefix parameter states lengths base depth k width (j + 1) ↔
      ChildrenPrefix parameter states lengths base depth k width j ∧
        ChildPresent states lengths depth k width j
          (parameter.getD (base + 3 + j) 0) := by
  constructor
  · intro h
    refine ⟨fun i hi => h i (by omega), h j (by omega)⟩
  · rintro ⟨h, hj⟩ i hi
    by_cases hij : i < j
    · exact h i hij
    · have : i = j := by omega
      simpa [this] using hj

def CheckChildrenInv (parameter states lengths : List Nat)
    (base depth k width : Nat) (σ : Env) : Prop :=
  σ.arrs "P" = parameter ∧ σ.arrs "S" = states ∧
  σ.arrs "L" = lengths ∧ σ.vars "base" = base ∧
  σ.vars "depth" = depth ∧ σ.vars "k" = k ∧
  σ.vars "T" = width ∧ σ.vars "j" ≤ k ∧
  σ.vars "valid" =
    if ChildrenPrefix parameter states lengths base depth k width
      (σ.vars "j") then 1 else 0

theorem checkChildrenBody_spec (B : Nat)
    (parameter states lengths : List Nat) (base depth k width : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ parameter, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hlengthsB : ∀ v ∈ lengths, v < B)
    (hparameterLenB : parameter.length < B) (hstatesLenB : states.length < B)
    (hlengthsLenB : lengths.length < B)
    (hbase : base + 3 + k ≤ parameter.length)
    (hkdepth : k ≤ depth) (hdepthRows : depth ≤ lengths.length)
    (hwidthB : width < B) (hdepthB : depth < B) (hkB : k < B)
    (hlenLe : ∀ row < depth, lengths.getD row 0 ≤ width)
    (hspan : ∀ j < k, (depth - k + j) * width +
      lengths.getD (depth - k + j) 0 ≤ states.length)
    (haddrB : ∀ j < k, (depth - k + j) * width +
      lengths.getD (depth - k + j) 0 < B) :
    Spec B
      (fun σ => CheckChildrenInv parameter states lengths base depth k width σ ∧
        σ.vars "j" < k)
      checkChildrenBody
      (fun σ σ' => CheckChildrenInv parameter states lengths base depth k width σ' ∧
        σ'.vars "j" = σ.vars "j" + 1)
      (70 * (width + 1)) := by
  intro σ hσ
  let j := σ.vars "j"
  have hj : j < k := hσ.2
  have hrow : depth - k + j < lengths.length := by omega
  have hrowDepth : depth - k + j < depth := by omega
  have hchildLen : lengths.getD (depth - k + j) 0 ≤ width :=
    hlenLe _ hrowDepth
  have hs0 := searchChild_spec B parameter states lengths base depth k width j
    h0 h1 hparameterB hstatesB hlengthsB hparameterLenB hstatesLenB
    hlengthsLenB (by omega) hrow hwidthB hdepthB hkB (by dsimp [j]; omega)
    (hspan j hj) (haddrB j hj)
  have hsbase : Spec B
      (fun τ => τ.arrs "P" = parameter ∧ τ.arrs "S" = states ∧
        τ.arrs "L" = lengths ∧ τ.vars "base" = base ∧
        τ.vars "depth" = depth ∧ τ.vars "k" = k ∧
        τ.vars "T" = width ∧ τ.vars "j" = j ∧ τ.vars "valid" = 1)
      searchChild
      (fun τ τ' => τ'.vars "valid" =
          (if ChildPresent states lengths depth k width j
            (parameter.getD (base + 3 + j) 0) then 1 else 0) ∧
        τ'.arrs "P" = parameter ∧ τ'.arrs "S" = states ∧
        τ'.arrs "L" = lengths ∧ τ'.vars "base" = base ∧
        τ'.vars "depth" = depth ∧ τ'.vars "k" = k ∧
        τ'.vars "T" = width ∧ τ'.vars "j" = j)
      (60 * (lengths.getD (depth - k + j) 0 + 1)) := hs0.frame.post (by
    rintro τ τ' hpre ⟨hv, hvars, harrs, _⟩
    refine ⟨hv, (harrs "P" (by decide)).trans hpre.1,
      (harrs "S" (by decide)).trans hpre.2.1,
      (harrs "L" (by decide)).trans hpre.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hvars "base" (by decide)).trans hpre.2.2.2.1
    · exact (hvars "depth" (by decide)).trans hpre.2.2.2.2.1
    · exact (hvars "k" (by decide)).trans hpre.2.2.2.2.2.1
    · exact (hvars "T" (by decide)).trans hpre.2.2.2.2.2.2.1
    · exact (hvars "j" (by decide)).trans hpre.2.2.2.2.2.2.2.1)
  have hs : Spec B
      (fun τ => τ.arrs "P" = parameter ∧ τ.arrs "S" = states ∧
        τ.arrs "L" = lengths ∧ τ.vars "base" = base ∧
        τ.vars "depth" = depth ∧ τ.vars "k" = k ∧
        τ.vars "T" = width ∧ τ.vars "j" = j ∧ τ.vars "valid" = 1)
      searchChild
      (fun τ τ' => τ'.vars "valid" =
          (if ChildPresent states lengths depth k width j
            (parameter.getD (base + 3 + j) 0) then 1 else 0) ∧
        τ'.arrs "P" = parameter ∧ τ'.arrs "S" = states ∧
        τ'.arrs "L" = lengths ∧ τ'.vars "base" = base ∧
        τ'.vars "depth" = depth ∧ τ'.vars "k" = k ∧
        τ'.vars "T" = width ∧ τ'.vars "j" = j)
      (60 * (width + 1)) := hsbase.mono (by omega)
  unfold checkChildrenBody seqs
  run_vcg [hs]
  all_goals simp_all [CheckChildrenInv, childrenPrefix_succ, j]
  all_goals aesop
  all_goals omega

theorem checkChildrenLoop_spec (B : Nat)
    (parameter states lengths : List Nat) (base depth k width : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ parameter, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hlengthsB : ∀ v ∈ lengths, v < B)
    (hparameterLenB : parameter.length < B) (hstatesLenB : states.length < B)
    (hlengthsLenB : lengths.length < B)
    (hbase : base + 3 + k ≤ parameter.length)
    (hkdepth : k ≤ depth) (hdepthRows : depth ≤ lengths.length)
    (hwidthB : width < B) (hdepthB : depth < B) (hkB : k < B)
    (hlenLe : ∀ row < depth, lengths.getD row 0 ≤ width)
    (hspan : ∀ j < k, (depth - k + j) * width +
      lengths.getD (depth - k + j) 0 ≤ states.length)
    (haddrB : ∀ j < k, (depth - k + j) * width +
      lengths.getD (depth - k + j) 0 < B) :
    Spec B (CheckChildrenInv parameter states lengths base depth k width)
      checkChildrenLoop
      (fun _ σ' => CheckChildrenInv parameter states lengths base depth k width σ' ∧
        σ'.vars "j" = k)
      ((70 * (width + 1) + 4) * k + 4) := by
  unfold checkChildrenLoop
  exact Spec.forRange "j" "k"
    (CheckChildrenInv parameter states lengths base depth k width)
    k (70 * (width + 1)) ((70 * (width + 1) + 4) * k + 4)
    (by rintro σ ⟨_, _, _, _, _, _, _, hj, _⟩; omega)
    (by rintro σ ⟨_, _, _, _, _, hk, _, _, _⟩; omega)
    (by rintro _ ⟨_, _, _, _, _, hk, _, _, _⟩; exact hk)
    (by rintro _ ⟨_, _, _, _, _, _, _, hj, _⟩; exact hj)
    (checkChildrenBody_spec B parameter states lengths base depth k width
      h0 h1 hparameterB hstatesB hlengthsB hparameterLenB hstatesLenB
      hlengthsLenB hbase hkdepth hdepthRows hwidthB hdepthB hkB hlenLe hspan haddrB)
    (fun _ hσ => hσ)
    (fun _ _ => Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)

theorem checkChildren_spec (B : Nat)
    (parameter states lengths : List Nat) (base depth k width : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ parameter, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hlengthsB : ∀ v ∈ lengths, v < B)
    (hparameterLenB : parameter.length < B) (hstatesLenB : states.length < B)
    (hlengthsLenB : lengths.length < B)
    (hbase : base + 3 + k ≤ parameter.length)
    (hkdepth : k ≤ depth) (hdepthRows : depth ≤ lengths.length)
    (hwidthB : width < B) (hdepthB : depth < B) (hkB : k < B)
    (hlenLe : ∀ row < depth, lengths.getD row 0 ≤ width)
    (hspan : ∀ j < k, (depth - k + j) * width +
      lengths.getD (depth - k + j) 0 ≤ states.length)
    (haddrB : ∀ j < k, (depth - k + j) * width +
      lengths.getD (depth - k + j) 0 < B) :
    Spec B
      (fun σ => σ.arrs "P" = parameter ∧ σ.arrs "S" = states ∧
        σ.arrs "L" = lengths ∧ σ.vars "base" = base ∧
        σ.vars "depth" = depth ∧ σ.vars "k" = k ∧
        σ.vars "T" = width ∧ σ.vars "valid" = 1)
      checkChildren
      (fun _ σ' => σ'.vars "valid" =
        if ChildrenPrefix parameter states lengths base depth k width k then 1 else 0)
      ((70 * (width + 1) + 4) * k + 10) := by
  intro σ hσ
  have hloop := checkChildrenLoop_spec B parameter states lengths base depth k width
    h0 h1 hparameterB hstatesB hlengthsB hparameterLenB hstatesLenB
    hlengthsLenB hbase hkdepth hdepthRows hwidthB hdepthB hkB hlenLe hspan haddrB
  unfold checkChildren seqs
  run_vcg [hloop]
  all_goals simp_all [CheckChildrenInv, ChildrenPrefix]
  all_goals aesop
  all_goals omega

def CheckChildrenDisabledInv (k : Nat) (σ : Env) : Prop :=
  σ.vars "k" = k ∧ σ.vars "j" ≤ k ∧ σ.vars "valid" = 0

theorem checkChildrenDisabledBody_spec (B k : Nat)
    (h1 : 1 < B) (hkB : k < B) :
    Spec B
      (fun σ => CheckChildrenDisabledInv k σ ∧ σ.vars "j" < k)
      checkChildrenBody
      (fun σ σ' => CheckChildrenDisabledInv k σ' ∧
        σ'.vars "j" = σ.vars "j" + 1)
      10 := by
  intro σ hσ
  simp only [CheckChildrenDisabledInv] at hσ
  have himpossible : Spec B
      (fun τ => (CheckChildrenDisabledInv k τ ∧ τ.vars "j" < k) ∧
        (Cond.eq (.var "valid") (.lit 1)).evalB B τ = some true)
      searchChild (fun _ _ => False) 0 := by
    intro τ hτ
    have : False := by
      simp [CheckChildrenDisabledInv] at hτ
      omega
    exact this.elim
  unfold checkChildrenBody seqs
  run_vcg [himpossible]
  all_goals simp_all [CheckChildrenDisabledInv]
  all_goals omega

theorem checkChildrenDisabledLoop_spec (B k : Nat)
    (h1 : 1 < B) (hkB : k < B) :
    Spec B (CheckChildrenDisabledInv k) checkChildrenLoop
      (fun _ σ' => CheckChildrenDisabledInv k σ' ∧ σ'.vars "j" = k)
      (14 * k + 4) := by
  unfold checkChildrenLoop
  exact Spec.forRange "j" "k" (CheckChildrenDisabledInv k)
    k 10 (14 * k + 4)
    (by rintro σ ⟨hk, hj, _⟩; omega)
    (by rintro σ ⟨hk, _, _⟩; omega)
    (by rintro _ ⟨hk, _, _⟩; exact hk)
    (by rintro _ ⟨_, hj, _⟩; exact hj)
    (checkChildrenDisabledBody_spec B k h1 hkB)
    (fun _ hσ => hσ)
    (fun _ _ => by omega)

/-- Once an earlier record check has failed, child checking only advances its
loop counter and leaves `valid` equal to zero. Keeping this as a separate spec
prevents symbolic execution from unfolding the child-state search in every
failed-validation branch of `checkTransition`. -/
theorem checkChildren_disabled_spec (B k : Nat)
    (h1 : 1 < B) (hkB : k < B) :
    Spec B
      (fun σ => σ.vars "k" = k ∧ σ.vars "valid" = 0)
      checkChildren
      (fun _ σ' => σ'.vars "valid" = 0)
      (14 * k + 10) := by
  intro σ hσ
  have hloop := checkChildrenDisabledLoop_spec B k h1 hkB
  unfold checkChildren seqs
  run_vcg [hloop]
  all_goals simp_all [CheckChildrenDisabledInv]
  all_goals omega

/-- The marshalling phase copies exactly the self-delimiting parameter block
and leaves the tree block on the input tape. -/
theorem readParameter_spec (B : Nat) (parameter rest : List Nat)
    (hlenB : parameter.length < B) (hvaluesB : ∀ v ∈ parameter, v < B) :
    Spec B
      (fun σ =>
        (σ.arrs "P").length = parameter.length ∧
        σ.inp = parameter.length :: (parameter ++ rest))
      readParameter
      (fun _ σ' =>
        σ'.arrs "P" = parameter ∧ σ'.inp = rest ∧
        σ'.vars "i" = parameter.length)
      (1 + (12 * parameter.length + 6)) := by
  unfold readParameter
  refine Spec.seq
    (Spec.read (x := "plen") (v := fun _ => parameter.length)
      (rest := fun _ => parameter ++ rest) ?_)
    (readArr_spec B "P" "i" "plen" "v" parameter rest
      (by decide) (by decide) (by decide) hlenB hvaluesB)
    ?_ ?_
  · intro σ hσ
    exact hσ.2
  · intro σ σ' hσ hq
    subst σ'
    refine ⟨?_, ?_, ?_⟩
    · exact hσ.1
    · simp [vars_setVar]
    · rfl
  · intro σ σ' σ'' hσ hq hq'
    exact hq'

end Lax842588Proofs.AutomatonRamCorrectness
