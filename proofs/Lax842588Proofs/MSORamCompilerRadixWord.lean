import Lax842588Proofs.FiniteAutomatonEncoding
import Lax842588Proofs.MSORamCompilerProgram
import Lax842588Proofs.MSORamCompilerTransition

/-!
Charged arithmetic materialization of canonical child-state rows in an
arbitrary positive radix.  The initial divisor is itself computed by an
IMP+ multiplication loop, so neither the row enumeration nor powers of the
state count are supplied to the machine as advice.
-/

namespace Lax842588Proofs.MSORamCompilerRadixWord

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.FiniteAutomatonEncoding
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.MSORamCompilerHeap
open Lax842588Proofs.MSORamCompilerProgram
open Lax842588Proofs.MSORamCompilerStorage
open Lax842588Proofs.MSORamCompilerTransition

def RadixWordReady (B base length state maximumRank : Nat)
    (sigma : Env) : Prop :=
  sigma.vars "radixBase" = base ∧
    sigma.vars "radixLength" = length ∧
    sigma.vars "radixState" = state ∧
    0 < base ∧ base < B ∧
    state < base ^ length ∧ base ^ length < B ∧
    length < B ∧
    length ≤ (sigma.arrs "NewTransitionChildren").length ∧
    (sigma.arrs "NewTransitionChildren").length < B ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    length ≤ maximumRank ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank ∧
    maximumRank < B

def RadixPowerInv (B base length state maximumRank : Nat)
    (sigma : Env) : Prop :=
  let powerIndex := sigma.vars "radixPowerIndex"
  RadixWordReady B base length state maximumRank sigma ∧
    sigma.vars "radixIndex" = 0 ∧
    sigma.vars "radixRemainder" = state ∧
    sigma.vars "radixPowerLimit" = length - 1 ∧
    powerIndex ≤ length - 1 ∧
    sigma.vars "radixDivisor" = base ^ powerIndex ∧
    powerIndex < B ∧
    sigma.vars "radixDivisor" < B

theorem initializeRadixWord_spec (B base length state maximumRank : Nat) :
    Spec B (RadixWordReady B base length state maximumRank)
      initializeRadixWord
      (fun _ sigma' => RadixPowerInv B base length state maximumRank sigma')
      60 := by
  intro sigma hready
  rcases hready with ⟨hbase, hlength, hstateVar, hbasePos, hbaseB,
    hstate, hpowerB, hlengthB, hspace, harrayB, hmaximumRank,
    hlengthMaximumRank, hmaximumRankSpace, hmaximumRankB⟩
  have honeB : 1 < B := by
    have hpowerPos : 0 < base ^ length := pow_pos hbasePos _
    omega
  have hzeroB : 0 < B := by omega
  unfold initializeRadixWord Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [RadixPowerInv, RadixWordReady]

theorem radixPowerBody_spec (B base length state maximumRank : Nat) :
    Spec B
      (fun sigma => RadixPowerInv B base length state maximumRank sigma ∧
        sigma.vars "radixPowerIndex" < length - 1)
      radixPowerBody
      (fun sigma sigma' =>
        RadixPowerInv B base length state maximumRank sigma' ∧
          sigma'.vars "radixPowerIndex" =
            sigma.vars "radixPowerIndex" + 1)
      50 := by
  intro sigma hpre
  rcases hpre with ⟨hinv, hindexLt⟩
  simp only [RadixPowerInv] at hinv
  rcases hinv with ⟨hready, hwordIndex, hremainder, hlimit,
    hindexLe, hdivisor, hindexB, hdivisorB⟩
  have hnextLe : sigma.vars "radixPowerIndex" + 1 ≤ length - 1 := by
    omega
  have hnextExponentLe : sigma.vars "radixPowerIndex" + 1 ≤ length := by
    omega
  have hproductEq :
      sigma.vars "radixDivisor" * sigma.vars "radixBase" =
        base ^ (sigma.vars "radixPowerIndex" + 1) := by
    rw [hdivisor, hready.1]
    simp [pow_succ]
  have hproductB :
      sigma.vars "radixDivisor" * sigma.vars "radixBase" < B := by
    rw [hproductEq]
    exact lt_of_le_of_lt
      (Nat.pow_le_pow_right hready.2.2.2.1 hnextExponentLe)
      hready.2.2.2.2.2.2.1
  have hnextIndexB : sigma.vars "radixPowerIndex" + 1 < B := by
    have hlengthB := hready.2.2.2.2.2.2.2.1
    omega
  unfold radixPowerBody Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [RadixPowerInv, RadixWordReady]

def radixPowerLoopCost (length : Nat) : Nat :=
  54 * (length - 1) + 4

theorem radixPowerLoop_spec (B base length state maximumRank : Nat) :
    Spec B (RadixPowerInv B base length state maximumRank) radixPowerLoop
      (fun _ sigma' =>
        RadixPowerInv B base length state maximumRank sigma' ∧
          sigma'.vars "radixPowerIndex" = length - 1)
      (radixPowerLoopCost length) := by
  unfold radixPowerLoop
  exact Spec.forRange "radixPowerIndex" "radixPowerLimit"
    (RadixPowerInv B base length state maximumRank) (length - 1) 50
      (radixPowerLoopCost length)
    (by
      intro sigma hinv
      exact hinv.2.2.2.2.2.2.1)
    (by
      intro sigma hinv
      rw [hinv.2.2.2.1]
      exact lt_of_le_of_lt (Nat.sub_le length 1)
        hinv.1.2.2.2.2.2.2.2.1)
    (by intro _ hinv; exact hinv.2.2.2.1)
    (by intro _ hinv; exact hinv.2.2.2.2.1)
    (radixPowerBody_spec B base length state maximumRank)
    (fun _ h => h)
    (by
      intro sigma _
      unfold radixPowerLoopCost
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 54
          (Nat.sub_le (length - 1)
            (sigma.vars "radixPowerIndex"))) 4)

def beginRadixWordCost (length : Nat) : Nat :=
  60 + radixPowerLoopCost length

theorem beginRadixWord_spec (B base length state maximumRank : Nat) :
    Spec B (RadixWordReady B base length state maximumRank) beginRadixWord
      (fun _ sigma' =>
        RadixPowerInv B base length state maximumRank sigma' ∧
          sigma'.vars "radixPowerIndex" = length - 1)
      (beginRadixWordCost length) := by
  unfold beginRadixWord beginRadixWordCost
  exact Spec.seq (initializeRadixWord_spec B base length state maximumRank)
    (radixPowerLoop_spec B base length state maximumRank)
    (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

def RadixWordInv (B base length state maximumRank : Nat)
    (sigma : Env) : Prop :=
  let index := sigma.vars "radixIndex"
  index ≤ length ∧
    sigma.vars "radixBase" = base ∧
    sigma.vars "radixLength" = length ∧
    sigma.vars "radixState" = state ∧
    0 < base ∧ base < B ∧
    state < base ^ length ∧ base ^ length < B ∧
    length < B ∧
    length ≤ (sigma.arrs "NewTransitionChildren").length ∧
    (sigma.arrs "NewTransitionChildren").length < B ∧
    WordsAt (sigma.arrs "NewTransitionChildren") 0
      ((radixWord base length state).take index) ∧
    (radixWord base length state).drop index =
      radixWord base (length - index) (sigma.vars "radixRemainder") ∧
    sigma.vars "radixRemainder" < B ∧
    sigma.vars "radixDivisor" < B ∧
    (index < length → sigma.vars "radixDivisor" =
      base ^ (length - index - 1)) ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    length ≤ maximumRank ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank ∧
    maximumRank < B

theorem radixPowerInv_to_wordInv
    {B base length state maximumRank : Nat} {sigma : Env}
    (hinv : RadixPowerInv B base length state maximumRank sigma)
    (hdone : sigma.vars "radixPowerIndex" = length - 1) :
    RadixWordInv B base length state maximumRank sigma := by
  simp only [RadixPowerInv] at hinv
  rcases hinv with ⟨hready, hindex, hremainder, _, _, hdivisor,
    _, hdivisorB⟩
  rcases hready with ⟨hbase, hlength, hstateVar, hbasePos, hbaseB,
    hstate, hpowerB, hlengthB, hspace, harrayB, hmaximumRank,
    hlengthMaximumRank, hmaximumRankSpace, hmaximumRankB⟩
  have hstateB : state < B := lt_trans hstate hpowerB
  simp only [RadixWordInv]
  refine ⟨by simp [hindex], hbase, hlength, hstateVar, hbasePos, hbaseB,
    hstate, hpowerB, hlengthB, hspace, harrayB, ?_, ?_, ?_, hdivisorB,
    ?_, hmaximumRank, hlengthMaximumRank, hmaximumRankSpace,
    hmaximumRankB⟩
  · simp [hindex, WordsAt]
  · simp [hindex, hremainder]
  · simpa [hremainder] using hstateB
  · intro _
    rw [hindex, hdivisor, hdone]
    simp

theorem radixWordBody_spec (B base length state maximumRank : Nat) :
    Spec B
      (fun sigma => RadixWordInv B base length state maximumRank sigma ∧
        sigma.vars "radixIndex" < length)
      radixWordBody
      (fun sigma sigma' =>
        RadixWordInv B base length state maximumRank sigma' ∧
          sigma'.vars "radixIndex" = sigma.vars "radixIndex" + 1)
      100 := by
  intro sigma hready
  rcases hready with ⟨hinv, hindexLt⟩
  simp only [RadixWordInv] at hinv
  rcases hinv with ⟨hindexLe, hbaseVar, hlengthVar, hstateVar,
    hbasePos, hbaseB, hstate, hpowerB, hlengthB, hspace, harrayB,
    hwords, hsuffix, hremainderB, hdivisorB, hdivisor,
    hmaximumRank, hlengthMaximumRank, hmaximumRankSpace,
    hmaximumRankB⟩
  let index := sigma.vars "radixIndex"
  let remainder := sigma.vars "radixRemainder"
  let target := radixWord base length state
  have htargetLength : target.length = length := by simp [target]
  have htargetIndex : index < target.length := by
    simpa [index, htargetLength] using hindexLt
  have hremainingPos : 0 < length - index := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hremainingPos)
  have hdivisorEq : sigma.vars "radixDivisor" = base ^ k := by
    rw [hdivisor hindexLt, hk]
    simp
  have hsuffix' : target.drop index = radixWord base (k + 1) remainder := by
    simpa [target, index, remainder, hk] using hsuffix
  rw [List.drop_eq_getElem_cons htargetIndex] at hsuffix'
  simp only [radixWord] at hsuffix'
  have hdigit : target[index] = remainder / base ^ k :=
    List.cons.inj hsuffix' |>.1
  have htail : target.drop (index + 1) =
      radixWord base k (remainder % base ^ k) :=
    List.cons.inj hsuffix' |>.2
  have hdigitBase : target[index] < base := by
    exact radixWord_value_lt hstate (List.getElem_mem _)
  have hdigitB : remainder / base ^ k < B := by
    rw [← hdigit]
    exact lt_trans hdigitBase hbaseB
  have hslot : index < (sigma.arrs "NewTransitionChildren").length := by
    omega
  have hprefixLength : (target.take index).length = index := by
    rw [List.length_take, htargetLength, Nat.min_eq_left hindexLe]
  have hwordsTarget : WordsAt (sigma.arrs "NewTransitionChildren") 0
      (target.take index) := by
    simpa [target, index] using hwords
  have hwords' := wordsAt_set_append
    (value := remainder / base ^ k) hwordsTarget (by
      simpa [hprefixLength] using hslot)
  have htake : target.take (index + 1) =
      target.take index ++ [remainder / base ^ k] := by
    rw [List.take_succ_eq_append_getElem htargetIndex, hdigit]
  have hwordsNext : WordsAt
      ((sigma.arrs "NewTransitionChildren").set index
        (remainder / base ^ k)) 0 (target.take (index + 1)) := by
    simpa [hprefixLength, htake] using hwords'
  have hremainderEq :
      remainder - base ^ k * (remainder / base ^ k) =
        remainder % base ^ k := by
    exact Nat.mod_eq_sub_mul_div.symm
  have hremainderNextB :
      remainder - base ^ k * (remainder / base ^ k) < B :=
    lt_of_le_of_lt (Nat.sub_le remainder _) hremainderB
  have hproductB : base ^ k * (remainder / base ^ k) < B :=
    lt_of_le_of_lt (Nat.mul_div_le remainder (base ^ k)) hremainderB
  have hdivisorNextB : base ^ k / base < B :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by
      simpa [hdivisorEq] using hdivisorB)
  have hsuffixNext : target.drop (index + 1) =
      radixWord base (length - (index + 1))
        (remainder - base ^ k * (remainder / base ^ k)) := by
    rw [hremainderEq]
    have hlenNext : length - (index + 1) = k := by omega
    rw [hlenNext]
    exact htail
  have hdivisorNext : index + 1 < length →
      base ^ k / base = base ^ (length - (index + 1) - 1) := by
    intro hnext
    have hkpos : 0 < k := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hkpos)
    have hlen : length - (index + 1) - 1 = j := by omega
    rw [hlen, pow_succ]
    simpa [Nat.mul_comm] using Nat.mul_div_right (base ^ j) hbasePos
  unfold radixWordBody Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [RadixWordInv, index, remainder, target]

def radixWordLoopCost (length : Nat) : Nat := 104 * length + 4

theorem radixWordLoop_spec (B base length state maximumRank : Nat) :
    Spec B (RadixWordInv B base length state maximumRank) radixWordLoop
      (fun _ sigma' =>
        RadixWordInv B base length state maximumRank sigma' ∧
          sigma'.vars "radixIndex" = length)
      (radixWordLoopCost length) := by
  unfold radixWordLoop
  exact Spec.forRange "radixIndex" "radixLength"
    (RadixWordInv B base length state maximumRank) length 100
      (radixWordLoopCost length)
    (by
      intro _ hinv
      rcases hinv with ⟨hindex, _, _, _, _, _, _, _, hlengthB, -⟩
      omega)
    (by
      intro _ hinv
      rcases hinv with ⟨_, _, hlength, _, _, _, _, _, hlengthB, -⟩
      rw [hlength]
      exact hlengthB)
    (by intro _ hinv; exact hinv.2.2.1)
    (by intro _ hinv; exact hinv.1)
    (radixWordBody_spec B base length state maximumRank)
    (fun _ h => h)
    (by
      intro sigma _
      unfold radixWordLoopCost
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 104
          (Nat.sub_le length (sigma.vars "radixIndex"))) 4)

def prepareRadixWordCost (length : Nat) : Nat :=
  beginRadixWordCost length + radixWordLoopCost length

theorem prepareRadixWord_spec (B base length state maximumRank : Nat) :
    Spec B (RadixWordReady B base length state maximumRank) prepareRadixWord
      (fun _ sigma' =>
        RadixWordInv B base length state maximumRank sigma' ∧
          sigma'.vars "radixIndex" = length)
      (prepareRadixWordCost length) := by
  unfold prepareRadixWord prepareRadixWordCost
  refine Spec.seq (beginRadixWord_spec B base length state maximumRank)
    (radixWordLoop_spec B base length state maximumRank) ?_ ?_
  · intro _ _ _ h
    exact radixPowerInv_to_wordInv h.1 h.2
  · intro _ _ _ _ _ h
    exact h

theorem radixWordInv_complete
    {B base length state maximumRank : Nat} {sigma : Env}
    (hinv : RadixWordInv B base length state maximumRank sigma)
    (hdone : sigma.vars "radixIndex" = length) :
    WordsAt (sigma.arrs "NewTransitionChildren") 0
      (radixWord base length state) := by
  have hwords := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hdone] at hwords
  have htake : (radixWord base length state).take length =
      radixWord base length state := by
    simp
  rw [htake] at hwords
  exact hwords

def paddedRadixWord (maximumRank base length state : Nat) : List Nat :=
  radixWord base length state ++ List.replicate (maximumRank - length) 0

@[simp] theorem paddedRadixWord_length
    {maximumRank base length state : Nat} (hlength : length ≤ maximumRank) :
    (paddedRadixWord maximumRank base length state).length = maximumRank := by
  simp [paddedRadixWord]
  omega

private theorem replicate_succ_eq_append (n value : Nat) :
    List.replicate (n + 1) value = List.replicate n value ++ [value] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        List.replicate (n + 1 + 1) value =
            value :: List.replicate (n + 1) value := List.replicate_succ
        _ = value :: (List.replicate n value ++ [value]) := by rw [ih]
        _ = List.replicate (n + 1) value ++ [value] := by
          rw [List.replicate_succ]
          rfl

def RadixPaddingInv (B base length state maximumRank : Nat)
    (sigma : Env) : Prop :=
  let index := sigma.vars "radixIndex"
  length ≤ index ∧ index ≤ maximumRank ∧
    sigma.vars "radixBase" = base ∧
    sigma.vars "radixLength" = length ∧
    sigma.vars "radixState" = state ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    length ≤ maximumRank ∧
    (sigma.arrs "NewTransitionChildren").length = maximumRank ∧
    maximumRank < B ∧
    WordsAt (sigma.arrs "NewTransitionChildren") 0
      (radixWord base length state ++
        List.replicate (index - length) 0)

theorem radixWordInv_to_padding
    {B base length state maximumRank : Nat} {sigma : Env}
    (hinv : RadixWordInv B base length state maximumRank sigma)
    (hdone : sigma.vars "radixIndex" = length) :
    RadixPaddingInv B base length state maximumRank sigma := by
  have hwords := radixWordInv_complete hinv hdone
  simp only [RadixWordInv] at hinv
  rcases hinv with ⟨_, hbase, hlength, hstate, _, _, _, _, _, _, _, _,
    _, _, _, _, hmaximumRank, hlengthMaximumRank, harrayLength,
    hmaximumRankB⟩
  simp [RadixPaddingInv, hdone, hbase, hlength, hstate, hmaximumRank,
    hlengthMaximumRank, harrayLength, hmaximumRankB, hwords]

theorem radixPaddingBody_spec (B base length state maximumRank : Nat) :
    Spec B
      (fun sigma => RadixPaddingInv B base length state maximumRank sigma ∧
        sigma.vars "radixIndex" < maximumRank)
      radixPaddingBody
      (fun sigma sigma' =>
        RadixPaddingInv B base length state maximumRank sigma' ∧
          sigma'.vars "radixIndex" = sigma.vars "radixIndex" + 1)
      30 := by
  intro sigma hready
  rcases hready with ⟨hinv, hindexLt⟩
  simp only [RadixPaddingInv] at hinv
  rcases hinv with ⟨hlengthIndex, hindexMaximumRank, hbase,
    hlength, hstate, hmaximumRank, hlengthMaximumRank, harrayLength,
    hmaximumRankB, hwords⟩
  let index := sigma.vars "radixIndex"
  have hindexB : index < B := by omega
  have hzeroB : 0 < B := by omega
  have hslot : index < (sigma.arrs "NewTransitionChildren").length := by
    simpa [index, harrayLength] using hindexLt
  have hprefixLength :
      (radixWord base length state ++
        List.replicate (index - length) 0).length = index := by
    simp [radixWord_length]
    omega
  have hwords' := wordsAt_set_append (value := 0) hwords (by
    simpa [hprefixLength, index] using hslot)
  have hcount : index + 1 - length = (index - length) + 1 := by omega
  have hnextWords :
      radixWord base length state ++
          List.replicate (index + 1 - length) 0 =
        (radixWord base length state ++
          List.replicate (index - length) 0) ++ [0] := by
    rw [hcount, replicate_succ_eq_append]
    simp [List.append_assoc]
  unfold radixPaddingBody Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [RadixPaddingInv, index]
  all_goals omega

def radixPaddingLoopCost (maximumRank : Nat) : Nat :=
  34 * maximumRank + 4

theorem radixPaddingLoop_spec (B base length state maximumRank : Nat) :
    Spec B (RadixPaddingInv B base length state maximumRank) radixPaddingLoop
      (fun _ sigma' =>
        RadixPaddingInv B base length state maximumRank sigma' ∧
          sigma'.vars "radixIndex" = maximumRank)
      (radixPaddingLoopCost maximumRank) := by
  unfold radixPaddingLoop
  exact Spec.forRange "radixIndex" "transitionMaximumRank"
    (RadixPaddingInv B base length state maximumRank) maximumRank 30
      (radixPaddingLoopCost maximumRank)
    (by
      intro _ hinv
      rcases hinv with ⟨_, hindexMaximumRank, _, _, _, _, _, _,
        hmaximumRankB, _⟩
      exact lt_of_le_of_lt hindexMaximumRank hmaximumRankB)
    (by
      intro _ hinv
      rcases hinv with ⟨_, _, _, _, _, hmaximumRank, _, _,
        hmaximumRankB, _⟩
      rw [hmaximumRank]
      exact hmaximumRankB)
    (by intro _ hinv; exact hinv.2.2.2.2.2.1)
    (by intro _ hinv; exact hinv.2.1)
    (radixPaddingBody_spec B base length state maximumRank)
    (fun _ h => h)
    (by
      intro sigma _
      unfold radixPaddingLoopCost
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 34
          (Nat.sub_le maximumRank (sigma.vars "radixIndex"))) 4)

def preparePaddedRadixWordCost (length maximumRank : Nat) : Nat :=
  prepareRadixWordCost length + radixPaddingLoopCost maximumRank

private theorem eq_of_wordsAt_zero {array words : List Nat}
    (hwords : WordsAt array 0 words)
    (hlength : array.length = words.length) : array = words := by
  apply List.ext_get
  · exact hlength
  · intro i harray hword
    have hi := hwords i hword
    simp only [Nat.zero_add] at hi
    rw [List.getD_eq_getElem (l := array) (d := 0) harray,
      List.getD_eq_getElem (l := words) (d := 0) hword] at hi
    exact hi

theorem preparePaddedRadixWord_spec
    (B base length state maximumRank : Nat) :
    Spec B (RadixWordReady B base length state maximumRank)
      preparePaddedRadixWord
      (fun _ sigma' =>
        sigma'.arrs "NewTransitionChildren" =
            paddedRadixWord maximumRank base length state ∧
          sigma'.vars "radixIndex" = maximumRank)
      (preparePaddedRadixWordCost length maximumRank) := by
  unfold preparePaddedRadixWord preparePaddedRadixWordCost
  refine (Spec.seq (prepareRadixWord_spec B base length state maximumRank)
    (radixPaddingLoop_spec B base length state maximumRank)
    (fun _ _ _ h => radixWordInv_to_padding h.1 h.2)
    (fun _ _ _ _ _ h => h)).post ?_
  intro _ sigma' _ hpost
  refine ⟨?_, hpost.2⟩
  have hwords := hpost.1.2.2.2.2.2.2.2.2.2
  rw [hpost.2] at hwords
  have harrayLength := hpost.1.2.2.2.2.2.2.2.1
  apply eq_of_wordsAt_zero hwords
  rw [harrayLength]
  exact (paddedRadixWord_length hpost.1.2.2.2.2.2.2.1).symm

private theorem preparePaddedRadixWord_storageAgrees {sigma sigma' : Env}
    (hvars : ∀ y, y ∉ preparePaddedRadixWord.wvars →
      sigma'.vars y = sigma.vars y)
    (harrs : ∀ a, a ∉ preparePaddedRadixWord.warrs →
      sigma'.arrs a = sigma.arrs a) :
    CompilerStorageAgrees sigma sigma' := by
  refine ⟨hvars _ (by decide), hvars _ (by decide), hvars _ (by decide),
    harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide), harrs _ (by decide), harrs _ (by decide),
    harrs _ (by decide)⟩

def CompilerPaddedRadixWordReady
    (B base length state maximumRank : Nat)
    (stack : List Lax842588.ValueTranslations.AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (sigma : Env) : Prop :=
  RadixWordReady B base length state maximumRank sigma ∧
    CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma

/-- Framed row materialization for use inside append-only automaton
constructors. -/
theorem preparePaddedRadixWord_compiler_spec
    (B base length state maximumRank : Nat)
    (stack : List Lax842588.ValueTranslations.AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) :
    Spec B
      (CompilerPaddedRadixWordReady B base length state maximumRank stack
        transitionPrefix acceptingPrefix)
      preparePaddedRadixWord
      (fun _ sigma' =>
        sigma'.arrs "NewTransitionChildren" =
            paddedRadixWord maximumRank base length state ∧
          sigma'.vars "radixIndex" = maximumRank ∧
          CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep transitionPrefix sigma' ∧
          AcceptingHeapRep acceptingPrefix sigma')
      (preparePaddedRadixWordCost length maximumRank) := by
  refine ((preparePaddedRadixWord_spec B base length state maximumRank).pre
    (fun _ h => h.1)).frame.post ?_
  intro sigma sigma' hpre hpost
  rcases hpre with ⟨_, hstack, htransitionHeap, hacceptingHeap⟩
  rcases hpost with ⟨hrow, hvars, harrs, _, _⟩
  have hagrees := preparePaddedRadixWord_storageAgrees hvars harrs
  exact ⟨hrow.1, hrow.2, compilerStackRep_of_agrees hagrees hstack,
    transitionHeapRep_of_agrees hagrees htransitionHeap,
    acceptingHeapRep_of_agrees hagrees hacceptingHeap⟩

theorem preparedChildren_radixWord
    (maximumRank base length state symbol parent : Nat)
    (hlength : length ≤ maximumRank) :
    preparedChildren maximumRank
        (symbol, parent, radixWord base length state) =
      paddedRadixWord maximumRank base length state := by
  simpa [paddedRadixWord, radixWord_length] using
    preparedChildren_eq_append_replicate maximumRank
      (symbol, parent, radixWord base length state) (by
        simpa [radixWord_length] using hlength)

theorem paddedRadixWord_value_lt
    {maximumRank base length state value : Nat}
    (hbase : 0 < base) (hstate : state < base ^ length)
    (hvalue : value ∈ paddedRadixWord maximumRank base length state) :
    value < base := by
  simp only [paddedRadixWord, List.mem_append,
    List.mem_replicate] at hvalue
  rcases hvalue with hvalue | ⟨_, rfl⟩
  · exact radixWord_value_lt hstate hvalue
  · exact hbase

def RadixTransitionReady (B maximumRank : Nat)
    (stack : List Lax842588.ValueTranslations.AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (base symbol parent length state : Nat) (sigma : Env) : Prop :=
  CompilerPaddedRadixWordReady B base length state maximumRank stack
      transitionPrefix acceptingPrefix sigma ∧
    sigma.vars "newTransitionSymbol" = symbol ∧
    sigma.vars "newTransitionParent" = parent ∧
    sigma.vars "newTransitionArity" = length ∧
    symbol < B ∧ parent < B ∧
    transitionPrefix.length + 3 + maximumRank < B ∧
    transitionPrefix.length + 3 + maximumRank ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

def appendRadixTransitionRecordCost (length maximumRank : Nat) : Nat :=
  preparePaddedRadixWordCost length maximumRank +
    transitionRecordCost maximumRank

/-- Append one transition whose child row is computed from a numeric index
in the automaton's state radix.  The parent register may be prepared by any
constructor-specific IMP+ fragment. -/
theorem appendRadixTransitionRecord_spec
    (B maximumRank : Nat)
    (stack : List Lax842588.ValueTranslations.AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat)
    (base symbol parent length state : Nat) (h0 : 0 < B) :
    Spec B
      (RadixTransitionReady B maximumRank stack transitionPrefix
        acceptingPrefix base symbol parent length state)
      appendRadixTransitionRecord
      (fun _ sigma' =>
        CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep
            (transitionPrefix ++ encodeTransitionFixed maximumRank
              (symbol, parent, radixWord base length state)) sigma' ∧
          AcceptingHeapRep acceptingPrefix sigma' ∧
          sigma'.arrs "NewTransitionChildren" =
            paddedRadixWord maximumRank base length state)
      (appendRadixTransitionRecordCost length maximumRank) := by
  unfold appendRadixTransitionRecord appendRadixTransitionRecordCost
  refine Spec.seq
    ((preparePaddedRadixWord_compiler_spec B base length state maximumRank
      stack transitionPrefix acceptingPrefix).pre (fun _ h => h.1) |>.frame)
    (appendEncodedTransition_spec B maximumRank stack transitionPrefix
      (symbol, parent, radixWord base length state) h0 |>.frame)
    ?_ ?_
  · intro sigma sigma' hpre hpost
    rcases hpre with ⟨hcompilerReady, hsymbol, hparent, harity,
      hsymbolB, hparentB, hrecordB, hcapacity, hheapLengthB⟩
    rcases hpost with ⟨hprepared, hvars, harrs, _, _⟩
    rcases hprepared with ⟨hrow, _, hstack, htransitionHeap,
      hacceptingHeap⟩
    rcases hcompilerReady.1 with ⟨hbaseVar, hlengthVar, hstateVar,
      hbasePos, hbaseB, hstateBound, _, hlengthB, _, _, hmaximumRank,
      hlengthMaximumRank, _, _⟩
    have hsymbol' : sigma'.vars "newTransitionSymbol" = symbol :=
      (hvars _ (by decide)).trans hsymbol
    have hparent' : sigma'.vars "newTransitionParent" = parent :=
      (hvars _ (by decide)).trans hparent
    have harity' : sigma'.vars "newTransitionArity" = length :=
      (hvars _ (by decide)).trans harity
    have hmaximumRank' :
        sigma'.vars "transitionMaximumRank" = maximumRank :=
      (hvars _ (by decide)).trans hmaximumRank
    have htransitionArray := harrs "CompiledTransitions" (by decide)
    have hcapacity' : transitionPrefix.length + 3 + maximumRank ≤
        (sigma'.arrs "CompiledTransitions").length := by
      rw [htransitionArray]
      exact hcapacity
    have hheapLengthB' :
        (sigma'.arrs "CompiledTransitions").length < B := by
      rw [htransitionArray]
      exact hheapLengthB
    show EncodedTransitionReady B maximumRank stack transitionPrefix
      (symbol, parent, radixWord base length state) sigma'
    simp only [EncodedTransitionReady, TransitionRecordReady]
    refine ⟨hstack, htransitionHeap, hsymbol', hparent', (by
        simpa using harity'), ?_, ?_, hmaximumRank', hsymbolB, hparentB,
      (by simpa using hlengthB), ?_, hrecordB, hcapacity', hheapLengthB'⟩
    · rw [preparedChildren_radixWord maximumRank base length state symbol
        parent hlengthMaximumRank]
      exact hrow
    · rw [preparedChildren_radixWord maximumRank base length state symbol
        parent hlengthMaximumRank]
      exact paddedRadixWord_length hlengthMaximumRank
    · intro value hvalue
      have hvalue' : value ∈ paddedRadixWord maximumRank base length state := by
        rwa [preparedChildren_radixWord maximumRank base length state symbol
          parent hlengthMaximumRank] at hvalue
      exact lt_trans
        (paddedRadixWord_value_lt hbasePos hstateBound hvalue') hbaseB
  · intro _ sigma' sigma'' _ hprepared hfinal
    rcases hprepared with ⟨hpreparedCore, _, _, _, _⟩
    rcases hpreparedCore with ⟨hrowPrepared, _, _, _, hacceptingHeap⟩
    rcases hfinal with
      ⟨⟨hstackFinal, htransitionFinal⟩, hvarsFinal, harrsFinal, _, _⟩
    have hacceptingFinal : AcceptingHeapRep acceptingPrefix sigma'' := by
      have hcursor := hvarsFinal "compiledAcceptingWords" (by decide)
      have harray := harrsFinal "CompiledAccepting" (by decide)
      exact ⟨hcursor.trans hacceptingHeap.1, by
        rw [harray]
        exact hacceptingHeap.2⟩
    have hrowFinal : sigma''.arrs "NewTransitionChildren" =
        paddedRadixWord maximumRank base length state :=
      (harrsFinal "NewTransitionChildren" (by decide)).trans hrowPrepared
    exact ⟨hstackFinal, htransitionFinal, hacceptingFinal, hrowFinal⟩

/-! ### Charged computation of the complete child-row count -/

def RadixRowsStartReady (B base length : Nat) (sigma : Env) : Prop :=
  sigma.vars "radixBase" = base ∧
    sigma.vars "radixLength" = length ∧
    0 < base ∧ base < B ∧
    base ^ length < B ∧ length < B

def RadixRowPowerInv (B base length : Nat) (sigma : Env) : Prop :=
  let index := sigma.vars "radixRowPowerIndex"
  RadixRowsStartReady B base length sigma ∧
    sigma.vars "radixState" = 0 ∧
    index ≤ length ∧
    sigma.vars "radixRowLimit" = base ^ index ∧
    index < B ∧ sigma.vars "radixRowLimit" < B

theorem initializeRadixRows_spec (B base length : Nat) :
    Spec B (RadixRowsStartReady B base length) initializeRadixRows
      (fun _ sigma' => RadixRowPowerInv B base length sigma') 30 := by
  intro sigma hready
  rcases hready with ⟨hbase, hlength, hbasePos, hbaseB, hpowerB,
    hlengthB⟩
  have hpowerPos : 0 < base ^ length := pow_pos hbasePos _
  have honeB : 1 < B := by omega
  have hzeroB : 0 < B := by omega
  unfold initializeRadixRows Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [RadixRowPowerInv, RadixRowsStartReady]

theorem radixRowPowerBody_spec (B base length : Nat) :
    Spec B
      (fun sigma => RadixRowPowerInv B base length sigma ∧
        sigma.vars "radixRowPowerIndex" < length)
      radixRowPowerBody
      (fun sigma sigma' =>
        RadixRowPowerInv B base length sigma' ∧
          sigma'.vars "radixRowPowerIndex" =
            sigma.vars "radixRowPowerIndex" + 1)
      50 := by
  intro sigma hpre
  rcases hpre with ⟨hinv, hindexLt⟩
  simp only [RadixRowPowerInv] at hinv
  rcases hinv with ⟨hready, hstate, hindexLe, hlimit, hindexB,
    hlimitB⟩
  rcases hready with ⟨hbase, hlength, hbasePos, hbaseB, hpowerB,
    hlengthB⟩
  have hnextLe : sigma.vars "radixRowPowerIndex" + 1 ≤ length := by
    omega
  have hproductEq :
      sigma.vars "radixRowLimit" * sigma.vars "radixBase" =
        base ^ (sigma.vars "radixRowPowerIndex" + 1) := by
    rw [hlimit, hbase]
    simp [pow_succ]
  have hproductB :
      sigma.vars "radixRowLimit" * sigma.vars "radixBase" < B := by
    rw [hproductEq]
    exact lt_of_le_of_lt
      (Nat.pow_le_pow_right hbasePos hnextLe) hpowerB
  have hnextIndexB : sigma.vars "radixRowPowerIndex" + 1 < B := by
    omega
  unfold radixRowPowerBody Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [RadixRowPowerInv, RadixRowsStartReady]

def radixRowPowerLoopCost (length : Nat) : Nat :=
  54 * length + 4

theorem radixRowPowerLoop_spec (B base length : Nat) :
    Spec B (RadixRowPowerInv B base length) radixRowPowerLoop
      (fun _ sigma' =>
        RadixRowPowerInv B base length sigma' ∧
          sigma'.vars "radixRowPowerIndex" = length)
      (radixRowPowerLoopCost length) := by
  unfold radixRowPowerLoop
  exact Spec.forRange "radixRowPowerIndex" "radixLength"
    (RadixRowPowerInv B base length) length 50
      (radixRowPowerLoopCost length)
    (by
      intro _ hinv
      rcases hinv with ⟨⟨_, _, _, _, _, hlengthB⟩, _, hindexLe, -⟩
      exact lt_of_le_of_lt hindexLe hlengthB)
    (by
      intro _ hinv
      rcases hinv with ⟨⟨_, hlength, _, _, _, hlengthB⟩, -⟩
      rw [hlength]
      exact hlengthB)
    (by intro _ hinv; exact hinv.1.2.1)
    (by intro _ hinv; exact hinv.2.2.1)
    (radixRowPowerBody_spec B base length)
    (fun _ h => h)
    (by
      intro sigma _
      unfold radixRowPowerLoopCost
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 54
          (Nat.sub_le length
            (sigma.vars "radixRowPowerIndex"))) 4)

def beginRadixRowsCost (length : Nat) : Nat :=
  30 + radixRowPowerLoopCost length

theorem beginRadixRows_spec (B base length : Nat) :
    Spec B (RadixRowsStartReady B base length) beginRadixRows
      (fun _ sigma' =>
        RadixRowPowerInv B base length sigma' ∧
          sigma'.vars "radixRowPowerIndex" = length ∧
          sigma'.vars "radixRowLimit" = base ^ length ∧
          sigma'.vars "radixState" = 0)
      (beginRadixRowsCost length) := by
  unfold beginRadixRows beginRadixRowsCost
  refine Spec.seq (initializeRadixRows_spec B base length)
    (radixRowPowerLoop_spec B base length) (fun _ _ _ h => h) ?_
  intro _ _ _ _ _ hpost
  rcases hpost with ⟨hinv, hdone⟩
  exact ⟨hinv, hdone, by
    have hlimit := hinv.2.2.2.1
    rw [hdone] at hlimit
    exact hlimit, hinv.2.1⟩

end Lax842588Proofs.MSORamCompilerRadixWord
