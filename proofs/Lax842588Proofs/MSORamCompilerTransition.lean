import Lax842588Proofs.MSORamCompilerHeap

/-! Charged construction of fixed-width transition child-state rows. -/

namespace Lax842588Proofs.MSORamCompilerTransition

set_option maxHeartbeats 3000000

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.MSORamCompilerHeap
open Lax842588Proofs.MSORamCompilerProgram
open Lax842588Proofs.MSORamCompilerStorage

/-- During the counted row loop, the transition heap ends in precisely the
prefix of the prepared fixed-width child array that has already been copied. -/
def TransitionChildrenInv (B maximumRank : Nat)
    (stack : List AutomatonCode) (priorWords children : List Nat)
    (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep
      (priorWords ++ children.take (sigma.vars "transitionChildIndex")) sigma ∧
    sigma.arrs "NewTransitionChildren" = children ∧
    children.length = maximumRank ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    sigma.vars "transitionChildIndex" ≤ maximumRank ∧
    (∀ value ∈ children, value < B) ∧
    priorWords.length + maximumRank < B ∧
    priorWords.length + maximumRank ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

theorem appendTransitionChildBody_spec (B maximumRank : Nat)
    (stack : List AutomatonCode) (priorWords children : List Nat)
    (h0 : 0 < B) :
    Spec B
      (fun sigma => TransitionChildrenInv B maximumRank stack priorWords children sigma ∧
        sigma.vars "transitionChildIndex" < maximumRank)
      appendTransitionChildBody
      (fun sigma sigma' =>
        TransitionChildrenInv B maximumRank stack priorWords children sigma' ∧
          sigma'.vars "transitionChildIndex" =
            sigma.vars "transitionChildIndex" + 1)
      60 := by
  intro sigma hready
  rcases hready with ⟨⟨hstack, ⟨hcursor, hwords⟩, hchildren, hchildrenLength,
    hmaximumRank, hindexLe, hchildrenB, hprefixB, hcapacity,
    hheapLengthB⟩, hindexLt⟩
  let index := sigma.vars "transitionChildIndex"
  let currentWords := priorWords ++ children.take index
  let value := children.getD index 0
  have hindexChildren : index < children.length := by
    simp [index, hchildrenLength, hindexLt]
  have hvalueMem : value ∈ children := by
    change children.getD index 0 ∈ children
    rw [List.getD_eq_getElem children 0 hindexChildren]
    exact List.getElem_mem _
  have hvalueB : value < B := hchildrenB value hvalueMem
  have htake : children.take (index + 1) = children.take index ++ [value] := by
    rw [List.take_succ_eq_append_getElem hindexChildren]
    have hvalue : value = children[index] := by
      exact List.getD_eq_getElem children 0 hindexChildren
    rw [hvalue]
  have hcurrentLength : currentWords.length = priorWords.length + index := by
    simp [currentWords, List.length_take, Nat.min_eq_left (Nat.le_of_lt hindexChildren)]
  have hcursorLength : sigma.vars "compiledTransitionWords" =
      priorWords.length + index := by
    exact hcursor.trans hcurrentLength
  have hnextB : currentWords.length + 1 < B := by
    rw [hcurrentLength]
    omega
  have hslot : currentWords.length <
      (sigma.arrs "CompiledTransitions").length := by
    rw [hcurrentLength]
    omega
  have hstack' := compilerStackRep_appendTransition (value := value) hstack (by
    rw [hcursor]
    exact hslot)
  have hwords' := wordsAt_set_append (value := value) hwords (by
    simpa [currentWords, index] using hslot)
  unfold appendTransitionChildBody Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [TransitionChildrenInv, appendTransitionEnv,
    currentWords, value, index, TransitionHeapRep]
  all_goals
    constructor
    · simpa [CompilerStackRep, DescriptorWithinCursors] using! hstack'
    · omega

def transitionChildrenLoopCost (maximumRank : Nat) : Nat :=
  64 * maximumRank + 4

theorem appendTransitionChildrenLoop_spec (B maximumRank : Nat)
    (stack : List AutomatonCode) (priorWords children : List Nat)
    (h0 : 0 < B) :
    Spec B (TransitionChildrenInv B maximumRank stack priorWords children)
      appendTransitionChildrenLoop
      (fun _ sigma' =>
        TransitionChildrenInv B maximumRank stack priorWords children sigma' ∧
          sigma'.vars "transitionChildIndex" = maximumRank)
      (transitionChildrenLoopCost maximumRank) := by
  unfold appendTransitionChildrenLoop
  exact Spec.forRange "transitionChildIndex" "transitionMaximumRank"
    (TransitionChildrenInv B maximumRank stack priorWords children)
    maximumRank 60 (transitionChildrenLoopCost maximumRank)
    (by
      intro sigma hinv
      rcases hinv with ⟨_, _, _, _, _, hindex, _, hprefixB, _, _⟩
      omega)
    (by
      intro sigma hinv
      rcases hinv with ⟨_, _, _, _, hmaximumRank, _, _, hprefixB, _, _⟩
      rw [hmaximumRank]
      omega)
    (by intro _ hinv; exact hinv.2.2.2.2.1)
    (by intro _ hinv; exact hinv.2.2.2.2.2.1)
    (appendTransitionChildBody_spec B maximumRank stack priorWords children h0)
    (fun _ h => h)
    (by
      intro sigma _
      unfold transitionChildrenLoopCost
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 64
          (Nat.sub_le maximumRank (sigma.vars "transitionChildIndex"))) 4)

def TransitionRecordReady (B maximumRank : Nat)
    (stack : List AutomatonCode) (priorWords : List Nat)
    (symbol parent arity : Nat) (children : List Nat) (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep priorWords sigma ∧
    sigma.vars "newTransitionSymbol" = symbol ∧
    sigma.vars "newTransitionParent" = parent ∧
    sigma.vars "newTransitionArity" = arity ∧
    sigma.arrs "NewTransitionChildren" = children ∧
    children.length = maximumRank ∧
    sigma.vars "transitionMaximumRank" = maximumRank ∧
    symbol < B ∧ parent < B ∧ arity < B ∧
    (∀ value ∈ children, value < B) ∧
    priorWords.length + 3 + maximumRank < B ∧
    priorWords.length + 3 + maximumRank ≤
      (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

theorem beginTransitionRecord_spec (B maximumRank : Nat)
    (stack : List AutomatonCode) (priorWords : List Nat)
    (symbol parent arity : Nat) (children : List Nat) :
    Spec B
      (TransitionRecordReady B maximumRank stack priorWords
        symbol parent arity children)
      beginTransitionRecord
      (fun _ sigma' => TransitionChildrenInv B maximumRank stack
        (priorWords ++ [symbol, parent, arity]) children sigma')
      100 := by
  intro sigma hready
  rcases hready with ⟨hstack, ⟨hcursor, hwords⟩, hsymbol, hparent,
    harity, hchildren, hchildrenLength, hmaximumRank, hsymbolB,
    hparentB, harityB, hchildrenB, hrecordB, hcapacity, hheapLengthB⟩
  have hslot0 : sigma.vars "compiledTransitionWords" <
      (sigma.arrs "CompiledTransitions").length := by
    rw [hcursor]
    omega
  let sigma1 := appendTransitionEnv sigma symbol
  have hstack1 : CompilerStackRep maximumRank stack sigma1 :=
    compilerStackRep_appendTransition (value := symbol) hstack hslot0
  have hwords1 := wordsAt_set_append (value := symbol) hwords (by
    simpa [hcursor] using hslot0)
  have hslot1 : sigma1.vars "compiledTransitionWords" <
      (sigma1.arrs "CompiledTransitions").length := by
    simp [sigma1, appendTransitionEnv, hcursor]
    omega
  let sigma2 := appendTransitionEnv sigma1 parent
  have hstack2 : CompilerStackRep maximumRank stack sigma2 :=
    compilerStackRep_appendTransition (value := parent) hstack1 hslot1
  have hwords2 := wordsAt_set_append (value := parent) hwords1 (by
    simpa [sigma1, appendTransitionEnv, hcursor] using hslot1)
  have hslot2 : sigma2.vars "compiledTransitionWords" <
      (sigma2.arrs "CompiledTransitions").length := by
    simp [sigma2, sigma1, appendTransitionEnv, hcursor]
    omega
  let sigma3 := appendTransitionEnv sigma2 arity
  have hstack3 : CompilerStackRep maximumRank stack sigma3 :=
    compilerStackRep_appendTransition (value := arity) hstack2 hslot2
  have hwords3 := wordsAt_set_append (value := arity) hwords2 (by
    simpa [sigma2, sigma1, appendTransitionEnv, hcursor] using hslot2)
  unfold beginTransitionRecord Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [TransitionChildrenInv, TransitionHeapRep,
    sigma3, sigma2, sigma1, appendTransitionEnv]
  all_goals
    constructor
    · exact hstack3.1
    · simpa [CompilerStackRep, DescriptorWithinCursors] using! hstack3.2

def transitionRecordCost (maximumRank : Nat) : Nat :=
  100 + transitionChildrenLoopCost maximumRank

theorem appendTransitionRecord_spec (B maximumRank : Nat)
    (stack : List AutomatonCode) (priorWords : List Nat)
    (symbol parent arity : Nat) (children : List Nat) (h0 : 0 < B) :
    Spec B
      (TransitionRecordReady B maximumRank stack priorWords
        symbol parent arity children)
      appendTransitionRecord
      (fun _ sigma' =>
        CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep
            (priorWords ++ [symbol, parent, arity] ++ children) sigma')
      (transitionRecordCost maximumRank) := by
  unfold appendTransitionRecord transitionRecordCost
  exact Spec.seq
    (beginTransitionRecord_spec B maximumRank stack priorWords
      symbol parent arity children)
    (appendTransitionChildrenLoop_spec B maximumRank stack
      (priorWords ++ [symbol, parent, arity]) children h0)
    (fun _ _ _ h => h)
    (by
      intro _ _ _ _ _ hdone
      refine ⟨hdone.1.1, ?_⟩
      have hchildrenLength : children.length = maximumRank :=
        hdone.1.2.2.2.1
      have htake : children.take maximumRank = children := by
        rw [← hchildrenLength, List.take_length]
      simpa [TransitionChildrenInv, hdone.2, htake] using hdone.1.2.1)

/-- The prepared fixed-width child buffer for a mathematical transition. -/
def preparedChildren (maximumRank : Nat) (transition : TransitionCode) :
    List Nat :=
  (List.range maximumRank).map fun i => transition.2.2.getD i 0

@[simp] theorem preparedChildren_length (maximumRank : Nat)
    (transition : TransitionCode) :
    (preparedChildren maximumRank transition).length = maximumRank := by
  simp [preparedChildren]

theorem preparedChildren_eq_append_replicate (maximumRank : Nat)
    (transition : TransitionCode)
    (hlength : transition.2.2.length ≤ maximumRank) :
    preparedChildren maximumRank transition =
      transition.2.2 ++
        List.replicate (maximumRank - transition.2.2.length) 0 := by
  apply List.ext_get
  · simp [preparedChildren]
    omega
  · intro i hleft hright
    simp only [preparedChildren, List.get_eq_getElem, List.getElem_map,
      List.getElem_range]
    rw [List.getElem_append]
    split
    · rw [List.getD_eq_getElem]
    · rw [List.getD_eq_default (l := transition.2.2) (d := 0)
        (Nat.le_of_not_gt ‹¬i < transition.2.2.length›)]
      simp

theorem transitionRecordWords_eq (maximumRank : Nat)
    (transition : TransitionCode) :
    [transition.1, transition.2.1, transition.2.2.length] ++
        preparedChildren maximumRank transition =
      encodeTransitionFixed maximumRank transition := by
  simp [preparedChildren, encodeTransitionFixed]

def EncodedTransitionReady (B maximumRank : Nat)
    (stack : List AutomatonCode) (priorWords : List Nat)
    (transition : TransitionCode) (sigma : Env) : Prop :=
  TransitionRecordReady B maximumRank stack priorWords
    transition.1 transition.2.1 transition.2.2.length
    (preparedChildren maximumRank transition) sigma

theorem appendEncodedTransition_spec (B maximumRank : Nat)
    (stack : List AutomatonCode) (priorWords : List Nat)
    (transition : TransitionCode) (h0 : 0 < B) :
    Spec B
      (EncodedTransitionReady B maximumRank stack priorWords transition)
      appendTransitionRecord
      (fun _ sigma' =>
        CompilerStackRep maximumRank stack sigma' ∧
          TransitionHeapRep
            (priorWords ++ encodeTransitionFixed maximumRank transition) sigma')
      (transitionRecordCost maximumRank) := by
  simpa [EncodedTransitionReady, transitionRecordWords_eq] using!
    appendTransitionRecord_spec B maximumRank stack priorWords
      transition.1 transition.2.1 transition.2.2.length
      (preparedChildren maximumRank transition) h0

end Lax842588Proofs.MSORamCompilerTransition
