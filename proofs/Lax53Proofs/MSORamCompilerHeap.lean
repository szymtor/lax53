import Lax53Proofs.MSORamCompilerProgram

/-!
Charged append-only heap writes for compiled automata.

The specifications preserve every automaton already represented by the
descriptor stack.  That preservation is not a memory-model convention: it
follows from the explicit fact that every old segment ends before the live
cursor and from the single-cell operational semantics of the IMP+ store.
-/

namespace Lax53Proofs.MSORamCompilerHeap

set_option maxHeartbeats 3000000

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53.ValueTranslations
open Lax53Proofs.AutomatonRamArenaSegments
open Lax53Proofs.MSORamCompilerProgram
open Lax53Proofs.MSORamCompilerStorage

def TransitionHeapRep (words : List Nat) (sigma : Env) : Prop :=
  sigma.vars "compiledTransitionWords" = words.length ∧
    WordsAt (sigma.arrs "CompiledTransitions") 0 words

def AcceptingHeapRep (words : List Nat) (sigma : Env) : Prop :=
  sigma.vars "compiledAcceptingWords" = words.length ∧
    WordsAt (sigma.arrs "CompiledAccepting") 0 words

theorem transitionHeapRep_of_agrees {words : List Nat} {sigma sigma' : Env}
    (hagrees : CompilerStorageAgrees sigma sigma')
    (hheap : TransitionHeapRep words sigma) :
    TransitionHeapRep words sigma' := by
  simpa [TransitionHeapRep, hagrees.2.1, hagrees.2.2.2.1] using hheap

theorem acceptingHeapRep_of_agrees {words : List Nat} {sigma sigma' : Env}
    (hagrees : CompilerStorageAgrees sigma sigma')
    (hheap : AcceptingHeapRep words sigma) :
    AcceptingHeapRep words sigma' := by
  simpa [AcceptingHeapRep, hagrees.2.2.1, hagrees.2.2.2.2.1] using hheap

def CompilerInitialized (maximumRank : Nat) (sigma : Env) : Prop :=
  sigma.vars "compilerIndex" = 0 ∧
    CompilerStackRep maximumRank [] sigma ∧
    TransitionHeapRep [] sigma ∧
    AcceptingHeapRep [] sigma

def appendTransitionEnv (sigma : Env) (value : Nat) : Env :=
  (sigma.setArr "CompiledTransitions"
      (sigma.vars "compiledTransitionWords") value).setVar
    "compiledTransitionWords" (sigma.vars "compiledTransitionWords" + 1)

def appendAcceptingEnv (sigma : Env) (value : Nat) : Env :=
  (sigma.setArr "CompiledAccepting"
      (sigma.vars "compiledAcceptingWords") value).setVar
    "compiledAcceptingWords" (sigma.vars "compiledAcceptingWords" + 1)

theorem initializeCompiler_spec (B maximumRank : Nat) (h0 : 0 < B) :
    Spec B (fun _ => True) initializeCompiler
      (fun _ sigma' => CompilerInitialized maximumRank sigma') 40 := by
  intro sigma _
  unfold initializeCompiler Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [CompilerInitialized, compilerStackRep_nil_iff,
    TransitionHeapRep, AcceptingHeapRep, WordsAt]

private theorem storesAutomaton_transition_set_after
    {maximumRank cursor value : Nat}
    {transitionHeap acceptingHeap : List Nat}
    {descriptor : Descriptor} {M : AutomatonCode}
    (hstored : StoresAutomaton maximumRank transitionHeap acceptingHeap
      descriptor M)
    (hwithin : descriptor.transitionBase +
        descriptor.transitionCount * (maximumRank + 3) ≤ cursor)
    (hslot : cursor < transitionHeap.length) :
    StoresAutomaton maximumRank (transitionHeap.set cursor value)
      acceptingHeap descriptor M := by
  rcases hstored with ⟨hstates, htransitionCount, hacceptingCount,
    htransitionWords, hacceptingWords⟩
  refine ⟨hstates, htransitionCount, hacceptingCount, ?_, hacceptingWords⟩
  apply wordsAt_of_sameBefore
    (sameBefore_set_after (sameBefore_refl transitionHeap cursor)
      (le_refl cursor) hslot)
    htransitionWords
  rw [htransitionCount] at hwithin
  simpa using hwithin

private theorem storesAutomaton_accepting_set_after
    {maximumRank cursor value : Nat}
    {transitionHeap acceptingHeap : List Nat}
    {descriptor : Descriptor} {M : AutomatonCode}
    (hstored : StoresAutomaton maximumRank transitionHeap acceptingHeap
      descriptor M)
    (hwithin : descriptor.acceptingBase + descriptor.acceptingCount ≤ cursor)
    (hslot : cursor < acceptingHeap.length) :
    StoresAutomaton maximumRank transitionHeap
      (acceptingHeap.set cursor value) descriptor M := by
  rcases hstored with ⟨hstates, htransitionCount, hacceptingCount,
    htransitionWords, hacceptingWords⟩
  refine ⟨hstates, htransitionCount, hacceptingCount, htransitionWords, ?_⟩
  apply wordsAt_of_sameBefore
    (sameBefore_set_after (sameBefore_refl acceptingHeap cursor)
      (le_refl cursor) hslot)
    hacceptingWords
  simpa [hacceptingCount] using hwithin

private theorem storedDescriptors_transition_set_after
    {maximumRank cursor value : Nat} {sigma : Env}
    {descriptors : List Descriptor} {stack : List AutomatonCode}
    (hstored : StoredDescriptors maximumRank
      (sigma.arrs "CompiledTransitions")
      (sigma.arrs "CompiledAccepting") descriptors stack)
    (hwithin : ∀ descriptor ∈ descriptors,
      DescriptorWithinCursors maximumRank descriptor sigma)
    (hcursor : sigma.vars "compiledTransitionWords" = cursor)
    (hslot : cursor < (sigma.arrs "CompiledTransitions").length) :
    StoredDescriptors maximumRank
      ((sigma.arrs "CompiledTransitions").set cursor value)
      (sigma.arrs "CompiledAccepting") descriptors stack := by
  unfold StoredDescriptors at hstored ⊢
  generalize stack.reverse = codes at hstored ⊢
  induction hstored with
  | nil => exact .nil
  | cons hhead htail ih =>
      apply List.Forall₂.cons
      · apply storesAutomaton_transition_set_after hhead
          (cursor := cursor) (value := value)
        simpa [DescriptorWithinCursors, hcursor] using
          (hwithin _ (by simp)) |>.1
        exact hslot
      · apply ih
        intro descriptor hdescriptor
        exact hwithin descriptor (by simp [hdescriptor])

private theorem storedDescriptors_accepting_set_after
    {maximumRank cursor value : Nat} {sigma : Env}
    {descriptors : List Descriptor} {stack : List AutomatonCode}
    (hstored : StoredDescriptors maximumRank
      (sigma.arrs "CompiledTransitions")
      (sigma.arrs "CompiledAccepting") descriptors stack)
    (hwithin : ∀ descriptor ∈ descriptors,
      DescriptorWithinCursors maximumRank descriptor sigma)
    (hcursor : sigma.vars "compiledAcceptingWords" = cursor)
    (hslot : cursor < (sigma.arrs "CompiledAccepting").length) :
    StoredDescriptors maximumRank
      (sigma.arrs "CompiledTransitions")
      ((sigma.arrs "CompiledAccepting").set cursor value)
      descriptors stack := by
  unfold StoredDescriptors at hstored ⊢
  generalize stack.reverse = codes at hstored ⊢
  induction hstored with
  | nil => exact .nil
  | cons hhead htail ih =>
      apply List.Forall₂.cons
      · apply storesAutomaton_accepting_set_after hhead
          (cursor := cursor) (value := value)
        simpa [DescriptorWithinCursors, hcursor] using
          (hwithin _ (by simp)) |>.2
        exact hslot
      · apply ih
        intro descriptor hdescriptor
        exact hwithin descriptor (by simp [hdescriptor])

theorem compilerStackRep_appendTransition
    {maximumRank value : Nat} {stack : List AutomatonCode} {sigma : Env}
    (hstack : CompilerStackRep maximumRank stack sigma)
    (hslot : sigma.vars "compiledTransitionWords" <
      (sigma.arrs "CompiledTransitions").length) :
    CompilerStackRep maximumRank stack (appendTransitionEnv sigma value) := by
  rcases hstack with ⟨hdepth, descriptors, hstored, harrays, hwithin⟩
  refine ⟨by simpa [appendTransitionEnv] using hdepth, descriptors, ?_, ?_, ?_⟩
  · simpa [appendTransitionEnv] using
      storedDescriptors_transition_set_after hstored hwithin rfl hslot
  · simpa [DescriptorArraysRep, appendTransitionEnv] using harrays
  · intro descriptor hdescriptor
    have hold := hwithin descriptor hdescriptor
    simp only [DescriptorWithinCursors] at hold ⊢
    constructor
    · simpa [appendTransitionEnv] using Nat.le.step hold.1
    · simpa [appendTransitionEnv] using hold.2

theorem compilerStackRep_appendAccepting
    {maximumRank value : Nat} {stack : List AutomatonCode} {sigma : Env}
    (hstack : CompilerStackRep maximumRank stack sigma)
    (hslot : sigma.vars "compiledAcceptingWords" <
      (sigma.arrs "CompiledAccepting").length) :
    CompilerStackRep maximumRank stack (appendAcceptingEnv sigma value) := by
  rcases hstack with ⟨hdepth, descriptors, hstored, harrays, hwithin⟩
  refine ⟨by simpa [appendAcceptingEnv] using hdepth, descriptors, ?_, ?_, ?_⟩
  · simpa [appendAcceptingEnv] using
      storedDescriptors_accepting_set_after hstored hwithin rfl hslot
  · simpa [DescriptorArraysRep, appendAcceptingEnv] using harrays
  · intro descriptor hdescriptor
    have hold := hwithin descriptor hdescriptor
    simp only [DescriptorWithinCursors] at hold ⊢
    constructor
    · simpa [appendAcceptingEnv] using hold.1
    · simpa [appendAcceptingEnv] using Nat.le.step hold.2

def TransitionAppendReady (B maximumRank : Nat)
    (stack : List AutomatonCode) (words : List Nat) (value : Nat)
    (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep words sigma ∧
    sigma.vars "newTransitionWord" = value ∧
    value < B ∧ words.length + 1 < B ∧
    words.length < (sigma.arrs "CompiledTransitions").length ∧
    (sigma.arrs "CompiledTransitions").length < B

def AcceptingAppendReady (B maximumRank : Nat)
    (stack : List AutomatonCode) (words : List Nat) (value : Nat)
    (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    AcceptingHeapRep words sigma ∧
    sigma.vars "newAcceptingWord" = value ∧
    value < B ∧ words.length + 1 < B ∧
    words.length < (sigma.arrs "CompiledAccepting").length ∧
    (sigma.arrs "CompiledAccepting").length < B

theorem appendTransitionWord_spec (B maximumRank : Nat)
    (stack : List AutomatonCode) (words : List Nat) (value : Nat) :
    Spec B (TransitionAppendReady B maximumRank stack words value)
      appendTransitionWord
      (fun sigma sigma' => CompilerStackRep maximumRank stack sigma' ∧
        TransitionHeapRep (words ++ [value]) sigma' ∧
        (sigma'.arrs "CompiledTransitions").length =
          (sigma.arrs "CompiledTransitions").length) 30 := by
  intro sigma hready
  rcases hready with ⟨hstack, ⟨hcursor, hwords⟩, hvalue,
    hvalueB, hnextB, hslot, hlengthB⟩
  have hstack' := compilerStackRep_appendTransition (value := value) hstack (by
    simpa [hcursor] using hslot)
  have hwords' := wordsAt_set_append (value := value) hwords (by
    simpa [hcursor] using hslot)
  unfold appendTransitionWord Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [TransitionHeapRep, appendTransitionEnv]

theorem appendAcceptingWord_spec (B maximumRank : Nat)
    (stack : List AutomatonCode) (words : List Nat) (value : Nat) :
    Spec B (AcceptingAppendReady B maximumRank stack words value)
      appendAcceptingWord
      (fun sigma sigma' => CompilerStackRep maximumRank stack sigma' ∧
        AcceptingHeapRep (words ++ [value]) sigma' ∧
        (sigma'.arrs "CompiledAccepting").length =
          (sigma.arrs "CompiledAccepting").length) 30 := by
  intro sigma hready
  rcases hready with ⟨hstack, ⟨hcursor, hwords⟩, hvalue,
    hvalueB, hnextB, hslot, hlengthB⟩
  have hstack' := compilerStackRep_appendAccepting (value := value) hstack (by
    simpa [hcursor] using hslot)
  have hwords' := wordsAt_set_append (value := value) hwords (by
    simpa [hcursor] using hslot)
  unfold appendAcceptingWord Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [AcceptingHeapRep, appendAcceptingEnv]

end Lax53Proofs.MSORamCompilerHeap
