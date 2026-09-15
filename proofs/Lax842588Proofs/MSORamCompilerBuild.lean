import Lax842588Proofs.MSORamCompilerHeap
import Lax842588Proofs.MSORamCompilerPush

/-!
Opening and finalizing one append-only compiled automaton segment.

Construction-specific loops only have to establish the exact transition and
accepting heap suffixes.  This module turns those suffix facts into the generic
descriptor contract and performs the charged stack push.
-/

namespace Lax842588Proofs.MSORamCompilerBuild

set_option maxHeartbeats 3000000

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.ValueTranslations
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.MSORamCompilerHeap
open Lax842588Proofs.MSORamCompilerProgram
open Lax842588Proofs.MSORamCompilerPush
open Lax842588Proofs.MSORamCompilerStorage

def AutomatonBuildStartReady (B maximumRank : Nat)
    (stack : List AutomatonCode) (transitionPrefix acceptingPrefix : List Nat)
    (states : Nat) (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    sigma.vars "newStates" = states ∧
    states < B ∧ transitionPrefix.length < B ∧
    acceptingPrefix.length < B ∧ 0 < B

def AutomatonBuildStarted (maximumRank : Nat)
    (stack : List AutomatonCode) (transitionPrefix acceptingPrefix : List Nat)
    (states : Nat) (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep transitionPrefix sigma ∧
    AcceptingHeapRep acceptingPrefix sigma ∧
    preparedDescriptor sigma = {
      states := states
      transitionBase := transitionPrefix.length
      transitionCount := 0
      acceptingBase := acceptingPrefix.length
      acceptingCount := 0 }

theorem beginCompiledAutomaton_spec (B maximumRank : Nat)
    (stack : List AutomatonCode) (transitionPrefix acceptingPrefix : List Nat)
    (states : Nat) :
    Spec B
      (AutomatonBuildStartReady B maximumRank stack transitionPrefix
        acceptingPrefix states)
      beginCompiledAutomaton
      (fun _ sigma' => AutomatonBuildStarted maximumRank stack
        transitionPrefix acceptingPrefix states sigma')
      50 := by
  intro sigma hready
  rcases hready with ⟨hstack, htransitionHeap, hacceptingHeap,
    hstates, hstatesB, htransitionPrefixB, hacceptingPrefixB, h0⟩
  let startedSigma :=
    ((((sigma.setVar "newTransitionBase" transitionPrefix.length).setVar
        "newTransitionCount" 0).setVar
      "newAcceptingBase" acceptingPrefix.length).setVar
      "newAcceptingCount" 0)
  have hstackStarted : CompilerStackRep maximumRank stack startedSigma := by
    simpa [startedSigma, CompilerStackRep, DescriptorWithinCursors] using! hstack
  unfold beginCompiledAutomaton Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [AutomatonBuildStarted, preparedDescriptor,
    TransitionHeapRep, AcceptingHeapRep, startedSigma]

def BuiltAutomaton (maximumRank : Nat) (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (M : AutomatonCode)
    (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    TransitionHeapRep
      (transitionPrefix ++ transitionWords maximumRank M) sigma ∧
    AcceptingHeapRep (acceptingPrefix ++ M.2.2) sigma ∧
    preparedDescriptor sigma = {
      states := M.1
      transitionBase := transitionPrefix.length
      transitionCount := M.2.1.length
      acceptingBase := acceptingPrefix.length
      acceptingCount := M.2.2.length }

def BuiltAutomatonPushReady (B maximumRank : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (M : AutomatonCode)
    (sigma : Env) : Prop :=
  BuiltAutomaton maximumRank stack transitionPrefix acceptingPrefix M sigma ∧
    M.1 < B ∧ transitionPrefix.length < B ∧ M.2.1.length < B ∧
    acceptingPrefix.length < B ∧ M.2.2.length < B ∧
    stack.length + 1 < B ∧
    stack.length < (sigma.arrs "AutomatonStatesStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionCountStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingCountStack").length ∧
    (sigma.arrs "AutomatonStatesStack").length < B ∧
    (sigma.arrs "AutomatonTransitionBaseStack").length < B ∧
    (sigma.arrs "AutomatonTransitionCountStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingBaseStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingCountStack").length < B

theorem builtAutomaton_descriptorReady {B maximumRank : Nat}
    {stack : List AutomatonCode}
    {transitionPrefix acceptingPrefix : List Nat} {M : AutomatonCode}
    {sigma : Env}
    (hready : BuiltAutomatonPushReady B maximumRank stack
      transitionPrefix acceptingPrefix M sigma) :
    DescriptorPushReady B maximumRank M stack (preparedDescriptor sigma) sigma := by
  rcases hready with ⟨⟨hstack, htransitionHeap, hacceptingHeap, hdescriptor⟩,
    hstatesB, htransitionBaseB, htransitionCountB, hacceptingBaseB,
    hacceptingCountB, hdepthB, hstatesSpace, htransitionBaseSpace,
    htransitionCountSpace, hacceptingBaseSpace, hacceptingCountSpace,
    hstatesLengthB, htransitionBaseLengthB, htransitionCountLengthB,
    hacceptingBaseLengthB, hacceptingCountLengthB⟩
  rcases htransitionHeap with ⟨htransitionCursor, htransitionWords⟩
  rcases hacceptingHeap with ⟨hacceptingCursor, hacceptingWords⟩
  have htransitionSegment := wordsAt_append_right htransitionWords
  have hacceptingSegment := wordsAt_append_right hacceptingWords
  have hstored : StoresAutomaton maximumRank
      (sigma.arrs "CompiledTransitions")
      (sigma.arrs "CompiledAccepting") (preparedDescriptor sigma) M := by
    rw [hdescriptor]
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · simpa using htransitionSegment
    · simpa using hacceptingSegment
  have hwithin : DescriptorWithinCursors maximumRank
      (preparedDescriptor sigma) sigma := by
    rw [hdescriptor]
    constructor
    · rw [htransitionCursor]
      simp [transitionWords_length]
    · rw [hacceptingCursor]
      simp
  have hstatesPrepared : (preparedDescriptor sigma).states < B := by
    rw [hdescriptor]
    exact hstatesB
  have htransitionBasePrepared :
      (preparedDescriptor sigma).transitionBase < B := by
    rw [hdescriptor]
    exact htransitionBaseB
  have htransitionCountPrepared :
      (preparedDescriptor sigma).transitionCount < B := by
    rw [hdescriptor]
    exact htransitionCountB
  have hacceptingBasePrepared :
      (preparedDescriptor sigma).acceptingBase < B := by
    rw [hdescriptor]
    exact hacceptingBaseB
  have hacceptingCountPrepared :
      (preparedDescriptor sigma).acceptingCount < B := by
    rw [hdescriptor]
    exact hacceptingCountB
  refine ⟨hstack, hstored, hwithin, ?_, ?_, ?_, ?_, ?_,
    hstatesPrepared, htransitionBasePrepared, htransitionCountPrepared,
    hacceptingBasePrepared, hacceptingCountPrepared, hdepthB,
    hstatesSpace, htransitionBaseSpace,
    htransitionCountSpace, hacceptingBaseSpace, hacceptingCountSpace,
    hstatesLengthB, htransitionBaseLengthB, htransitionCountLengthB,
    hacceptingBaseLengthB, hacceptingCountLengthB⟩
  all_goals simp [preparedDescriptor]

theorem pushBuiltAutomaton_spec (B maximumRank : Nat)
    (stack : List AutomatonCode)
    (transitionPrefix acceptingPrefix : List Nat) (M : AutomatonCode) :
    Spec B
      (BuiltAutomatonPushReady B maximumRank stack
        transitionPrefix acceptingPrefix M)
      pushAutomatonDescriptor
      (fun _ sigma' => CompilerStackRep maximumRank (M :: stack) sigma')
      100 := by
  intro sigma hready
  exact (pushAutomatonDescriptor_spec B maximumRank M stack
    (preparedDescriptor sigma)).run (builtAutomaton_descriptorReady hready)

end Lax842588Proofs.MSORamCompilerBuild
