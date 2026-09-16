import Lax842588Proofs.MSORamCompilerProgram

/-! Charged generic push of one immutable compiled-automaton descriptor. -/

namespace Lax842588Proofs.MSORamCompilerPush

set_option maxHeartbeats 3000000

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.ValueTranslations
open Lax842588Proofs.MSORamCompilerProgram
open Lax842588Proofs.MSORamCompilerStorage

def DescriptorPushReady (B maximumRank : Nat) (M : AutomatonCode)
    (stack : List AutomatonCode) (descriptor : Descriptor)
    (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    StoresAutomaton maximumRank
      (sigma.arrs "CompiledTransitions")
      (sigma.arrs "CompiledAccepting") descriptor M ∧
    DescriptorWithinCursors maximumRank descriptor sigma ∧
    sigma.vars "newStates" = descriptor.states ∧
    sigma.vars "newTransitionBase" = descriptor.transitionBase ∧
    sigma.vars "newTransitionCount" = descriptor.transitionCount ∧
    sigma.vars "newAcceptingBase" = descriptor.acceptingBase ∧
    sigma.vars "newAcceptingCount" = descriptor.acceptingCount ∧
    descriptor.states < B ∧ descriptor.transitionBase < B ∧
    descriptor.transitionCount < B ∧ descriptor.acceptingBase < B ∧
    descriptor.acceptingCount < B ∧ stack.length + 1 < B ∧
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

theorem pushAutomatonDescriptor_spec (B maximumRank : Nat)
    (M : AutomatonCode) (stack : List AutomatonCode)
    (descriptor : Descriptor) :
    Spec B (DescriptorPushReady B maximumRank M stack descriptor)
      pushAutomatonDescriptor
      (fun _ sigma' => CompilerStackRep maximumRank (M :: stack) sigma')
      100 := by
  intro sigma hready
  rcases hready with ⟨hstack, hstored, hwithin, hstatesValue,
    htransitionBaseValue, htransitionCountValue, hacceptingBaseValue,
    hacceptingCountValue, hstatesB, htransitionBaseB, htransitionCountB,
    hacceptingBaseB, hacceptingCountB, hdepthB, hstatesSpace,
    htransitionBaseSpace, htransitionCountSpace, hacceptingBaseSpace,
    hacceptingCountSpace, hstatesLengthB, htransitionBaseLengthB,
    htransitionCountLengthB, hacceptingBaseLengthB,
    hacceptingCountLengthB⟩
  have hdepth := compilerStackRep_depth hstack
  have hpush := compilerStackRep_push M descriptor hstack hstored hwithin
    hstatesSpace htransitionBaseSpace htransitionCountSpace
    hacceptingBaseSpace hacceptingCountSpace
  unfold pushAutomatonDescriptor
    Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [pushDescriptorEnv, CompilerStackRep,
    DescriptorArraysRep, StoredDescriptors]

end Lax842588Proofs.MSORamCompilerPush
