import Lax53Proofs.MSORamCompilerStorage
import Lax53Proofs.MSORamCompilerProgram

/-! Charged access to and removal of the logical top automaton descriptor. -/

namespace Lax53Proofs.MSORamCompilerPop

set_option maxHeartbeats 3000000

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53.ValueTranslations
open Lax53Proofs.MSORamCompilerProgram
open Lax53Proofs.MSORamCompilerStorage

def LoadedDescriptor (descriptor : Descriptor) (sigma : Env) : Prop :=
  sigma.vars "poppedStates" = descriptor.states ∧
    sigma.vars "poppedTransitionBase" = descriptor.transitionBase ∧
    sigma.vars "poppedTransitionCount" = descriptor.transitionCount ∧
    sigma.vars "poppedAcceptingBase" = descriptor.acceptingBase ∧
    sigma.vars "poppedAcceptingCount" = descriptor.acceptingCount

def DescriptorPopReady (B maximumRank : Nat) (M : AutomatonCode)
    (stack : List AutomatonCode) (sigma : Env) : Prop :=
  CompilerStackRep maximumRank (M :: stack) sigma ∧
    stack.length < B ∧
    stack.length < (sigma.arrs "AutomatonStatesStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonTransitionCountStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingBaseStack").length ∧
    stack.length < (sigma.arrs "AutomatonAcceptingCountStack").length ∧
    (sigma.arrs "AutomatonStatesStack").length < B ∧
    (sigma.arrs "AutomatonTransitionBaseStack").length < B ∧
    (sigma.arrs "AutomatonTransitionCountStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingBaseStack").length < B ∧
    (sigma.arrs "AutomatonAcceptingCountStack").length < B ∧
    (descriptorAt sigma stack.length).states < B ∧
    (descriptorAt sigma stack.length).transitionBase < B ∧
    (descriptorAt sigma stack.length).transitionCount < B ∧
    (descriptorAt sigma stack.length).acceptingBase < B ∧
    (descriptorAt sigma stack.length).acceptingCount < B

theorem popAutomatonDescriptor_spec (B maximumRank : Nat)
    (M : AutomatonCode) (stack : List AutomatonCode) :
    Spec B (DescriptorPopReady B maximumRank M stack)
      popAutomatonDescriptor
      (fun sigma sigma' =>
        let descriptor := descriptorAt sigma stack.length
        CompilerStackRep maximumRank stack sigma' ∧
          StoresAutomaton maximumRank
            (sigma'.arrs "CompiledTransitions")
            (sigma'.arrs "CompiledAccepting") descriptor M ∧
          LoadedDescriptor descriptor sigma')
      100 := by
  intro sigma hready
  rcases hready with ⟨hstack, hindexB, hstatesSlot,
    htransitionBaseSlot, htransitionCountSlot, hacceptingBaseSlot,
    hacceptingCountSlot, hstatesLengthB, htransitionBaseLengthB,
    htransitionCountLengthB, hacceptingBaseLengthB,
    hacceptingCountLengthB, hstatesB, htransitionBaseB,
    htransitionCountB, hacceptingBaseB, hacceptingCountB⟩
  let descriptor := descriptorAt sigma stack.length
  have hdepth := compilerStackRep_depth hstack
  have htop := compilerStackRep_top hstack
  have hpop := compilerStackRep_pop hstack
  unfold popAutomatonDescriptor Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [LoadedDescriptor, descriptorAt, popDescriptorEnv]
  all_goals
    first
    | simpa [CompilerStackRep, DescriptorWithinCursors,
        popDescriptorEnv] using hpop
    | assumption
    | omega

end Lax53Proofs.MSORamCompilerPop
