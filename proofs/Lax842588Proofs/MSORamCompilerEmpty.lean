import Lax842588Proofs.MSORamCompilerPush
import Lax842588Proofs.IntrinsicFormulaCompiler

/-! Charged construction of the primitive empty automaton. -/

namespace Lax842588Proofs.MSORamCompilerEmpty

set_option maxHeartbeats 3000000

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.ValueTranslations
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.IntrinsicFormulaCompiler
open Lax842588Proofs.MarkedAlphabetEncoding
open Lax842588Proofs.MSORamCompilerProgram
open Lax842588Proofs.MSORamCompilerPush
open Lax842588Proofs.MSORamCompilerStorage

def emptyDescriptor (sigma : Env) : Descriptor where
  states := 1
  transitionBase := sigma.vars "compiledTransitionWords"
  transitionCount := 0
  acceptingBase := sigma.vars "compiledAcceptingWords"
  acceptingCount := 0

def EmptyAutomatonReady (B maximumRank : Nat)
    (stack : List AutomatonCode) (sigma : Env) : Prop :=
  CompilerStackRep maximumRank stack sigma ∧
    1 < B ∧ sigma.vars "compiledTransitionWords" < B ∧
    sigma.vars "compiledAcceptingWords" < B ∧ stack.length + 1 < B ∧
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

theorem emptyDescriptor_stores (maximumRank : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat) (sigma : Env) :
    StoresAutomaton maximumRank
      (sigma.arrs "CompiledTransitions")
      (sigma.arrs "CompiledAccepting") (emptyDescriptor sigma)
      (emptyCode (code alphabet n m)) := by
  simp [StoresAutomaton, emptyDescriptor, transitionWords, WordsAt]

theorem prepareEmptyAutomatonDescriptor_spec (B maximumRank : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode) :
    Spec B (EmptyAutomatonReady B maximumRank stack)
      prepareEmptyAutomatonDescriptor
      (fun sigma sigma' => DescriptorPushReady B maximumRank
        (emptyCode (code alphabet n m)) stack (emptyDescriptor sigma) sigma')
      60 := by
  intro sigma hready
  rcases hready with ⟨hstack, h1, htransitionCursorB,
    hacceptingCursorB, hdepthB, hstatesSpace, htransitionBaseSpace,
    htransitionCountSpace, hacceptingBaseSpace, hacceptingCountSpace,
    hstatesLengthB, htransitionBaseLengthB, htransitionCountLengthB,
    hacceptingBaseLengthB, hacceptingCountLengthB⟩
  have hstored := emptyDescriptor_stores maximumRank alphabet n m sigma
  unfold prepareEmptyAutomatonDescriptor
    Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [DescriptorPushReady, emptyDescriptor,
    CompilerStackRep, DescriptorArraysRep, StoredDescriptors]
  all_goals
    constructor
    · simpa [CompilerStackRep, DescriptorWithinCursors] using hstack.2
    · constructor
      · simp [DescriptorWithinCursors]
      · omega

theorem pushEmptyAutomaton_spec (B maximumRank : Nat)
    (alphabet : RankedAlphabetCode) (n m : Nat)
    (stack : List AutomatonCode) :
    Spec B (EmptyAutomatonReady B maximumRank stack)
      pushEmptyAutomaton
      (fun _ sigma' => CompilerStackRep maximumRank
        (emptyCode (code alphabet n m) :: stack) sigma')
      160 := by
  intro sigma hready
  obtain ⟨sigma', hprepare, hpushReady⟩ :=
    (prepareEmptyAutomatonDescriptor_spec B maximumRank alphabet n m stack).run hready
  obtain ⟨sigma'', hpush, hstack⟩ :=
    (pushAutomatonDescriptor_spec B maximumRank
      (emptyCode (code alphabet n m)) stack (emptyDescriptor sigma)).run hpushReady
  exact ⟨sigma'', hprepare.seq hpush, hstack⟩

end Lax842588Proofs.MSORamCompilerEmpty
