import Lax842588Proofs.AutomatonRamArenaSegments
import Lax842588Proofs.RuntimeLayout
import Lax865980Proofs.Reasoning

/-!
Proof-private storage contract for the charged intrinsic-formula compiler.

Compiled automata are immutable append-only segments.  A small descriptor
records the state count and the locations of its transition and accepting
segments.  The physical descriptor stack is bottom-to-top, while the pure
postorder compiler uses a conventional head-as-top list; `CompilerStackRep`
states that reversal explicitly.

This is an evaluator layout, not a public representation of automata or
formulas.  It exists only inside the measured RAM execution.
-/

namespace Lax842588Proofs.MSORamCompilerStorage

open Lax865980Proofs.Imp
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamArenaSegments

/-- The fixed-width words occupied by the transitions of one immutable
compiled automaton.  The width is shared because marker extensions preserve
the ranks of the original alphabet. -/
def transitionWords (maximumRank : Nat) (M : AutomatonCode) : List Nat :=
  M.2.1.flatMap (encodeTransitionFixed maximumRank)

@[simp] theorem transitionWords_length (maximumRank : Nat)
    (M : AutomatonCode) :
    (transitionWords maximumRank M).length =
      M.2.1.length * (maximumRank + 3) := by
  simp [transitionWords, encodeTransitionFixed, List.length_flatMap]

/-- Five words suffice to locate a compiled automaton. -/
structure Descriptor where
  states : Nat
  transitionBase : Nat
  transitionCount : Nat
  acceptingBase : Nat
  acceptingCount : Nat
  deriving DecidableEq

@[ext] theorem Descriptor.ext {left right : Descriptor}
    (hstates : left.states = right.states)
    (htransitionBase : left.transitionBase = right.transitionBase)
    (htransitionCount : left.transitionCount = right.transitionCount)
    (hacceptingBase : left.acceptingBase = right.acceptingBase)
    (hacceptingCount : left.acceptingCount = right.acceptingCount) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Read the descriptor at a physical stack index. -/
def descriptorAt (sigma : Env) (i : Nat) : Descriptor where
  states := (sigma.arrs "AutomatonStatesStack").getD i 0
  transitionBase :=
    (sigma.arrs "AutomatonTransitionBaseStack").getD i 0
  transitionCount :=
    (sigma.arrs "AutomatonTransitionCountStack").getD i 0
  acceptingBase :=
    (sigma.arrs "AutomatonAcceptingBaseStack").getD i 0
  acceptingCount :=
    (sigma.arrs "AutomatonAcceptingCountStack").getD i 0

/-- Descriptor currently being assembled in scalar registers. -/
def preparedDescriptor (sigma : Env) : Descriptor where
  states := sigma.vars "newStates"
  transitionBase := sigma.vars "newTransitionBase"
  transitionCount := sigma.vars "newTransitionCount"
  acceptingBase := sigma.vars "newAcceptingBase"
  acceptingCount := sigma.vars "newAcceptingCount"

/-- Exact meaning of one descriptor in the two append-only heaps. -/
def StoresAutomaton (maximumRank : Nat)
    (transitionHeap acceptingHeap : List Nat)
    (descriptor : Descriptor) (M : AutomatonCode) : Prop :=
  descriptor.states = M.1 ∧
    descriptor.transitionCount = M.2.1.length ∧
    descriptor.acceptingCount = M.2.2.length ∧
    WordsAt transitionHeap descriptor.transitionBase
      (transitionWords maximumRank M) ∧
    WordsAt acceptingHeap descriptor.acceptingBase M.2.2

theorem storesAutomaton_transition_end {maximumRank : Nat}
    {transitionHeap acceptingHeap : List Nat} {descriptor : Descriptor}
    {M : AutomatonCode}
    (h : StoresAutomaton maximumRank transitionHeap acceptingHeap
      descriptor M) :
    descriptor.transitionBase +
        descriptor.transitionCount * (maximumRank + 3) =
      descriptor.transitionBase + (transitionWords maximumRank M).length := by
  rw [h.2.1, transitionWords_length]

theorem storesAutomaton_accepting_end {maximumRank : Nat}
    {transitionHeap acceptingHeap : List Nat} {descriptor : Descriptor}
    {M : AutomatonCode}
    (h : StoresAutomaton maximumRank transitionHeap acceptingHeap
      descriptor M) :
    descriptor.acceptingBase + descriptor.acceptingCount =
      descriptor.acceptingBase + M.2.2.length := by
  rw [h.2.2.1]

/-- Descriptor/code correspondence in physical bottom-to-top order. -/
def StoredDescriptors (maximumRank : Nat)
    (transitionHeap acceptingHeap : List Nat)
    (descriptors : List Descriptor) (stack : List AutomatonCode) : Prop :=
  List.Forall₂
    (StoresAutomaton maximumRank transitionHeap acceptingHeap)
    descriptors stack.reverse

/-- The five descriptor arrays contain a common prefix. -/
def DescriptorArraysRep (descriptors : List Descriptor)
    (sigma : Env) : Prop :=
  WordsAt (sigma.arrs "AutomatonStatesStack") 0
      (descriptors.map Descriptor.states) ∧
    WordsAt (sigma.arrs "AutomatonTransitionBaseStack") 0
      (descriptors.map Descriptor.transitionBase) ∧
    WordsAt (sigma.arrs "AutomatonTransitionCountStack") 0
      (descriptors.map Descriptor.transitionCount) ∧
    WordsAt (sigma.arrs "AutomatonAcceptingBaseStack") 0
      (descriptors.map Descriptor.acceptingBase) ∧
    WordsAt (sigma.arrs "AutomatonAcceptingCountStack") 0
      (descriptors.map Descriptor.acceptingCount)

/-- Both immutable segments named by a descriptor end no later than the
current append-only heap cursors.  This is the separation fact that makes it
safe to compile another subformula while older automata remain on the stack. -/
def DescriptorWithinCursors (maximumRank : Nat) (descriptor : Descriptor)
    (sigma : Env) : Prop :=
  descriptor.transitionBase +
        descriptor.transitionCount * (maximumRank + 3) ≤
      sigma.vars "compiledTransitionWords" ∧
    descriptor.acceptingBase + descriptor.acceptingCount ≤
      sigma.vars "compiledAcceptingWords"

/-- A physical stack stores the reverse of the pure compiler stack: physical
index zero is the bottom, and `automatonDepth - 1` is the logical head. -/
def CompilerStackRep (maximumRank : Nat) (stack : List AutomatonCode)
    (sigma : Env) : Prop :=
  sigma.vars "automatonDepth" = stack.length ∧
    ∃ descriptors,
      StoredDescriptors maximumRank
        (sigma.arrs "CompiledTransitions")
        (sigma.arrs "CompiledAccepting") descriptors stack ∧
      DescriptorArraysRep descriptors sigma ∧
      ∀ descriptor ∈ descriptors,
        DescriptorWithinCursors maximumRank descriptor sigma

/-- The complete footprint on which `CompilerStackRep` depends.  Arithmetic
row-generation commands can establish this relation from `Spec.frame` because
they touch only their private scalar variables and child buffer. -/
def CompilerStorageAgrees (sigma sigma' : Env) : Prop :=
  sigma'.vars "automatonDepth" = sigma.vars "automatonDepth" ∧
    sigma'.vars "compiledTransitionWords" =
      sigma.vars "compiledTransitionWords" ∧
    sigma'.vars "compiledAcceptingWords" =
      sigma.vars "compiledAcceptingWords" ∧
    sigma'.arrs "CompiledTransitions" = sigma.arrs "CompiledTransitions" ∧
    sigma'.arrs "CompiledAccepting" = sigma.arrs "CompiledAccepting" ∧
    sigma'.arrs "AutomatonStatesStack" = sigma.arrs "AutomatonStatesStack" ∧
    sigma'.arrs "AutomatonTransitionBaseStack" =
      sigma.arrs "AutomatonTransitionBaseStack" ∧
    sigma'.arrs "AutomatonTransitionCountStack" =
      sigma.arrs "AutomatonTransitionCountStack" ∧
    sigma'.arrs "AutomatonAcceptingBaseStack" =
      sigma.arrs "AutomatonAcceptingBaseStack" ∧
    sigma'.arrs "AutomatonAcceptingCountStack" =
      sigma.arrs "AutomatonAcceptingCountStack"

theorem compilerStackRep_of_agrees {maximumRank : Nat}
    {stack : List AutomatonCode} {sigma sigma' : Env}
    (hagrees : CompilerStorageAgrees sigma sigma')
    (hstack : CompilerStackRep maximumRank stack sigma) :
    CompilerStackRep maximumRank stack sigma' := by
  rcases hagrees with ⟨hdepth, htransitionCursor, hacceptingCursor,
    htransitionHeap, hacceptingHeap, hstates, htransitionBase,
    htransitionCount, hacceptingBase, hacceptingCount⟩
  rcases hstack with ⟨hstackDepth, descriptors, hstored, harrays, hwithin⟩
  refine ⟨hdepth.trans hstackDepth, descriptors, ?_, ?_, ?_⟩
  · simpa [htransitionHeap, hacceptingHeap] using hstored
  · simpa [DescriptorArraysRep, hstates, htransitionBase,
      htransitionCount, hacceptingBase, hacceptingCount] using harrays
  · intro descriptor hdescriptor
    simpa [DescriptorWithinCursors, htransitionCursor, hacceptingCursor] using
      hwithin descriptor hdescriptor

theorem descriptorAt_eq_of_arrays {descriptors : List Descriptor}
    {sigma : Env} (harrays : DescriptorArraysRep descriptors sigma)
    {i : Nat} (hi : i < descriptors.length) :
    descriptorAt sigma i = descriptors.get ⟨i, hi⟩ := by
  ext
  · simpa [descriptorAt, List.getD_eq_getElem, hi] using
      harrays.1 i (by simpa using hi)
  · simpa [descriptorAt, List.getD_eq_getElem, hi] using
      harrays.2.1 i (by simpa using hi)
  · simpa [descriptorAt, List.getD_eq_getElem, hi] using
      harrays.2.2.1 i (by simpa using hi)
  · simpa [descriptorAt, List.getD_eq_getElem, hi] using
      harrays.2.2.2.1 i (by simpa using hi)
  · simpa [descriptorAt, List.getD_eq_getElem, hi] using
      harrays.2.2.2.2 i (by simpa using hi)

/-- The descriptor at physical index `stack.length` represents the logical
top of a nonempty head-as-top compiler stack. -/
theorem compilerStackRep_top {maximumRank : Nat} {M : AutomatonCode}
    {stack : List AutomatonCode} {sigma : Env}
    (hstack : CompilerStackRep maximumRank (M :: stack) sigma) :
    StoresAutomaton maximumRank
      (sigma.arrs "CompiledTransitions")
      (sigma.arrs "CompiledAccepting")
      (descriptorAt sigma stack.length) M := by
  rcases hstack with ⟨_, descriptors, hstored, harrays, _⟩
  have hlength : descriptors.length = stack.length + 1 := by
    have := hstored.length_eq
    simpa [StoredDescriptors] using this
  have hiDescriptors : stack.length < descriptors.length := by omega
  have hiCodes : stack.length < (M :: stack).reverse.length := by simp
  have hrelation := hstored.get hiDescriptors hiCodes
  rw [descriptorAt_eq_of_arrays harrays hiDescriptors]
  simpa [StoredDescriptors, List.reverse_cons] using hrelation

/-- Pure environment change performed by popping one descriptor.  The five
descriptor arrays and both immutable heaps are left intact. -/
def popDescriptorEnv (sigma : Env) (depth : Nat) : Env :=
  sigma.setVar "automatonDepth" depth

/-- Dropping the logical head only shortens the represented descriptor
prefix; it does not erase or copy any automaton data. -/
theorem compilerStackRep_pop {maximumRank : Nat} {M : AutomatonCode}
    {stack : List AutomatonCode} {sigma : Env}
    (hstack : CompilerStackRep maximumRank (M :: stack) sigma) :
    CompilerStackRep maximumRank stack
      (popDescriptorEnv sigma stack.length) := by
  rcases hstack with ⟨hdepth, descriptors, hstored, harrays, hwithin⟩
  let kept := descriptors.take stack.length
  have hstoredTake := List.forall₂_take stack.length hstored
  have hstoredKept : StoredDescriptors maximumRank
      (sigma.arrs "CompiledTransitions")
      (sigma.arrs "CompiledAccepting") kept stack := by
    simpa [kept, StoredDescriptors, List.reverse_cons] using hstoredTake
  have harraysKept : DescriptorArraysRep kept sigma := by
    rcases harrays with ⟨hstates, htransitionBase, htransitionCount,
      hacceptingBase, hacceptingCount⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [kept] using wordsAt_take (count := stack.length) hstates
    · simpa [kept] using wordsAt_take (count := stack.length) htransitionBase
    · simpa [kept] using wordsAt_take (count := stack.length) htransitionCount
    · simpa [kept] using wordsAt_take (count := stack.length) hacceptingBase
    · simpa [kept] using wordsAt_take (count := stack.length) hacceptingCount
  have hwithinKept : ∀ descriptor ∈ kept,
      DescriptorWithinCursors maximumRank descriptor sigma := by
    intro descriptor hdescriptor
    exact hwithin descriptor (List.mem_of_mem_take hdescriptor)
  refine ⟨by simp [popDescriptorEnv], kept, ?_, ?_, ?_⟩
  · simpa [popDescriptorEnv] using hstoredKept
  · simpa [DescriptorArraysRep, popDescriptorEnv] using harraysKept
  · intro descriptor hdescriptor
    simpa [DescriptorWithinCursors, popDescriptorEnv] using
      hwithinKept descriptor hdescriptor

theorem compilerStackRep_nil_iff (maximumRank : Nat) (sigma : Env) :
    CompilerStackRep maximumRank [] sigma ↔
      sigma.vars "automatonDepth" = 0 := by
  constructor
  · exact fun h => h.1
  · intro hdepth
    refine ⟨hdepth, [], ?_, ?_, ?_⟩
    · exact .nil
    · simp [DescriptorArraysRep, WordsAt]
    · simp

theorem compilerStackRep_depth {maximumRank : Nat}
    {stack : List AutomatonCode} {sigma : Env}
    (h : CompilerStackRep maximumRank stack sigma) :
    sigma.vars "automatonDepth" = stack.length :=
  h.1

private theorem forall₂_append_singleton {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} {x : α} {y : β}
    (h : List.Forall₂ R xs ys) (hxy : R x y) :
    List.Forall₂ R (xs ++ [x]) (ys ++ [y]) := by
  induction h with
  | nil => exact .cons hxy .nil
  | cons hhead _ ih => exact .cons hhead ih

/-- Pure environment update performed by the five descriptor stores and the
depth increment. -/
def pushDescriptorEnv (sigma : Env) (i : Nat)
    (descriptor : Descriptor) : Env :=
  (((((sigma.setArr "AutomatonStatesStack" i descriptor.states).setArr
      "AutomatonTransitionBaseStack" i descriptor.transitionBase).setArr
      "AutomatonTransitionCountStack" i descriptor.transitionCount).setArr
      "AutomatonAcceptingBaseStack" i descriptor.acceptingBase).setArr
      "AutomatonAcceptingCountStack" i descriptor.acceptingCount).setVar
      "automatonDepth" (i + 1)

/-- Appending an immutable automaton and its descriptor is exactly a push on
the pure head-as-top stack. -/
theorem compilerStackRep_push {maximumRank : Nat}
    {stack : List AutomatonCode} {sigma : Env}
    (M : AutomatonCode) (descriptor : Descriptor)
    (hstack : CompilerStackRep maximumRank stack sigma)
    (hM : StoresAutomaton maximumRank
      (sigma.arrs "CompiledTransitions")
      (sigma.arrs "CompiledAccepting") descriptor M)
    (hwithin : DescriptorWithinCursors maximumRank descriptor sigma)
    (hstates : stack.length < (sigma.arrs "AutomatonStatesStack").length)
    (htransitionBase : stack.length <
      (sigma.arrs "AutomatonTransitionBaseStack").length)
    (htransitionCount : stack.length <
      (sigma.arrs "AutomatonTransitionCountStack").length)
    (hacceptingBase : stack.length <
      (sigma.arrs "AutomatonAcceptingBaseStack").length)
    (hacceptingCount : stack.length <
      (sigma.arrs "AutomatonAcceptingCountStack").length) :
    CompilerStackRep maximumRank (M :: stack)
      (pushDescriptorEnv sigma stack.length descriptor) := by
  rcases hstack with ⟨hdepth, descriptors, hstored, harrays, hwithinStack⟩
  have hdescriptorLength : descriptors.length = stack.length := by
    have hlength := hstored.length_eq
    simpa [StoredDescriptors] using hlength
  have hstored' := forall₂_append_singleton hstored hM
  have hstates' := wordsAt_set_append
    (value := descriptor.states) harrays.1 (by
      simpa [hdescriptorLength] using hstates)
  have htransitionBase' := wordsAt_set_append
    (value := descriptor.transitionBase) harrays.2.1
    (by simpa [hdescriptorLength] using htransitionBase)
  have htransitionCount' := wordsAt_set_append
    (value := descriptor.transitionCount) harrays.2.2.1
    (by simpa [hdescriptorLength] using htransitionCount)
  have hacceptingBase' := wordsAt_set_append
    (value := descriptor.acceptingBase) harrays.2.2.2.1
    (by simpa [hdescriptorLength] using hacceptingBase)
  have hacceptingCount' := wordsAt_set_append
    (value := descriptor.acceptingCount) harrays.2.2.2.2
    (by simpa [hdescriptorLength] using hacceptingCount)
  simp only [List.length_map, zero_add, hdescriptorLength] at hstates' htransitionBase' htransitionCount' hacceptingBase' hacceptingCount'
  refine ⟨by simp [pushDescriptorEnv], descriptors ++ [descriptor], ?_, ?_, ?_⟩
  · simpa [StoredDescriptors, List.reverse_cons, pushDescriptorEnv] using hstored'
  · simp only [DescriptorArraysRep, List.map_append, List.map_cons,
      List.map_nil]
    simpa [pushDescriptorEnv] using ⟨hstates', htransitionBase', htransitionCount',
      hacceptingBase', hacceptingCount'⟩
  · intro current hcurrent
    simp only [List.mem_append, List.mem_singleton] at hcurrent
    rcases hcurrent with hcurrent | rfl
    · simpa [DescriptorWithinCursors, pushDescriptorEnv] using
        hwithinStack current hcurrent
    · simpa [DescriptorWithinCursors, pushDescriptorEnv] using hwithin

/-- Heap cursors delimit the initialized append-only prefixes.  Stack
descriptors may point anywhere below these cursors; later operation-specific
invariants supply those bounds. -/
def CompilerHeapBounds (B : Nat) (sigma : Env) : Prop :=
  sigma.vars "compiledTransitionWords" ≤
      (sigma.arrs "CompiledTransitions").length ∧
    sigma.vars "compiledAcceptingWords" ≤
      (sigma.arrs "CompiledAccepting").length ∧
    (sigma.arrs "CompiledTransitions").length < B ∧
    (sigma.arrs "CompiledAccepting").length < B

end Lax842588Proofs.MSORamCompilerStorage
