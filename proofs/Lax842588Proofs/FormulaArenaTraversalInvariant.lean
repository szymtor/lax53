import Lax842588Proofs.FormulaArenaTraversalOr
import Lax842588Proofs.ImpArrayLengths

/-!
The complete semantic/physical invariant for the charged traversal of the
original intrinsic formula.  No formula code is introduced: the logical
state consists only of occurrences of `Lax146103.MSOSyntax.Formula`, their
intrinsic scope indices, and certified addresses in the input arena.
-/

namespace Lax842588Proofs.FormulaArenaTraversalInvariant

set_option maxHeartbeats 3000000
open Classical

open FirstOrder
open Lax146103.MSOSyntax
open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.FormulaArenaTraversalModel
open Lax842588Proofs.FormulaArenaTraversalStack
open Lax842588Proofs.FormulaArenaTraversalOrder
open Lax842588Proofs.FormulaArenaTraversalInit
open Lax842588Proofs.MSORamArenaProgram
open Lax560851.WordArena

/-- The four fixed symbolic tag literals occurring in the dispatch program
fit in a machine word.  This is a program constant, not input advice. -/
def FormulaTagBounds (B : Nat) : Prop :=
  orTag < B ∧ negTag < B ∧ exFOTag < B ∧ exSOTag < B

/-- Every scope index that the traversal will materialize fits in a word. -/
def FormulaScopesFit (B : Nat) (alphabet : RankedAlphabetCode)
    (occurrences : List (Occurrence alphabet)) : Prop :=
  ∀ occurrence ∈ occurrences, occurrence.fo < B ∧ occurrence.so < B

/-- Phase values in the live stack fit in a word. -/
def FormulaPhasesFit (B : Nat) (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) : Prop :=
  ∀ frame ∈ frames, frame.phase < B

/-- A fully related imperative/pure traversal state.  The equation involving
`formulaSteps` charges exactly one counter increment per semantic transition;
the program does not receive the total traversal count as input. -/
structure FormulaLoopState (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet))
    (frames : List (TraversalFrame alphabet)) (sigma : Env) : Prop where
  arenaLoaded : ArenaLoaded I sigma
  targetLengthB : (postorder alphabet phi).length < B
  traversalStepsB : traversalSteps alphabet phi < B
  rootOrderCapacity : (postorder alphabet phi).length ≤
    (sigma.arrs "FormulaOrder").length
  foOrderCapacity : (postorder alphabet phi).length ≤
    (sigma.arrs "FormulaFOOrder").length
  soOrderCapacity : (postorder alphabet phi).length ≤
    (sigma.arrs "FormulaSOOrder").length
  rootStackCapacity : (postorder alphabet phi).length ≤
    (sigma.arrs "FormulaRootStack").length
  foStackCapacity : (postorder alphabet phi).length ≤
    (sigma.arrs "FormulaFOStack").length
  soStackCapacity : (postorder alphabet phi).length ≤
    (sigma.arrs "FormulaSOStack").length
  phaseStackCapacity : (postorder alphabet phi).length ≤
    (sigma.arrs "FormulaPhaseStack").length
  rootOrderLengthB : (sigma.arrs "FormulaOrder").length < B
  foOrderLengthB : (sigma.arrs "FormulaFOOrder").length < B
  soOrderLengthB : (sigma.arrs "FormulaSOOrder").length < B
  rootStackLengthB : (sigma.arrs "FormulaRootStack").length < B
  foStackLengthB : (sigma.arrs "FormulaFOStack").length < B
  soStackLengthB : (sigma.arrs "FormulaSOStack").length < B
  phaseStackLengthB : (sigma.arrs "FormulaPhaseStack").length < B
  count : sigma.vars "formulaCount" = produced.length
  steps : sigma.vars "formulaSteps" + traversalWork alphabet frames =
    traversalSteps alphabet phi
  depth : sigma.vars "formulaDepth" = frames.length
  orderRep : FormulaOrderRep I alphabet produced
    (sigma.arrs "FormulaOrder") (sigma.arrs "FormulaFOOrder")
    (sigma.arrs "FormulaSOOrder")
  stackRep : FormulaStackRep I alphabet frames
    (sigma.arrs "FormulaRootStack") (sigma.arrs "FormulaFOStack")
    (sigma.arrs "FormulaSOStack") (sigma.arrs "FormulaPhaseStack")
  target : produced ++ pending alphabet frames = postorder alphabet phi
  scopesFit : FormulaScopesFit B alphabet (postorder alphabet phi)
  phasesFit : FormulaPhasesFit B alphabet frames

def FormulaLoopInv (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (sigma : Env) : Prop :=
  ∃ produced frames, FormulaLoopState B I alphabet phi produced frames sigma

/-- The machine-visible facts produced by one charged body execution.  The
semantic successor is fixed to `traversalStep`; the generic lifting theorem
below supplies all capacity and pure-model fields of `FormulaLoopState`. -/
def FormulaStepPhysical (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (frame : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet))
    (sigma sigma' : Env) : Prop :=
  ArenaLoaded I sigma' ∧
    sigma'.vars "formulaCount" =
      (traversalStep alphabet (produced, frame :: outer)).1.length ∧
    sigma'.vars "formulaSteps" = sigma.vars "formulaSteps" + 1 ∧
    sigma'.vars "formulaDepth" =
      (traversalStep alphabet (produced, frame :: outer)).2.length ∧
    FormulaOrderRep I alphabet
      (traversalStep alphabet (produced, frame :: outer)).1
      (sigma'.arrs "FormulaOrder") (sigma'.arrs "FormulaFOOrder")
      (sigma'.arrs "FormulaSOOrder") ∧
    FormulaStackRep I alphabet
      (traversalStep alphabet (produced, frame :: outer)).2
      (sigma'.arrs "FormulaRootStack") (sigma'.arrs "FormulaFOStack")
      (sigma'.arrs "FormulaSOStack") (sigma'.arrs "FormulaPhaseStack")

theorem FormulaLoopState.target_length {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {phi : Sentence (treeSignature alphabet.toRankedAlphabet)}
    {produced : List (Occurrence alphabet)}
    {frames : List (TraversalFrame alphabet)} {sigma : Env}
    (h : FormulaLoopState B I alphabet phi produced frames sigma) :
    produced.length + (pending alphabet frames).length =
      (postorder alphabet phi).length := by
  have hlength := congrArg List.length h.target
  simpa using hlength

theorem FormulaLoopState.frames_le_target {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {phi : Sentence (treeSignature alphabet.toRankedAlphabet)}
    {produced : List (Occurrence alphabet)}
    {frames : List (TraversalFrame alphabet)} {sigma : Env}
    (h : FormulaLoopState B I alphabet phi produced frames sigma) :
    frames.length ≤ (postorder alphabet phi).length := by
  have hpending := pending_length_ge_frames alphabet frames
  have hlength := h.target_length
  omega

theorem FormulaLoopState.produced_lt_of_nonempty {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {phi : Sentence (treeSignature alphabet.toRankedAlphabet)}
    {produced : List (Occurrence alphabet)}
    {frame : TraversalFrame alphabet}
    {outer : List (TraversalFrame alphabet)} {sigma : Env}
    (h : FormulaLoopState B I alphabet phi produced (frame :: outer) sigma) :
    produced.length < (postorder alphabet phi).length := by
  have hpending := pending_length_ge_frames alphabet (frame :: outer)
  have hlength := h.target_length
  simp only [List.length_cons] at hpending
  omega

theorem FormulaLoopState.current_scopes {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {phi : Sentence (treeSignature alphabet.toRankedAlphabet)}
    {produced : List (Occurrence alphabet)}
    {frame : TraversalFrame alphabet}
    {outer : List (TraversalFrame alphabet)} {sigma : Env}
    (h : FormulaLoopState B I alphabet phi produced (frame :: outer) sigma) :
    frame.occurrence.fo < B ∧ frame.occurrence.so < B := by
  apply h.scopesFit frame.occurrence
  rw [← h.target]
  simp only [List.mem_append]
  exact Or.inr (current_mem_pending alphabet frame outer)

theorem FormulaLoopState.pending_scopes {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {phi : Sentence (treeSignature alphabet.toRankedAlphabet)}
    {produced : List (Occurrence alphabet)}
    {frames : List (TraversalFrame alphabet)} {sigma : Env}
    (h : FormulaLoopState B I alphabet phi produced frames sigma)
    (occurrence : Occurrence alphabet)
    (hmem : occurrence ∈ pending alphabet frames) :
    occurrence.fo < B ∧ occurrence.so < B := by
  apply h.scopesFit occurrence
  rw [← h.target]
  exact List.mem_append_right produced hmem

theorem FormulaLoopState.current_phase {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {phi : Sentence (treeSignature alphabet.toRankedAlphabet)}
    {produced : List (Occurrence alphabet)}
    {frame : TraversalFrame alphabet}
    {outer : List (TraversalFrame alphabet)} {sigma : Env}
    (h : FormulaLoopState B I alphabet phi produced (frame :: outer) sigma) :
    frame.phase < B :=
  h.phasesFit frame (by simp)

theorem FormulaLoopState.after_step {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {phi : Sentence (treeSignature alphabet.toRankedAlphabet)}
    {produced : List (Occurrence alphabet)}
    {frame : TraversalFrame alphabet}
    {outer : List (TraversalFrame alphabet)} {sigma sigma' : Env}
    {cost : Nat}
    (h : FormulaLoopState B I alphabet phi produced (frame :: outer) sigma)
    (hphases : FormulaPhasesFit B alphabet
      (traversalStep alphabet (produced, frame :: outer)).2)
    (hrun : Run B formulaTraversalBody sigma sigma' cost)
    (hphysical : FormulaStepPhysical I alphabet produced frame outer
      sigma sigma') :
    FormulaLoopState B I alphabet phi
      (traversalStep alphabet (produced, frame :: outer)).1
      (traversalStep alphabet (produced, frame :: outer)).2 sigma' := by
  rcases hphysical with ⟨hphysicalArena, hphysicalCount, hphysicalSteps,
    hphysicalDepth, hphysicalOrder, hphysicalStack⟩
  have hrootOrderLength := Lax842588Proofs.Run.arrayLength_eq hrun "FormulaOrder"
  have hfoOrderLength := Lax842588Proofs.Run.arrayLength_eq hrun "FormulaFOOrder"
  have hsoOrderLength := Lax842588Proofs.Run.arrayLength_eq hrun "FormulaSOOrder"
  have hrootStackLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun "FormulaRootStack"
  have hfoStackLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun "FormulaFOStack"
  have hsoStackLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun "FormulaSOStack"
  have hphaseStackLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun "FormulaPhaseStack"
  have htarget := traversalStep_preserves_pending alphabet produced
    (frame :: outer)
  have hwork := traversalStep_work alphabet produced frame outer
  have hsteps := h.steps
  refine {
    arenaLoaded := hphysicalArena
    targetLengthB := h.targetLengthB
    traversalStepsB := h.traversalStepsB
    rootOrderCapacity := by
      simpa [hrootOrderLength] using h.rootOrderCapacity
    foOrderCapacity := by
      simpa [hfoOrderLength] using h.foOrderCapacity
    soOrderCapacity := by
      simpa [hsoOrderLength] using h.soOrderCapacity
    rootStackCapacity := by
      simpa [hrootStackLength] using h.rootStackCapacity
    foStackCapacity := by
      simpa [hfoStackLength] using h.foStackCapacity
    soStackCapacity := by
      simpa [hsoStackLength] using h.soStackCapacity
    phaseStackCapacity := by
      simpa [hphaseStackLength] using h.phaseStackCapacity
    rootOrderLengthB := by
      simpa [hrootOrderLength] using h.rootOrderLengthB
    foOrderLengthB := by
      simpa [hfoOrderLength] using h.foOrderLengthB
    soOrderLengthB := by
      simpa [hsoOrderLength] using h.soOrderLengthB
    rootStackLengthB := by
      simpa [hrootStackLength] using h.rootStackLengthB
    foStackLengthB := by
      simpa [hfoStackLength] using h.foStackLengthB
    soStackLengthB := by
      simpa [hsoStackLength] using h.soStackLengthB
    phaseStackLengthB := by
      simpa [hphaseStackLength] using h.phaseStackLengthB
    count := hphysicalCount
    steps := by omega
    depth := hphysicalDepth
    orderRep := hphysicalOrder
    stackRep := hphysicalStack
    target := htarget.trans h.target
    scopesFit := h.scopesFit
    phasesFit := hphases
  }

theorem pending_gt_frames_neg (alphabet : RankedAlphabetCode) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet)) :
    (⟨⟨n, m, .neg body⟩, 0⟩ :: outer :
        List (TraversalFrame alphabet)).length <
      (pending alphabet (⟨⟨n, m, .neg body⟩, 0⟩ :: outer)).length := by
  have hbody : 0 < (postorder alphabet body).length :=
    List.length_pos_of_ne_nil (postorder_ne_nil alphabet body)
  have houter := pending_length_ge_frames alphabet outer
  simp only [pending] at houter
  simp only [pending, List.flatMap_cons, framePending_neg, if_pos,
    List.length_cons, List.length_append]
  omega

theorem pending_gt_frames_exFO (alphabet : RankedAlphabetCode) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m)
    (outer : List (TraversalFrame alphabet)) :
    (⟨⟨n, m, .exFO body⟩, 0⟩ :: outer :
        List (TraversalFrame alphabet)).length <
      (pending alphabet (⟨⟨n, m, .exFO body⟩, 0⟩ :: outer)).length := by
  have hbody : 0 < (postorder alphabet body).length :=
    List.length_pos_of_ne_nil (postorder_ne_nil alphabet body)
  have houter := pending_length_ge_frames alphabet outer
  simp only [pending] at houter
  simp only [pending, List.flatMap_cons, framePending_exFO, if_pos,
    List.length_cons, List.length_append]
  omega

theorem pending_gt_frames_exSO (alphabet : RankedAlphabetCode) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n (m + 1))
    (outer : List (TraversalFrame alphabet)) :
    (⟨⟨n, m, .exSO body⟩, 0⟩ :: outer :
        List (TraversalFrame alphabet)).length <
      (pending alphabet (⟨⟨n, m, .exSO body⟩, 0⟩ :: outer)).length := by
  have hbody : 0 < (postorder alphabet body).length :=
    List.length_pos_of_ne_nil (postorder_ne_nil alphabet body)
  have houter := pending_length_ge_frames alphabet outer
  simp only [pending] at houter
  simp only [pending, List.flatMap_cons, framePending_exSO, if_pos,
    List.length_cons, List.length_append]
  omega

theorem pending_gt_frames_or_left (alphabet : RankedAlphabetCode) {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet)) :
    (⟨⟨n, m, .or left right⟩, 0⟩ :: outer :
        List (TraversalFrame alphabet)).length <
      (pending alphabet
        (⟨⟨n, m, .or left right⟩, 0⟩ :: outer)).length := by
  have hleft : 0 < (postorder alphabet left).length :=
    List.length_pos_of_ne_nil (postorder_ne_nil alphabet left)
  have houter := pending_length_ge_frames alphabet outer
  simp only [pending] at houter
  simp only [pending, List.flatMap_cons, framePending_or, if_pos,
    List.length_cons, List.length_append]
  omega

theorem pending_gt_frames_or_right (alphabet : RankedAlphabetCode) {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet)) :
    (⟨⟨n, m, .or left right⟩, 1⟩ :: outer :
        List (TraversalFrame alphabet)).length <
      (pending alphabet
        (⟨⟨n, m, .or left right⟩, 1⟩ :: outer)).length := by
  have hright : 0 < (postorder alphabet right).length :=
    List.length_pos_of_ne_nil (postorder_ne_nil alphabet right)
  have houter := pending_length_ge_frames alphabet outer
  simp only [pending] at houter
  simp only [pending, List.flatMap_cons, framePending_or, if_neg Nat.one_ne_zero,
    if_pos, List.length_cons, List.length_append]
  omega

theorem FormulaLoopState.stack_space_of_pending_gt {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {phi : Sentence (treeSignature alphabet.toRankedAlphabet)}
    {produced : List (Occurrence alphabet)}
    {frames : List (TraversalFrame alphabet)} {sigma : Env}
    (h : FormulaLoopState B I alphabet phi produced frames sigma)
    (hpending : frames.length < (pending alphabet frames).length) :
    frames.length < (sigma.arrs "FormulaRootStack").length ∧
      frames.length < (sigma.arrs "FormulaFOStack").length ∧
    frames.length < (sigma.arrs "FormulaSOStack").length ∧
      frames.length < (sigma.arrs "FormulaPhaseStack").length := by
  have hlength := h.target_length
  have hframesTarget : frames.length < (postorder alphabet phi).length := by
    omega
  exact ⟨hframesTarget.trans_le h.rootStackCapacity,
    hframesTarget.trans_le h.foStackCapacity,
    hframesTarget.trans_le h.soStackCapacity,
    hframesTarget.trans_le h.phaseStackCapacity⟩

theorem phasesFit_traversalStep (B : Nat) (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (frame : TraversalFrame alphabet) (outer : List (TraversalFrame alphabet))
    (h2 : 2 < B)
    (hfit : FormulaPhasesFit B alphabet (frame :: outer)) :
    FormulaPhasesFit B alphabet
      (traversalStep alphabet (produced, frame :: outer)).2 := by
  rcases frame with ⟨⟨n, m, formula⟩, phase⟩
  have h0 : 0 < B := by omega
  have h1 : 1 < B := by omega
  have houter : FormulaPhasesFit B alphabet outer := by
    intro outerFrame hmem
    exact hfit outerFrame (by simp [hmem])
  cases formula with
  | falsum => simpa [traversalStep] using houter
  | equal => simpa [traversalStep] using houter
  | rel => simpa [traversalStep] using houter
  | mem => simpa [traversalStep] using houter
  | or left right =>
      by_cases hzero : phase = 0
      · subst phase
        simpa [traversalStep, FormulaPhasesFit, initialFrame, h0, h1, h2]
          using houter
      · by_cases hone : phase = 1
        · subst phase
          simpa [traversalStep, FormulaPhasesFit, initialFrame, h0, h1, h2]
            using houter
        · simpa [traversalStep, hzero, hone] using houter
  | neg body =>
      by_cases hzero : phase = 0
      · subst phase
        simpa [traversalStep, FormulaPhasesFit, initialFrame, h0, h1, h2]
          using houter
      · simpa [traversalStep, hzero] using houter
  | exFO body =>
      by_cases hzero : phase = 0
      · subst phase
        simpa [traversalStep, FormulaPhasesFit, initialFrame, h0, h1, h2]
          using houter
      · simpa [traversalStep, hzero] using houter
  | exSO body =>
      by_cases hzero : phase = 0
      · subst phase
        simpa [traversalStep, FormulaPhasesFit, initialFrame, h0, h1, h2]
          using houter
      · simpa [traversalStep, hzero] using houter

/-- The charged initializer establishes the exact pure traversal state once
the caller supplies the preallocated seven formula arrays. -/
theorem initialized_loopState (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (sigma : Env)
    (hinit : FormulaTraversalInitialized B I alphabet phi sigma)
    (htargetB : (postorder alphabet phi).length < B)
    (hstepsB : traversalSteps alphabet phi < B)
    (hrootOrderCapacity : (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaOrder").length)
    (hfoOrderCapacity : (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaFOOrder").length)
    (hsoOrderCapacity : (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaSOOrder").length)
    (hrootStackCapacity : (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaRootStack").length)
    (hfoStackCapacity : (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaFOStack").length)
    (hsoStackCapacity : (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaSOStack").length)
    (hphaseStackCapacity : (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaPhaseStack").length)
    (hrootOrderLengthB : (sigma.arrs "FormulaOrder").length < B)
    (hfoOrderLengthB : (sigma.arrs "FormulaFOOrder").length < B)
    (hsoOrderLengthB : (sigma.arrs "FormulaSOOrder").length < B)
    (hscopes : FormulaScopesFit B alphabet (postorder alphabet phi)) :
    FormulaLoopState B I alphabet phi [] [initialFrame alphabet phi] sigma := by
  rcases hinit with ⟨hloaded, hcount, hsteps, hdepth,
    hrootStackLengthB, hfoStackLengthB, hsoStackLengthB,
    hphaseStackLengthB, hstack⟩
  have htargetPos : 0 < (postorder alphabet phi).length :=
    List.length_pos_of_ne_nil (postorder_ne_nil alphabet phi)
  have hB0 : 0 < B := by omega
  refine {
    arenaLoaded := hloaded
    targetLengthB := htargetB
    traversalStepsB := hstepsB
    rootOrderCapacity := hrootOrderCapacity
    foOrderCapacity := hfoOrderCapacity
    soOrderCapacity := hsoOrderCapacity
    rootStackCapacity := hrootStackCapacity
    foStackCapacity := hfoStackCapacity
    soStackCapacity := hsoStackCapacity
    phaseStackCapacity := hphaseStackCapacity
    rootOrderLengthB := hrootOrderLengthB
    foOrderLengthB := hfoOrderLengthB
    soOrderLengthB := hsoOrderLengthB
    rootStackLengthB := hrootStackLengthB
    foStackLengthB := hfoStackLengthB
    soStackLengthB := hsoStackLengthB
    phaseStackLengthB := hphaseStackLengthB
    count := by simpa using hcount
    steps := by
      rw [hsteps]
      simp [traversalWork]
    depth := by simpa using hdepth
    orderRep := formulaOrderRep_nil I alphabet _ _ _
    stackRep := hstack
    target := by simp
    scopesFit := hscopes
    phasesFit := by simp [FormulaPhasesFit, initialFrame, hB0]
  }

end Lax842588Proofs.FormulaArenaTraversalInvariant
