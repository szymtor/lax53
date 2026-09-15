import Lax842588Proofs.FormulaArenaTraversalInvariant
import Lax560851Proofs.StructuralCombinators

/-!
Verification of one complete charged formula-traversal iteration.
-/

namespace Lax842588Proofs.FormulaArenaTraversalBody

set_option maxHeartbeats 3000000
open Classical

open FirstOrder
open Lax146103.MSOSyntax
open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.FormulaArenaTraversalModel
open Lax842588Proofs.FormulaArenaTraversalStack
open Lax842588Proofs.FormulaArenaTraversalOrder
open Lax842588Proofs.FormulaArenaTraversalLoad
open Lax842588Proofs.FormulaArenaTraversalEmit
open Lax842588Proofs.FormulaArenaTraversalUnary
open Lax842588Proofs.FormulaArenaTraversalOr
open Lax842588Proofs.FormulaArenaTraversalInvariant
open Lax842588Proofs.MSORamArenaProgram
open Lax560851.StructuralCombinators
open Lax560851.WordArena

private theorem constructorTag_ne {left right : String}
    (hnames : left ≠ right) :
    Raw.constructorNameCode left ≠ Raw.constructorNameCode right := by
  intro hcodes
  have hconstructors : Raw.constructor left [] = Raw.constructor right [] := by
    simp [Raw.constructor, hcodes]
  exact hnames (Lax560851Proofs.StructuralCombinators.constructor_eq_iff_proof.mp hconstructors).1

private def FormulaLoadedContext (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) (before after : Env) : Prop :=
  FormulaFrameLoaded B I alphabet current outer after ∧
    after.vars "formulaCount" = before.vars "formulaCount" ∧
    after.vars "formulaSteps" = before.vars "formulaSteps" ∧
    after.arrs "FormulaRootStack" = before.arrs "FormulaRootStack" ∧
    after.arrs "FormulaFOStack" = before.arrs "FormulaFOStack" ∧
    after.arrs "FormulaSOStack" = before.arrs "FormulaSOStack" ∧
    after.arrs "FormulaPhaseStack" = before.arrs "FormulaPhaseStack" ∧
    after.arrs "FormulaOrder" = before.arrs "FormulaOrder" ∧
    after.arrs "FormulaFOOrder" = before.arrs "FormulaFOOrder" ∧
    after.arrs "FormulaSOOrder" = before.arrs "FormulaSOOrder"

private def FormulaEmittedWithStep (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (produced : List (Occurrence alphabet))
    (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) (before after : Env) : Prop :=
  FormulaEmitted B I alphabet produced current outer after ∧
    after.vars "formulaSteps" = before.vars "formulaSteps"

private def FormulaEmitPhysical (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet))
    (before after : Env) : Prop :=
  ArenaLoaded I after ∧
    after.vars "formulaCount" =
      (produced ++ [current.occurrence]).length ∧
    after.vars "formulaSteps" = before.vars "formulaSteps" + 1 ∧
    after.vars "formulaDepth" = outer.length ∧
    FormulaOrderRep I alphabet (produced ++ [current.occurrence])
      (after.arrs "FormulaOrder") (after.arrs "FormulaFOOrder")
      (after.arrs "FormulaSOOrder") ∧
    FormulaStackRep I alphabet outer
      (after.arrs "FormulaRootStack") (after.arrs "FormulaFOStack")
      (after.arrs "FormulaSOStack") (after.arrs "FormulaPhaseStack")

private def FormulaPushedWithContext (P : Env → Prop)
    (before after : Env) : Prop :=
  P after ∧
    after.vars "formulaCount" = before.vars "formulaCount" ∧
    after.vars "formulaSteps" = before.vars "formulaSteps" ∧
    after.arrs "FormulaOrder" = before.arrs "FormulaOrder" ∧
    after.arrs "FormulaFOOrder" = before.arrs "FormulaFOOrder" ∧
    after.arrs "FormulaSOOrder" = before.arrs "FormulaSOOrder"

private def FormulaPushPhysical (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (frames : List (TraversalFrame alphabet))
    (before after : Env) : Prop :=
  ArenaLoaded I after ∧
    after.vars "formulaCount" = produced.length ∧
    after.vars "formulaSteps" = before.vars "formulaSteps" + 1 ∧
    after.vars "formulaDepth" = frames.length ∧
    FormulaOrderRep I alphabet produced
      (after.arrs "FormulaOrder") (after.arrs "FormulaFOOrder")
      (after.arrs "FormulaSOOrder") ∧
    FormulaStackRep I alphabet frames
      (after.arrs "FormulaRootStack") (after.arrs "FormulaFOStack")
      (after.arrs "FormulaSOStack") (after.arrs "FormulaPhaseStack")

private theorem frameReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet))
    (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) (sigma : Env)
    (hstate : FormulaLoopState B I alphabet phi produced
      (current :: outer) sigma) :
    FormulaFrameReady B I alphabet current outer sigma := by
  have hframes := hstate.frames_le_target
  have hscopes := hstate.current_scopes
  have hphase := hstate.current_phase
  exact ⟨hstate.arenaLoaded, hstate.depth,
    hframes.trans hstate.rootStackCapacity,
    hframes.trans hstate.foStackCapacity,
    hframes.trans hstate.soStackCapacity,
    hframes.trans hstate.phaseStackCapacity,
    hstate.rootStackLengthB, hstate.foStackLengthB,
    hstate.soStackLengthB, hstate.phaseStackLengthB,
    hscopes.1, hscopes.2, hphase, hstate.stackRep⟩

private theorem emitBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet))
    (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B)
    (hOr : Raw.constructorNameCode
      (constructorName current.occurrence.formula) ≠ orTag)
    (hNeg : Raw.constructorNameCode
      (constructorName current.occurrence.formula) ≠ negTag)
    (hExFO : Raw.constructorNameCode
      (constructorName current.occurrence.formula) ≠ exFOTag)
    (hExSO : Raw.constructorNameCode
      (constructorName current.occurrence.formula) ≠ exSOTag)
    (hstep : traversalStep alphabet (produced, current :: outer) =
      (produced ++ [current.occurrence], outer)) :
    Spec B
      (FormulaLoopState B I alphabet phi produced (current :: outer))
      formulaTraversalBody
      (fun sigma sigma' => FormulaStepPhysical I alphabet produced
        current outer sigma sigma')
      600 := by
  intro sigma hstate
  have hready : FormulaFrameReady B I alphabet current outer sigma :=
    frameReady B I alphabet phi produced current outer sigma hstate
  have hload0 := (loadFormulaFrame_spec B I alphabet current outer h1 hmemB
    hvaluesB).frame
  have hload : Spec B (FormulaFrameReady B I alphabet current outer)
      loadFormulaFrame
      (FormulaLoadedContext B I alphabet current outer) 100 :=
    hload0.post (Q' := FormulaLoadedContext B I alphabet current outer)
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaRootStack" (by decide),
        hpost.2.2.1 "FormulaFOStack" (by decide),
        hpost.2.2.1 "FormulaSOStack" (by decide),
        hpost.2.2.1 "FormulaPhaseStack" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hproduced := hstate.produced_lt_of_nonempty
  have htargetLengthB := hstate.targetLengthB
  have hcount := hstate.count
  have horder := hstate.orderRep
  have hproducedSuccB : produced.length + 1 < B := by
    omega
  have hrootOrderSpace : produced.length <
      (sigma.arrs "FormulaOrder").length :=
    hproduced.trans_le hstate.rootOrderCapacity
  have hfoOrderSpace : produced.length <
      (sigma.arrs "FormulaFOOrder").length :=
    hproduced.trans_le hstate.foOrderCapacity
  have hsoOrderSpace : produced.length <
      (sigma.arrs "FormulaSOOrder").length :=
    hproduced.trans_le hstate.soOrderCapacity
  have hrootOrderLengthB := hstate.rootOrderLengthB
  have hfoOrderLengthB := hstate.foOrderLengthB
  have hsoOrderLengthB := hstate.soOrderLengthB
  have hemit0 := (emitFormula_spec B I alphabet produced current outer).frame
  have hemit : Spec B (FormulaEmitReady B I alphabet produced current outer)
      emitFormula
      (FormulaEmittedWithStep B I alphabet produced current outer) 50 :=
    hemit0.post
      (Q' := FormulaEmittedWithStep B I alphabet produced current outer)
      (fun tau tau' _ hpost =>
        ⟨hpost.1, hpost.2.1 "formulaSteps" (by decide)⟩)
  rcases htags with ⟨horB, hnegB, hexFOB, hexSOB⟩
  have hwork := traversalStep_work alphabet produced current outer
  have hsteps := hstate.steps
  have hstepsB := hstate.traversalStepsB
  have hstepNextB : sigma.vars "formulaSteps" + 1 < B := by omega
  by_cases hphase : current.phase = 0
  · have hcurrentPhase : current.phase = 0 := hphase
    have hcore : Spec B (fun tau => tau = sigma) formulaTraversalBody
        (fun _ sigma' => FormulaEmitPhysical I alphabet produced current outer
          sigma sigma') 600 := by
      unfold formulaTraversalBody enterFormula revisitFormula
        Lax842588Proofs.AutomatonRamProgram.seqs
      run_vcg [hload, hemit]
      all_goals simp_all [FormulaEmitReady, FormulaEmitPhysical,
        FormulaLoadedContext, FormulaEmittedWithStep, FormulaEmitted,
        FormulaFrameLoaded, FormulaFrameReady,
        orTag, negTag,
        exFOTag, exSOTag, ArenaLoaded]
      all_goals try omega
    obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
    exact ⟨sigma', hrun, by
      unfold FormulaStepPhysical
      rw [hstep]
      exact hpost⟩
  · have hcore : Spec B (fun tau => tau = sigma) formulaTraversalBody
        (fun _ sigma' => FormulaEmitPhysical I alphabet produced current outer
          sigma sigma') 600 := by
      unfold formulaTraversalBody enterFormula revisitFormula
        Lax842588Proofs.AutomatonRamProgram.seqs
      run_vcg [hload, hemit]
      all_goals simp_all [FormulaEmitReady, FormulaEmitPhysical,
        FormulaLoadedContext, FormulaEmittedWithStep, FormulaEmitted,
        FormulaFrameLoaded, FormulaFrameReady,
        orTag, negTag,
        exFOTag, exSOTag, ArenaLoaded]
      all_goals try omega
    obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
    exact ⟨sigma', hrun, by
      unfold FormulaStepPhysical
      rw [hstep]
      exact hpost⟩

private theorem revisitEmitBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet))
    (current : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B)
    (hphase : current.phase ≠ 0)
    (hdone : Raw.constructorNameCode
        (constructorName current.occurrence.formula) = orTag →
      current.phase ≠ 1)
    (hstep : traversalStep alphabet (produced, current :: outer) =
      (produced ++ [current.occurrence], outer)) :
    Spec B
      (FormulaLoopState B I alphabet phi produced (current :: outer))
      formulaTraversalBody
      (fun sigma sigma' => FormulaStepPhysical I alphabet produced
        current outer sigma sigma')
      600 := by
  intro sigma hstate
  have hready : FormulaFrameReady B I alphabet current outer sigma :=
    frameReady B I alphabet phi produced current outer sigma hstate
  have hload0 := (loadFormulaFrame_spec B I alphabet current outer h1 hmemB
    hvaluesB).frame
  have hload : Spec B (FormulaFrameReady B I alphabet current outer)
      loadFormulaFrame
      (FormulaLoadedContext B I alphabet current outer) 100 :=
    hload0.post (Q' := FormulaLoadedContext B I alphabet current outer)
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaRootStack" (by decide),
        hpost.2.2.1 "FormulaFOStack" (by decide),
        hpost.2.2.1 "FormulaSOStack" (by decide),
        hpost.2.2.1 "FormulaPhaseStack" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hproduced := hstate.produced_lt_of_nonempty
  have htargetLengthB := hstate.targetLengthB
  have hcount := hstate.count
  have horder := hstate.orderRep
  have hproducedSuccB : produced.length + 1 < B := by omega
  have hrootOrderSpace : produced.length <
      (sigma.arrs "FormulaOrder").length :=
    hproduced.trans_le hstate.rootOrderCapacity
  have hfoOrderSpace : produced.length <
      (sigma.arrs "FormulaFOOrder").length :=
    hproduced.trans_le hstate.foOrderCapacity
  have hsoOrderSpace : produced.length <
      (sigma.arrs "FormulaSOOrder").length :=
    hproduced.trans_le hstate.soOrderCapacity
  have hrootOrderLengthB := hstate.rootOrderLengthB
  have hfoOrderLengthB := hstate.foOrderLengthB
  have hsoOrderLengthB := hstate.soOrderLengthB
  have hemit0 := (emitFormula_spec B I alphabet produced current outer).frame
  have hemit : Spec B (FormulaEmitReady B I alphabet produced current outer)
      emitFormula
      (FormulaEmittedWithStep B I alphabet produced current outer) 50 :=
    hemit0.post
      (Q' := FormulaEmittedWithStep B I alphabet produced current outer)
      (fun tau tau' _ hpost =>
        ⟨hpost.1, hpost.2.1 "formulaSteps" (by decide)⟩)
  rcases htags with ⟨horB, hnegB, hexFOB, hexSOB⟩
  have hwork := traversalStep_work alphabet produced current outer
  have hsteps := hstate.steps
  have hstepsB := hstate.traversalStepsB
  have hstepNextB : sigma.vars "formulaSteps" + 1 < B := by omega
  have hcore : Spec B (fun tau => tau = sigma) formulaTraversalBody
      (fun _ sigma' => FormulaEmitPhysical I alphabet produced current outer
        sigma sigma') 600 := by
    unfold formulaTraversalBody enterFormula revisitFormula
      Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg [hload, hemit]
    all_goals simp_all [FormulaEmitReady, FormulaEmitPhysical,
      FormulaLoadedContext, FormulaEmittedWithStep, FormulaEmitted,
      FormulaFrameLoaded, FormulaFrameReady, orTag, negTag,
      exFOTag, exSOTag, ArenaLoaded]
    all_goals try omega
  obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
  exact ⟨sigma', hrun, by
    unfold FormulaStepPhysical
    rw [hstep]
    exact hpost⟩

private theorem negPushBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet)) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    let current : TraversalFrame alphabet := ⟨⟨n, m, .neg body⟩, 0⟩
    Spec B
      (FormulaLoopState B I alphabet phi produced (current :: outer))
      formulaTraversalBody
      (fun sigma sigma' => FormulaStepPhysical I alphabet produced
        current outer sigma sigma')
      600 := by
  dsimp only
  intro sigma hstate
  let current : TraversalFrame alphabet := ⟨⟨n, m, .neg body⟩, 0⟩
  let nextFrames : List (TraversalFrame alphabet) :=
    initialFrame alphabet body :: ⟨⟨n, m, .neg body⟩, 1⟩ :: outer
  have hready : FormulaFrameReady B I alphabet current outer sigma :=
    frameReady B I alphabet phi produced current outer sigma hstate
  have hload0 := (loadFormulaFrame_spec B I alphabet current outer h1 hmemB
    hvaluesB).frame
  have hload : Spec B (FormulaFrameReady B I alphabet current outer)
      loadFormulaFrame
      (FormulaLoadedContext B I alphabet current outer) 100 :=
    hload0.post (Q' := FormulaLoadedContext B I alphabet current outer)
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaRootStack" (by decide),
        hpost.2.2.1 "FormulaFOStack" (by decide),
        hpost.2.2.1 "FormulaSOStack" (by decide),
        hpost.2.2.1 "FormulaPhaseStack" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hspace :
      (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
      (current :: outer).length <
        (sigma.arrs "FormulaPhaseStack").length := by
    apply hstate.stack_space_of_pending_gt
    simpa [current] using pending_gt_frames_neg alphabet body outer
  have hpush0 :=
    (pushNegBody_spec B I alphabet body outer h1 hmemB).frame
  have hpush : Spec B (NegPushReady B I alphabet body outer)
      (pushUnaryBody (.var "currentFO") (.var "currentSO"))
      (fun tau tau' => FormulaPushedWithContext
        (NegPushed B I alphabet body outer) tau tau') 150 :=
    hpush0.post
      (Q' := fun tau tau' => FormulaPushedWithContext
        (NegPushed B I alphabet body outer) tau tau')
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hcount := hstate.count
  have horder := hstate.orderRep
  have hwork := traversalStep_work alphabet produced current outer
  dsimp [current] at hwork
  have hsteps := hstate.steps
  have hstepsB := hstate.traversalStepsB
  have hstepNextB : sigma.vars "formulaSteps" + 1 < B := by omega
  rcases htags with ⟨horB, hnegB, hexFOB, hexSOB⟩
  have hnegOr : Raw.constructorNameCode "neg" ≠
      Raw.constructorNameCode "or" := constructorTag_ne (by decide)
  have hstep : traversalStep alphabet (produced, current :: outer) =
      (produced, nextFrames) := by
    simp [current, nextFrames, traversalStep, initialFrame]
  have hcore : Spec B (fun tau => tau = sigma) formulaTraversalBody
      (fun _ sigma' => FormulaPushPhysical I alphabet produced nextFrames
        sigma sigma') 600 := by
    unfold formulaTraversalBody enterFormula revisitFormula
      Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg [hload, hpush]
    all_goals simp_all [NegPushReady, FormulaPushPhysical,
      FormulaPushedWithContext, NegPushed, FormulaLoadedContext,
      FormulaFrameLoaded, FormulaFrameReady, current, nextFrames,
      constructorName, orTag, negTag, exFOTag, exSOTag, ArenaLoaded,
      initialFrame]
    all_goals try omega
  obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
  exact ⟨sigma', hrun, by
    unfold FormulaStepPhysical
    rw [hstep]
    exact hpost⟩

private theorem exFOPushBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet)) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    let current : TraversalFrame alphabet := ⟨⟨n, m, .exFO body⟩, 0⟩
    Spec B
      (FormulaLoopState B I alphabet phi produced (current :: outer))
      formulaTraversalBody
      (fun sigma sigma' => FormulaStepPhysical I alphabet produced
        current outer sigma sigma')
      600 := by
  dsimp only
  intro sigma hstate
  let current : TraversalFrame alphabet := ⟨⟨n, m, .exFO body⟩, 0⟩
  let nextFrames : List (TraversalFrame alphabet) :=
    initialFrame alphabet body :: ⟨⟨n, m, .exFO body⟩, 1⟩ :: outer
  have hready : FormulaFrameReady B I alphabet current outer sigma :=
    frameReady B I alphabet phi produced current outer sigma hstate
  have hload0 := (loadFormulaFrame_spec B I alphabet current outer h1 hmemB
    hvaluesB).frame
  have hload : Spec B (FormulaFrameReady B I alphabet current outer)
      loadFormulaFrame
      (FormulaLoadedContext B I alphabet current outer) 100 :=
    hload0.post (Q' := FormulaLoadedContext B I alphabet current outer)
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaRootStack" (by decide),
        hpost.2.2.1 "FormulaFOStack" (by decide),
        hpost.2.2.1 "FormulaSOStack" (by decide),
        hpost.2.2.1 "FormulaPhaseStack" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hspace :
      (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
      (current :: outer).length <
        (sigma.arrs "FormulaPhaseStack").length := by
    apply hstate.stack_space_of_pending_gt
    simpa [current] using pending_gt_frames_exFO alphabet body outer
  let child : Occurrence alphabet := ⟨n + 1, m, body⟩
  have hchildPost : child ∈ postorder alphabet body := by
    have hmem := occurrence_mem_framePending alphabet
      (initialFrame alphabet body)
    simpa [child] using! hmem
  have hchildPending : child ∈ pending alphabet (current :: outer) := by
    simp only [pending, List.flatMap_cons, List.mem_append]
    left
    simpa [current, child, framePending] using
      List.mem_append_left [⟨n, m, .exFO body⟩] hchildPost
  have hnSuccB : n + 1 < B :=
    (hstate.pending_scopes child hchildPending).1
  have hpush0 :=
    (pushExFOBody_spec B I alphabet body outer h1 hmemB).frame
  have hpush : Spec B (ExFOPushReady B I alphabet body outer)
      (pushUnaryBody (.add (.var "currentFO") (.lit 1))
        (.var "currentSO"))
      (fun tau tau' => FormulaPushedWithContext
        (ExFOPushed B I alphabet body outer) tau tau') 150 :=
    hpush0.post
      (Q' := fun tau tau' => FormulaPushedWithContext
        (ExFOPushed B I alphabet body outer) tau tau')
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hcount := hstate.count
  have horder := hstate.orderRep
  have hwork := traversalStep_work alphabet produced current outer
  dsimp [current] at hwork
  have hsteps := hstate.steps
  have hstepsB := hstate.traversalStepsB
  have hstepNextB : sigma.vars "formulaSteps" + 1 < B := by omega
  rcases htags with ⟨horB, hnegB, hexFOB, hexSOB⟩
  have hexFOOr : Raw.constructorNameCode "exFO" ≠
      Raw.constructorNameCode "or" := constructorTag_ne (by decide)
  have hexFONeg : Raw.constructorNameCode "exFO" ≠
      Raw.constructorNameCode "neg" := constructorTag_ne (by decide)
  have hstep : traversalStep alphabet (produced, current :: outer) =
      (produced, nextFrames) := by
    simp [current, nextFrames, traversalStep, initialFrame]
  have hcore : Spec B (fun tau => tau = sigma) formulaTraversalBody
      (fun _ sigma' => FormulaPushPhysical I alphabet produced nextFrames
        sigma sigma') 600 := by
    unfold formulaTraversalBody enterFormula revisitFormula
      Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg [hload, hpush]
    all_goals simp_all [ExFOPushReady, FormulaPushPhysical,
      FormulaPushedWithContext, ExFOPushed, FormulaLoadedContext,
      FormulaFrameLoaded, FormulaFrameReady, current, nextFrames,
      constructorName, orTag, negTag, exFOTag, exSOTag, ArenaLoaded,
      initialFrame]
    all_goals try omega
  obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
  exact ⟨sigma', hrun, by
    unfold FormulaStepPhysical
    rw [hstep]
    exact hpost⟩

private theorem exSOPushBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet)) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n (m + 1))
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    let current : TraversalFrame alphabet := ⟨⟨n, m, .exSO body⟩, 0⟩
    Spec B
      (FormulaLoopState B I alphabet phi produced (current :: outer))
      formulaTraversalBody
      (fun sigma sigma' => FormulaStepPhysical I alphabet produced
        current outer sigma sigma')
      600 := by
  dsimp only
  intro sigma hstate
  let current : TraversalFrame alphabet := ⟨⟨n, m, .exSO body⟩, 0⟩
  let nextFrames : List (TraversalFrame alphabet) :=
    initialFrame alphabet body :: ⟨⟨n, m, .exSO body⟩, 1⟩ :: outer
  have hready : FormulaFrameReady B I alphabet current outer sigma :=
    frameReady B I alphabet phi produced current outer sigma hstate
  have hload0 := (loadFormulaFrame_spec B I alphabet current outer h1 hmemB
    hvaluesB).frame
  have hload : Spec B (FormulaFrameReady B I alphabet current outer)
      loadFormulaFrame
      (FormulaLoadedContext B I alphabet current outer) 100 :=
    hload0.post (Q' := FormulaLoadedContext B I alphabet current outer)
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaRootStack" (by decide),
        hpost.2.2.1 "FormulaFOStack" (by decide),
        hpost.2.2.1 "FormulaSOStack" (by decide),
        hpost.2.2.1 "FormulaPhaseStack" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hspace :
      (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
      (current :: outer).length <
        (sigma.arrs "FormulaPhaseStack").length := by
    apply hstate.stack_space_of_pending_gt
    simpa [current] using pending_gt_frames_exSO alphabet body outer
  let child : Occurrence alphabet := ⟨n, m + 1, body⟩
  have hchildPost : child ∈ postorder alphabet body := by
    have hmem := occurrence_mem_framePending alphabet
      (initialFrame alphabet body)
    simpa [child] using! hmem
  have hchildPending : child ∈ pending alphabet (current :: outer) := by
    simp only [pending, List.flatMap_cons, List.mem_append]
    left
    simpa [current, child, framePending] using
      List.mem_append_left [⟨n, m, .exSO body⟩] hchildPost
  have hmSuccB : m + 1 < B :=
    (hstate.pending_scopes child hchildPending).2
  have hpush0 :=
    (pushExSOBody_spec B I alphabet body outer h1 hmemB).frame
  have hpush : Spec B (ExSOPushReady B I alphabet body outer)
      (pushUnaryBody (.var "currentFO")
        (.add (.var "currentSO") (.lit 1)))
      (fun tau tau' => FormulaPushedWithContext
        (ExSOPushed B I alphabet body outer) tau tau') 150 :=
    hpush0.post
      (Q' := fun tau tau' => FormulaPushedWithContext
        (ExSOPushed B I alphabet body outer) tau tau')
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hcount := hstate.count
  have horder := hstate.orderRep
  have hwork := traversalStep_work alphabet produced current outer
  dsimp [current] at hwork
  have hsteps := hstate.steps
  have hstepsB := hstate.traversalStepsB
  have hstepNextB : sigma.vars "formulaSteps" + 1 < B := by omega
  rcases htags with ⟨horB, hnegB, hexFOB, hexSOB⟩
  have hexSOOr : Raw.constructorNameCode "exSO" ≠
      Raw.constructorNameCode "or" := constructorTag_ne (by decide)
  have hexSONeg : Raw.constructorNameCode "exSO" ≠
      Raw.constructorNameCode "neg" := constructorTag_ne (by decide)
  have hexSOExFO : Raw.constructorNameCode "exSO" ≠
      Raw.constructorNameCode "exFO" := constructorTag_ne (by decide)
  have hstep : traversalStep alphabet (produced, current :: outer) =
      (produced, nextFrames) := by
    simp [current, nextFrames, traversalStep, initialFrame]
  have hcore : Spec B (fun tau => tau = sigma) formulaTraversalBody
      (fun _ sigma' => FormulaPushPhysical I alphabet produced nextFrames
        sigma sigma') 600 := by
    unfold formulaTraversalBody enterFormula revisitFormula
      Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg [hload, hpush]
    all_goals simp_all [ExSOPushReady, FormulaPushPhysical,
      FormulaPushedWithContext, ExSOPushed, FormulaLoadedContext,
      FormulaFrameLoaded, FormulaFrameReady, current, nextFrames,
      constructorName, orTag, negTag, exFOTag, exSOTag, ArenaLoaded,
      initialFrame]
    all_goals try omega
  obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
  exact ⟨sigma', hrun, by
    unfold FormulaStepPhysical
    rw [hstep]
    exact hpost⟩

private theorem orLeftPushBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet)) {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    let current : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 0⟩
    Spec B
      (FormulaLoopState B I alphabet phi produced (current :: outer))
      formulaTraversalBody
      (fun sigma sigma' => FormulaStepPhysical I alphabet produced
        current outer sigma sigma')
      600 := by
  dsimp only
  intro sigma hstate
  let current : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 0⟩
  let nextFrames : List (TraversalFrame alphabet) :=
    initialFrame alphabet left ::
      ⟨⟨n, m, .or left right⟩, 1⟩ :: outer
  have hready : FormulaFrameReady B I alphabet current outer sigma :=
    frameReady B I alphabet phi produced current outer sigma hstate
  have hload0 := (loadFormulaFrame_spec B I alphabet current outer h1 hmemB
    hvaluesB).frame
  have hload : Spec B (FormulaFrameReady B I alphabet current outer)
      loadFormulaFrame
      (FormulaLoadedContext B I alphabet current outer) 100 :=
    hload0.post (Q' := FormulaLoadedContext B I alphabet current outer)
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaRootStack" (by decide),
        hpost.2.2.1 "FormulaFOStack" (by decide),
        hpost.2.2.1 "FormulaSOStack" (by decide),
        hpost.2.2.1 "FormulaPhaseStack" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hspace :
      (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
      (current :: outer).length <
        (sigma.arrs "FormulaPhaseStack").length := by
    apply hstate.stack_space_of_pending_gt
    simpa [current] using pending_gt_frames_or_left alphabet left right outer
  have hpush0 :=
    (pushOrLeft_spec B I alphabet left right outer h1 hmemB).frame
  have hpush : Spec B (OrLeftReady B I alphabet left right outer)
      pushOrLeft
      (fun tau tau' => FormulaPushedWithContext
        (OrLeftPushed B I alphabet left right outer) tau tau') 150 :=
    hpush0.post
      (Q' := fun tau tau' => FormulaPushedWithContext
        (OrLeftPushed B I alphabet left right outer) tau tau')
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hcount := hstate.count
  have horder := hstate.orderRep
  have hwork := traversalStep_work alphabet produced current outer
  dsimp [current] at hwork
  have hsteps := hstate.steps
  have hstepsB := hstate.traversalStepsB
  have hstepNextB : sigma.vars "formulaSteps" + 1 < B := by omega
  rcases htags with ⟨horB, hnegB, hexFOB, hexSOB⟩
  have hstep : traversalStep alphabet (produced, current :: outer) =
      (produced, nextFrames) := by
    simp [current, nextFrames, traversalStep, initialFrame]
  have hcore : Spec B (fun tau => tau = sigma) formulaTraversalBody
      (fun _ sigma' => FormulaPushPhysical I alphabet produced nextFrames
        sigma sigma') 600 := by
    unfold formulaTraversalBody enterFormula revisitFormula
      Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg [hload, hpush]
    all_goals simp_all [OrLeftReady, FormulaPushPhysical,
      FormulaPushedWithContext, OrLeftPushed, FormulaLoadedContext,
      FormulaFrameLoaded, FormulaFrameReady, current, nextFrames,
      constructorName, orTag, negTag, exFOTag, exSOTag, ArenaLoaded,
      initialFrame]
    all_goals try omega
  obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
  exact ⟨sigma', hrun, by
    unfold FormulaStepPhysical
    rw [hstep]
    exact hpost⟩

private theorem orRightPushBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet)) {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (outer : List (TraversalFrame alphabet))
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    let current : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 1⟩
    Spec B
      (FormulaLoopState B I alphabet phi produced (current :: outer))
      formulaTraversalBody
      (fun sigma sigma' => FormulaStepPhysical I alphabet produced
        current outer sigma sigma')
      600 := by
  dsimp only
  intro sigma hstate
  let current : TraversalFrame alphabet := ⟨⟨n, m, .or left right⟩, 1⟩
  let nextFrames : List (TraversalFrame alphabet) :=
    initialFrame alphabet right ::
      ⟨⟨n, m, .or left right⟩, 2⟩ :: outer
  have hready : FormulaFrameReady B I alphabet current outer sigma :=
    frameReady B I alphabet phi produced current outer sigma hstate
  have hload0 := (loadFormulaFrame_spec B I alphabet current outer h1 hmemB
    hvaluesB).frame
  have hload : Spec B (FormulaFrameReady B I alphabet current outer)
      loadFormulaFrame
      (FormulaLoadedContext B I alphabet current outer) 100 :=
    hload0.post (Q' := FormulaLoadedContext B I alphabet current outer)
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaRootStack" (by decide),
        hpost.2.2.1 "FormulaFOStack" (by decide),
        hpost.2.2.1 "FormulaSOStack" (by decide),
        hpost.2.2.1 "FormulaPhaseStack" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hspace :
      (current :: outer).length < (sigma.arrs "FormulaRootStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaFOStack").length ∧
      (current :: outer).length < (sigma.arrs "FormulaSOStack").length ∧
      (current :: outer).length <
        (sigma.arrs "FormulaPhaseStack").length := by
    apply hstate.stack_space_of_pending_gt
    simpa [current] using pending_gt_frames_or_right alphabet left right outer
  have hpush0 :=
    (pushOrRight_spec B I alphabet left right outer h1 hmemB).frame
  have hpush : Spec B (OrRightReady B I alphabet left right outer)
      pushOrRight
      (fun tau tau' => FormulaPushedWithContext
        (OrRightPushed B I alphabet left right outer) tau tau') 175 :=
    hpush0.post
      (Q' := fun tau tau' => FormulaPushedWithContext
        (OrRightPushed B I alphabet left right outer) tau tau')
      (fun tau tau' _ hpost => ⟨hpost.1,
        hpost.2.1 "formulaCount" (by decide),
        hpost.2.1 "formulaSteps" (by decide),
        hpost.2.2.1 "FormulaOrder" (by decide),
        hpost.2.2.1 "FormulaFOOrder" (by decide),
        hpost.2.2.1 "FormulaSOOrder" (by decide)⟩)
  have hcount := hstate.count
  have horder := hstate.orderRep
  have hwork := traversalStep_work alphabet produced current outer
  dsimp [current] at hwork
  have hsteps := hstate.steps
  have hstepsB := hstate.traversalStepsB
  have hstepNextB : sigma.vars "formulaSteps" + 1 < B := by omega
  rcases htags with ⟨horB, hnegB, hexFOB, hexSOB⟩
  have hstep : traversalStep alphabet (produced, current :: outer) =
      (produced, nextFrames) := by
    simp [current, nextFrames, traversalStep, initialFrame]
  have hcore : Spec B (fun tau => tau = sigma) formulaTraversalBody
      (fun _ sigma' => FormulaPushPhysical I alphabet produced nextFrames
        sigma sigma') 600 := by
    unfold formulaTraversalBody enterFormula revisitFormula
      Lax842588Proofs.AutomatonRamProgram.seqs
    run_vcg [hload, hpush]
    all_goals simp_all [OrRightReady, FormulaPushPhysical,
      FormulaPushedWithContext, OrRightPushed, FormulaLoadedContext,
      FormulaFrameLoaded, FormulaFrameReady, current, nextFrames,
      constructorName, orTag, negTag, exFOTag, exSOTag, ArenaLoaded,
      initialFrame]
    all_goals try omega
  obtain ⟨sigma', hrun, hpost⟩ := hcore.run rfl
  exact ⟨sigma', hrun, by
    unfold FormulaStepPhysical
    rw [hstep]
    exact hpost⟩

/-- One charged imperative iteration implements exactly one transition of
the intrinsic phase-stack traversal. -/
theorem formulaTraversalBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet))
    (frame : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet))
    (h2 : 2 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    Spec B
      (FormulaLoopState B I alphabet phi produced (frame :: outer))
      formulaTraversalBody
      (fun _ sigma' => FormulaLoopState B I alphabet phi
        (traversalStep alphabet (produced, frame :: outer)).1
        (traversalStep alphabet (produced, frame :: outer)).2 sigma')
      600 := by
  intro sigma hstate
  have h1 : 1 < B := by omega
  have hphases := phasesFit_traversalStep B alphabet produced frame outer h2
    hstate.phasesFit
  rcases frame with ⟨⟨n, m, formula⟩, phase⟩
  cases formula with
  | falsum =>
      let current : TraversalFrame alphabet := ⟨⟨n, m, .falsum⟩, phase⟩
      have hOr : Raw.constructorNameCode "falsum" ≠ orTag := by
        simpa [orTag] using constructorTag_ne
          (left := "falsum") (right := "or") (by decide)
      have hNeg : Raw.constructorNameCode "falsum" ≠ negTag := by
        simpa [negTag] using constructorTag_ne
          (left := "falsum") (right := "neg") (by decide)
      have hExFO : Raw.constructorNameCode "falsum" ≠ exFOTag := by
        simpa [exFOTag] using constructorTag_ne
          (left := "falsum") (right := "exFO") (by decide)
      have hExSO : Raw.constructorNameCode "falsum" ≠ exSOTag := by
        simpa [exSOTag] using constructorTag_ne
          (left := "falsum") (right := "exSO") (by decide)
      have hstep : traversalStep alphabet (produced, current :: outer) =
          (produced ++ [current.occurrence], outer) := by
        simp [current, traversalStep]
      have hphysical := emitBody_spec B I alphabet phi produced current outer
        h1 hmemB hvaluesB htags (by simpa [current, constructorName] using hOr)
        (by simpa [current, constructorName] using hNeg)
        (by simpa [current, constructorName] using hExFO)
        (by simpa [current, constructorName] using hExSO) hstep
      obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
      exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
  | equal lhs rhs =>
      let current : TraversalFrame alphabet := ⟨⟨n, m, .equal lhs rhs⟩, phase⟩
      have hOr : Raw.constructorNameCode "equal" ≠ orTag := by
        simpa [orTag] using constructorTag_ne
          (left := "equal") (right := "or") (by decide)
      have hNeg : Raw.constructorNameCode "equal" ≠ negTag := by
        simpa [negTag] using constructorTag_ne
          (left := "equal") (right := "neg") (by decide)
      have hExFO : Raw.constructorNameCode "equal" ≠ exFOTag := by
        simpa [exFOTag] using constructorTag_ne
          (left := "equal") (right := "exFO") (by decide)
      have hExSO : Raw.constructorNameCode "equal" ≠ exSOTag := by
        simpa [exSOTag] using constructorTag_ne
          (left := "equal") (right := "exSO") (by decide)
      have hstep : traversalStep alphabet (produced, current :: outer) =
          (produced ++ [current.occurrence], outer) := by
        simp [current, traversalStep]
      have hphysical := emitBody_spec B I alphabet phi produced current outer
        h1 hmemB hvaluesB htags (by simpa [current, constructorName] using hOr)
        (by simpa [current, constructorName] using hNeg)
        (by simpa [current, constructorName] using hExFO)
        (by simpa [current, constructorName] using hExSO) hstep
      obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
      exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
  | rel relation terms =>
      let current : TraversalFrame alphabet := ⟨⟨n, m, .rel relation terms⟩, phase⟩
      have hOr : Raw.constructorNameCode "rel" ≠ orTag := by
        simpa [orTag] using constructorTag_ne
          (left := "rel") (right := "or") (by decide)
      have hNeg : Raw.constructorNameCode "rel" ≠ negTag := by
        simpa [negTag] using constructorTag_ne
          (left := "rel") (right := "neg") (by decide)
      have hExFO : Raw.constructorNameCode "rel" ≠ exFOTag := by
        simpa [exFOTag] using constructorTag_ne
          (left := "rel") (right := "exFO") (by decide)
      have hExSO : Raw.constructorNameCode "rel" ≠ exSOTag := by
        simpa [exSOTag] using constructorTag_ne
          (left := "rel") (right := "exSO") (by decide)
      have hstep : traversalStep alphabet (produced, current :: outer) =
          (produced ++ [current.occurrence], outer) := by
        simp [current, traversalStep]
      have hphysical := emitBody_spec B I alphabet phi produced current outer
        h1 hmemB hvaluesB htags (by simpa [current, constructorName] using hOr)
        (by simpa [current, constructorName] using hNeg)
        (by simpa [current, constructorName] using hExFO)
        (by simpa [current, constructorName] using hExSO) hstep
      obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
      exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
  | mem term setVar =>
      let current : TraversalFrame alphabet := ⟨⟨n, m, .mem term setVar⟩, phase⟩
      have hOr : Raw.constructorNameCode "mem" ≠ orTag := by
        simpa [orTag] using constructorTag_ne
          (left := "mem") (right := "or") (by decide)
      have hNeg : Raw.constructorNameCode "mem" ≠ negTag := by
        simpa [negTag] using constructorTag_ne
          (left := "mem") (right := "neg") (by decide)
      have hExFO : Raw.constructorNameCode "mem" ≠ exFOTag := by
        simpa [exFOTag] using constructorTag_ne
          (left := "mem") (right := "exFO") (by decide)
      have hExSO : Raw.constructorNameCode "mem" ≠ exSOTag := by
        simpa [exSOTag] using constructorTag_ne
          (left := "mem") (right := "exSO") (by decide)
      have hstep : traversalStep alphabet (produced, current :: outer) =
          (produced ++ [current.occurrence], outer) := by
        simp [current, traversalStep]
      have hphysical := emitBody_spec B I alphabet phi produced current outer
        h1 hmemB hvaluesB htags (by simpa [current, constructorName] using hOr)
        (by simpa [current, constructorName] using hNeg)
        (by simpa [current, constructorName] using hExFO)
        (by simpa [current, constructorName] using hExSO) hstep
      obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
      exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
  | neg body =>
      by_cases hzero : phase = 0
      · subst phase
        have hphysical := negPushBody_spec B I alphabet phi produced body outer
          h1 hmemB hvaluesB htags
        obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
        exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
      · let current : TraversalFrame alphabet := ⟨⟨n, m, .neg body⟩, phase⟩
        have hnegOr : Raw.constructorNameCode "neg" ≠ orTag := by
          simpa [orTag] using constructorTag_ne
            (left := "neg") (right := "or") (by decide)
        have hdone : Raw.constructorNameCode
              (constructorName current.occurrence.formula) = orTag →
            current.phase ≠ 1 := by
          intro heq
          exact False.elim (hnegOr (by
            simpa [current, constructorName] using heq))
        have hstep : traversalStep alphabet (produced, current :: outer) =
            (produced ++ [current.occurrence], outer) := by
          simp [current, traversalStep, hzero]
        have hphysical := revisitEmitBody_spec B I alphabet phi produced
          current outer h1 hmemB hvaluesB htags
          (by simpa [current] using hzero) hdone hstep
        obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
        exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
  | exFO body =>
      by_cases hzero : phase = 0
      · subst phase
        have hphysical := exFOPushBody_spec B I alphabet phi produced body outer
          h1 hmemB hvaluesB htags
        obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
        exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
      · let current : TraversalFrame alphabet := ⟨⟨n, m, .exFO body⟩, phase⟩
        have hexFOOr : Raw.constructorNameCode "exFO" ≠ orTag := by
          simpa [orTag] using constructorTag_ne
            (left := "exFO") (right := "or") (by decide)
        have hdone : Raw.constructorNameCode
              (constructorName current.occurrence.formula) = orTag →
            current.phase ≠ 1 := by
          intro heq
          exact False.elim (hexFOOr (by
            simpa [current, constructorName] using heq))
        have hstep : traversalStep alphabet (produced, current :: outer) =
            (produced ++ [current.occurrence], outer) := by
          simp [current, traversalStep, hzero]
        have hphysical := revisitEmitBody_spec B I alphabet phi produced
          current outer h1 hmemB hvaluesB htags
          (by simpa [current] using hzero) hdone hstep
        obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
        exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
  | exSO body =>
      by_cases hzero : phase = 0
      · subst phase
        have hphysical := exSOPushBody_spec B I alphabet phi produced body outer
          h1 hmemB hvaluesB htags
        obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
        exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
      · let current : TraversalFrame alphabet := ⟨⟨n, m, .exSO body⟩, phase⟩
        have hexSOOr : Raw.constructorNameCode "exSO" ≠ orTag := by
          simpa [orTag] using constructorTag_ne
            (left := "exSO") (right := "or") (by decide)
        have hdone : Raw.constructorNameCode
              (constructorName current.occurrence.formula) = orTag →
            current.phase ≠ 1 := by
          intro heq
          exact False.elim (hexSOOr (by
            simpa [current, constructorName] using heq))
        have hstep : traversalStep alphabet (produced, current :: outer) =
            (produced ++ [current.occurrence], outer) := by
          simp [current, traversalStep, hzero]
        have hphysical := revisitEmitBody_spec B I alphabet phi produced
          current outer h1 hmemB hvaluesB htags
          (by simpa [current] using hzero) hdone hstep
        obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
        exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
  | or left right =>
      by_cases hzero : phase = 0
      · subst phase
        have hphysical := orLeftPushBody_spec B I alphabet phi produced
          left right outer h1 hmemB hvaluesB htags
        obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
        exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
      · by_cases hone : phase = 1
        · subst phase
          have hphysical := orRightPushBody_spec B I alphabet phi produced
            left right outer h1 hmemB hvaluesB htags
          obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
          exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩
        · let current : TraversalFrame alphabet :=
            ⟨⟨n, m, .or left right⟩, phase⟩
          have hdone : Raw.constructorNameCode
                (constructorName current.occurrence.formula) = orTag →
              current.phase ≠ 1 := by
            intro _
            simpa [current] using hone
          have hstep : traversalStep alphabet (produced, current :: outer) =
              (produced ++ [current.occurrence], outer) := by
            simp [current, traversalStep, hzero, hone]
          have hphysical := revisitEmitBody_spec B I alphabet phi produced
            current outer h1 hmemB hvaluesB htags
            (by simpa [current] using hzero) hdone hstep
          obtain ⟨sigma', hrun, hpost⟩ := hphysical.run hstate
          exact ⟨sigma', hrun, hstate.after_step hphases hrun hpost⟩

end Lax842588Proofs.FormulaArenaTraversalBody
