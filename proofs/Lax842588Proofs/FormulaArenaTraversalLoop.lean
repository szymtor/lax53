import Lax842588Proofs.FormulaArenaTraversalBody

/-!
Counted-loop verification for the charged traversal of the original
intrinsically scoped MSO sentence.
-/

namespace Lax842588Proofs.FormulaArenaTraversalLoop

set_option maxHeartbeats 3000000
open Classical

open FirstOrder
open Lax146103.MSOSyntax
open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.ValueTranslations
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.FormulaArenaTraversalModel
open Lax842588Proofs.FormulaArenaTraversalOrder
open Lax842588Proofs.FormulaArenaTraversalInvariant
open Lax842588Proofs.FormulaArenaTraversalBody
open Lax842588Proofs.MSORamArenaProgram
open Lax560851.WordArena

/-- Proof-local name for the concrete nonempty formula-stack guard. -/
def formulaLoopCondition : Cond := .lt (.lit 0) (.var "formulaDepth")

theorem formulaLoopCondition_value (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (produced : List (Occurrence alphabet))
    (frames : List (TraversalFrame alphabet)) (sigma : Env)
    (hstate : FormulaLoopState B I alphabet phi produced frames sigma) :
    formulaLoopCondition.evalB B sigma = some (!frames.isEmpty) := by
  have hdepthB : frames.length < B :=
    hstate.frames_le_target.trans_lt hstate.targetLengthB
  have hvar : (Expr.var "formulaDepth").evalB B sigma =
      some frames.length := by
    rw [evalB_var_iff]
    exact ⟨hstate.depth.symm, by simpa [hstate.depth] using hdepthB⟩
  cases frames with
  | nil =>
      simpa [formulaLoopCondition] using
        (evalB_condLt (evalB_lit (by omega : 0 < B)) hvar)
  | cons frame outer =>
      simpa [formulaLoopCondition] using
        (evalB_condLt (evalB_lit (by omega : 0 < B)) hvar)

theorem formulaLoopCondition_defined (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    ∀ sigma, FormulaLoopInv B I alphabet phi sigma →
      ∃ value, formulaLoopCondition.evalB B sigma = some value := by
  intro sigma hInv
  rcases hInv with ⟨produced, frames, hstate⟩
  exact ⟨!frames.isEmpty,
    formulaLoopCondition_value B I alphabet phi produced frames sigma hstate⟩

/-- Machine-visible remaining work. The program increments `formulaSteps`
once per iteration, so no traversal bound is stored as input advice. -/
def formulaPotential (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (sigma : Env) : Nat :=
  traversalSteps alphabet phi - sigma.vars "formulaSteps"

theorem FormulaLoopState.potential_eq {B : Nat} {I : WordImage}
    {alphabet : RankedAlphabetCode}
    {phi : Sentence (treeSignature alphabet.toRankedAlphabet)}
    {produced : List (Occurrence alphabet)}
    {frames : List (TraversalFrame alphabet)} {sigma : Env}
    (h : FormulaLoopState B I alphabet phi produced frames sigma) :
    formulaPotential alphabet phi sigma = traversalWork alphabet frames := by
  unfold formulaPotential
  rw [← h.steps]
  omega

private theorem formulaTraversalBody_decreases (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (h2 : 2 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    Spec B
      (fun sigma => FormulaLoopInv B I alphabet phi sigma ∧
        formulaLoopCondition.evalB B sigma = some true)
      formulaTraversalBody
      (fun sigma sigma' => FormulaLoopInv B I alphabet phi sigma' ∧
        formulaPotential alphabet phi sigma' <
          formulaPotential alphabet phi sigma)
      600 := by
  intro sigma hpre
  rcases hpre.1 with ⟨produced, frames, hstate⟩
  have hcondition := formulaLoopCondition_value B I alphabet phi produced
    frames sigma hstate
  cases frames with
  | nil =>
      have hfalse : formulaLoopCondition.evalB B sigma = some false := by
        simpa using hcondition
      rw [hpre.2] at hfalse
      contradiction
  | cons frame outer =>
      have hbody := formulaTraversalBody_spec B I alphabet phi produced frame
        outer h2 hmemB hvaluesB htags
      obtain ⟨sigma', hrun, hstate'⟩ := hbody.run hstate
      refine ⟨sigma', hrun,
        ⟨(traversalStep alphabet (produced, frame :: outer)).1,
          (traversalStep alphabet (produced, frame :: outer)).2, hstate'⟩,
        ?_⟩
      rw [FormulaLoopState.potential_eq hstate,
        FormulaLoopState.potential_eq hstate']
      exact traversalStep_decreases alphabet produced frame outer

/-- Conservative total cost for the exact constructor-phase traversal. -/
def formulaTraversalLoopCost (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) : Nat :=
  (1 + formulaLoopCondition.size + 600) * traversalSteps alphabet phi +
    1 + formulaLoopCondition.size

theorem formulaTraversalLoop_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (h2 : 2 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    Spec B (FormulaLoopInv B I alphabet phi) formulaTraversalLoop
      (fun _ sigma' => FormulaLoopInv B I alphabet phi sigma' ∧
        formulaLoopCondition.evalB B sigma' = some false)
      (formulaTraversalLoopCost alphabet phi) := by
  unfold formulaTraversalLoop formulaTraversalLoopCost
  refine Spec.while_count
    (FormulaLoopInv B I alphabet phi)
    (formulaPotential alphabet phi) 600
    (formulaLoopCondition_defined B I alphabet phi)
    (formulaTraversalBody_decreases B I alphabet phi h2 hmemB hvaluesB htags)
    (fun _ hInv => hInv) ?_
  intro sigma hInv
  have hpotential : formulaPotential alphabet phi sigma ≤
      traversalSteps alphabet phi := by
    unfold formulaPotential
    omega
  have hmul := Nat.mul_le_mul_left
    (1 + formulaLoopCondition.size + 600) hpotential
  simpa only [Nat.add_assoc] using!
    Nat.add_le_add_right hmul (1 + formulaLoopCondition.size)

/-- At loop exit the postorder occurrence arrays are complete and the
charged step counter equals the semantic traversal count. -/
theorem formulaTraversalLoop_completed_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (h2 : 2 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    Spec B (FormulaLoopInv B I alphabet phi) formulaTraversalLoop
      (fun _ sigma' =>
        FormulaLoopInv B I alphabet phi sigma' ∧
          sigma'.vars "formulaCount" = (postorder alphabet phi).length ∧
          sigma'.vars "formulaSteps" = traversalSteps alphabet phi ∧
          sigma'.vars "formulaDepth" = 0 ∧
          FormulaOrderRep I alphabet (postorder alphabet phi)
            (sigma'.arrs "FormulaOrder") (sigma'.arrs "FormulaFOOrder")
            (sigma'.arrs "FormulaSOOrder"))
      (formulaTraversalLoopCost alphabet phi) := by
  refine (formulaTraversalLoop_spec B I alphabet phi h2 hmemB hvaluesB
    htags).post ?_
  intro sigma sigma' hpre hpost
  rcases hpost.1 with ⟨produced, frames, hstate⟩
  have hcondition := formulaLoopCondition_value B I alphabet phi produced
    frames sigma' hstate
  have hempty : frames = [] := by
    cases frames with
    | nil => rfl
    | cons frame outer =>
        have htrue : formulaLoopCondition.evalB B sigma' = some true := by
          simpa using hcondition
        rw [hpost.2] at htrue
        contradiction
  subst frames
  have hproduced : produced = postorder alphabet phi :=
    completed_eq_target alphabet (postorder alphabet phi) produced hstate.target
  subst produced
  refine ⟨⟨postorder alphabet phi, [], hstate⟩, hstate.count, ?_,
    hstate.depth, hstate.orderRep⟩
  simpa [traversalWork] using hstate.steps

end Lax842588Proofs.FormulaArenaTraversalLoop
