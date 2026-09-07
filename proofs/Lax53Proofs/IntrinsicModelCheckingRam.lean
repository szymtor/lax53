import Lax53Proofs.IntrinsicModelChecking
import Lax53Proofs.ImpLayout
import Lax13Proofs.Transfer

/-!
One fixed actual RAM program on the unchanged certified public input.
The explicit compiler, workspace, and word-fit premises remain to be
bounded by computable functions of the public mathematical parameter size.
-/

namespace Lax53Proofs.IntrinsicModelCheckingRam

open Classical
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile Lax13Proofs.Transfer
open Lax13.RamComputes
open Lax52.MSOSyntax Lax53.RankedTree Lax53.TreeStructure Lax53.ValueTranslations
open Lax53.MSOLinearTime Lax53.TreeModelCheckingEncoding Lax58.WordArena
open Lax53Proofs.ArenaSemantics Lax53Proofs.FormulaArenaTraversalModel
open Lax53Proofs.PrimitiveRecursiveCode Lax53Proofs.IntrinsicModelChecking

theorem exists_ram : ∃ (c : Code) (L : Layout),
    ∀ (B w : Nat) (alphabet : RankedAlphabetCode)
      (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
      (t : Tree alphabet.toRankedAlphabet),
    L.FitsWords B w → IntrinsicPublicCompiler.Fits c B alphabet φ →
    (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords < B →
    (∀ v ∈ arenaWords (encodeRaw (msoTreeRaw alphabet φ t)), v < B) →
    (∀ v ∈ encodeAutomaton (compiled alphabet φ), v < B) →
    (encodeAutomaton (compiled alphabet φ)).length < B →
    treeSize t * (compiled alphabet φ).2.2.1.length < B →
    (alphabet.length + (compiled alphabet φ).2.1 + (compiled alphabet φ).2.2.1.length +
      maximumRank alphabet + (compiled alphabet φ).2.2.1.length * (maximumRank alphabet + 3) +
      (compiled alphabet φ).2.2.2.length + treeSize t + 20 < B) →
    ComputesInTime w (compileProgram L (program c))
      {Lax53.MSOLinearTime.modelCheckingInput alphabet φ t}
      (fun _ => if t ∈ sentenceLanguage φ then [1] else [0])
      (fun _ => L.const * timeBound c alphabet φ t) := by
  obtain ⟨c, hc⟩ := exists_modelChecker
  obtain ⟨L, hok⟩ := ImpLayout.exists_layout (program c)
  refine ⟨c, L, fun B w alphabet φ t hfit hcompiler hmem hvalues hparameter hplen hstates hwork => ?_⟩
  have hsolves : Solves L (program c)
      {Lax53.MSOLinearTime.modelCheckingInput alphabet φ t}
      (fun _ => if t ∈ sentenceLanguage φ then [1] else [0])
      (fun _ => B) (fun _ => timeBound c alphabet φ t) := by
    refine ⟨hok, ?_, ?_⟩
    · intro x hx v hv
      have hx' : x = Lax53.MSOLinearTime.modelCheckingInput alphabet φ t := hx
      subst x
      simp only [Lax53.MSOLinearTime.modelCheckingInput, WordImage.toInput, List.mem_cons] at hv
      rcases hv with rfl | hv
      · have hr := Lax58Proofs.WordArena.encodeRaw_root_last (msoTreeRaw alphabet φ t)
        omega
      · exact hvalues v (by simpa [arenaWords] using hv)
    · intro x hx
      have hx' : x = Lax53.MSOLinearTime.modelCheckingInput alphabet φ t := hx
      subst x
      have hcount : (postorder alphabet φ).length < B :=
        (postorder_length_le_traversalSteps alphabet φ).trans_lt hcompiler.steps
      obtain ⟨τ, hrun, hout⟩ := hc B alphabet φ t hcompiler hmem hvalues hparameter
        hplen hstates hwork _ (initial_initEnv B alphabet φ t hplen hcount)
      refine ⟨workspaceExt alphabet φ t, τ, hrun, ?_⟩
      by_cases h : t ∈ sentenceLanguage φ <;> simpa [initEnv, h] using hout
  exact hsolves.computesInTime (fun _ _ => hfit)

end Lax53Proofs.IntrinsicModelCheckingRam
