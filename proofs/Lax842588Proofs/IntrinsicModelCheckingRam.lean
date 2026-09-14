import Lax842588Proofs.IntrinsicModelChecking
import Lax842588Proofs.ImpLayout
import Lax865980Proofs.Transfer

/-!
One fixed actual RAM program on the unchanged certified public input.
The explicit compiler, workspace, and word-fit premises remain to be
bounded by computable functions of the public mathematical parameter size.
-/

namespace Lax842588Proofs.IntrinsicModelCheckingRam

open Classical
open Lax865980Proofs.Imp Lax865980Proofs.Reasoning Lax865980Proofs.Compile Lax865980Proofs.Transfer
open Lax865980.RamComputes
open Lax146103.MSOSyntax Lax842588.RankedTree Lax842588.TreeStructure Lax842588.ValueTranslations
open Lax842588.MSOLinearTime Lax842588.TreeModelCheckingEncoding Lax560851.WordArena
open Lax842588Proofs.ArenaSemantics Lax842588Proofs.FormulaArenaTraversalModel
open Lax842588Proofs.PrimitiveRecursiveCode Lax842588Proofs.IntrinsicModelChecking

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
      {Lax842588.MSOLinearTime.modelCheckingInput alphabet φ t}
      (fun _ => if t ∈ sentenceLanguage φ then [1] else [0])
      (fun _ => L.const * timeBound c alphabet φ t) := by
  obtain ⟨c, hc⟩ := exists_modelChecker
  obtain ⟨L, hok⟩ := ImpLayout.exists_layout (program c)
  refine ⟨c, L, fun B w alphabet φ t hfit hcompiler hmem hvalues hparameter hplen hstates hwork => ?_⟩
  have hsolves : Solves L (program c)
      {Lax842588.MSOLinearTime.modelCheckingInput alphabet φ t}
      (fun _ => if t ∈ sentenceLanguage φ then [1] else [0])
      (fun _ => B) (fun _ => timeBound c alphabet φ t) := by
    refine ⟨hok, ?_, ?_⟩
    · intro x hx v hv
      have hx' : x = Lax842588.MSOLinearTime.modelCheckingInput alphabet φ t := hx
      subst x
      simp only [Lax842588.MSOLinearTime.modelCheckingInput, WordImage.toInput, List.mem_cons] at hv
      rcases hv with rfl | hv
      · have hr := Lax560851Proofs.WordArena.encodeRaw_root_last (msoTreeRaw alphabet φ t)
        omega
      · exact hvalues v (by simpa [arenaWords] using hv)
    · intro x hx
      have hx' : x = Lax842588.MSOLinearTime.modelCheckingInput alphabet φ t := hx
      subst x
      have hcount : (postorder alphabet φ).length < B :=
        (postorder_length_le_traversalSteps alphabet φ).trans_lt hcompiler.steps
      obtain ⟨τ, hrun, hout⟩ := hc B alphabet φ t hcompiler hmem hvalues hparameter
        hplen hstates hwork _ (initial_initEnv B alphabet φ t hplen hcount)
      refine ⟨workspaceExt alphabet φ t, τ, hrun, ?_⟩
      by_cases h : t ∈ sentenceLanguage φ <;> simpa [initEnv, h] using hout
  exact hsolves.computesInTime (fun _ _ => hfit)

end Lax842588Proofs.IntrinsicModelCheckingRam
