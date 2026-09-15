import Lax842588Proofs.IntrinsicPublicCompiler
import Lax842588Proofs.IntrinsicEvaluatorPrepare
import Lax842588Proofs.IntrinsicSentenceCorrectness
import Lax842588Proofs.AutomatonRamBackend

/-!
The complete counted IMP body: certified public input, formula compilation,
tree materialization, automaton evaluation, and the satisfaction bit.
Word and workspace premises are explicit; the final RAM transfer and
parameter-size envelopes are separate obligations.
-/

namespace Lax842588Proofs.IntrinsicModelChecking

open Classical
open Lax865980Proofs.Imp Lax865980Proofs.Reasoning
open Lax146103.MSOSyntax Lax842588.RankedTree Lax842588.TreeStructure Lax842588.ValueTranslations
open Lax842588.MSOLinearTime Lax842588.TreeModelCheckingEncoding Lax560851.WordArena
open Lax842588Proofs.ArenaSemantics Lax842588Proofs.IntrinsicCompilerFields
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.PrimitiveRecursiveCode
open Lax842588Proofs.IntrinsicEvaluatorPrepare Lax842588Proofs.AutomatonRamBackend

def compiled (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) : EncodedAutomaton :=
  (alphabet, compileRows alphabet ((postorder alphabet φ).map fields))

def Initial (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) (σ : Env) : Prop :=
  IntrinsicCompilerPrepare.Initial B alphabet φ t σ ∧
    (σ.arrs "P").length = (encodeAutomaton (compiled alphabet φ)).length ∧
    Workspace (compiled alphabet φ) (treeSize t) σ

/-- Logical bounds for initially zero arrays. These lengths are not stored
in the machine, and no compiled table is present in its initial memory. -/
def workspaceExt (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) (a : String) : Nat :=
  if a ∈ IntrinsicCompilerPrepare.formulaArrays then (postorder alphabet φ).length
  else if a = "Arena" then (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords
  else if a = "P" then (encodeAutomaton (compiled alphabet φ)).length
  else if a = "W" ∨ a = "TreeSymbolStack" ∨ a = "TreeTailStack" ∨ a = "L" then treeSize t
  else if a = "S" then treeSize t * (compiled alphabet φ).2.2.1.length
  else if a = "O" then (compiled alphabet φ).2.2.1.length
  else 0

theorem initial_initEnv (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet)
    (hP : (encodeAutomaton (compiled alphabet φ)).length < B)
    (hcount : (postorder alphabet φ).length < B) :
    Initial B alphabet φ t (initEnv (workspaceExt alphabet φ t)
      (Lax842588.MSOLinearTime.modelCheckingInput alphabet φ t)) := by
  have hspace : alphabet.length + 4 ≤ (encodeAutomaton (compiled alphabet φ)).length := by
    rw [AutomatonTableEncoding.encodeAutomaton_length]
    dsimp [compiled]
    omega
  simp [Initial, IntrinsicCompilerPrepare.Initial, IntrinsicCompilerPrepare.Capacity,
    IntrinsicCompilerPrepare.formulaArrays, Workspace, workspaceExt, initEnv, hP, hcount, hspace]

def program (c : Code) : Com :=
  .seq (IntrinsicPublicCompiler.program c)
    (.seq IntrinsicEvaluatorPrepare.program automatonBackend)

def timeBound (c : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  IntrinsicPublicCompiler.timeBound c alphabet φ t +
    (IntrinsicEvaluatorPrepare.timeBound (compiled alphabet φ) t +
      automatonBackendCost (compiled alphabet φ) t)

set_option maxHeartbeats 3000000 in
theorem exists_modelChecker : ∃ c : Code, ∀ (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet),
    IntrinsicPublicCompiler.Fits c B alphabet φ →
    (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords < B →
    (∀ v ∈ arenaWords (encodeRaw (msoTreeRaw alphabet φ t)), v < B) →
    (∀ v ∈ encodeAutomaton (compiled alphabet φ), v < B) →
    (encodeAutomaton (compiled alphabet φ)).length < B →
    treeSize t * (compiled alphabet φ).2.2.1.length < B →
    (alphabet.length + (compiled alphabet φ).2.1 + (compiled alphabet φ).2.2.1.length +
      maximumRank alphabet + (compiled alphabet φ).2.2.1.length * (maximumRank alphabet + 3) +
      (compiled alphabet φ).2.2.2.length + treeSize t + 20 < B) →
    Spec B (Initial B alphabet φ t) (program c)
      (fun σ τ => τ.out = σ.out ++ [if t ∈ sentenceLanguage φ then 1 else 0])
      (timeBound c alphabet φ t) := by
  obtain ⟨c, hc⟩ := IntrinsicPublicCompiler.exists_compiler
  refine ⟨c, fun B alphabet φ t hfit hmem hvalues hparameter hplen hstates hwork => ?_⟩
  intro σ hσ
  obtain ⟨τ, hcompile, hP, harena, htree⟩ := hc B alphabet φ t hfit hmem hvalues
    σ ⟨hσ.1, hσ.2.1⟩
  have hworkspace : Workspace (compiled alphabet φ) (treeSize t) τ := by
    have hkeep (a : String) (ha : a ∈ ["W", "TreeSymbolStack", "TreeTailStack", "S", "L", "O"]) :=
      hcompile.frame_arr a (IntrinsicPublicCompiler.program_keeps_array c a ha)
    simpa only [Workspace, hkeep "W" (by simp), hkeep "TreeSymbolStack" (by simp),
      hkeep "TreeTailStack" (by simp), hkeep "S" (by simp), hkeep "L" (by simp),
      hkeep "O" (by simp)] using hσ.2.2
  have hready : Ready (encodeRaw (msoTreeRaw alphabet φ t)) (compiled alphabet φ) t τ :=
    ⟨harena, htree, hP, hworkspace⟩
  obtain ⟨υ, hprepare, hcontext⟩ := IntrinsicEvaluatorPrepare.program_spec B _
    (compiled alphabet φ) t (by have := hfit.eight; omega) hmem hvalues hparameter
    hstates hwork τ hready
  have hα : (compiled alphabet φ).1 = alphabet := rfl
  obtain ⟨ρ, hbackend, hout⟩ := automatonBackend_spec B (compiled alphabet φ) t
    (by have := hfit.eight; omega) (by have := hfit.eight; omega) hparameter hplen
    (by simpa only [hα] using! show treeSize t < B by omega) hstates hfit.width
    (by omega) (by omega) (by simpa only [hα] using show
      alphabet.length + 4 + (compiled alphabet φ).2.2.1.length * (maximumRank alphabet + 3) +
        (maximumRank alphabet + 3) < B by omega) υ hcontext
  have hout' : υ.out = σ.out :=
    (hprepare.out_eq IntrinsicEvaluatorPrepare.program_noWrite).trans
      (hcompile.out_eq (IntrinsicPublicCompiler.program_noWrite c))
  refine ⟨ρ, hcompile.seq (hprepare.seq hbackend), ?_⟩
  simpa only [hout', compiled, IntrinsicSentenceCorrectness.compileRows_sentence] using hout

end Lax842588Proofs.IntrinsicModelChecking
