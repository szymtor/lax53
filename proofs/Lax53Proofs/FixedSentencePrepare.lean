import Lax53Proofs.FixedTableLoader
import Lax53Proofs.IntrinsicEvaluatorPrepare
import Lax53Proofs.ImpArrayLengths
import Lax58Proofs.WordArena

/-! Tree-only input preparation for a fixed automaton embedded in the program. -/

namespace Lax53Proofs.FixedSentencePrepare

open Encodable Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax53.RankedTree Lax53.ValueTranslations Lax53.StructuralRepresentations
open Lax53.TreeModelCheckingEncoding Lax58.WordArena
open Lax53Proofs.IntrinsicEvaluatorPrepare Lax53Proofs.AutomatonRamArenaCorrectness

def program (M : EncodedAutomaton) : Com :=
  .seq (FixedTableLoader.program (encodeAutomaton M))
    (.seq AutomatonRamArenaProgram.readArena (.assign "treeRoot" (.var "root")))

def timeBound (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) : Nat :=
  FixedTableLoader.timeBound (encodeAutomaton M) +
    (12 * (encodeRaw (treeStructure M.1 t)).memoryWords + 20 + 2)

def Initial (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) (σ : Env) : Prop :=
  (σ.arrs "P").length = (encodeAutomaton M).length ∧
    (σ.arrs "Arena").length = (encodeRaw (treeStructure M.1 t)).memoryWords ∧
    σ.inp = (encodeRaw (treeStructure M.1 t)).toInput ∧ Workspace M (treeSize t) σ

theorem program_spec (B : Nat) (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet)
    (htable : 2 * encode (encodeAutomaton M) + 3 < B)
    (hmem : (encodeRaw (treeStructure M.1 t)).memoryWords < B)
    (hvalues : ∀ v ∈ (encodeRaw (treeStructure M.1 t)).toInput, v < B) :
    Spec B (Initial M t) (program M)
      (fun _ σ => Ready (encodeRaw (treeStructure M.1 t)) M t σ) (timeBound M t) := by
  intro σ hσ
  obtain ⟨hP, hA, hi, hW⟩ := hσ
  obtain ⟨τ, hload, htable'⟩ := FixedTableLoader.program_spec B (encodeAutomaton M) htable σ hP
  obtain ⟨υ, hread, ha⟩ := readArena_spec B (treeStructure M.1 t) hmem hvalues τ
    ⟨by rw [Lax53Proofs.Run.arrayLength_eq hload "Arena"]; exact hA,
      (hload.frame_inp (FixedTableLoader.program_noRead _)).trans hi⟩
  have hrB : υ.vars "root" < B := by
    rw [ha.2.1]
    have := Lax58Proofs.WordArena.encodeRaw_root_last (treeStructure M.1 t)
    omega
  have hset : Run B (.assign "treeRoot" (.var "root")) υ
      (υ.setVar "treeRoot" (υ.vars "root")) 2 :=
    Run.assign (by simp [Expr.evalB, fit_self hrB])
  have hrun := hload.seq (hread.seq hset)
  have hkeep (a : String) (ha : a ∈ ["W", "TreeSymbolStack", "TreeTailStack", "S", "L", "O"]) :
      (υ.setVar "treeRoot" (υ.vars "root")).arrs a = σ.arrs a := by
    apply hrun.frame_arr a
    simp only [Com.warrs, FixedTableLoader.program_warrs, List.mem_append,
      List.mem_singleton, List.not_mem_nil, or_false, not_or]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨_, hrun, ?_, ?_, ?_, ?_⟩
  · simpa [ArenaLoaded] using ha
  · have hrep := Lax58Proofs.WordArena.encodeRaw_represents_proof (treeStructure M.1 t)
    simpa [ha.2.1] using hrep
  · exact (hread.frame_arr "P" (by decide)).trans htable'
  · simpa only [Workspace, hkeep "W" (by simp), hkeep "TreeSymbolStack" (by simp),
      hkeep "TreeTailStack" (by simp), hkeep "S" (by simp), hkeep "L" (by simp),
      hkeep "O" (by simp)] using hW

theorem program_noWrite (M : EncodedAutomaton) : (program M).NoWrite := by
  simp [program, Com.NoWrite, FixedTableLoader.program_noWrite]
  decide

end Lax53Proofs.FixedSentencePrepare
