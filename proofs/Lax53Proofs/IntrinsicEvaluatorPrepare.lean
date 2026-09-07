import Lax53Proofs.IntrinsicEvaluatorHeader
import Lax53Proofs.AutomatonRamArenaReadTree

/-! Read the retained input tree and initialize the runtime-built automaton's evaluator. -/

namespace Lax53Proofs.IntrinsicEvaluatorPrepare

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax53.RankedTree Lax53.ValueTranslations Lax53.StructuralRepresentations
open Lax53.TreeModelCheckingEncoding Lax58.WordArena
open Lax53Proofs.ArenaSemantics Lax53Proofs.AutomatonRamArenaCorrectness
open Lax53Proofs.AutomatonRamCorrectness Lax53Proofs.AutomatonRamArenaReadTree

def Workspace (M : EncodedAutomaton) (n : Nat) (σ : Env) : Prop :=
  (σ.arrs "W").length = n ∧
    (σ.arrs "TreeSymbolStack").length = n ∧
    (σ.arrs "TreeTailStack").length = n ∧
    σ.arrs "S" = List.replicate (n * M.2.2.1.length) 0 ∧
    σ.arrs "L" = List.replicate n 0 ∧
    (σ.arrs "O").length = M.2.2.1.length

def Ready (I : WordImage) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (σ : Env) : Prop :=
  ArenaLoaded I σ ∧ I.Represents (σ.vars "treeRoot") (treeStructure M.1 t) ∧
    σ.arrs "P" = encodeAutomaton M ∧ Workspace M (treeSize t) σ

def program : Com :=
  .seq AutomatonRamArenaProgram.readTree IntrinsicEvaluatorHeader.program

def timeBound (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) : Nat :=
  readTreeCost M.1 t + 100

set_option maxHeartbeats 1500000 in
theorem program_spec (B : Nat) (I : WordImage) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (h1 : 1 < B) (hmem : I.memoryWords < B)
    (hvalues : ∀ v ∈ arenaWords I, v < B)
    (hparameter : ∀ v ∈ encodeAutomaton M, v < B)
    (hstates : treeSize t * M.2.2.1.length < B)
    (hwork : M.1.length + M.2.1 + M.2.2.1.length + maximumRank M.1 +
      M.2.2.1.length * (maximumRank M.1 + 3) + M.2.2.2.length + treeSize t + 20 < B) :
    Spec B (Ready I M t) program
      (fun _ σ => EvaluateTreeContext B M (encodeTree M.1 t) σ) (timeBound M t) := by
  intro σ hσ
  obtain ⟨ha, htree, hP, hW, hsymbol, htail, hS, hL, hO⟩ := hσ
  have hr : TreeReadReady B I M.1 t (σ.vars "treeRoot") σ :=
    ⟨ha, rfl, htree, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega⟩
  obtain ⟨τ, hread, _, hn, _, hwords⟩ := readTree_spec B I M.1 t _ h1 hmem hvalues
    (by omega) σ hr
  have hP' : τ.arrs "P" = encodeAutomaton M :=
    (hread.frame_arr "P" (by decide)).trans hP
  obtain ⟨υ, hheader, hfields⟩ := IntrinsicEvaluatorHeader.program_spec B M (treeSize t)
    (by omega) hparameter hwork τ ⟨hP', hn⟩
  have hrun := hread.seq hheader
  have hWlen : (υ.arrs "W").length = (encodeTree M.1 t).length := by
    rw [Lax53Proofs.Run.arrayLength_eq hrun "W", hW, encodeTree_length]
  have hWexact : υ.arrs "W" = encodeTree M.1 t := by
    apply List.ext_getElem hWlen
    intro i hi hj
    rw [← List.getD_eq_getElem (υ.arrs "W") 0 hi,
      hheader.frame_arr "W" (by simp),
      ← List.getD_eq_getElem (encodeTree M.1 t) 0 hj]
    simpa using hwords i hj
  have hkeep (a : String) (ha : a ∈ ["S", "L", "O"]) : υ.arrs a = σ.arrs a := by
    apply hrun.frame_arr a
    have hh : a ∉ AutomatonRamArenaProgram.readTree.warrs := by
      simp at ha
      rcases ha with rfl | rfl | rfl <;> decide
    simpa [Com.warrs] using hh
  refine ⟨υ, hrun, ?_, hWexact, ?_, ?_, ?_, ?_⟩
  · simpa [encodeTree_length] using hfields
  · simpa [hkeep "S" (by simp), encodeTree_length] using hS
  · simpa [hkeep "L" (by simp), encodeTree_length] using hL
  · simpa [hkeep "O" (by simp)] using hO
  · simpa [hWlen, encodeTree_length] using hstates

theorem program_noRead : ¬ program.reads := by decide
theorem program_noWrite : program.NoWrite := by decide

end Lax53Proofs.IntrinsicEvaluatorPrepare
