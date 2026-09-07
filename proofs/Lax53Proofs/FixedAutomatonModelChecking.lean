import Lax53Proofs.FixedSentencePrepare
import Lax53Proofs.AutomatonRamBackend
import Lax53Proofs.ImpLayout
import Lax13Proofs.Transfer
import Lax53.MSOLinearTime

/-! Counted execution of a fixed automaton on a tree-only certified arena. -/

namespace Lax53Proofs.FixedAutomatonModelChecking

open Classical Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax13Proofs.Compile Lax13Proofs.Transfer Lax13.RamComputes
open Lax53.RankedTree Lax53.ValueTranslations Lax53.StructuralRepresentations
open Lax53.TreeModelCheckingEncoding Lax58.WordArena
open Lax53Proofs.IntrinsicEvaluatorPrepare Lax53Proofs.AutomatonRamCorrectness
open Lax53Proofs.AutomatonRamBackend

def program (M : EncodedAutomaton) : Com :=
  .seq (FixedSentencePrepare.program M)
    (.seq IntrinsicEvaluatorPrepare.program automatonBackend)

def timeBound (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) : Nat :=
  FixedSentencePrepare.timeBound M t +
    (IntrinsicEvaluatorPrepare.timeBound M t + automatonBackendCost M t)

theorem program_spec (B : Nat) (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet)
    (htable : 2 * Encodable.encode (encodeAutomaton M) + 3 < B)
    (hmem : (encodeRaw (treeStructure M.1 t)).memoryWords < B)
    (hvalues : ∀ v ∈ (encodeRaw (treeStructure M.1 t)).toInput, v < B)
    (hparameter : ∀ v ∈ encodeAutomaton M, v < B)
    (hlen : (encodeAutomaton M).length < B)
    (hstates : treeSize t * M.2.2.1.length < B)
    (hwork : M.1.length + M.2.1 + M.2.2.1.length + maximumRank M.1 +
      M.2.2.1.length * (maximumRank M.1 + 3) + M.2.2.2.length + treeSize t + 20 < B) :
    Spec B (FixedSentencePrepare.Initial M t) (program M)
      (fun σ τ => τ.out = σ.out ++ [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0])
      (timeBound M t) := by
  intro σ hσ
  obtain ⟨τ, hstart, hready⟩ := FixedSentencePrepare.program_spec B M t htable hmem hvalues σ hσ
  have harena : ∀ v ∈ ArenaSemantics.arenaWords (encodeRaw (treeStructure M.1 t)), v < B := by
    intro v hv
    apply hvalues v
    exact List.mem_cons_of_mem _ hv
  obtain ⟨υ, hprepare, hcontext⟩ := IntrinsicEvaluatorPrepare.program_spec B
    (encodeRaw (treeStructure M.1 t)) M t (by omega) hmem harena hparameter
    hstates hwork τ hready
  obtain ⟨ρ, hbackend, hout⟩ := automatonBackend_spec B M t (by omega) (by omega)
    hparameter hlen (by omega) hstates (by omega) (by omega) (by omega) (by omega) υ hcontext
  have hout' : υ.out = σ.out :=
    (hprepare.out_eq IntrinsicEvaluatorPrepare.program_noWrite).trans
      (hstart.out_eq (FixedSentencePrepare.program_noWrite M))
  exact ⟨ρ, hstart.seq (hprepare.seq hbackend), by simpa only [hout'] using hout⟩

def workspaceExt (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) (a : String) : Nat :=
  if a = "Arena" then (encodeRaw (treeStructure M.1 t)).memoryWords
  else if a = "P" then (encodeAutomaton M).length
  else if a = "W" ∨ a = "TreeSymbolStack" ∨ a = "TreeTailStack" ∨ a = "L" then treeSize t
  else if a = "S" then treeSize t * M.2.2.1.length
  else if a = "O" then M.2.2.1.length
  else 0

theorem initial_initEnv (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) :
    FixedSentencePrepare.Initial M t
      (initEnv (workspaceExt M t) (Lax53.MSOLinearTime.treeInput M.1 t)) := by
  simp [FixedSentencePrepare.Initial, Workspace, workspaceExt, initEnv, Lax53.MSOLinearTime.treeInput]

theorem exists_ram (M : EncodedAutomaton) : ∃ L : Layout,
    ∀ (B w : Nat) (t : Tree M.1.toRankedAlphabet),
    L.FitsWords B w →
    2 * Encodable.encode (encodeAutomaton M) + 3 < B →
    (encodeRaw (treeStructure M.1 t)).memoryWords < B →
    (∀ v ∈ (encodeRaw (treeStructure M.1 t)).toInput, v < B) →
    (∀ v ∈ encodeAutomaton M, v < B) →
    (encodeAutomaton M).length < B →
    treeSize t * M.2.2.1.length < B →
    (M.1.length + M.2.1 + M.2.2.1.length + maximumRank M.1 +
      M.2.2.1.length * (maximumRank M.1 + 3) + M.2.2.2.length + treeSize t + 20 < B) →
    ComputesInTime w (compileProgram L (program M)) {Lax53.MSOLinearTime.treeInput M.1 t}
      (fun _ => [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0])
      (fun _ => L.const * timeBound M t) := by
  obtain ⟨L, hok⟩ := ImpLayout.exists_layout (program M)
  refine ⟨L, fun B w t hfit htable hmem hvalues hparameter hlen hstates hwork => ?_⟩
  have hsolves : Solves L (program M) {Lax53.MSOLinearTime.treeInput M.1 t}
      (fun _ => [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0])
      (fun _ => B) (fun _ => timeBound M t) := by
    refine ⟨hok, ?_, ?_⟩
    · intro x hx v hv
      have hx' : x = Lax53.MSOLinearTime.treeInput M.1 t := hx
      subst x
      exact hvalues v hv
    · intro x hx
      have hx' : x = Lax53.MSOLinearTime.treeInput M.1 t := hx
      subst x
      obtain ⟨τ, hrun, hout⟩ := program_spec B M t htable hmem hvalues hparameter hlen
        hstates hwork _ (initial_initEnv M t)
      exact ⟨workspaceExt M t, τ, hrun, by simpa [initEnv] using hout⟩
  exact hsolves.computesInTime (fun _ _ => hfit)

end Lax53Proofs.FixedAutomatonModelChecking
