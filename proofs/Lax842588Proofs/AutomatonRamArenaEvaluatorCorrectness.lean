import Lax842588Proofs.AutomatonRamBackend

/-!
Composition of the charged distinguished-arena frontend with the verified
bottom-up automaton backend.
-/

namespace Lax842588Proofs.AutomatonRamArenaEvaluatorCorrectness

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.AutomatonRamArenaPrepare
open Lax842588Proofs.AutomatonRamBackend
open Lax560851.WordArena

def arenaEvaluatorImpCost (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (transitionStepBudget : Nat) : Nat :=
  prepareCost M t transitionStepBudget + automatonBackendCost M t

/-- End-to-end IMP+ correctness on the distinguished certified structural
input, including all representation conversion. -/
theorem arenaEvaluator_spec (B : Nat) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (transitionStepBudget : Nat)
    (h4 : 4 < B)
    (hmemB : (encodeRaw (automatonTreeRaw M t)).memoryWords < B)
    (hvaluesB : ∀ value ∈
      arenaWords (encodeRaw (automatonTreeRaw M t)), value < B)
    (hparameterB : ∀ value ∈ encodeAutomaton M, value < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (htreeB : treeSize t < B)
    (hstatesCapacityB : treeSize t * M.2.2.1.length < B)
    (hwidthB : maximumRank M.1 + 3 < B)
    (hQB : M.2.1 < B)
    (htransitionsB : M.2.2.1.length < B)
    (hacceptingB : M.2.2.2.length < B)
    (hchildrenB : ∀ transition ∈ M.2.2.1,
      transition.2.2.length < B)
    (hstep : ∀ transition ∈ M.2.2.1,
      transitionBodyCost (maximumRank M.1) transition ≤
        transitionStepBudget)
    (halphabetB : M.1.length < B)
    (hworkB : M.1.length + 4 +
      M.2.2.1.length * (maximumRank M.1 + 3) +
        (maximumRank M.1 + 3) < B) :
    Spec B (ArenaEvaluatorInitial M t)
      Lax842588Proofs.AutomatonRamArenaProgram.evaluator
      (fun sigma sigma' => sigma'.out = sigma.out ++
        [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0])
      (arenaEvaluatorImpCost M t transitionStepBudget) := by
  have hprepare := (prepare_spec B M t transitionStepBudget h4 hmemB
    hvaluesB hparameterLenB htreeB hstatesCapacityB hwidthB
    htransitionsB hacceptingB hchildrenB hstep halphabetB).frame
  have hbackend := automatonBackend_spec B M t (by omega) (by omega)
    hparameterB hparameterLenB htreeB hstatesCapacityB hwidthB hQB
    htransitionsB hworkB
  have hcombined : Spec B (ArenaEvaluatorInitial M t)
      (.seq prepare automatonBackend)
      (fun sigma sigma' => sigma'.out = sigma.out ++
        [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0])
      (prepareCost M t transitionStepBudget + automatonBackendCost M t) :=
    Spec.seq hprepare hbackend
      (fun _ _ _ hpost => hpost.1)
      (by
        intro sigma middle final hinitial hprepared hfinal
        rw [hfinal, hprepared.2.2.2.2 (by decide)])
  simpa [Lax842588Proofs.AutomatonRamArenaProgram.evaluator,
    Lax842588Proofs.AutomatonRamProgram.seqs, automatonBackend,
    arenaEvaluatorImpCost] using hcombined

end Lax842588Proofs.AutomatonRamArenaEvaluatorCorrectness
