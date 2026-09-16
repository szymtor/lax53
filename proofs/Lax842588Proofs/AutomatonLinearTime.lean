import Lax842588Proofs.AutomatonRamArenaBounds
import Lax842588Proofs.CheckedRamAdapter

namespace Lax842588Proofs.AutomatonLinearTime

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
open Classical

open Lax759944Proofs.Legacy.Ram
open Lax759944Proofs.Legacy.RamComputes
open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Compile
open Lax759944Proofs.Legacy.Simulation
open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588.AutomatonLinearTime
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaPrepare
open Lax842588Proofs.AutomatonRamArenaEvaluatorCorrectness
open Lax842588Proofs.AutomatonRamArenaBounds
open Lax560851.WordArena
open Lax560851.RamComplexity

/-- Expanded sequential-machine implementation, embedded into `Lax808846`
by the concise public `RamComputableWithinUsing` theorem below. -/
theorem exists_uniform_automatonAcceptance_expanded :
    ∃ (program : Program) (timeConstant wordConstant : Nat),
      ∀ (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) (w : Nat),
        InputPayloadsFitInWord M t w →
        3 * inputStructuralSize M t ≤ 2 ^ w →
        uniformWordBound wordConstant M t ≤ 2 ^ w →
        ComputesInTime w program {automatonInput M t}
          (fun _ => if M.2.toAutomaton M.1 |>.Accepts t then [1] else [0])
          (fun _ => uniformTimeBound timeConstant M t) := by
  refine ⟨program, 1000000, 1000000, ?_⟩
  intro M t w _hpayloads _harenaFits hword
  let B := evaluatorValueBound M t
  have hbasic := valueBound_basic M t
  have hmemB : (encodeRaw (automatonTreeRaw M t)).memoryWords < B := by
    simpa [B] using arenaMemory_lt_valueBound M t
  have hinputB : ∀ value ∈ automatonInput M t, value < B := by
    simpa [B] using arenaInput_values_lt_valueBound M t
  have harenaValuesB : ∀ value ∈
      arenaWords (encodeRaw (automatonTreeRaw M t)), value < B := by
    intro value hvalue
    apply hinputB value
    simp only [automatonInput, WordImage.toInput, List.mem_cons]
    exact Or.inr (by simpa [arenaWords] using hvalue)
  have hparameterB : ∀ value ∈ encodeAutomaton M, value < B := by
    simpa [B] using encodeAutomaton_values_lt_valueBound M t
  have hparameterLenB : (encodeAutomaton M).length < B := by
    simpa [B] using encodeAutomaton_length_lt_valueBound M t
  have htreeB : treeSize t < B :=
    (treeSize_le_inputStructuralSize M t).trans_lt (by simpa [B] using hbasic.2.2.1)
  have hstatesCapacityB : treeSize t * M.2.2.1.length < B := by
    simpa [B] using evaluatorWorkspace_lt_valueBound M t
  have hindexWorkB : M.1.length + 4 +
      M.2.2.1.length * (maximumRank M.1 + 3) +
        (maximumRank M.1 + 3) < B := by
    simpa [B] using evaluatorIndexWork_lt_valueBound M t
  have hwidthB : maximumRank M.1 + 3 < B := by omega
  have hQB : M.2.1 < B :=
    (stateCount_le_inputPayloadMax M t).trans_lt
      (by simpa [B] using hbasic.2.2.2)
  have htransitionsB : M.2.2.1.length < B :=
    ((transitionCount_le_automatonSize M).trans
      (automatonSize_le_automatonWorkSize M)).trans_lt
        (by simpa [B] using hbasic.2.1)
  have hacceptingB : M.2.2.2.length < B :=
    ((acceptingCount_le_automatonSize M).trans
      (automatonSize_le_automatonWorkSize M)).trans_lt
        (by simpa [B] using hbasic.2.1)
  have hchildrenB : ∀ transition ∈ M.2.2.1,
      transition.2.2.length < B := by
    intro transition htransition
    exact (transitionChildrenLength_le_automatonSize M htransition).trans_lt
      ((automatonSize_le_automatonWorkSize M).trans_lt
        (by simpa [B] using hbasic.2.1))
  have hstep : ∀ transition ∈ M.2.2.1,
      transitionBodyCost (maximumRank M.1) transition ≤
        1000 * (automatonWorkSize M + 1) := by
    exact fun transition htransition => transitionBodyCost_le M htransition
  have halphabetB : M.1.length < B :=
    ((alphabetLength_le_automatonSize M).trans
      (automatonSize_le_automatonWorkSize M)).trans_lt
        (by simpa [B] using hbasic.2.1)
  have hspec := arenaEvaluator_spec B M t
    (1000 * (automatonWorkSize M + 1))
    (by simpa [B] using hbasic.1) hmemB harenaValuesB hparameterB
    hparameterLenB htreeB hstatesCapacityB hwidthB hQB htransitionsB
    hacceptingB hchildrenB hstep halphabetB hindexWorkB
  obtain ⟨sigma', hrun, hout⟩ := hspec.run
    (arenaEvaluatorInitial_initEnv M t)
  obtain ⟨impCost, himpCost, hbigStep⟩ := hrun
  have hfit : layout.FitsWords B w := by
    simpa [B] using arenaLayout_fitsWords M t w hword
  obtain ⟨machineTime, hmachineTime, hruns⟩ :=
    compileProgram_runsTo hfit evaluator_ok hinputB hbigStep
  have himpBound := arenaEvaluatorImpCost_le M t
  have htotalTime : layout.const * impCost ≤
      uniformTimeBound 1000000 M t := by
    have hcost : impCost ≤
        12000 * (automatonWorkSize M + 1) ^ 2 * (treeSize t + 1) :=
      himpCost.trans himpBound
    calc
      layout.const * impCost ≤ layout.const *
          (12000 * (automatonWorkSize M + 1) ^ 2 * (treeSize t + 1)) :=
        Nat.mul_le_mul_left _ hcost
      _ ≤ uniformTimeBound 1000000 M t := by
        simp [Layout.const, uniformTimeBound]
        nlinarith
  have houtFinal : sigma'.out =
      [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0] := by
    simpa [Lax759944Proofs.Legacy.Imp.initEnv] using hout
  have hsingleton :
      [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0] =
        (if M.2.toAutomaton M.1 |>.Accepts t then [1] else [0]) := by
    by_cases haccepts : M.2.toAutomaton M.1 |>.Accepts t <;> simp [haccepts]
  intro input hinput
  simp only [Set.mem_singleton_iff] at hinput
  subst input
  refine ⟨machineTime, hmachineTime.trans htotalTime, ?_⟩
  rw [← hsingleton, ← houtFinal]
  simpa [program] using hruns

/-- Expanded fixed-automaton form, retained as an internal implementation corollary. -/
theorem exists_fixed_automatonAcceptance_expanded (M : EncodedAutomaton) :
    ∃ (program : Program) (timeCoefficient wordCoefficient : Nat),
      ∀ (t : Tree M.1.toRankedAlphabet) (w : Nat),
        InputPayloadsFitInWord M t w →
        3 * inputStructuralSize M t ≤ 2 ^ w →
        wordCoefficient *
          (inputStructuralSize M t + inputPayloadMax M t + 1) ≤ 2 ^ w →
        ComputesInTime w program {automatonInput M t}
          (fun _ => if M.2.toAutomaton M.1 |>.Accepts t then [1] else [0])
          (fun _ => timeCoefficient * (treeSize t + 1)) := by
  obtain ⟨uniformProgram, timeConstant, wordConstant, huniform⟩ :=
    exists_uniform_automatonAcceptance_expanded
  refine ⟨uniformProgram,
    timeConstant * (automatonWorkSize M + 1) ^ 2,
    wordConstant * (automatonWorkSize M + 1) ^ 2, ?_⟩
  intro t w hpayloads harenaFits hword
  have huniformWord : uniformWordBound wordConstant M t ≤ 2 ^ w := by
    simpa [uniformWordBound, Nat.mul_assoc] using hword
  have hresult := huniform M t w hpayloads harenaFits huniformWord
  simpa [uniformTimeBound, Nat.mul_assoc] using hresult

/--
---
conclusion: Lax842588.AutomatonLinearTime.exists_uniform_automatonAcceptance
---
The fixed compiled program first reads and materializes the distinguished
structural arena and then runs the verified bottom-up evaluator. Its checked
embedding into `Lax808846` also charges the terminal instruction. Lax560851's
reusable predicate packages the program and the three sufficient-width
premises; the underlying expanded theorem above remains inspectable.
-/
theorem exists_uniform_automatonAcceptance_proof :
    ∃ timeConstant wordConstant : Nat,
      RamComputableWithinUsing automatonAcceptancePresentation natOutput
        (fun input => if input.automaton.2.toAutomaton input.automaton.1 |>.Accepts
          input.tree then 1 else 0)
        (fun input => uniformTimeBound timeConstant input.automaton input.tree)
        (fun input => uniformWordBound wordConstant input.automaton input.tree) := by
  obtain ⟨program, timeConstant, wordConstant, h⟩ :=
    exists_uniform_automatonAcceptance_expanded
  refine ⟨timeConstant + 1, wordConstant,
    Lax759944Proofs.LegacyRamBridge.embedProgram program, ?_⟩
  rintro ⟨M, t⟩ w hpayload harena hword
  have htarget := CheckedRamAdapter.computesInTime
    (U := fun _ => uniformTimeBound (timeConstant + 1) M t)
    (h M t w hpayload harena hword) (fun _ _ => by
      simpa only [uniformTimeBound, Nat.mul_assoc] using
        CheckedRamAdapter.add_one_le_scaled timeConstant
          ((automatonWorkSize M + 1) ^ 2 * (treeSize t + 1))
          (Nat.mul_pos (pow_pos (by omega) _) (by omega)))
  by_cases haccepts : M.2.toAutomaton M.1 |>.Accepts t <;>
    simpa [automatonAcceptancePresentation, automatonAcceptanceRaw,
      automatonInput, natOutput, Lax560851.WordArena.encode,
      Lax560851.StructuralPresentation.presentationOf, haccepts] using
        htarget

/--
The fixed-automaton statement is the quantifier-order specialization of the
uniform implementation. Its coefficients absorb the automaton workload; it
does not claim a separate effective program generator.
-/
theorem exists_fixed_automatonAcceptance_proof (M : EncodedAutomaton) :
    ∃ timeCoefficient wordCoefficient : Nat,
      RamComputableWithinUsing (fixedAutomatonPresentation M) natOutput
        (fun t => if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0)
        (fun t => timeCoefficient * (treeSize t + 1))
        (fun t => wordCoefficient * inputMagnitudeUsing
          (fixedAutomatonPresentation M) t) := by
  obtain ⟨timeConstant, wordConstant, program, huniform⟩ :=
    Lax842588.AutomatonLinearTime.exists_uniform_automatonAcceptance
  refine ⟨timeConstant * (automatonWorkSize M + 1) ^ 2,
    wordConstant * (automatonWorkSize M + 1) ^ 2, program, ?_⟩
  intro t w hpayload harena hword
  have hword' : uniformWordBound wordConstant M t ≤ 2 ^ w := by
    simpa [uniformWordBound, inputMagnitudeUsing, fixedAutomatonPresentation,
      inputStructuralSize, inputPayloadMax,
      Lax560851.StructuralPresentation.presentationOf, Nat.mul_assoc] using hword
  simpa [automatonAcceptancePresentation, automatonAcceptanceRaw,
    fixedAutomatonPresentation, uniformTimeBound,
    Lax560851.WordArena.encode,
    Lax560851.StructuralPresentation.presentationOf, Nat.mul_assoc] using
      huniform ⟨M, t⟩ w hpayload harena hword'

end Lax842588Proofs.AutomatonLinearTime
