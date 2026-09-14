import Lax842588Proofs.AutomatonRamArenaReadTree
import Lax842588Proofs.AutomatonRamEvaluateTree

/-!
End-to-end verification of the charged structural frontend, from the
distinguished Lax-58 input tape to the proof-private arrays consumed by the
existing automaton evaluator.
-/

namespace Lax842588Proofs.AutomatonRamArenaPrepare

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.AutomatonRamCorrectness
open Lax842588Proofs.AutomatonTableEncoding
open Lax842588Proofs.AutomatonRamArenaReadTree
open Lax560851.WordArena

private theorem eq_of_wordsAt_zero_of_length_eq {parameter words : List Nat}
    (hwords : WordsAt parameter 0 words)
    (hlength : parameter.length = words.length) :
    parameter = words := by
  apply List.ext_getElem hlength
  intro i hparameter hwordsIndex
  rw [← List.getD_eq_getElem parameter 0 hparameter]
  rw [← List.getD_eq_getElem words 0 hwordsIndex]
  simpa using hwords i hwordsIndex

/-- Workspace extents for the structural frontend followed by the existing
bottom-up evaluator. -/
def arenaEvaluatorExt (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (name : String) : Nat :=
  let I := encodeRaw (automatonTreeRaw M t)
  if name = "Arena" then I.memoryWords
  else if name = "P" then (encodeAutomaton M).length
  else if name = "W" then treeSize t
  else if name = "TreeSymbolStack" then treeSize t
  else if name = "TreeTailStack" then treeSize t
  else if name = "S" then treeSize t * M.2.2.1.length
  else if name = "L" then treeSize t
  else if name = "O" then M.2.2.1.length
  else 0

/-- Exact initial storage/tape convention used by the combined program. -/
def ArenaEvaluatorInitial (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (sigma : Env) : Prop :=
  let I := encodeRaw (automatonTreeRaw M t)
  (sigma.arrs "Arena").length = I.memoryWords ∧
    (sigma.arrs "P").length = (encodeAutomaton M).length ∧
    (sigma.arrs "W").length = treeSize t ∧
    (sigma.arrs "TreeSymbolStack").length = treeSize t ∧
    (sigma.arrs "TreeTailStack").length = treeSize t ∧
    sigma.arrs "S" =
      List.replicate (treeSize t * M.2.2.1.length) 0 ∧
    sigma.arrs "L" = List.replicate (treeSize t) 0 ∧
    (sigma.arrs "O").length = M.2.2.1.length ∧
    sigma.inp = automatonInput M t

theorem arenaEvaluatorInitial_initEnv (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    ArenaEvaluatorInitial M t
      (Lax865980Proofs.Imp.initEnv (arenaEvaluatorExt M t)
        (automatonInput M t)) := by
  simp [ArenaEvaluatorInitial, arenaEvaluatorExt,
    Lax865980Proofs.Imp.initEnv]

/-- Conservative cost of the complete structural-to-working-layout phase. -/
def prepareCost (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (transitionStepBudget : Nat) : Nat :=
  let I := encodeRaw (automatonTreeRaw M t)
  (12 * I.memoryWords + 20) + 40 +
    (alphabetLoopCost M.1 + 50) + 60 +
    readTransitionsCost M.2.2.1 transitionStepBudget +
    readAcceptingCost M.2.2.2 + readTreeCost M.1 t + 1

/-- The complete charged frontend establishes precisely the context expected
by `evaluateTree`; no whole-array conversion is treated as a unit operation. -/
theorem prepare_spec (B : Nat) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (transitionStepBudget : Nat)
    (h4 : 4 < B)
    (hmemB : (encodeRaw (automatonTreeRaw M t)).memoryWords < B)
    (hvaluesB : ∀ value ∈
      arenaWords (encodeRaw (automatonTreeRaw M t)), value < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (htreeB : treeSize t < B)
    (hstatesCapacityB : treeSize t * M.2.2.1.length < B)
    (hwidthB : maximumRank M.1 + 3 < B)
    (htransitionsB : M.2.2.1.length < B)
    (hacceptingB : M.2.2.2.length < B)
    (hchildrenB : ∀ transition ∈ M.2.2.1,
      transition.2.2.length < B)
    (hstep : ∀ transition ∈ M.2.2.1,
      transitionBodyCost (maximumRank M.1) transition ≤
        transitionStepBudget)
    (halphabetB : M.1.length < B) :
    Spec B (ArenaEvaluatorInitial M t) prepare
      (fun _ sigma' => EvaluateTreeContext B M (encodeTree M.1 t) sigma')
      (prepareCost M t transitionStepBudget) := by
  intro sigma hinitial
  let I := encodeRaw (automatonTreeRaw M t)
  obtain ⟨p⟩ := instancePointers M t
  rcases hinitial with
    ⟨hArenaLen, hPLen, hWLen, hSymbolLen, hTailLen, hS, hL, hO,
      hinput⟩
  have h0 : 0 < B := by omega
  have h1 : 1 < B := by omega
  have hrootB : I.root < B := by
    have hrootLast := Lax560851Proofs.WordArena.encodeRaw_root_last
      (automatonTreeRaw M t)
    dsimp [I]
    omega
  have hread := (readArena_spec B (automatonTreeRaw M t) hmemB
    (by
      intro value hvalue
      simp only [WordImage.toInput, List.mem_cons] at hvalue
      rcases hvalue with rfl | hvalue
      · exact hrootB
      · apply hvaluesB value
        simpa [I, arenaWords] using hvalue)).frame
  obtain ⟨sigma1, hrun1, ⟨hloaded1, hvars1, harrs1, hinp1, hout1⟩⟩ :=
    hread.run ⟨by simpa [I] using hArenaLen,
      by simpa [automatonInput, I] using hinput⟩
  have hopen := (openInstanceAt_spec B I p h0
    (by simpa [I] using hmemB)
    (by simpa [I] using hvaluesB)).frame
  obtain ⟨sigma2, hrun2,
      ⟨hopened2, hvars2, harrs2, hinp2, hout2⟩⟩ :=
    hopen.run (by simpa [I] using hloaded1)
  rcases hopened2 with
    ⟨hloaded2, hfields2, hautomaton2, htreeTail2, htreeRoot2,
      halphabetCursor2, hbodyRoot2⟩
  have hP2 : (sigma2.arrs "P").length = (encodeAutomaton M).length := by
    rw [harrs2 "P" (by decide), harrs1 "P" (by decide)]
    exact hPLen
  have halphabetReady : AlphabetReady B I M.1 sigma2 := by
    refine ⟨hloaded2, ?_, ?_, p.alphabet, halphabetCursor2, p.alphabetRep⟩
    · rw [hP2, encodeAutomaton_length]
      omega
    · rw [hP2]
      exact hparameterLenB
  have halphabet := (readAlphabet_spec B I M.1 h4
    (by simpa [I] using hmemB) (by simpa [I] using hvaluesB)
    hwidthB).frame
  obtain ⟨sigma3, hrun3,
      ⟨⟨halphabet3, hP3Length⟩, hvars3, harrs3, hinp3, hout3⟩⟩ :=
    halphabet.run halphabetReady
  have hbodyRoot3 : sigma3.vars "bodyRoot" = p.body := by
    rw [hvars3 "bodyRoot" (by decide)]
    exact hbodyRoot2
  have hbodyReady : AutomatonBodyReady B I M.1 M.2
      (encodeAutomaton M).length sigma3 := by
    refine ⟨halphabet3, ?_, p.body, hbodyRoot3, p.bodyRep⟩
    rw [hP3Length, hP2]
  have hbody := (openAutomatonBody_spec B I M.1 M.2
    (encodeAutomaton M).length h0 (by simpa [I] using hmemB)
    (by simpa [I] using hvaluesB)).frame
  obtain ⟨sigma4, hrun4,
      ⟨hbody4, hvars4, harrs4, hinp4, hout4⟩⟩ :=
    hbody.run hbodyReady
  have htransitions := (readTransitions_spec B I M.1 M.2
    transitionStepBudget h1 (by simpa [I] using hmemB)
    (by simpa [I] using hvaluesB) htransitionsB hwidthB hchildrenB
    hstep).frame
  obtain ⟨sigma5, hrun5,
      ⟨htransitions5, hvars5, harrs5, hinp5, hout5⟩⟩ :=
    htransitions.run hbody4
  have haccepting := (readAccepting_spec B I M.1 M.2 h1
    (by simpa [I] using hmemB) (by simpa [I] using hvaluesB)
    hacceptingB).frame
  obtain ⟨sigma6, hrun6,
      ⟨htable6, hvars6, harrs6, hinp6, hout6⟩⟩ :=
    haccepting.run htransitions5
  rcases htable6 with
    ⟨hloaded6, hPcapacity6, hPLenB6, hPWords6, hA6, hQ6, hT6,
      hR6, hwidth6, hrecords6, hacceptBase6, hF6⟩
  have htreeRoot6 : sigma6.vars "treeRoot" = p.tree := by
    rw [hvars6 "treeRoot" (by decide), hvars5 "treeRoot" (by decide),
      hvars4 "treeRoot" (by decide), hvars3 "treeRoot" (by decide)]
    exact htreeRoot2
  have hW6 : sigma6.arrs "W" = sigma.arrs "W" := by
    rw [harrs6 "W" (by decide), harrs5 "W" (by decide),
      harrs4 "W" (by decide), harrs3 "W" (by decide),
      harrs2 "W" (by decide), harrs1 "W" (by decide)]
  have hSymbol6 : sigma6.arrs "TreeSymbolStack" =
      sigma.arrs "TreeSymbolStack" := by
    rw [harrs6 "TreeSymbolStack" (by decide),
      harrs5 "TreeSymbolStack" (by decide),
      harrs4 "TreeSymbolStack" (by decide),
      harrs3 "TreeSymbolStack" (by decide),
      harrs2 "TreeSymbolStack" (by decide),
      harrs1 "TreeSymbolStack" (by decide)]
  have hTail6 : sigma6.arrs "TreeTailStack" =
      sigma.arrs "TreeTailStack" := by
    rw [harrs6 "TreeTailStack" (by decide),
      harrs5 "TreeTailStack" (by decide),
      harrs4 "TreeTailStack" (by decide),
      harrs3 "TreeTailStack" (by decide),
      harrs2 "TreeTailStack" (by decide),
      harrs1 "TreeTailStack" (by decide)]
  have htreeReady : TreeReadReady B I M.1 t p.tree sigma6 := by
    refine ⟨hloaded6, htreeRoot6, p.treeRep, htreeB, halphabetB,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hW6, hWLen]
    · rw [hSymbol6, hSymbolLen]
    · rw [hTail6, hTailLen]
    · rw [hW6, hWLen]
      exact htreeB
    · rw [hSymbol6, hSymbolLen]
      exact htreeB
    · rw [hTail6, hTailLen]
      exact htreeB
  have htree := (readTree_spec B I M.1 t p.tree h1
    (by simpa [I] using hmemB) (by simpa [I] using hvaluesB)
    halphabetB).frame
  obtain ⟨sigma7, hrun7,
      ⟨htree7, hvars7, harrs7, hinp7, hout7⟩⟩ :=
    htree.run htreeReady
  have hrunExact := hrun1.seq (hrun2.seq (hrun3.seq (hrun4.seq
    (hrun5.seq (hrun6.seq (hrun7.seq Run.skip))))))
  have hrun : Run B prepare sigma sigma7
      (prepareCost M t transitionStepBudget) := by
    unfold prepare Lax842588Proofs.AutomatonRamProgram.seqs prepareCost
    exact hrunExact.mono (by simp; omega)
  have hPLength7 : (sigma7.arrs "P").length =
      (encodeAutomaton M).length := by
    rw [Lax842588Proofs.Run.arrayLength_eq hrun "P"]
    exact hPLen
  have hPWords7 : WordsAt (sigma7.arrs "P") 0 (encodeAutomaton M) := by
    rw [harrs7 "P" (by decide)]
    exact hPWords6
  have hP7 : sigma7.arrs "P" = encodeAutomaton M :=
    eq_of_wordsAt_zero_of_length_eq hPWords7 hPLength7
  have hWLength7 : (sigma7.arrs "W").length = treeSize t := by
    rw [Lax842588Proofs.Run.arrayLength_eq hrun "W"]
    exact hWLen
  have hW7 : sigma7.arrs "W" = encodeTree M.1 t :=
    eq_of_wordsAt_zero_of_length_eq htree7.2.2.2
      (by simpa [encodeTree_length] using hWLength7)
  have hS7 : sigma7.arrs "S" =
      List.replicate (treeSize t * M.2.2.1.length) 0 := by
    rw [hrun.frame_arr "S" (by decide)]
    exact hS
  have hL7 : sigma7.arrs "L" = List.replicate (treeSize t) 0 := by
    rw [hrun.frame_arr "L" (by decide)]
    exact hL
  have hO7 : (sigma7.arrs "O").length = M.2.2.1.length := by
    rw [hrun.frame_arr "O" (by decide)]
    exact hO
  have hfields7 : EvalFields M (encodeTree M.1 t).length sigma7 := by
    refine ⟨hP7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hvars7 "A" (by decide)).trans hA6
    · exact (hvars7 "Q" (by decide)).trans hQ6
    · exact (hvars7 "T" (by decide)).trans hT6
    · exact (hvars7 "R" (by decide)).trans hR6
    · exact (hvars7 "width" (by decide)).trans hwidth6
    · exact (hvars7 "records" (by decide)).trans hrecords6
    · rw [hvars7 "acceptBase" (by decide), hacceptBase6,
        transitionTablePrefix_length]
    · exact (hvars7 "F" (by decide)).trans hF6
    · simpa [encodeTree_length] using htree7.2.1
  refine ⟨sigma7, hrun, hfields7, hW7, ?_, ?_, hO7, ?_⟩
  · simpa [encodeTree_length] using hS7
  · simpa [encodeTree_length] using hL7
  · simpa [hW7, encodeTree_length] using hstatesCapacityB

end Lax842588Proofs.AutomatonRamArenaPrepare
