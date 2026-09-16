import Lax842588Proofs.AutomatonRamArenaTransitionLoop

/-!
Verification of transition-table initialization, the complete represented
transition scan, and the table-header epilogue.
-/

namespace Lax842588Proofs.AutomatonRamArenaCorrectness

set_option maxHeartbeats 3000000
open Classical

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.AutomatonTableEncoding
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- Exact evaluator-table prefix through the last transition row. -/
def transitionTablePrefix (alphabet : RankedAlphabetCode)
    (body : AutomatonCode) : List Nat :=
  [alphabet.length] ++ alphabet ++
    [body.1, body.2.1.length, maximumRank alphabet] ++
      transitionRows (maximumRank alphabet) body.2.1

@[simp] theorem transitionTablePrefix_length (alphabet : RankedAlphabetCode)
    (body : AutomatonCode) :
    (transitionTablePrefix alphabet body).length =
      alphabet.length + 4 +
        body.2.1.length * (maximumRank alphabet + 3) := by
  simp [transitionTablePrefix]
  omega

theorem transitionTablePrefix_succ_le_encodeAutomaton_length
    (alphabet : RankedAlphabetCode) (body : AutomatonCode) :
    (transitionTablePrefix alphabet body).length + 1 ≤
      (encodeAutomaton (alphabet, body)).length := by
  rw [transitionTablePrefix_length, encodeAutomaton_length]
  simp only [Prod.fst, Prod.snd]
  omega

/-- Header facts already established before the two reserved transition
metadata cells are finalized. -/
def TransitionHeader (alphabet : RankedAlphabetCode) (stateCount : Nat)
    (parameter : List Nat) : Prop :=
  parameter.getD 0 0 = alphabet.length ∧
    AlphabetPrefixEq parameter alphabet ∧
    parameter.getD (alphabet.length + 1) 0 = stateCount

theorem transitionHeader_of_sameBefore {alphabet : RankedAlphabetCode}
    {stateCount records : Nat} {parameter original : List Nat}
    (hrecords : records = alphabet.length + 4)
    (hsame : SameBefore parameter original records)
    (hheader : TransitionHeader alphabet stateCount original) :
    TransitionHeader alphabet stateCount parameter := by
  subst records
  refine ⟨(hsame 0 (by omega)).trans hheader.1, ?_,
    (hsame (alphabet.length + 1) (by omega)).trans hheader.2.2⟩
  intro i hi
  exact (hsame (i + 1) (by omega)).trans (hheader.2.1 i hi)

private theorem wordsAt_singleton_of_getD {parameter : List Nat}
    {start value : Nat} (h : parameter.getD start 0 = value) :
    WordsAt parameter start [value] := by
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst i
  simpa using h

private theorem transitionHeader_wordsAt {alphabet : RankedAlphabetCode}
    {stateCount : Nat} {parameter : List Nat}
    (hheader : TransitionHeader alphabet stateCount parameter) :
    WordsAt parameter 0 ([alphabet.length] ++ alphabet ++ [stateCount]) := by
  have hA : WordsAt parameter 0 [alphabet.length] :=
    wordsAt_singleton_of_getD hheader.1
  have halphabet : WordsAt parameter 1 alphabet := by
    intro i hi
    simpa [Nat.add_comm] using hheader.2.1 i hi
  have hAalphabet := wordsAt_append hA halphabet
  have hQ : WordsAt parameter (alphabet.length + 1) [stateCount] :=
    wordsAt_singleton_of_getD hheader.2.2
  have hfull := wordsAt_append hAalphabet (by simpa using hQ)
  simpa [List.append_assoc] using hfull

private theorem transitionPrefix_after_headerStores
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (parameter : List Nat)
    (hspace : (transitionTablePrefix alphabet body).length + 1 ≤
      parameter.length)
    (hheader : TransitionHeader alphabet body.1 parameter)
    (hrows : WordsAt parameter (alphabet.length + 4)
      (transitionRows (maximumRank alphabet) body.2.1)) :
    WordsAt
      ((parameter.set (alphabet.length + 2) body.2.1.length).set
        (alphabet.length + 3) (maximumRank alphabet))
      0 (transitionTablePrefix alphabet body) := by
  let afterT := parameter.set (alphabet.length + 2) body.2.1.length
  let afterR := afterT.set (alphabet.length + 3) (maximumRank alphabet)
  have hbase := transitionHeader_wordsAt hheader
  have hTspace :
      ([alphabet.length] ++ alphabet ++ [body.1]).length < parameter.length := by
    simp
    have hprefixLength := transitionTablePrefix_length alphabet body
    omega
  have hthroughT : WordsAt afterT 0
      (([alphabet.length] ++ alphabet ++ [body.1]) ++
        [body.2.1.length]) := by
    simpa [afterT] using wordsAt_set_append
      (value := body.2.1.length) hbase (by simpa using hTspace)
  have hRspace :
      (([alphabet.length] ++ alphabet ++ [body.1]) ++
        [body.2.1.length]).length < afterT.length := by
    simp [afterT]
    have hprefixLength := transitionTablePrefix_length alphabet body
    omega
  have hthroughR : WordsAt afterR 0
      ((([alphabet.length] ++ alphabet ++ [body.1]) ++
        [body.2.1.length]) ++ [maximumRank alphabet]) := by
    simpa [afterR] using wordsAt_set_append
      (value := maximumRank alphabet) hthroughT (by simpa using hRspace)
  have hrowsSpace : alphabet.length + 4 +
      (transitionRows (maximumRank alphabet) body.2.1).length ≤
        parameter.length := by
    rw [transitionRows_length]
    have hprefixLength := transitionTablePrefix_length alphabet body
    omega
  have hrowsT : WordsAt afterT (alphabet.length + 4)
      (transitionRows (maximumRank alphabet) body.2.1) := by
    exact wordsAt_set_before hrows hrowsSpace (by omega)
  have hrowsR : WordsAt afterR (alphabet.length + 4)
      (transitionRows (maximumRank alphabet) body.2.1) := by
    apply wordsAt_set_before hrowsT
    · simpa [afterT] using hrowsSpace
    · omega
  have hfull := wordsAt_append hthroughR (by simpa using hrowsR)
  simpa [afterR, afterT, transitionTablePrefix, List.append_assoc] using hfull

/-- State immediately after initializing `T := 0`, ready for the represented
transition-list loop. -/
def TransitionScanReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (sigma : Env) : Prop :=
  (∃ baseline,
    TransitionLoopInv B I (maximumRank alphabet) (alphabet.length + 4)
      body.2.1 baseline sigma ∧
    TransitionHeader alphabet body.1 baseline) ∧
  (encodeAutomaton (alphabet, body)).length ≤
    (sigma.arrs "P").length ∧
  sigma.vars "A" = alphabet.length ∧
  sigma.vars "Q" = body.1 ∧
  I.Represents (sigma.vars "acceptCursor")
    ((derivedPresentation : Presentation (List Nat)).toRaw body.2.2)

/-- Result of the transition loop before writing its two reserved header
cells. -/
def TransitionScanDone (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
  (encodeAutomaton (alphabet, body)).length ≤
    (sigma.arrs "P").length ∧
  (sigma.arrs "P").length < B ∧
  TransitionHeader alphabet body.1 (sigma.arrs "P") ∧
  WordsAt (sigma.arrs "P") (alphabet.length + 4)
    (transitionRows (maximumRank alphabet) body.2.1) ∧
  sigma.vars "A" = alphabet.length ∧
  sigma.vars "Q" = body.1 ∧
  sigma.vars "T" = body.2.1.length ∧
  sigma.vars "R" = maximumRank alphabet ∧
  sigma.vars "width" = maximumRank alphabet + 3 ∧
  sigma.vars "records" = alphabet.length + 4 ∧
  I.Represents (sigma.vars "acceptCursor")
    ((derivedPresentation : Presentation (List Nat)).toRaw body.2.2)

/-- Exact result of `readTransitions`; the next free cell is the accepting
count cell. -/
def TransitionsRead (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
  (encodeAutomaton (alphabet, body)).length ≤
    (sigma.arrs "P").length ∧
  (sigma.arrs "P").length < B ∧
  WordsAt (sigma.arrs "P") 0 (transitionTablePrefix alphabet body) ∧
  sigma.vars "A" = alphabet.length ∧
  sigma.vars "Q" = body.1 ∧
  sigma.vars "T" = body.2.1.length ∧
  sigma.vars "R" = maximumRank alphabet ∧
  sigma.vars "width" = maximumRank alphabet + 3 ∧
  sigma.vars "records" = alphabet.length + 4 ∧
  sigma.vars "acceptBase" = (transitionTablePrefix alphabet body).length ∧
  I.Represents (sigma.vars "acceptCursor")
    ((derivedPresentation : Presentation (List Nat)).toRaw body.2.2)

private theorem initializeTransitions_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (h1 : 1 < B) (htransitionsB : body.2.1.length < B)
    (hwidthB : maximumRank alphabet + 3 < B) :
    Spec B
      (AutomatonBodyOpened B I alphabet body
        (encodeAutomaton (alphabet, body)).length)
      (.assign "T" (.lit 0))
      (fun _ sigma' => TransitionScanReady B I alphabet body sigma')
      10 := by
  intro sigma hopened
  rcases hopened with ⟨halphabet, hcapacity, hQ, htransitionRep,
    hacceptRep, hQcell⟩
  rcases halphabet with ⟨hloaded, hPspace, hPlenB, hA, hR, hwidthB',
    halphabetPrefix, hAcell, hwidth, hrecords⟩
  have hInv : TransitionLoopInv B I (maximumRank alphabet)
      (alphabet.length + 4) body.2.1 (sigma.arrs "P")
      (sigma.setVar "T" 0) := by
    refine ⟨?_, ?_, ?_, ?_, htransitionsB, hwidthB, ?_, ?_,
      sameBefore_refl _ _, [], body.2.1, sigma.vars "transitionCursor", ?_⟩
    · simpa [ArenaLoaded] using hloaded
    · simpa using hR
    · simpa using hwidth
    · simpa using hrecords
    · have hprefixLength := transitionTablePrefix_length alphabet body
      exact Nat.le_trans (by omega)
        (Nat.le_trans
          (transitionTablePrefix_succ_le_encodeAutomaton_length alphabet body)
          hcapacity)
    · simpa using hPlenB
    · simp [htransitionRep, transitionRows, WordsAt]
  have hheader : TransitionHeader alphabet body.1 (sigma.arrs "P") :=
    ⟨hAcell, halphabetPrefix, hQcell⟩
  unfold TransitionScanReady
  run_vcg
  all_goals simp_all [ArenaLoaded]
  all_goals exact ⟨sigma.arrs "P", hInv, hheader⟩

private theorem transitionScan_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (stepBudget : Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hchildrenB : ∀ transition ∈ body.2.1,
      transition.2.2.length < B)
    (hstep : ∀ transition ∈ body.2.1,
      transitionBodyCost (maximumRank alphabet) transition ≤ stepBudget) :
    Spec B (TransitionScanReady B I alphabet body) transitionLoop
      (fun _ sigma' => TransitionScanDone B I alphabet body sigma')
      (transitionLoopCost body.2.1 stepBudget) := by
  intro sigma hready
  rcases hready with ⟨⟨baseline, hInv, hheader⟩, hfullSpace, hA, hQ,
    hacceptRep⟩
  have hloop := (transitionLoop_completed_spec B I
    (maximumRank alphabet) (alphabet.length + 4) body.2.1 baseline
    stepBudget h1 hmemB hvaluesB hchildrenB hstep).frame
  obtain ⟨sigma', hrun, hpost⟩ := hloop.run hInv
  rcases hpost.1.1 with ⟨hloaded', hR', hwidth', hrecords',
    htransitionsB, hwidthB, hcapacity, hPlenB', hsame, done, rest,
    cursor, htransitions, hTinv, hcursor, hrestRep, hprefixRows⟩
  have hheader' := transitionHeader_of_sameBefore
    (records := alphabet.length + 4) rfl hsame hheader
  have hPlength : (sigma'.arrs "P").length =
      (sigma.arrs "P").length := Lax842588Proofs.Run.arrayLength_eq hrun "P"
  have hA' : sigma'.vars "A" = alphabet.length := by
    rw [hpost.2.1 "A" (by decide), hA]
  have hQ' : sigma'.vars "Q" = body.1 := by
    rw [hpost.2.1 "Q" (by decide), hQ]
  have hacceptCursor : sigma'.vars "acceptCursor" =
      sigma.vars "acceptCursor" := hpost.2.1 "acceptCursor" (by decide)
  have hacceptRep' : I.Represents (sigma'.vars "acceptCursor")
      ((derivedPresentation : Presentation (List Nat)).toRaw body.2.2) := by
    rw [hacceptCursor]
    exact hacceptRep
  exact ⟨sigma', hrun, hloaded', by simpa [hPlength] using hfullSpace,
    hPlenB', hheader', hpost.1.2.2, hA', hQ', hpost.1.2.1,
    hR', hwidth', hrecords', hacceptRep'⟩

private theorem finishTransitions_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (h1 : 1 < B) (htransitionsB : body.2.1.length < B)
    (hwidthB : maximumRank alphabet + 3 < B) :
    Spec B (TransitionScanDone B I alphabet body)
      (.seq
        (.store "P" (.add (.var "A") (.lit 2)) (.var "T"))
        (.seq
          (.store "P" (.add (.var "A") (.lit 3)) (.var "R"))
          (.seq
            (.assign "acceptBase"
              (.add (.var "records") (.mul (.var "T") (.var "width"))))
            .skip)))
      (fun _ sigma' => TransitionsRead B I alphabet body sigma')
      50 := by
  intro sigma hdone
  rcases hdone with ⟨hloaded, hspace, hPlenB, hheader, hrows, hA, hQ,
    hT, hR, hwidth, hrecords, hacceptRep⟩
  have htransitionSpace : (transitionTablePrefix alphabet body).length + 1 ≤
      (sigma.arrs "P").length := Nat.le_trans
    (transitionTablePrefix_succ_le_encodeAutomaton_length alphabet body) hspace
  have hprefix := transitionPrefix_after_headerStores alphabet body
    (sigma.arrs "P") htransitionSpace hheader hrows
  have hprefixB : (transitionTablePrefix alphabet body).length < B := by
    omega
  unfold TransitionsRead
  run_vcg
  all_goals simp_all [ArenaLoaded]
  all_goals (try omega)

/-- Conservative cost of the complete transition-reading phase. -/
def readTransitionsCost (transitions : List TransitionCode)
    (stepBudget : Nat) : Nat :=
  10 + transitionLoopCost transitions stepBudget + 50

theorem readTransitions_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (stepBudget : Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htransitionsB : body.2.1.length < B)
    (hwidthB : maximumRank alphabet + 3 < B)
    (hchildrenB : ∀ transition ∈ body.2.1,
      transition.2.2.length < B)
    (hstep : ∀ transition ∈ body.2.1,
      transitionBodyCost (maximumRank alphabet) transition ≤ stepBudget) :
    Spec B
      (AutomatonBodyOpened B I alphabet body
        (encodeAutomaton (alphabet, body)).length)
      readTransitions
      (fun _ sigma' => TransitionsRead B I alphabet body sigma')
      (readTransitionsCost body.2.1 stepBudget) := by
  have hinit := initializeTransitions_spec B I alphabet body h1
    htransitionsB hwidthB
  have hscan := transitionScan_spec B I alphabet body stepBudget h1 hmemB
    hvaluesB hchildrenB hstep
  have hfinish := finishTransitions_spec B I alphabet body h1
    htransitionsB hwidthB
  have htail : Spec B (TransitionScanReady B I alphabet body)
      (.seq transitionLoop
        (.seq
          (.store "P" (.add (.var "A") (.lit 2)) (.var "T"))
          (.seq
            (.store "P" (.add (.var "A") (.lit 3)) (.var "R"))
            (.seq
              (.assign "acceptBase"
                (.add (.var "records") (.mul (.var "T") (.var "width"))))
              .skip))))
      (fun _ sigma' => TransitionsRead B I alphabet body sigma')
      (transitionLoopCost body.2.1 stepBudget + 50) :=
    Spec.seq hscan hfinish
      (fun _ _ _ hpost => hpost)
      (fun _ _ _ _ _ hpost => hpost)
  have hall := Spec.seq hinit htail
    (fun _ _ _ hpost => hpost)
    (fun _ _ _ _ _ hpost => hpost)
  simpa [readTransitions, Lax842588Proofs.AutomatonRamProgram.seqs,
    readTransitionsCost, Nat.add_assoc] using hall

end Lax842588Proofs.AutomatonRamArenaCorrectness
