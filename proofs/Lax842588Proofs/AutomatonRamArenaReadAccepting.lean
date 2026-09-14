import Lax842588Proofs.AutomatonRamArenaReadTransitions

/-!
Verification of the accepting-state scan and completion of the evaluator's
working automaton table.
-/

namespace Lax842588Proofs.AutomatonRamArenaCorrectness

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588Proofs.ArrayInput
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamArenaSegments
open Lax842588Proofs.AutomatonRamCorrectness
open Lax842588Proofs.AutomatonTableEncoding
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- Proof-local name for the represented accepting-list guard. -/
def acceptingCondition : Cond :=
  .eq (.get "Arena" (.var "acceptCursor")) (.lit 1)

theorem encodeAutomaton_eq_transitionPrefix (alphabet : RankedAlphabetCode)
    (body : AutomatonCode) :
    encodeAutomaton (alphabet, body) =
      transitionTablePrefix alphabet body ++ [body.2.2.length] ++ body.2.2 := by
  rw [encodeAutomaton_eq]
  simp [transitionTablePrefix, transitionRows, List.append_assoc]

theorem encodeAutomaton_length_from_transitionPrefix
    (alphabet : RankedAlphabetCode) (body : AutomatonCode) :
    (encodeAutomaton (alphabet, body)).length =
      (transitionTablePrefix alphabet body).length + 1 + body.2.2.length := by
  rw [encodeAutomaton_eq_transitionPrefix]
  simp
  omega

/-- The accepting prefix already consumed by the arena cursor occupies the
consecutive cells after the reserved accepting-count word. -/
def AcceptingLoopInv (B : Nat) (I : WordImage) (base : Nat)
    (accepting : List Nat) (prefixBefore : List Nat) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "acceptBase" = base ∧
    base + 1 + accepting.length ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    accepting.length < B ∧
    SameBefore (sigma.arrs "P") prefixBefore (base + 1) ∧
    ∃ done rest cursor,
      accepting = done ++ rest ∧
      sigma.vars "F" = done.length ∧
      sigma.vars "acceptCursor" = cursor ∧
      I.Represents cursor
        ((derivedPresentation : Presentation (List Nat)).toRaw rest) ∧
      WordsAt (sigma.arrs "P") (base + 1) done

theorem acceptingCondition_value (B : Nat) (I : WordImage)
    (rest : List Nat) (cursor : Nat) (sigma : Env)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hloaded : ArenaLoaded I sigma)
    (hcursor : sigma.vars "acceptCursor" = cursor)
    (hrep : I.Represents cursor
      ((derivedPresentation : Presentation (List Nat)).toRaw rest)) :
    acceptingCondition.evalB B sigma = some (!rest.isEmpty) := by
  simpa [acceptingCondition, representedListCondition, WordImage.pairTag,
    derivedPresentation] using
    (representedListCondition_value B I nat rest cursor "acceptCursor" sigma
      h1 hmemB hloaded hcursor (by simpa [derivedPresentation] using hrep))

theorem acceptingCondition_defined (B : Nat) (I : WordImage) (base : Nat)
    (accepting prefixBefore : List Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B) :
    ∀ sigma, AcceptingLoopInv B I base accepting prefixBefore sigma →
      ∃ value, acceptingCondition.evalB B sigma = some value := by
  intro sigma hInv
  rcases hInv.2.2.2.2.2.2 with
    ⟨done, rest, cursor, haccepting, hF, hcursor, hrep, hwords⟩
  exact ⟨!rest.isEmpty,
    acceptingCondition_value B I rest cursor sigma h1 hmemB hInv.1 hcursor hrep⟩

theorem acceptingBody_spec (B : Nat) (I : WordImage) (base : Nat)
    (accepting prefixBefore : List Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B
      (fun sigma => AcceptingLoopInv B I base accepting prefixBefore sigma ∧
        acceptingCondition.evalB B sigma = some true)
      acceptingBody
      (fun sigma sigma' =>
        AcceptingLoopInv B I base accepting prefixBefore sigma' ∧
          sigma'.vars "F" = sigma.vars "F" + 1)
      100 := by
  intro sigma hpre
  rcases hpre.1 with ⟨hloaded, hbase, hcapacity, hPlenB, hacceptingB,
    hsame, done, rest, cursor, haccepting, hF, hcursor, hrep, hwords⟩
  have hcondition := acceptingCondition_value B I rest cursor sigma h1 hmemB
    hloaded hcursor hrep
  cases rest with
  | nil =>
      have hfalse : acceptingCondition.evalB B sigma = some false := by
        simpa only [List.isEmpty_nil, Bool.not_true] using hcondition
      rw [hpre.2] at hfalse
      contradiction
  | cons acceptState rest =>
      obtain ⟨valueAddress, restAddress, hcursorTag, hvalueWord, hrestWord,
          hvalueRep, hrestRep⟩ :=
        Lax842588Proofs.ArenaSemantics.Represents.list_cons hrep
      have hcursorValid := Lax842588Proofs.ArenaSemantics.Represents.valid hrep
      have hvalueValid :=
        Lax842588Proofs.ArenaSemantics.Represents.valid hvalueRep
      have hrestValid :=
        Lax842588Proofs.ArenaSemantics.Represents.valid hrestRep
      have hcursorLen :=
        Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hcursorValid
      have hvalueLen :=
        Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hvalueValid
      have hrestLen :=
        Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hrestValid
      have harenaLength : (arenaWords I).length = I.memoryWords := by
        simp [arenaWords, WordImage.memoryWords]
      have hgetB (i : Nat) : (arenaWords I).getD i 0 < B :=
        getD_lt_of_mem_bound (by omega) hvaluesB
      have hgetOptB (i : Nat) : ((arenaWords I)[i]?).getD 0 < B := by
        simpa [List.getD_eq_getElem?_getD] using hgetB i
      have hvalueGetD : ((arenaWords I)[cursor + 1]?).getD 0 =
          valueAddress := by
        simpa [List.getD_eq_getElem?_getD] using hvalueWord
      have hacceptWord :=
        Lax842588Proofs.ArenaSemantics.Represents.nat_payload hvalueRep
      have hacceptGetD : ((arenaWords I)[valueAddress + 1]?).getD 0 =
          acceptState := by
        simpa [List.getD_eq_getElem?_getD] using hacceptWord
      have hrestGetD : ((arenaWords I)[cursor + 2]?).getD 0 =
          restAddress := by
        simpa [List.getD_eq_getElem?_getD] using hrestWord
      have hvalueGetDB := hgetOptB (cursor + 1)
      have hacceptGetDB := hgetOptB (valueAddress + 1)
      have hrestGetDB := hgetOptB (cursor + 2)
      have hrestRep' : I.Represents restAddress
          ((derivedPresentation : Presentation (List Nat)).toRaw rest) := by
        simpa [derivedPresentation] using hrestRep
      have hdoneLt : done.length < accepting.length := by
        have hlength := congrArg List.length haccepting
        simp only [List.length_append, List.length_cons] at hlength
        omega
      have hslot : base + 1 + done.length < (sigma.arrs "P").length := by
        omega
      have hwords' : WordsAt
          ((sigma.arrs "P").set (base + 1 + done.length) acceptState)
          (base + 1) (done ++ [acceptState]) := by
        have happend := wordsAt_set_append (value := acceptState) hwords
          (by simpa [Nat.add_assoc] using hslot)
        simpa [Nat.add_assoc] using happend
      have hsame' : SameBefore
          ((sigma.arrs "P").set (base + 1 + done.length) acceptState)
          prefixBefore (base + 1) :=
        sameBefore_set_after hsame (by omega) hslot
      unfold acceptingBody Lax842588Proofs.AutomatonRamProgram.seqs
      run_vcg
      all_goals simp_all [AcceptingLoopInv, ArenaLoaded, acceptingCondition]
      all_goals (try omega)
      all_goals
        refine ⟨done ++ [acceptState], rest, ?_⟩
        simp_all [List.append_assoc]

/-- Conservative instruction budget for the accepting-state scan. -/
def acceptingLoopCost (accepting : List Nat) : Nat :=
  (1 + acceptingCondition.size + 100) * accepting.length +
    1 + acceptingCondition.size

private theorem acceptingBody_decreases (B : Nat) (I : WordImage)
    (base : Nat) (accepting prefixBefore : List Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B
      (fun sigma => AcceptingLoopInv B I base accepting prefixBefore sigma ∧
        acceptingCondition.evalB B sigma = some true)
      acceptingBody
      (fun sigma sigma' =>
        AcceptingLoopInv B I base accepting prefixBefore sigma' ∧
          accepting.length - sigma'.vars "F" <
            accepting.length - sigma.vars "F")
      100 := by
  refine (acceptingBody_spec B I base accepting prefixBefore h1 hmemB
    hvaluesB).post ?_
  intro sigma sigma' hpre hpost
  refine ⟨hpost.1, ?_⟩
  rcases hpre.1.2.2.2.2.2.2 with
    ⟨done, rest, cursor, haccepting, hF, hcursor, hrep, hwords⟩
  have hcondition := acceptingCondition_value B I rest cursor sigma h1 hmemB
    hpre.1.1 hcursor hrep
  cases rest with
  | nil =>
      have hfalse : acceptingCondition.evalB B sigma = some false := by
        simpa only [List.isEmpty_nil, Bool.not_true] using hcondition
      rw [hpre.2] at hfalse
      contradiction
  | cons acceptState rest =>
      have hlength := congrArg List.length haccepting
      simp only [List.length_append, List.length_cons] at hlength
      rw [hpost.2, hF]
      omega

theorem acceptingLoop_spec (B : Nat) (I : WordImage) (base : Nat)
    (accepting prefixBefore : List Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B (AcceptingLoopInv B I base accepting prefixBefore) acceptingLoop
      (fun _ sigma' =>
        AcceptingLoopInv B I base accepting prefixBefore sigma' ∧
          acceptingCondition.evalB B sigma' = some false)
      (acceptingLoopCost accepting) := by
  unfold acceptingLoop acceptingLoopCost
  refine Spec.while_count
    (AcceptingLoopInv B I base accepting prefixBefore)
    (fun sigma => accepting.length - sigma.vars "F")
    100
    (acceptingCondition_defined B I base accepting prefixBefore h1 hmemB)
    (acceptingBody_decreases B I base accepting prefixBefore h1 hmemB hvaluesB)
    (fun _ hInv => hInv) ?_
  intro sigma hInv
  have hsub : accepting.length - sigma.vars "F" ≤ accepting.length :=
    Nat.sub_le _ _
  have hmul := Nat.mul_le_mul_left
    (1 + acceptingCondition.size + 100) hsub
  simpa only [Nat.add_assoc] using
    Nat.add_le_add_right hmul (1 + acceptingCondition.size)

theorem acceptingLoop_completed_spec (B : Nat) (I : WordImage)
    (base : Nat) (accepting prefixBefore : List Nat) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B (AcceptingLoopInv B I base accepting prefixBefore) acceptingLoop
      (fun _ sigma' =>
        AcceptingLoopInv B I base accepting prefixBefore sigma' ∧
          sigma'.vars "F" = accepting.length ∧
          WordsAt (sigma'.arrs "P") (base + 1) accepting)
      (acceptingLoopCost accepting) := by
  refine (acceptingLoop_spec B I base accepting prefixBefore h1 hmemB
    hvaluesB).post ?_
  intro sigma sigma' hpre hpost
  rcases hpost.1.2.2.2.2.2.2 with
    ⟨done, rest, cursor, haccepting, hF, hcursor, hrep, hwords⟩
  have hcondition := acceptingCondition_value B I rest cursor sigma' h1 hmemB
    hpost.1.1 hcursor hrep
  have hempty : rest = [] := by
    cases rest with
    | nil => rfl
    | cons acceptState rest =>
        have htrue : acceptingCondition.evalB B sigma' = some true := by
          simpa only [List.isEmpty_cons, Bool.not_false] using hcondition
        rw [hpost.2] at htrue
        contradiction
  subst rest
  simp only [List.append_nil] at haccepting
  subst done
  exact ⟨hpost.1, hF, hwords⟩

/-- Complete evaluator automaton table produced from the represented value. -/
def AutomatonTableRead (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    (encodeAutomaton (alphabet, body)).length ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    WordsAt (sigma.arrs "P") 0 (encodeAutomaton (alphabet, body)) ∧
    sigma.vars "A" = alphabet.length ∧
    sigma.vars "Q" = body.1 ∧
    sigma.vars "T" = body.2.1.length ∧
    sigma.vars "R" = maximumRank alphabet ∧
    sigma.vars "width" = maximumRank alphabet + 3 ∧
    sigma.vars "records" = alphabet.length + 4 ∧
    sigma.vars "acceptBase" = (transitionTablePrefix alphabet body).length ∧
    sigma.vars "F" = body.2.2.length

/-- Conservative cost of reading and finalizing the accepting-state block. -/
def readAcceptingCost (accepting : List Nat) : Nat :=
  10 + acceptingLoopCost accepting + 20

theorem readAccepting_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (hacceptingB : body.2.2.length < B) :
    Spec B (TransitionsRead B I alphabet body) readAccepting
      (fun _ sigma' => AutomatonTableRead B I alphabet body sigma')
      (readAcceptingCost body.2.2) := by
  intro sigma hread
  rcases hread with ⟨hloaded, hspace, hPlenB, hprefix, hA, hQ, hT, hR,
    hwidth, hrecords, hbase, hacceptRep⟩
  let base := (transitionTablePrefix alphabet body).length
  have hcapacity : base + 1 + body.2.2.length ≤
      (sigma.arrs "P").length := by
    rw [← encodeAutomaton_length_from_transitionPrefix alphabet body]
    exact hspace
  have hInv : AcceptingLoopInv B I base body.2.2 (sigma.arrs "P")
      (sigma.setVar "F" 0) := by
    refine ⟨?_, ?_, hcapacity, ?_, hacceptingB, sameBefore_refl _ _,
      [], body.2.2, sigma.vars "acceptCursor", ?_⟩
    · simpa [ArenaLoaded] using hloaded
    · simpa [base] using hbase
    · simpa using hPlenB
    · simp [hacceptRep, WordsAt]
  have hloop := (acceptingLoop_completed_spec B I base body.2.2
    (sigma.arrs "P") h1 hmemB hvaluesB).frame
  obtain ⟨afterLoop, hrunLoop, hloopPost⟩ := hloop.run hInv
  rcases hloopPost.1.1 with ⟨hloaded', hbase', hcapacity', hPlenB',
    hacceptingB', hsame, done, rest, cursor, haccepting, hFinv, hcursor,
    hrestRep, hacceptPrefix⟩
  have hprefix' : WordsAt (afterLoop.arrs "P") 0
      (transitionTablePrefix alphabet body) := by
    apply wordsAt_of_sameBefore hsame hprefix
    simp [base]
  have hslot : base < (afterLoop.arrs "P").length := by omega
  have hthroughCount := wordsAt_set_append
    (value := body.2.2.length) hprefix' (by simpa [base] using hslot)
  have hacceptAfterCount : WordsAt
      ((afterLoop.arrs "P").set base body.2.2.length) (base + 1)
      body.2.2 := by
    exact wordsAt_set_before hloopPost.1.2.2 (by omega) (by omega)
  have hfull := wordsAt_append hthroughCount
    (by simpa [base] using hacceptAfterCount)
  have hfull' : WordsAt
      ((afterLoop.arrs "P").set base body.2.2.length) 0
      (encodeAutomaton (alphabet, body)) := by
    rw [encodeAutomaton_eq_transitionPrefix]
    simpa [base, List.append_assoc] using hfull
  have hAloop : afterLoop.vars "A" = alphabet.length := by
    calc
      _ = (sigma.setVar "F" 0).vars "A" := hloopPost.2.1 "A" (by decide)
      _ = sigma.vars "A" := by simp
      _ = alphabet.length := hA
  have hQloop : afterLoop.vars "Q" = body.1 := by
    calc
      _ = (sigma.setVar "F" 0).vars "Q" := hloopPost.2.1 "Q" (by decide)
      _ = sigma.vars "Q" := by simp
      _ = body.1 := hQ
  have hTloop : afterLoop.vars "T" = body.2.1.length := by
    calc
      _ = (sigma.setVar "F" 0).vars "T" := hloopPost.2.1 "T" (by decide)
      _ = sigma.vars "T" := by simp
      _ = body.2.1.length := hT
  have hRloop : afterLoop.vars "R" = maximumRank alphabet := by
    calc
      _ = (sigma.setVar "F" 0).vars "R" := hloopPost.2.1 "R" (by decide)
      _ = sigma.vars "R" := by simp
      _ = maximumRank alphabet := hR
  have hwidthLoop : afterLoop.vars "width" = maximumRank alphabet + 3 := by
    calc
      _ = (sigma.setVar "F" 0).vars "width" :=
        hloopPost.2.1 "width" (by decide)
      _ = sigma.vars "width" := by simp
      _ = maximumRank alphabet + 3 := hwidth
  have hrecordsLoop : afterLoop.vars "records" = alphabet.length + 4 := by
    calc
      _ = (sigma.setVar "F" 0).vars "records" :=
        hloopPost.2.1 "records" (by decide)
      _ = sigma.vars "records" := by simp
      _ = alphabet.length + 4 := hrecords
  have hspaceLoop : (encodeAutomaton (alphabet, body)).length ≤
      (afterLoop.arrs "P").length := by
    rw [Lax842588Proofs.Run.arrayLength_eq hrunLoop "P"]
    exact hspace
  have hinitRun : Run B (.assign "F" (.lit 0)) sigma
      (sigma.setVar "F" 0) 2 := by
    apply Run.assign
    exact evalB_lit (by omega)
  have hcountRun : Run B (.store "P" (.var "acceptBase") (.var "F"))
      afterLoop (afterLoop.setArr "P" base body.2.2.length) 3 := by
    have hFB : afterLoop.vars "F" < B := by
      rw [hloopPost.1.2.1]
      exact hacceptingB
    apply Run.store
    · rw [evalB_var_iff]
      exact ⟨hbase'.symm, by omega⟩
    · rw [evalB_var_iff]
      exact ⟨hloopPost.1.2.1.symm, hFB⟩
    · exact hslot
  let final := afterLoop.setArr "P" base body.2.2.length
  have hskipRun : Run B .skip final final 1 := Run.skip
  refine ⟨final, ?_, ?_⟩
  · unfold readAccepting Lax842588Proofs.AutomatonRamProgram.seqs
    exact hinitRun.seq (hrunLoop.seq (hcountRun.seq hskipRun)) |>.mono (by
      unfold readAcceptingCost
      omega)
  · exact ⟨by simpa [final, ArenaLoaded] using hloaded', by simpa [final] using hspaceLoop,
      by simpa [final] using hPlenB', by simpa [final] using hfull',
      by simpa [final] using hAloop, by simpa [final] using hQloop,
      by simpa [final] using hTloop, by simpa [final] using hRloop,
      by simpa [final] using hwidthLoop, by simpa [final] using hrecordsLoop,
      by simpa [final, base] using hbase', by simpa [final] using hloopPost.1.2.1⟩

end Lax842588Proofs.AutomatonRamArenaCorrectness
