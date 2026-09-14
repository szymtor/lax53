import Lax842588Proofs.AutomatonRamArenaRead

/-!
Proof-only verification of the alphabet phase of the charged structural
front end.  The phase walks the certified list cursor and materializes only
the evaluator's rank prefix and maximum rank.
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
open Lax842588Proofs.AutomatonRamCorrectness
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- The already decoded alphabet ranks occupy cells `1, ..., done.length`.
Cell zero is deliberately left for the final alphabet length. -/
def AlphabetPrefixEq (parameter : List Nat) (done : List Nat) : Prop :=
  ∀ i < done.length, parameter.getD (i + 1) 0 = done.getD i 0

theorem alphabetPrefixEq_nil (parameter : List Nat) :
    AlphabetPrefixEq parameter [] := by
  simp [AlphabetPrefixEq]

theorem alphabetPrefixEq_set_append {parameter done : List Nat} {rank : Nat}
    (hprefix : AlphabetPrefixEq parameter done)
    (hspace : done.length + 1 < parameter.length) :
    AlphabetPrefixEq (parameter.set (done.length + 1) rank) (done ++ [rank]) := by
  intro i hi
  by_cases hdone : i < done.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega)]
    rw [List.getElem_set_ne (by omega)]
    rw [List.getD_eq_getElem _ _ hi]
    rw [List.getElem_append_left hdone]
    rw [← List.getD_eq_getElem parameter 0 (by omega)]
    rw [← List.getD_eq_getElem done 0 hdone]
    exact hprefix i hdone
  · have hiEq : i = done.length := by simp at hi; omega
    subst i
    rw [List.getD_eq_getElem _ _ (by simpa using hspace)]
    rw [List.getElem_set_self (by simpa using hspace)]
    simp

/-- Loop invariant: `done` is the decoded prefix, `rest` is represented at
the current certified list cursor, and `R` is the prefix maximum. -/
def AlphabetLoopInv (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    alphabet.length + 4 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    ∃ done rest cursor,
      alphabet = done ++ rest ∧
      sigma.vars "alphabetCursor" = cursor ∧
      I.Represents cursor
        ((derivedPresentation : Presentation RankedAlphabetCode).toRaw rest) ∧
      sigma.vars "A" = done.length ∧
      sigma.vars "R" = maximumRank done ∧
      maximumRank done < B ∧
      AlphabetPrefixEq (sigma.arrs "P") done

private theorem arenaLookup (I : WordImage) (address value : Nat)
    (hlt : address < (arenaWords I).length)
    (hword : (arenaWords I).getD address 0 = value) :
    (arenaWords I)[address]? = some value := by
  rw [List.getElem?_eq_getElem hlt]
  rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem hlt]
  exact congrArg some hword

private theorem listCursorLookup (I : WordImage) (address tag : Nat)
    (hvalid : I.ValidAddress address)
    (htag : (arenaWords I).getD address 0 = tag) :
    (arenaWords I)[address]? = some tag := by
  have hlt :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hvalid
  exact arenaLookup I address tag (by omega) htag

theorem alphabetCondition_value (B : Nat) (I : WordImage)
    (rest : RankedAlphabetCode) (cursor : Nat) (sigma : Env)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hloaded : ArenaLoaded I sigma)
    (hcursor : sigma.vars "alphabetCursor" = cursor)
    (hrep : I.Represents cursor
      ((derivedPresentation : Presentation RankedAlphabetCode).toRaw rest)) :
    alphabetCondition.evalB B sigma = some (!rest.isEmpty) := by
  have hvalid := Lax842588Proofs.ArenaSemantics.Represents.valid hrep
  have hcursorLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hvalid
  have hcursorB : cursor < B := by
    have harenaLength : (arenaWords I).length = I.memoryWords := by
      simp [arenaWords, WordImage.memoryWords]
    omega
  have hvar : (Expr.var "alphabetCursor").evalB B sigma = some cursor := by
    rw [evalB_var_iff]
    exact ⟨hcursor.symm, by simpa [hcursor] using hcursorB⟩
  cases rest with
  | nil =>
      have htag := Lax842588Proofs.ArenaSemantics.Represents.list_tag hrep
      have hlookup := listCursorLookup I cursor WordImage.natTag hvalid (by
        simpa using htag)
      have hlookup' : (sigma.arrs "Arena")[cursor]? = some WordImage.natTag := by
        simpa [hloaded.1] using hlookup
      have hget := evalB_get hvar hlookup' (by simp [WordImage.natTag]; omega)
      simpa [alphabetCondition, WordImage.natTag] using
        (evalB_condEq hget (evalB_lit h1))
  | cons rank rest =>
      have htag := Lax842588Proofs.ArenaSemantics.Represents.list_tag hrep
      have hlookup := listCursorLookup I cursor WordImage.pairTag hvalid (by
        simpa using htag)
      have hlookup' : (sigma.arrs "Arena")[cursor]? = some WordImage.pairTag := by
        simpa [hloaded.1] using hlookup
      have hget := evalB_get hvar hlookup' (by simpa [WordImage.pairTag] using h1)
      simpa [alphabetCondition, WordImage.pairTag] using
        (evalB_condEq hget (evalB_lit h1))

theorem alphabetCondition_defined (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (h1 : 1 < B)
    (hmemB : I.memoryWords < B) :
    ∀ sigma, AlphabetLoopInv B I alphabet sigma →
      ∃ v, alphabetCondition.evalB B sigma = some v := by
  intro sigma hInv
  rcases hInv.2.2.2 with ⟨done, rest, cursor, halphabet, hcursor,
    hrep, hA, hR, hmaximumB, hprefix⟩
  exact ⟨!rest.isEmpty,
    alphabetCondition_value B I rest cursor sigma h1 hmemB hInv.1 hcursor hrep⟩

theorem alphabetBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords I, v < B) :
    Spec B
      (fun sigma => AlphabetLoopInv B I alphabet sigma ∧
        alphabetCondition.evalB B sigma = some true)
      alphabetBody
      (fun sigma sigma' => AlphabetLoopInv B I alphabet sigma' ∧
        sigma'.vars "A" = sigma.vars "A" + 1)
      100 := by
  intro sigma hpre
  rcases hpre.1 with ⟨hloaded, hPspace, hPlenB, done, rest, cursor,
    halphabet, hcursor, hrep, hA, hR, hmaximumB, hprefix⟩
  have hcondition := alphabetCondition_value B I rest cursor sigma h1 hmemB
    hloaded hcursor hrep
  cases rest with
  | nil =>
      simp at hcondition
      rw [hcondition] at hpre
      simp at hpre
  | cons rank rest =>
      obtain ⟨valueAddress, restAddress, hcursorTag, hvalueWord,
        hrestWord, hvalueRep, hrestRep⟩ :=
        Lax842588Proofs.ArenaSemantics.Represents.list_cons hrep
      have hcursorValid := Lax842588Proofs.ArenaSemantics.Represents.valid hrep
      have hvalueValid := Lax842588Proofs.ArenaSemantics.Represents.valid hvalueRep
      have hrestValid := Lax842588Proofs.ArenaSemantics.Represents.valid hrestRep
      have hrestRep' : I.Represents restAddress
          ((derivedPresentation : Presentation RankedAlphabetCode).toRaw rest) := by
        simpa [derivedPresentation] using hrestRep
      have hcursorLen :=
        Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hcursorValid
      have hvalueLen :=
        Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hvalueValid
      have hrestLen :=
        Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hrestValid
      have harenaLength : (arenaWords I).length = I.memoryWords := by
        simp [arenaWords, WordImage.memoryWords]
      have hcursorB : cursor + 2 < B := by omega
      have hvalueB : valueAddress + 1 < B := by omega
      have hrestB : restAddress < B := by omega
      have hvalueLookup : (arenaWords I)[cursor + 1]? = some valueAddress :=
        arenaLookup I (cursor + 1) valueAddress (by omega) hvalueWord
      have hrestLookup : (arenaWords I)[cursor + 2]? = some restAddress :=
        arenaLookup I (cursor + 2) restAddress hcursorLen hrestWord
      have hrestGet : (arenaWords I)[cursor + 2] = restAddress := by
        rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem hcursorLen]
        exact hrestWord
      have hrankWord :=
        Lax842588Proofs.ArenaSemantics.Represents.nat_payload hvalueRep
      have hrankLookup : (arenaWords I)[valueAddress + 1]? = some rank :=
        arenaLookup I (valueAddress + 1) rank (by omega) hrankWord
      have hrankB : rank < B := by
        have h := getD_lt_of_mem_bound (i := valueAddress + 1) (by omega) hvaluesB
        rwa [hrankWord] at h
      have hdoneLen : done.length < alphabet.length := by
        have hlength := congrArg List.length halphabet
        simp only [List.length_append, List.length_cons] at hlength
        omega
      have hstoreSpace : done.length + 1 < (sigma.arrs "P").length := by
        omega
      have hprefix' := alphabetPrefixEq_set_append (rank := rank) hprefix hstoreSpace
      have hmax : maximumRank (done ++ [rank]) = max (maximumRank done) rank := by
        simp [maximumRank, List.foldl_append]
      have hmaximumB' : maximumRank (done ++ [rank]) < B := by
        rw [hmax]
        exact max_lt hmaximumB hrankB
      have hrankLe : rank ≤ maximumRank (done ++ [rank]) := by
        rw [hmax]
        exact Nat.le_max_right _ _
      by_cases hRank : maximumRank done < rank
      · have hmaxCase : max (maximumRank done) rank = rank :=
          Nat.max_eq_right (Nat.le_of_lt hRank)
        unfold alphabetBody AutomatonRamProgram.seqs
        run_vcg
        all_goals simp_all [AlphabetLoopInv, ArenaLoaded, alphabetCondition]
        all_goals (try omega)
        all_goals
          refine ⟨done ++ [rank], rest, ?_⟩
          simp_all
      · have hmaxCase : max (maximumRank done) rank = maximumRank done :=
          Nat.max_eq_left (Nat.le_of_not_gt hRank)
        unfold alphabetBody AutomatonRamProgram.seqs
        run_vcg
        all_goals simp_all [AlphabetLoopInv, ArenaLoaded, alphabetCondition]
        all_goals (try omega)
        all_goals
          refine ⟨done ++ [rank], rest, ?_⟩
          simp_all

end Lax842588Proofs.AutomatonRamArenaCorrectness
