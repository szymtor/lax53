import Lax842588Proofs.AutomatonRamArenaReadAlphabet

/-!
Verification of the fixed, non-list part of the represented automaton body.
The phase extracts the state count and certified cursors for the transition
and accepting-state lists, then writes only the corresponding private table
header cell.
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

def AutomatonBodyReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (capacity : Nat) (sigma : Env) : Prop :=
  AlphabetRead B I alphabet sigma ∧
    capacity ≤ (sigma.arrs "P").length ∧
    ∃ root,
      sigma.vars "bodyRoot" = root ∧
      I.Represents root
        ((derivedPresentation : Presentation AutomatonCode).toRaw body)

def AutomatonBodyOpened (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (capacity : Nat) (sigma : Env) : Prop :=
  AlphabetRead B I alphabet sigma ∧
    capacity ≤ (sigma.arrs "P").length ∧
    sigma.vars "Q" = body.1 ∧
    I.Represents (sigma.vars "transitionCursor")
      ((derivedPresentation : Presentation (List TransitionCode)).toRaw body.2.1) ∧
    I.Represents (sigma.vars "acceptCursor")
      ((derivedPresentation : Presentation (List Nat)).toRaw body.2.2) ∧
    (sigma.arrs "P").getD (alphabet.length + 1) 0 = body.1

theorem alphabetPrefixEq_set_after {parameter alphabet : List Nat} {value : Nat}
    (hprefix : AlphabetPrefixEq parameter alphabet)
    (hspace : alphabet.length + 1 < parameter.length) :
    AlphabetPrefixEq (parameter.set (alphabet.length + 1) value) alphabet := by
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  rw [List.getElem_set_ne (by omega)]
  rw [← List.getD_eq_getElem parameter 0 (by omega)]
  exact hprefix i hi

theorem getD_zero_set_after {parameter : List Nat} {index value : Nat}
    (hindex : index < parameter.length) (hne : index ≠ 0) :
    (parameter.set index value).getD 0 0 = parameter.getD 0 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  rw [List.getElem_set_ne (by omega)]
  rw [← List.getD_eq_getElem parameter 0 (by omega)]

theorem openAutomatonBody_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (body : AutomatonCode)
    (capacity : Nat) (h0 : 0 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords I, v < B) :
    Spec B (AutomatonBodyReady B I alphabet body capacity)
      openAutomatonBody
      (fun _ sigma' => AutomatonBodyOpened B I alphabet body capacity sigma')
      60 := by
  intro sigma hready
  rcases hready with ⟨halphabet, hcapacity, root, hroot, hbodyRep⟩
  rcases halphabet with ⟨hloaded, hPspace, hPlenB, hA, hR, hwidthB,
    hprefix, hzero, hwidth, hrecords⟩
  have hbodyRep' : I.Represents root
      ((prod nat (prod (list (derivedPresentation : Presentation TransitionCode))
        (list nat))).toRaw body) := by
    simpa [derivedPresentation] using hbodyRep
  obtain ⟨qAddress, tailAddress, hrootTag, hqWord, htailWord,
      hqRep, htailRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.prod_fields hbodyRep'
  obtain ⟨transitionAddress, acceptAddress, htailTag, htransitionWord,
      hacceptWord, htransitionRep, hacceptRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.prod_fields htailRep
  have hqPayload :=
    Lax842588Proofs.ArenaSemantics.Represents.nat_payload hqRep
  have hrootValid := Lax842588Proofs.ArenaSemantics.Represents.valid hbodyRep
  have hqValid := Lax842588Proofs.ArenaSemantics.Represents.valid hqRep
  have htailValid := Lax842588Proofs.ArenaSemantics.Represents.valid htailRep
  have htransitionValid :=
    Lax842588Proofs.ArenaSemantics.Represents.valid htransitionRep
  have hacceptValid := Lax842588Proofs.ArenaSemantics.Represents.valid hacceptRep
  have hrootLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hrootValid
  have hqLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hqValid
  have htailLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length htailValid
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hgetB (i : Nat) : (arenaWords I).getD i 0 < B :=
    getD_lt_of_mem_bound h0 hvaluesB
  have hgetOptB (i : Nat) : ((arenaWords I)[i]?).getD 0 < B := by
    simpa [List.getD_eq_getElem?_getD] using hgetB i
  have hrootGet : (arenaWords I)[root + 1] = qAddress := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem (by omega)]
    exact hqWord
  have hqGet : (arenaWords I)[qAddress + 1] = body.1 := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem (by omega)]
    exact hqPayload
  have htailGet : (arenaWords I)[root + 2] = tailAddress := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem hrootLen]
    exact htailWord
  have htransitionGet : (arenaWords I)[tailAddress + 1] = transitionAddress := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem (by omega)]
    exact htransitionWord
  have hacceptGet : (arenaWords I)[tailAddress + 2] = acceptAddress := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem htailLen]
    exact hacceptWord
  have hrootGetD : ((arenaWords I)[root + 1]?).getD 0 = qAddress := by
    simpa [List.getD_eq_getElem?_getD] using hqWord
  have hqGetD : ((arenaWords I)[qAddress + 1]?).getD 0 = body.1 := by
    simpa [List.getD_eq_getElem?_getD] using hqPayload
  have htailGetD : ((arenaWords I)[root + 2]?).getD 0 = tailAddress := by
    simpa [List.getD_eq_getElem?_getD] using htailWord
  have htransitionGetD : ((arenaWords I)[tailAddress + 1]?).getD 0 =
      transitionAddress := by
    simpa [List.getD_eq_getElem?_getD] using htransitionWord
  have hacceptGetD : ((arenaWords I)[tailAddress + 2]?).getD 0 =
      acceptAddress := by
    simpa [List.getD_eq_getElem?_getD] using hacceptWord
  have hrootGetDB : ((arenaWords I)[root + 1]?).getD 0 < B := hgetOptB _
  have hqGetDB : ((arenaWords I)[qAddress + 1]?).getD 0 < B := hgetOptB _
  have htailGetDB : ((arenaWords I)[root + 2]?).getD 0 < B := hgetOptB _
  have htransitionGetDB : ((arenaWords I)[tailAddress + 1]?).getD 0 < B :=
    hgetOptB _
  have hacceptGetDB : ((arenaWords I)[tailAddress + 2]?).getD 0 < B :=
    hgetOptB _
  have hprefixAfter := alphabetPrefixEq_set_after
    (value := body.1) hprefix
    (by omega : alphabet.length + 1 < (sigma.arrs "P").length)
  have hzeroAfter := getD_zero_set_after
    (value := body.1)
    (by omega : alphabet.length + 1 < (sigma.arrs "P").length) (by omega)
  have hqAfter :
      (((sigma.arrs "P").set (alphabet.length + 1) body.1)[alphabet.length + 1]?).getD 0 =
        body.1 := by
    have hindex : alphabet.length + 1 < (sigma.arrs "P").length := by omega
    rw [List.getElem?_eq_getElem (by simpa using hindex)]
    rw [List.getElem_set_self (by simpa using hindex)]
    rfl
  have hqAfterB :
      (((sigma.arrs "P").set (alphabet.length + 1) body.1)[alphabet.length + 1]?).getD 0 <
        B := by
    rw [hqAfter]
    rw [← hqPayload]
    exact hgetB _
  have htransitionRep' : I.Represents transitionAddress
      ((derivedPresentation : Presentation (List TransitionCode)).toRaw body.2.1) := by
    simpa [derivedPresentation] using htransitionRep
  have hacceptRep' : I.Represents acceptAddress
      ((derivedPresentation : Presentation (List Nat)).toRaw body.2.2) := by
    simpa [derivedPresentation] using hacceptRep
  unfold openAutomatonBody AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [AutomatonBodyOpened, AlphabetRead, ArenaLoaded]
  all_goals omega

end Lax842588Proofs.AutomatonRamArenaCorrectness
