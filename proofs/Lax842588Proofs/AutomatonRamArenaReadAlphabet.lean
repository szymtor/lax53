import Lax842588Proofs.AutomatonRamArenaAlphabetLoop
import Lax842588Proofs.ImpArrayLengths

/-!
Verification of the complete alphabet-decoding phase, including the working
table header consumed by the existing evaluator backend.
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
open Lax842588Proofs.AutomatonRamCorrectness
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- State supplied by the instance-opening phase, together with enough
proof-private table space for the alphabet and fixed header. -/
def AlphabetReady (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    alphabet.length + 4 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    ∃ cursor,
      sigma.vars "alphabetCursor" = cursor ∧
      I.Represents cursor
        ((derivedPresentation : Presentation RankedAlphabetCode).toRaw alphabet)

/-- Semantic result of the scan before the zero cell and scalar header fields
are finalized. -/
def AlphabetMaterialized (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    alphabet.length + 4 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    sigma.vars "A" = alphabet.length ∧
    sigma.vars "R" = maximumRank alphabet ∧
    maximumRank alphabet + 3 < B ∧
    AlphabetPrefixEq (sigma.arrs "P") alphabet

/-- Final state produced by `readAlphabet`. -/
def AlphabetRead (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    alphabet.length + 4 ≤ (sigma.arrs "P").length ∧
    (sigma.arrs "P").length < B ∧
    sigma.vars "A" = alphabet.length ∧
    sigma.vars "R" = maximumRank alphabet ∧
    maximumRank alphabet + 3 < B ∧
    AlphabetPrefixEq (sigma.arrs "P") alphabet ∧
    (sigma.arrs "P").getD 0 0 = alphabet.length ∧
    sigma.vars "width" = maximumRank alphabet + 3 ∧
    sigma.vars "records" = alphabet.length + 4

theorem alphabetPrefixEq_set_zero {parameter alphabet : List Nat}
    (hprefix : AlphabetPrefixEq parameter alphabet)
    (hspace : alphabet.length < parameter.length) :
    AlphabetPrefixEq (parameter.set 0 alphabet.length) alphabet := by
  intro i hi
  have hsetLength : (parameter.set 0 alphabet.length).length = parameter.length := by
    simp
  rw [List.getD_eq_getElem _ _ (by rw [hsetLength]; omega)]
  rw [List.getElem_set_ne (by omega)]
  rw [← List.getD_eq_getElem parameter 0 (by omega)]
  exact hprefix i hi

theorem alphabetHeader_set {parameter alphabet : List Nat}
    (hspace : alphabet.length + 4 ≤ parameter.length)
    (hprefix : AlphabetPrefixEq parameter alphabet) :
    AlphabetPrefixEq (parameter.set 0 alphabet.length) alphabet ∧
      ((parameter.set 0 alphabet.length)[0]?).getD 0 = alphabet.length := by
  have hparameter : 0 < parameter.length := by omega
  have hsetParameter : 0 < (parameter.set 0 alphabet.length).length := by
    simpa using hparameter
  refine ⟨alphabetPrefixEq_set_zero hprefix (by omega), ?_⟩
  rw [List.getElem?_eq_getElem hsetParameter]
  rw [List.getElem_set_self hsetParameter]
  rfl

private theorem alphabetLoop_materialized_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (h1 : 1 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords I, v < B)
    (hwidthB : maximumRank alphabet + 3 < B) :
    Spec B (AlphabetLoopInv B I alphabet) alphabetLoop
      (fun _ sigma' => AlphabetMaterialized B I alphabet sigma')
      (alphabetLoopCost alphabet) := by
  refine (alphabetLoop_completed_spec B I alphabet h1 hmemB hvaluesB).post ?_
  intro sigma sigma' hpre hpost
  rcases hpost.1 with ⟨hloaded, hspace, hlenB, done, rest, cursor,
    halphabet, hcursor, hrep, hA, hR, hmaximumB, hprefix⟩
  have hlength := congrArg List.length halphabet
  have hrestLength : rest.length = 0 := by
    simp only [List.length_append] at hlength
    omega
  have hrest : rest = [] := List.eq_nil_of_length_eq_zero hrestLength
  subst rest
  simp only [List.append_nil] at halphabet
  subst done
  exact ⟨hloaded, hspace, hlenB, hpost.2, hR, hwidthB, hprefix⟩

private theorem readAlphabet_core_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (h4 : 4 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords I, v < B)
    (hwidthB : maximumRank alphabet + 3 < B) :
    Spec B (AlphabetReady B I alphabet) readAlphabet
      (fun _ sigma' => AlphabetRead B I alphabet sigma')
      (alphabetLoopCost alphabet + 50) := by
  have h1 : 1 < B := by omega
  have hloop := (alphabetLoop_materialized_spec B I alphabet h1 hmemB hvaluesB
    hwidthB).frame
  unfold readAlphabet AutomatonRamProgram.seqs
  run_vcg [hloop]
  all_goals simp_all [AlphabetReady, AlphabetLoopInv, AlphabetMaterialized,
    AlphabetRead, ArenaLoaded]
  all_goals (try omega)
  all_goals
    first
    | (apply alphabetHeader_set <;> simp_all)
    | refine ⟨[], alphabet, ?_⟩
      simp_all [maximumRank, alphabetPrefixEq_nil]
      omega

/-- The alphabet phase also preserves the allocated workspace capacity. -/
theorem readAlphabet_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (h4 : 4 < B)
    (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords I, v < B)
    (hwidthB : maximumRank alphabet + 3 < B) :
    Spec B (AlphabetReady B I alphabet) readAlphabet
      (fun sigma sigma' => AlphabetRead B I alphabet sigma' ∧
        (sigma'.arrs "P").length = (sigma.arrs "P").length)
      (alphabetLoopCost alphabet + 50) := by
  intro sigma hready
  obtain ⟨sigma', run, hread⟩ :=
    readAlphabet_core_spec B I alphabet h4 hmemB hvaluesB hwidthB sigma hready
  exact ⟨sigma', run, hread, Lax842588Proofs.Run.arrayLength_eq run "P"⟩

end Lax842588Proofs.AutomatonRamArenaCorrectness
