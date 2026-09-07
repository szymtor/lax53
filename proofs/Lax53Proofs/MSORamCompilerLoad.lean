import Lax53Proofs.MSORamCompilerProgram
import Lax53Proofs.FormulaArenaTraversalOrder
import Lax53Proofs.AutomatonRamArenaRead
import Lax53Proofs.MarkedAlphabetEncoding

/-!
Correctness of the charged loader for one intrinsic formula occurrence.
-/

namespace Lax53Proofs.MSORamCompilerLoad

set_option maxHeartbeats 3000000
open Classical

open FirstOrder
open Lax52.MSOSyntax
open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53Proofs.ArrayInput
open Lax53.RankedTree
open Lax53.ValueTranslations
open Lax53Proofs.ArenaSemantics
open Lax53Proofs.AutomatonRamArenaCorrectness
open Lax53Proofs.AutomatonRamCorrectness
open Lax53Proofs.FormulaArenaTraversalModel
open Lax53Proofs.FormulaArenaTraversalOrder
open Lax53Proofs.MarkedAlphabetEncoding
open Lax53Proofs.MSORamCompilerProgram
open Lax58.StructuralCombinators
open Lax58.WordArena

def CompilerOccurrenceReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (occurrences : List (Occurrence alphabet)) (i : Nat)
    (occurrence : Occurrence alphabet) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "compilerIndex" = i ∧
    occurrences[i]? = some occurrence ∧
    FormulaOrderRep I alphabet occurrences
      (sigma.arrs "FormulaOrder") (sigma.arrs "FormulaFOOrder")
      (sigma.arrs "FormulaSOOrder") ∧
    i < (sigma.arrs "FormulaOrder").length ∧
    i < (sigma.arrs "FormulaFOOrder").length ∧
    i < (sigma.arrs "FormulaSOOrder").length ∧
    (sigma.arrs "FormulaOrder").length < B ∧
    (sigma.arrs "FormulaFOOrder").length < B ∧
    (sigma.arrs "FormulaSOOrder").length < B ∧
    alphabet.length < B ∧ occurrence.fo < B ∧ occurrence.so < B ∧
    2 ^ occurrence.fo < B ∧ 2 ^ occurrence.so < B ∧
    symbolCount alphabet occurrence.fo occurrence.so < B ∧
    sigma.vars "A" = alphabet.length

def CompilerOccurrenceLoaded (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode) (i : Nat)
    (occurrence : Occurrence alphabet) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    ∃ root,
      root < B ∧
      sigma.vars "compilerIndex" = i + 1 ∧
      sigma.vars "currentFormula" = root ∧
      sigma.vars "currentFO" = occurrence.fo ∧
      sigma.vars "currentSO" = occurrence.so ∧
      sigma.vars "formulaTag" =
        Raw.constructorNameCode (constructorName occurrence.formula) ∧
      sigma.vars "foMarkerWords" = 2 ^ occurrence.fo ∧
      sigma.vars "soMarkerWords" = 2 ^ occurrence.so ∧
      sigma.vars "markedSymbols" =
        symbolCount alphabet occurrence.fo occurrence.so ∧
      I.Represents root occurrence.raw

theorem loadCompilerOccurrence_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (occurrences : List (Occurrence alphabet)) (i : Nat)
    (occurrence : Occurrence alphabet)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B) :
    Spec B (CompilerOccurrenceReady B I alphabet occurrences i occurrence)
      loadCompilerOccurrence
      (fun _ sigma' =>
        CompilerOccurrenceLoaded B I alphabet i occurrence sigma')
      150 := by
  intro sigma hready
  rcases hready with ⟨hloaded, hindex, hoccurrence, horder,
    hrootArray, hfoArray, hsoArray, hrootArrayB, hfoArrayB, hsoArrayB,
    halphabetB, hfoB, hsoB,
    hfoWordsB, hsoWordsB, hsymbolsB, hA⟩
  have hi : i < occurrences.length :=
    List.getElem?_eq_some_iff.mp hoccurrence |>.1
  obtain ⟨root, hrootWord, hfoWord, hsoWord, hrootRep⟩ :=
    horder.getD i hi
  have hoccurGet : occurrences.get ⟨i, hi⟩ = occurrence := by
    rw [← Option.some.injEq, ← hoccurrence]
    exact (List.getElem?_eq_getElem hi).symm
  simp only [hoccurGet] at hfoWord hsoWord hrootRep
  have hrootGet : (sigma.arrs "FormulaOrder")[i]? = some root := by
    rw [List.getElem?_eq_getElem hrootArray,
      ← Lax53Proofs.ArrayInput.getD_eq_getElem hrootArray]
    exact congrArg some hrootWord
  have hfoGet : (sigma.arrs "FormulaFOOrder")[i]? = some occurrence.fo := by
    rw [List.getElem?_eq_getElem hfoArray,
      ← Lax53Proofs.ArrayInput.getD_eq_getElem hfoArray]
    exact congrArg some hfoWord
  have hsoGet : (sigma.arrs "FormulaSOOrder")[i]? = some occurrence.so := by
    rw [List.getElem?_eq_getElem hsoArray,
      ← Lax53Proofs.ArrayInput.getD_eq_getElem hsoArray]
    exact congrArg some hsoWord
  obtain ⟨fields, hstructure⟩ :=
    formulaStructure_is_constructor occurrence.formula
  have hrootRep' : I.Represents root
      (Raw.constructor (constructorName occurrence.formula) fields) := by
    simpa [Occurrence.raw, hstructure] using hrootRep
  obtain ⟨nameRoot, _, _, hnameWord, _, hnameRep, _⟩ :=
    Lax53Proofs.ArenaSemantics.Represents.pair_words hrootRep'
  have htagWord :=
    Lax53Proofs.ArenaSemantics.Represents.nat_payload hnameRep
  have h0 : 0 < B := by omega
  have hgetB (j : Nat) : (arenaWords I).getD j 0 < B :=
    getD_lt_of_mem_bound h0 hvaluesB
  have hrootLen : root + 2 < (arenaWords I).length :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hrootRep)
  have hnameLen : nameRoot + 2 < (arenaWords I).length :=
    Lax53Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax53Proofs.ArenaSemantics.Represents.valid hnameRep)
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hrootB : root < B := by omega
  have hnameB : nameRoot < B := by omega
  have htagB :
      Raw.constructorNameCode (constructorName occurrence.formula) < B := by
    rw [← htagWord]
    exact hgetB (nameRoot + 1)
  have hnameGet : (sigma.arrs "Arena")[root + 1]? = some nameRoot := by
    rw [hloaded.1, List.getElem?_eq_getElem (by omega),
      ← Lax53Proofs.ArrayInput.getD_eq_getElem (by omega)]
    exact congrArg some hnameWord
  have htagGet : (sigma.arrs "Arena")[nameRoot + 1]? =
      some (Raw.constructorNameCode (constructorName occurrence.formula)) := by
    rw [hloaded.1, List.getElem?_eq_getElem (by omega),
      ← Lax53Proofs.ArrayInput.getD_eq_getElem (by omega)]
    exact congrArg some htagWord
  have hsymbolEq :
      alphabet.length * 2 ^ occurrence.fo * 2 ^ occurrence.so =
        symbolCount alphabet occurrence.fo occurrence.so := by
    simp [symbolCount, FiniteAutomatonEncoding.words_length]
  have hpartialB : alphabet.length * 2 ^ occurrence.fo < B := by
    apply lt_of_le_of_lt _ hsymbolsB
    rw [← hsymbolEq]
    exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  unfold loadCompilerOccurrence Lax53Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [CompilerOccurrenceLoaded, ArenaLoaded]
  all_goals try omega

end Lax53Proofs.MSORamCompilerLoad
