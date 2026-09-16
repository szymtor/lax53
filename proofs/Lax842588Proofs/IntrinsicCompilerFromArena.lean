import Lax842588Proofs.IntrinsicFormulaInput
import Lax842588Proofs.IntrinsicAlphabetInput
import Lax842588Proofs.IntrinsicCompilerMaterialize

/-!
Compose runtime alphabet and certified-formula extraction with the complete
compiler. The precondition describes working arrays produced by the existing
arena front end; it does not supply a compiled automaton or a numeric formula.
-/

namespace Lax842588Proofs.IntrinsicCompilerFromArena

open Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Reasoning
open Lax842588.ValueTranslations Lax560851.WordArena
open Lax842588Proofs.ArenaSemantics Lax842588Proofs.FormulaArenaTraversalModel
open Lax842588Proofs.IntrinsicCompilerFields Lax842588Proofs.PrimitiveRecursiveCode
open Lax842588Proofs.PrimitiveRecursiveCompile Lax842588Proofs.PrimitiveRecursivePairing
open Encodable

def inputProgram : Com :=
  .seq IntrinsicAlphabetInput.program
    (.seq IntrinsicFormulaInput.program (pairProgram "packCode" "rowsCode" (reg 0)))

def program (c : Code) : Com :=
  .seq inputProgram (IntrinsicCompilerMaterialize.materialize c "P")

def inputTime (alphabet : RankedAlphabetCode) (count : Nat) : Nat :=
  IntrinsicAlphabetInput.timeBound alphabet + 1000 * (count + 1) + 20

def Ready (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (os : List (Occurrence alphabet)) (σ : Env) : Prop :=
  IntrinsicFormulaInput.Context B I alphabet os σ ∧
    σ.vars "formulaCount" = os.length ∧
    CompilerArrayPacking.Prefix "P" (alphabet.length :: alphabet) σ ∧
    σ.vars "A" = alphabet.length

theorem alphabet_keeps (s : String) (hs : s ∈ ["root", "arenaLen", "A", "formulaCount"]) :
    s ∉ IntrinsicAlphabetInput.program.wvars := by
  simp at hs
  rcases hs with rfl | rfl | rfl | rfl <;>
    simp [IntrinsicAlphabetInput.program, CompilerArrayPacking.program,
      CompilerArrayPacking.loop, CompilerArrayPacking.step, unpairRightProgram,
      sqrtProgram, sqrtLoop, sqrtStep, pairProgram, Com.wvars]

theorem formula_keeps_packCode : "packCode" ∉ IntrinsicFormulaInput.program.wvars := by
  simp [IntrinsicFormulaInput.program, IntrinsicFormulaInput.loop, IntrinsicFormulaInput.step,
    IntrinsicOccurrenceInput.program, MSORamCompilerProgram.loadCompilerOccurrence,
    AutomatonRamProgram.seqs, IntrinsicFieldExtraction.packedProgram,
    IntrinsicFieldExtraction.program, IntrinsicFieldExtraction.dispatch,
    IntrinsicFieldExtraction.branches, IntrinsicFieldExtraction.relation,
    IntrinsicFieldExtraction.row, CompilerArrayPacking.registerProgram,
    IntrinsicFieldExtraction.outputRegisters, pairProgram, Com.wvars]

set_option maxRecDepth 4096 in
theorem input_spec (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (os : List (Occurrence alphabet)) (h8 : 8 < B) (hmem : I.memoryWords < B)
    (hvalues : ∀ value ∈ arenaWords I, value < B)
    (htags : IntrinsicFieldExtraction.TagsFit B)
    (hfields : ∀ o ∈ os, ∀ value ∈ fields o, value < B)
    (hrows : (2 * encode (IntrinsicFormulaInput.rowCodes os) + 3) ^ 2 < B)
    (halpha : (2 * encode (alphabet.length :: alphabet) + 3) ^ 2 < B)
    (hpair : (encode alphabet + encode (os.map fields) + 1) ^ 2 < B) :
    Spec B (Ready B I alphabet os) inputProgram
      (fun _ σ => σ.vars (reg 0) = encode (alphabet, os.map fields))
      (inputTime alphabet os.length) := by
  intro σ hσ
  obtain ⟨hcontext, hcount, hp, hA⟩ := hσ
  obtain ⟨τ, ha, halphabet⟩ := IntrinsicAlphabetInput.program_spec B alphabet halpha σ ⟨hp, hA⟩
  have harr : τ.arrs = σ.arrs := funext fun a => ha.frame_arr a (by simp)
  have hkeep (s : String) (hs : s ∈ ["root", "arenaLen", "A", "formulaCount"]) :=
    ha.frame_var s (alphabet_keeps s hs)
  have hcontext' := hcontext.congr harr
    (hkeep "root" (by simp)) (hkeep "arenaLen" (by simp)) (hkeep "A" (by simp))
    (ha.frame_inp IntrinsicAlphabetInput.program_noRead)
  obtain ⟨υ, hf, hformula⟩ := IntrinsicFormulaInput.program_spec B I alphabet os
    h8 hmem hvalues htags hfields hrows τ ⟨hcontext', (hkeep "formulaCount" (by simp)).trans hcount⟩
  have hα : υ.vars "packCode" = encode alphabet :=
    (hf.frame_var "packCode" formula_keeps_packCode).trans halphabet
  obtain ⟨ρ, hrun, hout⟩ := pair_spec B (encode alphabet) (encode (os.map fields))
    "packCode" "rowsCode" (reg 0) hpair υ ⟨hα, hformula⟩
  exact ⟨ρ, (ha.seq (hf.seq hrun)).mono (by unfold inputTime; omega), hout⟩

@[simp] theorem input_warrs : inputProgram.warrs = [] := by
  simp [inputProgram, pairProgram, Com.warrs]

/-- The exact evaluator table is constructed during this one counted run. -/
theorem exists_compiler :
    ∃ c : Code, ∀ (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
      (os : List (Occurrence alphabet)),
      8 < B → I.memoryWords < B →
      (∀ value ∈ arenaWords I, value < B) → IntrinsicFieldExtraction.TagsFit B →
      (∀ o ∈ os, ∀ value ∈ fields o, value < B) →
      (2 * encode (IntrinsicFormulaInput.rowCodes os) + 3) ^ 2 < B →
      (2 * encode (alphabet.length :: alphabet) + 3) ^ 2 < B →
      (encode alphabet + encode (os.map fields) + 1) ^ 2 < B →
      IntrinsicCompilerMaterialize.wordBound c (encode (alphabet, os.map fields)) < B →
      Spec B (fun σ => Ready B I alphabet os σ ∧
        (σ.arrs "P").length = (compileTable alphabet (os.map fields)).length)
        (program c)
        (fun _ σ => σ.arrs "P" = compileTable alphabet (os.map fields))
        (inputTime alphabet os.length +
          IntrinsicCompilerMaterialize.timeBound c (encode (alphabet, os.map fields))) := by
  obtain ⟨c, hc⟩ := IntrinsicCompilerMaterialize.exists_tableCompiler
  refine ⟨c, fun B I alphabet os h8 hmem hvalues htags hfields hrows halpha hpair hword => ?_⟩
  intro σ hσ
  obtain ⟨τ, hin, hcode⟩ := input_spec B I alphabet os h8 hmem hvalues htags hfields
    hrows halpha hpair σ hσ.1
  have hP : (τ.arrs "P").length = (compileTable alphabet (os.map fields)).length := by
    rw [hin.frame_arr "P" (by simp)]
    exact hσ.2
  obtain ⟨υ, hcompile, htable, _⟩ := hc alphabet (os.map fields) B hword τ ⟨hcode, hP⟩
  exact ⟨υ, hin.seq hcompile, htable⟩

theorem program_noRead (c : Code) : ¬ (program c).reads := by
  simp [program, inputProgram, Com.reads, pairProgram, IntrinsicAlphabetInput.program_noRead,
    IntrinsicFormulaInput.program_noRead, IntrinsicCompilerMaterialize.materialize_noRead]

theorem program_noWrite (c : Code) : (program c).NoWrite := by
  simp [program, inputProgram, Com.NoWrite, pairProgram, IntrinsicAlphabetInput.program_noWrite,
    IntrinsicFormulaInput.program_noWrite, IntrinsicCompilerMaterialize.materialize_noWrite]

@[simp] theorem program_warrs (c : Code) : (program c).warrs = ["P"] := by
  simp [program, Com.warrs, IntrinsicCompilerMaterialize.materialize_warrs]

theorem program_ok (c : Code) (L : Lax759944Proofs.Legacy.Compile.Layout) (ht : 9 ≤ L.temps)
    (hp : "P" ∈ L.arrays)
    (hf : ∀ s ∈ IntrinsicFormulaInput.scalars, s ∈ L.scalars)
    (hfa : ∀ a ∈ IntrinsicFormulaInput.arrays, a ∈ L.arrays)
    (ha : ∀ s ∈ IntrinsicAlphabetInput.scalars, s ∈ L.scalars)
    (hc : ∀ j, j < space c → reg j ∈ L.scalars)
    (hu : ∀ s ∈ CompilerArrayUnpacking.scalars, s ∈ L.scalars) :
    Lax759944Proofs.Legacy.Compile.Com.Ok L (program c) := by
  have hα := IntrinsicAlphabetInput.program_ok L (by omega) hp ha
  have hφ := IntrinsicFormulaInput.program_ok L ht hf hfa
  have hm := IntrinsicCompilerMaterialize.materialize_ok c "P" L (by omega) hp hc hu
  have hpack := ha "packCode" (by simp [IntrinsicAlphabetInput.scalars])
  have hrows := hf "rowsCode" (by simp [IntrinsicFormulaInput.scalars])
  have hreg := hc 0 (by have := space_ge_three c; omega)
  simp [program, inputProgram, pairProgram, Lax759944Proofs.Legacy.Compile.Com.Ok,
    Lax759944Proofs.Legacy.Compile.Cond.Ok, Lax759944Proofs.Legacy.Compile.Expr.Ok, Lax759944Proofs.Legacy.Compile.condExpr,
    hα, hφ, hm, hpack, hrows, hreg]
  omega

end Lax842588Proofs.IntrinsicCompilerFromArena
