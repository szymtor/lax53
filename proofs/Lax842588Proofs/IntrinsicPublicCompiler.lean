import Lax842588Proofs.IntrinsicCompilerPrepare
import Lax842588Proofs.IntrinsicCompilerFrame

/-! The measured formula compiler beginning at the unchanged public input tape. -/

namespace Lax842588Proofs.IntrinsicPublicCompiler

open Lax865980Proofs.Imp Lax865980Proofs.Reasoning
open Lax146103.MSOSyntax Lax842588.RankedTree Lax842588.TreeStructure Lax842588.ValueTranslations
open Lax842588.MSOLinearTime Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.IntrinsicCompilerFields
open Lax842588Proofs.PrimitiveRecursiveCode Lax560851.WordArena
open Encodable

def program (c : Code) : Com :=
  .seq IntrinsicCompilerPrepare.program (IntrinsicCompilerFromArena.program c)

def timeBound (c : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  IntrinsicCompilerPrepare.timeBound alphabet φ t +
    (IntrinsicCompilerFromArena.inputTime alphabet (postorder alphabet φ).length +
      IntrinsicCompilerMaterialize.timeBound c (encode (alphabet, (postorder alphabet φ).map fields)))

/-- All compiler-specific premises depend only on the alphabet and sentence;
the separate arena-memory premises may depend on the complete public input. -/
structure Fits (c : Code) (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) : Prop where
  eight : 8 < B
  tags : IntrinsicFieldExtraction.TagsFit B
  alphabetLength : alphabet.length < B
  width : Lax842588.TreeModelCheckingEncoding.maximumRank alphabet + 3 < B
  steps : traversalSteps alphabet φ < B
  scopes : ∀ o ∈ postorder alphabet φ, o.fo < B ∧ o.so < B ∧
    2 ^ o.fo < B ∧ 2 ^ o.so < B ∧
    MarkedAlphabetEncoding.symbolCount alphabet o.fo o.so < B
  fields : ∀ o ∈ postorder alphabet φ, ∀ v ∈ IntrinsicCompilerFields.fields o, v < B
  rows : (2 * encode (IntrinsicFormulaInput.rowCodes (postorder alphabet φ)) + 3) ^ 2 < B
  alphabetCode : (2 * encode (alphabet.length :: alphabet) + 3) ^ 2 < B
  pairing : (encode alphabet + encode ((postorder alphabet φ).map IntrinsicCompilerFields.fields) + 1) ^ 2 < B
  compiler : IntrinsicCompilerMaterialize.wordBound c
    (encode (alphabet, (postorder alphabet φ).map IntrinsicCompilerFields.fields)) < B

theorem traversal_tags {c : Code} {B : Nat} {alphabet : RankedAlphabetCode}
    {φ : Sentence (treeSignature alphabet.toRankedAlphabet)} (h : Fits c B alphabet φ) :
    FormulaArenaTraversalInvariant.FormulaTagBounds B := by
  exact ⟨h.tags "or" (by simp [IntrinsicFieldExtraction.names]),
    h.tags "neg" (by simp [IntrinsicFieldExtraction.names]),
    h.tags "exFO" (by simp [IntrinsicFieldExtraction.names]),
    h.tags "exSO" (by simp [IntrinsicFieldExtraction.names])⟩

theorem exists_compiler : ∃ c : Code, ∀ (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) (t : Tree alphabet.toRankedAlphabet),
    Fits c B alphabet φ →
    (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords < B →
    (∀ v ∈ arenaWords (encodeRaw (msoTreeRaw alphabet φ t)), v < B) →
    Spec B (fun σ => IntrinsicCompilerPrepare.Initial B alphabet φ t σ ∧
      (σ.arrs "P").length = (compileTable alphabet ((postorder alphabet φ).map fields)).length)
      (program c)
      (fun _ σ => σ.arrs "P" = compileTable alphabet ((postorder alphabet φ).map fields) ∧
        AutomatonRamArenaCorrectness.ArenaLoaded (encodeRaw (msoTreeRaw alphabet φ t)) σ ∧
        (encodeRaw (msoTreeRaw alphabet φ t)).Represents (σ.vars "treeRoot")
          (Lax842588.StructuralRepresentations.treeStructure alphabet t))
      (timeBound c alphabet φ t) := by
  obtain ⟨c, hc⟩ := IntrinsicCompilerFromArena.exists_compiler
  refine ⟨c, fun B alphabet φ t hfit hmem hvalues => ?_⟩
  obtain ⟨p⟩ := MSORamArenaRead.instancePointers alphabet φ t
  intro σ hσ
  obtain ⟨τ, hprepare, hready, harena, htree⟩ := IntrinsicCompilerPrepare.program_spec B alphabet φ t p
    (by have := hfit.eight; omega) hmem hvalues (traversal_tags hfit)
    hfit.alphabetLength hfit.width hfit.steps hfit.scopes σ hσ.1
  have hP : (τ.arrs "P").length =
      (compileTable alphabet ((postorder alphabet φ).map fields)).length :=
    (Lax842588Proofs.Run.arrayLength_eq hprepare "P").trans hσ.2
  obtain ⟨υ, hcompile, hout⟩ := hc B _ alphabet (postorder alphabet φ)
    hfit.eight hmem hvalues hfit.tags hfit.fields hfit.rows hfit.alphabetCode
    hfit.pairing hfit.compiler τ ⟨hready, hP⟩
  refine ⟨υ, hprepare.seq hcompile, hout,
    IntrinsicCompilerFrame.preserves_arena hcompile harena, ?_⟩
  rw [hcompile.frame_var "treeRoot" (IntrinsicCompilerFrame.program_keeps c _ (by simp)), htree]
  exact p.treeRep

theorem program_keeps_array (c : Code) (a : String)
    (ha : a ∈ ["W", "TreeSymbolStack", "TreeTailStack", "S", "L", "O"]) :
    a ∉ (program c).warrs := by
  have hf : a ∉ IntrinsicCompilerPrepare.program.warrs := by
    simp at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hp : a ≠ "P" := by
    simp at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simpa [program, Com.warrs, hp] using hf

theorem program_noWrite (c : Code) : (program c).NoWrite := by
  exact ⟨by decide, IntrinsicCompilerFromArena.program_noWrite c⟩

end Lax842588Proofs.IntrinsicPublicCompiler
