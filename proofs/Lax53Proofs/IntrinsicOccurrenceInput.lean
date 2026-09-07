import Lax53Proofs.IntrinsicFieldExtraction
import Lax53Proofs.MSORamCompilerLoad

/-! Charged conversion of one certified postorder occurrence to a packed row. -/

namespace Lax53Proofs.IntrinsicOccurrenceInput

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax53.ValueTranslations Lax58.WordArena
open Lax53Proofs.ArenaSemantics Lax53Proofs.FormulaArenaTraversalModel
open Lax53Proofs.IntrinsicCompilerFields Lax53Proofs.MSORamCompilerLoad

def program : Com :=
  .seq MSORamCompilerProgram.loadCompilerOccurrence IntrinsicFieldExtraction.packedProgram

theorem program_spec (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (occurrences : List (Occurrence alphabet)) (i : Nat) (o : Occurrence alphabet)
    (h8 : 8 < B) (hmem : I.memoryWords < B)
    (hvalues : ∀ value ∈ arenaWords I, value < B)
    (htags : IntrinsicFieldExtraction.TagsFit B)
    (hfields : ∀ value ∈ fields o, value < B)
    (hcode : (2 * Encodable.encode (fields o) + 3) ^ 2 < B) :
    Spec B (CompilerOccurrenceReady B I alphabet occurrences i o) program
      (fun _ σ => σ.vars "fieldCode" = Encodable.encode (fields o) ∧
        σ.vars "compilerIndex" = i + 1) 825 := by
  intro σ hσ
  obtain ⟨τ, hload, hloaded⟩ := loadCompilerOccurrence_spec B I alphabet occurrences i o
    (by omega) hmem hvalues σ hσ
  obtain ⟨ha, root, _, hi, hroot, hfo, hso, htag, _, _, _, hrep⟩ := hloaded
  have hn : o.fo < B := hσ.2.2.2.2.2.2.2.2.2.2.2.1
  have hm : o.so < B := hσ.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨υ, hpack, hc⟩ := IntrinsicFieldExtraction.packedProgram_spec B I alphabet o root
    hmem hrep h8 htags hn hm hfields hcode τ ⟨ha.1, hroot, hfo, hso, htag⟩
  have hindex : υ.vars "compilerIndex" = i + 1 := by
    rw [hpack.frame_var "compilerIndex" (by
      simp [IntrinsicFieldExtraction.packedProgram, IntrinsicFieldExtraction.program,
        IntrinsicFieldExtraction.dispatch, IntrinsicFieldExtraction.branches,
        IntrinsicFieldExtraction.relation, IntrinsicFieldExtraction.row, Com.wvars,
        CompilerArrayPacking.registerProgram_wvars "fieldCode"
          IntrinsicFieldExtraction.outputRegisters "compilerIndex" (by decide)]), hi]
  exact ⟨υ, hload.seq hpack, hc, hindex⟩

@[simp] theorem program_warrs : program.warrs = [] := by
  simp [program, MSORamCompilerProgram.loadCompilerOccurrence,
    AutomatonRamProgram.seqs, Com.warrs]

theorem program_noRead : ¬ program.reads := by
  simp [program, MSORamCompilerProgram.loadCompilerOccurrence,
    AutomatonRamProgram.seqs, Com.reads, IntrinsicFieldExtraction.packedProgram_noRead]

theorem program_noWrite : program.NoWrite := by
  simp [program, MSORamCompilerProgram.loadCompilerOccurrence,
    AutomatonRamProgram.seqs, Com.NoWrite, IntrinsicFieldExtraction.packedProgram_noWrite]

end Lax53Proofs.IntrinsicOccurrenceInput
