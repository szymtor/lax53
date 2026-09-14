import Lax842588Proofs.IntrinsicModelCheckingRam
import Lax842588Proofs.IntrinsicParameterFields

-- This header consumes the table constructed at runtime, not another input tape.
#guard ¬ Lax842588Proofs.IntrinsicEvaluatorHeader.program.reads
#guard ¬ Lax842588Proofs.IntrinsicEvaluatorPrepare.program.reads

example (c : Lax842588Proofs.PrimitiveRecursiveCode.Code) :
    ∃ L : Lax865980Proofs.Compile.Layout,
      Lax865980Proofs.Compile.Com.Ok L (Lax842588Proofs.IntrinsicModelChecking.program c) :=
  Lax842588Proofs.ImpLayout.exists_layout _

example : (Lax842588Proofs.IntrinsicFormulaCompiler.zeroSymbolMap [0, 2, 1]
    (⟨1, by decide⟩ : Fin 3)).val = 1 :=
  Lax842588Proofs.IntrinsicSentenceCorrectness.zeroSymbolMap_val _ _

/-- info: 'Lax842588Proofs.IntrinsicCompilerPrepare.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicCompilerPrepare.program_spec
/-- info: 'Lax842588Proofs.IntrinsicCompilerFrame.preserves_arena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicCompilerFrame.preserves_arena
/-- info: 'Lax842588Proofs.IntrinsicPublicCompiler.exists_compiler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicPublicCompiler.exists_compiler
/-- info: 'Lax842588Proofs.IntrinsicEvaluatorHeader.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicEvaluatorHeader.program_spec
/-- info: 'Lax842588Proofs.IntrinsicEvaluatorPrepare.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicEvaluatorPrepare.program_spec
/-- info: 'Lax842588Proofs.IntrinsicSentenceCorrectness.compileRows_sentence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicSentenceCorrectness.compileRows_sentence
/-- info: 'Lax842588Proofs.IntrinsicModelChecking.exists_modelChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicModelChecking.exists_modelChecker
/-- info: 'Lax842588Proofs.ImpLayout.exists_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.ImpLayout.exists_layout
/-- info: 'Lax842588Proofs.IntrinsicModelCheckingRam.exists_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicModelCheckingRam.exists_ram
/-- info: 'Lax842588Proofs.IntrinsicModelChecking.initial_initEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicModelChecking.initial_initEnv
/-- info: 'Lax842588Proofs.IntrinsicParameterFields.sentence_fields_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicParameterFields.sentence_fields_le
