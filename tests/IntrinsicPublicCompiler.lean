import Lax53Proofs.IntrinsicModelCheckingRam
import Lax53Proofs.IntrinsicParameterFields

-- This header consumes the table constructed at runtime, not another input tape.
#guard ¬ Lax53Proofs.IntrinsicEvaluatorHeader.program.reads
#guard ¬ Lax53Proofs.IntrinsicEvaluatorPrepare.program.reads

example (c : Lax53Proofs.PrimitiveRecursiveCode.Code) :
    ∃ L : Lax13Proofs.Compile.Layout,
      Lax13Proofs.Compile.Com.Ok L (Lax53Proofs.IntrinsicModelChecking.program c) :=
  Lax53Proofs.ImpLayout.exists_layout _

example : (Lax53Proofs.IntrinsicFormulaCompiler.zeroSymbolMap [0, 2, 1]
    (⟨1, by decide⟩ : Fin 3)).val = 1 :=
  Lax53Proofs.IntrinsicSentenceCorrectness.zeroSymbolMap_val _ _

/-- info: 'Lax53Proofs.IntrinsicCompilerPrepare.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicCompilerPrepare.program_spec
/-- info: 'Lax53Proofs.IntrinsicCompilerFrame.preserves_arena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicCompilerFrame.preserves_arena
/-- info: 'Lax53Proofs.IntrinsicPublicCompiler.exists_compiler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicPublicCompiler.exists_compiler
/-- info: 'Lax53Proofs.IntrinsicEvaluatorHeader.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicEvaluatorHeader.program_spec
/-- info: 'Lax53Proofs.IntrinsicEvaluatorPrepare.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicEvaluatorPrepare.program_spec
/-- info: 'Lax53Proofs.IntrinsicSentenceCorrectness.compileRows_sentence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicSentenceCorrectness.compileRows_sentence
/-- info: 'Lax53Proofs.IntrinsicModelChecking.exists_modelChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicModelChecking.exists_modelChecker
/-- info: 'Lax53Proofs.ImpLayout.exists_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.ImpLayout.exists_layout
/-- info: 'Lax53Proofs.IntrinsicModelCheckingRam.exists_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicModelCheckingRam.exists_ram
/-- info: 'Lax53Proofs.IntrinsicModelChecking.initial_initEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicModelChecking.initial_initEnv
/-- info: 'Lax53Proofs.IntrinsicParameterFields.sentence_fields_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicParameterFields.sentence_fields_le
