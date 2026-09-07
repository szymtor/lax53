import Lax53Proofs.IntrinsicUniformModelChecking

-- Compare types, without using the concept axiom as a proof premise.
run_meta do
  let statement ← Lean.getConstInfo ``Lax53.MSOLinearTime.exists_uniform_msoModelChecking
  let proof ← Lean.getConstInfo
    ``Lax53Proofs.IntrinsicUniformModelChecking.exists_uniform_msoModelChecking_proof
  unless ← Lean.Meta.isDefEq statement.type proof.type do
    throwError "Uniform proof does not have the concise headline type"

-- Computability is proved for the numerical envelopes; no executable
-- advice field or parameter-dependent uniform program is introduced.
example (c d : Lax53Proofs.PrimitiveRecursiveCode.Code)
    (L : Lax13Proofs.Compile.Layout) :
    Computable (Lax53Proofs.IntrinsicUniformModelChecking.timeCoefficient L c d) :=
  (Lax53Proofs.IntrinsicUniformModelChecking.timeCoefficient_prim L c d).to_comp

example (c d : Lax53Proofs.PrimitiveRecursiveCode.Code)
    (L : Lax13Proofs.Compile.Layout) :
    Computable (Lax53Proofs.IntrinsicWordBounds.wordCoefficient L c d) :=
  (Lax53Proofs.IntrinsicWordBounds.wordCoefficient_prim L c d).to_comp

/-- info: 'Lax53Proofs.IntrinsicParameterEncoding.input_code_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicParameterEncoding.input_code_le
/-- info: 'Lax53Proofs.IntrinsicCompilerParameters.fits_of_allowance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicCompilerParameters.fits_of_allowance
/-- info: 'Lax53Proofs.IntrinsicCompiledTableBounds.exists_table_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicCompiledTableBounds.exists_table_bound
/-- info: 'Lax53Proofs.IntrinsicInputBounds.input_size_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicInputBounds.input_size_le
/-- info: 'Lax53Proofs.IntrinsicTimeBounds.time_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicTimeBounds.time_le
/-- info: 'Lax53Proofs.IntrinsicWordBounds.resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicWordBounds.resources
/-- info: 'Lax53Proofs.IntrinsicWordBounds.fits_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicWordBounds.fits_words
/-- info: 'Lax53Proofs.IntrinsicUniformModelChecking.exists_uniform_msoModelChecking_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.IntrinsicUniformModelChecking.exists_uniform_msoModelChecking_proof
