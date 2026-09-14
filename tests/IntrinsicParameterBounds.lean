import Lax842588Proofs.IntrinsicUniformModelChecking

-- Compare types, without using the concept axiom as a proof premise.
run_meta do
  let statement ← Lean.getConstInfo ``Lax842588.MSOLinearTime.exists_uniform_msoModelChecking
  let proof ← Lean.getConstInfo
    ``Lax842588Proofs.IntrinsicUniformModelChecking.exists_uniform_msoModelChecking_proof
  unless ← Lean.Meta.isDefEq statement.type proof.type do
    throwError "Uniform proof does not have the concise headline type"

-- Computability is proved for the numerical envelopes; no executable
-- advice field or parameter-dependent uniform program is introduced.
example (c d : Lax842588Proofs.PrimitiveRecursiveCode.Code)
    (L : Lax865980Proofs.Compile.Layout) :
    Computable (Lax842588Proofs.IntrinsicUniformModelChecking.timeCoefficient L c d) :=
  (Lax842588Proofs.IntrinsicUniformModelChecking.timeCoefficient_prim L c d).to_comp

example (c d : Lax842588Proofs.PrimitiveRecursiveCode.Code)
    (L : Lax865980Proofs.Compile.Layout) :
    Computable (Lax842588Proofs.IntrinsicWordBounds.wordCoefficient L c d) :=
  (Lax842588Proofs.IntrinsicWordBounds.wordCoefficient_prim L c d).to_comp

/-- info: 'Lax842588Proofs.IntrinsicParameterEncoding.input_code_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicParameterEncoding.input_code_le
/-- info: 'Lax842588Proofs.IntrinsicCompilerParameters.fits_of_allowance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicCompilerParameters.fits_of_allowance
/-- info: 'Lax842588Proofs.IntrinsicCompiledTableBounds.exists_table_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicCompiledTableBounds.exists_table_bound
/-- info: 'Lax842588Proofs.IntrinsicInputBounds.input_size_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicInputBounds.input_size_le
/-- info: 'Lax842588Proofs.IntrinsicTimeBounds.time_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicTimeBounds.time_le
/-- info: 'Lax842588Proofs.IntrinsicWordBounds.resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicWordBounds.resources
/-- info: 'Lax842588Proofs.IntrinsicWordBounds.fits_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicWordBounds.fits_words
/-- info: 'Lax842588Proofs.IntrinsicUniformModelChecking.exists_uniform_msoModelChecking_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicUniformModelChecking.exists_uniform_msoModelChecking_proof
