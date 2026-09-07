import Lax53Proofs.FixedSentenceModelChecking

-- Specialization may change the program, never the stipulated tree-only tape.
run_meta do
  let statement ← Lean.getConstInfo ``Lax53.MSOLinearTime.exists_fixed_sentence_modelChecking
  let proof ← Lean.getConstInfo
    ``Lax53Proofs.FixedSentenceModelChecking.exists_fixed_sentence_modelChecking_proof
  unless ← Lean.Meta.isDefEq statement.type proof.type do
    throwError "Fixed-sentence proof does not have the concise headline type"

example (xs : List Nat) : ¬ (Lax53Proofs.FixedTableLoader.program xs).reads :=
  Lax53Proofs.FixedTableLoader.program_noRead xs

/-- info: 'Lax53Proofs.FixedTableLoader.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.FixedTableLoader.program_spec
/-- info: 'Lax53Proofs.FixedSentencePrepare.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.FixedSentencePrepare.program_spec
/-- info: 'Lax53Proofs.FixedAutomatonModelChecking.exists_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.FixedAutomatonModelChecking.exists_ram
/-- info: 'Lax53Proofs.FixedSentenceModelChecking.exists_fixed_sentence_modelChecking_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.FixedSentenceModelChecking.exists_fixed_sentence_modelChecking_proof
