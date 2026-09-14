import Lax842588Proofs.FixedSentenceModelChecking

-- Specialization may change the program, never the stipulated tree-only tape.
run_meta do
  let statement ← Lean.getConstInfo ``Lax842588.MSOLinearTime.exists_fixed_sentence_modelChecking
  let proof ← Lean.getConstInfo
    ``Lax842588Proofs.FixedSentenceModelChecking.exists_fixed_sentence_modelChecking_proof
  unless ← Lean.Meta.isDefEq statement.type proof.type do
    throwError "Fixed-sentence proof does not have the concise headline type"

example (xs : List Nat) : ¬ (Lax842588Proofs.FixedTableLoader.program xs).reads :=
  Lax842588Proofs.FixedTableLoader.program_noRead xs

/-- info: 'Lax842588Proofs.FixedTableLoader.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.FixedTableLoader.program_spec
/-- info: 'Lax842588Proofs.FixedSentencePrepare.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.FixedSentencePrepare.program_spec
/-- info: 'Lax842588Proofs.FixedAutomatonModelChecking.exists_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.FixedAutomatonModelChecking.exists_ram
/-- info: 'Lax842588Proofs.FixedSentenceModelChecking.exists_fixed_sentence_modelChecking_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.FixedSentenceModelChecking.exists_fixed_sentence_modelChecking_proof
