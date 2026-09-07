import Lax53Proofs.MSOTreeAutomataEquivalence

-- Each proof still certifies its original type after the concept-file merge.
run_meta do
  for (statementName, proofName) in [
      (``Lax53.MSOTreeAutomataEquivalence.automaton_definable_by_mso,
       ``Lax53Proofs.TreeAutomataToMSO.automaton_definable_by_mso_proof),
      (``Lax53.MSOTreeAutomataEquivalence.mso_definable_is_recognizable,
       ``Lax53Proofs.MSOToTreeAutomata.mso_definable_is_recognizable_proof),
      (``Lax53.MSOTreeAutomataEquivalence.recognizable_iff_msoDefinable,
       ``Lax53Proofs.MSOTreeAutomataEquivalence.recognizable_iff_msoDefinable_proof)] do
    let statement ← Lean.getConstInfo statementName
    let proof ← Lean.getConstInfo proofName
    unless ← Lean.Meta.isDefEq statement.type proof.type do
      throwError "Proof type differs from merged statement: {statementName}"
