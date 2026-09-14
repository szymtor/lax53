import Lax842588Proofs.MSOTreeAutomataEquivalence

-- Each proof still certifies its original type after the concept-file merge.
run_meta do
  for (statementName, proofName) in [
      (``Lax842588.MSOTreeAutomataEquivalence.automaton_definable_by_mso,
       ``Lax842588Proofs.TreeAutomataToMSO.automaton_definable_by_mso_proof),
      (``Lax842588.MSOTreeAutomataEquivalence.mso_definable_is_recognizable,
       ``Lax842588Proofs.MSOToTreeAutomata.mso_definable_is_recognizable_proof),
      (``Lax842588.MSOTreeAutomataEquivalence.recognizable_iff_msoDefinable,
       ``Lax842588Proofs.MSOTreeAutomataEquivalence.recognizable_iff_msoDefinable_proof)] do
    let statement ← Lean.getConstInfo statementName
    let proof ← Lean.getConstInfo proofName
    unless ← Lean.Meta.isDefEq statement.type proof.type do
      throwError "Proof type differs from merged statement: {statementName}"
