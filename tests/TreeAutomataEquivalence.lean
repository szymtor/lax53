import Lax842588Proofs.MSOTreeAutomataEquivalence
import Lax842588Proofs.TreeAutomataToMSO
import Lax842588Proofs.MSOToTreeAutomata
import Lean.Util.CollectAxioms

-- Each proof certifies its retained public statement.
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

-- These public contracts must remain visible in the Archive assumption graph.
run_meta do
  let background : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checks : Array (Lean.Name × Array Lean.Name) := #[
    (``Lax842588Proofs.TreeAutomataToMSO.automaton_definable_by_mso_proof, #[]),
    (``Lax842588Proofs.MSOToTreeAutomata.mso_definable_is_recognizable_proof,
      #[``Lax842588.Determinization.exists_deterministic_equivalent]),
    (``Lax842588Proofs.MSOTreeAutomataEquivalence.recognizable_iff_msoDefinable_proof,
      #[``Lax842588.MSOTreeAutomataEquivalence.automaton_definable_by_mso,
        ``Lax842588.MSOTreeAutomataEquivalence.mso_definable_is_recognizable])]
  for (proof, expected) in checks do
    let axioms ← Lean.collectAxioms proof
    let actual := (axioms.filter fun ax => !background.contains ax).qsort Lean.Name.lt
    unless actual == expected.qsort Lean.Name.lt do
      throwError "Unexpected public dependencies of {proof}: {actual.toList}"
