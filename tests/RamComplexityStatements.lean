import Lax53Proofs.AutomatonLinearTime
import Lax53Proofs.IntrinsicUniformModelChecking
import Lax53Proofs.FixedSentenceModelChecking

-- All four public RAM theorems are certified by proofs with exactly their
-- concise `RamComputableWithinUsing` types.
run_meta do
  for (statement, proof) in [
      (``Lax53.AutomatonLinearTime.exists_uniform_automatonAcceptance,
        ``Lax53Proofs.AutomatonLinearTime.exists_uniform_automatonAcceptance_proof),
      (``Lax53.AutomatonLinearTime.exists_fixed_automatonAcceptance,
        ``Lax53Proofs.AutomatonLinearTime.exists_fixed_automatonAcceptance_proof),
      (``Lax53.MSOLinearTime.exists_uniform_msoModelChecking,
        ``Lax53Proofs.IntrinsicUniformModelChecking.exists_uniform_msoModelChecking_proof),
      (``Lax53.MSOLinearTime.exists_fixed_sentence_modelChecking,
        ``Lax53Proofs.FixedSentenceModelChecking.exists_fixed_sentence_modelChecking_proof)] do
    let statementInfo ← Lean.getConstInfo statement
    let proofInfo ← Lean.getConstInfo proof
    unless ← Lean.Meta.isDefEq statementInfo.type proofInfo.type do
      throwError "Proof {proof} does not match concise statement {statement}"

open Lax53.RankedTree Lax53.ValueTranslations
open Lax53.TreeModelCheckingEncoding Lax53.MSOLinearTime

-- Bundling dependent inputs changes only their Lean type, not their certified
-- raw content. In particular it introduces no new tag or advice field.
example (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) :
    automatonAcceptanceRaw ⟨M, t⟩ = automatonTreeRaw M t := rfl

example (alphabet : RankedAlphabetCode)
    (sentence : Lax52.MSOSyntax.Sentence
      (Lax53.TreeStructure.treeSignature alphabet.toRankedAlphabet))
    (tree : Tree alphabet.toRankedAlphabet) :
    modelCheckingInstanceRaw ⟨alphabet, sentence, tree⟩ =
      msoTreeRaw alphabet sentence tree := rfl

/-- info: 'Lax53Proofs.AutomatonLinearTime.exists_uniform_automatonAcceptance_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lax58.StructuralCombinators.sizeLaws,
 Lax58.WordArena.encodeRaw_represents] -/
#guard_msgs in
#print axioms Lax53Proofs.AutomatonLinearTime.exists_uniform_automatonAcceptance_proof

/-- info: 'Lax53Proofs.AutomatonLinearTime.exists_fixed_automatonAcceptance_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lax58.StructuralCombinators.sizeLaws,
 Lax58.WordArena.encodeRaw_represents] -/
#guard_msgs in
#print axioms Lax53Proofs.AutomatonLinearTime.exists_fixed_automatonAcceptance_proof
