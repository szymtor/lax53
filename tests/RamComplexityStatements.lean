import Lax842588Proofs.AutomatonLinearTime
import Lax842588Proofs.IntrinsicUniformModelChecking
import Lax842588Proofs.FixedSentenceModelChecking

-- Both public RAM theorems are certified by proofs with exactly their
-- concise `RamComputableWithinUsing` types.
run_meta do
  for (statement, proof) in [
      (``Lax842588.AutomatonLinearTime.exists_uniform_automatonAcceptance,
        ``Lax842588Proofs.AutomatonLinearTime.exists_uniform_automatonAcceptance_proof),
      (``Lax842588.MSOLinearTime.exists_uniform_msoModelChecking,
        ``Lax842588Proofs.IntrinsicUniformModelChecking.exists_uniform_msoModelChecking_proof)] do
    let statementInfo ← Lean.getConstInfo statement
    let proofInfo ← Lean.getConstInfo proof
    unless ← Lean.Meta.isDefEq statementInfo.type proofInfo.type do
      throwError "Proof {proof} does not match concise statement {statement}"

open Lax842588.RankedTree Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding Lax842588.MSOLinearTime
open Lax560851.RamComplexity

-- The fixed-automaton corollary remains available with its original input
-- presentation and resource bounds, without a separate public axiom.
open Lax842588.AutomatonLinearTime Classical in
example (M : EncodedAutomaton) :
    ∃ timeCoefficient wordCoefficient : Nat,
      RamComputableWithinUsing (fixedAutomatonPresentation M) natOutput
        (fun t => if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0)
        (fun t => timeCoefficient * (treeSize t + 1))
        (fun t => wordCoefficient * inputMagnitudeUsing
          (fixedAutomatonPresentation M) t) :=
  Lax842588Proofs.AutomatonLinearTime.exists_fixed_automatonAcceptance_proof M

-- Bundling dependent inputs changes only their Lean type, not their certified
-- raw content. In particular it introduces no new tag or advice field.
example (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) :
    automatonAcceptanceRaw ⟨M, t⟩ = automatonTreeRaw M t := rfl

example (alphabet : RankedAlphabetCode)
    (sentence : Lax146103.MSOSyntax.Sentence
      (Lax842588.TreeStructure.treeSignature alphabet.toRankedAlphabet))
    (tree : Tree alphabet.toRankedAlphabet) :
    modelCheckingInstanceRaw ⟨alphabet, sentence, tree⟩ =
      msoTreeRaw alphabet sentence tree := rfl

/-- info: 'Lax842588Proofs.AutomatonLinearTime.exists_uniform_automatonAcceptance_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lax560851.StructuralCombinators.sizeLaws,
 Lax560851.WordArena.encodeRaw_represents] -/
#guard_msgs in
#print axioms Lax842588Proofs.AutomatonLinearTime.exists_uniform_automatonAcceptance_proof

/-- info: 'Lax842588Proofs.AutomatonLinearTime.exists_fixed_automatonAcceptance_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lax842588.AutomatonLinearTime.exists_uniform_automatonAcceptance] -/
#guard_msgs in
#print axioms Lax842588Proofs.AutomatonLinearTime.exists_fixed_automatonAcceptance_proof
