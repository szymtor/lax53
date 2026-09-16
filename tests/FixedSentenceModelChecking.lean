import Lax842588Proofs.FixedSentenceModelChecking

-- Specialization may change the program, never the stipulated tree-only tape.
-- This is now an ordinary corollary, so check its full type directly.
open Lax146103.MSOSyntax Lax842588.RankedTree Lax842588.TreeStructure
open Lax842588.ValueTranslations Lax842588.MSOLinearTime
open Lax842588.TreeModelCheckingEncoding Lax560851.RamComplexity
open Lax842588.StructuralRepresentations (treePresentation)

open Classical in
example (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    ∃ timeCoefficient wordCoefficient : Nat,
      RamComputableWithinUsing (treePresentation alphabet) natOutput
        (fun t => if t ∈ sentenceLanguage phi then 1 else 0)
        (fun t => timeCoefficient * (treeSize t + 1))
        (fun t => wordCoefficient * inputMagnitudeUsing
          (treePresentation alphabet) t) :=
  Lax842588Proofs.FixedSentenceModelChecking.exists_fixed_sentence_modelChecking_proof alphabet phi

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
