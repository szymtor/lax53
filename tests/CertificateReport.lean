import Lax842588.StructuralRepresentations

/- Display-only report. Run bash scripts/certificate-report.sh from the repo
root; --proofs also displays witness proof bodies. Never feed this printer
output back into the certified generator. Axiom expectations are enforced
separately by CertifiedRepresentations.lean. -/

set_option format.width 100
set_option pp.fullNames true

open Lax842588.StructuralRepresentations

#print Lax560851.CertifiedDerivation.CertifiedFieldEncoding
#print Lax560851.CertifiedDerivation.CertifiedFieldEncoding.ofLaws
#print Lax560851.CertifiedDerivation.CertifiedFieldEncoding.nat
#print Lax560851.CertifiedDerivation.CertifiedFieldEncoding.fin
#print Lax560851.CertifiedDerivation.CertifiedFieldEncoding.subtype
#print Lax560851.CertifiedDerivation.CertifiedFieldEncoding.family

#print termStructure
#print termStructure.Laws
#print termStructure.certified
#print axioms termStructure.certified

#print relationStructure
#print relationStructure.Laws
#print relationStructure.certified
#print axioms relationStructure.certified

#print formulaStructure
#print equations formulaStructure
#print formulaStructure.Laws
#print formulaStructure.certified
#print axioms formulaStructure.certified

#print treeStructure
#print equations treeStructure
#print treeStructure.Laws
#print treeStructure.certified
#print axioms treeStructure.certified

-- Lean extracts the rfl/cases proofs into auxiliary theorems. Printing the
-- witness with pp.proofs alone shows their names, not their bodies.
open Lean Elab Command in
run_cmd do
  if (← getOptions).getBool `pp.proofs false then
    for parent in #[
        `Lax842588.StructuralRepresentations.termStructure.certified,
        `Lax842588.StructuralRepresentations.relationStructure.certified,
        `Lax842588.StructuralRepresentations.formulaStructure.certified,
        `Lax842588.StructuralRepresentations.treeStructure.certified,
        `Lax560851.CertifiedDerivation.CertifiedFieldEncoding.ofLaws] do
      -- Do not depend on the number or numbering of extracted proofs.
      let helpers := (← getEnv).constants.toList.filterMap fun (name, info) =>
        if parent.isPrefixOf name && info.isTheorem then some name else none
      if helpers.isEmpty then
        throwError "no extracted proof helpers found for {parent}"
      for helper in helpers.mergeSort (fun a b => decide (a.toString < b.toString)) do
        elabCommand (← `(#print $(mkIdent helper)))
