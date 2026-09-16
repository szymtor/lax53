import Lax842588Proofs.IntrinsicModelCheckingRam
import Lax842588Proofs.IntrinsicTimeBounds
import Lax842588Proofs.IntrinsicWordBounds
import Lax842588Proofs.CheckedRamAdapter

/-! The uniform headline theorem on the unchanged certified public input. -/

namespace Lax842588Proofs.IntrinsicUniformModelChecking

open Classical Lax759944Proofs.Legacy.Ram Lax759944Proofs.Legacy.RamComputes
open Lax759944Proofs.Legacy.Compile
open Lax146103.MSOSyntax Lax842588.RankedTree Lax842588.TreeStructure Lax842588.ValueTranslations
open Lax842588.MSOLinearTime
open Lax842588.TreeModelCheckingEncoding (treeSize)
open Lax842588Proofs.PrimitiveRecursiveCode Lax842588Proofs.IntrinsicCompiledTableBounds
open Lax842588Proofs.IntrinsicTimeBounds Lax842588Proofs.IntrinsicWordBounds
open Lax560851.RamComplexity

def timeCoefficient (L : Layout) (c d : Code) (p : Nat) : Nat :=
  L.const * impTimeCoefficient c d p

theorem timeCoefficient_prim (L : Layout) (c d : Code) : Primrec (timeCoefficient L c d) :=
  Primrec.nat_mul.comp (Primrec.const _) (impTimeCoefficient_prim c d)

/-- Expanded sequential-machine implementation, embedded into `Lax808846`
by the concise reusable RAM-complexity theorem below. -/
theorem exists_uniform_msoModelChecking_expanded :
    ∃ (program : Program) (timeCoefficient wordCoefficient : Nat → Nat),
      Computable timeCoefficient ∧ Computable wordCoefficient ∧
      ∀ (alphabet : RankedAlphabetCode)
        (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
        (t : Tree alphabet.toRankedAlphabet) (w : Nat),
        InputPayloadsFitInWord alphabet phi t w →
        3 * inputStructuralSize alphabet phi t ≤ 2 ^ w →
        uniformWordBound wordCoefficient alphabet phi t ≤ 2 ^ w →
        ComputesInTime w program {Lax842588.MSOLinearTime.modelCheckingInput alphabet phi t}
          (fun _ => if t ∈ sentenceLanguage phi then [1] else [0])
          (fun _ => uniformTimeBound timeCoefficient alphabet phi t) := by
  obtain ⟨c, L, hram⟩ := IntrinsicModelCheckingRam.exists_ram
  obtain ⟨d, hd⟩ := exists_table_bound
  refine ⟨compileProgram L (IntrinsicModelChecking.program c),
    timeCoefficient L c d, wordCoefficient L c d,
    (timeCoefficient_prim L c d).to_comp, (wordCoefficient_prim L c d).to_comp, ?_⟩
  intro alphabet phi t w _hpayload _harena hw
  have hr := resources c d alphabet phi t (hd alphabet phi)
  have hf := fits_words L c d alphabet phi t w hw
  have hexec := hram (valueBound c d alphabet phi t) w alphabet phi t hf
    hr.compiler hr.memory hr.arena hr.table hr.tableLength hr.stateSpace hr.work
  have htime : L.const * IntrinsicModelChecking.timeBound c alphabet phi t ≤
      uniformTimeBound (timeCoefficient L c d) alphabet phi t := by
    have hh := Nat.mul_le_mul_left L.const (time_le c d alphabet phi (hd alphabet phi) t)
    simpa only [uniformTimeBound, timeCoefficient, Nat.mul_assoc] using hh
  intro x hx
  obtain ⟨steps, hsteps, hrun⟩ := hexec x hx
  exact ⟨steps, hsteps.trans htime, hrun⟩

/--
---
conclusion: Lax842588.MSOLinearTime.exists_uniform_msoModelChecking
---
The formula compiler is executed within the counted run. The checked embedding
into `Lax808846` includes the terminal instruction in that count. Parameter-only
computable envelopes cover its resources, the linear tree evaluator, and
the finite layout's machine addresses. Lax560851's reusable predicate hides the
expanded program and sufficient-width quantifiers without weakening them.
-/
theorem exists_uniform_msoModelChecking_proof :
    ∃ timeCoefficient wordCoefficient : Nat → Nat,
      Computable timeCoefficient ∧ Computable wordCoefficient ∧
      RamComputableWithinUsing modelCheckingPresentation natOutput
        (fun input => if input.tree ∈ sentenceLanguage input.sentence then 1 else 0)
        (fun input => uniformTimeBound timeCoefficient input.alphabet
          input.sentence input.tree)
        (fun input => uniformWordBound wordCoefficient input.alphabet
          input.sentence input.tree) := by
  obtain ⟨program, timeCoefficient, wordCoefficient, htimeComputable,
      hwordComputable, h⟩ := exists_uniform_msoModelChecking_expanded
  have htimeSuccessor : Computable (fun p => timeCoefficient p + 1) :=
    Computable.comp Primrec.succ.to_comp htimeComputable
  refine ⟨(fun p => timeCoefficient p + 1), wordCoefficient,
    htimeSuccessor, hwordComputable,
    Lax759944Proofs.LegacyRamBridge.embedProgram program, ?_⟩
  rintro ⟨alphabet, phi, t⟩ w hpayload harena hword
  have htarget := CheckedRamAdapter.computesInTime
    (U := fun _ => uniformTimeBound (fun p => timeCoefficient p + 1) alphabet phi t)
    (h alphabet phi t w hpayload harena hword) (fun _ _ =>
      CheckedRamAdapter.add_one_le_scaled (timeCoefficient (parameterSize alphabet phi))
        (treeSize t + 1) (by omega))
  by_cases hsatisfies : t ∈ sentenceLanguage phi <;>
    simpa [modelCheckingPresentation, modelCheckingInstanceRaw,
      modelCheckingInput, natOutput, Lax560851.WordArena.encode,
      Lax560851.StructuralPresentation.presentationOf, hsatisfies] using!
        htarget

end Lax842588Proofs.IntrinsicUniformModelChecking
