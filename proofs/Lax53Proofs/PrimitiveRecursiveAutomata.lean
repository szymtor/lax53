import Lax53Proofs.PrimitiveRecursiveRam
import Lax53Proofs.EncodedAutomataComputability

/-!
First automaton application of the generic RAM realization bridge.

Intersection is executed by a single fixed RAM program, including all pure
enumeration work, with computable resource bounds. The scalar convention is
an internal interface: certified-arena parsing and eventual automaton-table
materialization are separate charged phases still needed by the uniform MSO
compiler. In particular, callers cannot supply a precompiled automaton or
an arbitrary field encoder as part of the public model-checking input.
-/

namespace Lax53Proofs.PrimitiveRecursiveAutomata

open Lax13.Ram Lax13.RamComputes
open Lax53.ValueTranslations
open Lax53Proofs.EncodedAutomataOperations Lax53Proofs.EncodedAutomataComputability
open Lax53Proofs.PrimitiveRecursiveRam

/-- The exact existing intersection operation, not a replacement algorithm
or an assumed unit-cost function call, is realized on the word-RAM. -/
theorem inter_ram :
    ∃ (p : Program) (time words : Nat → Nat), Computable time ∧ Computable words ∧
      ∀ (alphabet : RankedAlphabetCode) (M N : AutomatonCode) (w : Nat),
        words (Encodable.encode (alphabet, M, N)) ≤ 2 ^ w →
        ComputesInTime w p {[Encodable.encode (alphabet, M, N)]}
          (fun _ => [Encodable.encode (some (inter alphabet M N))])
          (fun _ => time (Encodable.encode (alphabet, M, N))) := by
  obtain ⟨p, time, words, ht, hw, hrun⟩ := exists_typed_ram inter_prim
  exact ⟨p, time, words, ht.to_comp, hw.to_comp,
    fun alphabet M N w hfit => hrun (alphabet, M, N) w hfit⟩

end Lax53Proofs.PrimitiveRecursiveAutomata
