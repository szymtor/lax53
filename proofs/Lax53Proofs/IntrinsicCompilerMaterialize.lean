import Lax53Proofs.IntrinsicCompilerOutput
import Lax53Proofs.CompilerArrayUnpacking

/-!
The full intrinsic compiler and its output adapter as one composable IMP body.
The input word must have been constructed at runtime from certified fields.
Compilation, removal of the typed bridge's output tag, and every output store
are all charged. This body performs no tape I/O; the surrounding model checker
retains ownership of reading the canonical arena and emitting its answer.
-/

namespace Lax53Proofs.IntrinsicCompilerMaterialize

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax53Proofs.PrimitiveRecursiveCode Lax53Proofs.PrimitiveRecursiveCompile
open Lax53Proofs.PrimitiveRecursiveBounds Lax53Proofs.PrimitiveRecursiveCorrectness
open Lax53Proofs.IntrinsicCompilerFields
open Lax53.ValueTranslations
open Encodable

def materialize (c : Code) (arr : String) : Com :=
  .seq (compile c 0)
    (.seq (.assign "unpackCode" (.sub (.var (reg 0)) (.lit 1)))
      (CompilerArrayUnpacking.program arr))

def timeBound (c : Code) (n : Nat) : Nat := 300 * (budget c n + 1) ^ 2

def wordBound (c : Code) (n : Nat) : Nat := 3 * budget c n + 10

theorem timeBound_prim (c : Code) : Primrec (timeBound c) := by
  have hb := Primrec.nat_add.comp (budget_prim c) (Primrec.const 1)
  change Primrec (fun n => 300 * (budget c n + 1) ^ 2)
  simpa only [Nat.pow_two] using
    Primrec.nat_mul.comp (Primrec.const 300) (Primrec.nat_mul.comp hb hb)

theorem wordBound_prim (c : Code) : Primrec (wordBound c) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) (budget_prim c))
    (Primrec.const 10)

theorem materialize_spec (c : Code) (B n : Nat) (arr : String) (xs : List Nat)
    (hc : c.eval n = encode (some xs)) (hB : wordBound c n < B) :
    Spec B (fun σ => σ.vars (reg 0) = n ∧ xs.length ≤ (σ.arrs arr).length)
      (materialize c arr)
      (fun _ σ => (σ.arrs arr).take xs.length = xs ∧ σ.vars "unpackIndex" = xs.length)
      (timeBound c n) := by
  have heval := eval_le_budget c n n le_rfl
  rw [hc, encode_some] at heval
  have hlen := length_le_encode xs
  have hbudget : budget c n < B := by unfold wordBound at hB; omega
  have hunpackB : 2 * encode xs + 3 < B := by unfold wordBound at hB; omega
  intro σ hσ
  obtain ⟨hinput, hcapacity⟩ := hσ
  obtain ⟨τ, hcall, hout⟩ := compile_correct c 0 B n n le_rfl hbudget σ hinput
  have harr : τ.arrs arr = σ.arrs arr := hcall.frame_arr arr (by rw [compile_warrs]; simp)
  have hvalue : τ.vars (reg 0) = encode xs + 1 := by simpa [hc] using hout
  have hstrip : Run B (.assign "unpackCode" (.sub (.var (reg 0)) (.lit 1))) τ
      (τ.setVar "unpackCode" (encode xs)) 4 := by
    apply Run.assign
    simp [Expr.evalB, hvalue, fit_self (show encode xs + 1 < B by omega),
      fit_self (show 1 < B by omega), fit_self (show encode xs < B by omega)]
  obtain ⟨υ, hrun, htable⟩ := CompilerArrayUnpacking.program_spec B arr xs hunpackB
    (τ.setVar "unpackCode" (encode xs)) (by simpa [harr] using hcapacity)
  refine ⟨υ, (hcall.seq (hstrip.seq hrun)).mono ?_, htable⟩
  have hprod : (encode xs + 1) * (xs.length + 1) ≤ budget c n * budget c n :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold timeBound
  nlinarith

/-- Exact extents, as used by the evaluator's private `P` array, give exact
table equality rather than merely prefix equality. -/
theorem materialize_exact_spec (c : Code) (B n : Nat) (arr : String) (xs : List Nat)
    (hc : c.eval n = encode (some xs)) (hB : wordBound c n < B) :
    Spec B (fun σ => σ.vars (reg 0) = n ∧ (σ.arrs arr).length = xs.length)
      (materialize c arr)
      (fun _ σ => σ.arrs arr = xs ∧ σ.vars "unpackIndex" = xs.length)
      (timeBound c n) := by
  intro σ hσ
  obtain ⟨τ, hrun, hp, hi⟩ := materialize_spec c B n arr xs hc hB σ ⟨hσ.1, by omega⟩
  have hlen : (τ.arrs arr).length = xs.length := (Run.arrayLength_eq hrun arr).trans hσ.2
  exact ⟨τ, hrun, by simpa [← hlen] using hp, hi⟩

theorem materialize_noRead (c : Code) (arr : String) : ¬ (materialize c arr).reads := by
  simp [materialize, Com.reads, compile_not_reads, CompilerArrayUnpacking.program_noRead]

theorem materialize_noWrite (c : Code) (arr : String) : (materialize c arr).NoWrite := by
  simp [materialize, Com.NoWrite, compile_noWrite, CompilerArrayUnpacking.program_noWrite]

theorem materialize_warrs (c : Code) (arr : String) : (materialize c arr).warrs = [arr] := by
  simp [materialize, Com.warrs, compile_warrs, CompilerArrayUnpacking.program_warrs]

theorem materialize_ok (c : Code) (arr : String) (L : Layout) (ht : 5 ≤ L.temps)
    (ha : arr ∈ L.arrays) (hc : ∀ j, j < space c → reg j ∈ L.scalars)
    (hu : ∀ name ∈ CompilerArrayUnpacking.scalars, name ∈ L.scalars) :
    Com.Ok L (materialize c arr) := by
  have hcompile := compile_ok c 0 L ht (by simpa using hc)
  have hunpack := CompilerArrayUnpacking.program_ok arr L ht ha hu
  have hr := hc 0 (by have := space_ge_three c; omega)
  have hcode := hu "unpackCode" (by simp [CompilerArrayUnpacking.scalars])
  simp [materialize, Com.Ok, Expr.Ok, hcompile, hunpack, hr, hcode]
  omega

/-- One finite compiler body works for every alphabet and normalized field
stream and leaves the exact existing evaluator table in `P`. Its bounds are
primitive recursive in the runtime-built numeric input. -/
theorem exists_tableCompiler :
    ∃ c : Code, ∀ (alphabet : RankedAlphabetCode) (rows : List (List Nat)) (B : Nat),
      wordBound c (encode (alphabet, rows)) < B →
      Spec B (fun σ => σ.vars (reg 0) = encode (alphabet, rows) ∧
          (σ.arrs "P").length = (compileTable alphabet rows).length)
        (materialize c "P")
        (fun _ σ => σ.arrs "P" = compileTable alphabet rows ∧
          σ.vars "unpackIndex" = (compileTable alphabet rows).length)
        (timeBound c (encode (alphabet, rows))) := by
  obtain ⟨c, hc⟩ := exists_typed_code compileTable_prim
  refine ⟨c, fun alphabet rows B hB => ?_⟩
  exact materialize_exact_spec c B (encode (alphabet, rows)) "P"
    (compileTable alphabet rows) (typed_code_on_value hc (alphabet, rows)) hB

end Lax53Proofs.IntrinsicCompilerMaterialize
