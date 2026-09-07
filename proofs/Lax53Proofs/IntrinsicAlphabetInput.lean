import Lax53Proofs.CompilerArrayPacking
import Lax53Proofs.AutomatonRamArenaReadAlphabet

/-!
Pack the already decoded alphabet using the existing array-prefix routine.
The table's length header is included in the scan and removed by charged
unpairing. This reuses the verified reader and packer without copying ranks
or introducing a second alphabet array.
-/

namespace Lax53Proofs.IntrinsicAlphabetInput

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax53.ValueTranslations Lax58.WordArena
open Lax53Proofs.CompilerArrayPacking Lax53Proofs.PrimitiveRecursivePairing
open Lax53Proofs.AutomatonRamArenaCorrectness Lax53Proofs.AutomatonRamCorrectness
open Encodable

def program : Com :=
  .seq (.assign "packLength" (.add (.var "A") (.lit 1)))
    (.seq (CompilerArrayPacking.program "P" "packLength")
      (.seq (.assign "packCode" (.sub (.var "packCode") (.lit 1)))
        (unpairRightProgram "packCode" "alphaSqrt" "alphaRem")))

def timeBound (alphabet : RankedAlphabetCode) : Nat :=
  150 * (encode (alphabet.length :: alphabet) + alphabet.length + 2)

theorem program_spec (B : Nat) (alphabet : RankedAlphabetCode)
    (hB : (2 * encode (alphabet.length :: alphabet) + 3) ^ 2 < B) :
    Spec B (fun σ => Prefix "P" (alphabet.length :: alphabet) σ ∧
      σ.vars "A" = alphabet.length) program
      (fun _ σ => σ.vars "packCode" = encode alphabet) (timeBound alphabet) := by
  have he : encode (alphabet.length :: alphabet) = Nat.pair alphabet.length (encode alphabet) + 1 := rfl
  have hl := length_le_encode (alphabet.length :: alphabet)
  simp only [List.length_cons] at hl
  have huB : 2 * Nat.pair alphabet.length (encode alphabet) + 3 < B := by nlinarith
  have hpack := CompilerArrayPacking.program_spec B "P" "packLength"
    (alphabet.length :: alphabet) hB
  simp only [List.length_cons] at hpack
  have hu := unpairRight_spec B (Nat.pair alphabet.length (encode alphabet))
    "packCode" "alphaSqrt" "alphaRem" (by decide) huB
  unfold program timeBound
  run_vcg [hpack, hu]
  all_goals simp_all [Nat.unpair_pair, Prefix]
  all_goals nlinarith

theorem prefix_of_alphabetRead (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (σ : Env) (h : AlphabetRead B I alphabet σ) :
    Prefix "P" (alphabet.length :: alphabet) σ := by
  obtain ⟨_, hspace, _, _, _, _, hp, hzero, _, _⟩ := h
  intro i hi
  have hiP : i < (σ.arrs "P").length := by simp only [List.length_cons] at hi; omega
  rw [List.getElem?_eq_getElem hiP, ← Lax53Proofs.ArrayInput.getD_eq_getElem hiP]
  cases i with
  | zero => simpa using congrArg some hzero
  | succ i =>
      have hi' : i < alphabet.length := by simpa using hi
      have hp' := hp i hi'
      rw [List.getD_eq_getElem alphabet 0 hi'] at hp'
      simpa using congrArg some hp'

theorem from_alphabetRead (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (hB : (2 * encode (alphabet.length :: alphabet) + 3) ^ 2 < B) :
    Spec B (AlphabetRead B I alphabet) program
      (fun _ σ => σ.vars "packCode" = encode alphabet) (timeBound alphabet) := by
  intro σ hσ
  exact program_spec B alphabet hB σ ⟨prefix_of_alphabetRead B I alphabet σ hσ, hσ.2.2.2.1⟩

@[simp] theorem program_warrs : program.warrs = [] := by
  simp [program, unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep, Com.warrs]

theorem program_noRead : ¬ program.reads := by
  simp [program, CompilerArrayPacking.program_noRead, unpairRightProgram,
    sqrtProgram, sqrtLoop, sqrtStep, Com.reads]

theorem program_noWrite : program.NoWrite := by
  simp [program, CompilerArrayPacking.program_noWrite, unpairRightProgram,
    sqrtProgram, sqrtLoop, sqrtStep, Com.NoWrite]

theorem preserves_rowsCode : "rowsCode" ∉ program.wvars := by
  simp [program, CompilerArrayPacking.program, CompilerArrayPacking.loop,
    CompilerArrayPacking.step, unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep,
    pairProgram, Com.wvars]

def scalars : List String :=
  ["A", "packLength", "packIndex", "packValue", "packCode", "alphaSqrt", "alphaRem"]

theorem program_ok (L : Layout) (ht : 5 ≤ L.temps) (hp : "P" ∈ L.arrays)
    (hs : ∀ s ∈ scalars, s ∈ L.scalars) : Com.Ok L program := by
  simp only [scalars, List.forall_mem_cons] at hs
  rcases hs with ⟨hA, hL, hI, hV, hC, hS, hR⟩
  simp [program, CompilerArrayPacking.program, CompilerArrayPacking.loop,
    CompilerArrayPacking.step, CompilerArrayPacking.condition, unpairRightProgram,
    sqrtProgram, sqrtLoop, sqrtStep, sqrtCond, oddExpr, pairProgram,
    Com.Ok, Cond.Ok, Expr.Ok, condExpr, hp, hA, hL, hI, hV, hC, hS, hR]
  omega

end Lax53Proofs.IntrinsicAlphabetInput
