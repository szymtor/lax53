import Lax842588Proofs.IntrinsicParameterEncoding
import Lax842588Proofs.IntrinsicPublicCompiler

/-! Computable parameter-only envelopes discharge every compiler-specific word premise. -/

namespace Lax842588Proofs.IntrinsicCompilerParameters

open Encodable Lax146103.MSOSyntax Lax842588.ValueTranslations Lax842588.TreeStructure
open Lax842588.MSOLinearTime Lax842588.TreeModelCheckingEncoding Lax560851.StructuralCombinators
open Lax842588Proofs.IntrinsicParameterEncoding Lax842588Proofs.CompilerNumericBounds
open Lax842588Proofs.PrimitiveRecursiveBounds Lax842588Proofs.PrimitiveRecursiveCode
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.IntrinsicCompilerFields

def compilerBudget (c : Code) (p : Nat) : Nat := prefixMax (budget c) (inputCodeBound p)
def scopePower (p : Nat) : Nat := 2 ^ fieldBound p
def symbolBound (p : Nat) : Nat := fieldBound p * scopePower p * scopePower p
def rowsPackBound (p : Nat) : Nat := (2 * rowsCodeBound p + 3) ^ 2
def headerPackBound (p : Nat) : Nat := (2 * headerCodeBound p + 3) ^ 2
def materializeWords (c : Code) (p : Nat) : Nat := 3 * compilerBudget c p + 10
def materializeTime (c : Code) (p : Nat) : Nat := 300 * (compilerBudget c p + 1) ^ 2

def tagCeiling : Nat :=
  (IntrinsicFieldExtraction.names.map Raw.constructorNameCode).foldl max 0

def compilerAllowance (c : Code) (p : Nat) : Nat :=
  fieldBound p + scopePower p + symbolBound p + rowsPackBound p + headerPackBound p +
    inputCodeBound p + materializeWords c p + tagCeiling + 20

theorem compilerBudget_prim (c : Code) : Primrec (compilerBudget c) :=
  (prefixMax_prim (budget_prim c)).comp inputCodeBound_prim
theorem pow_prim : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow
theorem scopePower_prim : Primrec scopePower :=
  pow_prim.comp (Primrec.const 2) fieldBound_prim
theorem symbolBound_prim : Primrec symbolBound :=
  Primrec.nat_mul.comp (Primrec.nat_mul.comp fieldBound_prim scopePower_prim) scopePower_prim
theorem rowsPackBound_prim : Primrec rowsPackBound :=
  pow_prim.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) rowsCodeBound_prim)
      (Primrec.const 3)) (Primrec.const 2)
theorem headerPackBound_prim : Primrec headerPackBound :=
  pow_prim.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) headerCodeBound_prim)
      (Primrec.const 3)) (Primrec.const 2)
theorem materializeWords_prim (c : Code) : Primrec (materializeWords c) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) (compilerBudget_prim c))
    (Primrec.const 10)
theorem materializeTime_prim (c : Code) : Primrec (materializeTime c) :=
  Primrec.nat_mul.comp (Primrec.const 300)
    (pow_prim.comp (Primrec.nat_add.comp (compilerBudget_prim c) (Primrec.const 1))
      (Primrec.const 2))
theorem compilerAllowance_prim (c : Code) : Primrec (compilerAllowance c) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.nat_add.comp fieldBound_prim scopePower_prim)
          symbolBound_prim) rowsPackBound_prim) headerPackBound_prim)
      inputCodeBound_prim) (materializeWords_prim c)) (Primrec.const tagCeiling)) (Primrec.const 20)

theorem budget_le (c : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    budget c (encode (alphabet, (postorder alphabet φ).map fields)) ≤
      compilerBudget c (parameterSize alphabet φ) :=
  le_prefixMax _ (input_code_le alphabet φ)

theorem materialize_words_le (c : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    IntrinsicCompilerMaterialize.wordBound c (encode (alphabet, (postorder alphabet φ).map fields)) ≤
      materializeWords c (parameterSize alphabet φ) := by
  have := budget_le c alphabet φ
  unfold IntrinsicCompilerMaterialize.wordBound materializeWords
  omega

theorem materialize_time_le (c : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    IntrinsicCompilerMaterialize.timeBound c (encode (alphabet, (postorder alphabet φ).map fields)) ≤
      materializeTime c (parameterSize alphabet φ) := by
  unfold IntrinsicCompilerMaterialize.timeBound materializeTime
  exact Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left (Nat.add_le_add_right (budget_le c alphabet φ) 1) 2)

theorem scope_bounds (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)) (o : Occurrence alphabet)
    (ho : o ∈ postorder alphabet φ) :
    2 ^ o.fo ≤ scopePower (parameterSize alphabet φ) ∧
      2 ^ o.so ≤ scopePower (parameterSize alphabet φ) ∧
      MarkedAlphabetEncoding.symbolCount alphabet o.fo o.so ≤ symbolBound (parameterSize alphabet φ) := by
  have hs := (shape_bounds alphabet φ).scopes o ho
  have hf : 2 ^ o.fo ≤ scopePower (parameterSize alphabet φ) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hm : 2 ^ o.so ≤ scopePower (parameterSize alphabet φ) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨hf, hm, ?_⟩
  unfold MarkedAlphabetEncoding.symbolCount symbolBound
  rw [FiniteAutomatonEncoding.words_length, FiniteAutomatonEncoding.words_length]
  exact Nat.mul_le_mul (Nat.mul_le_mul (shape_bounds alphabet φ).alphabetLength hf) hm

theorem fits_of_allowance (c : Code) (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (hB : compilerAllowance c (parameterSize alphabet φ) < B) :
    IntrinsicPublicCompiler.Fits c B alphabet φ := by
  have hshape := shape_bounds alphabet φ
  have hK : 8 ≤ fieldBound (parameterSize alphabet φ) := by unfold fieldBound; omega
  have hR := (parameter_components alphabet φ).2.2
  have hpK : parameterSize alphabet φ ≤ fieldBound (parameterSize alphabet φ) := by
    unfold fieldBound; omega
  have hα := alphabet_code_le alphabet φ
  have hr := rows_code_le alphabet φ
  have hh := header_code_le alphabet φ
  have hrows : (2 * encode (IntrinsicFormulaInput.rowCodes (postorder alphabet φ)) + 3) ^ 2 ≤
      rowsPackBound (parameterSize alphabet φ) := by
    rw [IntrinsicFormulaInput.encode_rowCodes]
    exact Nat.pow_le_pow_left (by omega) 2
  have hheader : (2 * encode (alphabet.length :: alphabet) + 3) ^ 2 ≤
      headerPackBound (parameterSize alphabet φ) := Nat.pow_le_pow_left (by omega) 2
  have hpair : (encode alphabet + encode ((postorder alphabet φ).map fields) + 1) ^ 2 ≤
      inputCodeBound (parameterSize alphabet φ) := by
    simpa only [Nat.pow_two, pairCap] using pairCap_mono hα hr
  have hw := materialize_words_le c alphabet φ
  unfold compilerAllowance at hB
  refine ⟨by omega, ?_, by have := hshape.alphabetLength; omega, by omega,
    by have := hshape.steps; omega, ?_, ?_, by omega, by omega, by omega, by omega⟩
  · intro name hn
    have ht : Raw.constructorNameCode name ≤ tagCeiling := by
      apply fold_max_mem
      exact List.mem_map.mpr ⟨name, hn, rfl⟩
    omega
  · intro o ho
    have hs := hshape.scopes o ho
    obtain ⟨hf, hm, ha⟩ := scope_bounds alphabet φ o ho
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · intro o ho v hv
    have := hshape.fields o ho v hv
    omega

end Lax842588Proofs.IntrinsicCompilerParameters
