import Lax53Proofs.IntrinsicCompilerParameters
import Lax53Proofs.IntrinsicCompiledTableBounds
import Lax53Proofs.IntrinsicInputBounds
import Lax13Proofs.Compile

/-! One public word coefficient covers compiler values, tree workspaces, and layout addresses. -/

namespace Lax53Proofs.IntrinsicWordBounds

open Lax13Proofs.Compile
open Lax52.MSOSyntax Lax53.RankedTree Lax53.TreeStructure Lax53.ValueTranslations
open Lax53.MSOLinearTime Lax53.TreeModelCheckingEncoding Lax58.WordArena
open Lax53Proofs.IntrinsicParameterEncoding Lax53Proofs.IntrinsicCompilerParameters
open Lax53Proofs.IntrinsicCompiledTableBounds Lax53Proofs.IntrinsicInputBounds
open Lax53Proofs.PrimitiveRecursiveCode Lax53Proofs.IntrinsicModelChecking
open Lax53Proofs.ArenaSemantics

def wordCore (c d : Code) (p : Nat) : Nat :=
  compilerAllowance c p + 2 * p + 3 * tableAllowance d p +
    tableAllowance d p * (p + 3) + 50

theorem wordCore_prim (c d : Code) : Primrec (wordCore c d) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp (compilerAllowance_prim c)
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    (Primrec.nat_mul.comp (Primrec.const 3) (tableAllowance_prim d)))
    (Primrec.nat_mul.comp (tableAllowance_prim d)
      (Primrec.nat_add.comp Primrec.id (Primrec.const 3)))) (Primrec.const 50)

def wordCoefficient (L : Layout) (c d : Code) (p : Nat) : Nat :=
  (L.temps + 2 + L.scalars.length + L.arrays.length + 1) * wordCore c d p

theorem wordCoefficient_prim (L : Layout) (c d : Code) : Primrec (wordCoefficient L c d) :=
  Primrec.nat_mul.comp (Primrec.const _) (wordCore_prim c d)

def valueBound (c d : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  wordCore c d (parameterSize alphabet φ) *
    (Lax53.MSOLinearTime.inputStructuralSize alphabet φ t +
      Lax53.MSOLinearTime.inputPayloadMax alphabet φ t + 1)

theorem core_le (c d : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    wordCore c d (parameterSize alphabet φ) ≤ valueBound c d alphabet φ t := by
  unfold valueBound
  exact Nat.le_mul_of_pos_right _ (by omega)

theorem fifty_le_core (c d : Code) (p : Nat) : 50 ≤ wordCore c d p := by
  unfold wordCore
  omega

theorem fits_words (L : Layout) (c d : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) (w : Nat)
    (hw : uniformWordBound (wordCoefficient L c d) alphabet φ t ≤ 2 ^ w) :
    L.FitsWords (valueBound c d alphabet φ t) w := by
  have hcore := core_le c d alphabet φ t
  have h50 := fifty_le_core c d (parameterSize alphabet φ)
  have hB : 1 < valueBound c d alphabet φ t := by omega
  have heq : uniformWordBound (wordCoefficient L c d) alphabet φ t =
      (L.temps + 2 + L.scalars.length + L.arrays.length + 1) *
        valueBound c d alphabet φ t := by
    unfold uniformWordBound wordCoefficient valueBound
    exact Nat.mul_assoc _ _ _
  rw [heq] at hw
  refine ⟨hB, ?_, ?_⟩
  · nlinarith
  · unfold Layout.span
    nlinarith [Nat.mul_le_mul_left (L.temps + 2 + L.scalars.length) (Nat.le_of_lt hB)]

structure Resources (c : Code) (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Prop where
  compiler : IntrinsicPublicCompiler.Fits c B alphabet φ
  memory : (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords < B
  arena : ∀ v ∈ arenaWords (encodeRaw (msoTreeRaw alphabet φ t)), v < B
  table : ∀ v ∈ encodeAutomaton (compiled alphabet φ), v < B
  tableLength : (encodeAutomaton (compiled alphabet φ)).length < B
  stateSpace : treeSize t * (compiled alphabet φ).2.2.1.length < B
  work : alphabet.length + (compiled alphabet φ).2.1 + (compiled alphabet φ).2.2.1.length +
    maximumRank alphabet + (compiled alphabet φ).2.2.1.length * (maximumRank alphabet + 3) +
    (compiled alphabet φ).2.2.2.length + treeSize t + 20 < B

theorem resources (c d : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet)
    (h : TableBounds (compiled alphabet φ) (tableAllowance d (parameterSize alphabet φ))) :
    Resources c (valueBound c d alphabet φ t) alphabet φ t := by
  let p := parameterSize alphabet φ
  let H := tableAllowance d p
  let k := wordCore c d p
  let S := Lax53.MSOLinearTime.inputStructuralSize alphabet φ t
  let N := S + Lax53.MSOLinearTime.inputPayloadMax alphabet φ t + 1
  have hk : 50 ≤ k := fifty_le_core c d p
  have hC : compilerAllowance c p < k := by dsimp [k, wordCore]; omega
  have hH : H < k := by dsimp [H, k, wordCore]; omega
  have hcore : k ≤ valueBound c d alphabet φ t := core_le c d alphabet φ t
  have hn : treeSize t ≤ S := tree_size_le_input alphabet φ t
  have hSN : S < N := by dsimp [N]; omega
  have hprod : k * S < valueBound c d alphabet φ t := by
    exact Nat.mul_lt_mul_of_pos_left hSN (by omega)
  have hmem : 3 * S < valueBound c d alphabet φ t :=
    (Nat.mul_le_mul_right S (by omega : 3 ≤ k)).trans_lt hprod
  have hpayload : Lax53.MSOLinearTime.inputPayloadMax alphabet φ t <
      valueBound c d alphabet φ t := by
    have hN : N ≤ k * N := Nat.le_mul_of_pos_left _ (by omega)
    exact (show Lax53.MSOLinearTime.inputPayloadMax alphabet φ t < N by
      dsimp [N]; omega).trans_le hN
  have hplus : k + treeSize t ≤ valueBound c d alphabet φ t := by
    have hmul := Nat.mul_le_mul_left k (by omega : treeSize t + 1 ≤ N)
    have hnn : treeSize t ≤ k * treeSize t := Nat.le_mul_of_pos_left _ (by omega)
    change k + treeSize t ≤ k * N
    nlinarith
  refine ⟨fits_of_allowance c _ alphabet φ (hC.trans_le hcore), ?_,
    arena_values_lt _ alphabet φ t hpayload (Nat.le_of_lt hmem),
    (fun v hv => (h.values v hv).trans_lt (hH.trans_le hcore)),
    h.length.trans_lt (hH.trans_le hcore), ?_, ?_⟩
  · rw [arena_memory]
    exact hmem
  · have hmul := Nat.mul_le_mul hn (h.transitions.trans (Nat.le_of_lt hH))
    exact (hmul.trans_eq (Nat.mul_comm S k)).trans_lt hprod
  · have ha := (parameter_components alphabet φ).1
    have hr := (parameter_components alphabet φ).2.2
    have hT := h.transitions
    have hQ := h.states
    have hF := h.accepting
    have hmul := Nat.mul_le_mul hT (Nat.add_le_add_right hr 3)
    have hwork : alphabet.length + (compiled alphabet φ).2.1 +
        (compiled alphabet φ).2.2.1.length + maximumRank alphabet +
        (compiled alphabet φ).2.2.1.length * (maximumRank alphabet + 3) +
        (compiled alphabet φ).2.2.2.length + treeSize t + 20 < k + treeSize t := by
      dsimp [k, wordCore, p, H] at *
      omega
    exact hwork.trans_le hplus

end Lax53Proofs.IntrinsicWordBounds
