import Lax53Proofs.EncodedAtomicAutomata
import Lax53Proofs.EncodedComputableDeterminization
import Lax53Proofs.EncodedPrimitiveAtomicAutomata
import Lax53Proofs.EncodedPrimitiveProjection
import Lax53Proofs.QuantifierProjectionSemantics
import Lax53Proofs.EmptyMarkers
import Lax53Proofs.MSOFormulaToTreeAutomata

namespace Lax53Proofs.EncodedFormulaCompiler

open FirstOrder
open FirstOrder.Language
open Lax52.MSOSyntax
open Lax53.EffectiveTranslations
open Lax53.RankedTree
open Lax53.TreeAutomaton
open Lax53.TreeStructure
open Lax53Proofs.MarkedTrees
open Lax53Proofs.AtomicMarkedTrees
open Lax53Proofs.QuantifierProjectionSemantics
open Lax53Proofs.EncodedAutomataOperations
open Lax53Proofs.EncodedProjection
open Lax53Proofs.MarkedAlphabetEncoding
open Lax53Proofs.EncodedAtomicAutomata
open Lax53Proofs.EncodedPrimitiveAtomicAutomata
open Lax53Proofs.EncodedPrimitiveProjection
open Lax53Proofs.EmptyMarkers
open Lax53Proofs.MSOFormulaToTreeAutomata

def emptyCode (alphabet : RankedAlphabetCode) : AutomatonCode :=
  FiniteAutomatonEncoding.encode alphabet 1 (fun _ _ _ => false) (fun _ => false)

theorem emptyCode_not_accepts (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) :
    ¬((emptyCode alphabet).toAutomaton alphabet).Accepts t := by
  rintro ⟨q, hq, -⟩
  unfold emptyCode at hq
  rw [FiniteAutomatonEncoding.accept_encode] at hq
  contradiction

def compileMarked (alphabet : RankedAlphabetCode) :
    (n m : Nat) → RawFormula → AutomatonCode
  | n, m, .falsum => emptyCode (code alphabet n m)
  | n, m, .equal x y =>
      if hx : x < n then if hy : y < n then
        inter (code alphabet n m) (validCodeP alphabet n m)
          (somewhereCodeP alphabet n m
            (fun a => foMarked n m a x && foMarked n m a y))
      else emptyCode (code alphabet n m)
      else emptyCode (code alphabet n m)
  | n, m, .label a x =>
      if ha : a < alphabet.length then if hx : x < n then
        inter (code alphabet n m) (validCodeP alphabet n m)
          (somewhereCodeP alphabet n m
            (fun s => decide (baseSymbol n m s = a) && foMarked n m s x))
      else emptyCode (code alphabet n m)
      else emptyCode (code alphabet n m)
  | n, m, .child slot x y =>
      if hs : ∃ a : alphabet.toRankedAlphabet.Symbol,
          slot < alphabet.toRankedAlphabet.rank a then
        if hx : x < n then if hy : y < n then
          inter (code alphabet n m) (validCodeP alphabet n m)
            (edgeCodeP alphabet n m slot x y)
        else emptyCode (code alphabet n m)
        else emptyCode (code alphabet n m)
      else emptyCode (code alphabet n m)
  | n, m, .mem x X =>
      if hx : x < n then if hX : X < m then
        inter (code alphabet n m) (validCodeP alphabet n m)
          (somewhereCodeP alphabet n m
            (fun a => foMarked n m a x && soMarked m a X))
      else emptyCode (code alphabet n m)
      else emptyCode (code alphabet n m)
  | n, m, .or phi psi =>
      match RawFormula.elaborate alphabet n m phi,
          RawFormula.elaborate alphabet n m psi with
      | some _, some _ =>
          EncodedComputableDeterminization.union (code alphabet n m)
            (compileMarked alphabet n m phi)
            (compileMarked alphabet n m psi)
      | _, _ => emptyCode (code alphabet n m)
  | n, m, .neg phi =>
      match RawFormula.elaborate alphabet n m phi with
      | some _ =>
          inter (code alphabet n m) (validCodeP alphabet n m)
            (EncodedComputableDeterminization.compl (code alphabet n m)
              (compileMarked alphabet n m phi))
      | none => emptyCode (code alphabet n m)
  | n, m, .exFO phi =>
      project (code alphabet n m) (dropFOOfP alphabet n m)
        (compileMarked alphabet (n + 1) m phi)
  | n, m, .exSO phi =>
      project (code alphabet n m) (dropSOOfP alphabet n m)
        (compileMarked alphabet n (m + 1) phi)

def denotation (alphabet : RankedAlphabetCode) (n m : Nat)
    (raw : RawFormula) (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)) : Prop :=
  match RawFormula.elaborate alphabet n m raw with
  | some phi => t ∈ formulaLanguage phi
  | none => False

theorem elaborate_falsum (alphabet : RankedAlphabetCode) (n m : Nat) :
    RawFormula.elaborate alphabet n m .falsum = some .falsum := rfl

theorem not_mem_formulaLanguage_falsum {A : RankedAlphabet} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) :
    t ∉ formulaLanguage (Formula.falsum : Formula (treeSignature A) n m) := by
  rintro ⟨_, _, _, hfalse⟩
  exact hfalse

theorem denotation_some (alphabet : RankedAlphabetCode) (n m : Nat)
    (raw : RawFormula) (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m))
    (phi : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (h : RawFormula.elaborate alphabet n m raw = some phi) :
    denotation alphabet n m raw t ↔ t ∈ formulaLanguage phi := by
  unfold denotation
  rw [h]

theorem denotation_none (alphabet : RankedAlphabetCode) (n m : Nat)
    (raw : RawFormula) (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m))
    (h : RawFormula.elaborate alphabet n m raw = none) :
    denotation alphabet n m raw t ↔ False := by
  unfold denotation
  rw [h]

theorem compileMarked_correct (alphabet : RankedAlphabetCode) :
    ∀ (n m : Nat) (raw : RawFormula)
      (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)),
      ((compileMarked alphabet n m raw).toAutomaton (code alphabet n m)).Accepts
          (codeTree alphabet n m t) ↔ denotation alphabet n m raw t := by
  intro n m raw
  induction raw generalizing n m with
  | falsum =>
      intro t
      rw [compileMarked]
      change _ ↔ t ∈ formulaLanguage Formula.falsum
      exact iff_false_intro (emptyCode_not_accepts _ _) |>.trans
        (iff_false_intro (not_mem_formulaLanguage_falsum t)).symm
  | equal x y =>
      intro t
      by_cases hx : x < n <;> by_cases hy : y < n
      · rw [compileMarked, dif_pos hx, dif_pos hy]
        have helab : RawFormula.elaborate alphabet n m (.equal x y) =
            some (.equal (.var ⟨x, hx⟩) (.var ⟨y, hy⟩)) := by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_pos hx, dif_pos hy]
          rfl
        rw [denotation_some alphabet n m _ t _ helab]
        rw [inter_accepts_iff, validCodeP_accepts_iff,
          somewhereCodeP_accepts_iff alphabet n m
            (fun a => foMarked n m a x && foMarked n m a y)
            (fun s => s.2.1 ⟨x, hx⟩ && s.2.1 ⟨y, hy⟩) (by
              intro a
              simp [fromCode_fo])]
        rw [formulaLanguage_equal_eq]
        rfl
      · rw [compileMarked, dif_pos hx, dif_neg hy]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_pos hx, dif_neg hy]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
      · rw [compileMarked, dif_neg hx]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_neg hx]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
      · rw [compileMarked, dif_neg hx]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_neg hx]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
  | label symbol x =>
      intro t
      by_cases ha : symbol < alphabet.length <;> by_cases hx : x < n
      · rw [compileMarked, dif_pos ha, dif_pos hx]
        have helab : RawFormula.elaborate alphabet n m (.label symbol x) =
            some (.rel (.label ⟨symbol, ha⟩) (fun _ => .var ⟨x, hx⟩)) := by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_pos ha, dif_pos hx]
          rfl
        rw [denotation_some alphabet n m _ t _ helab]
        rw [inter_accepts_iff, validCodeP_accepts_iff,
          somewhereCodeP_accepts_iff alphabet n m
            (fun s => decide (baseSymbol n m s = symbol) && foMarked n m s x)
            (fun s => decide
              (s.1 = (⟨symbol, ha⟩ : alphabet.toRankedAlphabet.Symbol)) &&
                s.2.1 ⟨x, hx⟩) (by
              intro a
              change (decide (baseSymbol n m a.val = symbol) &&
                  foMarked n m a.val x) =
                (decide ((fromCodeSymbol alphabet n m a).1 = ⟨symbol, ha⟩) &&
                  (fromCodeSymbol alphabet n m a).2.1 ⟨x, hx⟩)
              rw [fromCode_fo]
              congr 1
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq]
              constructor
              · intro h
                apply Fin.ext
                exact (fromCode_base alphabet n m a).trans h
              · intro h
                exact (fromCode_base alphabet n m a).symm.trans
                  (congrArg Fin.val h))]
        rw [formulaLanguage_label_eq]
        rfl
      · rw [compileMarked, dif_pos ha, dif_neg hx]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_pos ha, dif_neg hx]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
      · rw [compileMarked, dif_neg ha]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_neg ha]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
      · rw [compileMarked, dif_neg ha]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_neg ha]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
  | child slot x y =>
      intro t
      by_cases hs : ∃ a : alphabet.toRankedAlphabet.Symbol,
          slot < alphabet.toRankedAlphabet.rank a
      · by_cases hx : x < n <;> by_cases hy : y < n
        · rw [compileMarked, dif_pos hs, dif_pos hx, dif_pos hy]
          have helab : RawFormula.elaborate alphabet n m (.child slot x y) =
              some (.rel (.child ⟨slot, hs⟩)
                (fun i => Fin.cases (.var ⟨x, hx⟩) (fun _ => .var ⟨y, hy⟩) i)) := by
            unfold RawFormula.elaborate RawFormula.childIndex? RawFormula.fin?
            rw [dif_pos hs, dif_pos hx, dif_pos hy]
            rfl
          rw [denotation_some alphabet n m _ t _ helab]
          rw [inter_accepts_iff, validCodeP_accepts_iff]
          have hedge := edgeCodeP_accepts_iff alphabet n m
            (⟨slot, hs⟩ : ChildIndex alphabet.toRankedAlphabet) ⟨x, hx⟩ ⟨y, hy⟩ t
          rw [hedge]
          rw [formulaLanguage_child_eq]
          rfl
        · rw [compileMarked, dif_pos hs, dif_pos hx, dif_neg hy]
          rw [denotation_none alphabet n m _ t (by
            unfold RawFormula.elaborate RawFormula.childIndex? RawFormula.fin?
            rw [dif_pos hs, dif_pos hx, dif_neg hy]
            rfl)]
          exact iff_false_intro (emptyCode_not_accepts _ _)
        · rw [compileMarked, dif_pos hs, dif_neg hx]
          rw [denotation_none alphabet n m _ t (by
            unfold RawFormula.elaborate RawFormula.childIndex? RawFormula.fin?
            rw [dif_pos hs, dif_neg hx]
            rfl)]
          exact iff_false_intro (emptyCode_not_accepts _ _)
        · rw [compileMarked, dif_pos hs, dif_neg hx]
          rw [denotation_none alphabet n m _ t (by
            unfold RawFormula.elaborate RawFormula.childIndex? RawFormula.fin?
            rw [dif_pos hs, dif_neg hx]
            rfl)]
          exact iff_false_intro (emptyCode_not_accepts _ _)
      · rw [compileMarked, dif_neg hs]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.childIndex?
          rw [dif_neg hs]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
  | mem x X =>
      intro t
      by_cases hx : x < n <;> by_cases hX : X < m
      · rw [compileMarked, dif_pos hx, dif_pos hX]
        have helab : RawFormula.elaborate alphabet n m (.mem x X) =
            some (.mem (.var ⟨x, hx⟩) ⟨X, hX⟩) := by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_pos hx, dif_pos hX]
          rfl
        rw [denotation_some alphabet n m _ t _ helab]
        rw [inter_accepts_iff, validCodeP_accepts_iff,
          somewhereCodeP_accepts_iff alphabet n m
            (fun a => foMarked n m a x && soMarked m a X)
            (fun s => s.2.1 ⟨x, hx⟩ && s.2.2 ⟨X, hX⟩) (by
              intro a
              simp [fromCode_fo, fromCode_so])]
        rw [formulaLanguage_mem_eq]
        rfl
      · rw [compileMarked, dif_pos hx, dif_neg hX]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_pos hx, dif_neg hX]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
      · rw [compileMarked, dif_neg hx]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_neg hx]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
      · rw [compileMarked, dif_neg hx]
        rw [denotation_none alphabet n m _ t (by
          unfold RawFormula.elaborate RawFormula.fin?
          rw [dif_neg hx]
          rfl)]
        exact iff_false_intro (emptyCode_not_accepts _ _)
  | or phi psi ihPhi ihPsi =>
      intro t
      cases hphi : RawFormula.elaborate alphabet n m phi with
      | none =>
          rw [compileMarked, hphi]
          rw [denotation_none alphabet n m _ t (by
            unfold RawFormula.elaborate
            rw [hphi]
            rfl)]
          exact iff_false_intro (emptyCode_not_accepts _ _)
      | some elaboratedPhi =>
          cases hpsi : RawFormula.elaborate alphabet n m psi with
          | none =>
              rw [compileMarked, hphi, hpsi]
              rw [denotation_none alphabet n m _ t (by
                unfold RawFormula.elaborate
                rw [hphi, hpsi]
                rfl)]
              exact iff_false_intro (emptyCode_not_accepts _ _)
          | some elaboratedPsi =>
              rw [compileMarked, hphi, hpsi]
              rw [denotation_some alphabet n m _ t
                (.or elaboratedPhi elaboratedPsi) (by
                  unfold RawFormula.elaborate
                  rw [hphi, hpsi]
                  rfl)]
              rw [EncodedComputableDeterminization.union_accepts_iff,
                ihPhi n m t, ihPsi n m t]
              rw [denotation_some alphabet n m phi t elaboratedPhi hphi]
              rw [denotation_some alphabet n m psi t elaboratedPsi hpsi]
              rw [formulaLanguage_or]
              rfl
  | neg phi ih =>
      intro t
      cases hphi : RawFormula.elaborate alphabet n m phi with
      | none =>
          rw [compileMarked, hphi]
          rw [denotation_none alphabet n m _ t (by
            unfold RawFormula.elaborate
            rw [hphi]
            rfl)]
          exact iff_false_intro (emptyCode_not_accepts _ _)
      | some elaborated =>
          rw [compileMarked, hphi]
          rw [denotation_some alphabet n m _ t (.neg elaborated) (by
            unfold RawFormula.elaborate
            rw [hphi]
            rfl)]
          rw [inter_accepts_iff, validCodeP_accepts_iff,
            EncodedComputableDeterminization.compl_accepts_iff,
            ih n m t, denotation_some alphabet n m phi t elaborated hphi]
          rw [formulaLanguage_neg]
          rfl
  | exFO phi ih =>
      intro t
      rw [compileMarked]
      rw [project_accepts_iff (code alphabet (n + 1) m) (code alphabet n m)
        (dropFOMap alphabet n m) (rank_dropFOMap alphabet n m)
        (dropFOOfP alphabet n m) (mem_dropFOOfP alphabet n m)
        (complete_dropFOOfP alphabet n m)]
      cases hphi : RawFormula.elaborate alphabet (n + 1) m phi with
      | none =>
          rw [denotation_none alphabet n m _ t (by
            unfold RawFormula.elaborate
            rw [hphi]
            rfl)]
          constructor
          · rintro ⟨source, -, hsource⟩
            have hcode : codeTree alphabet (n + 1) m
                (decodeTree alphabet (n + 1) m source) = source := by
              exact code_decodeTree alphabet (n + 1) m source
            have hs := (ih (n + 1) m
              (decodeTree alphabet (n + 1) m source)).mp (by
                rw [hcode]
                exact hsource)
            simp [denotation, hphi] at hs
          · intro hfalse
            exact False.elim hfalse
      | some elaborated =>
          rw [denotation_some alphabet n m _ t (.exFO elaborated) (by
            unfold RawFormula.elaborate
            rw [hphi]
            rfl)]
          rw [formulaLanguage_exFO]
          constructor
          · rintro ⟨source, hmap, hsource⟩
            let decoded := decodeTree alphabet (n + 1) m source
            refine ⟨decoded, ?_, ?_⟩
            · have := congrArg (decodeTree alphabet n m) hmap
              simpa only [decoded, codeTree, decodeTree_dropFO,
                decode_codeTree] using this
            · apply (denotation_some alphabet (n + 1) m phi decoded
                elaborated hphi).mp
              apply (ih (n + 1) m decoded).mp
              have hcode : codeTree alphabet (n + 1) m decoded = source := by
                exact code_decodeTree alphabet (n + 1) m source
              rw [hcode]
              exact hsource
          · rintro ⟨source, rfl, hsource⟩
            refine ⟨codeTree alphabet (n + 1) m source, ?_, ?_⟩
            · apply Function.LeftInverse.injective
                (fun coded => code_decodeTree alphabet n m coded)
              simp only [codeTree, decodeTree_dropFO, decode_codeTree]
            · apply (ih (n + 1) m source).mpr
              exact (denotation_some alphabet (n + 1) m phi source
                elaborated hphi).mpr hsource
  | exSO phi ih =>
      intro t
      rw [compileMarked]
      rw [project_accepts_iff (code alphabet n (m + 1)) (code alphabet n m)
        (dropSOMap alphabet n m) (rank_dropSOMap alphabet n m)
        (dropSOOfP alphabet n m) (mem_dropSOOfP alphabet n m)
        (complete_dropSOOfP alphabet n m)]
      cases hphi : RawFormula.elaborate alphabet n (m + 1) phi with
      | none =>
          rw [denotation_none alphabet n m _ t (by
            unfold RawFormula.elaborate
            rw [hphi]
            rfl)]
          constructor
          · rintro ⟨source, -, hsource⟩
            have hcode : codeTree alphabet n (m + 1)
                (decodeTree alphabet n (m + 1) source) = source := by
              exact code_decodeTree alphabet n (m + 1) source
            have hs := (ih n (m + 1)
              (decodeTree alphabet n (m + 1) source)).mp (by
                rw [hcode]
                exact hsource)
            simp [denotation, hphi] at hs
          · intro hfalse
            exact False.elim hfalse
      | some elaborated =>
          rw [denotation_some alphabet n m _ t (.exSO elaborated) (by
            unfold RawFormula.elaborate
            rw [hphi]
            rfl)]
          rw [formulaLanguage_exSO]
          constructor
          · rintro ⟨source, hmap, hsource⟩
            let decoded := decodeTree alphabet n (m + 1) source
            refine ⟨decoded, ?_, ?_⟩
            · have := congrArg (decodeTree alphabet n m) hmap
              simpa only [decoded, codeTree, decodeTree_dropSO,
                decode_codeTree] using this
            · apply (denotation_some alphabet n (m + 1) phi decoded
                elaborated hphi).mp
              apply (ih n (m + 1) decoded).mp
              have hcode : codeTree alphabet n (m + 1) decoded = source := by
                exact code_decodeTree alphabet n (m + 1) source
              rw [hcode]
              exact hsource
          · rintro ⟨source, rfl, hsource⟩
            refine ⟨codeTree alphabet n (m + 1) source, ?_, ?_⟩
            · apply Function.LeftInverse.injective
                (fun coded => code_decodeTree alphabet n m coded)
              simp only [codeTree, decodeTree_dropSO, decode_codeTree]
            · apply (ih n (m + 1) source).mpr
              exact (denotation_some alphabet n (m + 1) phi source
                elaborated hphi).mpr hsource

def zeroSymbolMap (alphabet : RankedAlphabetCode) :
    alphabet.toRankedAlphabet.Symbol →
      (code alphabet 0 0).toRankedAlphabet.Symbol :=
  fun a => toCodeSymbol alphabet 0 0
    (a, fun i => Fin.elim0 i, fun i => Fin.elim0 i)

theorem rank_zeroSymbolMap (alphabet : RankedAlphabetCode)
    (a : alphabet.toRankedAlphabet.Symbol) :
    (code alphabet 0 0).toRankedAlphabet.rank (zeroSymbolMap alphabet a) =
      alphabet.toRankedAlphabet.rank a := by
  unfold zeroSymbolMap
  rw [rank_toCodeSymbol]
  rfl

theorem mapTree_zero_eq (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) :
    mapTree alphabet (code alphabet 0 0) (zeroSymbolMap alphabet)
      (rank_zeroSymbolMap alphabet) t = codeTree alphabet 0 0 (emptyMark t) := by
  induction t with
  | node a children ih =>
      simp only [mapTree, codeTree, relabelTree, emptyMark, zeroSymbolMap,
        Tree.node.injEq, true_and]
      apply heq_of_eq
      funext i
      simpa using ih (Fin.cast (rank_zeroSymbolMap alphabet a) i)

def compileSentenceBody (alphabet : RankedAlphabetCode)
    (raw : FormulaCode) : AutomatonCode :=
  pullback alphabet
    (fun a => if h : a < alphabet.length then
      (zeroSymbolMap alphabet ⟨a, h⟩).val else 0)
    (compileMarked alphabet 0 0 raw)

def compileSentence (input : EncodedSentence) : EncodedAutomaton :=
  (input.1, compileSentenceBody input.1 input.2)

theorem compileSentence_alphabet (input : EncodedSentence) :
    (compileSentence input).1 = input.1 := rfl

theorem compileSentence_language (input : EncodedSentence) :
    AutomatonCode.language input.1 (compileSentence input).2 =
      FormulaCode.language input.1 input.2 := by
  ext t
  simp only [compileSentence, AutomatonCode.language]
  unfold compileSentenceBody FormulaCode.language
  change ((pullback input.1
      (fun a => if h : a < input.1.length then
        (zeroSymbolMap input.1 ⟨a, h⟩).val else 0)
      (compileMarked input.1 0 0 input.2)).toAutomaton input.1).Accepts t ↔ _
  rw [pullback_accepts_iff input.1 (code input.1 0 0)
    (zeroSymbolMap input.1) (rank_zeroSymbolMap input.1)]
  rw [mapTree_zero_eq]
  rw [compileMarked_correct]
  unfold denotation
  cases helab : RawFormula.elaborate input.1 0 0 input.2 with
  | none => rfl
  | some phi => exact emptyMark_mem_formulaLanguage_iff t phi

end Lax53Proofs.EncodedFormulaCompiler
