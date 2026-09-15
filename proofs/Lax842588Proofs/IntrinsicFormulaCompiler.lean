import Lax842588Proofs.EncodedAtomicAutomata
import Lax842588Proofs.EncodedComputableDeterminization
import Lax842588Proofs.EncodedPrimitiveAtomicAutomata
import Lax842588Proofs.EncodedPrimitiveProjection
import Lax842588Proofs.QuantifierProjectionSemantics
import Lax842588Proofs.EmptyMarkers
import Lax842588Proofs.MSOFormulaToTreeAutomata

/-!
Direct numeric-automaton compiler for the existing intrinsically scoped
Lax-52 formula syntax. The operational definition below contains no raw
formula copy, scope check, reification, or elaboration pass.

Its correctness proof follows the same intrinsic formula recursion, so no
duplicate formula syntax appears even in the proof interface.
-/

set_option backward.isDefEq.respectTransparency false

namespace Lax842588Proofs.IntrinsicFormulaCompiler

open FirstOrder
open FirstOrder.Language
open Lax146103.MSOSyntax
open Lax842588.ValueTranslations
open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588.TreeStructure
open Lax842588Proofs.MarkedTrees
open Lax842588Proofs.AtomicMarkedTrees
open Lax842588Proofs.MSOFormulaToTreeAutomata
open Lax842588Proofs.QuantifierProjectionSemantics
open Lax842588Proofs.EncodedAutomataOperations
open Lax842588Proofs.EncodedProjection
open Lax842588Proofs.MarkedAlphabetEncoding
open Lax842588Proofs.EncodedAtomicAutomata
open Lax842588Proofs.EncodedPrimitiveAtomicAutomata
open Lax842588Proofs.EncodedPrimitiveProjection
open Lax842588Proofs.EmptyMarkers

/-- Code for an automaton accepting no trees over the supplied alphabet. -/
def emptyCode (alphabet : RankedAlphabetCode) : AutomatonCode :=
  FiniteAutomatonEncoding.encode alphabet 1 (fun _ _ _ => false) (fun _ => false)

@[simp] theorem emptyCode_eq (alphabet : RankedAlphabetCode) :
    emptyCode alphabet = (1, [], []) := by
  simp [emptyCode, FiniteAutomatonEncoding.encode]

theorem emptyCode_not_accepts (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) :
    ¬((emptyCode alphabet).toAutomaton alphabet).Accepts t := by
  rintro ⟨q, hq, -⟩
  unfold emptyCode at hq
  rw [FiniteAutomatonEncoding.accept_encode] at hq
  contradiction

theorem not_mem_formulaLanguage_falsum {A : RankedAlphabet} {n m : Nat}
    (t : Tree (MarkedAlphabet A n m)) :
    t ∉ formulaLanguage (Formula.falsum : Formula (treeSignature A) n m) := by
  rintro ⟨_, _, _, hfalse⟩
  exact hfalse

/-- Compile an intrinsically scoped formula directly by structural recursion.
Every variable, symbol, and child index is already valid by construction, so
there is no syntax-validation or elaboration branch. -/
def compileFormula (alphabet : RankedAlphabetCode) :
    {n m : Nat} →
      Formula (treeSignature alphabet.toRankedAlphabet) n m → AutomatonCode
  | n, m, .falsum => emptyCode (code alphabet n m)
  | n, m, .equal x y =>
      inter (code alphabet n m) (validCodeP alphabet n m)
        (somewhereCodeP alphabet n m
          (fun a => foMarked n m a (treeTermVar x).val &&
            foMarked n m a (treeTermVar y).val))
  | n, m, .rel (.label symbol) terms =>
      inter (code alphabet n m) (validCodeP alphabet n m)
        (somewhereCodeP alphabet n m
          (fun s => decide (baseSymbol n m s = symbol.val) &&
            foMarked n m s (treeTermVar (terms 0)).val))
  | n, m, .rel (.child slot) terms =>
      inter (code alphabet n m) (validCodeP alphabet n m)
        (edgeCodeP alphabet n m slot.val
          (treeTermVar (terms 0)).val
          (treeTermVar (terms 1)).val)
  | n, m, .mem x X =>
      inter (code alphabet n m) (validCodeP alphabet n m)
        (somewhereCodeP alphabet n m
          (fun a => foMarked n m a (treeTermVar x).val &&
            soMarked m a X.val))
  | n, m, .or phi psi =>
      EncodedComputableDeterminization.union (code alphabet n m)
        (compileFormula alphabet phi) (compileFormula alphabet psi)
  | n, m, .neg phi =>
      inter (code alphabet n m) (validCodeP alphabet n m)
        (EncodedComputableDeterminization.compl (code alphabet n m)
          (compileFormula alphabet phi))
  | n, m, .exFO phi =>
      project (code alphabet n m) (dropFOOfP alphabet n m)
        (compileFormula alphabet phi)
  | n, m, .exSO phi =>
      project (code alphabet n m) (dropSOOfP alphabet n m)
        (compileFormula alphabet phi)

/-- The direct intrinsic compiler recognizes exactly the marked trees that
satisfy its input formula. This proof follows the intrinsic formula induction
itself and is independent of the legacy raw-formula correctness theorem. -/
theorem compileFormula_correct (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat}
      (phi : Formula (treeSignature alphabet.toRankedAlphabet) n m)
      (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)),
      ((compileFormula alphabet phi).toAutomaton (code alphabet n m)).Accepts
          (codeTree alphabet n m t) ↔ t ∈ formulaLanguage phi := by
  intro _ _ phi
  induction phi with
  | falsum =>
      intro t
      rw [compileFormula]
      exact iff_false_intro (emptyCode_not_accepts _ _) |>.trans
        (iff_false_intro (not_mem_formulaLanguage_falsum t)).symm
  | equal x y =>
      rename_i _ _ n m
      intro t
      rw [compileFormula, inter_accepts_iff, validCodeP_accepts_iff,
        somewhereCodeP_accepts_iff alphabet n m
          (fun a => foMarked n m a (treeTermVar x).val &&
            foMarked n m a (treeTermVar y).val)
          (fun s => s.2.1 (treeTermVar x) && s.2.1 (treeTermVar y)) (by
            intro a
            change (foMarked n m a.val (treeTermVar x).val &&
                foMarked n m a.val (treeTermVar y).val) =
              ((fromCodeSymbol alphabet n m a).2.1 (treeTermVar x) &&
                (fromCodeSymbol alphabet n m a).2.1 (treeTermVar y))
            rw [fromCode_fo, fromCode_fo])]
      rw [formulaLanguage_equal_eq]
      rfl
  | rel relation terms =>
      rename_i _ _ n m _
      cases relation with
      | label symbol =>
          intro t
          rw [compileFormula, inter_accepts_iff, validCodeP_accepts_iff,
            somewhereCodeP_accepts_iff alphabet n m
              (fun s => decide (baseSymbol n m s = symbol.val) &&
                foMarked n m s (treeTermVar (terms 0)).val)
              (fun s => decide (s.1 = symbol) &&
                s.2.1 (treeTermVar (terms 0))) (by
                intro a
                change (decide (baseSymbol n m a.val = symbol.val) &&
                    foMarked n m a.val (treeTermVar (terms 0)).val) =
                  (decide ((fromCodeSymbol alphabet n m a).1 = symbol) &&
                    (fromCodeSymbol alphabet n m a).2.1
                      (treeTermVar (terms 0)))
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
      | child slot =>
          intro t
          rw [compileFormula, inter_accepts_iff, validCodeP_accepts_iff,
            edgeCodeP_accepts_iff alphabet n m slot
              (treeTermVar (terms 0)) (treeTermVar (terms 1)) t,
            formulaLanguage_child_eq]
          rfl
  | mem x X =>
      rename_i _ _ n m
      intro t
      rw [compileFormula, inter_accepts_iff, validCodeP_accepts_iff,
        somewhereCodeP_accepts_iff alphabet n m
          (fun a => foMarked n m a (treeTermVar x).val && soMarked m a X.val)
          (fun s => s.2.1 (treeTermVar x) && s.2.2 X) (by
            intro a
            change (foMarked n m a.val (treeTermVar x).val &&
                soMarked m a.val X.val) =
              ((fromCodeSymbol alphabet n m a).2.1 (treeTermVar x) &&
                (fromCodeSymbol alphabet n m a).2.2 X)
            rw [fromCode_fo, fromCode_so])]
      rw [formulaLanguage_mem_eq]
      rfl
  | or phi psi ihPhi ihPsi =>
      intro t
      rw [compileFormula, EncodedComputableDeterminization.union_accepts_iff,
        ihPhi t, ihPsi t, formulaLanguage_or]
      rfl
  | neg phi ih =>
      intro t
      rw [compileFormula, inter_accepts_iff, validCodeP_accepts_iff,
        EncodedComputableDeterminization.compl_accepts_iff,
        ih t, formulaLanguage_neg]
      rfl
  | exFO phi ih =>
      rename_i _ _ n m
      intro t
      rw [compileFormula]
      rw [project_accepts_iff (code alphabet (n + 1) m) (code alphabet n m)
        (dropFOMap alphabet n m) (rank_dropFOMap alphabet n m)
        (dropFOOfP alphabet n m) (mem_dropFOOfP alphabet n m)
        (complete_dropFOOfP alphabet n m)]
      rw [formulaLanguage_exFO]
      constructor
      · rintro ⟨source, hmap, hsource⟩
        let decoded := decodeTree alphabet (n + 1) m source
        refine ⟨decoded, ?_, ?_⟩
        · have := congrArg (decodeTree alphabet n m) hmap
          simpa only [decoded, codeTree, decodeTree_dropFO,
            decode_codeTree] using this
        · apply (ih decoded).mp
          have hcode : codeTree alphabet (n + 1) m decoded = source := by
            exact code_decodeTree alphabet (n + 1) m source
          rw [hcode]
          exact hsource
      · rintro ⟨source, rfl, hsource⟩
        refine ⟨codeTree alphabet (n + 1) m source, ?_, ?_⟩
        · apply Function.LeftInverse.injective
            (fun coded => code_decodeTree alphabet n m coded)
          simp only [codeTree, decodeTree_dropFO, decode_codeTree]
        · exact (ih source).mpr hsource
  | exSO phi ih =>
      rename_i _ _ n m
      intro t
      rw [compileFormula]
      rw [project_accepts_iff (code alphabet n (m + 1)) (code alphabet n m)
        (dropSOMap alphabet n m) (rank_dropSOMap alphabet n m)
        (dropSOOfP alphabet n m) (mem_dropSOOfP alphabet n m)
        (complete_dropSOOfP alphabet n m)]
      rw [formulaLanguage_exSO]
      constructor
      · rintro ⟨source, hmap, hsource⟩
        let decoded := decodeTree alphabet n (m + 1) source
        refine ⟨decoded, ?_, ?_⟩
        · have := congrArg (decodeTree alphabet n m) hmap
          simpa only [decoded, codeTree, decodeTree_dropSO,
            decode_codeTree] using this
        · apply (ih decoded).mp
          have hcode : codeTree alphabet n (m + 1) decoded = source := by
            exact code_decodeTree alphabet n (m + 1) source
          rw [hcode]
          exact hsource
      · rintro ⟨source, rfl, hsource⟩
        refine ⟨codeTree alphabet n (m + 1) source, ?_, ?_⟩
        · apply Function.LeftInverse.injective
            (fun coded => code_decodeTree alphabet n m coded)
          simp only [codeTree, decodeTree_dropSO, decode_codeTree]
        · exact (ih source).mpr hsource

/-- Embed an unmarked alphabet into its zero-marker coding. -/
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
      simpa using! ih (Fin.cast (rank_zeroSymbolMap alphabet a) i)

/-- Direct formula-to-automaton translation on an intrinsic sentence. -/
def compileSentence (alphabet : RankedAlphabetCode)
    (phi : Lax146103.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet)) : AutomatonCode :=
  pullback alphabet
    (fun a => if h : a < alphabet.length then
      (zeroSymbolMap alphabet ⟨a, h⟩).val else 0)
    (compileFormula alphabet phi)

theorem compileSentence_language (alphabet : RankedAlphabetCode)
    (phi : Lax146103.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet)) :
    AutomatonCode.language alphabet (compileSentence alphabet phi) =
      sentenceLanguage phi := by
  ext t
  simp only [compileSentence, AutomatonCode.language]
  change ((pullback alphabet
      (fun a => if h : a < alphabet.length then
        (zeroSymbolMap alphabet ⟨a, h⟩).val else 0)
      (compileFormula alphabet phi)).toAutomaton alphabet).Accepts t ↔ _
  rw [pullback_accepts_iff alphabet (code alphabet 0 0)
    (zeroSymbolMap alphabet) (rank_zeroSymbolMap alphabet)]
  rw [mapTree_zero_eq]
  rw [compileFormula_correct]
  exact emptyMark_mem_formulaLanguage_iff t phi

end Lax842588Proofs.IntrinsicFormulaCompiler
