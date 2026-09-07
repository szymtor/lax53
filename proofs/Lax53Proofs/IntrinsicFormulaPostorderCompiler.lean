import Lax53Proofs.FormulaArenaTraversalModel
import Lax53Proofs.IntrinsicFormulaCompiler
import Lax53Proofs.MSORamCompilerBinaryWord
import Lax53Proofs.SparsePrimitiveAtomicAutomata

/-!
Pure semantic model for compiling the verified postorder stream. This model
assigns no machine cost; the forthcoming imperative proof relates each stack
transition to charged numeric automaton construction.
-/

namespace Lax53Proofs.IntrinsicFormulaPostorderCompiler

open FirstOrder
open Lax52.MSOSyntax
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.ValueTranslations
open Lax53Proofs.FormulaArenaTraversalModel
open Lax53Proofs.IntrinsicFormulaCompiler
open Lax53Proofs.EncodedAutomataOperations
open Lax53Proofs.EncodedComputableDeterminization
open Lax53Proofs.EncodedAtomicAutomata
open Lax53Proofs.EncodedPrimitiveAtomicAutomata
open Lax53Proofs.EncodedPrimitiveProjection
open Lax53Proofs.EncodedProjection
open Lax53Proofs.MarkedAlphabetEncoding
open Lax53Proofs.AtomicMarkedTrees
open Lax53Proofs.MarkedTrees
open Lax53Proofs.MSOFormulaToTreeAutomata
open Lax53Proofs.QuantifierProjectionSemantics
open Lax53Proofs.EmptyMarkers
open Lax53Proofs.MSORamCompilerBinaryWord
open Lax53Proofs.SparsePrimitiveAtomicAutomata

/-- Pure target of the charged compiler.  It differs from
`IntrinsicFormulaCompiler.compileFormula` only by using the sparse,
row-generated presentation of the three two-state "somewhere" automata. -/
def compileFormulaForRAM (alphabet : RankedAlphabetCode) :
    {n m : Nat} →
      Formula (treeSignature alphabet.toRankedAlphabet) n m → AutomatonCode
  | n, m, .falsum => emptyCode (code alphabet n m)
  | n, m, .equal x y =>
      inter (code alphabet n m) (sparseValidCodeP alphabet n m)
        (binarySomewhereCode (code alphabet n m)
          (fun a => foMarked n m a (treeTermVar x).val &&
            foMarked n m a (treeTermVar y).val))
  | n, m, .rel (.label symbol) terms =>
      inter (code alphabet n m) (sparseValidCodeP alphabet n m)
        (binarySomewhereCode (code alphabet n m)
          (fun s => decide (baseSymbol n m s = symbol.val) &&
            foMarked n m s (treeTermVar (terms 0)).val))
  | n, m, .rel (.child slot) terms =>
      inter (code alphabet n m) (sparseValidCodeP alphabet n m)
        (edgeCodeP alphabet n m slot.val
          (treeTermVar (terms 0)).val
          (treeTermVar (terms 1)).val)
  | n, m, .mem x X =>
      inter (code alphabet n m) (sparseValidCodeP alphabet n m)
        (binarySomewhereCode (code alphabet n m)
          (fun a => foMarked n m a (treeTermVar x).val &&
            soMarked m a X.val))
  | n, m, .or phi psi =>
      EncodedComputableDeterminization.union (code alphabet n m)
        (compileFormulaForRAM alphabet phi) (compileFormulaForRAM alphabet psi)
  | n, m, .neg phi =>
      inter (code alphabet n m) (sparseValidCodeP alphabet n m)
        (EncodedComputableDeterminization.compl (code alphabet n m)
          (compileFormulaForRAM alphabet phi))
  | n, m, .exFO phi =>
      project (code alphabet n m) (dropFOOfP alphabet n m)
        (compileFormulaForRAM alphabet phi)
  | n, m, .exSO phi =>
      project (code alphabet n m) (dropSOOfP alphabet n m)
        (compileFormulaForRAM alphabet phi)

/-- The RAM-oriented sparse presentation recognizes the same marked-tree
language as the intrinsic formula.  This is the semantic bridge that permits
the charged compiler to choose an operationally convenient transition order. -/
theorem compileFormulaForRAM_correct (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat}
      (phi : Formula (treeSignature alphabet.toRankedAlphabet) n m)
      (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)),
      ((compileFormulaForRAM alphabet phi).toAutomaton
        (code alphabet n m)).Accepts (codeTree alphabet n m t) ↔
          t ∈ formulaLanguage phi := by
  intro _ _ phi
  induction phi with
  | falsum =>
      intro t
      rw [compileFormulaForRAM]
      exact iff_false_intro (emptyCode_not_accepts _ _) |>.trans
        (iff_false_intro (not_mem_formulaLanguage_falsum t)).symm
  | equal x y =>
      rename_i _ _ n m
      intro t
      rw [compileFormulaForRAM, inter_accepts_iff,
        sparseValidCodeP_accepts_iff,
        binarySomewhere_accepts_iff_somewhereCodeP alphabet n m
          (fun a => foMarked n m a (treeTermVar x).val &&
            foMarked n m a (treeTermVar y).val)
          (codeTree alphabet n m t),
        somewhereCodeP_accepts_iff alphabet n m
          (fun a => foMarked n m a (treeTermVar x).val &&
            foMarked n m a (treeTermVar y).val)
          (fun s => s.2.1 (treeTermVar x) && s.2.1 (treeTermVar y)) (by
            intro a
            change (foMarked n m a.val (treeTermVar x).val &&
                foMarked n m a.val (treeTermVar y).val) =
              ((fromCodeSymbol alphabet n m a).2.1 (treeTermVar x) &&
                (fromCodeSymbol alphabet n m a).2.1 (treeTermVar y))
            rw [fromCode_fo, fromCode_fo]) t]
      rw [formulaLanguage_equal_eq]
      rfl
  | rel relation terms =>
      rename_i _ _ n m _
      cases relation with
      | label symbol =>
          intro t
          rw [compileFormulaForRAM, inter_accepts_iff,
            sparseValidCodeP_accepts_iff,
            binarySomewhere_accepts_iff_somewhereCodeP alphabet n m
              (fun s => decide (baseSymbol n m s = symbol.val) &&
                foMarked n m s (treeTermVar (terms 0)).val)
              (codeTree alphabet n m t),
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
                    (congrArg Fin.val h)) t]
          rw [formulaLanguage_label_eq]
          rfl
      | child slot =>
          intro t
          rw [compileFormulaForRAM, inter_accepts_iff,
            sparseValidCodeP_accepts_iff,
            edgeCodeP_accepts_iff alphabet n m slot
              (treeTermVar (terms 0)) (treeTermVar (terms 1)) t,
            formulaLanguage_child_eq]
          rfl
  | mem x X =>
      rename_i _ _ n m
      intro t
      rw [compileFormulaForRAM, inter_accepts_iff,
        sparseValidCodeP_accepts_iff,
        binarySomewhere_accepts_iff_somewhereCodeP alphabet n m
          (fun a => foMarked n m a (treeTermVar x).val && soMarked m a X.val)
          (codeTree alphabet n m t),
        somewhereCodeP_accepts_iff alphabet n m
          (fun a => foMarked n m a (treeTermVar x).val && soMarked m a X.val)
          (fun s => s.2.1 (treeTermVar x) && s.2.2 X) (by
            intro a
            change (foMarked n m a.val (treeTermVar x).val &&
                soMarked m a.val X.val) =
              ((fromCodeSymbol alphabet n m a).2.1 (treeTermVar x) &&
                (fromCodeSymbol alphabet n m a).2.2 X)
            rw [fromCode_fo, fromCode_so]) t]
      rw [formulaLanguage_mem_eq]
      rfl
  | or phi psi ihPhi ihPsi =>
      intro t
      rw [compileFormulaForRAM,
        EncodedComputableDeterminization.union_accepts_iff,
        ihPhi t, ihPsi t, formulaLanguage_or]
      rfl
  | neg phi ih =>
      intro t
      rw [compileFormulaForRAM, inter_accepts_iff,
        sparseValidCodeP_accepts_iff,
        EncodedComputableDeterminization.compl_accepts_iff,
        ih t, formulaLanguage_neg]
      rfl
  | exFO phi ih =>
      rename_i _ _ n m
      intro t
      rw [compileFormulaForRAM]
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
      rw [compileFormulaForRAM]
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

/-- One bottom-up compiler transition. Atomic formulas create a primitive
automaton. Compound formulas consume the already compiled child automata from
the stack and apply the same numeric closure operation as the direct intrinsic
compiler. The fallback branches are unreachable on a genuine postorder word. -/
def compileStep (alphabet : RankedAlphabetCode)
    (stack : List AutomatonCode) (occurrence : Occurrence alphabet) :
    List AutomatonCode :=
  match occurrence with
  | ⟨n, m, formula⟩ =>
      match formula with
      | .falsum | .equal _ _ | .rel _ _ | .mem _ _ =>
          compileFormulaForRAM alphabet formula :: stack
      | .or _ _ =>
          match stack with
          | rightCode :: leftCode :: rest =>
              EncodedComputableDeterminization.union
                (MarkedAlphabetEncoding.code alphabet n m)
                leftCode rightCode :: rest
          | _ => []
      | .neg _ =>
          match stack with
          | bodyCode :: rest =>
              inter (MarkedAlphabetEncoding.code alphabet n m)
                (sparseValidCodeP alphabet n m)
                (EncodedComputableDeterminization.compl
                  (MarkedAlphabetEncoding.code alphabet n m) bodyCode) :: rest
          | _ => []
      | .exFO _ =>
          match stack with
          | bodyCode :: rest =>
              project (MarkedAlphabetEncoding.code alphabet n m)
                (dropFOOfP alphabet n m)
                bodyCode :: rest
          | _ => []
      | .exSO _ =>
          match stack with
          | bodyCode :: rest =>
              project (MarkedAlphabetEncoding.code alphabet n m)
                (dropSOOfP alphabet n m)
                bodyCode :: rest
          | _ => []

theorem foldl_postorder (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat}
      (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m)
      (stack : List AutomatonCode),
      (postorder alphabet formula).foldl (compileStep alphabet) stack =
        compileFormulaForRAM alphabet formula :: stack := by
  intro n m formula
  induction formula with
  | falsum =>
      intro stack
      rfl
  | equal lhs rhs =>
      intro stack
      rfl
  | rel relation terms =>
      intro stack
      rfl
  | mem term setVar =>
      intro stack
      rfl
  | or left right ihLeft ihRight =>
      intro stack
      simp only [postorder, List.foldl_append]
      rw [ihLeft stack, ihRight]
      simp [compileStep, compileFormulaForRAM]
  | neg body ih =>
      intro stack
      simp only [postorder, List.foldl_append]
      rw [ih stack]
      simp [compileStep, compileFormulaForRAM]
  | exFO body ih =>
      intro stack
      simp only [postorder, List.foldl_append]
      rw [ih stack]
      simp [compileStep, compileFormulaForRAM]
  | exSO body ih =>
      intro stack
      simp only [postorder, List.foldl_append]
      rw [ih stack]
      simp [compileStep, compileFormulaForRAM]

theorem compile_postorder (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    (postorder alphabet phi).foldl (compileStep alphabet) [] =
      [compileFormulaForRAM alphabet phi] := by
  simpa using foldl_postorder alphabet phi []

end Lax53Proofs.IntrinsicFormulaPostorderCompiler
