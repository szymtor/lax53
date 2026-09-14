import Lax842588Proofs.IntrinsicCompilerFields
import Lax842588Proofs.EncodedAutomataComputability

/-! Primitive-recursiveness of the complete normalized-field compiler fold. -/

namespace Lax842588Proofs.IntrinsicCompilerFields

set_option maxHeartbeats 2000000

open Lax842588.ValueTranslations
open Lax842588Proofs.IntrinsicFormulaCompiler Lax842588Proofs.EncodedAutomataOperations
open Lax842588Proofs.EncodedAutomataComputability Lax842588Proofs.EncodedPrimitiveAtomicAutomata
open Lax842588Proofs.EncodedPrimitiveProjection Lax842588Proofs.EncodedProjection
open Lax842588Proofs.MarkedAlphabetEncoding Lax842588Proofs.EncodedComputableDeterminization

theorem applyFields_prim {X : Type*} [Primcodable X]
    (alphabet : X → RankedAlphabetCode) (row : X → List Nat)
    (left right : X → AutomatonCode)
    (halphabet : Primrec alphabet) (hrow : Primrec row)
    (hleft : Primrec left) (hright : Primrec right) :
    Primrec fun v => applyFields (alphabet v) (row v) (left v) (right v) := by
  let n := fun v => (row v).getD 1 0
  let m := fun v => (row v).getD 2 0
  let x := fun v => (row v).getD 3 0
  let y := fun v => (row v).getD 4 0
  let z := fun v => (row v).getD 5 0
  have hfield (k : Nat) : Primrec fun v => (row v).getD k 0 :=
    (Primrec.list_getD 0).comp hrow (Primrec.const k)
  have hn : Primrec n := hfield 1
  have hm : Primrec m := hfield 2
  have hx : Primrec x := hfield 3
  have hy : Primrec y := hfield 4
  have hz : Primrec z := hfield 5
  have htag (k : Nat) : PrimrecPred fun v => (row v).getD 0 0 = k :=
    Primrec.eq.comp (hfield 0) (Primrec.const k)
  have hcode : Primrec fun v => code (alphabet v) (n v) (m v) :=
    code_prim.comp (Primrec.pair halphabet (Primrec.pair hn hm))
  have hvalid := validCodeP_prim alphabet n m halphabet hn hm
  have hfo (index : X → Nat) (hindex : Primrec index) :
      Primrec fun p : X × Nat => foMarked (n p.1) (m p.1) p.2 (index p.1) :=
    foMarked_prim.comp (Primrec.pair (hn.comp Primrec.fst)
      (Primrec.pair (hm.comp Primrec.fst) (Primrec.pair Primrec.snd (hindex.comp Primrec.fst))))
  have hso : Primrec fun p : X × Nat => soMarked (m p.1) p.2 (y p.1) :=
    soMarked_prim.comp (Primrec.pair (hm.comp Primrec.fst)
      (Primrec.pair Primrec.snd (hy.comp Primrec.fst)))
  have hbase : Primrec fun p : X × Nat => baseSymbol (n p.1) (m p.1) p.2 :=
    baseSymbol_prim.comp (Primrec.pair (hn.comp Primrec.fst)
      (Primrec.pair (hm.comp Primrec.fst) Primrec.snd))
  have hequal := somewhereCodeP_prim alphabet n m
    (fun v a => foMarked (n v) (m v) a (x v) && foMarked (n v) (m v) a (y v))
    halphabet hn hm (Primrec.and.comp (hfo x hx) (hfo y hy))
  have hlabel := somewhereCodeP_prim alphabet n m
    (fun v a => decide (baseSymbol (n v) (m v) a = x v) && foMarked (n v) (m v) a (y v))
    halphabet hn hm
    (Primrec.and.comp ((Primrec.eq.comp hbase (hx.comp Primrec.fst)).decide) (hfo y hy))
  have hmem := somewhereCodeP_prim alphabet n m
    (fun v a => foMarked (n v) (m v) a (x v) && soMarked (m v) a (y v))
    halphabet hn hm (Primrec.and.comp (hfo x hx) hso)
  have hinter {f g : X → AutomatonCode} (hf : Primrec f) (hg : Primrec g) :
      Primrec fun v => inter (code (alphabet v) (n v) (m v)) (f v) (g v) :=
    inter_prim.comp (Primrec.pair hcode (Primrec.pair hf hg))
  have hedge := edgeCodeP_prim alphabet n m x y z halphabet hn hm hx hy hz
  have hor := union_prim (fun v => code (alphabet v) (n v) (m v)) left right hcode hleft hright
  have hneg := hinter hvalid
    (compl_prim (fun v => code (alphabet v) (n v) (m v)) right hcode hright)
  have hdropFO : Primrec fun p : X × Nat => dropFOOfP (alphabet p.1) (n p.1) (m p.1) p.2 :=
    dropFOOfP_prim.comp (Primrec.pair (halphabet.comp Primrec.fst)
      (Primrec.pair (hn.comp Primrec.fst) (Primrec.pair (hm.comp Primrec.fst) Primrec.snd)))
  have hdropSO : Primrec fun p : X × Nat => dropSOOfP (alphabet p.1) (n p.1) (m p.1) p.2 :=
    dropSOOfP_prim.comp (Primrec.pair (halphabet.comp Primrec.fst)
      (Primrec.pair (hn.comp Primrec.fst) (Primrec.pair (hm.comp Primrec.fst) Primrec.snd)))
  have hFO := project_prim (fun v => code (alphabet v) (n v) (m v))
    (fun v a => dropFOOfP (alphabet v) (n v) (m v) a) right hcode hdropFO hright
  have hSO := project_prim (fun v => code (alphabet v) (n v) (m v))
    (fun v a => dropSOOfP (alphabet v) (n v) (m v) a) right hcode hdropSO hright
  have hempty : Primrec fun _ : X => ((1, [], []) : AutomatonCode) := Primrec.const _
  simpa only [applyFields, emptyCode_eq] using
    Primrec.ite (htag 0) hempty
      (Primrec.ite (htag 1) (hinter hvalid hequal)
        (Primrec.ite (htag 2) (hinter hvalid hlabel)
          (Primrec.ite (htag 3) (hinter hvalid hedge)
            (Primrec.ite (htag 4) (hinter hvalid hmem)
              (Primrec.ite (htag 5) hor
                (Primrec.ite (htag 6) hneg
                  (Primrec.ite (htag 7) hFO (Primrec.ite (htag 8) hSO hempty))))))))

theorem popCount_prim : Primrec popCount := by
  have htag (k : Nat) : PrimrecPred fun row : List Nat => row.getD 0 0 = k :=
    Primrec.eq.comp ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 0)) (Primrec.const k)
  exact Primrec.ite (htag 5) (Primrec.const 2)
    (Primrec.ite (htag 6) (Primrec.const 1)
      (Primrec.ite (htag 7) (Primrec.const 1)
        (Primrec.ite (htag 8) (Primrec.const 1) (Primrec.const 0))))

theorem stackStep_prim {X : Type*} [Primcodable X]
    (alphabet : X → RankedAlphabetCode) (stack : X → List AutomatonCode) (row : X → List Nat)
    (halphabet : Primrec alphabet) (hstack : Primrec stack) (hrow : Primrec row) :
    Primrec fun v => stackStep (alphabet v) (stack v) (row v) := by
  have hget (k : Nat) : Primrec fun v => (stack v).getD k ((1, [], []) : AutomatonCode) :=
    (Primrec.list_getD (1, [], [])).comp hstack (Primrec.const k)
  exact Primrec.list_cons.comp
    (applyFields_prim alphabet row _ _ halphabet hrow (hget 1) (hget 0))
    (Primrec.list_drop.comp (popCount_prim.comp hrow) hstack)

theorem compileRows_prim : Primrec fun p : RankedAlphabetCode × List (List Nat) =>
    compileRows p.1 p.2 := by
  have hfold : Primrec fun p : RankedAlphabetCode × List (List Nat) =>
      p.2.foldl (stackStep p.1) [] := by
    apply Primrec.list_foldl (h := fun p sb => stackStep p.1 sb.1 sb.2)
      Primrec.snd (Primrec.const [])
    exact stackStep_prim
      (X := (RankedAlphabetCode × List (List Nat)) × (List AutomatonCode × List Nat))
      (fun p => p.1.1) (fun p => p.2.1) (fun p => p.2.2)
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_getD (1, [], [])).comp hfold (Primrec.const 0)

end Lax842588Proofs.IntrinsicCompilerFields
