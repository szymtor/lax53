import Lax842588Proofs.IntrinsicCompilerRam
import Lax842588Proofs.RuntimeLayout

/-!
The generic compiler produces the existing evaluator's flat automaton table.
Formatting is composed inside the primitive-recursive computation, hence
inside its charged RAM execution. The subsequent output adapter only needs
to unpack one list of naturals, not reconstruct nested automaton records.
-/

namespace Lax842588Proofs.IntrinsicCompilerFields

open Lax842588.ValueTranslations Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.PrimitiveRecursiveRam
open Lax759944Proofs.Legacy.Ram Lax759944Proofs.Legacy.RamComputes

theorem maximumRank_prim : Primrec maximumRank := by
  exact Primrec.list_foldl (h := fun (_ : List Nat) sb => max sb.1 sb.2)
    Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem encodeTransitionFixed_prim : Primrec fun p : Nat × TransitionCode =>
    encodeTransitionFixed p.1 p.2 := by
  have hs : Primrec fun p : Nat × TransitionCode => p.2.1 := Primrec.fst.comp Primrec.snd
  have hp : Primrec fun p : Nat × TransitionCode => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec fun p : Nat × TransitionCode => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hpad : Primrec fun p : Nat × TransitionCode =>
      (List.range p.1).map (fun i => p.2.2.2.getD i 0) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst)
      ((Primrec.list_getD 0).comp (hc.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_cons.comp hs (Primrec.list_cons.comp hp
    (Primrec.list_cons.comp (Primrec.list_length.comp hc) hpad))

theorem encodeAutomaton_prim : Primrec encodeAutomaton := by
  have ha : Primrec fun p : EncodedAutomaton => p.1 := Primrec.fst
  have hq : Primrec fun p : EncodedAutomaton => p.2.1 := Primrec.fst.comp Primrec.snd
  have ht : Primrec fun p : EncodedAutomaton => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hf : Primrec fun p : EncodedAutomaton => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hr := maximumRank_prim.comp ha
  have hrows : Primrec fun p : EncodedAutomaton =>
      p.2.2.1.flatMap (encodeTransitionFixed (maximumRank p.1)) :=
    Primrec.list_flatMap ht
      (encodeTransitionFixed_prim.comp (Primrec.pair (hr.comp Primrec.fst) Primrec.snd))
  have hheader : Primrec fun p : EncodedAutomaton =>
      [p.2.1, p.2.2.1.length, maximumRank p.1] :=
    Primrec.list_cons.comp hq (Primrec.list_cons.comp (Primrec.list_length.comp ht)
      (Primrec.list_cons.comp hr (Primrec.const [])))
  have hfinal : Primrec fun p : EncodedAutomaton => block p.2.2.2 :=
    Primrec.list_cons.comp (Primrec.list_length.comp hf) hf
  exact Primrec.list_cons.comp (Primrec.list_length.comp ha)
    (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.list_append.comp ha hheader) hrows) hfinal)

def compileTable (alphabet : RankedAlphabetCode) (rows : List (List Nat)) : List Nat :=
  encodeAutomaton (alphabet, compileRows alphabet rows)

theorem compileTable_eq (alphabet : RankedAlphabetCode) {n m : Nat}
    (f : Lax146103.MSOSyntax.Formula
      (Lax842588.TreeStructure.treeSignature alphabet.toRankedAlphabet) n m) :
    compileTable alphabet ((FormulaArenaTraversalModel.postorder alphabet f).map fields) =
      encodeAutomaton (alphabet, IntrinsicFormulaCompiler.compileFormula alphabet f) := by
  rw [compileTable, compileRows_eq]

theorem compileTable_prim : Primrec fun p : RankedAlphabetCode × List (List Nat) =>
    compileTable p.1 p.2 :=
  encodeAutomaton_prim.comp (Primrec.pair Primrec.fst compileRows_prim)

/-- All table construction is part of the same measured compiler call.
The `Option` tag is the generic bridge's internal decoding convention. -/
theorem compileTable_ram :
    ∃ (p : Program) (time words : Nat → Nat), Primrec time ∧ Primrec words ∧
      ∀ (alphabet : RankedAlphabetCode) (rows : List (List Nat)) (w : Nat),
        words (Encodable.encode (alphabet, rows)) ≤ 2 ^ w →
        ComputesInTime w p {[Encodable.encode (alphabet, rows)]}
          (fun _ => [Encodable.encode (some (compileTable alphabet rows))])
          (fun _ => time (Encodable.encode (alphabet, rows))) := by
  obtain ⟨p, time, words, ht, hw, hrun⟩ := exists_typed_ram compileTable_prim
  exact ⟨p, time, words, ht, hw, fun alphabet rows w hfit => hrun (alphabet, rows) w hfit⟩

end Lax842588Proofs.IntrinsicCompilerFields
