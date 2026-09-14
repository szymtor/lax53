import Lax842588Proofs.IntrinsicOccurrenceInput

/-!
A fixed backward scan of the verified postorder arrays. Each row is extracted
from the certified arena and prepended by charged pairing arithmetic. No row
array or input-dependent program is required, and no global address enters
the resulting numeric compiler input.
-/

namespace Lax842588Proofs.IntrinsicFormulaInput

set_option maxHeartbeats 3000000

open Lax865980Proofs.Imp Lax865980Proofs.Reasoning
open Lax842588.ValueTranslations Lax560851.WordArena
open Lax842588Proofs.ArenaSemantics Lax842588Proofs.FormulaArenaTraversalModel
open Lax842588Proofs.IntrinsicCompilerFields Lax842588Proofs.MSORamCompilerLoad
open Lax842588Proofs.AutomatonRamArenaCorrectness Lax842588Proofs.FormulaArenaTraversalOrder
open Lax842588Proofs.PrimitiveRecursivePairing Lax842588Proofs.CompilerArrayPacking
open Encodable

def rowCodes {alphabet : RankedAlphabetCode} (os : List (Occurrence alphabet)) : List Nat :=
  os.map fun o => encode (fields o)

theorem encode_rowCodes {alphabet : RankedAlphabetCode} (os : List (Occurrence alphabet)) :
    encode (rowCodes os) = encode (os.map fields) := by
  induction os with
  | nil => rfl
  | cons o os ih => simpa [rowCodes, encode_list_cons] using congrArg (fun n => Nat.pair (encode (fields o)) n + 1) ih

/-- The loader's static context, with its varying scan index supplied explicitly. -/
def Context (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (os : List (Occurrence alphabet)) (σ : Env) : Prop :=
  ∀ i (hi : i < os.length),
    CompilerOccurrenceReady B I alphabet os i os[i] (σ.setVar "compilerIndex" i)

theorem context_of_order (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (os : List (Occurrence alphabet)) (σ : Env)
    (hloaded : ArenaLoaded I σ)
    (horder : FormulaOrderRep I alphabet os (σ.arrs "FormulaOrder")
      (σ.arrs "FormulaFOOrder") (σ.arrs "FormulaSOOrder"))
    (hcapacity : ∀ a ∈ ["FormulaOrder", "FormulaFOOrder", "FormulaSOOrder"],
      os.length ≤ (σ.arrs a).length ∧ (σ.arrs a).length < B)
    (hA : σ.vars "A" = alphabet.length) (halphabet : alphabet.length < B)
    (hscopes : ∀ o ∈ os, o.fo < B ∧ o.so < B ∧ 2 ^ o.fo < B ∧
      2 ^ o.so < B ∧ MarkedAlphabetEncoding.symbolCount alphabet o.fo o.so < B) :
    Context B I alphabet os σ := by
  intro i hi
  obtain ⟨hrootLen, hrootB⟩ := hcapacity "FormulaOrder" (by simp)
  obtain ⟨hfoLen, hfoB⟩ := hcapacity "FormulaFOOrder" (by simp)
  obtain ⟨hsoLen, hsoB⟩ := hcapacity "FormulaSOOrder" (by simp)
  obtain ⟨hn, hm, hnWord, hmWord, hsymbols⟩ := hscopes os[i] (List.getElem_mem hi)
  simpa [CompilerOccurrenceReady, ArenaLoaded, List.getElem?_eq_getElem hi] using
    (show ArenaLoaded I σ ∧ i = i ∧ os[i]? = some os[i] ∧
      FormulaOrderRep I alphabet os (σ.arrs "FormulaOrder")
        (σ.arrs "FormulaFOOrder") (σ.arrs "FormulaSOOrder") ∧
      i < (σ.arrs "FormulaOrder").length ∧ i < (σ.arrs "FormulaFOOrder").length ∧
      i < (σ.arrs "FormulaSOOrder").length ∧ (σ.arrs "FormulaOrder").length < B ∧
      (σ.arrs "FormulaFOOrder").length < B ∧ (σ.arrs "FormulaSOOrder").length < B ∧
      alphabet.length < B ∧ os[i].fo < B ∧ os[i].so < B ∧ 2 ^ os[i].fo < B ∧
      2 ^ os[i].so < B ∧ MarkedAlphabetEncoding.symbolCount alphabet os[i].fo os[i].so < B ∧
      σ.vars "A" = alphabet.length from
      ⟨hloaded, rfl, List.getElem?_eq_getElem hi, horder, by omega, by omega, by omega,
        hrootB, hfoB, hsoB, halphabet, hn, hm, hnWord, hmWord, hsymbols, hA⟩)

theorem Context.congr {B : Nat} {I : WordImage} {alphabet : RankedAlphabetCode}
    {os : List (Occurrence alphabet)} {σ τ : Env} (h : Context B I alphabet os σ)
    (ha : τ.arrs = σ.arrs) (hr : τ.vars "root" = σ.vars "root")
    (hl : τ.vars "arenaLen" = σ.vars "arenaLen") (hA : τ.vars "A" = σ.vars "A")
    (hin : τ.inp = σ.inp) : Context B I alphabet os τ := by
  intro i hi
  have hh := h i hi
  simpa [CompilerOccurrenceReady, ArenaLoaded, ha, hr, hl, hA, hin] using hh

def condition : Cond := .lt (.lit 0) (.var "compilerIndex")

def step : Com :=
  .seq (.assign "compilerIndex" (.sub (.var "compilerIndex") (.lit 1)))
    (.seq IntrinsicOccurrenceInput.program
      (.seq (pairProgram "fieldCode" "rowsCode" "rowsCode")
        (.seq (.assign "rowsCode" (.add (.var "rowsCode") (.lit 1)))
          (.assign "compilerIndex" (.sub (.var "compilerIndex") (.lit 1))))))

def loop : Com := .while condition step

def program : Com :=
  .seq (.assign "compilerIndex" (.var "formulaCount"))
    (.seq (.assign "rowsCode" (.lit 0)) loop)

def Inv (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (os : List (Occurrence alphabet)) (σ : Env) : Prop :=
  Context B I alphabet os σ ∧ σ.vars "compilerIndex" ≤ os.length ∧
    σ.vars "rowsCode" = encode ((rowCodes os).drop (σ.vars "compilerIndex"))

theorem condition_eval (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (os : List (Occurrence alphabet)) (σ : Env)
    (hB : (2 * encode (rowCodes os) + 3) ^ 2 < B) (hI : Inv B I alphabet os σ) :
    condition.evalB B σ = some (decide (0 < σ.vars "compilerIndex")) := by
  have hlen := length_le_encode (rowCodes os)
  have hi : σ.vars "compilerIndex" < B := by
    have := hI.2.1
    rw [show (rowCodes os).length = os.length by simp [rowCodes]] at hlen
    nlinarith
  have h0 : 0 < B := by nlinarith
  simp [condition, Cond.evalB, Expr.evalB, fit_self hi, fit_self h0]

theorem step_spec (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (os : List (Occurrence alphabet)) (h8 : 8 < B) (hmem : I.memoryWords < B)
    (hvalues : ∀ value ∈ arenaWords I, value < B)
    (htags : IntrinsicFieldExtraction.TagsFit B)
    (hfields : ∀ o ∈ os, ∀ value ∈ fields o, value < B)
    (hB : (2 * encode (rowCodes os) + 3) ^ 2 < B) :
    Spec B (fun σ => Inv B I alphabet os σ ∧ condition.evalB B σ = some true)
      step (fun σ τ => Inv B I alphabet os τ ∧
        τ.vars "compilerIndex" < σ.vars "compilerIndex") 900 := by
  intro σ hσ
  obtain ⟨hI, ht⟩ := hσ
  rw [condition_eval B I alphabet os σ hB hI] at ht
  have hpos : 0 < σ.vars "compilerIndex" := by simpa using ht
  obtain ⟨hcontext, hi, hc⟩ := hI
  let j := σ.vars "compilerIndex" - 1
  have hj : j < os.length := by dsimp [j]; omega
  have hj' : j < (rowCodes os).length := by simpa [rowCodes] using hj
  have hentry : encode (fields os[j]) ≤ encode (rowCodes os) := by
    simpa [rowCodes] using entry_le_encode (rowCodes os) j hj'
  have htail := encode_drop_le (rowCodes os) (σ.vars "compilerIndex")
  have hnext := encode_drop_le (rowCodes os) j
  have hlen := length_le_encode (rowCodes os)
  rw [show (rowCodes os).length = os.length by simp [rowCodes]] at hlen
  have hrowB : (2 * encode (fields os[j]) + 3) ^ 2 < B := by nlinarith
  have hread := (IntrinsicOccurrenceInput.program_spec B I alphabet os j os[j]
    h8 hmem hvalues htags (hfields _ (List.getElem_mem hj)) hrowB).frame
  have hready := hcontext j hj
  have hpairB : (encode (fields os[j]) + encode ((rowCodes os).drop (σ.vars "compilerIndex")) + 1) ^ 2 < B := by
    nlinarith
  have hpair := (pair_spec B (encode (fields os[j]))
    (encode ((rowCodes os).drop (σ.vars "compilerIndex")))
    "fieldCode" "rowsCode" "rowsCode" hpairB).frame
  have hdrop : encode ((rowCodes os).drop j) =
      Nat.pair (encode (fields os[j]))
        (encode ((rowCodes os).drop (σ.vars "compilerIndex"))) + 1 := by
    have he : j + 1 = σ.vars "compilerIndex" := by dsimp [j]; omega
    rw [List.drop_eq_getElem_cons hj', encode_list_cons, he]
    simp [rowCodes]
  have hframe : ∀ s ∈ ["rowsCode", "root", "arenaLen", "A"],
      s ∉ IntrinsicOccurrenceInput.program.wvars := by
    intro s hs
    simp at hs
    rcases hs with rfl | rfl | rfl | rfl <;>
      simp [IntrinsicOccurrenceInput.program, MSORamCompilerProgram.loadCompilerOccurrence,
        AutomatonRamProgram.seqs, IntrinsicFieldExtraction.packedProgram,
        IntrinsicFieldExtraction.program, IntrinsicFieldExtraction.dispatch,
        IntrinsicFieldExtraction.branches, IntrinsicFieldExtraction.relation,
        IntrinsicFieldExtraction.row, CompilerArrayPacking.registerProgram,
        IntrinsicFieldExtraction.outputRegisters, pairProgram, Com.wvars]
  unfold step
  run_vcg [hread, hpair]
  all_goals simp_all [Inv, Context, CompilerOccurrenceReady, ArenaLoaded, j,
    pairProgram, Com.wvars, Com.warrs, Com.reads, Com.NoWrite, IntrinsicOccurrenceInput.program_warrs,
    IntrinsicOccurrenceInput.program_noRead]
  all_goals try omega
  all_goals try nlinarith

theorem loop_spec (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (os : List (Occurrence alphabet)) (h8 : 8 < B) (hmem : I.memoryWords < B)
    (hvalues : ∀ value ∈ arenaWords I, value < B)
    (htags : IntrinsicFieldExtraction.TagsFit B)
    (hfields : ∀ o ∈ os, ∀ value ∈ fields o, value < B)
    (hB : (2 * encode (rowCodes os) + 3) ^ 2 < B) :
    Spec B (Inv B I alphabet os) loop
      (fun _ σ => σ.vars "rowsCode" = encode (os.map fields))
      (950 * (os.length + 1)) := by
  have hloop : Spec B (Inv B I alphabet os) loop
      (fun _ σ => Inv B I alphabet os σ ∧ condition.evalB B σ = some false)
      (950 * (os.length + 1)) := by
    apply Spec.while_count (Inv B I alphabet os) (fun σ => σ.vars "compilerIndex") 900
    · intro σ hI
      exact ⟨_, condition_eval B I alphabet os σ hB hI⟩
    · exact step_spec B I alphabet os h8 hmem hvalues htags hfields hB
    · exact fun _ h => h
    · intro σ hI
      have := hI.2.1
      simp [condition, Cond.size, Expr.size]
      omega
  apply hloop.post
  intro σ τ _ hτ
  obtain ⟨hI, ht⟩ := hτ
  rw [condition_eval B I alphabet os τ hB hI] at ht
  have hi : τ.vars "compilerIndex" = 0 := by simpa using ht
  simpa [hi, encode_rowCodes] using hI.2.2

theorem program_spec (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (os : List (Occurrence alphabet)) (h8 : 8 < B) (hmem : I.memoryWords < B)
    (hvalues : ∀ value ∈ arenaWords I, value < B)
    (htags : IntrinsicFieldExtraction.TagsFit B)
    (hfields : ∀ o ∈ os, ∀ value ∈ fields o, value < B)
    (hB : (2 * encode (rowCodes os) + 3) ^ 2 < B) :
    Spec B (fun σ => Context B I alphabet os σ ∧ σ.vars "formulaCount" = os.length)
      program (fun _ σ => σ.vars "rowsCode" = encode (os.map fields))
      (1000 * (os.length + 1)) := by
  have hl := length_le_encode (rowCodes os)
  rw [show (rowCodes os).length = os.length by simp [rowCodes]] at hl
  have hloop := loop_spec B I alphabet os h8 hmem hvalues htags hfields hB
  have hlenB : os.length < B := by nlinarith
  intro σ hσ
  obtain ⟨hcontext, hcount⟩ := hσ
  have hinit : Run B (.assign "compilerIndex" (.var "formulaCount")) σ
      (σ.setVar "compilerIndex" os.length) 2 := by
    apply Run.assign
    simp [Expr.evalB, hcount, fit_self hlenB]
  have hzero : Run B (.assign "rowsCode" (.lit 0)) (σ.setVar "compilerIndex" os.length)
      ((σ.setVar "compilerIndex" os.length).setVar "rowsCode" 0) 2 := by
    apply Run.assign
    simp [Expr.evalB, fit_self (show 0 < B by omega)]
  have hcontext' : Context B I alphabet os
      ((σ.setVar "compilerIndex" os.length).setVar "rowsCode" 0) :=
    hcontext.congr rfl (by simp) (by simp) (by simp) rfl
  obtain ⟨τ, hr, hc⟩ := hloop _ ⟨hcontext', by simp,
    by simp [rowCodes, ← List.map_drop]⟩
  exact ⟨τ, (hinit.seq (hzero.seq hr)).mono (by omega), hc⟩

@[simp] theorem program_warrs : program.warrs = [] := by
  simp [program, loop, step, pairProgram, Com.warrs]

theorem program_noRead : ¬ program.reads := by
  simp [program, loop, step, pairProgram, Com.reads, IntrinsicOccurrenceInput.program_noRead]

theorem program_noWrite : program.NoWrite := by
  simp [program, loop, step, pairProgram, Com.NoWrite, IntrinsicOccurrenceInput.program_noWrite]

def scalars : List String := IntrinsicFieldExtraction.scalars ++
  ["fieldCode", "rowsCode", "compilerIndex", "formulaCount", "formulaNameRoot",
    "foMarkerWords", "soMarkerWords", "markedSymbols", "A"]

def arrays : List String := ["Arena", "FormulaOrder", "FormulaFOOrder", "FormulaSOOrder"]

theorem program_ok (L : Lax865980Proofs.Compile.Layout) (ht : 9 ≤ L.temps)
    (hs : ∀ s ∈ scalars, s ∈ L.scalars) (ha : ∀ a ∈ arrays, a ∈ L.arrays) :
    Lax865980Proofs.Compile.Com.Ok L program := by
  have hpacked := IntrinsicFieldExtraction.packedProgram_ok L ht
    (ha "Arena" (by simp [arrays]))
    (fun s h => hs s (List.mem_append_left _ h))
    (hs "fieldCode" (by simp [scalars]))
  have hscalar : ∀ s ∈ ["currentFormula", "currentFO", "currentSO", "formulaTag",
      "fieldCode", "rowsCode", "compilerIndex", "formulaCount", "formulaNameRoot",
      "foMarkerWords", "soMarkerWords", "markedSymbols", "A"], s ∈ L.scalars := by
    intro s h
    apply hs
    simp [scalars, IntrinsicFieldExtraction.scalars] at *
    tauto
  simp only [List.forall_mem_cons, List.forall_mem_nil, and_true] at hscalar
  simp only [arrays, List.forall_mem_cons, List.forall_mem_nil, and_true] at ha
  have hread : Lax865980Proofs.Compile.Com.Ok L IntrinsicOccurrenceInput.program := by
    refine ⟨?_, hpacked⟩
    simp only [MSORamCompilerProgram.loadCompilerOccurrence, AutomatonRamProgram.seqs,
      Lax865980Proofs.Compile.Com.Ok, Lax865980Proofs.Compile.Expr.Ok]
    rcases hscalar with ⟨hcf, hfo, hso, htag, hfc, hrc, hci, hcnt, hname, hfw, hsw, hms, hA⟩
    rcases ha with ⟨har, horder, hforder, hsorder⟩
    simp_all only [true_and, and_true]
    omega
  simp only [program, loop, step, condition, Lax865980Proofs.Compile.Com.Ok, hread,
    pairProgram, Lax865980Proofs.Compile.Cond.Ok, Lax865980Proofs.Compile.Expr.Ok,
    Lax865980Proofs.Compile.condExpr]
  rcases hscalar with ⟨hcf, hfo, hso, htag, hfc, hrc, hci, hcnt, hname, hfw, hsw, hms, hA⟩
  simp_all only [true_and, and_true]
  omega

end Lax842588Proofs.IntrinsicFormulaInput
