import Lax842588Proofs.IntrinsicFieldPaths
import Lax842588Proofs.CompilerArrayPacking

/-!
One fixed, charged constructor-field extractor. Runtime tags select branches;
the input formula never selects a different program. Every branch writes all
six working fields, including zero padding, and preserves the certified arena.
-/

namespace Lax842588Proofs.IntrinsicFieldExtraction

set_option maxHeartbeats 3000000

open Lax865980Proofs.Imp Lax865980Proofs.Reasoning Lax865980Proofs.Compile
open Lax842588.ValueTranslations Lax842588.TreeStructure Lax842588.StructuralRepresentations
open Lax842588Proofs.ArenaSemantics Lax842588Proofs.ArenaFieldAccess
open Lax842588Proofs.IntrinsicFieldPaths Lax842588Proofs.IntrinsicCompilerFields
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.MarkedTrees
open Lax560851.StructuralPresentation Lax560851.StructuralCombinators Lax560851.WordArena

def read (path : List Bool) : Expr := payload (.var "currentFormula") path

def row (tag : Nat) (x y z : Expr) : Com :=
  .seq (.assign "fieldTag" (.lit tag))
    (.seq (.assign "fieldFO" (.var "currentFO"))
      (.seq (.assign "fieldSO" (.var "currentSO"))
        (.seq (.assign "fieldX" x)
          (.seq (.assign "fieldY" y) (.assign "fieldZ" z)))))

def isTag (name : String) : Cond :=
  .eq (.var "formulaTag") (.lit (Raw.constructorNameCode name))

def relationChoice (tag : Nat) : Com :=
  if tag = Raw.constructorNameCode "label" then
    row 2 (read firstTerm) (read termZero) (.lit 0)
  else row 3 (read firstTerm) (read termZero) (read termOne)

def relation : Com :=
  .seq (.assign "fieldRelationTag" (read relationTag))
    (.ite (.eq (.var "fieldRelationTag") (.lit (Raw.constructorNameCode "label")))
      (row 2 (read firstTerm) (read termZero) (.lit 0))
      (row 3 (read firstTerm) (read termZero) (read termOne)))

def branches : List (String × Com) :=
  [("equal", row 1 (read firstTerm) (read secondTerm) (.lit 0)),
    ("rel", relation), ("mem", row 4 (read firstTerm) (read secondField) (.lit 0)),
    ("or", row 5 (.lit 0) (.lit 0) (.lit 0)),
    ("neg", row 6 (.lit 0) (.lit 0) (.lit 0)),
    ("exFO", row 7 (.lit 0) (.lit 0) (.lit 0)),
    ("exSO", row 8 (.lit 0) (.lit 0) (.lit 0))]

def dispatch : List (String × Com) → Com
  | [] => row 0 (.lit 0) (.lit 0) (.lit 0)
  | (name, body) :: rest => .ite (isTag name) body (dispatch rest)

/-- Proof-only identification of the branch reached by runtime dispatch. -/
def chosen (tag : Nat) : List (String × Com) → Com
  | [] => row 0 (.lit 0) (.lit 0) (.lit 0)
  | (name, body) :: rest => if tag = Raw.constructorNameCode name then body else chosen tag rest

def program : Com := dispatch branches

theorem dispatch_run (B tag : Nat) (σ τ : Env) (K : Nat)
    (bs : List (String × Com)) (hσ : σ.vars "formulaTag" = tag) (htag : tag < B)
    (hfit : ∀ entry ∈ bs, Raw.constructorNameCode entry.1 < B)
    (hrun : Run B (chosen tag bs) σ τ K) :
    Run B (dispatch bs) σ τ (K + 4 * bs.length) := by
  induction bs with
  | nil => simpa [chosen, dispatch] using hrun
  | cons entry rest ih =>
      obtain ⟨name, body⟩ := entry
      have hname := hfit (name, body) (by simp)
      by_cases he : tag = Raw.constructorNameCode name
      · have hb : (isTag name).evalB B σ = some true := by
          simp [isTag, Cond.evalB, Expr.evalB, hσ, he, fit_self hname]
        have hr : Run B body σ τ K := by simpa [chosen, he] using hrun
        exact (Run.ite_true hb hr).mono (by simp [isTag, Cond.size, Expr.size]; omega)
      · have hb : (isTag name).evalB B σ = some false := by
          simp [isTag, Cond.evalB, Expr.evalB, hσ, he, fit_self hname, fit_self htag]
        have hr := ih (fun entry hentry => hfit entry (by simp [hentry]))
          (by simpa [chosen, he] using hrun)
        exact (Run.ite_false hb hr).mono (by simp [isTag, Cond.size, Expr.size]; omega)

def names : List String :=
  ["falsum", "equal", "rel", "mem", "or", "neg", "exFO", "exSO", "label", "child"]

def TagsFit (B : Nat) : Prop := ∀ name ∈ names, Raw.constructorNameCode name < B

def Ready (I : WordImage) {alphabet : RankedAlphabetCode}
    (o : Occurrence alphabet) (root : Nat) (σ : Env) : Prop :=
  σ.arrs "Arena" = arenaWords I ∧ σ.vars "currentFormula" = root ∧
    σ.vars "currentFO" = o.fo ∧ σ.vars "currentSO" = o.so ∧
    σ.vars "formulaTag" = Raw.constructorNameCode (constructorName o.formula)

def output (σ : Env) : List Nat :=
  [σ.vars "fieldTag", σ.vars "fieldFO", σ.vars "fieldSO",
    σ.vars "fieldX", σ.vars "fieldY", σ.vars "fieldZ"]

theorem relation_spec (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (o : Occurrence alphabet) (root tag : Nat)
    (hmem : I.memoryWords < B) (hrep : I.Represents root o.raw)
    (hpath : atPath o.raw relationTag = some (.nat tag))
    (htag : tag < B) (hlabel : Raw.constructorNameCode "label" < B)
    (hrow : Spec B (Ready I o root) (relationChoice tag)
      (fun _ σ => output σ = fields o) 400) :
    Spec B (Ready I o root) relation (fun _ σ => output σ = fields o) 450 := by
  intro σ hσ
  obtain ⟨τ, hread, htagValue, hvars, harrs, _, _⟩ :=
    (load_spec B I o.raw relationTag root tag "currentFormula" "fieldRelationTag"
      hmem hrep hpath htag).frame σ ⟨hσ.1, hσ.2.1⟩
  have hready : Ready I o root τ := by
    simpa [Ready, hvars "currentFormula" (by simp [Com.wvars]),
      hvars "currentFO" (by simp [Com.wvars]), hvars "currentSO" (by simp [Com.wvars]),
      hvars "formulaTag" (by simp [Com.wvars]), harrs "Arena" (by simp [Com.warrs])] using hσ
  obtain ⟨υ, hbody, hout⟩ := hrow τ hready
  by_cases he : tag = Raw.constructorNameCode "label"
  · have hb : (Cond.eq (.var "fieldRelationTag") (.lit (Raw.constructorNameCode "label"))).evalB B τ = some true := by
      simp [Cond.evalB, Expr.evalB, htagValue, he, fit_self hlabel]
    have hr : Run B (row 2 (read firstTerm) (read termZero) (.lit 0)) τ υ 400 := by
      simpa [relationChoice, he] using hbody
    exact ⟨υ, (hread.seq (Run.ite_true hb hr)).mono (by
      simp [relationTag, Cond.size, Expr.size]), hout⟩
  · have hb : (Cond.eq (.var "fieldRelationTag") (.lit (Raw.constructorNameCode "label"))).evalB B τ = some false := by
      simp [Cond.evalB, Expr.evalB, htagValue, he, fit_self hlabel, fit_self htag]
    have hr : Run B (row 3 (read firstTerm) (read termZero) (read termOne)) τ υ 400 := by
      simpa [relationChoice, he] using hbody
    exact ⟨υ, (hread.seq (Run.ite_false hb hr)).mono (by
      simp [relationTag, Cond.size, Expr.size]), hout⟩

attribute [-simp] treeTerm_eq_var in
theorem program_spec (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (o : Occurrence alphabet) (root : Nat)
    (hmem : I.memoryWords < B) (hrep : I.Represents root o.raw)
    (h8 : 8 < B) (htags : TagsFit B) (hn : o.fo < B) (hm : o.so < B)
    (hfields : ∀ value ∈ fields o, value < B) :
    Spec B (Ready I o root) program (fun _ σ => output σ = fields o) 500 := by
  have hFalsum := htags "falsum" (by simp [names])
  have hEqual := htags "equal" (by simp [names])
  have hRel := htags "rel" (by simp [names])
  have hMem := htags "mem" (by simp [names])
  have hOr := htags "or" (by simp [names])
  have hNeg := htags "neg" (by simp [names])
  have hFO := htags "exFO" (by simp [names])
  have hSO := htags "exSO" (by simp [names])
  have hLabel := htags "label" (by simp [names])
  have hChild := htags "child" (by simp [names])
  have htagB : Raw.constructorNameCode (constructorName o.formula) < B := by
    apply htags
    obtain ⟨n, m, f⟩ := o
    cases f <;> simp [constructorName, names]
  have hbranchFit : ∀ entry ∈ branches, Raw.constructorNameCode entry.1 < B := by
    simp [branches]
    exact ⟨hEqual, hRel, hMem, hOr, hNeg, hFO, hSO⟩
  obtain ⟨n, m, f⟩ := o
  have load (path : List Bool) (value : Nat) (dst : String)
      (hpath : atPath (formulaStructure alphabet f) path = some (.nat value))
      (hv : value < B) :=
    (load_spec B I (formulaStructure alphabet f) path root value "currentFormula" dst
      hmem hrep hpath hv).frame
  have hselected : Spec B (Ready I ⟨n, m, f⟩ root)
      (chosen (Raw.constructorNameCode (constructorName f)) branches)
      (fun _ σ => output σ = fields ⟨n, m, f⟩) 450 := by
   cases f with
  | equal x y =>
      have hx := load firstTerm (treeTermVar x).val "fieldX" (equal_first alphabet x y)
        (hfields _ (by simp [fields]))
      have hy := load secondTerm (treeTermVar y).val "fieldY" (equal_second alphabet x y)
        (hfields _ (by simp [fields]))
      simp only [firstTerm, secondTerm, List.length_cons, List.length_nil] at hx hy
      simp only [constructorName, branches, chosen, tag_eq_iff]
      simp
      unfold row read
      run_vcg [hx, hy]
      all_goals simp_all [Ready, output, fields, Com.wvars, Com.warrs]
  | mem x X =>
      have hx := load firstTerm (treeTermVar x).val "fieldX" (mem_first alphabet x X)
        (hfields _ (by simp [fields]))
      have hy := load secondField X.val "fieldY" (mem_second alphabet x X)
        (hfields _ (by simp [fields]))
      simp only [firstTerm, secondField, List.length_cons, List.length_nil] at hx hy
      simp [constructorName, branches, chosen, tag_eq_iff]
      unfold row read
      run_vcg [hx, hy]
      all_goals simp_all [Ready, output, fields, Com.wvars, Com.warrs]
  | rel r ts =>
      cases r with
      | label symbol =>
          have hx := load firstTerm symbol.val "fieldX" (label_value alphabet symbol ts)
            (hfields _ (by simp [fields]))
          have hy := load termZero (treeTermVar (ts 0)).val "fieldY" (label_term alphabet symbol ts)
            (hfields _ (by simp [fields]))
          simp only [firstTerm, termZero, List.length_cons, List.length_nil] at hx hy
          simp [constructorName, branches, chosen, tag_eq_iff]
          apply relation_spec B I alphabet _ root (Raw.constructorNameCode "label")
            hmem hrep (label_tag alphabet symbol ts) hLabel hLabel
          simp [relationChoice]
          unfold row read
          run_vcg [hx, hy]
          all_goals simp_all [Ready, output, fields, Com.wvars, Com.warrs]
      | child slot =>
          have hx := load firstTerm slot.val "fieldX" (child_value alphabet slot ts)
            (hfields _ (by simp [fields]))
          have hy := load termZero (treeTermVar (ts 0)).val "fieldY" (child_first alphabet slot ts)
            (hfields _ (by simp [fields]))
          have hz := load termOne (treeTermVar (ts 1)).val "fieldZ" (child_second alphabet slot ts)
            (hfields _ (by simp [fields]))
          simp only [firstTerm, termZero, termOne, List.length_cons, List.length_nil] at hx hy hz
          simp [constructorName, branches, chosen, tag_eq_iff]
          apply relation_spec B I alphabet _ root (Raw.constructorNameCode "child")
            hmem hrep (child_tag alphabet slot ts) hChild hLabel
          simp [relationChoice, tag_eq_iff]
          unfold row read
          run_vcg [hx, hy, hz]
          all_goals simp_all [Ready, output, fields, Com.wvars, Com.warrs]
  | _ =>
      simp [constructorName, branches, chosen, tag_eq_iff]
      unfold row
      run_vcg
      all_goals simp_all [Ready, output, fields, Com.wvars, Com.warrs]
  intro σ hσ
  obtain ⟨τ, hrun, hout⟩ := hselected σ hσ
  exact ⟨τ, (dispatch_run B _ σ τ 450 branches hσ.2.2.2.2 htagB hbranchFit hrun).mono
    (by simp [branches]), hout⟩

@[simp] theorem program_warrs : program.warrs = [] := by
  simp [program, dispatch, branches, relation, row, Com.warrs]

theorem program_noRead : ¬ program.reads := by
  simp [program, dispatch, branches, relation, row, Com.reads]

theorem program_noWrite : program.NoWrite := by
  simp [program, dispatch, branches, relation, row, Com.NoWrite]

def scalars : List String :=
  ["currentFormula", "currentFO", "currentSO", "formulaTag", "fieldRelationTag",
    "fieldTag", "fieldFO", "fieldSO", "fieldX", "fieldY", "fieldZ"]

theorem program_ok (L : Layout) (ht : 9 ≤ L.temps)
    (ha : "Arena" ∈ L.arrays) (hs : ∀ s ∈ scalars, s ∈ L.scalars) :
    Com.Ok L program := by
  have hcurrentFormula := hs "currentFormula" (by simp [scalars])
  have hcurrentFO := hs "currentFO" (by simp [scalars])
  have hcurrentSO := hs "currentSO" (by simp [scalars])
  have hformulaTag := hs "formulaTag" (by simp [scalars])
  have hfieldRelationTag := hs "fieldRelationTag" (by simp [scalars])
  have hfieldTag := hs "fieldTag" (by simp [scalars])
  have hfieldFO := hs "fieldFO" (by simp [scalars])
  have hfieldSO := hs "fieldSO" (by simp [scalars])
  have hfieldX := hs "fieldX" (by simp [scalars])
  have hfieldY := hs "fieldY" (by simp [scalars])
  have hfieldZ := hs "fieldZ" (by simp [scalars])
  simp [program, dispatch, branches, relation, row, isTag, read, payload, follow,
    firstTerm, secondTerm, secondField, relationTag, termZero, termOne,
    Com.Ok, Cond.Ok, Expr.Ok, condExpr, ha, hcurrentFormula, hcurrentFO,
    hcurrentSO, hformulaTag, hfieldRelationTag, hfieldTag, hfieldFO, hfieldSO,
    hfieldX, hfieldY, hfieldZ]
  omega

/-- No extra array is needed to pack a row: the six output registers suffice. -/
def outputRegisters : List String :=
  ["fieldTag", "fieldFO", "fieldSO", "fieldX", "fieldY", "fieldZ"]

def packedProgram : Com :=
  .seq program (CompilerArrayPacking.registerProgram "fieldCode" outputRegisters)

theorem packedProgram_spec (B : Nat) (I : WordImage) (alphabet : RankedAlphabetCode)
    (o : Occurrence alphabet) (root : Nat)
    (hmem : I.memoryWords < B) (hrep : I.Represents root o.raw)
    (h8 : 8 < B) (htags : TagsFit B) (hn : o.fo < B) (hm : o.so < B)
    (hfields : ∀ value ∈ fields o, value < B)
    (hcode : (2 * Encodable.encode (fields o) + 3) ^ 2 < B) :
    Spec B (Ready I o root) packedProgram
      (fun _ σ => σ.vars "fieldCode" = Encodable.encode (fields o)) 675 := by
  intro σ hσ
  obtain ⟨τ, he, hf⟩ := program_spec B I alphabet o root hmem hrep h8 htags hn hm hfields σ hσ
  obtain ⟨υ, hp, hc⟩ := CompilerArrayPacking.registerProgram_spec B "fieldCode"
    outputRegisters (fields o) (by simp [outputRegisters]) hcode τ
      (by simpa [outputRegisters, output] using hf)
  exact ⟨υ, (he.seq hp).mono (by simp [outputRegisters]), hc⟩

@[simp] theorem packedProgram_warrs : packedProgram.warrs = [] := by
  simp [packedProgram, Com.warrs]

theorem packedProgram_ok (L : Layout) (ht : 9 ≤ L.temps)
    (ha : "Arena" ∈ L.arrays) (hs : ∀ s ∈ scalars, s ∈ L.scalars)
    (hc : "fieldCode" ∈ L.scalars) : Com.Ok L packedProgram := by
  refine ⟨program_ok L ht ha hs, CompilerArrayPacking.registerProgram_ok
    "fieldCode" outputRegisters L (by omega) hc ?_⟩
  intro s hs'
  apply hs s
  simp [outputRegisters] at hs'
  rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [scalars]

theorem packedProgram_noRead : ¬ packedProgram.reads := by
  simp [packedProgram, Com.reads, program_noRead, CompilerArrayPacking.registerProgram_noRead]

theorem packedProgram_noWrite : packedProgram.NoWrite := by
  exact ⟨program_noWrite, CompilerArrayPacking.registerProgram_noWrite _ _⟩

end Lax842588Proofs.IntrinsicFieldExtraction
