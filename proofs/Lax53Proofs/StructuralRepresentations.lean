import Lax53.StructuralRepresentations
import Lax58Proofs.StructuralPresentation

namespace Lax53Proofs.StructuralRepresentations

open Lax53.RankedTree
open FirstOrder
open FirstOrder.Language
open Lax52.MSOSyntax
open Lax53.TreeStructure
open Lax53.ValueTranslations
open Lax53.StructuralRepresentations
open Lax58.StructuralPresentation
open Lax58.StructuralPresentation.Presentation
open Lax58.StructuralCombinators
open Lax58.CertifiedDerivation

universe u

private theorem rawFields_injective : Function.Injective Raw.fields := by
  intro xs ys h
  have wrapped : Raw.constructor "fields" xs = Raw.constructor "fields" ys := by
    simp only [Raw.constructor, h]
  exact (Raw.constructor_eq_iff.mp wrapped).2

private theorem termStructure_injective (alphabet : RankedAlphabetCode) {n : Nat} :
    Function.Injective (@termStructure alphabet n) := by
  intro left right h
  cases left with
  | var left =>
      cases right with
      | var right =>
          simp only [termStructure, Raw.constructor_eq_iff, true_and,
            List.cons.injEq, and_true] at h
          change Raw.nat left.val = Raw.nat right.val at h
          exact congrArg FirstOrder.Language.Term.var (Fin.ext (Raw.nat.inj h))
      | func function _ => exact nomatch function
  | func function _ => exact nomatch function

private theorem symbolFieldRaw_injective (alphabet : RankedAlphabetCode) :
    Function.Injective
      ((CertifiedFieldEncoding.fin alphabet.length).toRaw :
        alphabet.toRankedAlphabet.Symbol → Raw) := by
  intro left right h
  change Raw.nat left.val = Raw.nat right.val at h
  exact Fin.ext (Raw.nat.inj h)

private theorem childIndexFieldRaw_injective (alphabet : RankedAlphabetCode) :
    Function.Injective
      ((CertifiedFieldEncoding.subtype CertifiedFieldEncoding.nat _).toRaw :
        ChildIndex alphabet.toRankedAlphabet → Raw) := by
  intro left right h
  change Raw.nat left.val = Raw.nat right.val at h
  exact Subtype.ext (Raw.nat.inj h)

private theorem finFieldRaw_injective {n : Nat} :
    Function.Injective ((CertifiedFieldEncoding.fin n).toRaw : Fin n → Raw) := by
  intro left right h
  change Raw.nat left.val = Raw.nat right.val at h
  exact Fin.ext (Raw.nat.inj h)

private theorem termFieldRaw_injective (alphabet : RankedAlphabetCode) {n : Nat} :
    Function.Injective
      ((termStructure.certified alphabet).toRaw :
        (treeSignature alphabet.toRankedAlphabet).Term (Fin n) → Raw) := by
  intro left right h
  change termStructure alphabet left = termStructure alphabet right at h
  exact termStructure_injective alphabet h

private theorem relationStructure_injective (alphabet : RankedAlphabetCode)
    {arity : Nat} :
    Function.Injective (@relationStructure alphabet arity) := by
  intro left right h
  cases left with
  | label left =>
      cases right with
      | label right =>
          simp only [relationStructure, Raw.constructor_eq_iff, true_and,
            List.cons.injEq, and_true] at h
          exact congrArg TreeRelation.label
            (symbolFieldRaw_injective alphabet h)
  | child left =>
      cases right with
      | child right =>
          simp only [relationStructure, Raw.constructor_eq_iff, true_and,
            List.cons.injEq, and_true] at h
          exact congrArg TreeRelation.child
            (childIndexFieldRaw_injective alphabet h)

private theorem relationFieldRaw_injective (alphabet : RankedAlphabetCode)
    {arity : Nat} :
    Function.Injective
      ((relationStructure.certified alphabet).toRaw :
        (treeSignature alphabet.toRankedAlphabet).Relations arity → Raw) := by
  intro left right h
  change relationStructure alphabet left = relationStructure alphabet right at h
  exact relationStructure_injective alphabet h

private theorem termFamilyFieldRaw_injective (alphabet : RankedAlphabetCode)
    {n k : Nat} :
    Function.Injective
      ((CertifiedFieldEncoding.family (fun _ => termStructure.certified alphabet)).toRaw :
        (Fin k → (treeSignature alphabet.toRankedAlphabet).Term (Fin n)) → Raw) := by
  intro left right h
  change Raw.fields (List.ofFn fun i => termStructure alphabet (left i)) =
    Raw.fields (List.ofFn fun i => termStructure alphabet (right i)) at h
  have hlist := rawFields_injective h
  funext i
  exact termStructure_injective alphabet
    (congrFun (List.ofFn_injective hlist) i)

private theorem formulaStructure_injective (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat}, Function.Injective (@formulaStructure alphabet n m) := by
  intro n m left
  induction left with
  | falsum =>
      intro right h
      cases right <;> simp_all [formulaStructure, Raw.constructor_eq_iff]
  | equal leftTerm rightTerm =>
      intro right h
      cases right with
      | equal otherLeft otherRight =>
          simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
            List.cons.injEq, and_true] at h
          cases h with
          | intro hleft hright =>
              rw [termFieldRaw_injective alphabet hleft,
                termFieldRaw_injective alphabet hright]
      | _ => simp_all [formulaStructure, Raw.constructor_eq_iff]
  | rel relation terms =>
      intro right h
      cases right with
      | rel otherRelation otherTerms =>
          cases relation with
          | label symbol =>
              cases otherRelation with
              | label otherSymbol =>
                  simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
                    List.cons.injEq, and_true] at h
                  rcases h with ⟨hrelation, hterms⟩
                  change relationStructure alphabet (.label symbol) =
                    relationStructure alphabet (.label otherSymbol) at hrelation
                  simp only [relationStructure, Raw.constructor_eq_iff, true_and,
                    List.cons.injEq, and_true] at hrelation
                  have hsymbol : symbol = otherSymbol :=
                    symbolFieldRaw_injective alphabet hrelation
                  subst otherSymbol
                  have hterms' : terms = otherTerms :=
                    termFamilyFieldRaw_injective alphabet hterms
                  subst otherTerms
                  rfl
              | child otherChild =>
                  simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
                    List.cons.injEq, and_true] at h
                  have hrelation := h.1
                  change relationStructure alphabet (.label symbol) =
                    relationStructure alphabet (.child otherChild) at hrelation
                  simp [relationStructure, Raw.constructor_eq_iff] at hrelation
          | child child =>
              cases otherRelation with
              | label otherSymbol =>
                  simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
                    List.cons.injEq, and_true] at h
                  have hrelation := h.1
                  change relationStructure alphabet (.child child) =
                    relationStructure alphabet (.label otherSymbol) at hrelation
                  simp [relationStructure, Raw.constructor_eq_iff] at hrelation
              | child otherChild =>
                  simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
                    List.cons.injEq, and_true] at h
                  rcases h with ⟨hrelation, hterms⟩
                  change relationStructure alphabet (.child child) =
                    relationStructure alphabet (.child otherChild) at hrelation
                  simp only [relationStructure, Raw.constructor_eq_iff, true_and,
                    List.cons.injEq, and_true] at hrelation
                  have hchild : child = otherChild :=
                    childIndexFieldRaw_injective alphabet hrelation
                  subst otherChild
                  have hterms' : terms = otherTerms :=
                    termFamilyFieldRaw_injective alphabet hterms
                  subst otherTerms
                  rfl
      | _ => simp_all [formulaStructure, Raw.constructor_eq_iff]
  | mem term setVariable =>
      intro right h
      cases right with
      | mem otherTerm otherSetVariable =>
          simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
            List.cons.injEq, and_true] at h
          cases h with
          | intro hterm hset =>
              rw [termFieldRaw_injective alphabet hterm,
                finFieldRaw_injective hset]
      | _ => simp_all [formulaStructure, Raw.constructor_eq_iff]
  | or left right ihLeft ihRight =>
      intro other h
      cases other with
      | or otherLeft otherRight =>
          simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
            List.cons.injEq, and_true] at h
          cases h with
          | intro hleft hright => rw [ihLeft hleft, ihRight hright]
      | _ => simp_all [formulaStructure, Raw.constructor_eq_iff]
  | neg formula ih =>
      intro other h
      cases other with
      | neg other =>
          simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
            List.cons.injEq, and_true] at h
          rw [ih h]
      | _ => simp_all [formulaStructure, Raw.constructor_eq_iff]
  | exFO formula ih =>
      intro other h
      cases other with
      | exFO other =>
          simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
            List.cons.injEq, and_true] at h
          rw [ih h]
      | _ => simp_all [formulaStructure, Raw.constructor_eq_iff]
  | exSO formula ih =>
      intro other h
      cases other with
      | exSO other =>
          simp only [formulaStructure, Raw.constructor_eq_iff, true_and,
            List.cons.injEq, and_true] at h
          rw [ih h]
      | _ => simp_all [formulaStructure, Raw.constructor_eq_iff]

private theorem treeStructure_injective (alphabet : RankedAlphabetCode) :
    Function.Injective (Lax53.StructuralRepresentations.treeStructure alphabet) := by
  intro t
  induction t with
  | node symbol children ih =>
      intro other h
      cases other with
      | node otherSymbol otherChildren =>
          simp only [Lax53.StructuralRepresentations.treeStructure,
            Raw.constructor_eq_iff, true_and] at h
          have listEq := h
          have symbolValEq : symbol.val = otherSymbol.val := by
            have headOptionEq := congrArg List.head? listEq
            simp only [List.head?_cons, Option.some.injEq] at headOptionEq
            change Raw.nat symbol.val = Raw.nat otherSymbol.val at headOptionEq
            injection headOptionEq
          have tailEq :
              List.ofFn (fun i => treeStructure alphabet (children i)) =
                List.ofFn (fun i => treeStructure alphabet (otherChildren i)) := by
            have tailsEq := congrArg List.tail listEq
            simpa using tailsEq
          have symbolEq : symbol = otherSymbol := Fin.ext symbolValEq
          subst otherSymbol
          have childrenEq : children = otherChildren := by
            funext i
            apply ih i
            exact congrFun (List.ofFn_injective tailEq) i
          subst otherChildren
          rfl

/--
---
conclusion: Lax53.StructuralRepresentations.formula_structural
---
-/
theorem formula_structural_proof (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat}, formulaStructure.Laws alphabet (n := n) (m := m) :=
  fun {n m} => (formulaStructure.certified alphabet (n := n) (m := m)).checked

/--
---
conclusion: Lax53.StructuralRepresentations.tree_structural
---
-/
theorem tree_structural_proof (alphabet : RankedAlphabetCode) :
    treeStructure.Laws alphabet :=
  (treeStructure.certified alphabet).checked

/--
---
conclusion: Lax53.StructuralRepresentations.tree_lawful
---
-/
theorem tree_lawful_proof (alphabet : RankedAlphabetCode) :
    (Lax53.StructuralRepresentations.treePresentation alphabet).Lawful :=
  Lax58Proofs.StructuralPresentation.presentationOf_lawful
    (treeStructure_injective alphabet)

/--
---
conclusion: Lax53.StructuralRepresentations.sentence_lawful
---
-/
theorem sentence_lawful_proof (alphabet : RankedAlphabetCode) :
    (Lax53.StructuralRepresentations.sentencePresentation alphabet).Lawful :=
  Lax58Proofs.StructuralPresentation.presentationOf_lawful
    (formulaStructure_injective alphabet)

end Lax53Proofs.StructuralRepresentations
