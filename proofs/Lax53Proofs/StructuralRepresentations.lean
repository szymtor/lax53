import Lax53.StructuralRepresentations

namespace Lax53Proofs.StructuralRepresentations

open Lax53.RankedTree
open Lax53.EffectiveTranslations
open Lax53.StructuralRepresentations
open Lax58.StructuralPresentation
open Lax58.StructuralPresentation.Presentation
open Lax58.StructuralCombinators

universe u

private theorem presentationOf_lawful {α : Type u} {f : α → Raw}
    (hf : Function.Injective f) : (presentationOf f).Lawful := by
  intro x
  classical
  simp only [presentationOf]
  split
  next h =>
    apply congrArg some
    apply hf
    exact Classical.choose_spec h
  next h => exact False.elim (h ⟨x, rfl⟩)

private theorem formulaRaw_injective : Function.Injective formulaRaw := by
  intro phi
  induction phi with
  | falsum =>
      intro other h
      cases other <;>
        simp_all [formulaRaw, Raw.constructor, Raw.fields, Lax58.StructuralCombinators.nat]
  | equal x y =>
      intro other h
      cases other <;>
        simp_all [formulaRaw, Raw.constructor, Raw.fields, Lax58.StructuralCombinators.nat]
  | label symbol x =>
      intro other h
      cases other <;>
        simp_all [formulaRaw, Raw.constructor, Raw.fields, Lax58.StructuralCombinators.nat]
  | child slot x y =>
      intro other h
      cases other <;>
        simp_all [formulaRaw, Raw.constructor, Raw.fields, Lax58.StructuralCombinators.nat]
  | mem x X =>
      intro other h
      cases other <;>
        simp_all [formulaRaw, Raw.constructor, Raw.fields, Lax58.StructuralCombinators.nat]
  | or phi psi ihPhi ihPsi =>
      intro other h
      cases other <;>
        simp [formulaRaw, Raw.constructor, Raw.fields, Lax58.StructuralCombinators.nat] at h ⊢
      exact ⟨ihPhi h.1, ihPsi h.2⟩
  | neg phi ih =>
      intro other h
      cases other <;>
        simp [formulaRaw, Raw.constructor, Raw.fields, Lax58.StructuralCombinators.nat] at h ⊢
      exact ih h
  | exFO phi ih =>
      intro other h
      cases other <;>
        simp [formulaRaw, Raw.constructor, Raw.fields, Lax58.StructuralCombinators.nat] at h ⊢
      exact ih h
  | exSO phi ih =>
      intro other h
      cases other <;>
        simp [formulaRaw, Raw.constructor, Raw.fields, Lax58.StructuralCombinators.nat] at h ⊢
      exact ih h

private theorem fields_injective : Function.Injective Raw.fields := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys => simp [Raw.fields] at h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp [Raw.fields] at h
      | cons y ys =>
          simp only [Raw.fields, Raw.pair.injEq] at h
          exact congrArg₂ List.cons h.1 (ih h.2)

private theorem treeRaw_injective (alphabet : RankedAlphabetCode) :
    Function.Injective (treeRaw alphabet) := by
  intro t
  induction t with
  | node symbol children ih =>
      intro other h
      cases other with
      | node otherSymbol otherChildren =>
          simp only [treeRaw, Raw.constructor, Raw.pair.injEq] at h
          have listEq := fields_injective h.2
          have symbolValEq : symbol.val = otherSymbol.val := by
            have headOptionEq := congrArg List.head? listEq
            simp only [List.head?_cons, Option.some.injEq] at headOptionEq
            change Raw.nat symbol.val = Raw.nat otherSymbol.val at headOptionEq
            injection headOptionEq
          have tailEq :
              List.ofFn (fun i => treeRaw alphabet (children i)) =
                List.ofFn (fun i => treeRaw alphabet (otherChildren i)) := by
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

private theorem codeWitness : CodeCertificates := by
  let laws : Lax58.StructuralCombinators.Lawful.{0, 0} := lawful
  have hNat := laws.nat
  have hListNat := laws.list nat hNat
  have hTransition := laws.prod nat (prod nat (list nat)) hNat
    (laws.prod nat (list nat) hNat hListNat)
  have hAutomatonBody := laws.prod nat (prod (list transition) (list nat)) hNat
    (laws.prod (list transition) (list nat) (laws.list transition hTransition) hListNat)
  exact {
    rankedAlphabet := hListNat
    transition := hTransition
    automatonBody := hAutomatonBody
    automaton := laws.prod rankedAlphabet automatonBody hListNat hAutomatonBody
  }

private theorem formulaWitness : FormulaCertificate where
  lawful := presentationOf_lawful formulaRaw_injective
  sentenceLawful := by
    let laws : Lax58.StructuralCombinators.Lawful.{0, 0} := lawful
    exact laws.prod rankedAlphabet formula (laws.list nat laws.nat)
      (presentationOf_lawful formulaRaw_injective)
  falsum := rfl
  equal := by intros; rfl
  label := by intros; rfl
  child := by intros; rfl
  mem := by intros; rfl
  or := by intros; rfl
  neg := by intros; rfl
  exFO := by intros; rfl
  exSO := by intros; rfl

private theorem treeWitness : TreeCertificate where
  lawful := by
    intro alphabet
    exact presentationOf_lawful (treeRaw_injective alphabet)
  node := by intros; rfl

/--
---
conclusion: Lax53.StructuralRepresentations.codeCertificates
---
-/
theorem code_certificates_proof : CodeCertificates := codeWitness

/--
---
conclusion: Lax53.StructuralRepresentations.formulaCertificate
---
-/
theorem formula_certificate_proof : FormulaCertificate := formulaWitness

/--
---
conclusion: Lax53.StructuralRepresentations.treeCertificate
---
-/
theorem tree_certificate_proof : TreeCertificate := treeWitness

end Lax53Proofs.StructuralRepresentations
