import Lax53Proofs.EncodedAutomataOperations

namespace Lax53Proofs.EncodedAutomataComputability

open Lax53.EffectiveTranslations
open Lax53Proofs.EncodedAutomataOperations
open Lax53Proofs.FiniteAutomatonEncoding

/-- Sparse transition lookup is primitive recursive on the public numeric
automaton representation. -/
theorem step_prim : Primrec fun p : AutomatonCode × Nat × Nat × List Nat =>
    step p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold step
  have hrel : PrimrecRel fun (tr : TransitionCode)
      (ctx : Nat × Nat × List Nat) => tr = (ctx.1, ctx.2.1, ctx.2.2) := by
    exact Primrec.eq.comp Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      |>.primrecRel
  have hlist : Primrec fun p : AutomatonCode × Nat × Nat × List Nat => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hctx : Primrec fun p : AutomatonCode × Nat × Nat × List Nat =>
      (p.2.1, p.2.2.1, p.2.2.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact hrel.exists_mem_list.decide.comp hlist hctx
    |>.of_eq fun p => by
      apply Bool.eq_iff_iff.mpr
      simp

/-- Accepting-state lookup is primitive recursive. -/
theorem accepting_prim : Primrec₂ accepting := by
  unfold accepting
  have h := PrimrecRel.exists_mem_list (R := fun q r : Nat => q = r)
    Primrec.eq.primrecRel
  exact h.decide.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    |>.to₂.of_eq fun M q => by
      apply Bool.eq_iff_iff.mpr
      simp

private abbrev InterInput :=
  RankedAlphabetCode × AutomatonCode × AutomatonCode

private def interTransition (x : InterInput) (a q : Nat)
    (children : List Nat) : Bool :=
  step x.2.1 a (q / x.2.2.1) (children.map fun s => s / x.2.2.1) &&
    step x.2.2 a (q % x.2.2.1) (children.map fun s => s % x.2.2.1)

private def interAccept (x : InterInput) (q : Nat) : Bool :=
  accepting x.2.1 (q / x.2.2.1) &&
    accepting x.2.2 (q % x.2.2.1)

private theorem interTransition_prim : Primrec fun
    p : InterInput × Nat × Nat × List Nat =>
      interTransition p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  let hX : Primrec fun p : InterInput × Nat × Nat × List Nat => p.1 := Primrec.fst
  let hM : Primrec fun p : InterInput × Nat × Nat × List Nat => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp hX)
  let hN : Primrec fun p : InterInput × Nat × Nat × List Nat => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp hX)
  let hNstates : Primrec fun p : InterInput × Nat × Nat × List Nat => p.1.2.2.1 :=
    Primrec.fst.comp hN
  let ha : Primrec fun p : InterInput × Nat × Nat × List Nat => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  let hq : Primrec fun p : InterInput × Nat × Nat × List Nat => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let hc : Primrec fun p : InterInput × Nat × Nat × List Nat => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hdiv : Primrec fun p : InterInput × Nat × Nat × List Nat =>
      p.2.2.1 / p.1.2.2.1 := Primrec.nat_div.comp hq hNstates
  have hmod : Primrec fun p : InterInput × Nat × Nat × List Nat =>
      p.2.2.1 % p.1.2.2.1 := Primrec.nat_mod.comp hq hNstates
  have hmapDiv : Primrec fun p : InterInput × Nat × Nat × List Nat =>
      p.2.2.2.map fun s => s / p.1.2.2.1 := by
    exact Primrec.list_map hc <|
      Primrec.nat_div.comp₂ Primrec₂.right
        (hNstates.comp Primrec.fst |>.to₂)
  have hmapMod : Primrec fun p : InterInput × Nat × Nat × List Nat =>
      p.2.2.2.map fun s => s % p.1.2.2.1 := by
    exact Primrec.list_map hc <|
      Primrec.nat_mod.comp₂ Primrec₂.right
        (hNstates.comp Primrec.fst |>.to₂)
  unfold interTransition
  apply Primrec.and.comp
  · exact step_prim.comp (Primrec.pair hM (Primrec.pair ha (Primrec.pair hdiv hmapDiv)))
  · exact step_prim.comp (Primrec.pair hN (Primrec.pair ha (Primrec.pair hmod hmapMod)))

private theorem interAccept_prim : Primrec fun p : InterInput × Nat =>
    interAccept p.1 p.2 := by
  let hX : Primrec fun p : InterInput × Nat => p.1 := Primrec.fst
  let hM : Primrec fun p : InterInput × Nat => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp hX)
  let hN : Primrec fun p : InterInput × Nat => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp hX)
  let hNstates : Primrec fun p : InterInput × Nat => p.1.2.2.1 :=
    Primrec.fst.comp hN
  let hq : Primrec fun p : InterInput × Nat => p.2 := Primrec.snd
  unfold interAccept
  apply Primrec.and.comp
  · exact accepting_prim.comp hM (Primrec.nat_div.comp hq hNstates)
  · exact accepting_prim.comp hN (Primrec.nat_mod.comp hq hNstates)

/-- Synchronous intersection is primitive recursive uniformly in the ranked
alphabet and both encoded automata. -/
theorem inter_prim : Primrec fun x : InterInput => inter x.1 x.2.1 x.2.2 := by
  change Primrec fun x : InterInput =>
    encode x.1 (x.2.1.1 * x.2.2.1) (interTransition x) (interAccept x)
  apply encode_prim (fun x : InterInput => x.1)
    (fun x : InterInput => x.2.1.1 * x.2.2.1)
    interTransition interAccept
  · exact Primrec.fst
  · exact Primrec.nat_mul.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))
  · exact interTransition_prim
  · exact interAccept_prim

/-- Existential projection is primitive recursive whenever the target rank
word, source-fiber enumeration, and source automaton are primitive recursive. -/
theorem project_prim {X : Type*} [Primcodable X]
    (target : X → RankedAlphabetCode) (sourceOf : X → Nat → List Nat)
    (M : X → AutomatonCode)
    (htarget : Primrec target)
    (hsourceOf : Primrec fun p : X × Nat => sourceOf p.1 p.2)
    (hM : Primrec M) :
    Primrec fun x => project (target x) (sourceOf x) (M x) := by
  let transition (x : X) (a q : Nat) (children : List Nat) : Bool :=
    (sourceOf x a).any fun source => step (M x) source q children
  let accept (x : X) (q : Nat) : Bool := accepting (M x) q
  change Primrec fun x => encode (target x) (M x).1 (transition x) (accept x)
  apply encode_prim target (fun x => (M x).1) transition accept htarget
    (Primrec.fst.comp hM)
  · let P := X × Nat × Nat × List Nat
    have hrel : PrimrecRel fun (source : Nat) (p : P) =>
        step (M p.1) source p.2.2.1 p.2.2.2 = true := by
      exact (Primrec.eq.comp
        (step_prim.comp <| Primrec.pair
          (hM.comp (Primrec.fst.comp Primrec.snd)) <|
          Primrec.pair Primrec.fst <|
            Primrec.pair
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.const true)).primrecRel
    have hlist : Primrec fun p : P => sourceOf p.1 p.2.1 :=
      hsourceOf.comp <| Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
    exact hrel.exists_mem_list.decide.comp hlist Primrec.id
      |>.of_eq fun p => by
        apply Bool.eq_iff_iff.mpr
        simp [transition]
  · exact accepting_prim.comp (hM.comp Primrec.fst) Primrec.snd

/-- Pullback along a numeric symbol map is primitive recursive. -/
theorem pullback_prim {X : Type*} [Primcodable X]
    (source : X → RankedAlphabetCode) (symbolMap : X → Nat → Nat)
    (M : X → AutomatonCode)
    (hsource : Primrec source)
    (hsymbolMap : Primrec fun p : X × Nat => symbolMap p.1 p.2)
    (hM : Primrec M) :
    Primrec fun x => pullback (source x) (symbolMap x) (M x) := by
  let transition (x : X) (a q : Nat) (children : List Nat) : Bool :=
    step (M x) (symbolMap x a) q children
  let accept (x : X) (q : Nat) : Bool := accepting (M x) q
  change Primrec fun x => encode (source x) (M x).1 (transition x) (accept x)
  apply encode_prim source (fun x => (M x).1) transition accept hsource
    (Primrec.fst.comp hM)
  · exact step_prim.comp <| Primrec.pair
      (hM.comp Primrec.fst) <|
      Primrec.pair
        (hsymbolMap.comp <| Primrec.pair Primrec.fst
          (Primrec.fst.comp Primrec.snd)) <|
        Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  · exact accepting_prim.comp (hM.comp Primrec.fst) Primrec.snd

end Lax53Proofs.EncodedAutomataComputability
