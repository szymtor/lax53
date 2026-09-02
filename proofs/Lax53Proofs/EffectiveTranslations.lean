import Lax53.EffectiveTranslations
import Lax53Proofs.MSOSemantics
import Lax53Proofs.TreeAutomataToMSO

namespace Lax53Proofs.EffectiveTranslations

open Lax53.EffectiveTranslations


namespace RawFormula

/-- Derived raw connectives used by the compiler. -/
def verum : RawFormula := .neg .falsum
def and (phi psi : RawFormula) : RawFormula := .neg (.or (.neg phi) (.neg psi))
def imp (phi psi : RawFormula) : RawFormula := .or (.neg phi) psi
def allFO (phi : RawFormula) : RawFormula := .neg (.exFO (.neg phi))

def any : List RawFormula → RawFormula
  | [] => .falsum
  | phi :: rest => .or phi (any rest)

def all : List RawFormula → RawFormula
  | [] => verum
  | phi :: rest => and phi (all rest)

def anyFin : (k : Nat) → (Fin k → RawFormula) → RawFormula
  | 0, _ => .falsum
  | k + 1, f => .or (f 0) (anyFin k (fun i => f i.succ))

def allFin : (k : Nat) → (Fin k → RawFormula) → RawFormula
  | 0, _ => verum
  | k + 1, f => and (f 0) (allFin k (fun i => f i.succ))

def closeSO : Nat → RawFormula → RawFormula
  | 0, phi => phi
  | n + 1, phi => closeSO n (.exSO phi)

def labelAt (a x : Nat) : RawFormula := .label a x
def stateAt (x q : Nat) : RawFormula := .mem x q
def childAt (i x y : Nat) : RawFormula := .child i x y

end RawFormula

namespace AutomatonToMSO

open RawFormula

def validTransition (alphabet : RankedAlphabetCode) (states : Nat)
    (tr : TransitionCode) : Bool :=
  decide (tr.1 < alphabet.length ∧ tr.2.1 < states ∧
    tr.2.2.length = alphabet.getD tr.1 0 ∧
    ∀ q ∈ tr.2.2, q < states)

def transitionClause (tr : TransitionCode) : RawFormula :=
  and (labelAt tr.1 0) <| and (stateAt 0 tr.2.1) <|
    allFin tr.2.2.length fun i =>
      allFO (imp (childAt i.val 1 0) (stateAt 0 (tr.2.2.get i)))

def uniqueStateAt (states : Nat) : RawFormula :=
  and (anyFin states fun q => stateAt 0 q.val) <|
    allFin states fun q => allFin states fun r =>
      imp (and (stateAt 0 q.val) (stateAt 0 r.val))
        (if q = r then verum else .falsum)

def partition (states : Nat) : RawFormula := allFO (uniqueStateAt states)

def transitions (alphabet : RankedAlphabetCode) (M : AutomatonCode) : RawFormula :=
  allFO <| any <| (M.2.1.filter (validTransition alphabet M.1)).map transitionClause

def rootAt (alphabet : RankedAlphabetCode) : RawFormula :=
  allFin alphabet.length fun a =>
    allFin (alphabet.get a) fun i => allFO (.neg (childAt i.val 0 1))

def accepting (alphabet : RankedAlphabetCode) (M : AutomatonCode) : RawFormula :=
  allFO <| imp (rootAt alphabet) <| any <|
    (M.2.2.filter fun q => q < M.1).map (stateAt 0)

def sentence (alphabet : RankedAlphabetCode) (M : AutomatonCode) : RawFormula :=
  closeSO M.1 <| and (partition M.1) <|
    and (transitions alphabet M) (accepting alphabet M)

def compile (input : EncodedAutomaton) : EncodedSentence :=
  (input.1, sentence input.1 input.2)

theorem compile_alphabet (input : EncodedAutomaton) : (compile input).1 = input.1 := rfl

open Lax52.MSOSyntax
open Lax52.MSOSemantics
open Lax53.RankedTree
open Lax53.TreeStructure

theorem fin?_self {n : Nat} (i : Fin n) : RawFormula.fin? i.val n = some i := by
  simp [RawFormula.fin?]

theorem elaborate_verum (alphabet : RankedAlphabetCode) (n m : Nat) :
    RawFormula.elaborate alphabet n m RawFormula.verum = some Formula.verum := rfl

theorem elaborate_and (alphabet : RankedAlphabetCode) {n m : Nat}
    {p q : RawFormula} {phi psi : Formula (treeSignature alphabet.toRankedAlphabet) n m}
    (hp : RawFormula.elaborate alphabet n m p = some phi)
    (hq : RawFormula.elaborate alphabet n m q = some psi) :
    RawFormula.elaborate alphabet n m (RawFormula.and p q) = some (Formula.and phi psi) := by
  simp [RawFormula.and, RawFormula.elaborate, hp, hq, Formula.and]

theorem elaborate_imp (alphabet : RankedAlphabetCode) {n m : Nat}
    {p q : RawFormula} {phi psi : Formula (treeSignature alphabet.toRankedAlphabet) n m}
    (hp : RawFormula.elaborate alphabet n m p = some phi)
    (hq : RawFormula.elaborate alphabet n m q = some psi) :
    RawFormula.elaborate alphabet n m (RawFormula.imp p q) = some (Formula.imp phi psi) := by
  simp [RawFormula.imp, RawFormula.elaborate, hp, hq, Formula.imp]

theorem elaborate_allFO (alphabet : RankedAlphabetCode) {n m : Nat}
    {p : RawFormula} {phi : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m}
    (hp : RawFormula.elaborate alphabet (n + 1) m p = some phi) :
    RawFormula.elaborate alphabet n m (RawFormula.allFO p) = some (Formula.allFO phi) := by
  simp [RawFormula.allFO, RawFormula.elaborate, hp, Formula.allFO]

theorem elaborate_any (alphabet : RankedAlphabetCode) {n m : Nat}
    (raw : List RawFormula)
    (f : Fin raw.length → Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (h : ∀ i, RawFormula.elaborate alphabet n m (raw.get i) = some (f i)) :
    RawFormula.elaborate alphabet n m (RawFormula.any raw) =
      some (Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin raw.length f) := by
  induction raw with
  | nil => rfl
  | cons p raw ih =>
      simp only [RawFormula.any,
        Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin, RawFormula.elaborate]
      have h0 : RawFormula.elaborate alphabet n m p = some (f 0) := by
        simpa using h 0
      rw [h0]
      dsimp
      have ht := ih (fun i => f i.succ) (fun i => by simpa using h i.succ)
      rw [ht]
      rfl

theorem elaborate_any_map (alphabet : RankedAlphabetCode) {n m : Nat}
    {X : Type*} (xs : List X) (raw : X → RawFormula)
    (f : (i : Fin xs.length) →
      Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (h : ∀ i, RawFormula.elaborate alphabet n m (raw (xs.get i)) = some (f i)) :
    RawFormula.elaborate alphabet n m (RawFormula.any (xs.map raw)) =
      some (Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin xs.length f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, RawFormula.any,
        Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin, RawFormula.elaborate]
      have h0 : RawFormula.elaborate alphabet n m (raw x) = some (f 0) := by
        simpa using h (0 : Fin (xs.length + 1))
      rw [h0]
      dsimp
      have ht := ih (fun i => f i.succ) (fun i => by simpa using h i.succ)
      rw [ht]
      rfl

theorem elaborate_anyFin (alphabet : RankedAlphabetCode) {n m k : Nat}
    (raw : Fin k → RawFormula)
    (f : Fin k → Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (h : ∀ i, RawFormula.elaborate alphabet n m (raw i) = some (f i)) :
    RawFormula.elaborate alphabet n m (RawFormula.anyFin k raw) =
      some (Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin k f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [RawFormula.anyFin,
        Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin, RawFormula.elaborate]
      rw [h 0]
      dsimp
      rw [ih (fun i => raw i.succ) (fun i => f i.succ) (fun i => h i.succ)]
      rfl

theorem elaborate_allFin (alphabet : RankedAlphabetCode) {n m k : Nat}
    (raw : Fin k → RawFormula)
    (f : Fin k → Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (h : ∀ i, RawFormula.elaborate alphabet n m (raw i) = some (f i)) :
    RawFormula.elaborate alphabet n m (RawFormula.allFin k raw) =
      some (Lax53Proofs.TreeAutomataToMSO.RunFormula.allFin k f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [RawFormula.allFin,
        Lax53Proofs.TreeAutomataToMSO.RunFormula.allFin]
      apply elaborate_and alphabet (h 0)
      exact ih (fun i => raw i.succ) (fun i => f i.succ) (fun i => h i.succ)

theorem elaborate_closeSO (alphabet : RankedAlphabetCode) {m : Nat}
    {raw : RawFormula} {phi : Formula (treeSignature alphabet.toRankedAlphabet) 0 m}
    (h : RawFormula.elaborate alphabet 0 m raw = some phi) :
    RawFormula.elaborate alphabet 0 0 (RawFormula.closeSO m raw) =
      some (Lax53Proofs.TreeAutomataToMSO.RunFormula.closeSO m phi) := by
  induction m generalizing raw with
  | zero => exact h
  | succ m ih =>
      apply ih
      simp only [RawFormula.closeSO, RawFormula.elaborate]
      rw [h]
      rfl

theorem elaborate_labelAt (alphabet : RankedAlphabetCode) {n m : Nat}
    (a : Fin alphabet.length) (x : Fin n) :
    RawFormula.elaborate alphabet n m (RawFormula.labelAt a.val x.val) =
      some (Lax53Proofs.TreeAutomataToMSO.RunFormula.label a x) := by
  simp [RawFormula.labelAt, RawFormula.elaborate, fin?_self,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.label,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.var]

theorem elaborate_stateAt (alphabet : RankedAlphabetCode) {n m : Nat}
    (x : Fin n) (q : Fin m) :
    RawFormula.elaborate alphabet n m (RawFormula.stateAt x.val q.val) =
      some (Lax53Proofs.TreeAutomataToMSO.RunFormula.mem x q) := by
  simp [RawFormula.stateAt, RawFormula.elaborate, fin?_self,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.mem,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.var]

theorem elaborate_childAt (alphabet : RankedAlphabetCode) {n m : Nat}
    (i : ChildIndex alphabet.toRankedAlphabet) (x y : Fin n) :
    RawFormula.elaborate alphabet n m (RawFormula.childAt i.val x.val y.val) =
      some (Lax53Proofs.TreeAutomataToMSO.RunFormula.child i x y) := by
  simp only [RawFormula.childAt, RawFormula.elaborate, RawFormula.childIndex?]
  split
  · rename_i h
    have hi : (⟨i.val, h⟩ : ChildIndex alphabet.toRankedAlphabet) = i := Subtype.ext rfl
    simp [hi, fin?_self, Lax53Proofs.TreeAutomataToMSO.RunFormula.child,
      Lax53Proofs.TreeAutomataToMSO.RunFormula.var]
  · rename_i h
    exact False.elim (h i.property)

theorem realize_anyFin {alphabet : RankedAlphabetCode} {n m k : Nat}
    (raw : Fin k → RawFormula)
    (f : Fin k → Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (h : ∀ i, RawFormula.elaborate alphabet n m (raw i) = some (f i))
    {X : Type*} [((treeSignature alphabet.toRankedAlphabet).Structure X)]
    (v : Fin n → X) (V : Fin m → Set X) :
    Realize (Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin k f) v V ↔
      ∃ i, Realize (f i) v V :=
  Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_anyFin f v V

theorem realize_allFin {alphabet : RankedAlphabetCode} {n m k : Nat}
    (raw : Fin k → RawFormula)
    (f : Fin k → Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (h : ∀ i, RawFormula.elaborate alphabet n m (raw i) = some (f i))
    {X : Type*} [((treeSignature alphabet.toRankedAlphabet).Structure X)]
    (v : Fin n → X) (V : Fin m → Set X) :
    Realize (Lax53Proofs.TreeAutomataToMSO.RunFormula.allFin k f) v V ↔
      ∀ i, Realize (f i) v V :=
  Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_allFin f v V

/-- Canonical intrinsic formula corresponding to `uniqueStateAt`. -/
def uniqueStateFormula (alphabet : RankedAlphabetCode) (states : Nat) :
    Formula (treeSignature alphabet.toRankedAlphabet) 1 states :=
  Formula.and
    (Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin states fun q =>
      Lax53Proofs.TreeAutomataToMSO.RunFormula.mem 0 q)
    (Lax53Proofs.TreeAutomataToMSO.RunFormula.allFin states fun q =>
      Lax53Proofs.TreeAutomataToMSO.RunFormula.allFin states fun r =>
        Formula.imp
          (Formula.and
            (Lax53Proofs.TreeAutomataToMSO.RunFormula.mem 0 q)
            (Lax53Proofs.TreeAutomataToMSO.RunFormula.mem 0 r))
          (if q = r then Formula.verum else Formula.falsum))

theorem elaborate_uniqueStateAt (alphabet : RankedAlphabetCode) (states : Nat) :
    RawFormula.elaborate alphabet 1 states (uniqueStateAt states) =
      some (uniqueStateFormula alphabet states) := by
  unfold uniqueStateAt uniqueStateFormula
  apply elaborate_and alphabet
  · apply elaborate_anyFin alphabet
    intro q
    exact elaborate_stateAt alphabet 0 q
  · apply elaborate_allFin alphabet
    intro q
    apply elaborate_allFin alphabet
    intro r
    apply elaborate_imp alphabet
    · exact elaborate_and alphabet (elaborate_stateAt alphabet 0 q)
        (elaborate_stateAt alphabet 0 r)
    · by_cases hqr : q = r
      · subst r
        simp [elaborate_verum]
      · simp [hqr, RawFormula.elaborate]

theorem realize_uniqueStateFormula (alphabet : RankedAlphabetCode) (states : Nat)
    {X : Type*} [((treeSignature alphabet.toRankedAlphabet).Structure X)]
    (x : X) (V : Fin states → Set X) :
    Realize (uniqueStateFormula alphabet states) (fun _ => x) V ↔
      ∃! q : Fin states, x ∈ V q := by
  simp only [uniqueStateFormula, Lax53Proofs.MSOSemantics.realize_and,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_anyFin,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_allFin,
    Lax53Proofs.MSOSemantics.realize_imp,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_mem]
  constructor
  · rintro ⟨⟨q, hq⟩, hu⟩
    refine ⟨q, hq, ?_⟩
    intro r hr
    by_contra hne
    have := hu q r ⟨hq, hr⟩
    have hqr : q ≠ r := fun h => hne h.symm
    simp [hqr, Lax53Proofs.MSOSemantics.realize_falsum] at this
  · rintro ⟨q, hq, hu⟩
    refine ⟨⟨q, hq⟩, ?_⟩
    intro r s hrs
    have hrs' : r = s := (hu r hrs.1).trans (hu s hrs.2).symm
    subst s
    simp

structure ValidTransition (alphabet : RankedAlphabetCode) (states : Nat)
    (tr : TransitionCode) : Prop where
  symbol : tr.1 < alphabet.length
  parent : tr.2.1 < states
  arity : tr.2.2.length = alphabet.getD tr.1 0
  children : ∀ q ∈ tr.2.2, q < states

theorem ValidTransition.arity_rank {alphabet : RankedAlphabetCode} {states : Nat}
    {tr : TransitionCode} (h : ValidTransition alphabet states tr) :
    tr.2.2.length =
      alphabet.toRankedAlphabet.rank (⟨tr.1, h.symbol⟩ : Fin alphabet.length) := by
  simpa [RankedAlphabetCode.toRankedAlphabet, List.getD_eq_getElem?_getD, h.symbol]
    using h.arity

theorem validTransition_eq_true_iff (alphabet : RankedAlphabetCode) (states : Nat)
    (tr : TransitionCode) :
    validTransition alphabet states tr = true ↔ ValidTransition alphabet states tr := by
  simp only [validTransition, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hp, ha, hc⟩
    exact ⟨hs, hp, ha, hc⟩
  · rintro ⟨hs, hp, ha, hc⟩
    exact ⟨hs, hp, ha, hc⟩

def transitionClauseFormula (alphabet : RankedAlphabetCode) (states : Nat)
    (tr : TransitionCode) (h : ValidTransition alphabet states tr) :
    Formula (treeSignature alphabet.toRankedAlphabet) 1 states :=
  let a : Fin alphabet.length := ⟨tr.1, h.symbol⟩
  let q : Fin states := ⟨tr.2.1, h.parent⟩
  Formula.and (Lax53Proofs.TreeAutomataToMSO.RunFormula.label a 0) <|
    Formula.and (Lax53Proofs.TreeAutomataToMSO.RunFormula.mem 0 q) <|
      Lax53Proofs.TreeAutomataToMSO.RunFormula.allFin tr.2.2.length fun i =>
        Formula.allFO <| Formula.imp
          (Lax53Proofs.TreeAutomataToMSO.RunFormula.child
            (ChildIndex.ofSymbolIndex a ⟨i.val, by simpa [h.arity_rank] using i.isLt⟩) 1 0)
          (Lax53Proofs.TreeAutomataToMSO.RunFormula.mem 0
            ⟨tr.2.2.get i, h.children _ (List.get_mem _ i)⟩)

theorem transitionClauseFormula_congr (alphabet : RankedAlphabetCode) (states : Nat)
    {tr tr' : TransitionCode} (e : tr = tr')
    (h : ValidTransition alphabet states tr)
    (h' : ValidTransition alphabet states tr') :
    transitionClauseFormula alphabet states tr h =
      transitionClauseFormula alphabet states tr' h' := by
  subst tr'
  exact congrArg (transitionClauseFormula alphabet states tr) (Subsingleton.elim h h')

theorem elaborate_transitionClause (alphabet : RankedAlphabetCode) (states : Nat)
    (tr : TransitionCode) (h : ValidTransition alphabet states tr) :
    RawFormula.elaborate alphabet 1 states (transitionClause tr) =
      some (transitionClauseFormula alphabet states tr h) := by
  unfold transitionClause transitionClauseFormula
  apply elaborate_and alphabet (elaborate_labelAt alphabet ⟨tr.1, h.symbol⟩ 0)
  apply elaborate_and alphabet (elaborate_stateAt alphabet 0 ⟨tr.2.1, h.parent⟩)
  apply elaborate_allFin alphabet
  intro i
  apply elaborate_allFO alphabet
  apply elaborate_imp alphabet
  · let slot : ChildIndex alphabet.toRankedAlphabet :=
      ChildIndex.ofSymbolIndex (⟨tr.1, h.symbol⟩ : Fin alphabet.length)
        ⟨i.val, by simpa [h.arity_rank] using i.isLt⟩
    have hslot : slot.val = i.val := rfl
    simpa [hslot] using elaborate_childAt alphabet slot (1 : Fin 2) (0 : Fin 2)
  · exact elaborate_stateAt alphabet (0 : Fin 2)
      ⟨tr.2.2.get i, h.children _ (List.get_mem _ i)⟩

def transitionFormula (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    Formula (treeSignature alphabet.toRankedAlphabet) 0 M.1 :=
  Formula.allFO <| Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin
    (M.2.1.filter (validTransition alphabet M.1)).length fun i =>
      transitionClauseFormula alphabet M.1
        ((M.2.1.filter (validTransition alphabet M.1)).get i)
        ((validTransition_eq_true_iff alphabet M.1 _).mp <|
          List.mem_filter.mp (List.get_mem _ i) |>.2)

theorem elaborate_transitions (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    RawFormula.elaborate alphabet 0 M.1 (transitions alphabet M) =
      some (transitionFormula alphabet M) := by
  unfold transitions transitionFormula
  apply elaborate_allFO alphabet
  exact elaborate_any_map alphabet
      (M.2.1.filter (validTransition alphabet M.1)) transitionClause
      (fun i => transitionClauseFormula alphabet M.1
        ((M.2.1.filter (validTransition alphabet M.1)).get i)
        ((validTransition_eq_true_iff alphabet M.1 _).mp <|
          List.mem_filter.mp (List.get_mem _ i) |>.2))
      (fun i => by
        exact elaborate_transitionClause alphabet M.1 _
          ((validTransition_eq_true_iff alphabet M.1 _).mp <|
            List.mem_filter.mp (List.get_mem _ i) |>.2))

def rootFormula (alphabet : RankedAlphabetCode) (states : Nat) :
    Formula (treeSignature alphabet.toRankedAlphabet) 1 states :=
  Lax53Proofs.TreeAutomataToMSO.RunFormula.allFin alphabet.length fun a =>
    Lax53Proofs.TreeAutomataToMSO.RunFormula.allFin (alphabet.get a) fun i =>
      Formula.allFO <| Formula.neg <|
        Lax53Proofs.TreeAutomataToMSO.RunFormula.child
          (ChildIndex.ofSymbolIndex a i) 0 1

theorem elaborate_rootAt (alphabet : RankedAlphabetCode) (states : Nat) :
    RawFormula.elaborate alphabet 1 states (rootAt alphabet) =
      some (rootFormula alphabet states) := by
  unfold rootAt rootFormula
  apply elaborate_allFin alphabet
  intro a
  apply elaborate_allFin alphabet
  intro i
  apply elaborate_allFO alphabet
  simp only [RawFormula.elaborate]
  let slot : ChildIndex alphabet.toRankedAlphabet := ⟨i.val, ⟨a, i.isLt⟩⟩
  have hslot : slot = ChildIndex.ofSymbolIndex a i := Subtype.ext rfl
  have h := elaborate_childAt (m := states) alphabet slot (0 : Fin 2) (1 : Fin 2)
  change (do
    let phi ← RawFormula.elaborate alphabet 2 states
      (RawFormula.childAt slot.val 0 1)
    pure phi.neg) = some
      (Lax53Proofs.TreeAutomataToMSO.RunFormula.child
        (ChildIndex.ofSymbolIndex a i) 0 1).neg
  rw [← hslot]
  generalize he : RawFormula.elaborate alphabet 2 states
      (RawFormula.childAt slot.val 0 1) = o
  cases o with
  | none => simp [he] at h
  | some phi =>
      have hphi := Option.some.inj (h.symm.trans he)
      subst phi
      rfl

def acceptingFormula (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    Formula (treeSignature alphabet.toRankedAlphabet) 0 M.1 :=
  Formula.allFO <| Formula.imp (rootFormula alphabet M.1) <|
    Lax53Proofs.TreeAutomataToMSO.RunFormula.anyFin
      (M.2.2.filter fun q => q < M.1).length fun i =>
        Lax53Proofs.TreeAutomataToMSO.RunFormula.mem 0
          ⟨(M.2.2.filter fun q => q < M.1).get i,
            decide_eq_true_eq.mp (List.mem_filter.mp (List.get_mem _ i) |>.2)⟩

theorem elaborate_accepting (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    RawFormula.elaborate alphabet 0 M.1 (accepting alphabet M) =
      some (acceptingFormula alphabet M) := by
  unfold accepting acceptingFormula
  apply elaborate_allFO alphabet
  apply elaborate_imp alphabet (elaborate_rootAt alphabet M.1)
  exact elaborate_any_map alphabet
      (M.2.2.filter fun q => q < M.1) (stateAt 0)
      (fun i => Lax53Proofs.TreeAutomataToMSO.RunFormula.mem 0
        ⟨(M.2.2.filter fun q => q < M.1).get i,
          decide_eq_true_eq.mp (List.mem_filter.mp (List.get_mem _ i) |>.2)⟩)
      (fun i => by
        exact elaborate_stateAt alphabet (0 : Fin 1)
          ⟨(M.2.2.filter fun q => q < M.1).get i,
            decide_eq_true_eq.mp (List.mem_filter.mp (List.get_mem _ i) |>.2)⟩)

def bodyFormula (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    Formula (treeSignature alphabet.toRankedAlphabet) 0 M.1 :=
  Formula.and (Formula.allFO (uniqueStateFormula alphabet M.1)) <|
    Formula.and (transitionFormula alphabet M) (acceptingFormula alphabet M)

theorem elaborate_body (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    RawFormula.elaborate alphabet 0 M.1
        (RawFormula.and (partition M.1)
          (RawFormula.and (transitions alphabet M) (accepting alphabet M))) =
      some (bodyFormula alphabet M) := by
  unfold partition bodyFormula
  apply elaborate_and alphabet
  · exact elaborate_allFO alphabet (elaborate_uniqueStateAt alphabet M.1)
  · exact elaborate_and alphabet (elaborate_transitions alphabet M)
      (elaborate_accepting alphabet M)

def sentenceFormula (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    Sentence (treeSignature alphabet.toRankedAlphabet) :=
  Lax53Proofs.TreeAutomataToMSO.RunFormula.closeSO M.1 (bodyFormula alphabet M)

theorem elaborate_sentence (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    RawFormula.elaborate alphabet 0 0 (sentence alphabet M) =
      some (sentenceFormula alphabet M) := by
  unfold sentence sentenceFormula
  exact elaborate_closeSO alphabet (elaborate_body alphabet M)

def StatePartition {X : Type*} {states : Nat} (V : Fin states → Set X) : Prop :=
  ∀ x, ∃! q, x ∈ V q

theorem realize_partition (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (V : Fin M.1 → Set (Node t)) :
    @Realize _ _ (treeStructure t) _ _
        (Formula.allFO (uniqueStateFormula alphabet M.1))
        (fun i : Fin 0 => Fin.elim0 i) V ↔ StatePartition V := by
  simp only [Lax53Proofs.MSOSemantics.realize_allFO]
  constructor
  · intro h p
    have hv : consVal p (fun i : Fin 0 => Fin.elim0 i) = fun _ : Fin 1 => p := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    exact (@realize_uniqueStateFormula alphabet M.1 (Node t) (treeStructure t) p V).mp
      (hv ▸ h p)
  · intro h p
    have hv : consVal p (fun i : Fin 0 => Fin.elim0 i) = fun _ : Fin 1 => p := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    exact hv.symm ▸
      (@realize_uniqueStateFormula alphabet M.1 (Node t) (treeStructure t) p V).mpr (h p)

def TransitionCondition (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (V : Fin M.1 → Set (Node t)) : Prop :=
  ∀ p : Node t, ∃ q : Fin M.1, p ∈ V q ∧
    ∃ childStates : Fin (alphabet.toRankedAlphabet.rank p.label) → Fin M.1,
      (M.toAutomaton alphabet).transition p.label q childStates = true ∧
      ∀ i, Node.child p i ∈ V (childStates i)

theorem validTransition_of_automaton_mem (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) {a : alphabet.toRankedAlphabet.Symbol} {q : Fin M.1}
    {childStates : Fin (alphabet.toRankedAlphabet.rank a) → Fin M.1}
    {tr : TransitionCode} (htr : tr ∈ M.2.1)
    (hmatch : tr.1 = a.val ∧ tr.2.1 = q.val ∧
      tr.2.2 = List.ofFn fun i => (childStates i).val) :
    ValidTransition alphabet M.1 tr := by
  refine ⟨hmatch.1 ▸ a.isLt, hmatch.2.1 ▸ q.isLt, ?_, ?_⟩
  · rw [hmatch.2.2]
    simpa [RankedAlphabetCode.toRankedAlphabet, List.getD_eq_getElem?_getD,
      hmatch.1, a.isLt]
  · intro r hr
    rw [hmatch.2.2] at hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact (childStates i).isLt

theorem realize_transitionClauseFormula (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (tr : TransitionCode) (h : ValidTransition alphabet M.1 tr)
    (t : Tree alphabet.toRankedAlphabet) (p : Node t)
    (V : Fin M.1 → Set (Node t)) :
    @Realize _ _ (treeStructure t) _ _ (transitionClauseFormula alphabet M.1 tr h)
      (fun _ : Fin 1 => p) V ↔
      p.label.val = tr.1 ∧ p ∈ V ⟨tr.2.1, h.parent⟩ ∧
        ∀ (i : Fin tr.2.2.length) (y : Node t),
          Node.ChildAt
              (ChildIndex.ofSymbolIndex (⟨tr.1, h.symbol⟩ : Fin alphabet.length)
                ⟨i.val, by simpa [h.arity_rank] using i.isLt⟩) p y →
            y ∈ V ⟨tr.2.2.get i, h.children _ (List.get_mem _ i)⟩ := by
  simp only [transitionClauseFormula, Lax53Proofs.MSOSemantics.realize_and,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_label,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_mem,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_allFin,
    Lax53Proofs.MSOSemantics.realize_allFO,
    Lax53Proofs.MSOSemantics.realize_imp,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_child]
  constructor
  · rintro ⟨hp, hq, hc⟩
    refine ⟨congrArg Fin.val hp, hq, ?_⟩
    intro i y hy
    exact hc i y hy
  · rintro ⟨hp, hq, hc⟩
    have hp' : p.label = (⟨tr.1, h.symbol⟩ : Fin alphabet.length) := Fin.ext hp
    refine ⟨hp', hq, ?_⟩
    intro i y hy
    exact hc i y (by simpa [hp'] using hy)

theorem realize_transitionFormula (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (V : Fin M.1 → Set (Node t)) :
    @Realize _ _ (treeStructure t) _ _ (transitionFormula alphabet M)
      (fun i : Fin 0 => Fin.elim0 i) V ↔ TransitionCondition alphabet M t V := by
  simp only [transitionFormula, Lax53Proofs.MSOSemantics.realize_allFO,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_anyFin]
  constructor
  · intro h p
    obtain ⟨i, hi⟩ := h p
    let tr := (M.2.1.filter (validTransition alphabet M.1)).get i
    let hv : ValidTransition alphabet M.1 tr :=
      (validTransition_eq_true_iff alphabet M.1 tr).mp
        (List.mem_filter.mp (List.get_mem _ i)).2
    have hval : consVal p (fun i : Fin 0 => Fin.elim0 i) = fun _ : Fin 1 => p := by
      funext j
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    have hi' : @Realize _ _ (treeStructure t) _ _
        (transitionClauseFormula alphabet M.1 tr hv) (fun _ : Fin 1 => p) V := by
      simpa [tr, hv, hval] using hi
    have hclause := (realize_transitionClauseFormula alphabet M tr hv t p V).mp hi'
    let q : Fin M.1 := ⟨tr.2.1, hv.parent⟩
    let childStates : Fin (alphabet.toRankedAlphabet.rank p.label) → Fin M.1 := fun j =>
      ⟨tr.2.2.get ⟨j.val, by
        have hp : p.label.val = tr.1 := hclause.1
        have hp' : p.label = (⟨tr.1, hv.symbol⟩ : Fin alphabet.length) := Fin.ext hp
        simpa [hp', hv.arity_rank] using j.isLt⟩,
        hv.children _ (List.get_mem _ _)⟩
    refine ⟨q, hclause.2.1, childStates, ?_, ?_⟩
    · simp only [AutomatonCode.toAutomaton]
      apply List.any_eq_true.mpr
      refine ⟨tr, List.mem_of_mem_filter (List.get_mem _ i), ?_⟩
      simp only [decide_eq_true_eq]
      refine ⟨hclause.1.symm, rfl, ?_⟩
      apply List.ext_get
      · have hp' : p.label = (⟨tr.1, hv.symbol⟩ : Fin alphabet.length) :=
          Fin.ext hclause.1
        simp [childStates, hp', hv.arity_rank]
      · intro n hn₁ hn₂
        simp [childStates]
    · intro j
      let i : Fin tr.2.2.length := ⟨j.val, by
        have hp' : p.label = (⟨tr.1, hv.symbol⟩ : Fin alphabet.length) :=
          Fin.ext hclause.1
        simpa [hp', hv.arity_rank] using j.isLt⟩
      have hchild : Node.ChildAt
          (ChildIndex.ofSymbolIndex (⟨tr.1, hv.symbol⟩ : Fin alphabet.length)
            ⟨i.val, by simpa [hv.arity_rank] using i.isLt⟩)
          p (Node.child p j) := by
        have hp' : p.label = (⟨tr.1, hv.symbol⟩ : Fin alphabet.length) :=
          Fin.ext hclause.1
        simpa [hp', i] using Lax53Proofs.TreeNodes.childAt_childNode p j
      simpa [childStates, i] using hclause.2.2 i (Node.child p j) hchild
  · intro h p
    obtain ⟨q, hpq, childStates, hstep, hchildren⟩ := h p
    simp only [AutomatonCode.toAutomaton] at hstep
    obtain ⟨tr, htrmem, hmatch⟩ := List.any_eq_true.mp hstep
    simp only [decide_eq_true_eq] at hmatch
    let hv := validTransition_of_automaton_mem alphabet M htrmem hmatch
    have hvalid : validTransition alphabet M.1 tr = true :=
      (validTransition_eq_true_iff alphabet M.1 tr).mpr hv
    have htrfilter : tr ∈ M.2.1.filter (validTransition alphabet M.1) :=
      List.mem_filter.mpr ⟨htrmem, hvalid⟩
    let i : Fin (M.2.1.filter (validTransition alphabet M.1)).length :=
      ⟨(M.2.1.filter (validTransition alphabet M.1)).idxOf tr,
        List.idxOf_lt_length_of_mem htrfilter⟩
    refine ⟨i, ?_⟩
    have hget : (M.2.1.filter (validTransition alphabet M.1)).get i = tr := by
      exact List.idxOf_get (List.idxOf_lt_length_of_mem htrfilter)
    let hv' : ValidTransition alphabet M.1
        ((M.2.1.filter (validTransition alphabet M.1)).get i) :=
      (validTransition_eq_true_iff alphabet M.1 _).mp
        (List.mem_filter.mp (List.get_mem _ i)).2
    have hvEq : hv' = hget ▸ hv := Subsingleton.elim _ _
    have hgoal : @Realize _ _ (treeStructure t) _ _
        (transitionClauseFormula alphabet M.1 tr hv)
        (fun _ : Fin 1 => p) V := by
      apply (realize_transitionClauseFormula alphabet M tr hv t p V).mpr
      refine ⟨hmatch.1.symm, ?_, ?_⟩
      · simpa only [hmatch.2.1] using hpq
      · intro j y hy
        let k : Fin (alphabet.toRankedAlphabet.rank p.label) :=
          ⟨j.val, by simpa [hmatch.2.2] using j.isLt⟩
        have hp' : (⟨tr.1, hv.symbol⟩ : Fin alphabet.length) = p.label :=
          Fin.ext hmatch.1
        have hy' : Node.ChildAt (ChildIndex.ofSymbolIndex p.label k) p y := by
          simpa [hp', k] using hy
        have hey := (Lax53Proofs.TreeNodes.childAt_iff_eq_childNode p y k).mp hy'
        subst y
        have hj : tr.2.2.get j = (childStates k).val := by
          have hj? := congrArg (fun l : List Nat => l[j.val]?) hmatch.2.2
          dsimp only at hj?
          have hjleft : tr.2.2[j.val]? = some (tr.2.2.get j) :=
            List.getElem?_eq_getElem j.isLt
          rw [hjleft, List.getElem?_ofFn] at hj?
          split at hj?
          · simpa [k] using Option.some.inj hj?
          · simp at hj?
        simpa only [hj] using hchildren k
    have hvGoal : transitionClauseFormula alphabet M.1
        ((M.2.1.filter (validTransition alphabet M.1)).get i) hv' =
        transitionClauseFormula alphabet M.1 tr hv := by
      exact transitionClauseFormula_congr alphabet M.1 hget hv' hv
    have hval : consVal p (fun i : Fin 0 => Fin.elim0 i) = fun _ : Fin 1 => p := by
      funext j
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    simpa only [hvGoal, hval] using hgoal

theorem realize_rootFormula (alphabet : RankedAlphabetCode) (states : Nat)
    (t : Tree alphabet.toRankedAlphabet) (p : Node t)
    (V : Fin states → Set (Node t)) :
    @Realize _ _ (treeStructure t) _ _ (rootFormula alphabet states)
      (fun _ : Fin 1 => p) V ↔ p = Node.rootOf t := by
  simp only [rootFormula,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_allFin,
    Lax53Proofs.MSOSemantics.realize_allFO,
    Lax53Proofs.MSOSemantics.realize_neg,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_child]
  rw [← Lax53Proofs.TreeAutomataToMSO.RunFormula.isRoot_iff_eq_root t p]
  constructor
  · intro h ai i y
    let a := Lax53Proofs.TreeAutomataToMSO.RunFormula.enum
      alphabet.toRankedAlphabet.Symbol ai
    exact h a ⟨i.val, by
      change i.val < alphabet.get a
      exact i.isLt⟩ y
  · intro h a i y
    let ai := (Lax53Proofs.TreeAutomataToMSO.RunFormula.enum
      alphabet.toRankedAlphabet.Symbol).symm a
    let j : Fin (alphabet.toRankedAlphabet.rank
        (Lax53Proofs.TreeAutomataToMSO.RunFormula.enum
          alphabet.toRankedAlphabet.Symbol ai)) :=
      ⟨i.val, by
        simp only [ai, Equiv.apply_symm_apply]
        exact i.isLt⟩
    simpa [ai, j] using h ai j y

def AcceptingCondition (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (V : Fin M.1 → Set (Node t)) : Prop :=
  ∀ p, p = Node.rootOf t → ∃ q, p ∈ V q ∧ (M.toAutomaton alphabet).accept q = true

theorem realize_acceptingFormula (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (V : Fin M.1 → Set (Node t)) :
    @Realize _ _ (treeStructure t) _ _ (acceptingFormula alphabet M)
      (fun i : Fin 0 => Fin.elim0 i) V ↔ AcceptingCondition alphabet M t V := by
  simp only [acceptingFormula, Lax53Proofs.MSOSemantics.realize_allFO,
    Lax53Proofs.MSOSemantics.realize_imp,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_anyFin,
    Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_mem]
  constructor
  · intro h p hp
    have hroot : @Realize _ _ (treeStructure t) _ _ (rootFormula alphabet M.1)
        (consVal p (fun i : Fin 0 => Fin.elim0 i)) V := by
      have hv : consVal p (fun i : Fin 0 => Fin.elim0 i) = fun _ : Fin 1 => p := by
        funext i
        exact Fin.cases rfl (fun j => Fin.elim0 j) i
      exact hv.symm ▸ (realize_rootFormula alphabet M.1 t p V).mpr hp
    obtain ⟨i, hi⟩ := h p hroot
    let q : Fin M.1 :=
      ⟨(M.2.2.filter fun q => q < M.1).get i,
        decide_eq_true_eq.mp (List.mem_filter.mp (List.get_mem _ i) |>.2)⟩
    refine ⟨q, hi, ?_⟩
    simp only [AutomatonCode.toAutomaton]
    exact List.contains_iff_mem.mpr (List.mem_of_mem_filter (List.get_mem _ i))
  · intro h p hp
    have hv : consVal p (fun i : Fin 0 => Fin.elim0 i) = fun _ : Fin 1 => p := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    have hproot : p = Node.rootOf t :=
      (realize_rootFormula alphabet M.1 t p V).mp (hv ▸ hp)
    obtain ⟨q, hpq, haccept⟩ := h p hproot
    simp only [AutomatonCode.toAutomaton] at haccept
    have hqmem : q.val ∈ M.2.2.filter fun r => r < M.1 :=
      List.mem_filter.mpr ⟨List.contains_iff_mem.mp haccept, decide_eq_true_eq.mpr q.isLt⟩
    let i : Fin (M.2.2.filter fun r => r < M.1).length :=
      ⟨(M.2.2.filter fun r => r < M.1).idxOf q.val,
        List.idxOf_lt_length_of_mem hqmem⟩
    refine ⟨i, ?_⟩
    have hget : (M.2.2.filter fun r => r < M.1).get i = q.val :=
      List.idxOf_get (List.idxOf_lt_length_of_mem hqmem)
    change p ∈ V ((⟨(M.2.2.filter fun r => r < M.1).get i,
      decide_eq_true_eq.mp (List.mem_filter.mp (List.get_mem _ i)).2⟩ : Fin M.1))
    simpa only [hget] using hpq

def RunValuation (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (V : Fin M.1 → Set (Node t)) : Prop :=
  StatePartition V ∧ TransitionCondition alphabet M t V ∧
    AcceptingCondition alphabet M t V

theorem realize_bodyFormula (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (V : Fin M.1 → Set (Node t)) :
    @Realize _ _ (treeStructure t) _ _ (bodyFormula alphabet M)
      (fun i : Fin 0 => Fin.elim0 i) V ↔ RunValuation alphabet M t V := by
  simp only [bodyFormula, Lax53Proofs.MSOSemantics.realize_and,
    realize_partition, realize_transitionFormula, realize_acceptingFormula,
    RunValuation]

noncomputable def stateOf {X : Type*} {states : Nat} (V : Fin states → Set X)
    (hV : StatePartition V) (x : X) : Fin states := Classical.choose (hV x)

theorem mem_stateOf {X : Type*} {states : Nat} (V : Fin states → Set X)
    (hV : StatePartition V) (x : X) : x ∈ V (stateOf V hV x) :=
  Classical.choose_spec (hV x) |>.1

theorem eq_stateOf {X : Type*} {states : Nat} (V : Fin states → Set X)
    (hV : StatePartition V) (x : X) {q : Fin states} (hq : x ∈ V q) :
    q = stateOf V hV x := Classical.choose_spec (hV x) |>.2 q hq

theorem runValuation_iff_accepts (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) :
    (∃ V, RunValuation alphabet M t V) ↔ (M.toAutomaton alphabet).Accepts t := by
  constructor
  · rintro ⟨V, hpart, htrans, haccept⟩
    let r : Node t → Fin M.1 := stateOf V hpart
    have hlocal : Lax53Proofs.TreeAutomataToMSO.RunFormula.LocallyCompatible
        (M.toAutomaton alphabet) t r := by
      intro p
      obtain ⟨q, hpq, childStates, hstep, hchildren⟩ := htrans p
      have hq : q = r p := eq_stateOf V hpart p hpq
      have hc : childStates = fun i => r (Node.child p i) := by
        funext i
        exact eq_stateOf V hpart _ (hchildren i)
      simpa [hq, hc] using hstep
    have hroot := haccept (Node.rootOf t) rfl
    obtain ⟨q, hq, haccept⟩ := hroot
    have hqr : q = r (Node.rootOf t) := eq_stateOf V hpart _ hq
    apply (Lax53Proofs.TreeAutomataToMSO.RunFormula.exists_acceptingLabeling_iff_accepts
      (M.toAutomaton alphabet) t).mp
    exact ⟨r, hlocal, by simpa [hqr] using haccept⟩
  · intro haccept
    obtain ⟨r, hlocal, hroot⟩ :=
      (Lax53Proofs.TreeAutomataToMSO.RunFormula.exists_acceptingLabeling_iff_accepts
        (M.toAutomaton alphabet) t).mpr haccept
    let V : Fin M.1 → Set (Node t) := fun q => {p | r p = q}
    refine ⟨V, ?_, ?_, ?_⟩
    · intro p
      exact ⟨r p, rfl, fun q hq => hq.symm⟩
    · intro p
      refine ⟨r p, rfl, fun i => r (Node.child p i), hlocal p, fun i => rfl⟩
    · intro p hp
      subst p
      exact ⟨r (Node.rootOf t), rfl, hroot⟩

theorem sentenceFormula_correct (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) :
    TreeModels t (sentenceFormula alphabet M) ↔ (M.toAutomaton alphabet).Accepts t := by
  unfold sentenceFormula TreeModels
  rw [Lax53Proofs.TreeAutomataToMSO.RunFormula.realize_closeSO]
  simp only [realize_bodyFormula]
  exact runValuation_iff_accepts alphabet M t

theorem compile_language (input : EncodedAutomaton) :
    AutomatonCode.language input.1 input.2 =
      FormulaCode.language input.1 (compile input).2 := by
  ext t
  change (input.2.toAutomaton input.1).Accepts t ↔
    t ∈ FormulaCode.language input.1 (sentence input.1 input.2)
  unfold FormulaCode.language
  rw [elaborate_sentence]
  exact (sentenceFormula_correct input.1 input.2 t).symm

end AutomatonToMSO

end Lax53Proofs.EffectiveTranslations
