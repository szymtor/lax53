import Mathlib.Computability.Primrec.Basic

/-!
A finite, oracle-free program for each primitive-recursive function.

This is the semantic front end of the reusable RAM realization bridge. It
reuses the exact pairing and decoding conventions of the existing `Primrec`
proofs. Its evaluator is a specification, not a free machine instruction:
the RAM back end must implement every constructor, including pairing,
unpairing, and primitive recursion, and charge its execution.

The numeric encoding here is proof-private intermediate data. In particular,
this module does not change or add to the certified public input convention.
-/

namespace Lax842588Proofs.PrimitiveRecursiveCode

/-- A finite program has only the seven primitive-recursive constructors;
there is no constructor for an arbitrary Lean function or external oracle. -/
inductive Code where
  | zero
  | succ
  | left
  | right
  | pair (f g : Code)
  | comp (f g : Code)
  | prec (initial step : Code)
  deriving DecidableEq, Repr

/-- Pure semantics of the code; the recursion bound is part of the input. -/
def Code.eval : Code → Nat → Nat
  | .zero, _ => 0
  | .succ, n => n + 1
  | .left, n => n.unpair.1
  | .right, n => n.unpair.2
  | .pair f g, n => Nat.pair (f.eval n) (g.eval n)
  | .comp f g, n => f.eval (g.eval n)
  | .prec initial step, n =>
      Nat.rec (initial.eval n.unpair.1)
        (fun k acc => step.eval (Nat.pair n.unpair.1 (Nat.pair k acc)))
        n.unpair.2

/-- Every code denotes a primitive-recursive function, with precisely the
same pairing convention as Mathlib's existing computability proofs. -/
theorem Code.primrec (c : Code) : Nat.Primrec c.eval := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | pair f g hf hg => exact .pair hf hg
  | comp f g hf hg =>
      exact Nat.Primrec.comp (f := f.eval) (g := g.eval) hf hg
  | prec initial step hi hs => exact .prec hi hs

/-- A primitive-recursiveness proof supplies the existence of a finite
program. No function-valued instruction is added to obtain this result. -/
theorem exists_code {f : Nat → Nat} (hf : Nat.Primrec f) :
    ∃ c : Code, c.eval = f := by
  induction hf with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | pair hf hg ihf ihg =>
      obtain ⟨cf, hcf⟩ := ihf
      obtain ⟨cg, hcg⟩ := ihg
      exact ⟨.pair cf cg, by funext n; simp [Code.eval, hcf, hcg]⟩
  | comp hf hg ihf ihg =>
      obtain ⟨cf, hcf⟩ := ihf
      obtain ⟨cg, hcg⟩ := ihg
      exact ⟨.comp cf cg, by funext n; simp [Code.eval, hcf, hcg]⟩
  | prec hi hs ihi ihs =>
      obtain ⟨ci, hci⟩ := ihi
      obtain ⟨cs, hcs⟩ := ihs
      exact ⟨.prec ci cs, by funext n; simp [Code.eval, hci, hcs]⟩

/-- The typed bridge states exactly what the inherited numeric convention
computes, including the `Option` tag for invalid encodings. It makes no
claim that the public RAM input is already encoded as this natural number. -/
theorem exists_typed_code {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} (hf : Primrec f) :
    ∃ c : Code, ∀ n : Nat,
      c.eval n = Encodable.encode ((Encodable.decode (α := α) n).map f) := by
  obtain ⟨c, hc⟩ := exists_code hf
  exact ⟨c, congrFun hc⟩

/-- On a valid input the scalar evaluator returns the tagged output encoding.
The caller must still construct this intermediate encoding at runtime. -/
theorem typed_code_on_value {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} {c : Code}
    (hc : ∀ n : Nat,
      c.eval n = Encodable.encode ((Encodable.decode (α := α) n).map f))
    (a : α) :
    c.eval (Encodable.encode a) = Encodable.encode (some (f a)) := by
  rw [hc]
  simp

end Lax842588Proofs.PrimitiveRecursiveCode
