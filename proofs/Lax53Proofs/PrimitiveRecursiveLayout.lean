import Lax53Proofs.PrimitiveRecursiveCompile

/-! Finite memory layouts for generated primitive-recursive programs. -/

namespace Lax53Proofs.PrimitiveRecursiveCompile

open Lax13Proofs.Imp Lax13Proofs.Compile
open Lax53Proofs.PrimitiveRecursiveCode Lax53Proofs.PrimitiveRecursivePairing

/-- A deliberately loose, input-independent count of scalar registers. -/
def space : Code → Nat
  | .zero | .succ | .left | .right => 3
  | .pair f g | .comp f g | .prec f g => space f + space g + 6

theorem space_ge_three (c : Code) : 3 ≤ space c := by cases c <;> simp [space] <;> omega

theorem compile_ok (c : Code) (d : Nat) (L : Layout) (ht : 5 ≤ L.temps)
    (hvars : ∀ j, j < d + space c → reg j ∈ L.scalars) : Com.Ok L (compile c d) := by
  induction c generalizing d with
  | zero => simpa [compile, Com.Ok, Expr.Ok] using hvars d (by simp [space])
  | succ =>
      have h0 := hvars d (by simp [space])
      simp [compile, Com.Ok, Expr.Ok, h0]
      omega
  | left =>
      have h0 := hvars d (by simp [space])
      have h1 := hvars (d + 1) (by simp [space])
      have h2 := hvars (d + 2) (by simp [space])
      simp [compile, unpairLeftProgram, sqrtProgram, sqrtLoop, sqrtStep, sqrtCond,
        oddExpr, Com.Ok, Cond.Ok, Expr.Ok, condExpr, h0, h1, h2]
      omega
  | right =>
      have h0 := hvars d (by simp [space])
      have h1 := hvars (d + 1) (by simp [space])
      have h2 := hvars (d + 2) (by simp [space])
      simp [compile, unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep, sqrtCond,
        oddExpr, Com.Ok, Cond.Ok, Expr.Ok, condExpr, h0, h1, h2]
      omega
  | pair f g hf hg =>
      have hf' := hf (d + 1) (fun j hj => hvars j (by simp only [space]; omega))
      have hg' := hg (d + 2) (fun j hj => hvars j (by simp only [space]; omega))
      have h0 := hvars d (by simp [space])
      have h1 := hvars (d + 1) (by simp [space])
      have h2 := hvars (d + 2) (by simp [space])
      simp [compile, copy, pairProgram, Com.Ok, Cond.Ok, Expr.Ok, condExpr,
        hf', hg', h0, h1, h2]
      omega
  | comp f g hf hg =>
      exact ⟨hg d (fun j hj => hvars j (by simp only [space]; omega)),
        hf d (fun j hj => hvars j (by simp only [space]; omega))⟩
  | prec initial step hi hs =>
      have hi' := hi (d + 4) (fun j hj => hvars j (by simp only [space]; omega))
      have hs' := hs (d + 5) (fun j hj => hvars j (by simp only [space]; omega))
      have h0 := hvars d (by simp [space])
      have h1 := hvars (d + 1) (by simp [space])
      have h2 := hvars (d + 2) (by simp [space])
      have h3 := hvars (d + 3) (by simp [space])
      have h4 := hvars (d + 4) (by simp [space])
      have h5 := hvars (d + 5) (by simp [space])
      simp [compile, copy, recursionStep, pairProgram, unpairLeftProgram, unpairRightProgram,
        sqrtProgram, sqrtLoop, sqrtStep, sqrtCond, oddExpr, Com.Ok, Cond.Ok, Expr.Ok,
        condExpr, hi', hs', h0, h1, h2, h3, h4, h5]
      omega

def layout (c : Code) : Layout where
  scalars := (List.range (space c)).map reg
  arrays := []
  temps := 5

theorem layout_ok (c : Code) : Com.Ok (layout c) (compile c 0) := by
  apply compile_ok c 0 (layout c) (by simp [layout])
  intro j hj
  simp only [layout, List.mem_map]
  exact ⟨j, List.mem_range.mpr (by simpa using hj), rfl⟩

@[simp] theorem layout_span (c : Code) (B : Nat) : (layout c).span B = 7 + space c := by
  simp [layout, Layout.span]

end Lax53Proofs.PrimitiveRecursiveCompile
