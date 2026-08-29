/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Infinite sums and products in topological fields

Lemmas on topological sums in rings with a strictly multiplicative norm, of which normed fields are
the most familiar examples.
-/

public section


section NormMulClass

variable {α E : Type*} [SeminormedCommRing E] [NormMulClass E] [NormOneClass E]
  {f : α -> E} {x : E}

nonrec theorem HasProd.norm (hfx : HasProd f x) : HasProd (‖f ·‖) ‖x‖ := by
  simp only [HasProd, ← norm_prod]
  exact hfx.norm

/--
theorem `Multipliable.norm` / 定理 `Multipliable.norm`

English:
theorem Multipliable.norm
  given: (hf : Multipliable f)
  statement: Multipliable (‖f ·‖)
  proof: let ⟨x, hx⟩ := hf; ⟨‖x‖, hx.norm⟩

中文:
定理 Multipliable.norm
  条件: (hf : Multipliable f)
  结论: Multipliable (‖f ·‖)
  证明: let ⟨x, hx⟩ := hf; ⟨‖x‖, hx.norm⟩

Depends on / 依赖: hx.norm
-/
theorem Multipliable.norm (hf : Multipliable f) : Multipliable (‖f ·‖) :=
  let ⟨x, hx⟩ := hf; ⟨‖x‖, hx.norm⟩

/--
theorem `Multipliable.norm_tprod` / 定理 `Multipliable.norm_tprod`

English:
theorem Multipliable.norm_tprod
  given: (hf : Multipliable f)
  statement: ‖∏' i, f i‖ = ∏' i, ‖f i‖
  proof: hf.hasProd.norm.tprod_eq.symm

中文:
定理 Multipliable.norm_tprod
  条件: (hf : Multipliable f)
  结论: ‖∏' i, f i‖ = ∏' i, ‖f i‖
  证明: hf.hasProd.norm.tprod_eq.symm
-/
protected theorem Multipliable.norm_tprod (hf : Multipliable f) : ‖∏' i, f i‖ = ∏' i, ‖f i‖ :=
  hf.hasProd.norm.tprod_eq.symm

end NormMulClass
