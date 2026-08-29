/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# A multiple tensor product of finitely generated modules is finitely generated

-/

public section

open TensorProduct

namespace PiTensorProduct

/--
Instance `finite` / 实例 `finite`

English:
instance finite
  signature: {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
  body: by
  choose n γ hg using fun i => Module.Finite.exists_fin (R := R) (M := M i)
  rw [Module.finite_def]; rw [← submodule_span_eq_top hg]
  exact Submodule.fg_span (Set.finite_range _)

中文:
实例 finite
  签名: {R : 类型} [交换环 R] {ι : 类型} [有限 ι]
  定义体: by
  choose n γ hg using fun i => Module.Finite.exists_fin (R := R) (M := M i)
  rw [Module.finite_def]; rw [← submodule_span_eq_top hg]
  exact Submodule.fg_span (Set.finite_range _)

Depends on / 依赖: Finite, Module, Module.Finite.exists_fin, Module.finite_def, Set.finite_range, Submodule, Submodule.fg_span, exists_fin, fg_span, finite_def, finite_range, submodule_span_eq_top
-/
instance finite {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    {M : ι -> Type*} [forall i, AddCommGroup (M i)] [forall i, Module R (M i)]
    [forall i, Module.Finite R (M i)] :
    Module.Finite R (⨂[R] i, M i) := by
  choose n γ hg using fun i => Module.Finite.exists_fin (R := R) (M := M i)
  rw [Module.finite_def]; rw [← submodule_span_eq_top hg]
  exact Submodule.fg_span (Set.finite_range _)

end PiTensorProduct
