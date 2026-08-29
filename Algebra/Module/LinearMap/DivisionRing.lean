/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Some lemmas about linear functionals on division rings

This file proves some results on linear functionals on division semirings.

## Main results

* `LinearMap.surjective_iff_ne_zero`: a linear functional `f` is surjective iff `f ≠ 0`.
* `LinearMap.range_smulRight_apply`: for a nonzero linear functional `f` and element `x`,
  the range of `f.smulRight x` is the span of the set `{x}`.
-/

public section

namespace LinearMap
variable {R M M₁ : Type*} [AddCommMonoid M] [AddCommMonoid M₁]

/--
theorem `surjective_iff_ne_zero` / 定理 `surjective_iff_ne_zero`

English:
theorem surjective_iff_ne_zero
  given: [DivisionSemiring R] [Module R M] {f : M ->ₗ[R] R}
  proof: by
  refine ⟨ne_zero_of_surjective, fun hf z => ?_⟩
  obtain ⟨y, hy⟩ : exists y, f y != 0 := by simpa [Ne, LinearMap.ext_iff] using hf
  exact ⟨(z * (f y)⁻¹) • y, by simp [hy]⟩

protected alias ⟨_, surjective⟩ := surjective_iff_ne_zero

中文:
定理 surjective_iff_ne_zero
  条件: [DivisionSemiring R] [Module R M] {f : M ->ₗ[R] R}
  证明: by
  refine ⟨ne_zero_of_surjective, fun hf z => ?_⟩
  obtain ⟨y, hy⟩ : exists y, f y != 0 := by simpa [Ne, LinearMap.ext_iff] using hf
  exact ⟨(z * (f y)⁻¹) • y, by simp [hy]⟩

protected alias ⟨_, surjective⟩ := surjective_iff_ne_zero

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ext_iff, ne_zero_of_surjective
-/
theorem surjective_iff_ne_zero [DivisionSemiring R] [Module R M] {f : M ->ₗ[R] R} :
    Function.Surjective f ↔ f != 0 := by
  refine ⟨ne_zero_of_surjective, fun hf z => ?_⟩
  obtain ⟨y, hy⟩ : exists y, f y != 0 := by simpa [Ne, LinearMap.ext_iff] using hf
  exact ⟨(z * (f y)⁻¹) • y, by simp [hy]⟩

protected alias ⟨_, surjective⟩ := surjective_iff_ne_zero

/--
theorem `range_smulRight_apply_of_surjective` / 定理 `range_smulRight_apply_of_surjective`

English:
theorem range_smulRight_apply_of_surjective
  statement: [Semiring R] [Module R M] [Module R M₁]
  proof: Submodule.ext fun z => by
  simp_rw [mem_range, smulRight_apply, Submodule.mem_span_singleton]
  refine ⟨fun ⟨w, hw⟩ => ⟨f w, hw ▸ rfl⟩, fun ⟨w, hw⟩ => ?_⟩
  obtain ⟨y, rfl⟩ := hf w
  exact ⟨y, hw⟩

中文:
定理 range_smulRight_apply_of_surjective
  结论: [Semiring R] [Module R M] [Module R M₁]
  证明: Submodule.ext fun z => by
  simp_rw [mem_range, smulRight_apply, Submodule.mem_span_singleton]
  refine ⟨fun ⟨w, hw⟩ => ⟨f w, hw ▸ rfl⟩, fun ⟨w, hw⟩ => ?_⟩
  obtain ⟨y, rfl⟩ := hf w
  exact ⟨y, hw⟩

Depends on / 依赖: Submodule, Submodule.ext, Submodule.mem_span_singleton, mem_range, mem_span_singleton, simp_rw, smulRight_apply
-/
theorem range_smulRight_apply_of_surjective [Semiring R] [Module R M] [Module R M₁]
    {f : M ->ₗ[R] R} (hf : Function.Surjective f) (x : M₁) :
    range (f.smulRight x) = Submodule.span R {x} := Submodule.ext fun z => by
  simp_rw [mem_range, smulRight_apply, Submodule.mem_span_singleton]
  refine ⟨fun ⟨w, hw⟩ => ⟨f w, hw ▸ rfl⟩, fun ⟨w, hw⟩ => ?_⟩
  obtain ⟨y, rfl⟩ := hf w
  exact ⟨y, hw⟩

/--
theorem `range_smulRight_apply` / 定理 `range_smulRight_apply`

English:
theorem range_smulRight_apply
  statement: [DivisionSemiring R] [Module R M] [Module R M₁]
  proof: range_smulRight_apply_of_surjective (f.surjective hf) x

中文:
定理 range_smulRight_apply
  结论: [DivisionSemiring R] [Module R M] [Module R M₁]
  证明: range_smulRight_apply_of_surjective (f.surjective hf) x

Depends on / 依赖: f.surjective, range_smulRight_apply_of_surjective, surjective
-/
theorem range_smulRight_apply [DivisionSemiring R] [Module R M] [Module R M₁]
    {f : M ->ₗ[R] R} (hf : f != 0) (x : M₁) :
    range (f.smulRight x) = Submodule.span R {x} :=
  range_smulRight_apply_of_surjective (f.surjective hf) x

end LinearMap
