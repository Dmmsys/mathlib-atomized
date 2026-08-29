/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Ring.Action.Pointwise.Set

/-!
# Homeomorphism between a normed space and sphere times `(0, +∞)`

In this file we define a homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) r × Set.Ioi (0 : ℝ)`, `r > 0`.
One may think about it as generalization of polar coordinates to any normed space.

We also specialize this definition to the case `r = 1` and prove
-/

@[expose] public section

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]

open Filter Set Metric
open scoped Pointwise Set.Notation Topology

/-- The natural homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) r × Set.Ioi (0 : ℝ)`, `0 < r`.

The forward map sends `⟨x, hx⟩` to `⟨r • ‖x‖⁻¹ • x, ‖x‖ / r⟩`,
the inverse map sends `(x, r)` to `r • x`.

In the case of the unit sphere `r = `,
one may think about it as generalization of polar coordinates to any normed space. -/
@[simps apply_fst_coe apply_snd_coe symm_apply_coe]
/--
Definition of `homeomorphSphereProd` / `homeomorphSphereProd` 的定义

English:
definition homeomorphSphereProd
  signature: (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
  body: have : 0 < ‖(x : E)‖ := by simpa [-Subtype.coe_prop] using x.2
    (⟨r • ‖x.1‖⁻¹ • x.1, by simp [norm_smul, abs_of_pos hr, this.ne']⟩,
      ⟨‖x.1‖ / r, by rw [mem_Ioi]; positivity⟩)
  invFun x := ⟨x.2.1 • x.1.1, smul_ne_zero x.2.2.out.ne' (ne_of_mem_sphere x.1.2 hr.ne')⟩
  left_inv
  | ⟨x, hx⟩ => b

中文:
定义 homeomorphSphereProd
  签名: (E : 类型) [NormedAddCommGroup E] [NormedSpace 实数 E]
  定义体: have : 0 < ‖(x : E)‖ := by simpa [-Subtype.coe_prop] using x.2
    (⟨r • ‖x.1‖⁻¹ • x.1, by simp [norm_smul, abs_of_pos hr, this.ne']⟩,
      ⟨‖x.1‖ / r, by rw [mem_Ioi]; positivity⟩)
  invFun x := ⟨x.2.1 • x.1.1, smul_ne_zero x.2.2.out.ne' (ne_of_mem_sphere x.1.2 hr.ne')⟩
  left_inv
  | ⟨x, hx⟩ => b

Depends on / 依赖: Subtype, Subtype.coe_prop, abs_of_pos, coe_prop, hr.ne, invFun, left_inv, mem_Ioi, mem_sphere_zero_iff_norm, ne_of_mem_sphere, norm_smul, out.ne, right_inv, smul_ne_zero, smul_smul, this.ne
-/
noncomputable def homeomorphSphereProd (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    (r : Real) (hr : 0 < r) :
    ({0}ᶜ : Set E) ≃ₜ (sphere (0 : E) r × Ioi (0 : Real)) where
  toFun x :=
    have : 0 < ‖(x : E)‖ := by simpa [-Subtype.coe_prop] using x.2
    (⟨r • ‖x.1‖⁻¹ • x.1, by simp [norm_smul, abs_of_pos hr, this.ne']⟩,
      ⟨‖x.1‖ / r, by rw [mem_Ioi]; positivity⟩)
  invFun x := ⟨x.2.1 • x.1.1, smul_ne_zero x.2.2.out.ne' (ne_of_mem_sphere x.1.2 hr.ne')⟩
  left_inv
  | ⟨x, hx⟩ => by
    have : 0 < ‖x‖ := by simpa using hx
    ext; simp only [smul_smul]; field_simp; simp
  right_inv
  | (⟨x, hx⟩, ⟨d, hd⟩) => by
    rw [mem_Ioi] at hd
    rw [mem_sphere_zero_iff_norm] at hx
    simp (disch := positivity) [norm_smul, smul_smul, abs_of_pos hd, hx]
  continuous_toFun := by
    simp only
    fun_prop (disch := simp)

/-- The natural homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)`.

The forward map sends `⟨x, hx⟩` to `⟨‖x‖⁻¹ • x, ‖x‖⟩`,
the inverse map sends `(x, r)` to `r • x`.

One may think about it as generalization of polar coordinates to any normed space.
See also `homeomorphSphereProd` for a version that works for a sphere of any positive radius. -/
@[simps! apply_fst_coe apply_snd_coe symm_apply_coe]
/--
Definition of `homeomorphUnitSphereProd` / `homeomorphUnitSphereProd` 的定义

English:
definition homeomorphUnitSphereProd
  signature: :
  body: homeomorphSphereProd E 1 one_pos

中文:
定义 homeomorphUnitSphereProd
  签名: :
  定义体: homeomorphSphereProd E 1 one_pos

Depends on / 依赖: homeomorphSphereProd, one_pos
-/
noncomputable def homeomorphUnitSphereProd :
    ({0}ᶜ : Set E) ≃ₜ (sphere (0 : E) 1 × Ioi (0 : Real)) :=
  homeomorphSphereProd E 1 one_pos

variable {E}

/--
theorem `IsOpen.smul_sphere` / 定理 `IsOpen.smul_sphere`

English:
theorem IsOpen.smul_sphere
  statement: {r : Real} (hr : r != 0) {U : Set Real} {V : Set (Metric.sphere (0 : E) r)}
  proof: by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxU, _, ⟨y, hyV, rfl⟩, rfl⟩
  wlog hx₀ : 0 < x generalizing x U
  · replace hx₀ : 0 < -x := by
      rw [not_lt]; rw [le_iff_eq_or_lt]; rw [← neg_pos] at hx₀
exact hx₀.resolve_left ne_of_mem_of_not_mem hxU hU₀
    specialize this hU.neg (by simpa) (-x) (b

中文:
定理 IsOpen.smul_sphere
  结论: {r : 实数} (hr : r != 0) {U : Set 实数} {V : Set (Metric.sphere (0 : E) r)}
  证明: by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxU, _, ⟨y, hyV, rfl⟩, rfl⟩
  wlog hx₀ : 0 < x generalizing x U
  · replace hx₀ : 0 < -x := by
      rw [not_lt]; rw [le_iff_eq_or_lt]; rw [← neg_pos] at hx₀
exact hx₀.resolve_left ne_of_mem_of_not_mem hxU hU₀
    specialize this hU.neg (by simpa) (-x) (b

Depends on / 依赖: Filter, Filter.mem_neg, Set.neg_smul, generalizing, hU.neg, hr.symm, isOpen_iff_mem_nhds, le_iff_eq_or_lt, lt_of_le_of_ne, mem_neg, ne_of_mem_of_not_mem, neg_pos, neg_smul, nhds_neg, norm_nonneg, not_lt, replace, resolve_left, specialize
-/
theorem IsOpen.smul_sphere {r : Real} (hr : r != 0) {U : Set Real} {V : Set (Metric.sphere (0 : E) r)}
    (hU : IsOpen U) (hU₀ : 0 ∉ U) (hV : IsOpen V) : IsOpen (U • (V : Set E)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxU, _, ⟨y, hyV, rfl⟩, rfl⟩
  wlog hx₀ : 0 < x generalizing x U
  · replace hx₀ : 0 < -x := by
      rw [not_lt]; rw [le_iff_eq_or_lt]; rw [← neg_pos] at hx₀
exact hx₀.resolve_left ne_of_mem_of_not_mem hxU hU₀
    specialize this hU.neg (by simpa) (-x) (by simpa) hx₀
    simp only [neg_smul, nhds_neg, Set.neg_smul, Filter.mem_neg] at this
    simpa using this
  have hr₀ : 0 < r := lt_of_le_of_ne (by simpa using norm_nonneg y.1) hr.symm
  lift x to Ioi (0 : Real) using hx₀
  have : V ×ˢ (Ioi (0 : Real) ↓inter U) in 𝓝 (y, x) :=
    prod_mem_nhds (hV.mem_nhds hyV) (hU.preimage_val.mem_nhds hxU)
  replace := image_mem_map (m := Subtype.val ∘ (homeomorphSphereProd E r hr₀).symm) this
  rw [← Filter.map_map]; rw [(homeomorphSphereProd _ r hr₀).symm.map_nhds_eq]; rw [map_nhds_subtype_val]; rw [IsOpen.nhdsWithin_eq]; rw [homeomorphSphereProd_symm_apply_coe] at this
  · filter_upwards [this]
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    rw [Function.comp_apply]; rw [homeomorphSphereProd_symm_apply_coe]
    apply Set.smul_mem_smul
    exacts [hb, mem_image_of_mem _ ha]
  · exact isOpen_compl_singleton
  · simp [x.2.out.ne', ne_zero_of_mem_sphere, hr₀.ne']
