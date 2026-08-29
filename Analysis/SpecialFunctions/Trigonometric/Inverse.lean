/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.ProjIcc

/-!
# Inverse trigonometric functions.

See also `Analysis.SpecialFunctions.Trigonometric.Arctan` for the inverse tan function.
(This is delayed as it is easier to set up after developing complex trigonometric functions.)

Basic inequalities on trigonometric functions.
-/

@[expose] public section


noncomputable section

open Topology Filter Set Filter Real

namespace Real
variable {x y : Real}

/-- Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x ≤ π / 2`.
It defaults to `-π / 2` on `(-∞, -1)` and to `π / 2` to `(1, ∞)`. -/
@[pp_nodot]
/--
Definition of `arcsin` / `arcsin` 的定义

English:
definition arcsin
  signature: : Real -> Real
  body: Subtype.val ∘ IccExtend (neg_le_self zero_le_one) sinOrderIso.symm

中文:
定义 arcsin
  签名: : 实数 -> 实数
  定义体: Subtype.val ∘ IccExtend (neg_le_self zero_le_one) sinOrderIso.symm

Depends on / 依赖: IccExtend, Subtype, Subtype.val, neg_le_self, sinOrderIso, sinOrderIso.symm, zero_le_one
-/
noncomputable def arcsin : Real -> Real :=
  Subtype.val ∘ IccExtend (neg_le_self zero_le_one) sinOrderIso.symm

/--
theorem `arcsin_mem_Icc` / 定理 `arcsin_mem_Icc`

English:
theorem arcsin_mem_Icc
  given: (x : Real)
  statement: arcsin x in Icc (-(π / 2)) (π / 2)
  proof: Subtype.coe_prop _

中文:
定理 arcsin_mem_Icc
  条件: (x : 实数)
  结论: arcsin x in 闭区间 (-(π / 2)) (π / 2)
  证明: Subtype.coe_prop _

Depends on / 依赖: Subtype, Subtype.coe_prop, coe_prop
-/
theorem arcsin_mem_Icc (x : Real) : arcsin x in Icc (-(π / 2)) (π / 2) :=
  Subtype.coe_prop _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `range_arcsin` / 定理 `range_arcsin`

English:
theorem range_arcsin
  statement: range arcsin = Icc (-(π / 2)) (π / 2)
  proof: by
  rw [arcsin]; rw [range_comp Subtype.val]
  ext
  simp

中文:
定理 range_arcsin
  结论: range arcsin = 闭区间 (-(π / 2)) (π / 2)
  证明: by
  rw [arcsin]; rw [range_comp Subtype.val]
  ext
  simp

Depends on / 依赖: Subtype, Subtype.val, arcsin, range_comp
-/
theorem range_arcsin : range arcsin = Icc (-(π / 2)) (π / 2) := by
  rw [arcsin]; rw [range_comp Subtype.val]
  ext
  simp

/--
theorem `arcsin_le_pi_div_two` / 定理 `arcsin_le_pi_div_two`

English:
theorem arcsin_le_pi_div_two
  given: (x : Real)
  statement: arcsin x <= π / 2
  proof: (arcsin_mem_Icc x).2

中文:
定理 arcsin_le_pi_div_two
  条件: (x : 实数)
  结论: arcsin x <= π / 2
  证明: (arcsin_mem_Icc x).2

Depends on / 依赖: arcsin_mem_Icc
-/
theorem arcsin_le_pi_div_two (x : Real) : arcsin x <= π / 2 :=
  (arcsin_mem_Icc x).2

/--
theorem `neg_pi_div_two_le_arcsin` / 定理 `neg_pi_div_two_le_arcsin`

English:
theorem neg_pi_div_two_le_arcsin
  given: (x : Real)
  statement: -(π / 2) <= arcsin x
  proof: (arcsin_mem_Icc x).1

中文:
定理 neg_pi_div_two_le_arcsin
  条件: (x : 实数)
  结论: -(π / 2) <= arcsin x
  证明: (arcsin_mem_Icc x).1

Depends on / 依赖: arcsin_mem_Icc
-/
theorem neg_pi_div_two_le_arcsin (x : Real) : -(π / 2) <= arcsin x :=
  (arcsin_mem_Icc x).1

/--
theorem `arcsin_projIcc` / 定理 `arcsin_projIcc`

English:
theorem arcsin_projIcc
  given: (x : Real)
  proof: by
  rw [arcsin]; rw [Function.comp_apply]; rw [IccExtend_val]; rw [Function.comp_apply]; rw [IccExtend]; rw [Function.comp_apply]

中文:
定理 arcsin_projIcc
  条件: (x : 实数)
  证明: by
  rw [arcsin]; rw [Function.comp_apply]; rw [IccExtend_val]; rw [Function.comp_apply]; rw [IccExtend]; rw [Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, IccExtend, IccExtend_val, arcsin, comp_apply
-/
theorem arcsin_projIcc (x : Real) :
    arcsin (projIcc (-1) 1 (neg_le_self zero_le_one) x) = arcsin x := by
  rw [arcsin]; rw [Function.comp_apply]; rw [IccExtend_val]; rw [Function.comp_apply]; rw [IccExtend]; rw [Function.comp_apply]

/--
theorem `sin_arcsin'` / 定理 `sin_arcsin'`

English:
theorem sin_arcsin'
  given: {x : Real} (hx : x in Icc (-1 : Real) 1)
  statement: sin (arcsin x) = x
  proof: by
  simpa [arcsin, IccExtend_of_mem _ _ hx, -OrderIso.apply_symm_apply] using
    Subtype.ext_iff.1 (sinOrderIso.apply_symm_apply ⟨x, hx⟩)

中文:
定理 sin_arcsin'
  条件: {x : 实数} (hx : x in 闭区间 (-1 : 实数) 1)
  结论: sin (arcsin x) = x
  证明: by
  simpa [arcsin, IccExtend_of_mem _ _ hx, -OrderIso.apply_symm_apply] using
    Subtype.ext_iff.1 (sinOrderIso.apply_symm_apply ⟨x, hx⟩)

Depends on / 依赖: IccExtend_of_mem, OrderIso, OrderIso.apply_symm_apply, Subtype, Subtype.ext_iff, apply_symm_apply, arcsin, ext_iff, sinOrderIso, sinOrderIso.apply_symm_apply
-/
theorem sin_arcsin' {x : Real} (hx : x in Icc (-1 : Real) 1) : sin (arcsin x) = x := by
  simpa [arcsin, IccExtend_of_mem _ _ hx, -OrderIso.apply_symm_apply] using
    Subtype.ext_iff.1 (sinOrderIso.apply_symm_apply ⟨x, hx⟩)

/--
theorem `sin_arcsin` / 定理 `sin_arcsin`

English:
theorem sin_arcsin
  given: {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1)
  statement: sin (arcsin x) = x
  proof: sin_arcsin' ⟨hx₁, hx₂⟩

中文:
定理 sin_arcsin
  条件: {x : 实数} (hx₁ : -1 <= x) (hx₂ : x <= 1)
  结论: sin (arcsin x) = x
  证明: sin_arcsin' ⟨hx₁, hx₂⟩

Depends on / 依赖: sin_arcsin
-/
theorem sin_arcsin {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : sin (arcsin x) = x :=
  sin_arcsin' ⟨hx₁, hx₂⟩

/--
theorem `arcsin_sin'` / 定理 `arcsin_sin'`

English:
theorem arcsin_sin'
  given: {x : Real} (hx : x in Icc (-(π / 2)) (π / 2))
  statement: arcsin (sin x) = x
  proof: injOn_sin (arcsin_mem_Icc _) hx by rw [sin_arcsin (neg_one_le_sin _) (sin_le_one _)]

中文:
定理 arcsin_sin'
  条件: {x : 实数} (hx : x in 闭区间 (-(π / 2)) (π / 2))
  结论: arcsin (sin x) = x
  证明: injOn_sin (arcsin_mem_Icc _) hx by rw [sin_arcsin (neg_one_le_sin _) (sin_le_one _)]

Depends on / 依赖: arcsin_mem_Icc, injOn_sin, neg_one_le_sin, sin_arcsin, sin_le_one
-/
theorem arcsin_sin' {x : Real} (hx : x in Icc (-(π / 2)) (π / 2)) : arcsin (sin x) = x :=
injOn_sin (arcsin_mem_Icc _) hx by rw [sin_arcsin (neg_one_le_sin _) (sin_le_one _)]

/--
theorem `arcsin_sin` / 定理 `arcsin_sin`

English:
theorem arcsin_sin
  given: {x : Real} (hx₁ : -(π / 2) <= x) (hx₂ : x <= π / 2)
  statement: arcsin (sin x) = x
  proof: arcsin_sin' ⟨hx₁, hx₂⟩

中文:
定理 arcsin_sin
  条件: {x : 实数} (hx₁ : -(π / 2) <= x) (hx₂ : x <= π / 2)
  结论: arcsin (sin x) = x
  证明: arcsin_sin' ⟨hx₁, hx₂⟩

Depends on / 依赖: arcsin_sin
-/
theorem arcsin_sin {x : Real} (hx₁ : -(π / 2) <= x) (hx₂ : x <= π / 2) : arcsin (sin x) = x :=
  arcsin_sin' ⟨hx₁, hx₂⟩

/--
theorem `strictMonoOn_arcsin` / 定理 `strictMonoOn_arcsin`

English:
theorem strictMonoOn_arcsin
  statement: StrictMonoOn arcsin (Icc (-1) 1)
  proof: (Subtype.strictMono_coe _).comp_strictMonoOn
    sinOrderIso.symm.strictMono.strictMonoOn_IccExtend _

@[gcongr]

中文:
定理 strictMonoOn_arcsin
  结论: StrictMonoOn arcsin (闭区间 (-1) 1)
  证明: (Subtype.strictMono_coe _).comp_strictMonoOn
    sinOrderIso.symm.strictMono.strictMonoOn_IccExtend _

@[gcongr]

Depends on / 依赖: Subtype, Subtype.strictMono_coe, comp_strictMonoOn, sinOrderIso, sinOrderIso.symm.strictMono.strictMonoOn_IccExtend, strictMono, strictMonoOn_IccExtend, strictMono_coe
-/
theorem strictMonoOn_arcsin : StrictMonoOn arcsin (Icc (-1) 1) :=
(Subtype.strictMono_coe _).comp_strictMonoOn
    sinOrderIso.symm.strictMono.strictMonoOn_IccExtend _

@[gcongr]
/--
theorem `arcsin_lt_arcsin` / 定理 `arcsin_lt_arcsin`

English:
theorem arcsin_lt_arcsin
  given: {x y : Real} (hx : -1 <= x) (hlt : x < y) (hy : y <= 1)
  proof: strictMonoOn_arcsin ⟨hx, hlt.le.trans hy⟩ ⟨hx.trans hlt.le, hy⟩ hlt

中文:
定理 arcsin_lt_arcsin
  条件: {x y : 实数} (hx : -1 <= x) (hlt : x < y) (hy : y <= 1)
  证明: strictMonoOn_arcsin ⟨hx, hlt.le.trans hy⟩ ⟨hx.trans hlt.le, hy⟩ hlt

Depends on / 依赖: hlt.le, hlt.le.trans, hx.trans, strictMonoOn_arcsin
-/
theorem arcsin_lt_arcsin {x y : Real} (hx : -1 <= x) (hlt : x < y) (hy : y <= 1) :
    arcsin x < arcsin y :=
  strictMonoOn_arcsin ⟨hx, hlt.le.trans hy⟩ ⟨hx.trans hlt.le, hy⟩ hlt

/--
theorem `monotone_arcsin` / 定理 `monotone_arcsin`

English:
theorem monotone_arcsin
  statement: Monotone arcsin
  proof: (Subtype.mono_coe _).comp sinOrderIso.symm.monotone.IccExtend _

@[gcongr]

中文:
定理 monotone_arcsin
  结论: 递增 arcsin
  证明: (Subtype.mono_coe _).comp sinOrderIso.symm.monotone.IccExtend _

@[gcongr]

Depends on / 依赖: IccExtend, Subtype, Subtype.mono_coe, mono_coe, monotone, sinOrderIso, sinOrderIso.symm.monotone.IccExtend
-/
theorem monotone_arcsin : Monotone arcsin :=
(Subtype.mono_coe _).comp sinOrderIso.symm.monotone.IccExtend _

@[gcongr]
/--
theorem `arcsin_le_arcsin` / 定理 `arcsin_le_arcsin`

English:
theorem arcsin_le_arcsin
  given: {x y : Real} (h : x <= y)
  statement: arcsin x <= arcsin y
  proof: monotone_arcsin h

中文:
定理 arcsin_le_arcsin
  条件: {x y : 实数} (h : x <= y)
  结论: arcsin x <= arcsin y
  证明: monotone_arcsin h

Depends on / 依赖: monotone_arcsin
-/
theorem arcsin_le_arcsin {x y : Real} (h : x <= y) : arcsin x <= arcsin y := monotone_arcsin h

/--
theorem `injOn_arcsin` / 定理 `injOn_arcsin`

English:
theorem injOn_arcsin
  statement: InjOn arcsin (Icc (-1) 1)
  proof: strictMonoOn_arcsin.injOn

中文:
定理 injOn_arcsin
  结论: 单射限制 arcsin (闭区间 (-1) 1)
  证明: strictMonoOn_arcsin.injOn

Depends on / 依赖: strictMonoOn_arcsin, strictMonoOn_arcsin.injOn
-/
theorem injOn_arcsin : InjOn arcsin (Icc (-1) 1) :=
  strictMonoOn_arcsin.injOn

/--
theorem `arcsin_inj` / 定理 `arcsin_inj`

English:
theorem arcsin_inj
  given: {x y : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) (hy₁ : -1 <= y) (hy₂ : y <= 1)
  proof: injOn_arcsin.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[continuity, fun_prop]

中文:
定理 arcsin_inj
  条件: {x y : 实数} (hx₁ : -1 <= x) (hx₂ : x <= 1) (hy₁ : -1 <= y) (hy₂ : y <= 1)
  证明: injOn_arcsin.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[continuity, fun_prop]

Depends on / 依赖: eq_iff, injOn_arcsin, injOn_arcsin.eq_iff
-/
theorem arcsin_inj {x y : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) (hy₁ : -1 <= y) (hy₂ : y <= 1) :
    arcsin x = arcsin y ↔ x = y :=
  injOn_arcsin.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[continuity, fun_prop]
/--
theorem `continuous_arcsin` / 定理 `continuous_arcsin`

English:
theorem continuous_arcsin
  statement: Continuous arcsin
  proof: continuous_subtype_val.comp sinOrderIso.symm.continuous.Icc_extend'

@[fun_prop]

中文:
定理 continuous_arcsin
  结论: 连续 arcsin
  证明: continuous_subtype_val.comp sinOrderIso.symm.continuous.Icc_extend'

@[fun_prop]

Depends on / 依赖: Icc_extend, continuous, continuous_subtype_val, continuous_subtype_val.comp, sinOrderIso, sinOrderIso.symm.continuous.Icc_extend
-/
theorem continuous_arcsin : Continuous arcsin :=
  continuous_subtype_val.comp sinOrderIso.symm.continuous.Icc_extend'

@[fun_prop]
/--
theorem `continuousAt_arcsin` / 定理 `continuousAt_arcsin`

English:
theorem continuousAt_arcsin
  given: {x : Real}
  statement: ContinuousAt arcsin x
  proof: continuous_arcsin.continuousAt

中文:
定理 continuousAt_arcsin
  条件: {x : 实数}
  结论: ContinuousAt arcsin x
  证明: continuous_arcsin.continuousAt

Depends on / 依赖: continuousAt, continuous_arcsin, continuous_arcsin.continuousAt
-/
theorem continuousAt_arcsin {x : Real} : ContinuousAt arcsin x :=
  continuous_arcsin.continuousAt

/--
theorem `arcsin_eq_of_sin_eq` / 定理 `arcsin_eq_of_sin_eq`

English:
theorem arcsin_eq_of_sin_eq
  given: {x y : Real} (h₁ : sin x = y) (h₂ : x in Icc (-(π / 2)) (π / 2))
  proof: by
  subst y
  exact injOn_sin (arcsin_mem_Icc _) h₂ (sin_arcsin' (sin_mem_Icc x))

@[simp]

中文:
定理 arcsin_eq_of_sin_eq
  条件: {x y : 实数} (h₁ : sin x = y) (h₂ : x in 闭区间 (-(π / 2)) (π / 2))
  证明: by
  subst y
  exact injOn_sin (arcsin_mem_Icc _) h₂ (sin_arcsin' (sin_mem_Icc x))

@[simp]

Depends on / 依赖: arcsin_mem_Icc, injOn_sin, sin_arcsin, sin_mem_Icc
-/
theorem arcsin_eq_of_sin_eq {x y : Real} (h₁ : sin x = y) (h₂ : x in Icc (-(π / 2)) (π / 2)) :
    arcsin y = x := by
  subst y
  exact injOn_sin (arcsin_mem_Icc _) h₂ (sin_arcsin' (sin_mem_Icc x))

@[simp]
/--
theorem `arcsin_zero` / 定理 `arcsin_zero`

English:
theorem arcsin_zero
  statement: arcsin 0 = 0
  proof: arcsin_eq_of_sin_eq sin_zero ⟨neg_nonpos.2 pi_div_two_pos.le, pi_div_two_pos.le⟩

@[simp]

中文:
定理 arcsin_zero
  结论: arcsin 0 = 0
  证明: arcsin_eq_of_sin_eq sin_zero ⟨neg_nonpos.2 pi_div_two_pos.le, pi_div_two_pos.le⟩

@[simp]

Depends on / 依赖: arcsin_eq_of_sin_eq, neg_nonpos, pi_div_two_pos, pi_div_two_pos.le, sin_zero
-/
theorem arcsin_zero : arcsin 0 = 0 :=
  arcsin_eq_of_sin_eq sin_zero ⟨neg_nonpos.2 pi_div_two_pos.le, pi_div_two_pos.le⟩

@[simp]
/--
theorem `arcsin_one` / 定理 `arcsin_one`

English:
theorem arcsin_one
  statement: arcsin 1 = π / 2
  proof: arcsin_eq_of_sin_eq sin_pi_div_two right_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

中文:
定理 arcsin_one
  结论: arcsin 1 = π / 2
  证明: arcsin_eq_of_sin_eq sin_pi_div_two right_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

Depends on / 依赖: arcsin_eq_of_sin_eq, neg_le_self, pi_div_two_pos, pi_div_two_pos.le, right_mem_Icc, sin_pi_div_two
-/
theorem arcsin_one : arcsin 1 = π / 2 :=
arcsin_eq_of_sin_eq sin_pi_div_two right_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

/--
theorem `arcsin_of_one_le` / 定理 `arcsin_of_one_le`

English:
theorem arcsin_of_one_le
  given: {x : Real} (hx : 1 <= x)
  statement: arcsin x = π / 2
  proof: by
  rw [← arcsin_projIcc]; rw [projIcc_of_right_le _ hx]; rw [Subtype.coe_mk]; rw [arcsin_one]

中文:
定理 arcsin_of_one_le
  条件: {x : 实数} (hx : 1 <= x)
  结论: arcsin x = π / 2
  证明: by
  rw [← arcsin_projIcc]; rw [projIcc_of_right_le _ hx]; rw [Subtype.coe_mk]; rw [arcsin_one]

Depends on / 依赖: Subtype, Subtype.coe_mk, arcsin_one, arcsin_projIcc, coe_mk, projIcc_of_right_le
-/
theorem arcsin_of_one_le {x : Real} (hx : 1 <= x) : arcsin x = π / 2 := by
  rw [← arcsin_projIcc]; rw [projIcc_of_right_le _ hx]; rw [Subtype.coe_mk]; rw [arcsin_one]

/--
theorem `arcsin_neg_one` / 定理 `arcsin_neg_one`

English:
theorem arcsin_neg_one
  statement: arcsin (-1) = -(π / 2)
  proof: arcsin_eq_of_sin_eq (by rw [sin_neg, sin_pi_div_two])
    left_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

中文:
定理 arcsin_neg_one
  结论: arcsin (-1) = -(π / 2)
  证明: arcsin_eq_of_sin_eq (by rw [sin_neg, sin_pi_div_two])
    left_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

Depends on / 依赖: arcsin_eq_of_sin_eq, left_mem_Icc, neg_le_self, pi_div_two_pos, pi_div_two_pos.le, sin_neg, sin_pi_div_two
-/
theorem arcsin_neg_one : arcsin (-1) = -(π / 2) :=
arcsin_eq_of_sin_eq (by rw [sin_neg, sin_pi_div_two])
    left_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

/--
theorem `arcsin_of_le_neg_one` / 定理 `arcsin_of_le_neg_one`

English:
theorem arcsin_of_le_neg_one
  given: {x : Real} (hx : x <= -1)
  statement: arcsin x = -(π / 2)
  proof: by
  rw [← arcsin_projIcc]; rw [projIcc_of_le_left _ hx]; rw [Subtype.coe_mk]; rw [arcsin_neg_one]

@[simp]

中文:
定理 arcsin_of_le_neg_one
  条件: {x : 实数} (hx : x <= -1)
  结论: arcsin x = -(π / 2)
  证明: by
  rw [← arcsin_projIcc]; rw [projIcc_of_le_left _ hx]; rw [Subtype.coe_mk]; rw [arcsin_neg_one]

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_mk, arcsin_neg_one, arcsin_projIcc, coe_mk, projIcc_of_le_left
-/
theorem arcsin_of_le_neg_one {x : Real} (hx : x <= -1) : arcsin x = -(π / 2) := by
  rw [← arcsin_projIcc]; rw [projIcc_of_le_left _ hx]; rw [Subtype.coe_mk]; rw [arcsin_neg_one]

@[simp]
/--
theorem `arcsin_neg` / 定理 `arcsin_neg`

English:
theorem arcsin_neg
  given: (x : Real)
  statement: arcsin (-x) = -arcsin x
  proof: by
  rcases le_total x (-1) with hx₁ | hx₁
  · rw [arcsin_of_le_neg_one hx₁, neg_neg, arcsin_of_one_le (le_neg.2 hx₁)]
  rcases le_total 1 x with hx₂ | hx₂
  · rw [arcsin_of_one_le hx₂, arcsin_of_le_neg_one (neg_le_neg hx₂)]
  refine arcsin_eq_of_sin_eq ?_ ?_
  · rw [sin_neg, sin_arcsin hx₁ hx₂]
  · exact ⟨neg_le_neg (arcsin_le_pi_div_two _), neg_le.2 (neg_pi_div_two_le_arcsin _)⟩

中文:
定理 arcsin_neg
  条件: (x : 实数)
  结论: arcsin (-x) = -arcsin x
  证明: by
  rcases le_total x (-1) with hx₁ | hx₁
  · rw [arcsin_of_le_neg_one hx₁, neg_neg, arcsin_of_one_le (le_neg.2 hx₁)]
  rcases le_total 1 x with hx₂ | hx₂
  · rw [arcsin_of_one_le hx₂, arcsin_of_le_neg_one (neg_le_neg hx₂)]
  refine arcsin_eq_of_sin_eq ?_ ?_
  · rw [sin_neg, sin_arcsin hx₁ hx₂]
  · exact ⟨neg_le_neg (arcsin_le_pi_div_two _), neg_le.2 (neg_pi_div_two_le_arcsin _)⟩

Depends on / 依赖: arcsin_eq_of_sin_eq, arcsin_le_pi_div_two, arcsin_of_le_neg_one, arcsin_of_one_le, le_neg, le_total, neg_le, neg_le_neg, neg_neg, neg_pi_div_two_le_arcsin, sin_arcsin, sin_neg
-/
theorem arcsin_neg (x : Real) : arcsin (-x) = -arcsin x := by
  rcases le_total x (-1) with hx₁ | hx₁
  · rw [arcsin_of_le_neg_one hx₁, neg_neg, arcsin_of_one_le (le_neg.2 hx₁)]
  rcases le_total 1 x with hx₂ | hx₂
  · rw [arcsin_of_one_le hx₂, arcsin_of_le_neg_one (neg_le_neg hx₂)]
  refine arcsin_eq_of_sin_eq ?_ ?_
  · rw [sin_neg, sin_arcsin hx₁ hx₂]
  · exact ⟨neg_le_neg (arcsin_le_pi_div_two _), neg_le.2 (neg_pi_div_two_le_arcsin _)⟩

/--
theorem `arcsin_le_iff_le_sin` / 定理 `arcsin_le_iff_le_sin`

English:
theorem arcsin_le_iff_le_sin
  given: {x y : Real} (hx : x in Icc (-1 : Real) 1) (hy : y in Icc (-(π / 2)) (π / 2))
  proof: by
  rw [← arcsin_sin' hy]; rw [strictMonoOn_arcsin.le_iff_le hx (sin_mem_Icc _)]; rw [arcsin_sin' hy]

中文:
定理 arcsin_le_iff_le_sin
  条件: {x y : 实数} (hx : x in 闭区间 (-1 : 实数) 1) (hy : y in 闭区间 (-(π / 2)) (π / 2))
  证明: by
  rw [← arcsin_sin' hy]; rw [strictMonoOn_arcsin.le_iff_le hx (sin_mem_Icc _)]; rw [arcsin_sin' hy]

Depends on / 依赖: arcsin_sin, le_iff_le, sin_mem_Icc, strictMonoOn_arcsin, strictMonoOn_arcsin.le_iff_le
-/
theorem arcsin_le_iff_le_sin {x y : Real} (hx : x in Icc (-1 : Real) 1) (hy : y in Icc (-(π / 2)) (π / 2)) :
    arcsin x <= y ↔ x <= sin y := by
  rw [← arcsin_sin' hy]; rw [strictMonoOn_arcsin.le_iff_le hx (sin_mem_Icc _)]; rw [arcsin_sin' hy]

/--
theorem `arcsin_le_iff_le_sin'` / 定理 `arcsin_le_iff_le_sin'`

English:
theorem arcsin_le_iff_le_sin'
  given: {x y : Real} (hy : y in Ico (-(π / 2)) (π / 2))
  proof: by
  rcases le_total x (-1) with hx₁ | hx₁
  · simp [arcsin_of_le_neg_one hx₁, hy.1, hx₁.trans (neg_one_le_sin _)]
  rcases lt_or_ge 1 x with hx₂ | hx₂
  · simp [arcsin_of_one_le hx₂.le, hy.2.not_ge, (sin_le_one y).trans_lt hx₂]
  exact arcsin_le_iff_le_sin ⟨hx₁, hx₂⟩ (mem_Icc_of_Ico hy)

中文:
定理 arcsin_le_iff_le_sin'
  条件: {x y : 实数} (hy : y in 左闭右开区间 (-(π / 2)) (π / 2))
  证明: by
  rcases le_total x (-1) with hx₁ | hx₁
  · simp [arcsin_of_le_neg_one hx₁, hy.1, hx₁.trans (neg_one_le_sin _)]
  rcases lt_or_ge 1 x with hx₂ | hx₂
  · simp [arcsin_of_one_le hx₂.le, hy.2.not_ge, (sin_le_one y).trans_lt hx₂]
  exact arcsin_le_iff_le_sin ⟨hx₁, hx₂⟩ (mem_Icc_of_Ico hy)

Depends on / 依赖: arcsin_le_iff_le_sin, arcsin_of_le_neg_one, arcsin_of_one_le, le_total, lt_or_ge, mem_Icc_of_Ico, neg_one_le_sin, not_ge, sin_le_one, trans_lt
-/
theorem arcsin_le_iff_le_sin' {x y : Real} (hy : y in Ico (-(π / 2)) (π / 2)) :
    arcsin x <= y ↔ x <= sin y := by
  rcases le_total x (-1) with hx₁ | hx₁
  · simp [arcsin_of_le_neg_one hx₁, hy.1, hx₁.trans (neg_one_le_sin _)]
  rcases lt_or_ge 1 x with hx₂ | hx₂
  · simp [arcsin_of_one_le hx₂.le, hy.2.not_ge, (sin_le_one y).trans_lt hx₂]
  exact arcsin_le_iff_le_sin ⟨hx₁, hx₂⟩ (mem_Icc_of_Ico hy)

/--
theorem `le_arcsin_iff_sin_le` / 定理 `le_arcsin_iff_sin_le`

English:
theorem le_arcsin_iff_sin_le
  given: {x y : Real} (hx : x in Icc (-(π / 2)) (π / 2)) (hy : y in Icc (-1 : Real) 1)
  proof: by
  rw [← neg_le_neg_iff]; rw [← arcsin_neg]; rw [arcsin_le_iff_le_sin ⟨neg_le_neg hy.2]; rw [neg_le.2 hy.1⟩ ⟨neg_le_neg hx.2]; rw [neg_le.2 hx.1⟩]; rw [sin_neg]; rw [neg_le_neg_iff]

中文:
定理 le_arcsin_iff_sin_le
  条件: {x y : 实数} (hx : x in 闭区间 (-(π / 2)) (π / 2)) (hy : y in 闭区间 (-1 : 实数) 1)
  证明: by
  rw [← neg_le_neg_iff]; rw [← arcsin_neg]; rw [arcsin_le_iff_le_sin ⟨neg_le_neg hy.2]; rw [neg_le.2 hy.1⟩ ⟨neg_le_neg hx.2]; rw [neg_le.2 hx.1⟩]; rw [sin_neg]; rw [neg_le_neg_iff]

Depends on / 依赖: arcsin_le_iff_le_sin, arcsin_neg, neg_le, neg_le_neg, neg_le_neg_iff, sin_neg
-/
theorem le_arcsin_iff_sin_le {x y : Real} (hx : x in Icc (-(π / 2)) (π / 2)) (hy : y in Icc (-1 : Real) 1) :
    x <= arcsin y ↔ sin x <= y := by
  rw [← neg_le_neg_iff]; rw [← arcsin_neg]; rw [arcsin_le_iff_le_sin ⟨neg_le_neg hy.2]; rw [neg_le.2 hy.1⟩ ⟨neg_le_neg hx.2]; rw [neg_le.2 hx.1⟩]; rw [sin_neg]; rw [neg_le_neg_iff]

/--
theorem `le_arcsin_iff_sin_le'` / 定理 `le_arcsin_iff_sin_le'`

English:
theorem le_arcsin_iff_sin_le'
  given: {x y : Real} (hx : x in Ioc (-(π / 2)) (π / 2))
  proof: by
  rw [← neg_le_neg_iff]; rw [← arcsin_neg]; rw [arcsin_le_iff_le_sin' ⟨neg_le_neg hx.2]; rw [neg_lt.2 hx.1⟩]; rw [sin_neg]; rw [neg_le_neg_iff]

中文:
定理 le_arcsin_iff_sin_le'
  条件: {x y : 实数} (hx : x in 左开右闭区间 (-(π / 2)) (π / 2))
  证明: by
  rw [← neg_le_neg_iff]; rw [← arcsin_neg]; rw [arcsin_le_iff_le_sin' ⟨neg_le_neg hx.2]; rw [neg_lt.2 hx.1⟩]; rw [sin_neg]; rw [neg_le_neg_iff]

Depends on / 依赖: arcsin_le_iff_le_sin, arcsin_neg, neg_le_neg, neg_le_neg_iff, neg_lt, sin_neg
-/
theorem le_arcsin_iff_sin_le' {x y : Real} (hx : x in Ioc (-(π / 2)) (π / 2)) :
    x <= arcsin y ↔ sin x <= y := by
  rw [← neg_le_neg_iff]; rw [← arcsin_neg]; rw [arcsin_le_iff_le_sin' ⟨neg_le_neg hx.2]; rw [neg_lt.2 hx.1⟩]; rw [sin_neg]; rw [neg_le_neg_iff]

/--
theorem `arcsin_lt_iff_lt_sin` / 定理 `arcsin_lt_iff_lt_sin`

English:
theorem arcsin_lt_iff_lt_sin
  given: {x y : Real} (hx : x in Icc (-1 : Real) 1) (hy : y in Icc (-(π / 2)) (π / 2))
  proof: not_le.symm.trans (not_congr <| le_arcsin_iff_sin_le hy hx).trans not_le

中文:
定理 arcsin_lt_iff_lt_sin
  条件: {x y : 实数} (hx : x in 闭区间 (-1 : 实数) 1) (hy : y in 闭区间 (-(π / 2)) (π / 2))
  证明: not_le.symm.trans (not_congr <| le_arcsin_iff_sin_le hy hx).trans not_le

Depends on / 依赖: le_arcsin_iff_sin_le, not_congr, not_le, not_le.symm.trans
-/
theorem arcsin_lt_iff_lt_sin {x y : Real} (hx : x in Icc (-1 : Real) 1) (hy : y in Icc (-(π / 2)) (π / 2)) :
    arcsin x < y ↔ x < sin y :=
not_le.symm.trans (not_congr <| le_arcsin_iff_sin_le hy hx).trans not_le

/--
theorem `arcsin_lt_iff_lt_sin'` / 定理 `arcsin_lt_iff_lt_sin'`

English:
theorem arcsin_lt_iff_lt_sin'
  given: {x y : Real} (hy : y in Ioc (-(π / 2)) (π / 2))
  proof: not_le.symm.trans (not_congr <| le_arcsin_iff_sin_le' hy).trans not_le

中文:
定理 arcsin_lt_iff_lt_sin'
  条件: {x y : 实数} (hy : y in 左开右闭区间 (-(π / 2)) (π / 2))
  证明: not_le.symm.trans (not_congr <| le_arcsin_iff_sin_le' hy).trans not_le

Depends on / 依赖: le_arcsin_iff_sin_le, not_congr, not_le, not_le.symm.trans
-/
theorem arcsin_lt_iff_lt_sin' {x y : Real} (hy : y in Ioc (-(π / 2)) (π / 2)) :
    arcsin x < y ↔ x < sin y :=
not_le.symm.trans (not_congr <| le_arcsin_iff_sin_le' hy).trans not_le

/--
theorem `lt_arcsin_iff_sin_lt` / 定理 `lt_arcsin_iff_sin_lt`

English:
theorem lt_arcsin_iff_sin_lt
  given: {x y : Real} (hx : x in Icc (-(π / 2)) (π / 2)) (hy : y in Icc (-1 : Real) 1)
  proof: not_le.symm.trans (not_congr <| arcsin_le_iff_le_sin hy hx).trans not_le

中文:
定理 lt_arcsin_iff_sin_lt
  条件: {x y : 实数} (hx : x in 闭区间 (-(π / 2)) (π / 2)) (hy : y in 闭区间 (-1 : 实数) 1)
  证明: not_le.symm.trans (not_congr <| arcsin_le_iff_le_sin hy hx).trans not_le

Depends on / 依赖: arcsin_le_iff_le_sin, not_congr, not_le, not_le.symm.trans
-/
theorem lt_arcsin_iff_sin_lt {x y : Real} (hx : x in Icc (-(π / 2)) (π / 2)) (hy : y in Icc (-1 : Real) 1) :
    x < arcsin y ↔ sin x < y :=
not_le.symm.trans (not_congr <| arcsin_le_iff_le_sin hy hx).trans not_le

/--
theorem `lt_arcsin_iff_sin_lt'` / 定理 `lt_arcsin_iff_sin_lt'`

English:
theorem lt_arcsin_iff_sin_lt'
  given: {x y : Real} (hx : x in Ico (-(π / 2)) (π / 2))
  proof: not_le.symm.trans (not_congr <| arcsin_le_iff_le_sin' hx).trans not_le

中文:
定理 lt_arcsin_iff_sin_lt'
  条件: {x y : 实数} (hx : x in 左闭右开区间 (-(π / 2)) (π / 2))
  证明: not_le.symm.trans (not_congr <| arcsin_le_iff_le_sin' hx).trans not_le

Depends on / 依赖: arcsin_le_iff_le_sin, not_congr, not_le, not_le.symm.trans
-/
theorem lt_arcsin_iff_sin_lt' {x y : Real} (hx : x in Ico (-(π / 2)) (π / 2)) :
    x < arcsin y ↔ sin x < y :=
not_le.symm.trans (not_congr <| arcsin_le_iff_le_sin' hx).trans not_le

/--
theorem `arcsin_eq_iff_eq_sin` / 定理 `arcsin_eq_iff_eq_sin`

English:
theorem arcsin_eq_iff_eq_sin
  given: {x y : Real} (hy : y in Ioo (-(π / 2)) (π / 2))
  proof: by
  simp only [le_antisymm_iff, arcsin_le_iff_le_sin' (mem_Ico_of_Ioo hy),
    le_arcsin_iff_sin_le' (mem_Ioc_of_Ioo hy)]

@[simp]

中文:
定理 arcsin_eq_iff_eq_sin
  条件: {x y : 实数} (hy : y in 开区间 (-(π / 2)) (π / 2))
  证明: by
  simp only [le_antisymm_iff, arcsin_le_iff_le_sin' (mem_Ico_of_Ioo hy),
    le_arcsin_iff_sin_le' (mem_Ioc_of_Ioo hy)]

@[simp]

Depends on / 依赖: arcsin_le_iff_le_sin, le_antisymm_iff, le_arcsin_iff_sin_le, mem_Ico_of_Ioo, mem_Ioc_of_Ioo
-/
theorem arcsin_eq_iff_eq_sin {x y : Real} (hy : y in Ioo (-(π / 2)) (π / 2)) :
    arcsin x = y ↔ x = sin y := by
  simp only [le_antisymm_iff, arcsin_le_iff_le_sin' (mem_Ico_of_Ioo hy),
    le_arcsin_iff_sin_le' (mem_Ioc_of_Ioo hy)]

@[simp]
/--
theorem `arcsin_nonneg` / 定理 `arcsin_nonneg`

English:
theorem arcsin_nonneg
  given: {x : Real}
  statement: 0 <= arcsin x ↔ 0 <= x
  proof: (le_arcsin_iff_sin_le' ⟨neg_lt_zero.2 pi_div_two_pos, pi_div_two_pos.le⟩).trans by
    rw [sin_zero]

@[simp]

中文:
定理 arcsin_nonneg
  条件: {x : 实数}
  结论: 0 <= arcsin x ↔ 0 <= x
  证明: (le_arcsin_iff_sin_le' ⟨neg_lt_zero.2 pi_div_two_pos, pi_div_two_pos.le⟩).trans by
    rw [sin_zero]

@[simp]

Depends on / 依赖: le_arcsin_iff_sin_le, neg_lt_zero, pi_div_two_pos, pi_div_two_pos.le, sin_zero
-/
theorem arcsin_nonneg {x : Real} : 0 <= arcsin x ↔ 0 <= x :=
(le_arcsin_iff_sin_le' ⟨neg_lt_zero.2 pi_div_two_pos, pi_div_two_pos.le⟩).trans by
    rw [sin_zero]

@[simp]
/--
theorem `arcsin_nonpos` / 定理 `arcsin_nonpos`

English:
theorem arcsin_nonpos
  given: {x : Real}
  statement: arcsin x <= 0 ↔ x <= 0
  proof: neg_nonneg.symm.trans arcsin_neg x ▸ arcsin_nonneg.trans neg_nonneg

@[simp]

中文:
定理 arcsin_nonpos
  条件: {x : 实数}
  结论: arcsin x <= 0 ↔ x <= 0
  证明: neg_nonneg.symm.trans arcsin_neg x ▸ arcsin_nonneg.trans neg_nonneg

@[simp]

Depends on / 依赖: arcsin_neg, arcsin_nonneg, arcsin_nonneg.trans, neg_nonneg, neg_nonneg.symm.trans
-/
theorem arcsin_nonpos {x : Real} : arcsin x <= 0 ↔ x <= 0 :=
neg_nonneg.symm.trans arcsin_neg x ▸ arcsin_nonneg.trans neg_nonneg

@[simp]
/--
theorem `arcsin_eq_zero_iff` / 定理 `arcsin_eq_zero_iff`

English:
theorem arcsin_eq_zero_iff
  given: {x : Real}
  statement: arcsin x = 0 ↔ x = 0
  proof: by simp [le_antisymm_iff]

@[simp]

中文:
定理 arcsin_eq_zero_iff
  条件: {x : 实数}
  结论: arcsin x = 0 ↔ x = 0
  证明: by simp [le_antisymm_iff]

@[simp]

Depends on / 依赖: le_antisymm_iff
-/
theorem arcsin_eq_zero_iff {x : Real} : arcsin x = 0 ↔ x = 0 := by simp [le_antisymm_iff]

@[simp]
/--
theorem `zero_eq_arcsin_iff` / 定理 `zero_eq_arcsin_iff`

English:
theorem zero_eq_arcsin_iff
  given: {x}
  statement: 0 = arcsin x ↔ x = 0
  proof: eq_comm.trans arcsin_eq_zero_iff

@[simp]

中文:
定理 zero_eq_arcsin_iff
  条件: {x}
  结论: 0 = arcsin x ↔ x = 0
  证明: eq_comm.trans arcsin_eq_zero_iff

@[simp]

Depends on / 依赖: arcsin_eq_zero_iff, eq_comm, eq_comm.trans
-/
theorem zero_eq_arcsin_iff {x} : 0 = arcsin x ↔ x = 0 :=
  eq_comm.trans arcsin_eq_zero_iff

@[simp]
/--
theorem `arcsin_pos` / 定理 `arcsin_pos`

English:
theorem arcsin_pos
  given: {x : Real}
  statement: 0 < arcsin x ↔ 0 < x
  proof: lt_iff_lt_of_le_iff_le arcsin_nonpos

@[simp]

中文:
定理 arcsin_pos
  条件: {x : 实数}
  结论: 0 < arcsin x ↔ 0 < x
  证明: lt_iff_lt_of_le_iff_le arcsin_nonpos

@[simp]

Depends on / 依赖: arcsin_nonpos, lt_iff_lt_of_le_iff_le
-/
theorem arcsin_pos {x : Real} : 0 < arcsin x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arcsin_nonpos

@[simp]
/--
theorem `arcsin_lt_zero` / 定理 `arcsin_lt_zero`

English:
theorem arcsin_lt_zero
  given: {x : Real}
  statement: arcsin x < 0 ↔ x < 0
  proof: lt_iff_lt_of_le_iff_le arcsin_nonneg

@[simp]

中文:
定理 arcsin_lt_zero
  条件: {x : 实数}
  结论: arcsin x < 0 ↔ x < 0
  证明: lt_iff_lt_of_le_iff_le arcsin_nonneg

@[simp]

Depends on / 依赖: arcsin_nonneg, lt_iff_lt_of_le_iff_le
-/
theorem arcsin_lt_zero {x : Real} : arcsin x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arcsin_nonneg

@[simp]
/--
theorem `arcsin_lt_pi_div_two` / 定理 `arcsin_lt_pi_div_two`

English:
theorem arcsin_lt_pi_div_two
  given: {x : Real}
  statement: arcsin x < π / 2 ↔ x < 1
  proof: (arcsin_lt_iff_lt_sin' (right_mem_Ioc.2 <| neg_lt_self pi_div_two_pos)).trans by
    rw [sin_pi_div_two]

@[simp]

中文:
定理 arcsin_lt_pi_div_two
  条件: {x : 实数}
  结论: arcsin x < π / 2 ↔ x < 1
  证明: (arcsin_lt_iff_lt_sin' (right_mem_Ioc.2 <| neg_lt_self pi_div_two_pos)).trans by
    rw [sin_pi_div_two]

@[simp]

Depends on / 依赖: arcsin_lt_iff_lt_sin, neg_lt_self, pi_div_two_pos, right_mem_Ioc, sin_pi_div_two
-/
theorem arcsin_lt_pi_div_two {x : Real} : arcsin x < π / 2 ↔ x < 1 :=
(arcsin_lt_iff_lt_sin' (right_mem_Ioc.2 <| neg_lt_self pi_div_two_pos)).trans by
    rw [sin_pi_div_two]

@[simp]
/--
theorem `neg_pi_div_two_lt_arcsin` / 定理 `neg_pi_div_two_lt_arcsin`

English:
theorem neg_pi_div_two_lt_arcsin
  given: {x : Real}
  statement: -(π / 2) < arcsin x ↔ -1 < x
  proof: (lt_arcsin_iff_sin_lt' <| left_mem_Ico.2 <| neg_lt_self pi_div_two_pos).trans by
    rw [sin_neg]; rw [sin_pi_div_two]

@[simp]

中文:
定理 neg_pi_div_two_lt_arcsin
  条件: {x : 实数}
  结论: -(π / 2) < arcsin x ↔ -1 < x
  证明: (lt_arcsin_iff_sin_lt' <| left_mem_Ico.2 <| neg_lt_self pi_div_two_pos).trans by
    rw [sin_neg]; rw [sin_pi_div_two]

@[simp]

Depends on / 依赖: left_mem_Ico, lt_arcsin_iff_sin_lt, neg_lt_self, pi_div_two_pos, sin_neg, sin_pi_div_two
-/
theorem neg_pi_div_two_lt_arcsin {x : Real} : -(π / 2) < arcsin x ↔ -1 < x :=
(lt_arcsin_iff_sin_lt' <| left_mem_Ico.2 <| neg_lt_self pi_div_two_pos).trans by
    rw [sin_neg]; rw [sin_pi_div_two]

@[simp]
/--
theorem `arcsin_eq_pi_div_two` / 定理 `arcsin_eq_pi_div_two`

English:
theorem arcsin_eq_pi_div_two
  given: {x : Real}
  statement: arcsin x = π / 2 ↔ 1 <= x
  proof: ⟨fun h => not_lt.1 fun h' => (arcsin_lt_pi_div_two.2 h').ne h, arcsin_of_one_le⟩

@[simp]

中文:
定理 arcsin_eq_pi_div_two
  条件: {x : 实数}
  结论: arcsin x = π / 2 ↔ 1 <= x
  证明: ⟨fun h => not_lt.1 fun h' => (arcsin_lt_pi_div_two.2 h').ne h, arcsin_of_one_le⟩

@[simp]

Depends on / 依赖: arcsin_lt_pi_div_two, arcsin_of_one_le, not_lt
-/
theorem arcsin_eq_pi_div_two {x : Real} : arcsin x = π / 2 ↔ 1 <= x :=
  ⟨fun h => not_lt.1 fun h' => (arcsin_lt_pi_div_two.2 h').ne h, arcsin_of_one_le⟩

@[simp]
/--
theorem `pi_div_two_eq_arcsin` / 定理 `pi_div_two_eq_arcsin`

English:
theorem pi_div_two_eq_arcsin
  given: {x}
  statement: π / 2 = arcsin x ↔ 1 <= x
  proof: eq_comm.trans arcsin_eq_pi_div_two

@[simp]

中文:
定理 pi_div_two_eq_arcsin
  条件: {x}
  结论: π / 2 = arcsin x ↔ 1 <= x
  证明: eq_comm.trans arcsin_eq_pi_div_two

@[simp]

Depends on / 依赖: arcsin_eq_pi_div_two, eq_comm, eq_comm.trans
-/
theorem pi_div_two_eq_arcsin {x} : π / 2 = arcsin x ↔ 1 <= x :=
  eq_comm.trans arcsin_eq_pi_div_two

@[simp]
/--
theorem `pi_div_two_le_arcsin` / 定理 `pi_div_two_le_arcsin`

English:
theorem pi_div_two_le_arcsin
  given: {x}
  statement: π / 2 <= arcsin x ↔ 1 <= x
  proof: (arcsin_le_pi_div_two x).ge_iff_eq'.trans pi_div_two_eq_arcsin

@[simp]

中文:
定理 pi_div_two_le_arcsin
  条件: {x}
  结论: π / 2 <= arcsin x ↔ 1 <= x
  证明: (arcsin_le_pi_div_two x).ge_iff_eq'.trans pi_div_two_eq_arcsin

@[simp]

Depends on / 依赖: arcsin_le_pi_div_two, ge_iff_eq, pi_div_two_eq_arcsin
-/
theorem pi_div_two_le_arcsin {x} : π / 2 <= arcsin x ↔ 1 <= x :=
  (arcsin_le_pi_div_two x).ge_iff_eq'.trans pi_div_two_eq_arcsin

@[simp]
/--
theorem `arcsin_eq_neg_pi_div_two` / 定理 `arcsin_eq_neg_pi_div_two`

English:
theorem arcsin_eq_neg_pi_div_two
  given: {x : Real}
  statement: arcsin x = -(π / 2) ↔ x <= -1
  proof: ⟨fun h => not_lt.1 fun h' => (neg_pi_div_two_lt_arcsin.2 h').ne' h, arcsin_of_le_neg_one⟩

@[simp]

中文:
定理 arcsin_eq_neg_pi_div_two
  条件: {x : 实数}
  结论: arcsin x = -(π / 2) ↔ x <= -1
  证明: ⟨fun h => not_lt.1 fun h' => (neg_pi_div_two_lt_arcsin.2 h').ne' h, arcsin_of_le_neg_one⟩

@[simp]

Depends on / 依赖: arcsin_of_le_neg_one, neg_pi_div_two_lt_arcsin, not_lt
-/
theorem arcsin_eq_neg_pi_div_two {x : Real} : arcsin x = -(π / 2) ↔ x <= -1 :=
  ⟨fun h => not_lt.1 fun h' => (neg_pi_div_two_lt_arcsin.2 h').ne' h, arcsin_of_le_neg_one⟩

@[simp]
/--
theorem `neg_pi_div_two_eq_arcsin` / 定理 `neg_pi_div_two_eq_arcsin`

English:
theorem neg_pi_div_two_eq_arcsin
  given: {x}
  statement: -(π / 2) = arcsin x ↔ x <= -1
  proof: eq_comm.trans arcsin_eq_neg_pi_div_two

@[simp]

中文:
定理 neg_pi_div_two_eq_arcsin
  条件: {x}
  结论: -(π / 2) = arcsin x ↔ x <= -1
  证明: eq_comm.trans arcsin_eq_neg_pi_div_two

@[simp]

Depends on / 依赖: arcsin_eq_neg_pi_div_two, eq_comm, eq_comm.trans
-/
theorem neg_pi_div_two_eq_arcsin {x} : -(π / 2) = arcsin x ↔ x <= -1 :=
  eq_comm.trans arcsin_eq_neg_pi_div_two

@[simp]
/--
theorem `arcsin_le_neg_pi_div_two` / 定理 `arcsin_le_neg_pi_div_two`

English:
theorem arcsin_le_neg_pi_div_two
  given: {x}
  statement: arcsin x <= -(π / 2) ↔ x <= -1
  proof: (neg_pi_div_two_le_arcsin x).ge_iff_eq'.trans arcsin_eq_neg_pi_div_two

@[simp]

中文:
定理 arcsin_le_neg_pi_div_two
  条件: {x}
  结论: arcsin x <= -(π / 2) ↔ x <= -1
  证明: (neg_pi_div_two_le_arcsin x).ge_iff_eq'.trans arcsin_eq_neg_pi_div_two

@[simp]

Depends on / 依赖: arcsin_eq_neg_pi_div_two, ge_iff_eq, neg_pi_div_two_le_arcsin
-/
theorem arcsin_le_neg_pi_div_two {x} : arcsin x <= -(π / 2) ↔ x <= -1 :=
  (neg_pi_div_two_le_arcsin x).ge_iff_eq'.trans arcsin_eq_neg_pi_div_two

@[simp]
/--
theorem `pi_div_four_le_arcsin` / 定理 `pi_div_four_le_arcsin`

English:
theorem pi_div_four_le_arcsin
  given: {x}
  statement: π / 4 <= arcsin x ↔ √2 / 2 <= x
  proof: by
  rw [← sin_pi_div_four]; rw [le_arcsin_iff_sin_le']
  have := pi_pos
  constructor <;> linarith

中文:
定理 pi_div_four_le_arcsin
  条件: {x}
  结论: π / 4 <= arcsin x ↔ √2 / 2 <= x
  证明: by
  rw [← sin_pi_div_four]; rw [le_arcsin_iff_sin_le']
  have := pi_pos
  constructor <;> linarith

Depends on / 依赖: le_arcsin_iff_sin_le, pi_pos, sin_pi_div_four
-/
theorem pi_div_four_le_arcsin {x} : π / 4 <= arcsin x ↔ √2 / 2 <= x := by
  rw [← sin_pi_div_four]; rw [le_arcsin_iff_sin_le']
  have := pi_pos
  constructor <;> linarith

/--
theorem `cos_arcsin_nonneg` / 定理 `cos_arcsin_nonneg`

English:
theorem cos_arcsin_nonneg
  given: (x : Real)
  statement: 0 <= cos (arcsin x)
  proof: cos_nonneg_of_mem_Icc ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩

中文:
定理 cos_arcsin_nonneg
  条件: (x : 实数)
  结论: 0 <= cos (arcsin x)
  证明: cos_nonneg_of_mem_Icc ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩

Depends on / 依赖: arcsin_le_pi_div_two, cos_nonneg_of_mem_Icc, neg_pi_div_two_le_arcsin
-/
theorem cos_arcsin_nonneg (x : Real) : 0 <= cos (arcsin x) :=
  cos_nonneg_of_mem_Icc ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩

-- The junk values for `arcsin` and `sqrt` make this true even outside `[-1, 1]`.
/--
theorem `cos_arcsin` / 定理 `cos_arcsin`

English:
theorem cos_arcsin
  given: (x : Real)
  statement: cos (arcsin x) = √(1 - x ^ 2)
  proof: by
  by_cases hx₁ : -1 <= x; swap
  · rw [not_le] at hx₁
    rw [arcsin_of_le_neg_one hx₁.le]; rw [cos_neg]; rw [cos_pi_div_two]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x <= 1; swap
  · rw [not_le] at hx₂
    rw [arcsin_of_one_le hx₂.le]; rw [cos_pi_div_two]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  have : sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x)
  rw [← eq_sub_iff_add_eq']; rw [← sqrt_inj (sq_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x)))]; rw [sq]; rw [sqrt_mul_self (cos_arcsin_nonneg _)] at this
  rw [this]; rw [sin_arcsin hx₁ hx₂]

中文:
定理 cos_arcsin
  条件: (x : 实数)
  结论: cos (arcsin x) = √(1 - x ^ 2)
  证明: by
  by_cases hx₁ : -1 <= x; swap
  · rw [not_le] at hx₁
    rw [arcsin_of_le_neg_one hx₁.le]; rw [cos_neg]; rw [cos_pi_div_two]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x <= 1; swap
  · rw [not_le] at hx₂
    rw [arcsin_of_one_le hx₂.le]; rw [cos_pi_div_two]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  have : sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x)
  rw [← eq_sub_iff_add_eq']; rw [← sqrt_inj (sq_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x)))]; rw [sq]; rw [sqrt_mul_self (cos_arcsin_nonneg _)] at this
  rw [this]; rw [sin_arcsin hx₁ hx₂]

Depends on / 依赖: arcsin, arcsin_of_le_neg_one, arcsin_of_one_le, cos_neg, cos_pi_div_two, eq_sub_iff_add_eq, not_le, sin_sq_add_cos_sq, sin_sq_le_one, sq_nonneg, sqrt_eq_zero_of_nonpos, sqrt_inj, sqrt_m, sub_nonneg
-/
theorem cos_arcsin (x : Real) : cos (arcsin x) = √(1 - x ^ 2) := by
  by_cases hx₁ : -1 <= x; swap
  · rw [not_le] at hx₁
    rw [arcsin_of_le_neg_one hx₁.le]; rw [cos_neg]; rw [cos_pi_div_two]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x <= 1; swap
  · rw [not_le] at hx₂
    rw [arcsin_of_one_le hx₂.le]; rw [cos_pi_div_two]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  have : sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x)
  rw [← eq_sub_iff_add_eq']; rw [← sqrt_inj (sq_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x)))]; rw [sq]; rw [sqrt_mul_self (cos_arcsin_nonneg _)] at this
  rw [this]; rw [sin_arcsin hx₁ hx₂]

-- The junk values for `arcsin` and `sqrt` make this true even outside `[-1, 1]`.
/--
theorem `tan_arcsin` / 定理 `tan_arcsin`

English:
theorem tan_arcsin
  given: (x : Real)
  statement: tan (arcsin x) = x / √(1 - x ^ 2)
  proof: by
  rw [tan_eq_sin_div_cos]; rw [cos_arcsin]
  by_cases hx₁ : -1 <= x; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  by_cases hx₂ : x <= 1; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  rw [sin_arcsin hx₁ hx₂]

中文:
定理 tan_arcsin
  条件: (x : 实数)
  结论: tan (arcsin x) = x / √(1 - x ^ 2)
  证明: by
  rw [tan_eq_sin_div_cos]; rw [cos_arcsin]
  by_cases hx₁ : -1 <= x; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  by_cases hx₂ : x <= 1; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  rw [sin_arcsin hx₁ hx₂]

Depends on / 依赖: cos_arcsin, sin_arcsin, sqrt_eq_zero_of_nonpos, tan_eq_sin_div_cos
-/
theorem tan_arcsin (x : Real) : tan (arcsin x) = x / √(1 - x ^ 2) := by
  rw [tan_eq_sin_div_cos]; rw [cos_arcsin]
  by_cases hx₁ : -1 <= x; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  by_cases hx₂ : x <= 1; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  rw [sin_arcsin hx₁ hx₂]

/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  It defaults to `π` on `(-∞, -1)` and to `0` to `(1, ∞)`. -/
@[pp_nodot]
/--
Definition of `arccos` / `arccos` 的定义

English:
definition arccos
  signature: (x : Real)
  body: π / 2 - arcsin x

中文:
定义 arccos
  签名: (x : 实数)
  定义体: π / 2 - arcsin x

Depends on / 依赖: arcsin
-/
noncomputable def arccos (x : Real) : Real :=
  π / 2 - arcsin x

/--
theorem `arccos_eq_pi_div_two_sub_arcsin` / 定理 `arccos_eq_pi_div_two_sub_arcsin`

English:
theorem arccos_eq_pi_div_two_sub_arcsin
  given: (x : Real)
  statement: arccos x = π / 2 - arcsin x
  proof: rfl

中文:
定理 arccos_eq_pi_div_two_sub_arcsin
  条件: (x : 实数)
  结论: arccos x = π / 2 - arcsin x
  证明: rfl
-/
theorem arccos_eq_pi_div_two_sub_arcsin (x : Real) : arccos x = π / 2 - arcsin x :=
  rfl

/--
theorem `arcsin_eq_pi_div_two_sub_arccos` / 定理 `arcsin_eq_pi_div_two_sub_arccos`

English:
theorem arcsin_eq_pi_div_two_sub_arccos
  given: (x : Real)
  statement: arcsin x = π / 2 - arccos x
  proof: by simp [arccos]

中文:
定理 arcsin_eq_pi_div_two_sub_arccos
  条件: (x : 实数)
  结论: arcsin x = π / 2 - arccos x
  证明: by simp [arccos]

Depends on / 依赖: arccos
-/
theorem arcsin_eq_pi_div_two_sub_arccos (x : Real) : arcsin x = π / 2 - arccos x := by simp [arccos]

/--
theorem `arccos_le_pi` / 定理 `arccos_le_pi`

English:
theorem arccos_le_pi
  given: (x : Real)
  statement: arccos x <= π
  proof: by
  unfold arccos; linarith [neg_pi_div_two_le_arcsin x]

中文:
定理 arccos_le_pi
  条件: (x : 实数)
  结论: arccos x <= π
  证明: by
  unfold arccos; linarith [neg_pi_div_two_le_arcsin x]

Depends on / 依赖: arccos, neg_pi_div_two_le_arcsin
-/
theorem arccos_le_pi (x : Real) : arccos x <= π := by
  unfold arccos; linarith [neg_pi_div_two_le_arcsin x]

/--
theorem `arccos_nonneg` / 定理 `arccos_nonneg`

English:
theorem arccos_nonneg
  given: (x : Real)
  statement: 0 <= arccos x
  proof: by
  unfold arccos; linarith [arcsin_le_pi_div_two x]

@[simp]

中文:
定理 arccos_nonneg
  条件: (x : 实数)
  结论: 0 <= arccos x
  证明: by
  unfold arccos; linarith [arcsin_le_pi_div_two x]

@[simp]

Depends on / 依赖: arccos, arcsin_le_pi_div_two
-/
theorem arccos_nonneg (x : Real) : 0 <= arccos x := by
  unfold arccos; linarith [arcsin_le_pi_div_two x]

@[simp]
/--
theorem `arccos_pos` / 定理 `arccos_pos`

English:
theorem arccos_pos
  given: {x : Real}
  statement: 0 < arccos x ↔ x < 1
  proof: by simp [arccos]

中文:
定理 arccos_pos
  条件: {x : 实数}
  结论: 0 < arccos x ↔ x < 1
  证明: by simp [arccos]

Depends on / 依赖: arccos
-/
theorem arccos_pos {x : Real} : 0 < arccos x ↔ x < 1 := by simp [arccos]

/--
theorem `cos_arccos` / 定理 `cos_arccos`

English:
theorem cos_arccos
  given: {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1)
  statement: cos (arccos x) = x
  proof: by
  rw [arccos]; rw [cos_pi_div_two_sub]; rw [sin_arcsin hx₁ hx₂]

中文:
定理 cos_arccos
  条件: {x : 实数} (hx₁ : -1 <= x) (hx₂ : x <= 1)
  结论: cos (arccos x) = x
  证明: by
  rw [arccos]; rw [cos_pi_div_two_sub]; rw [sin_arcsin hx₁ hx₂]

Depends on / 依赖: arccos, cos_pi_div_two_sub, sin_arcsin
-/
theorem cos_arccos {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : cos (arccos x) = x := by
  rw [arccos]; rw [cos_pi_div_two_sub]; rw [sin_arcsin hx₁ hx₂]

/--
theorem `arccos_cos` / 定理 `arccos_cos`

English:
theorem arccos_cos
  given: {x : Real} (hx₁ : 0 <= x) (hx₂ : x <= π)
  statement: arccos (cos x) = x
  proof: by
  rw [arccos]; rw [← sin_pi_div_two_sub]; rw [arcsin_sin] <;> simp [sub_eq_add_neg] <;> linarith

中文:
定理 arccos_cos
  条件: {x : 实数} (hx₁ : 0 <= x) (hx₂ : x <= π)
  结论: arccos (cos x) = x
  证明: by
  rw [arccos]; rw [← sin_pi_div_two_sub]; rw [arcsin_sin] <;> simp [sub_eq_add_neg] <;> linarith

Depends on / 依赖: arccos, arcsin_sin, sin_pi_div_two_sub, sub_eq_add_neg
-/
theorem arccos_cos {x : Real} (hx₁ : 0 <= x) (hx₂ : x <= π) : arccos (cos x) = x := by
  rw [arccos]; rw [← sin_pi_div_two_sub]; rw [arcsin_sin] <;> simp [sub_eq_add_neg] <;> linarith

/--
lemma `arccos_eq_of_eq_cos` / 引理 `arccos_eq_of_eq_cos`

English:
lemma arccos_eq_of_eq_cos
  given: (hy₀ : 0 <= y) (hy₁ : y <= π) (hxy : x = cos y)
  statement: arccos x = y
  proof: by
  rw [hxy]; rw [arccos_cos hy₀ hy₁]

中文:
引理 arccos_eq_of_eq_cos
  条件: (hy₀ : 0 <= y) (hy₁ : y <= π) (hxy : x = cos y)
  结论: arccos x = y
  证明: by
  rw [hxy]; rw [arccos_cos hy₀ hy₁]

Depends on / 依赖: arccos_cos
-/
lemma arccos_eq_of_eq_cos (hy₀ : 0 <= y) (hy₁ : y <= π) (hxy : x = cos y) : arccos x = y := by
  rw [hxy]; rw [arccos_cos hy₀ hy₁]

/--
theorem `strictAntiOn_arccos` / 定理 `strictAntiOn_arccos`

English:
theorem strictAntiOn_arccos
  statement: StrictAntiOn arccos (Icc (-1) 1)
  proof: fun _ hx _ hy h =>
  sub_lt_sub_left (strictMonoOn_arcsin hx hy h) _

@[gcongr]

中文:
定理 strictAntiOn_arccos
  结论: StrictAntiOn arccos (闭区间 (-1) 1)
  证明: fun _ hx _ hy h =>
  sub_lt_sub_left (strictMonoOn_arcsin hx hy h) _

@[gcongr]
-/
theorem strictAntiOn_arccos : StrictAntiOn arccos (Icc (-1) 1) := fun _ hx _ hy h =>
  sub_lt_sub_left (strictMonoOn_arcsin hx hy h) _

@[gcongr]
/--
lemma `arccos_lt_arccos` / 引理 `arccos_lt_arccos`

English:
lemma arccos_lt_arccos
  given: {x y : Real} (hx : -1 <= x) (hlt : x < y) (hy : y <= 1)
  proof: by
  unfold arccos; gcongr

@[gcongr]

中文:
引理 arccos_lt_arccos
  条件: {x y : 实数} (hx : -1 <= x) (hlt : x < y) (hy : y <= 1)
  证明: by
  unfold arccos; gcongr

@[gcongr]

Depends on / 依赖: arccos
-/
lemma arccos_lt_arccos {x y : Real} (hx : -1 <= x) (hlt : x < y) (hy : y <= 1) :
    arccos y < arccos x := by
  unfold arccos; gcongr

@[gcongr]
/--
lemma `arccos_le_arccos` / 引理 `arccos_le_arccos`

English:
lemma arccos_le_arccos
  given: {x y : Real} (hlt : x <= y)
  statement: arccos y <= arccos x
  proof: by unfold arccos; gcongr

中文:
引理 arccos_le_arccos
  条件: {x y : 实数} (hlt : x <= y)
  结论: arccos y <= arccos x
  证明: by unfold arccos; gcongr

Depends on / 依赖: arccos
-/
lemma arccos_le_arccos {x y : Real} (hlt : x <= y) : arccos y <= arccos x := by unfold arccos; gcongr

/--
theorem `antitone_arccos` / 定理 `antitone_arccos`

English:
theorem antitone_arccos
  statement: Antitone arccos
  proof: fun _ _ => arccos_le_arccos

中文:
定理 antitone_arccos
  结论: 递减 arccos
  证明: fun _ _ => arccos_le_arccos

Depends on / 依赖: arccos_le_arccos
-/
theorem antitone_arccos : Antitone arccos := fun _ _ => arccos_le_arccos

/--
theorem `arccos_injOn` / 定理 `arccos_injOn`

English:
theorem arccos_injOn
  statement: InjOn arccos (Icc (-1) 1)
  proof: strictAntiOn_arccos.injOn

中文:
定理 arccos_injOn
  结论: 单射限制 arccos (闭区间 (-1) 1)
  证明: strictAntiOn_arccos.injOn

Depends on / 依赖: strictAntiOn_arccos, strictAntiOn_arccos.injOn
-/
theorem arccos_injOn : InjOn arccos (Icc (-1) 1) :=
  strictAntiOn_arccos.injOn

/--
theorem `arccos_inj` / 定理 `arccos_inj`

English:
theorem arccos_inj
  given: {x y : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) (hy₁ : -1 <= y) (hy₂ : y <= 1)
  proof: arccos_injOn.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[simp]

中文:
定理 arccos_inj
  条件: {x y : 实数} (hx₁ : -1 <= x) (hx₂ : x <= 1) (hy₁ : -1 <= y) (hy₂ : y <= 1)
  证明: arccos_injOn.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[simp]

Depends on / 依赖: arccos_injOn, arccos_injOn.eq_iff, eq_iff
-/
theorem arccos_inj {x y : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) (hy₁ : -1 <= y) (hy₂ : y <= 1) :
    arccos x = arccos y ↔ x = y :=
  arccos_injOn.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[simp]
/--
theorem `arccos_zero` / 定理 `arccos_zero`

English:
theorem arccos_zero
  statement: arccos 0 = π / 2
  proof: by simp [arccos]

@[simp]

中文:
定理 arccos_zero
  结论: arccos 0 = π / 2
  证明: by simp [arccos]

@[simp]

Depends on / 依赖: arccos
-/
theorem arccos_zero : arccos 0 = π / 2 := by simp [arccos]

@[simp]
/--
theorem `arccos_one` / 定理 `arccos_one`

English:
theorem arccos_one
  statement: arccos 1 = 0
  proof: by simp [arccos]

@[simp]

中文:
定理 arccos_one
  结论: arccos 1 = 0
  证明: by simp [arccos]

@[simp]

Depends on / 依赖: arccos
-/
theorem arccos_one : arccos 1 = 0 := by simp [arccos]

@[simp]
/--
theorem `arccos_neg_one` / 定理 `arccos_neg_one`

English:
theorem arccos_neg_one
  statement: arccos (-1) = π
  proof: by simp [arccos, add_halves]

@[simp]

中文:
定理 arccos_neg_one
  结论: arccos (-1) = π
  证明: by simp [arccos, add_halves]

@[simp]

Depends on / 依赖: add_halves, arccos
-/
theorem arccos_neg_one : arccos (-1) = π := by simp [arccos, add_halves]

@[simp]
/--
theorem `arccos_eq_zero` / 定理 `arccos_eq_zero`

English:
theorem arccos_eq_zero
  given: {x}
  statement: arccos x = 0 ↔ 1 <= x
  proof: by simp [arccos, sub_eq_zero]

@[simp]

中文:
定理 arccos_eq_zero
  条件: {x}
  结论: arccos x = 0 ↔ 1 <= x
  证明: by simp [arccos, sub_eq_zero]

@[simp]

Depends on / 依赖: arccos, sub_eq_zero
-/
theorem arccos_eq_zero {x} : arccos x = 0 ↔ 1 <= x := by simp [arccos, sub_eq_zero]

@[simp]
/--
theorem `arccos_eq_pi_div_two` / 定理 `arccos_eq_pi_div_two`

English:
theorem arccos_eq_pi_div_two
  given: {x}
  statement: arccos x = π / 2 ↔ x = 0
  proof: by simp [arccos]

@[simp]

中文:
定理 arccos_eq_pi_div_two
  条件: {x}
  结论: arccos x = π / 2 ↔ x = 0
  证明: by simp [arccos]

@[simp]

Depends on / 依赖: arccos
-/
theorem arccos_eq_pi_div_two {x} : arccos x = π / 2 ↔ x = 0 := by simp [arccos]

@[simp]
/--
theorem `arccos_eq_pi` / 定理 `arccos_eq_pi`

English:
theorem arccos_eq_pi
  given: {x}
  statement: arccos x = π ↔ x <= -1
  proof: by
  rw [arccos]; rw [sub_eq_iff_eq_add]; rw [← sub_eq_iff_eq_add']; rw [div_two_sub_self]; rw [neg_pi_div_two_eq_arcsin]

中文:
定理 arccos_eq_pi
  条件: {x}
  结论: arccos x = π ↔ x <= -1
  证明: by
  rw [arccos]; rw [sub_eq_iff_eq_add]; rw [← sub_eq_iff_eq_add']; rw [div_two_sub_self]; rw [neg_pi_div_two_eq_arcsin]

Depends on / 依赖: arccos, div_two_sub_self, neg_pi_div_two_eq_arcsin, sub_eq_iff_eq_add
-/
theorem arccos_eq_pi {x} : arccos x = π ↔ x <= -1 := by
  rw [arccos]; rw [sub_eq_iff_eq_add]; rw [← sub_eq_iff_eq_add']; rw [div_two_sub_self]; rw [neg_pi_div_two_eq_arcsin]

/--
theorem `arccos_lt_pi` / 定理 `arccos_lt_pi`

English:
theorem arccos_lt_pi
  given: {x}
  statement: arccos x < π ↔ -1 < x
  proof: by grind [arccos_le_pi, arccos_eq_pi]

中文:
定理 arccos_lt_pi
  条件: {x}
  结论: arccos x < π ↔ -1 < x
  证明: by grind [arccos_le_pi, arccos_eq_pi]

Depends on / 依赖: arccos_eq_pi, arccos_le_pi
-/
theorem arccos_lt_pi {x} : arccos x < π ↔ -1 < x := by grind [arccos_le_pi, arccos_eq_pi]

/--
theorem `arccos_neg` / 定理 `arccos_neg`

English:
theorem arccos_neg
  given: (x : Real)
  statement: arccos (-x) = π - arccos x
  proof: by
  rw [← add_halves π]; rw [arccos]; rw [arcsin_neg]; rw [arccos]; rw [add_sub_assoc]; rw [sub_sub_self]; rw [sub_neg_eq_add]

中文:
定理 arccos_neg
  条件: (x : 实数)
  结论: arccos (-x) = π - arccos x
  证明: by
  rw [← add_halves π]; rw [arccos]; rw [arcsin_neg]; rw [arccos]; rw [add_sub_assoc]; rw [sub_sub_self]; rw [sub_neg_eq_add]

Depends on / 依赖: add_halves, add_sub_assoc, arccos, arcsin_neg, sub_neg_eq_add, sub_sub_self
-/
theorem arccos_neg (x : Real) : arccos (-x) = π - arccos x := by
  rw [← add_halves π]; rw [arccos]; rw [arcsin_neg]; rw [arccos]; rw [add_sub_assoc]; rw [sub_sub_self]; rw [sub_neg_eq_add]

/--
theorem `arccos_of_one_le` / 定理 `arccos_of_one_le`

English:
theorem arccos_of_one_le
  given: {x : Real} (hx : 1 <= x)
  statement: arccos x = 0
  proof: by
  rw [arccos]; rw [arcsin_of_one_le hx]; rw [sub_self]

中文:
定理 arccos_of_one_le
  条件: {x : 实数} (hx : 1 <= x)
  结论: arccos x = 0
  证明: by
  rw [arccos]; rw [arcsin_of_one_le hx]; rw [sub_self]

Depends on / 依赖: arccos, arcsin_of_one_le, sub_self
-/
theorem arccos_of_one_le {x : Real} (hx : 1 <= x) : arccos x = 0 := by
  rw [arccos]; rw [arcsin_of_one_le hx]; rw [sub_self]

/--
theorem `arccos_of_le_neg_one` / 定理 `arccos_of_le_neg_one`

English:
theorem arccos_of_le_neg_one
  given: {x : Real} (hx : x <= -1)
  statement: arccos x = π
  proof: by
  rw [arccos]; rw [arcsin_of_le_neg_one hx]; rw [sub_neg_eq_add]; rw [add_halves]

中文:
定理 arccos_of_le_neg_one
  条件: {x : 实数} (hx : x <= -1)
  结论: arccos x = π
  证明: by
  rw [arccos]; rw [arcsin_of_le_neg_one hx]; rw [sub_neg_eq_add]; rw [add_halves]

Depends on / 依赖: add_halves, arccos, arcsin_of_le_neg_one, sub_neg_eq_add
-/
theorem arccos_of_le_neg_one {x : Real} (hx : x <= -1) : arccos x = π := by
  rw [arccos]; rw [arcsin_of_le_neg_one hx]; rw [sub_neg_eq_add]; rw [add_halves]

-- The junk values for `arccos` and `sqrt` make this true even outside `[-1, 1]`.
/--
theorem `sin_arccos` / 定理 `sin_arccos`

English:
theorem sin_arccos
  given: (x : Real)
  statement: sin (arccos x) = √(1 - x ^ 2)
  proof: by
  by_cases hx₁ : -1 <= x; swap
  · rw [not_le] at hx₁
    rw [arccos_of_le_neg_one hx₁.le]; rw [sin_pi]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x <= 1; swap
  · rw [not_le] at hx₂
    rw [arccos_of_one_le hx₂.le]; rw [sin_zero]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  rw [arccos_eq_pi_div_two_sub_arcsin]; rw [sin_pi_div_two_sub]; rw [cos_arcsin]

@[simp]

中文:
定理 sin_arccos
  条件: (x : 实数)
  结论: sin (arccos x) = √(1 - x ^ 2)
  证明: by
  by_cases hx₁ : -1 <= x; swap
  · rw [not_le] at hx₁
    rw [arccos_of_le_neg_one hx₁.le]; rw [sin_pi]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x <= 1; swap
  · rw [not_le] at hx₂
    rw [arccos_of_one_le hx₂.le]; rw [sin_zero]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  rw [arccos_eq_pi_div_two_sub_arcsin]; rw [sin_pi_div_two_sub]; rw [cos_arcsin]

@[simp]

Depends on / 依赖: arccos_eq_pi_div_two_sub_arcsin, arccos_of_le_neg_one, arccos_of_one_le, cos_arcsin, not_le, sin_pi, sin_pi_div_two_sub, sin_zero, sqrt_eq_zero_of_nonpos
-/
theorem sin_arccos (x : Real) : sin (arccos x) = √(1 - x ^ 2) := by
  by_cases hx₁ : -1 <= x; swap
  · rw [not_le] at hx₁
    rw [arccos_of_le_neg_one hx₁.le]; rw [sin_pi]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x <= 1; swap
  · rw [not_le] at hx₂
    rw [arccos_of_one_le hx₂.le]; rw [sin_zero]; rw [sqrt_eq_zero_of_nonpos]
    nlinarith
  rw [arccos_eq_pi_div_two_sub_arcsin]; rw [sin_pi_div_two_sub]; rw [cos_arcsin]

@[simp]
/--
theorem `arccos_le_pi_div_two` / 定理 `arccos_le_pi_div_two`

English:
theorem arccos_le_pi_div_two
  given: {x}
  statement: arccos x <= π / 2 ↔ 0 <= x
  proof: by simp [arccos]

@[simp]

中文:
定理 arccos_le_pi_div_two
  条件: {x}
  结论: arccos x <= π / 2 ↔ 0 <= x
  证明: by simp [arccos]

@[simp]

Depends on / 依赖: arccos
-/
theorem arccos_le_pi_div_two {x} : arccos x <= π / 2 ↔ 0 <= x := by simp [arccos]

@[simp]
/--
theorem `arccos_lt_pi_div_two` / 定理 `arccos_lt_pi_div_two`

English:
theorem arccos_lt_pi_div_two
  given: {x : Real}
  statement: arccos x < π / 2 ↔ 0 < x
  proof: by simp [arccos]

@[simp]

中文:
定理 arccos_lt_pi_div_two
  条件: {x : 实数}
  结论: arccos x < π / 2 ↔ 0 < x
  证明: by simp [arccos]

@[simp]

Depends on / 依赖: arccos
-/
theorem arccos_lt_pi_div_two {x : Real} : arccos x < π / 2 ↔ 0 < x := by simp [arccos]

@[simp]
/--
theorem `arccos_le_pi_div_four` / 定理 `arccos_le_pi_div_four`

English:
theorem arccos_le_pi_div_four
  given: {x}
  statement: arccos x <= π / 4 ↔ √2 / 2 <= x
  proof: by
  rw [arccos]; rw [← pi_div_four_le_arcsin]
  constructor <;>
    · intro
      linarith

@[continuity, fun_prop]

中文:
定理 arccos_le_pi_div_four
  条件: {x}
  结论: arccos x <= π / 4 ↔ √2 / 2 <= x
  证明: by
  rw [arccos]; rw [← pi_div_four_le_arcsin]
  constructor <;>
    · intro
      linarith

@[continuity, fun_prop]

Depends on / 依赖: arccos, pi_div_four_le_arcsin
-/
theorem arccos_le_pi_div_four {x} : arccos x <= π / 4 ↔ √2 / 2 <= x := by
  rw [arccos]; rw [← pi_div_four_le_arcsin]
  constructor <;>
    · intro
      linarith

@[continuity, fun_prop]
/--
theorem `continuous_arccos` / 定理 `continuous_arccos`

English:
theorem continuous_arccos
  statement: Continuous arccos
  proof: continuous_const.sub continuous_arcsin

中文:
定理 continuous_arccos
  结论: 连续 arccos
  证明: continuous_const.sub continuous_arcsin

Depends on / 依赖: continuous_arcsin, continuous_const, continuous_const.sub
-/
theorem continuous_arccos : Continuous arccos :=
  continuous_const.sub continuous_arcsin

-- The junk values for `arccos` and `sqrt` make this true even outside `[-1, 1]`.
/--
theorem `tan_arccos` / 定理 `tan_arccos`

English:
theorem tan_arccos
  given: (x : Real)
  statement: tan (arccos x) = √(1 - x ^ 2) / x
  proof: by
  rw [arccos]; rw [tan_pi_div_two_sub]; rw [tan_arcsin]; rw [inv_div]

中文:
定理 tan_arccos
  条件: (x : 实数)
  结论: tan (arccos x) = √(1 - x ^ 2) / x
  证明: by
  rw [arccos]; rw [tan_pi_div_two_sub]; rw [tan_arcsin]; rw [inv_div]

Depends on / 依赖: arccos, inv_div, tan_arcsin, tan_pi_div_two_sub
-/
theorem tan_arccos (x : Real) : tan (arccos x) = √(1 - x ^ 2) / x := by
  rw [arccos]; rw [tan_pi_div_two_sub]; rw [tan_arcsin]; rw [inv_div]

-- The junk values for `arccos` and `sqrt` make this true even for `1 < x`.
/--
theorem `arccos_eq_arcsin` / 定理 `arccos_eq_arcsin`

English:
theorem arccos_eq_arcsin
  given: {x : Real} (h : 0 <= x)
  statement: arccos x = arcsin (√(1 - x ^ 2))
  proof: (arcsin_eq_of_sin_eq (sin_arccos _)
      ⟨(Left.neg_nonpos_iff.2 (div_nonneg pi_pos.le (by simp))).trans (arccos_nonneg _),
        arccos_le_pi_div_two.2 h⟩).symm

中文:
定理 arccos_eq_arcsin
  条件: {x : 实数} (h : 0 <= x)
  结论: arccos x = arcsin (√(1 - x ^ 2))
  证明: (arcsin_eq_of_sin_eq (sin_arccos _)
      ⟨(Left.neg_nonpos_iff.2 (div_nonneg pi_pos.le (by simp))).trans (arccos_nonneg _),
        arccos_le_pi_div_two.2 h⟩).symm

Depends on / 依赖: Left.neg_nonpos_iff, arccos_le_pi_div_two, arccos_nonneg, arcsin_eq_of_sin_eq, div_nonneg, neg_nonpos_iff, pi_pos, pi_pos.le, sin_arccos
-/
theorem arccos_eq_arcsin {x : Real} (h : 0 <= x) : arccos x = arcsin (√(1 - x ^ 2)) :=
  (arcsin_eq_of_sin_eq (sin_arccos _)
      ⟨(Left.neg_nonpos_iff.2 (div_nonneg pi_pos.le (by simp))).trans (arccos_nonneg _),
        arccos_le_pi_div_two.2 h⟩).symm

-- The junk values for `arcsin` and `sqrt` make this true even for `1 < x`.
/--
theorem `arcsin_eq_arccos` / 定理 `arcsin_eq_arccos`

English:
theorem arcsin_eq_arccos
  given: {x : Real} (h : 0 <= x)
  statement: arcsin x = arccos (√(1 - x ^ 2))
  proof: by
  rw [eq_comm]; rw [← cos_arcsin]
  exact
    arccos_cos (arcsin_nonneg.2 h)
      ((arcsin_le_pi_div_two _).trans (div_le_self pi_pos.le one_le_two))

中文:
定理 arcsin_eq_arccos
  条件: {x : 实数} (h : 0 <= x)
  结论: arcsin x = arccos (√(1 - x ^ 2))
  证明: by
  rw [eq_comm]; rw [← cos_arcsin]
  exact
    arccos_cos (arcsin_nonneg.2 h)
      ((arcsin_le_pi_div_two _).trans (div_le_self pi_pos.le one_le_two))

Depends on / 依赖: arccos_cos, arcsin_le_pi_div_two, arcsin_nonneg, cos_arcsin, div_le_self, eq_comm, one_le_two, pi_pos, pi_pos.le
-/
theorem arcsin_eq_arccos {x : Real} (h : 0 <= x) : arcsin x = arccos (√(1 - x ^ 2)) := by
  rw [eq_comm]; rw [← cos_arcsin]
  exact
    arccos_cos (arcsin_nonneg.2 h)
      ((arcsin_le_pi_div_two _).trans (div_le_self pi_pos.le one_le_two))

/-- `Real.sin` as an `OpenPartialHomeomorph` between `(-π / 2, π / 2)` and `(-1, 1)`. -/
@[simp]
/--
Definition of `sinPartialHomeomorph` / `sinPartialHomeomorph` 的定义

English:
definition sinPartialHomeomorph
  signature: : OpenPartialHomeomorph Real Real where
  body: sin
  invFun := arcsin
  source := Ioo (-(π / 2)) (π / 2)
  target := Ioo (-1) 1
  map_source' := by grind [arcsin_lt_pi_div_two, neg_pi_div_two_lt_arcsin, arcsin_sin]
  map_target' _ hy := ⟨neg_pi_div_two_lt_arcsin.2 hy.1, arcsin_lt_pi_div_two.2 hy.2⟩
  left_inv' _ hx := arcsin_sin hx.1.le hx.2.le
  right_inv' _ hy := sin_arcsin hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_sin.continuousOn
  continuousOn_invFun := continuous_arcsin.continuousOn

中文:
定义 sinPartialHomeomorph
  签名: : OpenPartialHomeomorph 实数 实数 where
  定义体: sin
  invFun := arcsin
  source := Ioo (-(π / 2)) (π / 2)
  target := Ioo (-1) 1
  map_source' := by grind [arcsin_lt_pi_div_two, neg_pi_div_two_lt_arcsin, arcsin_sin]
  map_target' _ hy := ⟨neg_pi_div_two_lt_arcsin.2 hy.1, arcsin_lt_pi_div_two.2 hy.2⟩
  left_inv' _ hx := arcsin_sin hx.1.le hx.2.le
  right_inv' _ hy := sin_arcsin hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_sin.continuousOn
  continuousOn_invFun := continuous_arcsin.continuousOn
-/
def sinPartialHomeomorph : OpenPartialHomeomorph Real Real where
  toFun := sin
  invFun := arcsin
  source := Ioo (-(π / 2)) (π / 2)
  target := Ioo (-1) 1
  map_source' := by grind [arcsin_lt_pi_div_two, neg_pi_div_two_lt_arcsin, arcsin_sin]
  map_target' _ hy := ⟨neg_pi_div_two_lt_arcsin.2 hy.1, arcsin_lt_pi_div_two.2 hy.2⟩
  left_inv' _ hx := arcsin_sin hx.1.le hx.2.le
  right_inv' _ hy := sin_arcsin hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_sin.continuousOn
  continuousOn_invFun := continuous_arcsin.continuousOn

/-- `Real.sin` and `Real.arcsin` as a (partial) equivalence from `[-(π / 2), (π / 2)]` to
`[-1, 1]` -/
@[simp]
/--
Definition of `sinPartialEquiv` / `sinPartialEquiv` 的定义

English:
definition sinPartialEquiv
  signature: : PartialEquiv Real Real where
  body: sin
  invFun := arcsin
  source := Icc (-(π / 2)) (π / 2)
  target := Icc (-1) 1
  map_source' x hx := by simpa [← abs_le] using abs_sin_le_one x
  map_target' θ hθ := arcsin_mem_Icc θ
  left_inv' θ hθ := arcsin_sin (by aesop) (by aesop)
  right_inv' x hx := sin_arcsin (by aesop) (by aesop)

中文:
定义 sinPartialEquiv
  签名: : 部分等价 实数 实数 where
  定义体: sin
  invFun := arcsin
  source := Icc (-(π / 2)) (π / 2)
  target := Icc (-1) 1
  map_source' x hx := by simpa [← abs_le] using abs_sin_le_one x
  map_target' θ hθ := arcsin_mem_Icc θ
  left_inv' θ hθ := arcsin_sin (by aesop) (by aesop)
  right_inv' x hx := sin_arcsin (by aesop) (by aesop)
-/
def sinPartialEquiv : PartialEquiv Real Real where
  toFun := sin
  invFun := arcsin
  source := Icc (-(π / 2)) (π / 2)
  target := Icc (-1) 1
  map_source' x hx := by simpa [← abs_le] using abs_sin_le_one x
  map_target' θ hθ := arcsin_mem_Icc θ
  left_inv' θ hθ := arcsin_sin (by aesop) (by aesop)
  right_inv' x hx := sin_arcsin (by aesop) (by aesop)

/--
theorem `mapsTo_sin_Ioo` / 定理 `mapsTo_sin_Ioo`

English:
theorem mapsTo_sin_Ioo
  statement: MapsTo sin (Ioo (-(π / 2)) (π / 2)) (Ioo (-1) 1)
  proof: sinPartialHomeomorph.map_source'

@[simp]

中文:
定理 mapsTo_sin_Ioo
  结论: 映射到 sin (开区间 (-(π / 2)) (π / 2)) (开区间 (-1) 1)
  证明: sinPartialHomeomorph.map_source'

@[simp]

Depends on / 依赖: map_source, sinPartialHomeomorph, sinPartialHomeomorph.map_source
-/
theorem mapsTo_sin_Ioo : MapsTo sin (Ioo (-(π / 2)) (π / 2)) (Ioo (-1) 1) :=
  sinPartialHomeomorph.map_source'

@[simp]
/--
lemma `arcsin_image_Icc` / 引理 `arcsin_image_Icc`

English:
lemma arcsin_image_Icc
  statement: arcsin '' Set.Icc (-1) 1 = Set.Icc (-(π / 2)) (π / 2)
  proof: by
  simpa using sinPartialEquiv.symm.image_source_eq_target

中文:
引理 arcsin_image_Icc
  结论: arcsin '' 集合.闭区间 (-1) 1 = 集合.闭区间 (-(π / 2)) (π / 2)
  证明: by
  simpa using sinPartialEquiv.symm.image_source_eq_target

Depends on / 依赖: image_source_eq_target, sinPartialEquiv, sinPartialEquiv.symm.image_source_eq_target
-/
lemma arcsin_image_Icc : arcsin '' Set.Icc (-1) 1 = Set.Icc (-(π / 2)) (π / 2) := by
  simpa using sinPartialEquiv.symm.image_source_eq_target

/-- `Real.cos` as an `OpenPartialHomeomorph` between `(0, π)` and `(-1, 1)`. -/
@[simp]
/--
Definition of `cosPartialHomeomorph` / `cosPartialHomeomorph` 的定义

English:
definition cosPartialHomeomorph
  signature: : OpenPartialHomeomorph Real Real where
  body: cos
  invFun := arccos
  source := Ioo 0 π
  target := Ioo (-1) 1
  map_source' := by grind [arccos_pos, arccos_lt_pi, arccos_cos]
  map_target' _ hy := ⟨arccos_pos.mpr hy.2, arccos_lt_pi.mpr hy.1⟩
  left_inv' _ hx := arccos_cos hx.1.le hx.2.le
  right_inv' _ hy := cos_arccos hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_cos.continuousOn
  continuousOn_invFun := continuous_arccos.continuousOn

中文:
定义 cosPartialHomeomorph
  签名: : OpenPartialHomeomorph 实数 实数 where
  定义体: cos
  invFun := arccos
  source := Ioo 0 π
  target := Ioo (-1) 1
  map_source' := by grind [arccos_pos, arccos_lt_pi, arccos_cos]
  map_target' _ hy := ⟨arccos_pos.mpr hy.2, arccos_lt_pi.mpr hy.1⟩
  left_inv' _ hx := arccos_cos hx.1.le hx.2.le
  right_inv' _ hy := cos_arccos hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_cos.continuousOn
  continuousOn_invFun := continuous_arccos.continuousOn
-/
def cosPartialHomeomorph : OpenPartialHomeomorph Real Real where
  toFun := cos
  invFun := arccos
  source := Ioo 0 π
  target := Ioo (-1) 1
  map_source' := by grind [arccos_pos, arccos_lt_pi, arccos_cos]
  map_target' _ hy := ⟨arccos_pos.mpr hy.2, arccos_lt_pi.mpr hy.1⟩
  left_inv' _ hx := arccos_cos hx.1.le hx.2.le
  right_inv' _ hy := cos_arccos hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_cos.continuousOn
  continuousOn_invFun := continuous_arccos.continuousOn

/-- `Real.cos` and `Real.arccos` as a (partial) equivalence from `[0, π]` to `[-1, 1]` -/
@[simps]
/--
Definition of `cosPartialEquiv` / `cosPartialEquiv` 的定义

English:
definition cosPartialEquiv
  signature: : PartialEquiv Real Real where
  body: cos θ
  invFun x := arccos x
  source := Icc 0 π
  target := Icc (-1) 1
  map_source' x hx := by simpa [← abs_le] using abs_cos_le_one x
  map_target' θ hθ := ⟨arccos_nonneg θ, arccos_le_pi θ⟩
  left_inv' θ hθ := arccos_cos (by aesop) (by aesop)
  right_inv' x hx := cos_arccos (by aesop) (by aesop)

中文:
定义 cosPartialEquiv
  签名: : 部分等价 实数 实数 where
  定义体: cos θ
  invFun x := arccos x
  source := Icc 0 π
  target := Icc (-1) 1
  map_source' x hx := by simpa [← abs_le] using abs_cos_le_one x
  map_target' θ hθ := ⟨arccos_nonneg θ, arccos_le_pi θ⟩
  left_inv' θ hθ := arccos_cos (by aesop) (by aesop)
  right_inv' x hx := cos_arccos (by aesop) (by aesop)

Depends on / 依赖: HasEnrichedHom, Under.forget, forget
-/
noncomputable def cosPartialEquiv : PartialEquiv Real Real where
  toFun θ := cos θ
  invFun x := arccos x
  source := Icc 0 π
  target := Icc (-1) 1
  map_source' x hx := by simpa [← abs_le] using abs_cos_le_one x
  map_target' θ hθ := ⟨arccos_nonneg θ, arccos_le_pi θ⟩
  left_inv' θ hθ := arccos_cos (by aesop) (by aesop)
  right_inv' x hx := cos_arccos (by aesop) (by aesop)

/--
theorem `mapsTo_cos_Ioo` / 定理 `mapsTo_cos_Ioo`

English:
theorem mapsTo_cos_Ioo
  statement: MapsTo cos (Ioo 0 π) (Ioo (-1) 1)
  proof: cosPartialHomeomorph.map_source'

@[simp]

中文:
定理 mapsTo_cos_Ioo
  结论: 映射到 cos (开区间 0 π) (开区间 (-1) 1)
  证明: cosPartialHomeomorph.map_source'

@[simp]

Depends on / 依赖: cosPartialHomeomorph, cosPartialHomeomorph.map_source, map_source
-/
theorem mapsTo_cos_Ioo : MapsTo cos (Ioo 0 π) (Ioo (-1) 1) := cosPartialHomeomorph.map_source'

@[simp]
/--
lemma `arccos_image_Icc` / 引理 `arccos_image_Icc`

English:
lemma arccos_image_Icc
  statement: arccos '' Icc (-1) 1 = Icc 0 π
  proof: by
  simpa using cosPartialEquiv.symm.image_source_eq_target

中文:
引理 arccos_image_Icc
  结论: arccos '' 闭区间 (-1) 1 = 闭区间 0 π
  证明: by
  simpa using cosPartialEquiv.symm.image_source_eq_target

Depends on / 依赖: cosPartialEquiv, cosPartialEquiv.symm.image_source_eq_target, image_source_eq_target
-/
lemma arccos_image_Icc : arccos '' Icc (-1) 1 = Icc 0 π := by
  simpa using cosPartialEquiv.symm.image_source_eq_target

end Real

open Real

/-!
### Convenience dot notation lemmas
-/

namespace Filter.Tendsto

variable {α : Type*} {l : Filter α} {x : Real} {f : α -> Real}

/--
theorem `arcsin` / 定理 `arcsin`

English:
theorem arcsin
  given: (h : Tendsto f l (𝓝 x))
  statement: Tendsto (arcsin <| f ·) l (𝓝 (arcsin x))
  proof: (continuous_arcsin.tendsto _).comp h

中文:
定理 arcsin
  条件: (h : 收敛 f l (𝓝 x))
  结论: 收敛 (arcsin <| f ·) l (𝓝 (arcsin x))
  证明: (continuous_arcsin.tendsto _).comp h
-/
protected theorem arcsin (h : Tendsto f l (𝓝 x)) : Tendsto (arcsin <| f ·) l (𝓝 (arcsin x)) :=
  (continuous_arcsin.tendsto _).comp h

/--
theorem `arcsin_nhdsLE` / 定理 `arcsin_nhdsLE`

English:
theorem arcsin_nhdsLE
  given: (h : Tendsto f l (𝓝[<=] x))
  proof: by
  refine ((continuous_arcsin.tendsto _).inf <| MapsTo.tendsto fun y hy => ?_).comp h
  exact monotone_arcsin hy

中文:
定理 arcsin_nhdsLE
  条件: (h : 收敛 f l (𝓝[<=] x))
  证明: by
  refine ((continuous_arcsin.tendsto _).inf <| MapsTo.tendsto fun y hy => ?_).comp h
  exact monotone_arcsin hy

Depends on / 依赖: MapsTo, MapsTo.tendsto, continuous_arcsin, continuous_arcsin.tendsto, monotone_arcsin, tendsto
-/
theorem arcsin_nhdsLE (h : Tendsto f l (𝓝[<=] x)) :
    Tendsto (arcsin <| f ·) l (𝓝[<=] (arcsin x)) := by
  refine ((continuous_arcsin.tendsto _).inf <| MapsTo.tendsto fun y hy => ?_).comp h
  exact monotone_arcsin hy

/--
theorem `arcsin_nhdsGE` / 定理 `arcsin_nhdsGE`

English:
theorem arcsin_nhdsGE
  given: (h : Tendsto f l (𝓝[>=] x))
  statement: Tendsto (arcsin <| f ·) l (𝓝[>=] (arcsin x))
  proof: ((continuous_arcsin.tendsto _).inf <| MapsTo.tendsto fun _ => arcsin_le_arcsin).comp h

中文:
定理 arcsin_nhdsGE
  条件: (h : 收敛 f l (𝓝[>=] x))
  结论: 收敛 (arcsin <| f ·) l (𝓝[>=] (arcsin x))
  证明: ((continuous_arcsin.tendsto _).inf <| MapsTo.tendsto fun _ => arcsin_le_arcsin).comp h

Depends on / 依赖: MapsTo, MapsTo.tendsto, arcsin_le_arcsin, continuous_arcsin, continuous_arcsin.tendsto, tendsto
-/
theorem arcsin_nhdsGE (h : Tendsto f l (𝓝[>=] x)) : Tendsto (arcsin <| f ·) l (𝓝[>=] (arcsin x)) :=
  ((continuous_arcsin.tendsto _).inf <| MapsTo.tendsto fun _ => arcsin_le_arcsin).comp h

/--
theorem `arccos` / 定理 `arccos`

English:
theorem arccos
  given: (h : Tendsto f l (𝓝 x))
  statement: Tendsto (arccos <| f ·) l (𝓝 (arccos x))
  proof: (continuous_arccos.tendsto _).comp h

中文:
定理 arccos
  条件: (h : 收敛 f l (𝓝 x))
  结论: 收敛 (arccos <| f ·) l (𝓝 (arccos x))
  证明: (continuous_arccos.tendsto _).comp h
-/
protected theorem arccos (h : Tendsto f l (𝓝 x)) : Tendsto (arccos <| f ·) l (𝓝 (arccos x)) :=
  (continuous_arccos.tendsto _).comp h

/--
theorem `arccos_nhdsLE` / 定理 `arccos_nhdsLE`

English:
theorem arccos_nhdsLE
  given: (h : Tendsto f l (𝓝[<=] x))
  statement: Tendsto (arccos <| f ·) l (𝓝[>=] (arccos x))
  proof: ((continuous_arccos.tendsto _).inf <| MapsTo.tendsto fun _ => arccos_le_arccos).comp h

中文:
定理 arccos_nhdsLE
  条件: (h : 收敛 f l (𝓝[<=] x))
  结论: 收敛 (arccos <| f ·) l (𝓝[>=] (arccos x))
  证明: ((continuous_arccos.tendsto _).inf <| MapsTo.tendsto fun _ => arccos_le_arccos).comp h

Depends on / 依赖: MapsTo, MapsTo.tendsto, arccos_le_arccos, continuous_arccos, continuous_arccos.tendsto, tendsto
-/
theorem arccos_nhdsLE (h : Tendsto f l (𝓝[<=] x)) : Tendsto (arccos <| f ·) l (𝓝[>=] (arccos x)) :=
  ((continuous_arccos.tendsto _).inf <| MapsTo.tendsto fun _ => arccos_le_arccos).comp h

/--
theorem `arccos_nhdsGE` / 定理 `arccos_nhdsGE`

English:
theorem arccos_nhdsGE
  given: (h : Tendsto f l (𝓝[>=] x))
  proof: by
  refine ((continuous_arccos.tendsto _).inf <| MapsTo.tendsto fun y hy => ?_).comp h
  push _ in _ at hy ⊢
  exact antitone_arccos hy

中文:
定理 arccos_nhdsGE
  条件: (h : 收敛 f l (𝓝[>=] x))
  证明: by
  refine ((continuous_arccos.tendsto _).inf <| MapsTo.tendsto fun y hy => ?_).comp h
  push _ in _ at hy ⊢
  exact antitone_arccos hy

Depends on / 依赖: MapsTo, MapsTo.tendsto, antitone_arccos, continuous_arccos, continuous_arccos.tendsto, tendsto
-/
theorem arccos_nhdsGE (h : Tendsto f l (𝓝[>=] x)) :
    Tendsto (arccos <| f ·) l (𝓝[<=] (arccos x)) := by
  refine ((continuous_arccos.tendsto _).inf <| MapsTo.tendsto fun y hy => ?_).comp h
  push _ in _ at hy ⊢
  exact antitone_arccos hy

end Filter.Tendsto

variable {X : Type*} [TopologicalSpace X] {f : X -> Real} {s : Set X} {x : X}

protected nonrec theorem ContinuousWithinAt.arcsin (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (arcsin <| f ·) s x :=
  h.arcsin

protected nonrec theorem ContinuousWithinAt.arccos (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (arccos <| f ·) s x :=
  h.arccos

protected nonrec theorem ContinuousAt.arcsin (h : ContinuousAt f x) :
    ContinuousAt (arcsin <| f ·) x :=
  h.arcsin

protected nonrec theorem ContinuousAt.arccos (h : ContinuousAt f x) :
    ContinuousAt (arccos <| f ·) x :=
  h.arccos

/--
theorem `ContinuousOn.arcsin` / 定理 `ContinuousOn.arcsin`

English:
theorem ContinuousOn.arcsin
  given: (h : ContinuousOn f s)
  statement: ContinuousOn (arcsin <| f ·) s
  proof: fun x hx => (h x hx).arcsin

中文:
定理 ContinuousOn.arcsin
  条件: (h : ContinuousOn f s)
  结论: ContinuousOn (arcsin <| f ·) s
  证明: fun x hx => (h x hx).arcsin
-/
protected theorem ContinuousOn.arcsin (h : ContinuousOn f s) : ContinuousOn (arcsin <| f ·) s :=
  fun x hx => (h x hx).arcsin

/--
theorem `ContinuousOn.arccos` / 定理 `ContinuousOn.arccos`

English:
theorem ContinuousOn.arccos
  given: (h : ContinuousOn f s)
  statement: ContinuousOn (arccos <| f ·) s
  proof: fun x hx => (h x hx).arccos

中文:
定理 ContinuousOn.arccos
  条件: (h : ContinuousOn f s)
  结论: ContinuousOn (arccos <| f ·) s
  证明: fun x hx => (h x hx).arccos
-/
protected theorem ContinuousOn.arccos (h : ContinuousOn f s) : ContinuousOn (arccos <| f ·) s :=
  fun x hx => (h x hx).arccos

/--
theorem `Continuous.arcsin` / 定理 `Continuous.arcsin`

English:
theorem Continuous.arcsin
  given: (h : Continuous f)
  statement: Continuous (arcsin <| f ·)
  proof: continuous_arcsin.comp h

中文:
定理 连续.arcsin
  条件: (h : 连续 f)
  结论: 连续 (arcsin <| f ·)
  证明: continuous_arcsin.comp h
-/
protected theorem Continuous.arcsin (h : Continuous f) : Continuous (arcsin <| f ·) :=
  continuous_arcsin.comp h

/--
theorem `Continuous.arccos` / 定理 `Continuous.arccos`

English:
theorem Continuous.arccos
  given: (h : Continuous f)
  statement: Continuous (arccos <| f ·)
  proof: continuous_arccos.comp h

中文:
定理 连续.arccos
  条件: (h : 连续 f)
  结论: 连续 (arccos <| f ·)
  证明: continuous_arccos.comp h
-/
protected theorem Continuous.arccos (h : Continuous f) : Continuous (arccos <| f ·) :=
  continuous_arccos.comp h
