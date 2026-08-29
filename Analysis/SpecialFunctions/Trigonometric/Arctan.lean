/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# The `arctan` function.

Inequalities, identities and `Real.tan` as an `OpenPartialHomeomorph` between `(-(π / 2), π / 2)`
and the whole line.

The result of `arctan x + arctan y` is given by `arctan_add`, `arctan_add_eq_add_pi` or
`arctan_add_eq_sub_pi` depending on whether `x * y < 1` and `0 < x`. As an application of
`arctan_add` we give four Machin-like formulas (linear combinations of arctangents equal to
`π / 4 = arctan 1`), including John Machin's original one at
`four_mul_arctan_inv_5_sub_arctan_inv_239`.
-/

@[expose] public section


noncomputable section

open Set Filter
open scoped Topology

namespace Real

variable {x y : Real}

/--
theorem `tan_add` / 定理 `tan_add`

English:
theorem tan_add
  proof: by
  simpa only [← Complex.ofReal_inj, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_tan] using!
    @Complex.tan_add (x : Complex) (y : Complex) (by convert h <;> norm_cast)

中文:
定理 tan_add
  证明: by
  simpa only [← Complex.ofReal_inj, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_tan] using!
    @Complex.tan_add (x : Complex) (y : Complex) (by convert h <;> norm_cast)

Depends on / 依赖: Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_inj, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_tan, Complex.tan_add, convert, ofReal_add, ofReal_div, ofReal_inj, ofReal_mul, ofReal_sub, ofReal_tan, tan_add
-/
theorem tan_add
    (h : ((forall k : Int, x != (2 * k + 1) * π / 2) ∧ forall l : Int, y != (2 * l + 1) * π / 2) ∨
      (exists k : Int, x = (2 * k + 1) * π / 2) ∧ exists l : Int, y = (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  simpa only [← Complex.ofReal_inj, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_tan] using!
    @Complex.tan_add (x : Complex) (y : Complex) (by convert h <;> norm_cast)

/--
theorem `tan_add'` / 定理 `tan_add'`

English:
theorem tan_add'
  proof: tan_add (Or.inl h)

中文:
定理 tan_add'
  证明: tan_add (Or.inl h)

Depends on / 依赖: Or.inl, tan_add
-/
theorem tan_add'
    (h : (forall k : Int, x != (2 * k + 1) * π / 2) ∧ forall l : Int, y != (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)

/--
theorem `tan_sub` / 定理 `tan_sub`

English:
theorem tan_sub
  statement: {x y : Real}
  proof: by
  simpa only [← Complex.ofReal_inj, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_tan] using!
    @Complex.tan_sub (x : Complex) (y : Complex) (by convert h <;> norm_cast)

中文:
定理 tan_sub
  结论: {x y : 实数}
  证明: by
  simpa only [← Complex.ofReal_inj, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_tan] using!
    @Complex.tan_sub (x : Complex) (y : Complex) (by convert h <;> norm_cast)

Depends on / 依赖: Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_inj, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_tan, Complex.tan_sub, convert, ofReal_add, ofReal_div, ofReal_inj, ofReal_mul, ofReal_sub, ofReal_tan, tan_sub
-/
theorem tan_sub {x y : Real}
    (h : ((forall k : Int, x != (2 * k + 1) * π / 2) ∧ forall l : Int, y != (2 * l + 1) * π / 2) ∨
      (exists k : Int, x = (2 * k + 1) * π / 2) ∧ exists l : Int, y = (2 * l + 1) * π / 2) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := by
  simpa only [← Complex.ofReal_inj, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_tan] using!
    @Complex.tan_sub (x : Complex) (y : Complex) (by convert h <;> norm_cast)

/--
theorem `tan_sub'` / 定理 `tan_sub'`

English:
theorem tan_sub'
  statement: {x y : Real}
  proof: tan_sub (Or.inl h)

中文:
定理 tan_sub'
  结论: {x y : 实数}
  证明: tan_sub (Or.inl h)

Depends on / 依赖: Or.inl, tan_sub
-/
theorem tan_sub' {x y : Real}
    (h : (forall k : Int, x != (2 * k + 1) * π / 2) ∧ forall l : Int, y != (2 * l + 1) * π / 2) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) :=
  tan_sub (Or.inl h)

/--
theorem `tan_two_mul` / 定理 `tan_two_mul`

English:
theorem tan_two_mul
  statement: tan (2 * x) = 2 * tan x / (1 - tan x ^ 2)
  proof: by
  have := @Complex.tan_two_mul x
  norm_cast at *

中文:
定理 tan_two_mul
  结论: tan (2 * x) = 2 * tan x / (1 - tan x ^ 2)
  证明: by
  have := @Complex.tan_two_mul x
  norm_cast at *

Depends on / 依赖: Complex.tan_two_mul, tan_two_mul
-/
theorem tan_two_mul : tan (2 * x) = 2 * tan x / (1 - tan x ^ 2) := by
  have := @Complex.tan_two_mul x
  norm_cast at *

/--
theorem `tan_int_mul_pi_div_two` / 定理 `tan_int_mul_pi_div_two`

English:
theorem tan_int_mul_pi_div_two
  given: (n : Int)
  statement: tan (n * π / 2) = 0
  proof: tan_eq_zero_iff.mpr (by use n)

中文:
定理 tan_int_mul_pi_div_two
  条件: (n : 整数)
  结论: tan (n * π / 2) = 0
  证明: tan_eq_zero_iff.mpr (by use n)

Depends on / 依赖: tan_eq_zero_iff, tan_eq_zero_iff.mpr
-/
theorem tan_int_mul_pi_div_two (n : Int) : tan (n * π / 2) = 0 :=
  tan_eq_zero_iff.mpr (by use n)

/--
theorem `continuousOn_tan` / 定理 `continuousOn_tan`

English:
theorem continuousOn_tan
  statement: ContinuousOn tan {x | cos x != 0}
  proof: by
  suffices ContinuousOn (fun x => sin x / cos x) {x | cos x != 0} by
    have h_eq : (fun x => sin x / cos x) = tan := by ext1 x; rw [tan_eq_sin_div_cos]
    rwa [h_eq] at this
  exact continuousOn_sin.div continuousOn_cos fun x => id

@[continuity]

中文:
定理 continuousOn_tan
  结论: ContinuousOn tan {x | cos x != 0}
  证明: by
  suffices ContinuousOn (fun x => sin x / cos x) {x | cos x != 0} by
    have h_eq : (fun x => sin x / cos x) = tan := by ext1 x; rw [tan_eq_sin_div_cos]
    rwa [h_eq] at this
  exact continuousOn_sin.div continuousOn_cos fun x => id

@[continuity]

Depends on / 依赖: ContinuousOn, continuousOn_cos, continuousOn_sin, continuousOn_sin.div, h_eq, tan_eq_sin_div_cos
-/
theorem continuousOn_tan : ContinuousOn tan {x | cos x != 0} := by
  suffices ContinuousOn (fun x => sin x / cos x) {x | cos x != 0} by
    have h_eq : (fun x => sin x / cos x) = tan := by ext1 x; rw [tan_eq_sin_div_cos]
    rwa [h_eq] at this
  exact continuousOn_sin.div continuousOn_cos fun x => id

@[continuity]
/--
theorem `continuous_tan` / 定理 `continuous_tan`

English:
theorem continuous_tan
  statement: Continuous fun x : {x | cos x != 0} => tan x
  proof: continuousOn_iff_continuous_domRestrict.1 continuousOn_tan

中文:
定理 continuous_tan
  结论: 连续 fun x : {x | cos x != 0} => tan x
  证明: continuousOn_iff_continuous_domRestrict.1 continuousOn_tan

Depends on / 依赖: continuousOn_iff_continuous_domRestrict, continuousOn_tan
-/
theorem continuous_tan : Continuous fun x : {x | cos x != 0} => tan x :=
  continuousOn_iff_continuous_domRestrict.1 continuousOn_tan

/--
theorem `continuousOn_tan_Ioo` / 定理 `continuousOn_tan_Ioo`

English:
theorem continuousOn_tan_Ioo
  statement: ContinuousOn tan (Ioo (-(π / 2)) (π / 2))
  proof: by
  refine ContinuousOn.mono continuousOn_tan fun x => ?_
  simp only [and_imp, mem_Ioo, mem_ofPred_eq, Ne]
  rw [cos_eq_zero_iff]
  rintro hx_gt hx_lt ⟨r, hxr_eq⟩
  rcases le_or_gt 0 r with h | h
  · rw [lt_iff_not_ge] at hx_lt
    refine hx_lt ?_
    rw [hxr_eq]; rw [← one_mul (π / 2)]; rw [mul_d

中文:
定理 continuousOn_tan_Ioo
  结论: ContinuousOn tan (开区间 (-(π / 2)) (π / 2))
  证明: by
  refine ContinuousOn.mono continuousOn_tan fun x => ?_
  simp only [and_imp, mem_Ioo, mem_ofPred_eq, Ne]
  rw [cos_eq_zero_iff]
  rintro hx_gt hx_lt ⟨r, hxr_eq⟩
  rcases le_or_gt 0 r with h | h
  · rw [lt_iff_not_ge] at hx_lt
    refine hx_lt ?_
    rw [hxr_eq]; rw [← one_mul (π / 2)]; rw [mul_d

Depends on / 依赖: ContinuousOn, ContinuousOn.mono, and_imp, continuousOn_tan, cos_eq_zero_iff, half_pos, hx_gt, hx_lt, hxr_eq, le_or_gt, lt_iff_not_ge, mem_Ioo, mem_ofPred_eq, mul_div_assoc, neg_mul_eq_neg_mul, one_mul, pi_pos
-/
theorem continuousOn_tan_Ioo : ContinuousOn tan (Ioo (-(π / 2)) (π / 2)) := by
  refine ContinuousOn.mono continuousOn_tan fun x => ?_
  simp only [and_imp, mem_Ioo, mem_ofPred_eq, Ne]
  rw [cos_eq_zero_iff]
  rintro hx_gt hx_lt ⟨r, hxr_eq⟩
  rcases le_or_gt 0 r with h | h
  · rw [lt_iff_not_ge] at hx_lt
    refine hx_lt ?_
    rw [hxr_eq]; rw [← one_mul (π / 2)]; rw [mul_div_assoc]; rw [mul_le_mul_iff_left₀ (half_pos pi_pos)]
    simp [h]
  · rw [lt_iff_not_ge] at hx_gt
    refine hx_gt ?_
    rw [hxr_eq]; rw [← one_mul (π / 2)]; rw [mul_div_assoc]; rw [neg_mul_eq_neg_mul]; rw [mul_le_mul_iff_left₀ (half_pos pi_pos)]
    have hr_le : r <= -1 := by rwa [Int.lt_iff_add_one_le, ← le_neg_iff_add_nonpos_right] at h
    rw [← le_sub_iff_add_le]; rw [mul_comm]; rw [← le_div_iff₀]
    · norm_num
      assumption_mod_cast
    · exact zero_lt_two

/--
theorem `surjOn_tan` / 定理 `surjOn_tan`

English:
theorem surjOn_tan
  statement: SurjOn tan (Ioo (-(π / 2)) (π / 2)) univ
  proof: have := neg_lt_self pi_div_two_pos
  continuousOn_tan_Ioo.surjOn_of_tendsto (nonempty_Ioo.2 this)
    (by rw [tendsto_comp_coe_Ioo_atBot this]; exact tendsto_tan_neg_pi_div_two)
    (by rw [tendsto_comp_coe_Ioo_atTop this]; exact tendsto_tan_pi_div_two)

中文:
定理 surjOn_tan
  结论: 满射限制 tan (开区间 (-(π / 2)) (π / 2)) univ
  证明: have := neg_lt_self pi_div_two_pos
  continuousOn_tan_Ioo.surjOn_of_tendsto (nonempty_Ioo.2 this)
    (by rw [tendsto_comp_coe_Ioo_atBot this]; exact tendsto_tan_neg_pi_div_two)
    (by rw [tendsto_comp_coe_Ioo_atTop this]; exact tendsto_tan_pi_div_two)

Depends on / 依赖: continuousOn_tan_Ioo, continuousOn_tan_Ioo.surjOn_of_tendsto, neg_lt_self, nonempty_Ioo, pi_div_two_pos, surjOn_of_tendsto, tendsto_comp_coe_Ioo_atBot, tendsto_comp_coe_Ioo_atTop, tendsto_tan_neg_pi_div_two, tendsto_tan_pi_div_two
-/
theorem surjOn_tan : SurjOn tan (Ioo (-(π / 2)) (π / 2)) univ :=
  have := neg_lt_self pi_div_two_pos
  continuousOn_tan_Ioo.surjOn_of_tendsto (nonempty_Ioo.2 this)
    (by rw [tendsto_comp_coe_Ioo_atBot this]; exact tendsto_tan_neg_pi_div_two)
    (by rw [tendsto_comp_coe_Ioo_atTop this]; exact tendsto_tan_pi_div_two)

/--
theorem `tan_surjective` / 定理 `tan_surjective`

English:
theorem tan_surjective
  statement: Function.Surjective tan
  proof: fun _ => surjOn_tan.subset_range trivial

中文:
定理 tan_surjective
  结论: 函数.满射 tan
  证明: fun _ => surjOn_tan.subset_range trivial

Depends on / 依赖: subset_range, surjOn_tan, surjOn_tan.subset_range
-/
theorem tan_surjective : Function.Surjective tan := fun _ => surjOn_tan.subset_range trivial

/--
theorem `image_tan_Ioo` / 定理 `image_tan_Ioo`

English:
theorem image_tan_Ioo
  statement: tan '' Ioo (-(π / 2)) (π / 2) = univ
  proof: univ_subset_iff.1 surjOn_tan

中文:
定理 image_tan_Ioo
  结论: tan '' 开区间 (-(π / 2)) (π / 2) = univ
  证明: univ_subset_iff.1 surjOn_tan

Depends on / 依赖: surjOn_tan, univ_subset_iff
-/
theorem image_tan_Ioo : tan '' Ioo (-(π / 2)) (π / 2) = univ :=
  univ_subset_iff.1 surjOn_tan

/--
Definition of `tanOrderIso` / `tanOrderIso` 的定义

English:
definition tanOrderIso
  signature: : Ioo (-(π / 2)) (π / 2) ≃o Real
  body: (strictMonoOn_tan.orderIso _ _).trans
    (OrderIso.setCongr _ _ image_tan_Ioo).trans OrderIso.Set.univ

中文:
定义 tanOrderIso
  签名: : 开区间 (-(π / 2)) (π / 2) ≃o 实数
  定义体: (strictMonoOn_tan.orderIso _ _).trans
    (OrderIso.setCongr _ _ image_tan_Ioo).trans OrderIso.Set.univ

Depends on / 依赖: OrderIso, OrderIso.Set.univ, OrderIso.setCongr, image_tan_Ioo, orderIso, setCongr, strictMonoOn_tan, strictMonoOn_tan.orderIso
-/
def tanOrderIso : Ioo (-(π / 2)) (π / 2) ≃o Real :=
(strictMonoOn_tan.orderIso _ _).trans
    (OrderIso.setCongr _ _ image_tan_Ioo).trans OrderIso.Set.univ

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and
`arctan x < π / 2` -/
@[pp_nodot]
/--
Definition of `arctan` / `arctan` 的定义

English:
definition arctan
  signature: (x : Real)
  body: tanOrderIso.symm x

@[simp]

中文:
定义 arctan
  签名: (x : 实数)
  定义体: tanOrderIso.symm x

@[simp]

Depends on / 依赖: tanOrderIso, tanOrderIso.symm
-/
noncomputable def arctan (x : Real) : Real :=
  tanOrderIso.symm x

@[simp]
/--
theorem `tan_arctan` / 定理 `tan_arctan`

English:
theorem tan_arctan
  given: (x : Real)
  statement: tan (arctan x) = x
  proof: tanOrderIso.apply_symm_apply x

中文:
定理 tan_arctan
  条件: (x : 实数)
  结论: tan (arctan x) = x
  证明: tanOrderIso.apply_symm_apply x

Depends on / 依赖: apply_symm_apply, tanOrderIso, tanOrderIso.apply_symm_apply
-/
theorem tan_arctan (x : Real) : tan (arctan x) = x :=
  tanOrderIso.apply_symm_apply x

/--
theorem `arctan_mem_Ioo` / 定理 `arctan_mem_Ioo`

English:
theorem arctan_mem_Ioo
  given: (x : Real)
  statement: arctan x in Ioo (-(π / 2)) (π / 2)
  proof: Subtype.coe_prop _

@[simp]

中文:
定理 arctan_mem_Ioo
  条件: (x : 实数)
  结论: arctan x in 开区间 (-(π / 2)) (π / 2)
  证明: Subtype.coe_prop _

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_prop, coe_prop
-/
theorem arctan_mem_Ioo (x : Real) : arctan x in Ioo (-(π / 2)) (π / 2) :=
  Subtype.coe_prop _

@[simp]
/--
theorem `range_arctan` / 定理 `range_arctan`

English:
theorem range_arctan
  statement: range arctan = Ioo (-(π / 2)) (π / 2)
  proof: ((EquivLike.surjective _).range_comp _).trans Subtype.range_coe

中文:
定理 range_arctan
  结论: range arctan = 开区间 (-(π / 2)) (π / 2)
  证明: ((EquivLike.surjective _).range_comp _).trans Subtype.range_coe

Depends on / 依赖: EquivLike, EquivLike.surjective, Subtype, Subtype.range_coe, range_coe, range_comp, surjective
-/
theorem range_arctan : range arctan = Ioo (-(π / 2)) (π / 2) :=
  ((EquivLike.surjective _).range_comp _).trans Subtype.range_coe

/--
theorem `arctan_tan` / 定理 `arctan_tan`

English:
theorem arctan_tan
  given: (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  statement: arctan (tan x) = x
  proof: Subtype.ext_iff.1 tanOrderIso.symm_apply_apply ⟨x, hx₁, hx₂⟩

中文:
定理 arctan_tan
  条件: (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  结论: arctan (tan x) = x
  证明: Subtype.ext_iff.1 tanOrderIso.symm_apply_apply ⟨x, hx₁, hx₂⟩

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, symm_apply_apply, tanOrderIso, tanOrderIso.symm_apply_apply
-/
theorem arctan_tan (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : arctan (tan x) = x :=
Subtype.ext_iff.1 tanOrderIso.symm_apply_apply ⟨x, hx₁, hx₂⟩

/--
theorem `cos_arctan_pos` / 定理 `cos_arctan_pos`

English:
theorem cos_arctan_pos
  given: (x : Real)
  statement: 0 < cos (arctan x)
  proof: cos_pos_of_mem_Ioo arctan_mem_Ioo x

中文:
定理 cos_arctan_pos
  条件: (x : 实数)
  结论: 0 < cos (arctan x)
  证明: cos_pos_of_mem_Ioo arctan_mem_Ioo x

Depends on / 依赖: arctan_mem_Ioo, cos_pos_of_mem_Ioo
-/
theorem cos_arctan_pos (x : Real) : 0 < cos (arctan x) :=
cos_pos_of_mem_Ioo arctan_mem_Ioo x

/--
theorem `sin_sq_arctan` / 定理 `sin_sq_arctan`

English:
theorem sin_sq_arctan
  given: (x : Real)
  statement: sin (arctan x) ^ 2 = x ^ 2 / (1 + x ^ 2)
  proof: by
  rw [← tan_sq_div_one_add_tan_sq (cos_arctan_pos x).ne']; rw [tan_arctan]

中文:
定理 sin_sq_arctan
  条件: (x : 实数)
  结论: sin (arctan x) ^ 2 = x ^ 2 / (1 + x ^ 2)
  证明: by
  rw [← tan_sq_div_one_add_tan_sq (cos_arctan_pos x).ne']; rw [tan_arctan]

Depends on / 依赖: cos_arctan_pos, tan_arctan, tan_sq_div_one_add_tan_sq
-/
theorem sin_sq_arctan (x : Real) : sin (arctan x) ^ 2 = x ^ 2 / (1 + x ^ 2) := by
  rw [← tan_sq_div_one_add_tan_sq (cos_arctan_pos x).ne']; rw [tan_arctan]

/--
theorem `cos_sq_arctan` / 定理 `cos_sq_arctan`

English:
theorem cos_sq_arctan
  given: (x : Real)
  statement: cos (arctan x) ^ 2 = 1 / (1 + x ^ 2)
  proof: by
  rw [one_div]; rw [← inv_one_add_tan_sq (cos_arctan_pos x).ne']; rw [tan_arctan]

中文:
定理 cos_sq_arctan
  条件: (x : 实数)
  结论: cos (arctan x) ^ 2 = 1 / (1 + x ^ 2)
  证明: by
  rw [one_div]; rw [← inv_one_add_tan_sq (cos_arctan_pos x).ne']; rw [tan_arctan]

Depends on / 依赖: cos_arctan_pos, inv_one_add_tan_sq, one_div, tan_arctan
-/
theorem cos_sq_arctan (x : Real) : cos (arctan x) ^ 2 = 1 / (1 + x ^ 2) := by
  rw [one_div]; rw [← inv_one_add_tan_sq (cos_arctan_pos x).ne']; rw [tan_arctan]

/--
theorem `sin_arctan` / 定理 `sin_arctan`

English:
theorem sin_arctan
  given: (x : Real)
  statement: sin (arctan x) = x / √(1 + x ^ 2)
  proof: by
  rw [← tan_div_sqrt_one_add_tan_sq (cos_arctan_pos x)]; rw [tan_arctan]

中文:
定理 sin_arctan
  条件: (x : 实数)
  结论: sin (arctan x) = x / √(1 + x ^ 2)
  证明: by
  rw [← tan_div_sqrt_one_add_tan_sq (cos_arctan_pos x)]; rw [tan_arctan]

Depends on / 依赖: cos_arctan_pos, tan_arctan, tan_div_sqrt_one_add_tan_sq
-/
theorem sin_arctan (x : Real) : sin (arctan x) = x / √(1 + x ^ 2) := by
  rw [← tan_div_sqrt_one_add_tan_sq (cos_arctan_pos x)]; rw [tan_arctan]

/--
theorem `cos_arctan` / 定理 `cos_arctan`

English:
theorem cos_arctan
  given: (x : Real)
  statement: cos (arctan x) = 1 / √(1 + x ^ 2)
  proof: by
  rw [one_div]; rw [← inv_sqrt_one_add_tan_sq (cos_arctan_pos x)]; rw [tan_arctan]

中文:
定理 cos_arctan
  条件: (x : 实数)
  结论: cos (arctan x) = 1 / √(1 + x ^ 2)
  证明: by
  rw [one_div]; rw [← inv_sqrt_one_add_tan_sq (cos_arctan_pos x)]; rw [tan_arctan]

Depends on / 依赖: cos_arctan_pos, inv_sqrt_one_add_tan_sq, one_div, tan_arctan
-/
theorem cos_arctan (x : Real) : cos (arctan x) = 1 / √(1 + x ^ 2) := by
  rw [one_div]; rw [← inv_sqrt_one_add_tan_sq (cos_arctan_pos x)]; rw [tan_arctan]

/--
theorem `arctan_lt_pi_div_two` / 定理 `arctan_lt_pi_div_two`

English:
theorem arctan_lt_pi_div_two
  given: (x : Real)
  statement: arctan x < π / 2
  proof: (arctan_mem_Ioo x).2

中文:
定理 arctan_lt_pi_div_two
  条件: (x : 实数)
  结论: arctan x < π / 2
  证明: (arctan_mem_Ioo x).2

Depends on / 依赖: arctan_mem_Ioo
-/
theorem arctan_lt_pi_div_two (x : Real) : arctan x < π / 2 :=
  (arctan_mem_Ioo x).2

/--
theorem `neg_pi_div_two_lt_arctan` / 定理 `neg_pi_div_two_lt_arctan`

English:
theorem neg_pi_div_two_lt_arctan
  given: (x : Real)
  statement: -(π / 2) < arctan x
  proof: (arctan_mem_Ioo x).1

中文:
定理 neg_pi_div_two_lt_arctan
  条件: (x : 实数)
  结论: -(π / 2) < arctan x
  证明: (arctan_mem_Ioo x).1

Depends on / 依赖: arctan_mem_Ioo
-/
theorem neg_pi_div_two_lt_arctan (x : Real) : -(π / 2) < arctan x :=
  (arctan_mem_Ioo x).1

/--
theorem `arctan_eq_arcsin` / 定理 `arctan_eq_arcsin`

English:
theorem arctan_eq_arcsin
  given: (x : Real)
  statement: arctan x = arcsin (x / √(1 + x ^ 2))
  proof: Eq.symm arcsin_eq_of_sin_eq (sin_arctan x) (mem_Icc_of_Ioo <| arctan_mem_Ioo x)

中文:
定理 arctan_eq_arcsin
  条件: (x : 实数)
  结论: arctan x = arcsin (x / √(1 + x ^ 2))
  证明: Eq.symm arcsin_eq_of_sin_eq (sin_arctan x) (mem_Icc_of_Ioo <| arctan_mem_Ioo x)

Depends on / 依赖: Eq.symm, arcsin_eq_of_sin_eq, arctan_mem_Ioo, mem_Icc_of_Ioo, sin_arctan
-/
theorem arctan_eq_arcsin (x : Real) : arctan x = arcsin (x / √(1 + x ^ 2)) :=
Eq.symm arcsin_eq_of_sin_eq (sin_arctan x) (mem_Icc_of_Ioo <| arctan_mem_Ioo x)

/--
theorem `arcsin_eq_arctan` / 定理 `arcsin_eq_arctan`

English:
theorem arcsin_eq_arctan
  given: (h : x in Ioo (-(1 : Real)) 1)
  proof: by
  rw_mod_cast [arctan_eq_arcsin, div_pow, sq_sqrt, one_add_div, div_div, ← sqrt_mul,
    mul_div_cancel₀, sub_add_cancel, sqrt_one, div_one] <;> simp at h <;> nlinarith [h.1, h.2]

@[simp]

中文:
定理 arcsin_eq_arctan
  条件: (h : x in 开区间 (-(1 : 实数)) 1)
  证明: by
  rw_mod_cast [arctan_eq_arcsin, div_pow, sq_sqrt, one_add_div, div_div, ← sqrt_mul,
    mul_div_cancel₀, sub_add_cancel, sqrt_one, div_one] <;> simp at h <;> nlinarith [h.1, h.2]

@[simp]

Depends on / 依赖: arctan_eq_arcsin, div_div, div_one, div_pow, one_add_div, rw_mod_cast, sq_sqrt, sqrt_mul, sqrt_one, sub_add_cancel
-/
theorem arcsin_eq_arctan (h : x in Ioo (-(1 : Real)) 1) :
    arcsin x = arctan (x / √(1 - x ^ 2)) := by
  rw_mod_cast [arctan_eq_arcsin, div_pow, sq_sqrt, one_add_div, div_div, ← sqrt_mul,
    mul_div_cancel₀, sub_add_cancel, sqrt_one, div_one] <;> simp at h <;> nlinarith [h.1, h.2]

@[simp]
/--
theorem `arctan_zero` / 定理 `arctan_zero`

English:
theorem arctan_zero
  statement: arctan 0 = 0
  proof: by simp [arctan_eq_arcsin]

@[gcongr, mono]

中文:
定理 arctan_zero
  结论: arctan 0 = 0
  证明: by simp [arctan_eq_arcsin]

@[gcongr, mono]

Depends on / 依赖: arctan_eq_arcsin
-/
theorem arctan_zero : arctan 0 = 0 := by simp [arctan_eq_arcsin]

@[gcongr, mono]
/--
theorem `arctan_strictMono` / 定理 `arctan_strictMono`

English:
theorem arctan_strictMono
  statement: StrictMono arctan
  proof: tanOrderIso.symm.strictMono

@[gcongr]

中文:
定理 arctan_strictMono
  结论: 严格递增 arctan
  证明: tanOrderIso.symm.strictMono

@[gcongr]

Depends on / 依赖: strictMono, tanOrderIso, tanOrderIso.symm.strictMono
-/
theorem arctan_strictMono : StrictMono arctan := tanOrderIso.symm.strictMono

@[gcongr]
/--
theorem `arctan_mono` / 定理 `arctan_mono`

English:
theorem arctan_mono
  statement: Monotone arctan
  proof: arctan_strictMono.monotone

@[simp]

中文:
定理 arctan_mono
  结论: 递增 arctan
  证明: arctan_strictMono.monotone

@[simp]

Depends on / 依赖: arctan_strictMono, arctan_strictMono.monotone, monotone
-/
theorem arctan_mono : Monotone arctan := arctan_strictMono.monotone

@[simp]
/--
theorem `arctan_lt_arctan_iff` / 定理 `arctan_lt_arctan_iff`

English:
theorem arctan_lt_arctan_iff
  statement: arctan x < arctan y ↔ x < y
  proof: arctan_strictMono.lt_iff_lt

@[simp]

中文:
定理 arctan_lt_arctan_iff
  结论: arctan x < arctan y ↔ x < y
  证明: arctan_strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: arctan_strictMono, arctan_strictMono.lt_iff_lt, lt_iff_lt
-/
theorem arctan_lt_arctan_iff : arctan x < arctan y ↔ x < y := arctan_strictMono.lt_iff_lt

@[simp]
/--
theorem `arctan_le_arctan_iff` / 定理 `arctan_le_arctan_iff`

English:
theorem arctan_le_arctan_iff
  statement: arctan x <= arctan y ↔ x <= y
  proof: arctan_strictMono.le_iff_le

中文:
定理 arctan_le_arctan_iff
  结论: arctan x <= arctan y ↔ x <= y
  证明: arctan_strictMono.le_iff_le

Depends on / 依赖: arctan_strictMono, arctan_strictMono.le_iff_le, le_iff_le
-/
theorem arctan_le_arctan_iff : arctan x <= arctan y ↔ x <= y := arctan_strictMono.le_iff_le

/--
theorem `arctan_injective` / 定理 `arctan_injective`

English:
theorem arctan_injective
  statement: arctan.Injective
  proof: arctan_strictMono.injective

@[simp]

中文:
定理 arctan_injective
  结论: arctan.单射
  证明: arctan_strictMono.injective

@[simp]

Depends on / 依赖: arctan_strictMono, arctan_strictMono.injective, injective
-/
theorem arctan_injective : arctan.Injective := arctan_strictMono.injective

@[simp]
/--
theorem `arctan_inj` / 定理 `arctan_inj`

English:
theorem arctan_inj
  statement: arctan x = arctan y ↔ x = y
  proof: arctan_injective.eq_iff

@[simp]

中文:
定理 arctan_inj
  结论: arctan x = arctan y ↔ x = y
  证明: arctan_injective.eq_iff

@[simp]

Depends on / 依赖: arctan_injective, arctan_injective.eq_iff, eq_iff
-/
theorem arctan_inj : arctan x = arctan y ↔ x = y := arctan_injective.eq_iff

@[simp]
/--
theorem `arctan_eq_zero_iff` / 定理 `arctan_eq_zero_iff`

English:
theorem arctan_eq_zero_iff
  statement: arctan x = 0 ↔ x = 0
  proof: .trans (by rw [arctan_zero]) arctan_injective.eq_iff

中文:
定理 arctan_eq_zero_iff
  结论: arctan x = 0 ↔ x = 0
  证明: .trans (by rw [arctan_zero]) arctan_injective.eq_iff

Depends on / 依赖: arctan_injective, arctan_injective.eq_iff, arctan_zero, eq_iff
-/
theorem arctan_eq_zero_iff : arctan x = 0 ↔ x = 0 :=
  .trans (by rw [arctan_zero]) arctan_injective.eq_iff

/--
theorem `tendsto_arctan_atTop` / 定理 `tendsto_arctan_atTop`

English:
theorem tendsto_arctan_atTop
  statement: Tendsto arctan atTop (𝓝[<] (π / 2))
  proof: .mp tanOrderIso.symm.tendsto_atTop tendsto_Ioo_atTop (by simp)

中文:
定理 tendsto_arctan_atTop
  结论: 收敛 arctan atTop (𝓝[<] (π / 2))
  证明: .mp tanOrderIso.symm.tendsto_atTop tendsto_Ioo_atTop (by simp)

Depends on / 依赖: tanOrderIso, tanOrderIso.symm.tendsto_atTop, tendsto_Ioo_atTop, tendsto_atTop
-/
theorem tendsto_arctan_atTop : Tendsto arctan atTop (𝓝[<] (π / 2)) :=
.mp tanOrderIso.symm.tendsto_atTop tendsto_Ioo_atTop (by simp)

/--
theorem `tendsto_arctan_atBot` / 定理 `tendsto_arctan_atBot`

English:
theorem tendsto_arctan_atBot
  statement: Tendsto arctan atBot (𝓝[>] (-(π / 2)))
  proof: .mp tanOrderIso.symm.tendsto_atBot tendsto_Ioo_atBot (by simp)

中文:
定理 tendsto_arctan_atBot
  结论: 收敛 arctan atBot (𝓝[>] (-(π / 2)))
  证明: .mp tanOrderIso.symm.tendsto_atBot tendsto_Ioo_atBot (by simp)

Depends on / 依赖: tanOrderIso, tanOrderIso.symm.tendsto_atBot, tendsto_Ioo_atBot, tendsto_atBot
-/
theorem tendsto_arctan_atBot : Tendsto arctan atBot (𝓝[>] (-(π / 2))) :=
.mp tanOrderIso.symm.tendsto_atBot tendsto_Ioo_atBot (by simp)

/--
theorem `arctan_eq_of_tan_eq` / 定理 `arctan_eq_of_tan_eq`

English:
theorem arctan_eq_of_tan_eq
  given: (h : tan x = y) (hx : x in Ioo (-(π / 2)) (π / 2))
  proof: injOn_tan (arctan_mem_Ioo _) hx (by rw [tan_arctan, h])

@[simp]

中文:
定理 arctan_eq_of_tan_eq
  条件: (h : tan x = y) (hx : x in 开区间 (-(π / 2)) (π / 2))
  证明: injOn_tan (arctan_mem_Ioo _) hx (by rw [tan_arctan, h])

@[simp]

Depends on / 依赖: arctan_mem_Ioo, injOn_tan, tan_arctan
-/
theorem arctan_eq_of_tan_eq (h : tan x = y) (hx : x in Ioo (-(π / 2)) (π / 2)) :
    arctan y = x :=
  injOn_tan (arctan_mem_Ioo _) hx (by rw [tan_arctan, h])

@[simp]
/--
theorem `arctan_one` / 定理 `arctan_one`

English:
theorem arctan_one
  statement: arctan 1 = π / 4
  proof: arctan_eq_of_tan_eq tan_pi_div_four by constructor <;> linarith [pi_pos]

@[simp]

中文:
定理 arctan_one
  结论: arctan 1 = π / 4
  证明: arctan_eq_of_tan_eq tan_pi_div_four by constructor <;> linarith [pi_pos]

@[simp]

Depends on / 依赖: arctan_eq_of_tan_eq, pi_pos, tan_pi_div_four
-/
theorem arctan_one : arctan 1 = π / 4 :=
arctan_eq_of_tan_eq tan_pi_div_four by constructor <;> linarith [pi_pos]

@[simp]
/--
theorem `arctan_sqrt_three` / 定理 `arctan_sqrt_three`

English:
theorem arctan_sqrt_three
  statement: arctan (√3) = π / 3
  proof: by
  rw [← tan_pi_div_three]; rw [arctan_tan]
  all_goals
  · field_simp
    norm_num

@[simp]

中文:
定理 arctan_sqrt_three
  结论: arctan (√3) = π / 3
  证明: by
  rw [← tan_pi_div_three]; rw [arctan_tan]
  all_goals
  · field_simp
    norm_num

@[simp]

Depends on / 依赖: all_goals, arctan_tan, tan_pi_div_three
-/
theorem arctan_sqrt_three : arctan (√3) = π / 3 := by
  rw [← tan_pi_div_three]; rw [arctan_tan]
  all_goals
  · field_simp
    norm_num

@[simp]
/--
theorem `arctan_inv_sqrt_three` / 定理 `arctan_inv_sqrt_three`

English:
theorem arctan_inv_sqrt_three
  statement: arctan (√3)⁻¹ = π / 6
  proof: by
  rw [inv_eq_one_div]; rw [← tan_pi_div_six]; rw [arctan_tan]
  all_goals
  · field_simp
    norm_num

@[simp]

中文:
定理 arctan_inv_sqrt_three
  结论: arctan (√3)⁻¹ = π / 6
  证明: by
  rw [inv_eq_one_div]; rw [← tan_pi_div_six]; rw [arctan_tan]
  all_goals
  · field_simp
    norm_num

@[simp]

Depends on / 依赖: all_goals, arctan_tan, inv_eq_one_div, tan_pi_div_six
-/
theorem arctan_inv_sqrt_three : arctan (√3)⁻¹ = π / 6 := by
  rw [inv_eq_one_div]; rw [← tan_pi_div_six]; rw [arctan_tan]
  all_goals
  · field_simp
    norm_num

@[simp]
/--
theorem `arctan_eq_pi_div_four` / 定理 `arctan_eq_pi_div_four`

English:
theorem arctan_eq_pi_div_four
  statement: arctan x = π / 4 ↔ x = 1
  proof: arctan_injective.eq_iff' arctan_one

@[simp]

中文:
定理 arctan_eq_pi_div_four
  结论: arctan x = π / 4 ↔ x = 1
  证明: arctan_injective.eq_iff' arctan_one

@[simp]

Depends on / 依赖: arctan_injective, arctan_injective.eq_iff, arctan_one, eq_iff
-/
theorem arctan_eq_pi_div_four : arctan x = π / 4 ↔ x = 1 := arctan_injective.eq_iff' arctan_one

@[simp]
/--
theorem `arctan_neg` / 定理 `arctan_neg`

English:
theorem arctan_neg
  given: (x : Real)
  statement: arctan (-x) = -arctan x
  proof: by simp [arctan_eq_arcsin, neg_div]

@[simp]

中文:
定理 arctan_neg
  条件: (x : 实数)
  结论: arctan (-x) = -arctan x
  证明: by simp [arctan_eq_arcsin, neg_div]

@[simp]

Depends on / 依赖: arctan_eq_arcsin, neg_div
-/
theorem arctan_neg (x : Real) : arctan (-x) = -arctan x := by simp [arctan_eq_arcsin, neg_div]

@[simp]
/--
theorem `arctan_eq_neg_pi_div_four` / 定理 `arctan_eq_neg_pi_div_four`

English:
theorem arctan_eq_neg_pi_div_four
  statement: arctan x = -(π / 4) ↔ x = -1
  proof: arctan_injective.eq_iff' by rw [arctan_neg, arctan_one]

@[simp]

中文:
定理 arctan_eq_neg_pi_div_four
  结论: arctan x = -(π / 4) ↔ x = -1
  证明: arctan_injective.eq_iff' by rw [arctan_neg, arctan_one]

@[simp]

Depends on / 依赖: arctan_injective, arctan_injective.eq_iff, arctan_neg, arctan_one, eq_iff
-/
theorem arctan_eq_neg_pi_div_four : arctan x = -(π / 4) ↔ x = -1 :=
arctan_injective.eq_iff' by rw [arctan_neg, arctan_one]

@[simp]
/--
theorem `arctan_pos` / 定理 `arctan_pos`

English:
theorem arctan_pos
  statement: 0 < arctan x ↔ 0 < x
  proof: by
  simpa only [arctan_zero] using arctan_lt_arctan_iff (x := 0)

@[simp]

中文:
定理 arctan_pos
  结论: 0 < arctan x ↔ 0 < x
  证明: by
  simpa only [arctan_zero] using arctan_lt_arctan_iff (x := 0)

@[simp]

Depends on / 依赖: arctan_lt_arctan_iff, arctan_zero
-/
theorem arctan_pos : 0 < arctan x ↔ 0 < x := by
  simpa only [arctan_zero] using arctan_lt_arctan_iff (x := 0)

@[simp]
/--
theorem `arctan_lt_zero` / 定理 `arctan_lt_zero`

English:
theorem arctan_lt_zero
  statement: arctan x < 0 ↔ x < 0
  proof: by
  simpa only [arctan_zero] using arctan_lt_arctan_iff (y := 0)

@[simp]

中文:
定理 arctan_lt_zero
  结论: arctan x < 0 ↔ x < 0
  证明: by
  simpa only [arctan_zero] using arctan_lt_arctan_iff (y := 0)

@[simp]

Depends on / 依赖: arctan_lt_arctan_iff, arctan_zero
-/
theorem arctan_lt_zero : arctan x < 0 ↔ x < 0 := by
  simpa only [arctan_zero] using arctan_lt_arctan_iff (y := 0)

@[simp]
/--
theorem `arctan_nonneg` / 定理 `arctan_nonneg`

English:
theorem arctan_nonneg
  statement: 0 <= arctan x ↔ 0 <= x
  proof: by
  simpa only [arctan_zero] using arctan_le_arctan_iff (x := 0)

@[simp]

中文:
定理 arctan_nonneg
  结论: 0 <= arctan x ↔ 0 <= x
  证明: by
  simpa only [arctan_zero] using arctan_le_arctan_iff (x := 0)

@[simp]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, Faithful, arctan_le_arctan_iff, arctan_zero
-/
theorem arctan_nonneg : 0 <= arctan x ↔ 0 <= x := by
  simpa only [arctan_zero] using arctan_le_arctan_iff (x := 0)

@[simp]
/--
theorem `arctan_le_zero` / 定理 `arctan_le_zero`

English:
theorem arctan_le_zero
  statement: arctan x <= 0 ↔ x <= 0
  proof: by
  simpa only [arctan_zero] using arctan_le_arctan_iff (y := 0)

中文:
定理 arctan_le_zero
  结论: arctan x <= 0 ↔ x <= 0
  证明: by
  simpa only [arctan_zero] using arctan_le_arctan_iff (y := 0)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, arctan_le_arctan_iff, arctan_zero
-/
theorem arctan_le_zero : arctan x <= 0 ↔ x <= 0 := by
  simpa only [arctan_zero] using arctan_le_arctan_iff (y := 0)

/--
theorem `arctan_eq_arccos` / 定理 `arctan_eq_arccos`

English:
theorem arctan_eq_arccos
  given: (h : 0 <= x)
  statement: arctan x = arccos (√(1 + x ^ 2))⁻¹
  proof: by
  rw [arctan_eq_arcsin]; rw [arccos_eq_arcsin]; swap; · exact inv_nonneg.2 (sqrt_nonneg _)
  congr 1
  rw_mod_cast [← sqrt_inv, sq_sqrt, ← one_div, one_sub_div, add_sub_cancel_left, sqrt_div,
    sqrt_sq h]
  all_goals positivity

中文:
定理 arctan_eq_arccos
  条件: (h : 0 <= x)
  结论: arctan x = arccos (√(1 + x ^ 2))⁻¹
  证明: by
  rw [arctan_eq_arcsin]; rw [arccos_eq_arcsin]; swap; · exact inv_nonneg.2 (sqrt_nonneg _)
  congr 1
  rw_mod_cast [← sqrt_inv, sq_sqrt, ← one_div, one_sub_div, add_sub_cancel_left, sqrt_div,
    sqrt_sq h]
  all_goals positivity

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, EssSurj, add_sub_cancel_left, all_goals, arccos_eq_arcsin, arctan_eq_arcsin, inv_nonneg, one_div, one_sub_div, rw_mod_cast, sq_sqrt, sqrt_div, sqrt_inv, sqrt_nonneg, sqrt_sq
-/
theorem arctan_eq_arccos (h : 0 <= x) : arctan x = arccos (√(1 + x ^ 2))⁻¹ := by
  rw [arctan_eq_arcsin]; rw [arccos_eq_arcsin]; swap; · exact inv_nonneg.2 (sqrt_nonneg _)
  congr 1
  rw_mod_cast [← sqrt_inv, sq_sqrt, ← one_div, one_sub_div, add_sub_cancel_left, sqrt_div,
    sqrt_sq h]
  all_goals positivity

-- The junk values for `arccos` and `sqrt` make this true even for `1 < x`.
/--
theorem `arccos_eq_arctan` / 定理 `arccos_eq_arctan`

English:
theorem arccos_eq_arctan
  given: (h : 0 < x)
  statement: arccos x = arctan (√(1 - x ^ 2) / x)
  proof: by
  rw [arccos]; rw [eq_comm]
  refine arctan_eq_of_tan_eq ?_ ⟨?_, ?_⟩
  · rw_mod_cast [tan_pi_div_two_sub, tan_arcsin, inv_div]
  · linarith only [arcsin_le_pi_div_two x, pi_pos]
  · linarith only [arcsin_pos.2 h]

中文:
定理 arccos_eq_arctan
  条件: (h : 0 < x)
  结论: arccos x = arctan (√(1 - x ^ 2) / x)
  证明: by
  rw [arccos]; rw [eq_comm]
  refine arctan_eq_of_tan_eq ?_ ⟨?_, ?_⟩
  · rw_mod_cast [tan_pi_div_two_sub, tan_arcsin, inv_div]
  · linarith only [arcsin_le_pi_div_two x, pi_pos]
  · linarith only [arcsin_pos.2 h]

Depends on / 依赖: arccos, arcsin_le_pi_div_two, arcsin_pos, arctan_eq_of_tan_eq, eq_comm, inv_div, pi_pos, rw_mod_cast, tan_arcsin, tan_pi_div_two_sub
-/
theorem arccos_eq_arctan (h : 0 < x) : arccos x = arctan (√(1 - x ^ 2) / x) := by
  rw [arccos]; rw [eq_comm]
  refine arctan_eq_of_tan_eq ?_ ⟨?_, ?_⟩
  · rw_mod_cast [tan_pi_div_two_sub, tan_arcsin, inv_div]
  · linarith only [arcsin_le_pi_div_two x, pi_pos]
  · linarith only [arcsin_pos.2 h]

/--
theorem `arctan_inv_of_pos` / 定理 `arctan_inv_of_pos`

English:
theorem arctan_inv_of_pos
  given: (h : 0 < x)
  statement: arctan x⁻¹ = π / 2 - arctan x
  proof: by
  rw [← arctan_tan (x := _ - _)]; rw [tan_pi_div_two_sub]; rw [tan_arctan]
  · simpa using (arctan_lt_pi_div_two x).trans (half_lt_self_iff.mpr pi_pos)
  · rw [sub_lt_self_iff, ← arctan_zero]
    exact tanOrderIso.symm.strictMono h

中文:
定理 arctan_inv_of_pos
  条件: (h : 0 < x)
  结论: arctan x⁻¹ = π / 2 - arctan x
  证明: by
  rw [← arctan_tan (x := _ - _)]; rw [tan_pi_div_two_sub]; rw [tan_arctan]
  · simpa using (arctan_lt_pi_div_two x).trans (half_lt_self_iff.mpr pi_pos)
  · rw [sub_lt_self_iff, ← arctan_zero]
    exact tanOrderIso.symm.strictMono h

Depends on / 依赖: arctan_lt_pi_div_two, arctan_tan, arctan_zero, half_lt_self_iff, half_lt_self_iff.mpr, pi_pos, strictMono, sub_lt_self_iff, tanOrderIso, tanOrderIso.symm.strictMono, tan_arctan, tan_pi_div_two_sub
-/
theorem arctan_inv_of_pos (h : 0 < x) : arctan x⁻¹ = π / 2 - arctan x := by
  rw [← arctan_tan (x := _ - _)]; rw [tan_pi_div_two_sub]; rw [tan_arctan]
  · simpa using (arctan_lt_pi_div_two x).trans (half_lt_self_iff.mpr pi_pos)
  · rw [sub_lt_self_iff, ← arctan_zero]
    exact tanOrderIso.symm.strictMono h

/--
theorem `arctan_inv_of_neg` / 定理 `arctan_inv_of_neg`

English:
theorem arctan_inv_of_neg
  given: (h : x < 0)
  statement: arctan x⁻¹ = -(π / 2) - arctan x
  proof: by
  have := arctan_inv_of_pos (neg_pos.mpr h)
  rwa [inv_neg, arctan_neg, neg_eq_iff_eq_neg, neg_sub', arctan_neg, neg_neg] at this

中文:
定理 arctan_inv_of_neg
  条件: (h : x < 0)
  结论: arctan x⁻¹ = -(π / 2) - arctan x
  证明: by
  have := arctan_inv_of_pos (neg_pos.mpr h)
  rwa [inv_neg, arctan_neg, neg_eq_iff_eq_neg, neg_sub', arctan_neg, neg_neg] at this

Depends on / 依赖: arctan_inv_of_pos, arctan_neg, inv_neg, neg_eq_iff_eq_neg, neg_neg, neg_pos, neg_pos.mpr, neg_sub
-/
theorem arctan_inv_of_neg (h : x < 0) : arctan x⁻¹ = -(π / 2) - arctan x := by
  have := arctan_inv_of_pos (neg_pos.mpr h)
  rwa [inv_neg, arctan_neg, neg_eq_iff_eq_neg, neg_sub', arctan_neg, neg_neg] at this

section ArctanAdd

/--
lemma `arctan_ne_mul_pi_div_two` / 引理 `arctan_ne_mul_pi_div_two`

English:
lemma arctan_ne_mul_pi_div_two
  statement: forall (k : Int), arctan x != (2 * k + 1) * π / 2
  proof: by
  by_contra! ⟨k, h⟩
  obtain ⟨lb, ub⟩ := arctan_mem_Ioo x
  rw [h]; rw [neg_eq_neg_one_mul]; rw [mul_div_assoc]; rw [mul_lt_mul_iff_left₀ (by positivity)] at lb
  rw [h]; rw [← one_mul (π / 2)]; rw [mul_div_assoc]; rw [mul_lt_mul_iff_left₀ (by positivity)] at ub
  norm_cast at lb ub; change -1 < 

中文:
引理 arctan_ne_mul_pi_div_two
  结论: 对任意 (k : 整数), arctan x != (2 * k + 1) * π / 2
  证明: by
  by_contra! ⟨k, h⟩
  obtain ⟨lb, ub⟩ := arctan_mem_Ioo x
  rw [h]; rw [neg_eq_neg_one_mul]; rw [mul_div_assoc]; rw [mul_lt_mul_iff_left₀ (by positivity)] at lb
  rw [h]; rw [← one_mul (π / 2)]; rw [mul_div_assoc]; rw [mul_lt_mul_iff_left₀ (by positivity)] at ub
  norm_cast at lb ub; change -1 < 

Depends on / 依赖: arctan_mem_Ioo, mul_div_assoc, neg_eq_neg_one_mul, one_mul
-/
lemma arctan_ne_mul_pi_div_two : forall (k : Int), arctan x != (2 * k + 1) * π / 2 := by
  by_contra! ⟨k, h⟩
  obtain ⟨lb, ub⟩ := arctan_mem_Ioo x
  rw [h]; rw [neg_eq_neg_one_mul]; rw [mul_div_assoc]; rw [mul_lt_mul_iff_left₀ (by positivity)] at lb
  rw [h]; rw [← one_mul (π / 2)]; rw [mul_div_assoc]; rw [mul_lt_mul_iff_left₀ (by positivity)] at ub
  norm_cast at lb ub; change -1 < _ at lb; lia

/--
lemma `arctan_add_arctan_lt_pi_div_two` / 引理 `arctan_add_arctan_lt_pi_div_two`

English:
lemma arctan_add_arctan_lt_pi_div_two
  given: (h : x * y < 1)
  statement: arctan x + arctan y < π / 2
  proof: by
  rcases le_or_gt y 0 with hy | hy
  · rw [← add_zero (π / 2), ← arctan_zero]
    exact add_lt_add_of_lt_of_le (arctan_lt_pi_div_two _) (tanOrderIso.symm.monotone hy)
  · rw [← lt_div_iff₀ hy, ← inv_eq_one_div] at h
    replace h : arctan x < arctan y⁻¹ := tanOrderIso.symm.strictMono h
    rwa [a

中文:
引理 arctan_add_arctan_lt_pi_div_two
  条件: (h : x * y < 1)
  结论: arctan x + arctan y < π / 2
  证明: by
  rcases le_or_gt y 0 with hy | hy
  · rw [← add_zero (π / 2), ← arctan_zero]
    exact add_lt_add_of_lt_of_le (arctan_lt_pi_div_two _) (tanOrderIso.symm.monotone hy)
  · rw [← lt_div_iff₀ hy, ← inv_eq_one_div] at h
    replace h : arctan x < arctan y⁻¹ := tanOrderIso.symm.strictMono h
    rwa [a

Depends on / 依赖: add_lt_add_of_lt_of_le, add_zero, arctan, arctan_inv_of_pos, arctan_lt_pi_div_two, arctan_zero, inv_eq_one_div, le_or_gt, lt_tsub_iff_right, monotone, replace, strictMono, tanOrderIso, tanOrderIso.symm.monotone, tanOrderIso.symm.strictMono
-/
lemma arctan_add_arctan_lt_pi_div_two (h : x * y < 1) : arctan x + arctan y < π / 2 := by
  rcases le_or_gt y 0 with hy | hy
  · rw [← add_zero (π / 2), ← arctan_zero]
    exact add_lt_add_of_lt_of_le (arctan_lt_pi_div_two _) (tanOrderIso.symm.monotone hy)
  · rw [← lt_div_iff₀ hy, ← inv_eq_one_div] at h
    replace h : arctan x < arctan y⁻¹ := tanOrderIso.symm.strictMono h
    rwa [arctan_inv_of_pos hy, lt_tsub_iff_right] at h

/--
theorem `arctan_add` / 定理 `arctan_add`

English:
theorem arctan_add
  given: (h : x * y < 1)
  proof: by
  rw [← arctan_tan (x := _ + _)]
  · congr
    conv_rhs => rw [← tan_arctan x, ← tan_arctan y]
    exact tan_add' ⟨arctan_ne_mul_pi_div_two, arctan_ne_mul_pi_div_two⟩
  · rw [neg_lt, neg_add, ← arctan_neg, ← arctan_neg]
    rw [← neg_mul_neg] at h
    exact arctan_add_arctan_lt_pi_div_two h
  · e

中文:
定理 arctan_add
  条件: (h : x * y < 1)
  证明: by
  rw [← arctan_tan (x := _ + _)]
  · congr
    conv_rhs => rw [← tan_arctan x, ← tan_arctan y]
    exact tan_add' ⟨arctan_ne_mul_pi_div_two, arctan_ne_mul_pi_div_two⟩
  · rw [neg_lt, neg_add, ← arctan_neg, ← arctan_neg]
    rw [← neg_mul_neg] at h
    exact arctan_add_arctan_lt_pi_div_two h
  · e

Depends on / 依赖: Under.Hom, arctan_add_arctan_lt_pi_div_two, arctan_ne_mul_pi_div_two, arctan_neg, arctan_tan, conv_rhs, neg_add, neg_lt, neg_mul_neg, tan_add, tan_arctan
-/
theorem arctan_add (h : x * y < 1) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) := by
  rw [← arctan_tan (x := _ + _)]
  · congr
    conv_rhs => rw [← tan_arctan x, ← tan_arctan y]
    exact tan_add' ⟨arctan_ne_mul_pi_div_two, arctan_ne_mul_pi_div_two⟩
  · rw [neg_lt, neg_add, ← arctan_neg, ← arctan_neg]
    rw [← neg_mul_neg] at h
    exact arctan_add_arctan_lt_pi_div_two h
  · exact arctan_add_arctan_lt_pi_div_two h

/--
theorem `arctan_add_eq_add_pi` / 定理 `arctan_add_eq_add_pi`

English:
theorem arctan_add_eq_add_pi
  given: (h : 1 < x * y) (hx : 0 < x)
  proof: by
  have hy : 0 < y := by
    have := mul_pos_iff.mp (zero_lt_one.trans h)
    simpa [hx, hx.asymm]
  have k := arctan_add (mul_inv x y ▸ inv_lt_one_of_one_lt₀ h)
  rw [arctan_inv_of_pos hx]; rw [arctan_inv_of_pos hy]; rw [show _ + _ = π - (arctan x + arctan y) by ring]; rw [sub_eq_iff_eq_add]; rw 

中文:
定理 arctan_add_eq_add_pi
  条件: (h : 1 < x * y) (hx : 0 < x)
  证明: by
  have hy : 0 < y := by
    have := mul_pos_iff.mp (zero_lt_one.trans h)
    simpa [hx, hx.asymm]
  have k := arctan_add (mul_inv x y ▸ inv_lt_one_of_one_lt₀ h)
  rw [arctan_inv_of_pos hx]; rw [arctan_inv_of_pos hy]; rw [show _ + _ = π - (arctan x + arctan y) by ring]; rw [sub_eq_iff_eq_add]; rw 

Depends on / 依赖: add_comm, arctan, arctan_add, arctan_inv_of_pos, arctan_neg, hx.asymm, mul_inv, mul_pos_iff, mul_pos_iff.mp, sub_eq_add_neg, sub_eq_iff_eq_add, zero_lt_one, zero_lt_one.trans
-/
theorem arctan_add_eq_add_pi (h : 1 < x * y) (hx : 0 < x) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) + π := by
  have hy : 0 < y := by
    have := mul_pos_iff.mp (zero_lt_one.trans h)
    simpa [hx, hx.asymm]
  have k := arctan_add (mul_inv x y ▸ inv_lt_one_of_one_lt₀ h)
  rw [arctan_inv_of_pos hx]; rw [arctan_inv_of_pos hy]; rw [show _ + _ = π - (arctan x + arctan y) by ring]; rw [sub_eq_iff_eq_add]; rw [← sub_eq_iff_eq_add']; rw [sub_eq_add_neg]; rw [← arctan_neg]; rw [add_comm] at k
  grind

/--
theorem `arctan_add_eq_sub_pi` / 定理 `arctan_add_eq_sub_pi`

English:
theorem arctan_add_eq_sub_pi
  given: (h : 1 < x * y) (hx : x < 0)
  proof: by
  rw [← neg_mul_neg] at h
  have k := arctan_add_eq_add_pi h (neg_pos.mpr hx)
  rw [show _ / _ = -((x + y) / (1 - x * y)) by ring]; rw [← neg_inj] at k
  simp only [arctan_neg, neg_add, neg_neg, ← sub_eq_add_neg _ π] at k
  exact k

中文:
定理 arctan_add_eq_sub_pi
  条件: (h : 1 < x * y) (hx : x < 0)
  证明: by
  rw [← neg_mul_neg] at h
  have k := arctan_add_eq_add_pi h (neg_pos.mpr hx)
  rw [show _ / _ = -((x + y) / (1 - x * y)) by ring]; rw [← neg_inj] at k
  simp only [arctan_neg, neg_add, neg_neg, ← sub_eq_add_neg _ π] at k
  exact k

Depends on / 依赖: arctan_add_eq_add_pi, arctan_neg, neg_add, neg_inj, neg_mul_neg, neg_neg, neg_pos, neg_pos.mpr, sub_eq_add_neg
-/
theorem arctan_add_eq_sub_pi (h : 1 < x * y) (hx : x < 0) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) - π := by
  rw [← neg_mul_neg] at h
  have k := arctan_add_eq_add_pi h (neg_pos.mpr hx)
  rw [show _ / _ = -((x + y) / (1 - x * y)) by ring]; rw [← neg_inj] at k
  simp only [arctan_neg, neg_add, neg_neg, ← sub_eq_add_neg _ π] at k
  exact k

/--
theorem `two_mul_arctan` / 定理 `two_mul_arctan`

English:
theorem two_mul_arctan
  given: (h₁ : -1 < x) (h₂ : x < 1)
  proof: by
  rw [two_mul]; rw [arctan_add (by nlinarith)]; congr 1; ring

中文:
定理 two_mul_arctan
  条件: (h₁ : -1 < x) (h₂ : x < 1)
  证明: by
  rw [two_mul]; rw [arctan_add (by nlinarith)]; congr 1; ring

Depends on / 依赖: arctan_add, two_mul
-/
theorem two_mul_arctan (h₁ : -1 < x) (h₂ : x < 1) :
    2 * arctan x = arctan (2 * x / (1 - x ^ 2)) := by
  rw [two_mul]; rw [arctan_add (by nlinarith)]; congr 1; ring

/--
theorem `two_mul_arctan_add_pi` / 定理 `two_mul_arctan_add_pi`

English:
theorem two_mul_arctan_add_pi
  given: (h : 1 < x)
  proof: by
  rw [two_mul]; rw [arctan_add_eq_add_pi (by nlinarith) (by linarith)]; congr 2; ring

中文:
定理 two_mul_arctan_add_pi
  条件: (h : 1 < x)
  证明: by
  rw [two_mul]; rw [arctan_add_eq_add_pi (by nlinarith) (by linarith)]; congr 2; ring

Depends on / 依赖: arctan_add_eq_add_pi, two_mul
-/
theorem two_mul_arctan_add_pi (h : 1 < x) :
    2 * arctan x = arctan (2 * x / (1 - x ^ 2)) + π := by
  rw [two_mul]; rw [arctan_add_eq_add_pi (by nlinarith) (by linarith)]; congr 2; ring

/--
theorem `two_mul_arctan_sub_pi` / 定理 `two_mul_arctan_sub_pi`

English:
theorem two_mul_arctan_sub_pi
  given: (h : x < -1)
  proof: by
  rw [two_mul]; rw [arctan_add_eq_sub_pi (by nlinarith) (by linarith)]; congr 2; ring

中文:
定理 two_mul_arctan_sub_pi
  条件: (h : x < -1)
  证明: by
  rw [two_mul]; rw [arctan_add_eq_sub_pi (by nlinarith) (by linarith)]; congr 2; ring

Depends on / 依赖: arctan_add_eq_sub_pi, two_mul
-/
theorem two_mul_arctan_sub_pi (h : x < -1) :
    2 * arctan x = arctan (2 * x / (1 - x ^ 2)) - π := by
  rw [two_mul]; rw [arctan_add_eq_sub_pi (by nlinarith) (by linarith)]; congr 2; ring

/--
theorem `arctan_inv_2_add_arctan_inv_3` / 定理 `arctan_inv_2_add_arctan_inv_3`

English:
theorem arctan_inv_2_add_arctan_inv_3
  statement: arctan 2⁻¹ + arctan 3⁻¹ = π / 4
  proof: by
  rw [arctan_add] <;> norm_num

中文:
定理 arctan_inv_2_add_arctan_inv_3
  结论: arctan 2⁻¹ + arctan 3⁻¹ = π / 4
  证明: by
  rw [arctan_add] <;> norm_num

Depends on / 依赖: Under.w, arctan_add
-/
theorem arctan_inv_2_add_arctan_inv_3 : arctan 2⁻¹ + arctan 3⁻¹ = π / 4 := by
  rw [arctan_add] <;> norm_num

/--
theorem `two_mul_arctan_inv_2_sub_arctan_inv_7` / 定理 `two_mul_arctan_inv_2_sub_arctan_inv_7`

English:
theorem two_mul_arctan_inv_2_sub_arctan_inv_7
  statement: 2 * arctan 2⁻¹ - arctan 7⁻¹ = π / 4
  proof: by
  rw [two_mul_arctan]; rw [← arctan_one]; rw [sub_eq_iff_eq_add]; rw [arctan_add] <;> norm_num

中文:
定理 two_mul_arctan_inv_2_sub_arctan_inv_7
  结论: 2 * arctan 2⁻¹ - arctan 7⁻¹ = π / 4
  证明: by
  rw [two_mul_arctan]; rw [← arctan_one]; rw [sub_eq_iff_eq_add]; rw [arctan_add] <;> norm_num

Depends on / 依赖: arctan_add, arctan_one, sub_eq_iff_eq_add, two_mul_arctan
-/
theorem two_mul_arctan_inv_2_sub_arctan_inv_7 : 2 * arctan 2⁻¹ - arctan 7⁻¹ = π / 4 := by
  rw [two_mul_arctan]; rw [← arctan_one]; rw [sub_eq_iff_eq_add]; rw [arctan_add] <;> norm_num

/--
theorem `two_mul_arctan_inv_3_add_arctan_inv_7` / 定理 `two_mul_arctan_inv_3_add_arctan_inv_7`

English:
theorem two_mul_arctan_inv_3_add_arctan_inv_7
  statement: 2 * arctan 3⁻¹ + arctan 7⁻¹ = π / 4
  proof: by
  rw [two_mul_arctan]; rw [arctan_add] <;> norm_num

中文:
定理 two_mul_arctan_inv_3_add_arctan_inv_7
  结论: 2 * arctan 3⁻¹ + arctan 7⁻¹ = π / 4
  证明: by
  rw [two_mul_arctan]; rw [arctan_add] <;> norm_num

Depends on / 依赖: arctan_add, two_mul_arctan
-/
theorem two_mul_arctan_inv_3_add_arctan_inv_7 : 2 * arctan 3⁻¹ + arctan 7⁻¹ = π / 4 := by
  rw [two_mul_arctan]; rw [arctan_add] <;> norm_num

/--
theorem `four_mul_arctan_inv_5_sub_arctan_inv_239` / 定理 `four_mul_arctan_inv_5_sub_arctan_inv_239`

English:
theorem four_mul_arctan_inv_5_sub_arctan_inv_239
  statement: 4 * arctan 5⁻¹ - arctan 239⁻¹ = π / 4
  proof: by
  rw [show 4 * arctan _ = 2 * (2 * _) by ring]; rw [two_mul_arctan]; rw [two_mul_arctan]; rw [← arctan_one]; rw [sub_eq_iff_eq_add]; rw [arctan_add] <;> norm_num

中文:
定理 four_mul_arctan_inv_5_sub_arctan_inv_239
  结论: 4 * arctan 5⁻¹ - arctan 239⁻¹ = π / 4
  证明: by
  rw [show 4 * arctan _ = 2 * (2 * _) by ring]; rw [two_mul_arctan]; rw [two_mul_arctan]; rw [← arctan_one]; rw [sub_eq_iff_eq_add]; rw [arctan_add] <;> norm_num

Depends on / 依赖: arctan, arctan_add, arctan_one, sub_eq_iff_eq_add, two_mul_arctan
-/
theorem four_mul_arctan_inv_5_sub_arctan_inv_239 : 4 * arctan 5⁻¹ - arctan 239⁻¹ = π / 4 := by
  rw [show 4 * arctan _ = 2 * (2 * _) by ring]; rw [two_mul_arctan]; rw [two_mul_arctan]; rw [← arctan_one]; rw [sub_eq_iff_eq_add]; rw [arctan_add] <;> norm_num

end ArctanAdd

/--
theorem `sin_arctan_strictMono` / 定理 `sin_arctan_strictMono`

English:
theorem sin_arctan_strictMono
  statement: StrictMono (sin <| arctan ·)
  proof: fun x y h =>
  strictMonoOn_sin (Ioo_subset_Icc_self <| arctan_mem_Ioo x)
    (Ioo_subset_Icc_self <| arctan_mem_Ioo y) (arctan_strictMono h)

@[simp]

中文:
定理 sin_arctan_strictMono
  结论: 严格递增 (sin <| arctan ·)
  证明: fun x y h =>
  strictMonoOn_sin (Ioo_subset_Icc_self <| arctan_mem_Ioo x)
    (Ioo_subset_Icc_self <| arctan_mem_Ioo y) (arctan_strictMono h)

@[simp]
-/
theorem sin_arctan_strictMono : StrictMono (sin <| arctan ·) := fun x y h =>
  strictMonoOn_sin (Ioo_subset_Icc_self <| arctan_mem_Ioo x)
    (Ioo_subset_Icc_self <| arctan_mem_Ioo y) (arctan_strictMono h)

@[simp]
/--
theorem `sin_arctan_pos` / 定理 `sin_arctan_pos`

English:
theorem sin_arctan_pos
  statement: 0 < sin (arctan x) ↔ 0 < x
  proof: by
  simpa using sin_arctan_strictMono.lt_iff_lt (a := 0)

@[simp]

中文:
定理 sin_arctan_pos
  结论: 0 < sin (arctan x) ↔ 0 < x
  证明: by
  simpa using sin_arctan_strictMono.lt_iff_lt (a := 0)

@[simp]

Depends on / 依赖: lt_iff_lt, sin_arctan_strictMono, sin_arctan_strictMono.lt_iff_lt
-/
theorem sin_arctan_pos : 0 < sin (arctan x) ↔ 0 < x := by
  simpa using sin_arctan_strictMono.lt_iff_lt (a := 0)

@[simp]
/--
theorem `sin_arctan_lt_zero` / 定理 `sin_arctan_lt_zero`

English:
theorem sin_arctan_lt_zero
  statement: sin (arctan x) < 0 ↔ x < 0
  proof: by
  simpa using sin_arctan_strictMono.lt_iff_lt (b := 0)

@[simp]

中文:
定理 sin_arctan_lt_zero
  结论: sin (arctan x) < 0 ↔ x < 0
  证明: by
  simpa using sin_arctan_strictMono.lt_iff_lt (b := 0)

@[simp]

Depends on / 依赖: lt_iff_lt, sin_arctan_strictMono, sin_arctan_strictMono.lt_iff_lt
-/
theorem sin_arctan_lt_zero : sin (arctan x) < 0 ↔ x < 0 := by
  simpa using sin_arctan_strictMono.lt_iff_lt (b := 0)

@[simp]
/--
theorem `sin_arctan_eq_zero` / 定理 `sin_arctan_eq_zero`

English:
theorem sin_arctan_eq_zero
  statement: sin (arctan x) = 0 ↔ x = 0
  proof: sin_arctan_strictMono.injective.eq_iff' by simp

@[simp]

中文:
定理 sin_arctan_eq_zero
  结论: sin (arctan x) = 0 ↔ x = 0
  证明: sin_arctan_strictMono.injective.eq_iff' by simp

@[simp]

Depends on / 依赖: eq_iff, injective, sin_arctan_strictMono, sin_arctan_strictMono.injective.eq_iff
-/
theorem sin_arctan_eq_zero : sin (arctan x) = 0 ↔ x = 0 :=
sin_arctan_strictMono.injective.eq_iff' by simp

@[simp]
/--
theorem `sin_arctan_nonneg` / 定理 `sin_arctan_nonneg`

English:
theorem sin_arctan_nonneg
  statement: 0 <= sin (arctan x) ↔ 0 <= x
  proof: by
  simpa using sin_arctan_strictMono.le_iff_le (a := 0)

@[simp]

中文:
定理 sin_arctan_nonneg
  结论: 0 <= sin (arctan x) ↔ 0 <= x
  证明: by
  simpa using sin_arctan_strictMono.le_iff_le (a := 0)

@[simp]

Depends on / 依赖: le_iff_le, sin_arctan_strictMono, sin_arctan_strictMono.le_iff_le
-/
theorem sin_arctan_nonneg : 0 <= sin (arctan x) ↔ 0 <= x := by
  simpa using sin_arctan_strictMono.le_iff_le (a := 0)

@[simp]
/--
theorem `sin_arctan_le_zero` / 定理 `sin_arctan_le_zero`

English:
theorem sin_arctan_le_zero
  statement: sin (arctan x) <= 0 ↔ x <= 0
  proof: by
  simpa using sin_arctan_strictMono.le_iff_le (b := 0)

@[continuity, fun_prop]

中文:
定理 sin_arctan_le_zero
  结论: sin (arctan x) <= 0 ↔ x <= 0
  证明: by
  simpa using sin_arctan_strictMono.le_iff_le (b := 0)

@[continuity, fun_prop]

Depends on / 依赖: le_iff_le, sin_arctan_strictMono, sin_arctan_strictMono.le_iff_le
-/
theorem sin_arctan_le_zero : sin (arctan x) <= 0 ↔ x <= 0 := by
  simpa using sin_arctan_strictMono.le_iff_le (b := 0)

@[continuity, fun_prop]
/--
theorem `continuous_arctan` / 定理 `continuous_arctan`

English:
theorem continuous_arctan
  statement: Continuous arctan
  proof: continuous_subtype_val.comp tanOrderIso.toHomeomorph.continuous_invFun

中文:
定理 continuous_arctan
  结论: 连续 arctan
  证明: continuous_subtype_val.comp tanOrderIso.toHomeomorph.continuous_invFun

Depends on / 依赖: continuous_invFun, continuous_subtype_val, continuous_subtype_val.comp, tanOrderIso, tanOrderIso.toHomeomorph.continuous_invFun, toHomeomorph
-/
theorem continuous_arctan : Continuous arctan :=
  continuous_subtype_val.comp tanOrderIso.toHomeomorph.continuous_invFun

/--
theorem `continuousAt_arctan` / 定理 `continuousAt_arctan`

English:
theorem continuousAt_arctan
  statement: ContinuousAt arctan x
  proof: continuous_arctan.continuousAt

中文:
定理 continuousAt_arctan
  结论: ContinuousAt arctan x
  证明: continuous_arctan.continuousAt

Depends on / 依赖: continuousAt, continuous_arctan, continuous_arctan.continuousAt
-/
theorem continuousAt_arctan : ContinuousAt arctan x :=
  continuous_arctan.continuousAt

/--
Definition of `tanPartialHomeomorph` / `tanPartialHomeomorph` 的定义

English:
definition tanPartialHomeomorph
  signature: : OpenPartialHomeomorph Real Real where
  body: tan
  invFun := arctan
  source := Ioo (-(π / 2)) (π / 2)
  target := univ
  map_source' := mapsTo_univ _ _
  map_target' y _ := arctan_mem_Ioo y
  left_inv' _ hx := arctan_tan hx.1 hx.2
  right_inv' y _ := tan_arctan y
  open_source := isOpen_Ioo
  open_target := isOpen_univ
  continuousOn_toFun :=

中文:
定义 tanPartialHomeomorph
  签名: : OpenPartialHomeomorph 实数 实数 where
  定义体: tan
  invFun := arctan
  source := Ioo (-(π / 2)) (π / 2)
  target := univ
  map_source' := mapsTo_univ _ _
  map_target' y _ := arctan_mem_Ioo y
  left_inv' _ hx := arctan_tan hx.1 hx.2
  right_inv' y _ := tan_arctan y
  open_source := isOpen_Ioo
  open_target := isOpen_univ
  continuousOn_toFun :=
-/
def tanPartialHomeomorph : OpenPartialHomeomorph Real Real where
  toFun := tan
  invFun := arctan
  source := Ioo (-(π / 2)) (π / 2)
  target := univ
  map_source' := mapsTo_univ _ _
  map_target' y _ := arctan_mem_Ioo y
  left_inv' _ hx := arctan_tan hx.1 hx.2
  right_inv' y _ := tan_arctan y
  open_source := isOpen_Ioo
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_tan_Ioo
  continuousOn_invFun := continuous_arctan.continuousOn

@[simp]
/--
theorem `coe_tanPartialHomeomorph` / 定理 `coe_tanPartialHomeomorph`

English:
theorem coe_tanPartialHomeomorph
  statement: ⇑tanPartialHomeomorph = tan
  proof: rfl

@[simp]

中文:
定理 coe_tanPartialHomeomorph
  结论: ⇑tanPartialHomeomorph = tan
  证明: rfl

@[simp]
-/
theorem coe_tanPartialHomeomorph : ⇑tanPartialHomeomorph = tan :=
  rfl

@[simp]
/--
theorem `coe_tanPartialHomeomorph_symm` / 定理 `coe_tanPartialHomeomorph_symm`

English:
theorem coe_tanPartialHomeomorph_symm
  statement: ⇑tanPartialHomeomorph.symm = arctan
  proof: rfl

中文:
定理 coe_tanPartialHomeomorph_symm
  结论: ⇑tanPartialHomeomorph.symm = arctan
  证明: rfl
-/
theorem coe_tanPartialHomeomorph_symm : ⇑tanPartialHomeomorph.symm = arctan :=
  rfl

end Real

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `Real.arctan`. -/
@[positivity Real.arctan _]
meta def evalRealArctan : PositivityExt where eval {u α} z p e :=
  match p with | none => pure .none | some p => do
  match u, α, e with
  | 0, ~q(Real), ~q(Real.arctan $a) =>
    let ra ← core z p a
    match ra with
    | .positive pa =>
      assumeInstancesCommute
      return .positive q(Real.arctan_pos.mpr $pa)
    | .nonnegative na =>
      assumeInstancesCommute
      return .nonnegative q(Real.arctan_nonneg.mpr $na)
    | .nonzero na =>
      assumeInstancesCommute
      return .nonzero q(mt Real.arctan_eq_zero_iff.mp $na)
    | .none => return .none
  | _ => throwError "not Real.arctan"

/-- Extension for `Real.cos (Real.arctan _)`. -/
@[positivity Real.cos (Real.arctan _)]
meta def evalRealCosArctan : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(Real.cos (Real.arctan $a)) =>
    assumeInstancesCommute
    return .positive q(Real.cos_arctan_pos _)
  | _ => throwError "not Real.cos (Real.arctan _)"

/-- Extension for `Real.sin (Real.arctan _)`. -/
@[positivity Real.sin (Real.arctan _)]
meta def evalRealSinArctan : PositivityExt where eval {u α} z p e :=
  match p with | none => pure .none | some p => do
  match u, α, e with
  | 0, ~q(Real), ~q(Real.sin (Real.arctan $a)) =>
    match ← core z p a with
    | .positive pa =>
      assumeInstancesCommute
      return .positive q(Real.sin_arctan_pos.mpr $pa)
    | .nonnegative na =>
      assumeInstancesCommute
      return .nonnegative q(Real.sin_arctan_nonneg.mpr $na)
    | .nonzero na =>
      assumeInstancesCommute
      return .nonzero q(mt Real.sin_arctan_eq_zero.mp $na)
    | .none => return .none
  | _ => throwError "not Real.sin (Real.arctan _)"

end Mathlib.Meta.Positivity
