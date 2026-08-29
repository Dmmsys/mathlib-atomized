/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Square root of a real number

In this file we define

* `NNReal.sqrt` to be the square root of a nonnegative real number.
* `Real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.

Then we prove some basic properties of these functions.

## Implementation notes

We define `NNReal.sqrt` as the noncomputable inverse to the function `x ↦ x * x`. We use general
theory of inverses of strictly monotone functions to prove that `NNReal.sqrt x` exists. As a side
effect, `NNReal.sqrt` is a bundled `OrderIso`, so for `NNReal` numbers we get continuity as well as
theorems like `NNReal.sqrt x ≤ y ↔ x ≤ y * y` for free.

Then we define `Real.sqrt x` to be `NNReal.sqrt (Real.toNNReal x)`.

## Tags

square root
-/

@[expose] public section

open Set Filter
open scoped Filter NNReal Topology

namespace NNReal

variable {x y : Real>=0}

/-- Square root of a nonnegative real number. -/
@[pp_nodot]
/--
Definition of `sqrt` / `sqrt` 的定义

English:
definition sqrt
  signature: : Real>=0 ≃o Real>=0
  body: OrderIso.symm powOrderIso 2 two_ne_zero

中文:
定义 sqrt
  签名: : 实数>=0 ≃o 实数>=0
  定义体: OrderIso.symm powOrderIso 2 two_ne_zero

Depends on / 依赖: OrderIso, OrderIso.symm, powOrderIso, two_ne_zero
-/
noncomputable def sqrt : Real>=0 ≃o Real>=0 :=
OrderIso.symm powOrderIso 2 two_ne_zero

/--
lemma `sq_sqrt` / 引理 `sq_sqrt`

English:
lemma sq_sqrt
  given: (x : Real>=0)
  statement: sqrt x ^ 2 = x
  proof: sqrt.symm_apply_apply _

中文:
引理 sq_sqrt
  条件: (x : 实数>=0)
  结论: sqrt x ^ 2 = x
  证明: sqrt.symm_apply_apply _
-/
@[simp] lemma sq_sqrt (x : Real>=0) : sqrt x ^ 2 = x := sqrt.symm_apply_apply _

/--
lemma `sqrt_sq` / 引理 `sqrt_sq`

English:
lemma sqrt_sq
  given: (x : Real>=0)
  statement: sqrt (x ^ 2) = x
  proof: sqrt.apply_symm_apply _

中文:
引理 sqrt_sq
  条件: (x : 实数>=0)
  结论: sqrt (x ^ 2) = x
  证明: sqrt.apply_symm_apply _
-/
@[simp] lemma sqrt_sq (x : Real>=0) : sqrt (x ^ 2) = x := sqrt.apply_symm_apply _

/--
lemma `mul_self_sqrt` / 引理 `mul_self_sqrt`

English:
lemma mul_self_sqrt
  given: (x : Real>=0)
  statement: sqrt x * sqrt x = x
  proof: by rw [← sq, sq_sqrt]

中文:
引理 mul_self_sqrt
  条件: (x : 实数>=0)
  结论: sqrt x * sqrt x = x
  证明: by rw [← sq, sq_sqrt]
-/
@[simp] lemma mul_self_sqrt (x : Real>=0) : sqrt x * sqrt x = x := by rw [← sq, sq_sqrt]

/--
lemma `sqrt_mul_self` / 引理 `sqrt_mul_self`

English:
lemma sqrt_mul_self
  given: (x : Real>=0)
  statement: sqrt (x * x) = x
  proof: by rw [← sq, sqrt_sq]

中文:
引理 sqrt_mul_self
  条件: (x : 实数>=0)
  结论: sqrt (x * x) = x
  证明: by rw [← sq, sqrt_sq]
-/
@[simp] lemma sqrt_mul_self (x : Real>=0) : sqrt (x * x) = x := by rw [← sq, sqrt_sq]

/--
lemma `sqrt_le_sqrt` / 引理 `sqrt_le_sqrt`

English:
lemma sqrt_le_sqrt
  statement: sqrt x <= sqrt y ↔ x <= y
  proof: sqrt.le_iff_le

中文:
引理 sqrt_le_sqrt
  结论: sqrt x <= sqrt y ↔ x <= y
  证明: sqrt.le_iff_le

Depends on / 依赖: le_iff_le, sqrt.le_iff_le
-/
lemma sqrt_le_sqrt : sqrt x <= sqrt y ↔ x <= y := sqrt.le_iff_le

/--
lemma `sqrt_lt_sqrt` / 引理 `sqrt_lt_sqrt`

English:
lemma sqrt_lt_sqrt
  statement: sqrt x < sqrt y ↔ x < y
  proof: sqrt.lt_iff_lt

中文:
引理 sqrt_lt_sqrt
  结论: sqrt x < sqrt y ↔ x < y
  证明: sqrt.lt_iff_lt

Depends on / 依赖: lt_iff_lt, sqrt.lt_iff_lt
-/
lemma sqrt_lt_sqrt : sqrt x < sqrt y ↔ x < y := sqrt.lt_iff_lt

/--
lemma `sqrt_eq_iff_eq_sq` / 引理 `sqrt_eq_iff_eq_sq`

English:
lemma sqrt_eq_iff_eq_sq
  statement: sqrt x = y ↔ x = y ^ 2
  proof: sqrt.toEquiv.eq_symm_apply.symm

中文:
引理 sqrt_eq_iff_eq_sq
  结论: sqrt x = y ↔ x = y ^ 2
  证明: sqrt.toEquiv.eq_symm_apply.symm

Depends on / 依赖: eq_symm_apply, sqrt.toEquiv.eq_symm_apply.symm, toEquiv
-/
lemma sqrt_eq_iff_eq_sq : sqrt x = y ↔ x = y ^ 2 := sqrt.toEquiv.eq_symm_apply.symm

/--
lemma `sqrt_le_iff_le_sq` / 引理 `sqrt_le_iff_le_sq`

English:
lemma sqrt_le_iff_le_sq
  statement: sqrt x <= y ↔ x <= y ^ 2
  proof: sqrt.to_galoisConnection _ _

中文:
引理 sqrt_le_iff_le_sq
  结论: sqrt x <= y ↔ x <= y ^ 2
  证明: sqrt.to_galoisConnection _ _

Depends on / 依赖: sqrt.to_galoisConnection, to_galoisConnection
-/
lemma sqrt_le_iff_le_sq : sqrt x <= y ↔ x <= y ^ 2 := sqrt.to_galoisConnection _ _

/--
lemma `le_sqrt_iff_sq_le` / 引理 `le_sqrt_iff_sq_le`

English:
lemma le_sqrt_iff_sq_le
  statement: x <= sqrt y ↔ x ^ 2 <= y
  proof: (sqrt.symm.to_galoisConnection _ _).symm

中文:
引理 le_sqrt_iff_sq_le
  结论: x <= sqrt y ↔ x ^ 2 <= y
  证明: (sqrt.symm.to_galoisConnection _ _).symm

Depends on / 依赖: sqrt.symm.to_galoisConnection, to_galoisConnection
-/
lemma le_sqrt_iff_sq_le : x <= sqrt y ↔ x ^ 2 <= y := (sqrt.symm.to_galoisConnection _ _).symm

/--
lemma `sqrt_eq_zero` / 引理 `sqrt_eq_zero`

English:
lemma sqrt_eq_zero
  statement: sqrt x = 0 ↔ x = 0
  proof: by simp [sqrt_eq_iff_eq_sq]

中文:
引理 sqrt_eq_zero
  结论: sqrt x = 0 ↔ x = 0
  证明: by simp [sqrt_eq_iff_eq_sq]
-/
@[simp] lemma sqrt_eq_zero : sqrt x = 0 ↔ x = 0 := by simp [sqrt_eq_iff_eq_sq]

/--
lemma `sqrt_eq_one` / 引理 `sqrt_eq_one`

English:
lemma sqrt_eq_one
  statement: sqrt x = 1 ↔ x = 1
  proof: by simp [sqrt_eq_iff_eq_sq]

中文:
引理 sqrt_eq_one
  结论: sqrt x = 1 ↔ x = 1
  证明: by simp [sqrt_eq_iff_eq_sq]
-/
@[simp] lemma sqrt_eq_one : sqrt x = 1 ↔ x = 1 := by simp [sqrt_eq_iff_eq_sq]

/--
lemma `sqrt_zero` / 引理 `sqrt_zero`

English:
lemma sqrt_zero
  statement: sqrt 0 = 0
  proof: by simp

中文:
引理 sqrt_zero
  结论: sqrt 0 = 0
  证明: by simp
-/
@[simp] lemma sqrt_zero : sqrt 0 = 0 := by simp

/--
lemma `sqrt_one` / 引理 `sqrt_one`

English:
lemma sqrt_one
  statement: sqrt 1 = 1
  proof: by simp

中文:
引理 sqrt_one
  结论: sqrt 1 = 1
  证明: by simp
-/
@[simp] lemma sqrt_one : sqrt 1 = 1 := by simp

/--
lemma `sqrt_le_one` / 引理 `sqrt_le_one`

English:
lemma sqrt_le_one
  statement: sqrt x <= 1 ↔ x <= 1
  proof: by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]

中文:
引理 sqrt_le_one
  结论: sqrt x <= 1 ↔ x <= 1
  证明: by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]
-/
@[simp] lemma sqrt_le_one : sqrt x <= 1 ↔ x <= 1 := by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]
/--
lemma `one_le_sqrt` / 引理 `one_le_sqrt`

English:
lemma one_le_sqrt
  statement: 1 <= sqrt x ↔ 1 <= x
  proof: by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]

中文:
引理 one_le_sqrt
  结论: 1 <= sqrt x ↔ 1 <= x
  证明: by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]
-/
@[simp] lemma one_le_sqrt : 1 <= sqrt x ↔ 1 <= x := by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]

/--
lemma `sqrt_mul_le_max` / 引理 `sqrt_mul_le_max`

English:
lemma sqrt_mul_le_max
  statement: sqrt (x * y) <= max x y
  proof: by
  rw [sqrt_le_iff_le_sq]; rw [sq]; gcongr <;> simp

中文:
引理 sqrt_mul_le_max
  结论: sqrt (x * y) <= 最大值 x y
  证明: by
  rw [sqrt_le_iff_le_sq]; rw [sq]; gcongr <;> simp

Depends on / 依赖: sqrt_le_iff_le_sq
-/
lemma sqrt_mul_le_max : sqrt (x * y) <= max x y := by
  rw [sqrt_le_iff_le_sq]; rw [sq]; gcongr <;> simp

/--
theorem `sqrt_mul` / 定理 `sqrt_mul`

English:
theorem sqrt_mul
  given: (x y : Real>=0)
  statement: sqrt (x * y) = sqrt x * sqrt y
  proof: by
  rw [sqrt_eq_iff_eq_sq]; rw [mul_pow]; rw [sq_sqrt]; rw [sq_sqrt]

中文:
定理 sqrt_mul
  条件: (x y : 实数>=0)
  结论: sqrt (x * y) = sqrt x * sqrt y
  证明: by
  rw [sqrt_eq_iff_eq_sq]; rw [mul_pow]; rw [sq_sqrt]; rw [sq_sqrt]

Depends on / 依赖: mul_pow, sq_sqrt, sqrt_eq_iff_eq_sq
-/
theorem sqrt_mul (x y : Real>=0) : sqrt (x * y) = sqrt x * sqrt y := by
  rw [sqrt_eq_iff_eq_sq]; rw [mul_pow]; rw [sq_sqrt]; rw [sq_sqrt]

/--
Definition of `sqrtHom` / `sqrtHom` 的定义

English:
definition sqrtHom
  signature: : Real>=0 ->*₀ Real>=0
  body: ⟨⟨sqrt, sqrt_zero⟩, sqrt_one, sqrt_mul⟩

中文:
定义 sqrtHom
  签名: : 实数>=0 ->*₀ 实数>=0
  定义体: ⟨⟨sqrt, sqrt_zero⟩, sqrt_one, sqrt_mul⟩

Depends on / 依赖: sqrt_mul, sqrt_one, sqrt_zero
-/
noncomputable def sqrtHom : Real>=0 ->*₀ Real>=0 :=
  ⟨⟨sqrt, sqrt_zero⟩, sqrt_one, sqrt_mul⟩

/--
theorem `sqrt_inv` / 定理 `sqrt_inv`

English:
theorem sqrt_inv
  given: (x : Real>=0)
  statement: sqrt x⁻¹ = (sqrt x)⁻¹
  proof: map_inv₀ sqrtHom x

中文:
定理 sqrt_inv
  条件: (x : 实数>=0)
  结论: sqrt x⁻¹ = (sqrt x)⁻¹
  证明: map_inv₀ sqrtHom x

Depends on / 依赖: sqrtHom
-/
theorem sqrt_inv (x : Real>=0) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
  map_inv₀ sqrtHom x

/--
theorem `sqrt_div` / 定理 `sqrt_div`

English:
theorem sqrt_div
  given: (x y : Real>=0)
  statement: sqrt (x / y) = sqrt x / sqrt y
  proof: map_div₀ sqrtHom x y

@[continuity, fun_prop]

中文:
定理 sqrt_div
  条件: (x y : 实数>=0)
  结论: sqrt (x / y) = sqrt x / sqrt y
  证明: map_div₀ sqrtHom x y

@[continuity, fun_prop]

Depends on / 依赖: sqrtHom
-/
theorem sqrt_div (x y : Real>=0) : sqrt (x / y) = sqrt x / sqrt y :=
  map_div₀ sqrtHom x y

@[continuity, fun_prop]
/--
theorem `continuous_sqrt` / 定理 `continuous_sqrt`

English:
theorem continuous_sqrt
  statement: Continuous sqrt
  proof: sqrt.continuous

中文:
定理 continuous_sqrt
  结论: 连续 sqrt
  证明: sqrt.continuous

Depends on / 依赖: continuous, sqrt.continuous
-/
theorem continuous_sqrt : Continuous sqrt := sqrt.continuous

/--
theorem `sqrt_pos` / 定理 `sqrt_pos`

English:
theorem sqrt_pos
  statement: 0 < sqrt x ↔ 0 < x
  proof: by simp [pos_iff_ne_zero]

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

中文:
定理 sqrt_pos
  结论: 0 < sqrt x ↔ 0 < x
  证明: by simp [pos_iff_ne_zero]

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

Depends on / 依赖: isCorepresentable, shrinkCoyonedaCorepresentableBy
-/
@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x := by simp [pos_iff_ne_zero]

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

attribute [bound] sqrt_pos_of_pos

.symm⟩ @[simp] theorem isSquare (x : Real>=0) : IsSquare x := ⟨_, mul_self_sqrt _

end NNReal

namespace Real

/--
Definition of `sqrt` / `sqrt` 的定义

English:
definition sqrt
  signature: (x : Real)
  body: NNReal.sqrt (Real.toNNReal x)

中文:
定义 sqrt
  签名: (x : 实数)
  定义体: NNReal.sqrt (Real.toNNReal x)
-/
@[irreducible] noncomputable def sqrt (x : Real) : Real :=
  NNReal.sqrt (Real.toNNReal x)

-- TODO: replace this with a typeclass
@[inherit_doc]
prefix:max "√" => Real.sqrt

variable {x y : Real}

@[simp, norm_cast]
/--
theorem `coe_sqrt` / 定理 `coe_sqrt`

English:
theorem coe_sqrt
  given: {x : Real>=0}
  statement: (NNReal.sqrt x : Real) = √(x : Real)
  proof: by
  rw [Real.sqrt]; rw [Real.toNNReal_coe]

@[continuity, fun_prop]

中文:
定理 coe_sqrt
  条件: {x : 实数>=0}
  结论: (非负实数.sqrt x : 实数) = √(x : 实数)
  证明: by
  rw [Real.sqrt]; rw [Real.toNNReal_coe]

@[continuity, fun_prop]

Depends on / 依赖: Real.sqrt, Real.toNNReal_coe, toNNReal_coe
-/
theorem coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : Real) := by
  rw [Real.sqrt]; rw [Real.toNNReal_coe]

@[continuity, fun_prop]
/--
theorem `continuous_sqrt` / 定理 `continuous_sqrt`

English:
theorem continuous_sqrt
  statement: Continuous (√· : Real -> Real)
  proof: by unfold sqrt; fun_prop

@[simp]

中文:
定理 continuous_sqrt
  结论: 连续 (√· : 实数 -> 实数)
  证明: by unfold sqrt; fun_prop

@[simp]

Depends on / 依赖: fun_prop
-/
theorem continuous_sqrt : Continuous (√· : Real -> Real) := by unfold sqrt; fun_prop

@[simp]
/--
lemma `map_sqrt_atTop` / 引理 `map_sqrt_atTop`

English:
lemma map_sqrt_atTop
  statement: map (√·) atTop = atTop
  proof: by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← map_map]

@[simp]

中文:
引理 map_sqrt_atTop
  结论: map (√·) atTop = atTop
  证明: by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← map_map]

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_def, map_map, simp_rw
-/
lemma map_sqrt_atTop : map (√·) atTop = atTop := by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← map_map]

@[simp]
/--
lemma `comap_sqrt_atTop` / 引理 `comap_sqrt_atTop`

English:
lemma comap_sqrt_atTop
  statement: comap (√·) atTop = atTop
  proof: by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← comap_comap]

中文:
引理 comap_sqrt_atTop
  结论: comap (√·) atTop = atTop
  证明: by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← comap_comap]

Depends on / 依赖: Function, Function.comp_def, comap_comap, comp_def, simp_rw
-/
lemma comap_sqrt_atTop : comap (√·) atTop = atTop := by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← comap_comap]

/--
lemma `tendsto_sqrt_atTop` / 引理 `tendsto_sqrt_atTop`

English:
lemma tendsto_sqrt_atTop
  statement: Tendsto (√·) atTop atTop
  proof: map_sqrt_atTop.le

中文:
引理 tendsto_sqrt_atTop
  结论: 收敛 (√·) atTop atTop
  证明: map_sqrt_atTop.le

Depends on / 依赖: map_sqrt_atTop, map_sqrt_atTop.le
-/
lemma tendsto_sqrt_atTop : Tendsto (√·) atTop atTop := map_sqrt_atTop.le

/--
theorem `sqrt_eq_zero_of_nonpos` / 定理 `sqrt_eq_zero_of_nonpos`

English:
theorem sqrt_eq_zero_of_nonpos
  given: (h : x <= 0)
  statement: √x = 0
  proof: by simp [sqrt, Real.toNNReal_eq_zero.2 h]

中文:
定理 sqrt_eq_zero_of_nonpos
  条件: (h : x <= 0)
  结论: √x = 0
  证明: by simp [sqrt, Real.toNNReal_eq_zero.2 h]

Depends on / 依赖: Real.toNNReal_eq_zero, toNNReal_eq_zero
-/
theorem sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 0 := by simp [sqrt, Real.toNNReal_eq_zero.2 h]

/--
theorem `sqrt_nonneg` / 定理 `sqrt_nonneg`

English:
theorem sqrt_nonneg
  given: (x : Real)
  statement: 0 <= √x
  proof: by
  unfold sqrt
  exact NNReal.coe_nonneg _

@[simp]

中文:
定理 sqrt_nonneg
  条件: (x : 实数)
  结论: 0 <= √x
  证明: by
  unfold sqrt
  exact NNReal.coe_nonneg _

@[simp]
-/
@[simp] theorem sqrt_nonneg (x : Real) : 0 <= √x := by
  unfold sqrt
  exact NNReal.coe_nonneg _

@[simp]
/--
theorem `mul_self_sqrt` / 定理 `mul_self_sqrt`

English:
theorem mul_self_sqrt
  given: (h : 0 <= x)
  statement: √x * √x = x
  proof: by
  rw [Real.sqrt]; rw [← NNReal.coe_mul]; rw [NNReal.mul_self_sqrt]; rw [Real.coe_toNNReal _ h]

@[simp]

中文:
定理 mul_self_sqrt
  条件: (h : 0 <= x)
  结论: √x * √x = x
  证明: by
  rw [Real.sqrt]; rw [← NNReal.coe_mul]; rw [NNReal.mul_self_sqrt]; rw [Real.coe_toNNReal _ h]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_mul, NNReal.mul_self_sqrt, Real.coe_toNNReal, Real.sqrt, coe_mul, coe_toNNReal, mul_self_sqrt
-/
theorem mul_self_sqrt (h : 0 <= x) : √x * √x = x := by
  rw [Real.sqrt]; rw [← NNReal.coe_mul]; rw [NNReal.mul_self_sqrt]; rw [Real.coe_toNNReal _ h]

@[simp]
/--
theorem `sqrt_mul_self` / 定理 `sqrt_mul_self`

English:
theorem sqrt_mul_self
  given: (h : 0 <= x)
  statement: √(x * x) = x
  proof: (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))

中文:
定理 sqrt_mul_self
  条件: (h : 0 <= x)
  结论: √(x * x) = x
  证明: (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))

Depends on / 依赖: mul_self_inj_of_nonneg, mul_self_nonneg, mul_self_sqrt, sqrt_nonneg
-/
theorem sqrt_mul_self (h : 0 <= x) : √(x * x) = x :=
  (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))

/--
theorem `sqrt_eq_cases` / 定理 `sqrt_eq_cases`

English:
theorem sqrt_eq_cases
  statement: √x = y ↔ y * y = x ∧ 0 <= y ∨ x < 0 ∧ y = 0
  proof: by
  constructor
  · rintro rfl
    rcases le_or_gt 0 x with hle | hlt
    · exact Or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩
    · exact Or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
    exacts [sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le]

中文:
定理 sqrt_eq_cases
  结论: √x = y ↔ y * y = x ∧ 0 <= y ∨ x < 0 ∧ y = 0
  证明: by
  constructor
  · rintro rfl
    rcases le_or_gt 0 x with hle | hlt
    · exact Or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩
    · exact Or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
    exacts [sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le]

Depends on / 依赖: Or.inl, Or.inr, exacts, hlt.le, hx.le, id_nonzero, le_or_gt, mul_self_sqrt, nontrivial_of_ne, sqrt_eq_zero_of_nonpos, sqrt_mul_self, sqrt_nonneg
-/
theorem sqrt_eq_cases : √x = y ↔ y * y = x ∧ 0 <= y ∨ x < 0 ∧ y = 0 := by
  constructor
  · rintro rfl
    rcases le_or_gt 0 x with hle | hlt
    · exact Or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩
    · exact Or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
    exacts [sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le]

/--
theorem `sqrt_eq_iff_mul_self_eq` / 定理 `sqrt_eq_iff_mul_self_eq`

English:
theorem sqrt_eq_iff_mul_self_eq
  given: (hx : 0 <= x) (hy : 0 <= y)
  statement: √x = y ↔ x = y * y
  proof: ⟨fun h => by rw [← h, mul_self_sqrt hx], fun h => by rw [h, sqrt_mul_self hy]⟩

中文:
定理 sqrt_eq_iff_mul_self_eq
  条件: (hx : 0 <= x) (hy : 0 <= y)
  结论: √x = y ↔ x = y * y
  证明: ⟨fun h => by rw [← h, mul_self_sqrt hx], fun h => by rw [h, sqrt_mul_self hy]⟩

Depends on / 依赖: mul_self_sqrt, sqrt_mul_self
-/
theorem sqrt_eq_iff_mul_self_eq (hx : 0 <= x) (hy : 0 <= y) : √x = y ↔ x = y * y :=
  ⟨fun h => by rw [← h, mul_self_sqrt hx], fun h => by rw [h, sqrt_mul_self hy]⟩

/--
theorem `sqrt_eq_iff_mul_self_eq_of_pos` / 定理 `sqrt_eq_iff_mul_self_eq_of_pos`

English:
theorem sqrt_eq_iff_mul_self_eq_of_pos
  given: (h : 0 < y)
  statement: √x = y ↔ y * y = x
  proof: by
  simp [sqrt_eq_cases, h.ne', h.le]

@[simp]

中文:
定理 sqrt_eq_iff_mul_self_eq_of_pos
  条件: (h : 0 < y)
  结论: √x = y ↔ y * y = x
  证明: by
  simp [sqrt_eq_cases, h.ne', h.le]

@[simp]

Depends on / 依赖: h.le, h.ne, sqrt_eq_cases
-/
theorem sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) : √x = y ↔ y * y = x := by
  simp [sqrt_eq_cases, h.ne', h.le]

@[simp]
/--
theorem `sqrt_eq_one` / 定理 `sqrt_eq_one`

English:
theorem sqrt_eq_one
  statement: √x = 1 ↔ x = 1
  proof: calc
    √x = 1 ↔ 1 * 1 = x := sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
    _ ↔ x = 1 := by rw [eq_comm, mul_one]

@[simp]

中文:
定理 sqrt_eq_one
  结论: √x = 1 ↔ x = 1
  证明: calc
    √x = 1 ↔ 1 * 1 = x := sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
    _ ↔ x = 1 := by rw [eq_comm, mul_one]

@[simp]

Depends on / 依赖: eq_comm, mul_one, sqrt_eq_iff_mul_self_eq_of_pos, zero_lt_one
-/
theorem sqrt_eq_one : √x = 1 ↔ x = 1 :=
  calc
    √x = 1 ↔ 1 * 1 = x := sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
    _ ↔ x = 1 := by rw [eq_comm, mul_one]

@[simp]
/--
theorem `sq_sqrt` / 定理 `sq_sqrt`

English:
theorem sq_sqrt
  given: (h : 0 <= x)
  statement: √x ^ 2 = x
  proof: by rw [sq, mul_self_sqrt h]

@[simp]

中文:
定理 sq_sqrt
  条件: (h : 0 <= x)
  结论: √x ^ 2 = x
  证明: by rw [sq, mul_self_sqrt h]

@[simp]

Depends on / 依赖: mul_self_sqrt
-/
theorem sq_sqrt (h : 0 <= x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]

@[simp]
/--
theorem `sqrt_sq` / 定理 `sqrt_sq`

English:
theorem sqrt_sq
  given: (h : 0 <= x)
  statement: √(x ^ 2) = x
  proof: by rw [sq, sqrt_mul_self h]

中文:
定理 sqrt_sq
  条件: (h : 0 <= x)
  结论: √(x ^ 2) = x
  证明: by rw [sq, sqrt_mul_self h]

Depends on / 依赖: sqrt_mul_self
-/
theorem sqrt_sq (h : 0 <= x) : √(x ^ 2) = x := by rw [sq, sqrt_mul_self h]

/--
theorem `sqrt_eq_iff_eq_sq` / 定理 `sqrt_eq_iff_eq_sq`

English:
theorem sqrt_eq_iff_eq_sq
  given: (hx : 0 <= x) (hy : 0 <= y)
  statement: √x = y ↔ x = y ^ 2
  proof: by
  rw [sq]; rw [sqrt_eq_iff_mul_self_eq hx hy]

中文:
定理 sqrt_eq_iff_eq_sq
  条件: (hx : 0 <= x) (hy : 0 <= y)
  结论: √x = y ↔ x = y ^ 2
  证明: by
  rw [sq]; rw [sqrt_eq_iff_mul_self_eq hx hy]

Depends on / 依赖: sqrt_eq_iff_mul_self_eq
-/
theorem sqrt_eq_iff_eq_sq (hx : 0 <= x) (hy : 0 <= y) : √x = y ↔ x = y ^ 2 := by
  rw [sq]; rw [sqrt_eq_iff_mul_self_eq hx hy]

/--
theorem `sqrt_mul_self_eq_abs` / 定理 `sqrt_mul_self_eq_abs`

English:
theorem sqrt_mul_self_eq_abs
  given: (x : Real)
  statement: √(x * x) = |x|
  proof: by
  rw [← abs_mul_abs_self x]; rw [sqrt_mul_self (abs_nonneg _)]

中文:
定理 sqrt_mul_self_eq_abs
  条件: (x : 实数)
  结论: √(x * x) = |x|
  证明: by
  rw [← abs_mul_abs_self x]; rw [sqrt_mul_self (abs_nonneg _)]

Depends on / 依赖: abs_mul_abs_self, abs_nonneg, sqrt_mul_self
-/
theorem sqrt_mul_self_eq_abs (x : Real) : √(x * x) = |x| := by
  rw [← abs_mul_abs_self x]; rw [sqrt_mul_self (abs_nonneg _)]

/--
theorem `sqrt_sq_eq_abs` / 定理 `sqrt_sq_eq_abs`

English:
theorem sqrt_sq_eq_abs
  given: (x : Real)
  statement: √(x ^ 2) = |x|
  proof: by rw [sq, sqrt_mul_self_eq_abs]

@[simp, grind =]

中文:
定理 sqrt_sq_eq_abs
  条件: (x : 实数)
  结论: √(x ^ 2) = |x|
  证明: by rw [sq, sqrt_mul_self_eq_abs]

@[simp, grind =]

Depends on / 依赖: sqrt_mul_self_eq_abs
-/
theorem sqrt_sq_eq_abs (x : Real) : √(x ^ 2) = |x| := by rw [sq, sqrt_mul_self_eq_abs]

@[simp, grind =]
/--
theorem `sqrt_zero` / 定理 `sqrt_zero`

English:
theorem sqrt_zero
  statement: √0 = 0
  proof: by simp [Real.sqrt]

@[simp, grind =]

中文:
定理 sqrt_zero
  结论: √0 = 0
  证明: by simp [Real.sqrt]

@[simp, grind =]

Depends on / 依赖: Real.sqrt, Simple, Simple.not_isZero, nontrivial_of_not_isZero, not_isZero
-/
theorem sqrt_zero : √0 = 0 := by simp [Real.sqrt]

@[simp, grind =]
/--
theorem `sqrt_one` / 定理 `sqrt_one`

English:
theorem sqrt_one
  statement: √1 = 1
  proof: by simp [Real.sqrt]

@[simp]

中文:
定理 sqrt_one
  结论: √1 = 1
  证明: by simp [Real.sqrt]

@[simp]

Depends on / 依赖: Or.inl, Or.inr, Real.sqrt, Simple, Simple.mono_isIso_iff_nonzero, Subobject, Subobject.mk_surjective, isIso_iff_mk_eq_top, mk_eq_bot_iff_zero, mk_eq_bot_iff_zero.mpr, mk_surjective, mono_isIso_iff_nonzero
-/
theorem sqrt_one : √1 = 1 := by simp [Real.sqrt]

@[simp]
/--
theorem `sqrt_le_sqrt_iff` / 定理 `sqrt_le_sqrt_iff`

English:
theorem sqrt_le_sqrt_iff
  given: (hy : 0 <= y)
  statement: √x <= √y ↔ x <= y
  proof: by
  rw [Real.sqrt]; rw [Real.sqrt]; rw [NNReal.coe_le_coe]; rw [NNReal.sqrt_le_sqrt]; rw [toNNReal_le_toNNReal_iff hy]

@[simp]

中文:
定理 sqrt_le_sqrt_iff
  条件: (hy : 0 <= y)
  结论: √x <= √y ↔ x <= y
  证明: by
  rw [Real.sqrt]; rw [Real.sqrt]; rw [NNReal.coe_le_coe]; rw [NNReal.sqrt_le_sqrt]; rw [toNNReal_le_toNNReal_iff hy]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt, Real.sqrt, coe_le_coe, sqrt_le_sqrt, toNNReal_le_toNNReal_iff
-/
theorem sqrt_le_sqrt_iff (hy : 0 <= y) : √x <= √y ↔ x <= y := by
  rw [Real.sqrt]; rw [Real.sqrt]; rw [NNReal.coe_le_coe]; rw [NNReal.sqrt_le_sqrt]; rw [toNNReal_le_toNNReal_iff hy]

@[simp]
/--
theorem `sqrt_lt_sqrt_iff` / 定理 `sqrt_lt_sqrt_iff`

English:
theorem sqrt_lt_sqrt_iff
  given: (hx : 0 <= x)
  statement: √x < √y ↔ x < y
  proof: lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)

中文:
定理 sqrt_lt_sqrt_iff
  条件: (hx : 0 <= x)
  结论: √x < √y ↔ x < y
  证明: lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)

Depends on / 依赖: lt_iff_lt_of_le_iff_le, sqrt_le_sqrt_iff
-/
theorem sqrt_lt_sqrt_iff (hx : 0 <= x) : √x < √y ↔ x < y :=
  lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)

/--
theorem `sqrt_lt_sqrt_iff_of_pos` / 定理 `sqrt_lt_sqrt_iff_of_pos`

English:
theorem sqrt_lt_sqrt_iff_of_pos
  given: (hy : 0 < y)
  statement: √x < √y ↔ x < y
  proof: by
  rw [Real.sqrt]; rw [Real.sqrt]; rw [NNReal.coe_lt_coe]; rw [NNReal.sqrt_lt_sqrt]; rw [toNNReal_lt_toNNReal_iff hy]

@[bound]

中文:
定理 sqrt_lt_sqrt_iff_of_pos
  条件: (hy : 0 < y)
  结论: √x < √y ↔ x < y
  证明: by
  rw [Real.sqrt]; rw [Real.sqrt]; rw [NNReal.coe_lt_coe]; rw [NNReal.sqrt_lt_sqrt]; rw [toNNReal_lt_toNNReal_iff hy]

@[bound]

Depends on / 依赖: NNReal, NNReal.coe_lt_coe, NNReal.sqrt_lt_sqrt, Real.sqrt, coe_lt_coe, sqrt_lt_sqrt, toNNReal_lt_toNNReal_iff
-/
theorem sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : √x < √y ↔ x < y := by
  rw [Real.sqrt]; rw [Real.sqrt]; rw [NNReal.coe_lt_coe]; rw [NNReal.sqrt_lt_sqrt]; rw [toNNReal_lt_toNNReal_iff hy]

@[bound]
/--
theorem `sqrt_le_sqrt` / 定理 `sqrt_le_sqrt`

English:
theorem sqrt_le_sqrt
  given: (h : x <= y)
  statement: √x <= √y
  proof: by
  rw [Real.sqrt]; rw [Real.sqrt]; rw [NNReal.coe_le_coe]; rw [NNReal.sqrt_le_sqrt]
  exact toNNReal_le_toNNReal h

@[gcongr]

中文:
定理 sqrt_le_sqrt
  条件: (h : x <= y)
  结论: √x <= √y
  证明: by
  rw [Real.sqrt]; rw [Real.sqrt]; rw [NNReal.coe_le_coe]; rw [NNReal.sqrt_le_sqrt]
  exact toNNReal_le_toNNReal h

@[gcongr]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt, Real.sqrt, coe_le_coe, sqrt_le_sqrt, toNNReal_le_toNNReal
-/
theorem sqrt_le_sqrt (h : x <= y) : √x <= √y := by
  rw [Real.sqrt]; rw [Real.sqrt]; rw [NNReal.coe_le_coe]; rw [NNReal.sqrt_le_sqrt]
  exact toNNReal_le_toNNReal h

@[gcongr]
/--
theorem `sqrt_monotone` / 定理 `sqrt_monotone`

English:
theorem sqrt_monotone
  statement: Monotone Real.sqrt
  proof: fun _ _ => sqrt_le_sqrt

中文:
定理 sqrt_monotone
  结论: 递增 实数.sqrt
  证明: fun _ _ => sqrt_le_sqrt

Depends on / 依赖: sqrt_le_sqrt
-/
theorem sqrt_monotone : Monotone Real.sqrt :=
  fun _ _ => sqrt_le_sqrt

/--
theorem `strictMonoOn_sqrt` / 定理 `strictMonoOn_sqrt`

English:
theorem strictMonoOn_sqrt
  statement: StrictMonoOn sqrt (Ici 0)
  proof: fun _ ha _ _ h => (sqrt_lt_sqrt_iff ha).mpr h

@[gcongr, bound]

中文:
定理 strictMonoOn_sqrt
  结论: StrictMonoOn sqrt (左闭右无界区间 0)
  证明: fun _ ha _ _ h => (sqrt_lt_sqrt_iff ha).mpr h

@[gcongr, bound]

Depends on / 依赖: sqrt_lt_sqrt_iff
-/
theorem strictMonoOn_sqrt : StrictMonoOn sqrt (Ici 0) :=
  fun _ ha _ _ h => (sqrt_lt_sqrt_iff ha).mpr h

@[gcongr, bound]
/--
theorem `sqrt_lt_sqrt` / 定理 `sqrt_lt_sqrt`

English:
theorem sqrt_lt_sqrt
  given: (hx : 0 <= x) (h : x < y)
  statement: √x < √y
  proof: (sqrt_lt_sqrt_iff hx).2 h

中文:
定理 sqrt_lt_sqrt
  条件: (hx : 0 <= x) (h : x < y)
  结论: √x < √y
  证明: (sqrt_lt_sqrt_iff hx).2 h

Depends on / 依赖: sqrt_lt_sqrt_iff
-/
theorem sqrt_lt_sqrt (hx : 0 <= x) (h : x < y) : √x < √y :=
  (sqrt_lt_sqrt_iff hx).2 h

/--
theorem `sqrt_le_left` / 定理 `sqrt_le_left`

English:
theorem sqrt_le_left
  given: (hy : 0 <= y)
  statement: √x <= y ↔ x <= y ^ 2
  proof: by
  rw [sqrt]; rw [← Real.le_toNNReal_iff_coe_le hy]; rw [NNReal.sqrt_le_iff_le_sq]; rw [sq]; rw [← Real.toNNReal_mul hy]; rw [Real.toNNReal_le_toNNReal_iff (mul_self_nonneg y)]; rw [sq]

中文:
定理 sqrt_le_left
  条件: (hy : 0 <= y)
  结论: √x <= y ↔ x <= y ^ 2
  证明: by
  rw [sqrt]; rw [← Real.le_toNNReal_iff_coe_le hy]; rw [NNReal.sqrt_le_iff_le_sq]; rw [sq]; rw [← Real.toNNReal_mul hy]; rw [Real.toNNReal_le_toNNReal_iff (mul_self_nonneg y)]; rw [sq]

Depends on / 依赖: NNReal, NNReal.sqrt_le_iff_le_sq, Real.le_toNNReal_iff_coe_le, Real.toNNReal_le_toNNReal_iff, Real.toNNReal_mul, le_toNNReal_iff_coe_le, mul_self_nonneg, sqrt_le_iff_le_sq, toNNReal_le_toNNReal_iff, toNNReal_mul
-/
theorem sqrt_le_left (hy : 0 <= y) : √x <= y ↔ x <= y ^ 2 := by
  rw [sqrt]; rw [← Real.le_toNNReal_iff_coe_le hy]; rw [NNReal.sqrt_le_iff_le_sq]; rw [sq]; rw [← Real.toNNReal_mul hy]; rw [Real.toNNReal_le_toNNReal_iff (mul_self_nonneg y)]; rw [sq]

/--
theorem `sqrt_le_iff` / 定理 `sqrt_le_iff`

English:
theorem sqrt_le_iff
  statement: √x <= y ↔ 0 <= y ∧ x <= y ^ 2
  proof: by
  rw [← and_iff_right_of_imp fun h => (sqrt_nonneg x).trans h]; rw [and_congr_right_iff]
  exact sqrt_le_left

中文:
定理 sqrt_le_iff
  结论: √x <= y ↔ 0 <= y ∧ x <= y ^ 2
  证明: by
  rw [← and_iff_right_of_imp fun h => (sqrt_nonneg x).trans h]; rw [and_congr_right_iff]
  exact sqrt_le_left

Depends on / 依赖: and_congr_right_iff, and_iff_right_of_imp, sqrt_le_left, sqrt_nonneg
-/
theorem sqrt_le_iff : √x <= y ↔ 0 <= y ∧ x <= y ^ 2 := by
  rw [← and_iff_right_of_imp fun h => (sqrt_nonneg x).trans h]; rw [and_congr_right_iff]
  exact sqrt_le_left

/--
theorem `sqrt_lt` / 定理 `sqrt_lt`

English:
theorem sqrt_lt
  given: (hx : 0 <= x) (hy : 0 <= y)
  statement: √x < y ↔ x < y ^ 2
  proof: by
  rw [← sqrt_lt_sqrt_iff hx]; rw [sqrt_sq hy]

中文:
定理 sqrt_lt
  条件: (hx : 0 <= x) (hy : 0 <= y)
  结论: √x < y ↔ x < y ^ 2
  证明: by
  rw [← sqrt_lt_sqrt_iff hx]; rw [sqrt_sq hy]

Depends on / 依赖: sqrt_lt_sqrt_iff, sqrt_sq
-/
theorem sqrt_lt (hx : 0 <= x) (hy : 0 <= y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff hx]; rw [sqrt_sq hy]

/--
theorem `sqrt_lt'` / 定理 `sqrt_lt'`

English:
theorem sqrt_lt'
  given: (hy : 0 < y)
  statement: √x < y ↔ x < y ^ 2
  proof: by
  rw [← sqrt_lt_sqrt_iff_of_pos (pow_pos hy _)]; rw [sqrt_sq hy.le]

中文:
定理 sqrt_lt'
  条件: (hy : 0 < y)
  结论: √x < y ↔ x < y ^ 2
  证明: by
  rw [← sqrt_lt_sqrt_iff_of_pos (pow_pos hy _)]; rw [sqrt_sq hy.le]

Depends on / 依赖: hy.le, pow_pos, sqrt_lt_sqrt_iff_of_pos, sqrt_sq
-/
theorem sqrt_lt' (hy : 0 < y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff_of_pos (pow_pos hy _)]; rw [sqrt_sq hy.le]

/--
theorem `le_sqrt` / 定理 `le_sqrt`

English:
theorem le_sqrt
  given: (hx : 0 <= x) (hy : 0 <= y)
  statement: x <= √y ↔ x ^ 2 <= y
  proof: le_iff_le_iff_lt_iff_lt.2 sqrt_lt hy hx

中文:
定理 le_sqrt
  条件: (hx : 0 <= x) (hy : 0 <= y)
  结论: x <= √y ↔ x ^ 2 <= y
  证明: le_iff_le_iff_lt_iff_lt.2 sqrt_lt hy hx

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, sqrt_lt
-/
theorem le_sqrt (hx : 0 <= x) (hy : 0 <= y) : x <= √y ↔ x ^ 2 <= y :=
le_iff_le_iff_lt_iff_lt.2 sqrt_lt hy hx

/--
theorem `le_sqrt'` / 定理 `le_sqrt'`

English:
theorem le_sqrt'
  given: (hx : 0 < x)
  statement: x <= √y ↔ x ^ 2 <= y
  proof: le_iff_le_iff_lt_iff_lt.2 sqrt_lt' hx

中文:
定理 le_sqrt'
  条件: (hx : 0 < x)
  结论: x <= √y ↔ x ^ 2 <= y
  证明: le_iff_le_iff_lt_iff_lt.2 sqrt_lt' hx

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, sqrt_lt
-/
theorem le_sqrt' (hx : 0 < x) : x <= √y ↔ x ^ 2 <= y :=
le_iff_le_iff_lt_iff_lt.2 sqrt_lt' hx

/--
theorem `abs_le_sqrt` / 定理 `abs_le_sqrt`

English:
theorem abs_le_sqrt
  given: (h : x ^ 2 <= y)
  statement: |x| <= √y
  proof: by
  rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h

中文:
定理 abs_le_sqrt
  条件: (h : x ^ 2 <= y)
  结论: |x| <= √y
  证明: by
  rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h

Depends on / 依赖: sqrt_le_sqrt, sqrt_sq_eq_abs
-/
theorem abs_le_sqrt (h : x ^ 2 <= y) : |x| <= √y := by
  rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h

/--
theorem `sq_le` / 定理 `sq_le`

English:
theorem sq_le
  given: (h : 0 <= y)
  statement: x ^ 2 <= y ↔ -√y <= x ∧ x <= √y
  proof: by
  constructor
  · simpa only [abs_le] using abs_le_sqrt
  · rw [← abs_le, ← sq_abs]
    exact (le_sqrt (abs_nonneg x) h).mp

中文:
定理 sq_le
  条件: (h : 0 <= y)
  结论: x ^ 2 <= y ↔ -√y <= x ∧ x <= √y
  证明: by
  constructor
  · simpa only [abs_le] using abs_le_sqrt
  · rw [← abs_le, ← sq_abs]
    exact (le_sqrt (abs_nonneg x) h).mp

Depends on / 依赖: abs_le, abs_le_sqrt, abs_nonneg, le_sqrt, sq_abs
-/
theorem sq_le (h : 0 <= y) : x ^ 2 <= y ↔ -√y <= x ∧ x <= √y := by
  constructor
  · simpa only [abs_le] using abs_le_sqrt
  · rw [← abs_le, ← sq_abs]
    exact (le_sqrt (abs_nonneg x) h).mp

/--
theorem `neg_sqrt_le_of_sq_le` / 定理 `neg_sqrt_le_of_sq_le`

English:
theorem neg_sqrt_le_of_sq_le
  given: (h : x ^ 2 <= y)
  statement: -√y <= x
  proof: ((sq_le ((sq_nonneg x).trans h)).mp h).1

中文:
定理 neg_sqrt_le_of_sq_le
  条件: (h : x ^ 2 <= y)
  结论: -√y <= x
  证明: ((sq_le ((sq_nonneg x).trans h)).mp h).1

Depends on / 依赖: sq_le, sq_nonneg
-/
theorem neg_sqrt_le_of_sq_le (h : x ^ 2 <= y) : -√y <= x :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).1

/--
theorem `le_sqrt_of_sq_le` / 定理 `le_sqrt_of_sq_le`

English:
theorem le_sqrt_of_sq_le
  given: (h : x ^ 2 <= y)
  statement: x <= √y
  proof: ((sq_le ((sq_nonneg x).trans h)).mp h).2

@[simp]

中文:
定理 le_sqrt_of_sq_le
  条件: (h : x ^ 2 <= y)
  结论: x <= √y
  证明: ((sq_le ((sq_nonneg x).trans h)).mp h).2

@[simp]

Depends on / 依赖: sq_le, sq_nonneg
-/
theorem le_sqrt_of_sq_le (h : x ^ 2 <= y) : x <= √y :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).2

@[simp]
/--
theorem `sqrt_inj` / 定理 `sqrt_inj`

English:
theorem sqrt_inj
  given: (hx : 0 <= x) (hy : 0 <= y)
  statement: √x = √y ↔ x = y
  proof: by
  simp [le_antisymm_iff, hx, hy]

@[simp]

中文:
定理 sqrt_inj
  条件: (hx : 0 <= x) (hy : 0 <= y)
  结论: √x = √y ↔ x = y
  证明: by
  simp [le_antisymm_iff, hx, hy]

@[simp]

Depends on / 依赖: le_antisymm_iff
-/
theorem sqrt_inj (hx : 0 <= x) (hy : 0 <= y) : √x = √y ↔ x = y := by
  simp [le_antisymm_iff, hx, hy]

@[simp]
/--
theorem `sqrt_eq_zero` / 定理 `sqrt_eq_zero`

English:
theorem sqrt_eq_zero
  given: (h : 0 <= x)
  statement: √x = 0 ↔ x = 0
  proof: by simpa using sqrt_inj h le_rfl

中文:
定理 sqrt_eq_zero
  条件: (h : 0 <= x)
  结论: √x = 0 ↔ x = 0
  证明: by simpa using sqrt_inj h le_rfl

Depends on / 依赖: le_rfl, sqrt_inj
-/
theorem sqrt_eq_zero (h : 0 <= x) : √x = 0 ↔ x = 0 := by simpa using sqrt_inj h le_rfl

/--
theorem `sqrt_eq_zero'` / 定理 `sqrt_eq_zero'`

English:
theorem sqrt_eq_zero'
  statement: √x = 0 ↔ x <= 0
  proof: by
  rw [sqrt]; rw [NNReal.coe_eq_zero]; rw [NNReal.sqrt_eq_zero]; rw [Real.toNNReal_eq_zero]

中文:
定理 sqrt_eq_zero'
  结论: √x = 0 ↔ x <= 0
  证明: by
  rw [sqrt]; rw [NNReal.coe_eq_zero]; rw [NNReal.sqrt_eq_zero]; rw [Real.toNNReal_eq_zero]

Depends on / 依赖: NNReal, NNReal.coe_eq_zero, NNReal.sqrt_eq_zero, Real.toNNReal_eq_zero, coe_eq_zero, sqrt_eq_zero, toNNReal_eq_zero
-/
theorem sqrt_eq_zero' : √x = 0 ↔ x <= 0 := by
  rw [sqrt]; rw [NNReal.coe_eq_zero]; rw [NNReal.sqrt_eq_zero]; rw [Real.toNNReal_eq_zero]

/--
theorem `sqrt_ne_zero` / 定理 `sqrt_ne_zero`

English:
theorem sqrt_ne_zero
  given: (h : 0 <= x)
  statement: √x != 0 ↔ x != 0
  proof: by rw [not_iff_not, sqrt_eq_zero h]

中文:
定理 sqrt_ne_zero
  条件: (h : 0 <= x)
  结论: √x != 0 ↔ x != 0
  证明: by rw [not_iff_not, sqrt_eq_zero h]

Depends on / 依赖: not_iff_not, sqrt_eq_zero
-/
theorem sqrt_ne_zero (h : 0 <= x) : √x != 0 ↔ x != 0 := by rw [not_iff_not, sqrt_eq_zero h]

/--
theorem `sqrt_ne_zero'` / 定理 `sqrt_ne_zero'`

English:
theorem sqrt_ne_zero'
  statement: √x != 0 ↔ 0 < x
  proof: by rw [← not_le, not_iff_not, sqrt_eq_zero']

中文:
定理 sqrt_ne_zero'
  结论: √x != 0 ↔ 0 < x
  证明: by rw [← not_le, not_iff_not, sqrt_eq_zero']

Depends on / 依赖: not_iff_not, not_le, sqrt_eq_zero
-/
theorem sqrt_ne_zero' : √x != 0 ↔ 0 < x := by rw [← not_le, not_iff_not, sqrt_eq_zero']

/--
theorem `sq_sqrt'` / 定理 `sq_sqrt'`

English:
theorem sq_sqrt'
  statement: √x ^ 2 = max x 0
  proof: by
  rcases lt_trichotomy x 0 with _ | _ | _ <;> grind [sqrt_eq_zero', sq_sqrt]

中文:
定理 sq_sqrt'
  结论: √x ^ 2 = 最大值 x 0
  证明: by
  rcases lt_trichotomy x 0 with _ | _ | _ <;> grind [sqrt_eq_zero', sq_sqrt]

Depends on / 依赖: lt_trichotomy, sq_sqrt, sqrt_eq_zero
-/
theorem sq_sqrt' : √x ^ 2 = max x 0 := by
  rcases lt_trichotomy x 0 with _ | _ | _ <;> grind [sqrt_eq_zero', sq_sqrt]

-- Add the rule for `√x ^ 2` to the grind whiteboard whenever we see a real square root.
grind_pattern sq_sqrt' => √x

-- Check that `grind` can discharge non-zero goals for square roots of positive numerals.
example : √7 != 0 := by grind

@[simp]
/--
theorem `sqrt_pos` / 定理 `sqrt_pos`

English:
theorem sqrt_pos
  statement: 0 < √x ↔ 0 < x
  proof: lt_iff_lt_of_le_iff_le (Iff.trans (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

中文:
定理 sqrt_pos
  结论: 0 < √x ↔ 0 < x
  证明: lt_iff_lt_of_le_iff_le (Iff.trans (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

Depends on / 依赖: Iff.trans, le_antisymm_iff, lt_iff_lt_of_le_iff_le, sqrt_eq_zero, sqrt_nonneg
-/
theorem sqrt_pos : 0 < √x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le (Iff.trans (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

/--
lemma `sqrt_le_sqrt_iff'` / 引理 `sqrt_le_sqrt_iff'`

English:
lemma sqrt_le_sqrt_iff'
  given: (hx : 0 < x)
  statement: √x <= √y ↔ x <= y
  proof: by
  obtain hy | hy := le_total y 0
  · exact iff_of_false ((sqrt_eq_zero_of_nonpos hy).trans_lt <| sqrt_pos.2 hx).not_ge
      (hy.trans_lt hx).not_ge
  · exact sqrt_le_sqrt_iff hy

中文:
引理 sqrt_le_sqrt_iff'
  条件: (hx : 0 < x)
  结论: √x <= √y ↔ x <= y
  证明: by
  obtain hy | hy := le_total y 0
  · exact iff_of_false ((sqrt_eq_zero_of_nonpos hy).trans_lt <| sqrt_pos.2 hx).not_ge
      (hy.trans_lt hx).not_ge
  · exact sqrt_le_sqrt_iff hy

Depends on / 依赖: hy.trans_lt, iff_of_false, le_total, not_ge, sqrt_eq_zero_of_nonpos, sqrt_le_sqrt_iff, sqrt_pos, trans_lt
-/
lemma sqrt_le_sqrt_iff' (hx : 0 < x) : √x <= √y ↔ x <= y := by
  obtain hy | hy := le_total y 0
  · exact iff_of_false ((sqrt_eq_zero_of_nonpos hy).trans_lt <| sqrt_pos.2 hx).not_ge
      (hy.trans_lt hx).not_ge
  · exact sqrt_le_sqrt_iff hy

/--
lemma `one_le_sqrt` / 引理 `one_le_sqrt`

English:
lemma one_le_sqrt
  statement: 1 <= √x ↔ 1 <= x
  proof: by
  rw [← sqrt_one]; rw [sqrt_le_sqrt_iff' zero_lt_one]; rw [sqrt_one]

中文:
引理 one_le_sqrt
  结论: 1 <= √x ↔ 1 <= x
  证明: by
  rw [← sqrt_one]; rw [sqrt_le_sqrt_iff' zero_lt_one]; rw [sqrt_one]
-/
@[simp] lemma one_le_sqrt : 1 <= √x ↔ 1 <= x := by
  rw [← sqrt_one]; rw [sqrt_le_sqrt_iff' zero_lt_one]; rw [sqrt_one]

/--
lemma `sqrt_le_one` / 引理 `sqrt_le_one`

English:
lemma sqrt_le_one
  statement: √x <= 1 ↔ x <= 1
  proof: by
  rw [← sqrt_one]; rw [sqrt_le_sqrt_iff zero_le_one]; rw [sqrt_one]

中文:
引理 sqrt_le_one
  结论: √x <= 1 ↔ x <= 1
  证明: by
  rw [← sqrt_one]; rw [sqrt_le_sqrt_iff zero_le_one]; rw [sqrt_one]
-/
@[simp] lemma sqrt_le_one : √x <= 1 ↔ x <= 1 := by
  rw [← sqrt_one]; rw [sqrt_le_sqrt_iff zero_le_one]; rw [sqrt_one]

/--
lemma `isSquare_iff` / 引理 `isSquare_iff`

English:
lemma isSquare_iff
  statement: IsSquare x ↔ 0 <= x
  proof: ⟨(·.nonneg), (⟨√x, mul_self_sqrt · |>.symm⟩)⟩

中文:
引理 isSquare_iff
  结论: IsSquare x ↔ 0 <= x
  证明: ⟨(·.nonneg), (⟨√x, mul_self_sqrt · |>.symm⟩)⟩
-/
@[simp] lemma isSquare_iff : IsSquare x ↔ 0 <= x :=
  ⟨(·.nonneg), (⟨√x, mul_self_sqrt · |>.symm⟩)⟩

/--
lemma `sqrt_le_self_iff` / 引理 `sqrt_le_self_iff`

English:
lemma sqrt_le_self_iff
  statement: √x <= x ↔ x = 0 ∨ 1 <= x
  proof: by
  rw [sqrt_le_iff]; rw [← sub_nonneg (a := x ^ 2)]; rw [sq]; rw [← mul_sub_one]
  grind [mul_nonneg_iff]

中文:
引理 sqrt_le_self_iff
  结论: √x <= x ↔ x = 0 ∨ 1 <= x
  证明: by
  rw [sqrt_le_iff]; rw [← sub_nonneg (a := x ^ 2)]; rw [sq]; rw [← mul_sub_one]
  grind [mul_nonneg_iff]
-/
@[simp] lemma sqrt_le_self_iff : √x <= x ↔ x = 0 ∨ 1 <= x := by
  rw [sqrt_le_iff]; rw [← sub_nonneg (a := x ^ 2)]; rw [sq]; rw [← mul_sub_one]
  grind [mul_nonneg_iff]

/--
lemma `le_sqrt_self_iff` / 引理 `le_sqrt_self_iff`

English:
lemma le_sqrt_self_iff
  statement: x <= √x ↔ x <= 1
  proof: by
  obtain hx | hx := le_or_gt x 0
  · simp [hx.trans]
  · rw [le_sqrt' hx, sq, mul_le_iff_le_one_left hx]

中文:
引理 le_sqrt_self_iff
  结论: x <= √x ↔ x <= 1
  证明: by
  obtain hx | hx := le_or_gt x 0
  · simp [hx.trans]
  · rw [le_sqrt' hx, sq, mul_le_iff_le_one_left hx]
-/
@[simp] lemma le_sqrt_self_iff : x <= √x ↔ x <= 1 := by
  obtain hx | hx := le_or_gt x 0
  · simp [hx.trans]
  · rw [le_sqrt' hx, sq, mul_le_iff_le_one_left hx]

/--
lemma `sqrt_lt_self_iff` / 引理 `sqrt_lt_self_iff`

English:
lemma sqrt_lt_self_iff
  statement: √x < x ↔ 1 < x
  proof: by simp [← not_le]

中文:
引理 sqrt_lt_self_iff
  结论: √x < x ↔ 1 < x
  证明: by simp [← not_le]
-/
@[simp] lemma sqrt_lt_self_iff : √x < x ↔ 1 < x := by simp [← not_le]
/--
lemma `lt_sqrt_self_iff` / 引理 `lt_sqrt_self_iff`

English:
lemma lt_sqrt_self_iff
  statement: x < √x ↔ x != 0 ∧ x < 1
  proof: by simp [← not_le]

中文:
引理 lt_sqrt_self_iff
  结论: x < √x ↔ x != 0 ∧ x < 1
  证明: by simp [← not_le]
-/
@[simp] lemma lt_sqrt_self_iff : x < √x ↔ x != 0 ∧ x < 1 := by simp [← not_le]

end Real

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: a square root of a strictly positive nonnegative real is
positive. -/
@[positivity NNReal.sqrt _]
meta def evalNNRealSqrt : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(NNReal.sqrt_pos_of_pos $pa))
    | _ => failure -- this case is dealt with by generic nonnegativity of nnreals
  | _, _, _ => throwError "not NNReal.sqrt"

/-- Extension for the `positivity` tactic: a square root is nonnegative, and is strictly positive if
its input is. -/
@[positivity √_]
meta def evalSqrt : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(√$a) =>
    assertInstancesCommute
let ra ← catchNone core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(Real.sqrt_pos_of_pos $pa))
    | _ => pure (.nonnegative q(Real.sqrt_nonneg $a))
  | _, _, _ => throwError "not Real.sqrt"

end Mathlib.Meta.Positivity

namespace Real

/--
lemma `one_lt_sqrt_two` / 引理 `one_lt_sqrt_two`

English:
lemma one_lt_sqrt_two
  statement: 1 < √2
  proof: by rw [← Real.sqrt_one]; gcongr; simp

中文:
引理 one_lt_sqrt_two
  结论: 1 < √2
  证明: by rw [← Real.sqrt_one]; gcongr; simp

Depends on / 依赖: Real.sqrt_one, sqrt_one
-/
lemma one_lt_sqrt_two : 1 < √2 := by rw [← Real.sqrt_one]; gcongr; simp

/--
lemma `sqrt_two_lt_three_halves` / 引理 `sqrt_two_lt_three_halves`

English:
lemma sqrt_two_lt_three_halves
  statement: √2 < 3 / 2
  proof: by
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  grind

中文:
引理 sqrt_two_lt_three_halves
  结论: √2 < 3 / 2
  证明: by
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  grind
-/
lemma sqrt_two_lt_three_halves : √2 < 3 / 2 := by
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  grind

/--
lemma `inv_sqrt_two_sub_one` / 引理 `inv_sqrt_two_sub_one`

English:
lemma inv_sqrt_two_sub_one
  statement: (√2 - 1)⁻¹ = √2 + 1
  proof: by
  grind

@[simp]

中文:
引理 inv_sqrt_two_sub_one
  结论: (√2 - 1)⁻¹ = √2 + 1
  证明: by
  grind

@[simp]
-/
lemma inv_sqrt_two_sub_one : (√2 - 1)⁻¹ = √2 + 1 := by
  grind

@[simp]
/--
theorem `sqrt_mul` / 定理 `sqrt_mul`

English:
theorem sqrt_mul
  given: {x : Real} (hx : 0 <= x) (y : Real)
  statement: √(x * y) = √x * √y
  proof: by
  simp_rw [Real.sqrt, ← NNReal.coe_mul, NNReal.coe_inj, Real.toNNReal_mul hx, NNReal.sqrt_mul]

@[simp]

中文:
定理 sqrt_mul
  条件: {x : 实数} (hx : 0 <= x) (y : 实数)
  结论: √(x * y) = √x * √y
  证明: by
  simp_rw [Real.sqrt, ← NNReal.coe_mul, NNReal.coe_inj, Real.toNNReal_mul hx, NNReal.sqrt_mul]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.coe_mul, NNReal.sqrt_mul, Real.sqrt, Real.toNNReal_mul, coe_inj, coe_mul, simp_rw, sqrt_mul, toNNReal_mul
-/
theorem sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) = √x * √y := by
  simp_rw [Real.sqrt, ← NNReal.coe_mul, NNReal.coe_inj, Real.toNNReal_mul hx, NNReal.sqrt_mul]

@[simp]
/--
theorem `sqrt_mul'` / 定理 `sqrt_mul'`

English:
theorem sqrt_mul'
  given: (x) {y : Real} (hy : 0 <= y)
  statement: √(x * y) = √x * √y
  proof: by
  rw [mul_comm]; rw [sqrt_mul hy]; rw [mul_comm]

@[simp]

中文:
定理 sqrt_mul'
  条件: (x) {y : 实数} (hy : 0 <= y)
  结论: √(x * y) = √x * √y
  证明: by
  rw [mul_comm]; rw [sqrt_mul hy]; rw [mul_comm]

@[simp]

Depends on / 依赖: mul_comm, sqrt_mul
-/
theorem sqrt_mul' (x) {y : Real} (hy : 0 <= y) : √(x * y) = √x * √y := by
  rw [mul_comm]; rw [sqrt_mul hy]; rw [mul_comm]

@[simp]
/--
theorem `sqrt_inv` / 定理 `sqrt_inv`

English:
theorem sqrt_inv
  given: (x : Real)
  statement: √x⁻¹ = (√x)⁻¹
  proof: by
  rw [Real.sqrt]; rw [Real.toNNReal_inv]; rw [NNReal.sqrt_inv]; rw [NNReal.coe_inv]; rw [Real.sqrt]

@[simp]

中文:
定理 sqrt_inv
  条件: (x : 实数)
  结论: √x⁻¹ = (√x)⁻¹
  证明: by
  rw [Real.sqrt]; rw [Real.toNNReal_inv]; rw [NNReal.sqrt_inv]; rw [NNReal.coe_inv]; rw [Real.sqrt]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_inv, NNReal.sqrt_inv, Real.sqrt, Real.toNNReal_inv, coe_inv, sqrt_inv, toNNReal_inv
-/
theorem sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹ := by
  rw [Real.sqrt]; rw [Real.toNNReal_inv]; rw [NNReal.sqrt_inv]; rw [NNReal.coe_inv]; rw [Real.sqrt]

@[simp]
/--
theorem `sqrt_div` / 定理 `sqrt_div`

English:
theorem sqrt_div
  given: {x : Real} (hx : 0 <= x) (y : Real)
  statement: √(x / y) = √x / √y
  proof: by
  rw [division_def]; rw [sqrt_mul hx]; rw [sqrt_inv]; rw [division_def]

@[simp]

中文:
定理 sqrt_div
  条件: {x : 实数} (hx : 0 <= x) (y : 实数)
  结论: √(x / y) = √x / √y
  证明: by
  rw [division_def]; rw [sqrt_mul hx]; rw [sqrt_inv]; rw [division_def]

@[simp]

Depends on / 依赖: division_def, sqrt_inv, sqrt_mul
-/
theorem sqrt_div {x : Real} (hx : 0 <= x) (y : Real) : √(x / y) = √x / √y := by
  rw [division_def]; rw [sqrt_mul hx]; rw [sqrt_inv]; rw [division_def]

@[simp]
/--
theorem `sqrt_div'` / 定理 `sqrt_div'`

English:
theorem sqrt_div'
  given: (x) {y : Real} (hy : 0 <= y)
  statement: √(x / y) = √x / √y
  proof: by
  rw [division_def]; rw [sqrt_mul' x (inv_nonneg.2 hy)]; rw [sqrt_inv]; rw [division_def]

中文:
定理 sqrt_div'
  条件: (x) {y : 实数} (hy : 0 <= y)
  结论: √(x / y) = √x / √y
  证明: by
  rw [division_def]; rw [sqrt_mul' x (inv_nonneg.2 hy)]; rw [sqrt_inv]; rw [division_def]

Depends on / 依赖: division_def, inv_nonneg, sqrt_inv, sqrt_mul
-/
theorem sqrt_div' (x) {y : Real} (hy : 0 <= y) : √(x / y) = √x / √y := by
  rw [division_def]; rw [sqrt_mul' x (inv_nonneg.2 hy)]; rw [sqrt_inv]; rw [division_def]

variable {x y : Real}

@[simp]
/--
theorem `div_sqrt` / 定理 `div_sqrt`

English:
theorem div_sqrt
  statement: x / √x = √x
  proof: by
  grind

中文:
定理 div_sqrt
  结论: x / √x = √x
  证明: by
  grind
-/
theorem div_sqrt : x / √x = √x := by
  grind

/--
theorem `sqrt_div_self'` / 定理 `sqrt_div_self'`

English:
theorem sqrt_div_self'
  statement: √x / x = 1 / √x
  proof: by rw [← div_sqrt, one_div_div, div_sqrt]

中文:
定理 sqrt_div_self'
  结论: √x / x = 1 / √x
  证明: by rw [← div_sqrt, one_div_div, div_sqrt]

Depends on / 依赖: div_sqrt, one_div_div
-/
theorem sqrt_div_self' : √x / x = 1 / √x := by rw [← div_sqrt, one_div_div, div_sqrt]

/--
theorem `sqrt_div_self` / 定理 `sqrt_div_self`

English:
theorem sqrt_div_self
  statement: √x / x = (√x)⁻¹
  proof: by rw [sqrt_div_self', one_div]

中文:
定理 sqrt_div_self
  结论: √x / x = (√x)⁻¹
  证明: by rw [sqrt_div_self', one_div]

Depends on / 依赖: one_div, sqrt_div_self
-/
theorem sqrt_div_self : √x / x = (√x)⁻¹ := by rw [sqrt_div_self', one_div]

/--
theorem `lt_sqrt` / 定理 `lt_sqrt`

English:
theorem lt_sqrt
  given: (hx : 0 <= x)
  statement: x < √y ↔ x ^ 2 < y
  proof: by
  rw [← sqrt_lt_sqrt_iff (sq_nonneg _)]; rw [sqrt_sq hx]

中文:
定理 lt_sqrt
  条件: (hx : 0 <= x)
  结论: x < √y ↔ x ^ 2 < y
  证明: by
  rw [← sqrt_lt_sqrt_iff (sq_nonneg _)]; rw [sqrt_sq hx]

Depends on / 依赖: sq_nonneg, sqrt_lt_sqrt_iff, sqrt_sq
-/
theorem lt_sqrt (hx : 0 <= x) : x < √y ↔ x ^ 2 < y := by
  rw [← sqrt_lt_sqrt_iff (sq_nonneg _)]; rw [sqrt_sq hx]

/--
theorem `sq_lt` / 定理 `sq_lt`

English:
theorem sq_lt
  statement: x ^ 2 < y ↔ -√y < x ∧ x < √y
  proof: by
  rw [← abs_lt]; rw [← sq_abs]; rw [lt_sqrt (abs_nonneg _)]

中文:
定理 sq_lt
  结论: x ^ 2 < y ↔ -√y < x ∧ x < √y
  证明: by
  rw [← abs_lt]; rw [← sq_abs]; rw [lt_sqrt (abs_nonneg _)]

Depends on / 依赖: abs_lt, abs_nonneg, lt_sqrt, sq_abs
-/
theorem sq_lt : x ^ 2 < y ↔ -√y < x ∧ x < √y := by
  rw [← abs_lt]; rw [← sq_abs]; rw [lt_sqrt (abs_nonneg _)]

/--
theorem `neg_sqrt_lt_of_sq_lt` / 定理 `neg_sqrt_lt_of_sq_lt`

English:
theorem neg_sqrt_lt_of_sq_lt
  given: (h : x ^ 2 < y)
  statement: -√y < x
  proof: (sq_lt.mp h).1

中文:
定理 neg_sqrt_lt_of_sq_lt
  条件: (h : x ^ 2 < y)
  结论: -√y < x
  证明: (sq_lt.mp h).1

Depends on / 依赖: sq_lt, sq_lt.mp
-/
theorem neg_sqrt_lt_of_sq_lt (h : x ^ 2 < y) : -√y < x :=
  (sq_lt.mp h).1

/--
theorem `lt_sqrt_of_sq_lt` / 定理 `lt_sqrt_of_sq_lt`

English:
theorem lt_sqrt_of_sq_lt
  given: (h : x ^ 2 < y)
  statement: x < √y
  proof: (sq_lt.mp h).2

中文:
定理 lt_sqrt_of_sq_lt
  条件: (h : x ^ 2 < y)
  结论: x < √y
  证明: (sq_lt.mp h).2

Depends on / 依赖: sq_lt, sq_lt.mp
-/
theorem lt_sqrt_of_sq_lt (h : x ^ 2 < y) : x < √y :=
  (sq_lt.mp h).2

/--
theorem `lt_sq_of_sqrt_lt` / 定理 `lt_sq_of_sqrt_lt`

English:
theorem lt_sq_of_sqrt_lt
  given: (h : √x < y)
  statement: x < y ^ 2
  proof: by
  have hy := x.sqrt_nonneg.trans_lt h
  rwa [← sqrt_lt_sqrt_iff_of_pos (sq_pos_of_pos hy), sqrt_sq hy.le]

中文:
定理 lt_sq_of_sqrt_lt
  条件: (h : √x < y)
  结论: x < y ^ 2
  证明: by
  have hy := x.sqrt_nonneg.trans_lt h
  rwa [← sqrt_lt_sqrt_iff_of_pos (sq_pos_of_pos hy), sqrt_sq hy.le]

Depends on / 依赖: hy.le, sq_pos_of_pos, sqrt_lt_sqrt_iff_of_pos, sqrt_nonneg, sqrt_sq, trans_lt, x.sqrt_nonneg.trans_lt
-/
theorem lt_sq_of_sqrt_lt (h : √x < y) : x < y ^ 2 := by
  have hy := x.sqrt_nonneg.trans_lt h
  rwa [← sqrt_lt_sqrt_iff_of_pos (sq_pos_of_pos hy), sqrt_sq hy.le]

/--
theorem `nat_sqrt_le_real_sqrt` / 定理 `nat_sqrt_le_real_sqrt`

English:
theorem nat_sqrt_le_real_sqrt
  given: {a : Nat}
  statement: ↑(Nat.sqrt a) <= √(a : Real)
  proof: by
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  norm_cast
  exact Nat.sqrt_le' a

中文:
定理 nat_sqrt_le_real_sqrt
  条件: {a : 自然数}
  结论: ↑(自然数.sqrt a) <= √(a : 实数)
  证明: by
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  norm_cast
  exact Nat.sqrt_le' a

Depends on / 依赖: Nat.cast_nonneg, Nat.sqrt_le, Real.le_sqrt, cast_nonneg, le_sqrt, sqrt_le
-/
theorem nat_sqrt_le_real_sqrt {a : Nat} : ↑(Nat.sqrt a) <= √(a : Real) := by
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  norm_cast
  exact Nat.sqrt_le' a

/--
theorem `real_sqrt_lt_nat_sqrt_succ` / 定理 `real_sqrt_lt_nat_sqrt_succ`

English:
theorem real_sqrt_lt_nat_sqrt_succ
  given: {a : Nat}
  statement: √(a : Real) < Nat.sqrt a + 1
  proof: by
  rw [sqrt_lt (by simp)] <;> norm_cast
  · exact Nat.lt_succ_sqrt' a
  · exact Nat.le_add_left 0 (Nat.sqrt a + 1)

中文:
定理 real_sqrt_lt_nat_sqrt_succ
  条件: {a : 自然数}
  结论: √(a : 实数) < 自然数.sqrt a + 1
  证明: by
  rw [sqrt_lt (by simp)] <;> norm_cast
  · exact Nat.lt_succ_sqrt' a
  · exact Nat.le_add_left 0 (Nat.sqrt a + 1)

Depends on / 依赖: Nat.le_add_left, Nat.lt_succ_sqrt, Nat.sqrt, le_add_left, lt_succ_sqrt, sqrt_lt
-/
theorem real_sqrt_lt_nat_sqrt_succ {a : Nat} : √(a : Real) < Nat.sqrt a + 1 := by
  rw [sqrt_lt (by simp)] <;> norm_cast
  · exact Nat.lt_succ_sqrt' a
  · exact Nat.le_add_left 0 (Nat.sqrt a + 1)

/--
theorem `real_sqrt_le_nat_sqrt_succ` / 定理 `real_sqrt_le_nat_sqrt_succ`

English:
theorem real_sqrt_le_nat_sqrt_succ
  given: {a : Nat}
  statement: √(a : Real) <= Nat.sqrt a + 1
  proof: real_sqrt_lt_nat_sqrt_succ.le

中文:
定理 real_sqrt_le_nat_sqrt_succ
  条件: {a : 自然数}
  结论: √(a : 实数) <= 自然数.sqrt a + 1
  证明: real_sqrt_lt_nat_sqrt_succ.le

Depends on / 依赖: real_sqrt_lt_nat_sqrt_succ, real_sqrt_lt_nat_sqrt_succ.le
-/
theorem real_sqrt_le_nat_sqrt_succ {a : Nat} : √(a : Real) <= Nat.sqrt a + 1 :=
  real_sqrt_lt_nat_sqrt_succ.le

/-- The floor of the real square root is the same as the natural square root. -/
@[simp]
/--
theorem `floor_real_sqrt_eq_nat_sqrt` / 定理 `floor_real_sqrt_eq_nat_sqrt`

English:
theorem floor_real_sqrt_eq_nat_sqrt
  given: {a : Nat}
  statement: ⌊√(a : Real)⌋ = Nat.sqrt a
  proof: by
  rw [Int.floor_eq_iff]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

中文:
定理 floor_real_sqrt_eq_nat_sqrt
  条件: {a : 自然数}
  结论: ⌊√(a : 实数)⌋ = 自然数.sqrt a
  证明: by
  rw [Int.floor_eq_iff]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

Depends on / 依赖: Int.floor_eq_iff, floor_eq_iff, nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ
-/
theorem floor_real_sqrt_eq_nat_sqrt {a : Nat} : ⌊√(a : Real)⌋ = Nat.sqrt a := by
  rw [Int.floor_eq_iff]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

/-- The natural floor of the real square root is the same as the natural square root. -/
@[simp]
/--
theorem `nat_floor_real_sqrt_eq_nat_sqrt` / 定理 `nat_floor_real_sqrt_eq_nat_sqrt`

English:
theorem nat_floor_real_sqrt_eq_nat_sqrt
  given: {a : Nat}
  statement: ⌊√(a : Real)⌋₊ = Nat.sqrt a
  proof: by
  rw [Nat.floor_eq_iff (sqrt_nonneg a)]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

中文:
定理 nat_floor_real_sqrt_eq_nat_sqrt
  条件: {a : 自然数}
  结论: ⌊√(a : 实数)⌋₊ = 自然数.sqrt a
  证明: by
  rw [Nat.floor_eq_iff (sqrt_nonneg a)]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

Depends on / 依赖: Nat.floor_eq_iff, floor_eq_iff, nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ, sqrt_nonneg
-/
theorem nat_floor_real_sqrt_eq_nat_sqrt {a : Nat} : ⌊√(a : Real)⌋₊ = Nat.sqrt a := by
  rw [Nat.floor_eq_iff (sqrt_nonneg a)]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

/--
theorem `sqrt_one_add_le` / 定理 `sqrt_one_add_le`

English:
theorem sqrt_one_add_le
  given: (h : -1 <= x)
  statement: √(1 + x) <= 1 + x / 2
  proof: by
  refine sqrt_le_iff.mpr ⟨by linarith, ?_⟩
  calc 1 + x
_ <= 1 + x + (x / 2) ^ 2 := le_add_of_nonneg_right sq_nonneg _
    _ = _ := by ring

中文:
定理 sqrt_one_add_le
  条件: (h : -1 <= x)
  结论: √(1 + x) <= 1 + x / 2
  证明: by
  refine sqrt_le_iff.mpr ⟨by linarith, ?_⟩
  calc 1 + x
_ <= 1 + x + (x / 2) ^ 2 := le_add_of_nonneg_right sq_nonneg _
    _ = _ := by ring

Depends on / 依赖: le_add_of_nonneg_right, sq_nonneg, sqrt_le_iff, sqrt_le_iff.mpr
-/
theorem sqrt_one_add_le (h : -1 <= x) : √(1 + x) <= 1 + x / 2 := by
  refine sqrt_le_iff.mpr ⟨by linarith, ?_⟩
  calc 1 + x
_ <= 1 + x + (x / 2) ^ 2 := le_add_of_nonneg_right sq_nonneg _
    _ = _ := by ring

/--
theorem `sqrt_prod` / 定理 `sqrt_prod`

English:
theorem sqrt_prod
  given: {ι : Type*} (s : Finset ι) {x : ι -> Real} (hx : forall i in s, 0 <= x i)
  proof: by
convert! congr_arg NNReal.toReal map_prod NNReal.sqrtHom (Real.toNNReal ∘ x) s <;>
    simp +contextual [-map_prod, NNReal.sqrtHom, hx]

中文:
定理 sqrt_prod
  条件: {ι : 类型} (s : 有限集 ι) {x : ι -> 实数} (hx : 对任意 i in s, 0 <= x i)
  证明: by
convert! congr_arg NNReal.toReal map_prod NNReal.sqrtHom (Real.toNNReal ∘ x) s <;>
    simp +contextual [-map_prod, NNReal.sqrtHom, hx]

Depends on / 依赖: NNReal, NNReal.sqrtHom, NNReal.toReal, Real.toNNReal, congr_arg, contextual, convert, map_prod, sqrtHom, toNNReal, toReal
-/
theorem sqrt_prod {ι : Type*} (s : Finset ι) {x : ι -> Real} (hx : forall i in s, 0 <= x i) :
    √(∏ i in s, x i) = ∏ i in s, √(x i) := by
convert! congr_arg NNReal.toReal map_prod NNReal.sqrtHom (Real.toNNReal ∘ x) s <;>
    simp +contextual [-map_prod, NNReal.sqrtHom, hx]

end Real

open Real

variable {α : Type*}

/--
theorem `Filter.Tendsto.sqrt` / 定理 `Filter.Tendsto.sqrt`

English:
theorem Filter.Tendsto.sqrt
  given: {f : α -> Real} {l : Filter α} {x : Real} (h : Tendsto f l (𝓝 x))
  proof: (continuous_sqrt.tendsto _).comp h

中文:
定理 滤子.收敛.sqrt
  条件: {f : α -> 实数} {l : 滤子 α} {x : 实数} (h : 收敛 f l (𝓝 x))
  证明: (continuous_sqrt.tendsto _).comp h

Depends on / 依赖: continuous_sqrt, continuous_sqrt.tendsto, tendsto
-/
theorem Filter.Tendsto.sqrt {f : α -> Real} {l : Filter α} {x : Real} (h : Tendsto f l (𝓝 x)) :
    Tendsto (fun x => √(f x)) l (𝓝 (√x)) :=
  (continuous_sqrt.tendsto _).comp h

variable [TopologicalSpace α] {f : α -> Real} {s : Set α} {x : α}

nonrec theorem ContinuousWithinAt.sqrt (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => √(f x)) s x :=
  h.sqrt

@[fun_prop]
nonrec theorem ContinuousAt.sqrt (h : ContinuousAt f x) : ContinuousAt (fun x => √(f x)) x :=
  h.sqrt

@[fun_prop]
/--
theorem `ContinuousOn.sqrt` / 定理 `ContinuousOn.sqrt`

English:
theorem ContinuousOn.sqrt
  given: (h : ContinuousOn f s)
  statement: ContinuousOn (fun x => √(f x)) s
  proof: fun x hx => (h x hx).sqrt

@[continuity, fun_prop]

中文:
定理 ContinuousOn.sqrt
  条件: (h : ContinuousOn f s)
  结论: ContinuousOn (fun x => √(f x)) s
  证明: fun x hx => (h x hx).sqrt

@[continuity, fun_prop]
-/
theorem ContinuousOn.sqrt (h : ContinuousOn f s) : ContinuousOn (fun x => √(f x)) s :=
  fun x hx => (h x hx).sqrt

@[continuity, fun_prop]
/--
theorem `Continuous.sqrt` / 定理 `Continuous.sqrt`

English:
theorem Continuous.sqrt
  given: (h : Continuous f)
  statement: Continuous fun x => √(f x)
  proof: continuous_sqrt.comp h

中文:
定理 连续.sqrt
  条件: (h : 连续 f)
  结论: 连续 fun x => √(f x)
  证明: continuous_sqrt.comp h

Depends on / 依赖: continuous_sqrt, continuous_sqrt.comp
-/
theorem Continuous.sqrt (h : Continuous f) : Continuous fun x => √(f x) :=
  continuous_sqrt.comp h

namespace NNReal
variable {ι : Type*}
open Finset

/--
lemma `sum_mul_le_sqrt_mul_sqrt` / 引理 `sum_mul_le_sqrt_mul_sqrt`

English:
lemma sum_mul_le_sqrt_mul_sqrt
  given: (s : Finset ι) (f g : ι -> Real>=0)
  proof: (le_sqrt_iff_sq_le.2 <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq sqrt_mul _ _

中文:
引理 sum_mul_le_sqrt_mul_sqrt
  条件: (s : 有限集 ι) (f g : ι -> 实数>=0)
  证明: (le_sqrt_iff_sq_le.2 <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq sqrt_mul _ _

Depends on / 依赖: le_sqrt_iff_sq_le, sqrt_mul, sum_mul_sq_le_sq_mul_sq, trans_eq
-/
lemma sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι -> Real>=0) :
    ∑ i in s, f i * g i <= sqrt (∑ i in s, f i ^ 2) * sqrt (∑ i in s, g i ^ 2) :=
(le_sqrt_iff_sq_le.2 <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq sqrt_mul _ _

/--
lemma `sum_sqrt_mul_sqrt_le` / 引理 `sum_sqrt_mul_sqrt_le`

English:
lemma sum_sqrt_mul_sqrt_le
  given: (s : Finset ι) (f g : ι -> Real>=0)
  proof: by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x => sqrt (f x)) (fun x => sqrt (g x))

中文:
引理 sum_sqrt_mul_sqrt_le
  条件: (s : 有限集 ι) (f g : ι -> 实数>=0)
  证明: by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x => sqrt (f x)) (fun x => sqrt (g x))

Depends on / 依赖: sum_mul_le_sqrt_mul_sqrt
-/
lemma sum_sqrt_mul_sqrt_le (s : Finset ι) (f g : ι -> Real>=0) :
    ∑ i in s, sqrt (f i) * sqrt (g i) <= sqrt (∑ i in s, f i) * sqrt (∑ i in s, g i) := by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x => sqrt (f x)) (fun x => sqrt (g x))

end NNReal

namespace Real
variable {ι : Type*} {f g : ι -> Real}
open Finset

/--
lemma `sum_mul_le_sqrt_mul_sqrt` / 引理 `sum_mul_le_sqrt_mul_sqrt`

English:
lemma sum_mul_le_sqrt_mul_sqrt
  given: (s : Finset ι) (f g : ι -> Real)
  proof: (le_sqrt_of_sq_le <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq sqrt_mul
    (sum_nonneg fun _ _ => by positivity) _

中文:
引理 sum_mul_le_sqrt_mul_sqrt
  条件: (s : 有限集 ι) (f g : ι -> 实数)
  证明: (le_sqrt_of_sq_le <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq sqrt_mul
    (sum_nonneg fun _ _ => by positivity) _

Depends on / 依赖: le_sqrt_of_sq_le, sqrt_mul, sum_mul_sq_le_sq_mul_sq, sum_nonneg, trans_eq
-/
lemma sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι -> Real) :
    ∑ i in s, f i * g i <= √(∑ i in s, f i ^ 2) * √(∑ i in s, g i ^ 2) :=
(le_sqrt_of_sq_le <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq sqrt_mul
    (sum_nonneg fun _ _ => by positivity) _

/--
lemma `sum_sqrt_mul_sqrt_le` / 引理 `sum_sqrt_mul_sqrt_le`

English:
lemma sum_sqrt_mul_sqrt_le
  given: (s : Finset ι) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i)
  proof: by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x => √(f x)) (fun x => √(g x))

中文:
引理 sum_sqrt_mul_sqrt_le
  条件: (s : 有限集 ι) (hf : 对任意 i, 0 <= f i) (hg : 对任意 i, 0 <= g i)
  证明: by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x => √(f x)) (fun x => √(g x))

Depends on / 依赖: sum_mul_le_sqrt_mul_sqrt
-/
lemma sum_sqrt_mul_sqrt_le (s : Finset ι) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i) :
    ∑ i in s, √(f i) * √(g i) <= √(∑ i in s, f i) * √(∑ i in s, g i) := by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x => √(f x)) (fun x => √(g x))

end Real
