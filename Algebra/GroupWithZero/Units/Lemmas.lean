/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.GroupWithZero.Hom

/-!
# Further lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

-/

@[expose] public section

assert_not_exists DenselyOrdered MulAction Ring

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}
variable [MonoidWithZero M₀]

section Monoid

variable [Monoid M] [GroupWithZero G₀]

/--
lemma `isLocalHom_of_exists_map_ne_one` / 引理 `isLocalHom_of_exists_map_ne_one`

English:
lemma isLocalHom_of_exists_map_ne_one
  statement: [FunLike F G₀ M] [MonoidHomClass F G₀ M] {f : F}
  proof: by
    rcases eq_or_ne a 0 with (rfl | h)
    · obtain ⟨t, ht⟩ := hf
      refine (ht ?_).elim
      have := map_mul f t 0
      rw [← one_mul (f (t * 0))]; rw [mul_zero] at this
      exact (h.mul_right_cancel this).symm
    · exact ⟨⟨a, a⁻¹, mul_inv_cancel₀ h, inv_mul_cancel₀ h⟩, rfl⟩

中文:
引理 isLocalHom_of_存在_map_ne_one
  结论: [函数状 F G₀ M] [幺半群态射类 F G₀ M] {f : F}
  证明: by
    rcases eq_or_ne a 0 with (rfl | h)
    · obtain ⟨t, ht⟩ := hf
      refine (ht ?_).elim
      have := map_mul f t 0
      rw [← one_mul (f (t * 0))]; rw [mul_zero] at this
      exact (h.mul_right_cancel this).symm
    · exact ⟨⟨a, a⁻¹, mul_inv_cancel₀ h, inv_mul_cancel₀ h⟩, rfl⟩

Depends on / 依赖: eq_or_ne, h.mul_right_cancel, map_mul, mul_right_cancel, mul_zero, one_mul
-/
lemma isLocalHom_of_exists_map_ne_one [FunLike F G₀ M] [MonoidHomClass F G₀ M] {f : F}
    (hf : exists x : G₀, f x != 1) : IsLocalHom f where
  map_nonunit a h := by
    rcases eq_or_ne a 0 with (rfl | h)
    · obtain ⟨t, ht⟩ := hf
      refine (ht ?_).elim
      have := map_mul f t 0
      rw [← one_mul (f (t * 0))]; rw [mul_zero] at this
      exact (h.mul_right_cancel this).symm
    · exact ⟨⟨a, a⁻¹, mul_inv_cancel₀ h, inv_mul_cancel₀ h⟩, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FunLike
  signature: F G₀ M₀] [MonoidWithZeroHomClass F G₀ M₀] [Nontrivial M₀]
  body: isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩

中文:
实例 [函数状
  签名: F G₀ M₀] [带零幺半群态射类 F G₀ M₀] [非平凡 M₀]
  定义体: isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩

Depends on / 依赖: isLocalHom_of_exists_map_ne_one
-/
instance [FunLike F G₀ M₀] [MonoidWithZeroHomClass F G₀ M₀] [Nontrivial M₀]
    (f : F) : IsLocalHom f :=
  isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩

end Monoid

section GroupWithZero

namespace Commute

variable [GroupWithZero G₀] {a b c d : G₀}

/--
lemma `div_eq_div_iff` / 引理 `div_eq_div_iff`

English:
lemma div_eq_div_iff
  given: (hbd : Commute b d) (hb : b != 0) (hd : d != 0)
  proof: hbd.div_eq_div_iff_of_isUnit hb.isUnit hd.isUnit

中文:
引理 div_eq_div_iff
  条件: (hbd : Commute b d) (hb : b != 0) (hd : d != 0)
  证明: hbd.div_eq_div_iff_of_isUnit hb.isUnit hd.isUnit
-/
protected lemma div_eq_div_iff (hbd : Commute b d) (hb : b != 0) (hd : d != 0) :
    a / b = c / d ↔ a * d = c * b :=
  hbd.div_eq_div_iff_of_isUnit hb.isUnit hd.isUnit

/--
lemma `mul_inv_eq_mul_inv_iff` / 引理 `mul_inv_eq_mul_inv_iff`

English:
lemma mul_inv_eq_mul_inv_iff
  given: (hbd : Commute b d) (hb : b != 0) (hd : d != 0)
  proof: hbd.mul_inv_eq_mul_inv_iff_of_isUnit hb.isUnit hd.isUnit

中文:
引理 mul_inv_eq_mul_inv_iff
  条件: (hbd : Commute b d) (hb : b != 0) (hd : d != 0)
  证明: hbd.mul_inv_eq_mul_inv_iff_of_isUnit hb.isUnit hd.isUnit
-/
protected lemma mul_inv_eq_mul_inv_iff (hbd : Commute b d) (hb : b != 0) (hd : d != 0) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b :=
  hbd.mul_inv_eq_mul_inv_iff_of_isUnit hb.isUnit hd.isUnit

/--
lemma `inv_mul_eq_inv_mul_iff` / 引理 `inv_mul_eq_inv_mul_iff`

English:
lemma inv_mul_eq_inv_mul_iff
  given: (hbd : Commute b d) (hb : b != 0) (hd : d != 0)
  proof: hbd.inv_mul_eq_inv_mul_iff_of_isUnit hb.isUnit hd.isUnit

中文:
引理 inv_mul_eq_inv_mul_iff
  条件: (hbd : Commute b d) (hb : b != 0) (hd : d != 0)
  证明: hbd.inv_mul_eq_inv_mul_iff_of_isUnit hb.isUnit hd.isUnit
-/
protected lemma inv_mul_eq_inv_mul_iff (hbd : Commute b d) (hb : b != 0) (hd : d != 0) :
    b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c :=
  hbd.inv_mul_eq_inv_mul_iff_of_isUnit hb.isUnit hd.isUnit

end Commute

section MulZeroOneClass

variable [GroupWithZero G₀] [MulZeroOneClass M₀'] [Nontrivial M₀'] [FunLike F G₀ M₀']
  [MonoidWithZeroHomClass F G₀ M₀']
  (f : F) {a : G₀}

/--
theorem `map_ne_zero` / 定理 `map_ne_zero`

English:
theorem map_ne_zero
  statement: f a != 0 ↔ a != 0
  proof: by
refine ⟨fun hfa ha => hfa ha.symm ▸ map_zero f, ?_⟩
  intro hx H
  lift a to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀')
  rw [← map_one f]; rw [← Units.mul_inv a]; rw [map_mul]; rw [H]; rw [zero_mul]

@[simp]

中文:
定理 map_ne_zero
  结论: f a != 0 ↔ a != 0
  证明: by
refine ⟨fun hfa ha => hfa ha.symm ▸ map_zero f, ?_⟩
  intro hx H
  lift a to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀')
  rw [← map_one f]; rw [← Units.mul_inv a]; rw [map_mul]; rw [H]; rw [zero_mul]

@[simp]

Depends on / 依赖: Units.mul_inv, ha.symm, isUnit_iff_ne_zero, isUnit_iff_ne_zero.mpr, map_mul, map_one, map_zero, mul_inv, one_ne_zero, zero_mul
-/
theorem map_ne_zero : f a != 0 ↔ a != 0 := by
refine ⟨fun hfa ha => hfa ha.symm ▸ map_zero f, ?_⟩
  intro hx H
  lift a to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀')
  rw [← map_one f]; rw [← Units.mul_inv a]; rw [map_mul]; rw [H]; rw [zero_mul]

@[simp]
/--
theorem `map_eq_zero` / 定理 `map_eq_zero`

English:
theorem map_eq_zero
  statement: f a = 0 ↔ a = 0
  proof: not_iff_not.1 (map_ne_zero f)

中文:
定理 map_eq_zero
  结论: f a = 0 ↔ a = 0
  证明: not_iff_not.1 (map_ne_zero f)

Depends on / 依赖: map_ne_zero, not_iff_not
-/
theorem map_eq_zero : f a = 0 ↔ a = 0 :=
  not_iff_not.1 (map_ne_zero f)

end MulZeroOneClass

section MonoidWithZero

variable [GroupWithZero G₀] [Nontrivial M₀] [MonoidWithZero M₀'] [FunLike F G₀ M₀]
  [MonoidWithZeroHomClass F G₀ M₀] [FunLike F' G₀ M₀']
  (f : F) {a : G₀}

/--
theorem `eq_on_inv₀` / 定理 `eq_on_inv₀`

English:
theorem eq_on_inv₀
  given: [MonoidWithZeroHomClass F' G₀ M₀'] (f g : F') (h : f a = g a)
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [inv_zero, map_zero, map_zero]
  · exact (IsUnit.mk0 a ha).eq_on_inv f g h

中文:
定理 eq_on_inv₀
  条件: [带零幺半群态射类 F' G₀ M₀'] (f g : F') (h : f a = g a)
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [inv_zero, map_zero, map_zero]
  · exact (IsUnit.mk0 a ha).eq_on_inv f g h

Depends on / 依赖: IsUnit, IsUnit.mk0, eq_on_inv, eq_or_ne, inv_zero, map_zero
-/
theorem eq_on_inv₀ [MonoidWithZeroHomClass F' G₀ M₀'] (f g : F') (h : f a = g a) :
    f a⁻¹ = g a⁻¹ := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [inv_zero, map_zero, map_zero]
  · exact (IsUnit.mk0 a ha).eq_on_inv f g h

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
  [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (a b : G₀)

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp]
/--
theorem `map_inv₀` / 定理 `map_inv₀`

English:
theorem map_inv₀
  statement: f a⁻¹ = (f a)⁻¹
  proof: by
  by_cases h : a = 0
  · simp [h, map_zero f]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]; rw [inv_mul_cancel₀ h]; rw [map_one]

@[simp]

中文:
定理 map_inv₀
  结论: f a⁻¹ = (f a)⁻¹
  证明: by
  by_cases h : a = 0
  · simp [h, map_zero f]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]; rw [inv_mul_cancel₀ h]; rw [map_one]

@[simp]

Depends on / 依赖: eq_inv_of_mul_eq_one_left, map_mul, map_one, map_zero
-/
theorem map_inv₀ : f a⁻¹ = (f a)⁻¹ := by
  by_cases h : a = 0
  · simp [h, map_zero f]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]; rw [inv_mul_cancel₀ h]; rw [map_one]

@[simp]
/--
theorem `map_div₀` / 定理 `map_div₀`

English:
theorem map_div₀
  statement: f (a / b) = f a / f b
  proof: map_div' f (map_inv₀ f) a b

中文:
定理 map_div₀
  结论: f (a / b) = f a / f b
  证明: map_div' f (map_inv₀ f) a b

Depends on / 依赖: map_div
-/
theorem map_div₀ : f (a / b) = f a / f b :=
  map_div' f (map_inv₀ f) a b

end GroupWithZero

/--
Definition of `MonoidWithZero.inverse` / `MonoidWithZero.inverse` 的定义

English:
definition MonoidWithZero.inverse
  signature: {M : Type*} [CommMonoidWithZero M]
  body: Ring.inverse
  map_zero' := Ring.inverse_zero _
  map_one' := Ring.inverse_one _
  map_mul' x y := (Ring.mul_inverse_rev x y).trans (mul_comm _ _)

@[simp]

中文:
定义 带零幺半群.inverse
  签名: {M : 类型} [带零交换幺半群 M]
  定义体: Ring.inverse
  map_zero' := Ring.inverse_zero _
  map_one' := Ring.inverse_one _
  map_mul' x y := (Ring.mul_inverse_rev x y).trans (mul_comm _ _)

@[simp]

Depends on / 依赖: Ring.inverse, ShortComplex, ShortComplex.quasiIso_iff, inverse, quasiIsoAt_iff, quasiIso_iff
-/
noncomputable def MonoidWithZero.inverse {M : Type*} [CommMonoidWithZero M] :
    M ->*₀ M where
  toFun := Ring.inverse
  map_zero' := Ring.inverse_zero _
  map_one' := Ring.inverse_one _
  map_mul' x y := (Ring.mul_inverse_rev x y).trans (mul_comm _ _)

@[simp]
/--
theorem `MonoidWithZero.coe_inverse` / 定理 `MonoidWithZero.coe_inverse`

English:
theorem MonoidWithZero.coe_inverse
  given: {M : Type*} [CommMonoidWithZero M]
  proof: rfl

@[simp]

中文:
定理 带零幺半群.coe_inverse
  条件: {M : 类型} [带零交换幺半群 M]
  证明: rfl

@[simp]
-/
theorem MonoidWithZero.coe_inverse {M : Type*} [CommMonoidWithZero M] :
    (MonoidWithZero.inverse : M -> M) = Ring.inverse :=
  rfl

@[simp]
/--
theorem `MonoidWithZero.inverse_apply` / 定理 `MonoidWithZero.inverse_apply`

English:
theorem MonoidWithZero.inverse_apply
  given: {M : Type*} [CommMonoidWithZero M] (a : M)
  proof: rfl

中文:
定理 带零幺半群.inverse_apply
  条件: {M : 类型} [带零交换幺半群 M] (a : M)
  证明: rfl
-/
theorem MonoidWithZero.inverse_apply {M : Type*} [CommMonoidWithZero M] (a : M) :
    MonoidWithZero.inverse a = a⁻¹ʳ :=
  rfl

/--
Definition of `invMonoidWithZeroHom` / `invMonoidWithZeroHom` 的定义

English:
definition invMonoidWithZeroHom
  signature: {G₀ : Type*} [CommGroupWithZero G₀]
  body: { invMonoidHom with map_zero' := inv_zero }

中文:
定义 invMonoidWithZeroHom
  签名: {G₀ : 类型} [带零交换群 G₀]
  定义体: { invMonoidHom with map_zero' := inv_zero }

Depends on / 依赖: invMonoidHom, inv_zero, map_zero
-/
def invMonoidWithZeroHom {G₀ : Type*} [CommGroupWithZero G₀] : G₀ ->*₀ G₀ :=
  { invMonoidHom with map_zero' := inv_zero }

/-- If a monoid homomorphism `f` between two `GroupWithZero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
@[simp]
/--
theorem `map_zpow₀` / 定理 `map_zpow₀`

English:
theorem map_zpow₀
  statement: {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
  proof: map_zpow' f (map_inv₀ f) x n

中文:
定理 map_zpow₀
  结论: {F G₀ G₀' : 类型} [带零群 G₀] [带零群 G₀'] [函数状 F G₀ G₀']
  证明: map_zpow' f (map_inv₀ f) x n

Depends on / 依赖: map_zpow
-/
theorem map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
    [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n : Int) : f (x ^ n) = f x ^ n :=
  map_zpow' f (map_inv₀ f) x n

end GroupWithZero
