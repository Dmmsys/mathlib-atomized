/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Lemmas about semiconjugate elements in a `GroupWithZero`.

-/

public section

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace SemiconjBy

@[simp]
/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  given: [MulZeroClass G₀] (a : G₀)
  statement: SemiconjBy a 0 0
  proof: by
  simp only [SemiconjBy, mul_zero, zero_mul]

@[simp]

中文:
定理 zero_right
  条件: [乘零类 G₀] (a : G₀)
  结论: SemiconjBy a 0 0
  证明: by
  simp only [SemiconjBy, mul_zero, zero_mul]

@[simp]

Depends on / 依赖: SemiconjBy, mul_zero, zero_mul
-/
theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [SemiconjBy, mul_zero, zero_mul]

@[simp]
/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  given: [MulZeroClass G₀] (x y : G₀)
  statement: SemiconjBy 0 x y
  proof: by
  simp only [SemiconjBy, mul_zero, zero_mul]

中文:
定理 zero_left
  条件: [乘零类 G₀] (x y : G₀)
  结论: SemiconjBy 0 x y
  证明: by
  simp only [SemiconjBy, mul_zero, zero_mul]

Depends on / 依赖: SemiconjBy, mul_zero, zero_mul
-/
theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [SemiconjBy, mul_zero, zero_mul]

variable [GroupWithZero G₀] {a x y x' y' : G₀}

@[simp]
/--
theorem `inv_symm_left_iff₀` / 定理 `inv_symm_left_iff₀`

English:
theorem inv_symm_left_iff₀
  statement: SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x
  proof: Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _

中文:
定理 inv_symm_left_iff₀
  结论: SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x
  证明: Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _

Depends on / 依赖: Classical, Classical.by_cases, SemiconjBy, SemiconjBy.zero_left, Units.mk0, inv_zero, units_inv_symm_left_iff, zero_left
-/
theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _

/--
theorem `inv_symm_left₀` / 定理 `inv_symm_left₀`

English:
theorem inv_symm_left₀
  given: (h : SemiconjBy a x y)
  statement: SemiconjBy a⁻¹ y x
  proof: SemiconjBy.inv_symm_left_iff₀.2 h

中文:
定理 inv_symm_left₀
  条件: (h : SemiconjBy a x y)
  结论: SemiconjBy a⁻¹ y x
  证明: SemiconjBy.inv_symm_left_iff₀.2 h

Depends on / 依赖: SemiconjBy, SemiconjBy.inv_symm_left_iff
-/
theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  SemiconjBy.inv_symm_left_iff₀.2 h

/--
theorem `inv_right₀` / 定理 `inv_right₀`

English:
theorem inv_right₀
  given: (h : SemiconjBy a x y)
  statement: SemiconjBy a x⁻¹ y⁻¹
  proof: by
  by_cases ha : a = 0
  · simp only [ha, zero_left]
  by_cases hx : x = 0
  · subst x
    simp only [SemiconjBy, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h
    simp [h.resolve_right ha]
  · have := mul_ne_zero ha hx
    rw [h.eq]; rw [mul_ne_zero_iff] at this
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h

@[simp]

中文:
定理 inv_right₀
  条件: (h : SemiconjBy a x y)
  结论: SemiconjBy a x⁻¹ y⁻¹
  证明: by
  by_cases ha : a = 0
  · simp only [ha, zero_left]
  by_cases hx : x = 0
  · subst x
    simp only [SemiconjBy, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h
    simp [h.resolve_right ha]
  · have := mul_ne_zero ha hx
    rw [h.eq]; rw [mul_ne_zero_iff] at this
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h

@[simp]

Depends on / 依赖: SemiconjBy, Units.mk0, eq_comm, h.eq, h.resolve_right, mul_eq_zero, mul_ne_zero, mul_ne_zero_iff, mul_zero, resolve_right, units_inv_right, zero_left
-/
theorem inv_right₀ (h : SemiconjBy a x y) : SemiconjBy a x⁻¹ y⁻¹ := by
  by_cases ha : a = 0
  · simp only [ha, zero_left]
  by_cases hx : x = 0
  · subst x
    simp only [SemiconjBy, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h
    simp [h.resolve_right ha]
  · have := mul_ne_zero ha hx
    rw [h.eq]; rw [mul_ne_zero_iff] at this
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h

@[simp]
/--
theorem `inv_right_iff₀` / 定理 `inv_right_iff₀`

English:
theorem inv_right_iff₀
  statement: SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y
  proof: ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩

中文:
定理 inv_right_iff₀
  结论: SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y
  证明: ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩

Depends on / 依赖: h.inv_right, inv_inv
-/
theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩

/--
theorem `div_right` / 定理 `div_right`

English:
theorem div_right
  given: (h : SemiconjBy a x y) (h' : SemiconjBy a x' y')
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact h.mul_right h'.inv_right₀

中文:
定理 div_right
  条件: (h : SemiconjBy a x y) (h' : SemiconjBy a x' y')
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact h.mul_right h'.inv_right₀

Depends on / 依赖: div_eq_mul_inv, h.mul_right, mul_right
-/
theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact h.mul_right h'.inv_right₀

/--
lemma `zpow_right₀` / 引理 `zpow_right₀`

English:
lemma zpow_right₀
  given: {a x y : G₀} (h : SemiconjBy a x y)
  statement: forall m : Int, SemiconjBy a (x ^ m) (y ^ m)

中文:
引理 zpow_right₀
  条件: {a x y : G₀} (h : SemiconjBy a x y)
  结论: 对任意 m : 整数, SemiconjBy a (x ^ m) (y ^ m)
-/
lemma zpow_right₀ {a x y : G₀} (h : SemiconjBy a x y) : forall m : Int, SemiconjBy a (x ^ m) (y ^ m)
  | (n : Nat) => by simp [h.pow_right n]
  | .negSucc n => by simp only [zpow_negSucc, (h.pow_right (n + 1)).inv_right₀]

end SemiconjBy

namespace Commute
variable [GroupWithZero G₀] {a b : G₀}

/--
lemma `zpow_right₀` / 引理 `zpow_right₀`

English:
lemma zpow_right₀
  given: (h : Commute a b)
  statement: forall m : Int, Commute a (b ^ m)
  proof: SemiconjBy.zpow_right₀ h

中文:
引理 zpow_right₀
  条件: (h : Commute a b)
  结论: 对任意 m : 整数, Commute a (b ^ m)
  证明: SemiconjBy.zpow_right₀ h

Depends on / 依赖: SemiconjBy, SemiconjBy.zpow_right
-/
lemma zpow_right₀ (h : Commute a b) : forall m : Int, Commute a (b ^ m) := SemiconjBy.zpow_right₀ h

/--
lemma `zpow_left₀` / 引理 `zpow_left₀`

English:
lemma zpow_left₀
  given: (h : Commute a b) (m : Int)
  statement: Commute (a ^ m) b
  proof: (h.symm.zpow_right₀ m).symm

中文:
引理 zpow_left₀
  条件: (h : Commute a b) (m : 整数)
  结论: Commute (a ^ m) b
  证明: (h.symm.zpow_right₀ m).symm

Depends on / 依赖: h.symm.zpow_right
-/
lemma zpow_left₀ (h : Commute a b) (m : Int) : Commute (a ^ m) b := (h.symm.zpow_right₀ m).symm

/--
lemma `zpow_zpow₀` / 引理 `zpow_zpow₀`

English:
lemma zpow_zpow₀
  given: (h : Commute a b) (m n : Int)
  statement: Commute (a ^ m) (b ^ n)
  proof: (h.zpow_left₀ m).zpow_right₀ n

中文:
引理 zpow_zpow₀
  条件: (h : Commute a b) (m n : 整数)
  结论: Commute (a ^ m) (b ^ n)
  证明: (h.zpow_left₀ m).zpow_right₀ n

Depends on / 依赖: h.zpow_left
-/
lemma zpow_zpow₀ (h : Commute a b) (m n : Int) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left₀ m).zpow_right₀ n

/--
lemma `zpow_self₀` / 引理 `zpow_self₀`

English:
lemma zpow_self₀
  given: (a : G₀) (n : Int)
  statement: Commute (a ^ n) a
  proof: (Commute.refl a).zpow_left₀ n

中文:
引理 zpow_self₀
  条件: (a : G₀) (n : 整数)
  结论: Commute (a ^ n) a
  证明: (Commute.refl a).zpow_left₀ n

Depends on / 依赖: Commute, Commute.refl
-/
lemma zpow_self₀ (a : G₀) (n : Int) : Commute (a ^ n) a := (Commute.refl a).zpow_left₀ n

/--
lemma `self_zpow₀` / 引理 `self_zpow₀`

English:
lemma self_zpow₀
  given: (a : G₀) (n : Int)
  statement: Commute a (a ^ n)
  proof: (Commute.refl a).zpow_right₀ n

中文:
引理 self_zpow₀
  条件: (a : G₀) (n : 整数)
  结论: Commute a (a ^ n)
  证明: (Commute.refl a).zpow_right₀ n

Depends on / 依赖: Commute, Commute.refl
-/
lemma self_zpow₀ (a : G₀) (n : Int) : Commute a (a ^ n) := (Commute.refl a).zpow_right₀ n

/--
lemma `zpow_zpow_self₀` / 引理 `zpow_zpow_self₀`

English:
lemma zpow_zpow_self₀
  given: (a : G₀) (m n : Int)
  statement: Commute (a ^ m) (a ^ n)
  proof: (Commute.refl a).zpow_zpow₀ m n

中文:
引理 zpow_zpow_self₀
  条件: (a : G₀) (m n : 整数)
  结论: Commute (a ^ m) (a ^ n)
  证明: (Commute.refl a).zpow_zpow₀ m n

Depends on / 依赖: Commute, Commute.refl
-/
lemma zpow_zpow_self₀ (a : G₀) (m n : Int) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow₀ m n

end Commute
