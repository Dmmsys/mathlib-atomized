/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Euclidean absolute values

This file defines a predicate `AbsoluteValue.IsEuclidean abv` stating the
absolute value is compatible with the Euclidean domain structure on its domain.

## Main definitions

* `AbsoluteValue.IsEuclidean abv` is a predicate on absolute values on `R` mapping to `S`
  that preserve the order on `R` arising from the Euclidean domain structure.
* `AbsoluteValue.abs_isEuclidean` shows the "standard" absolute value on `ℤ`,
  mapping negative `x` to `-x`, is Euclidean.
-/

public section

@[inherit_doc]
local infixl:50 " ≺ " => EuclideanDomain.r

namespace AbsoluteValue

section OrderedSemiring

variable {R S : Type*} [EuclideanDomain R] [Semiring S] [PartialOrder S]
variable (abv : AbsoluteValue R S)

/-- An absolute value `abv : R → S` is Euclidean if it is compatible with the
`EuclideanDomain` structure on `R`, namely `abv` is strictly monotone with respect to the well
founded relation `≺` on `R`. -/
/-
**AbsoluteValue.IsEuclidean** 是 Mathlib 中的一个归纳类型，位于命名空间 `AbsoluteValue`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : EuclideanDomain R] → [inst
_1 : Semiring S] → [inst_2 : PartialOrder S] → AbsoluteValue R S → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute value `abv : R → S` is Euclidean if it is compatible with the
`EuclideanDomain` structure on `R`, namely `abv` is strictly monotone with respe
ct to the well
founded relation `≺` on `R`.
-/
structure IsEuclidean : Prop where
  /-- The requirement of a Euclidean absolute value
  that `abv` is monotone with respect to `≺` -/
  map_lt_map_iff' : ∀ {x y}, abv x < abv y ↔ x ≺ y

namespace IsEuclidean

variable {abv}

-- Rearrange the parameters to `map_lt_map_iff'` so it elaborates better.
/-
**AbsoluteValue.IsEuclidean.map_lt_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteVa
lue.IsEuclidean`。
形式化陈述：map_lt_map_iff {x y : R} (h : abv.IsEuclidean) : abv x < abv y ↔ x ≺ y
参数：h : abv.IsEuclidean。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.IsEuclidean.map_lt_map_iff'`：∀ {R : Type u_1} {S : Type u_
2} [inst : EuclideanDomain R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   
{abv : AbsoluteValue R S}, abv.…
-/
theorem map_lt_map_iff {x y : R} (h : abv.IsEuclidean) : abv x < abv y ↔ x ≺ y :=
  map_lt_map_iff' h

attribute [simp] map_lt_map_iff
/-
**AbsoluteValue.IsEuclidean.sub_mod_lt** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.
IsEuclidean`。
形式化陈述：sub_mod_lt (h : abv.IsEuclidean) (a : R) {b : R} (hb : b != 0) : abv (a % 
b) < abv b
参数：h : abv.IsEuclidean；a : R；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AbsoluteValue.IsEuclidean.map_lt_map_iff`：map_lt_map_iff {x y : R} (h : 
abv.IsEuclidean) : abv x < abv y ↔ x ≺ y
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
-/
theorem sub_mod_lt (h : abv.IsEuclidean) (a : R) {b : R} (hb : b ≠ 0) : abv (a % b) < abv b :=
  h.map_lt_map_iff.mpr (EuclideanDomain.mod_lt a hb)

end IsEuclidean

end OrderedSemiring

section Int

open Int

-- TODO: generalize to `LinearOrderedEuclideanDomain`s if we ever get a definition of those
/-- `abs : ℤ → ℤ` is a Euclidean absolute value -/
/-
**AbsoluteValue.abs_isEuclidean** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：AbsoluteValue.abs.IsEuclidean
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`abs : ℤ → ℤ` is a Euclidean absolute value
-/
protected theorem abs_isEuclidean : IsEuclidean (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) :=
  { map_lt_map_iff' := fun {x y} =>
       show abs x < abs y ↔ natAbs x < natAbs y by rw [abs_eq_natAbs, abs_eq_natAbs, ofNat_lt] }

end Int

end AbsoluteValue

