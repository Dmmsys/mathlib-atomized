/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# Semireal rings

A semireal ring is a commutative ring (with unit) in which `-1` is *not* a sum of squares.

For instance, linearly ordered rings are semireal, because sums of squares are positive and `-1` is
not.

## Main declaration

- `IsSemireal`: the predicate asserting that a commutative ring `R` is semireal.

## References

- *An introduction to real algebra*, by T.Y. Lam. Rocky Mountain J. Math. 14(4): 767-814 (1984).
  [lam_1984](https://doi.org/10.1216/RMJ-1984-14-4-767)
-/

public section

variable (R : Type*)

/--
A semireal ring is a commutative ring (with unit) in which `-1` is *not* a sum of
squares. We define the predicate `IsSemireal R` for structures `R` equipped with
a multiplication, an addition, a multiplicative unit and an additive unit.
-/
@[mk_iff]
/--
Definition of `IsSemireal` / `IsSemireal` 的定义

English:
class IsSemireal
  parameters: [Add R] [Mul R] [One R] [Zero R]
  axioms and operations (1):
    - one_add_ne_zero({s : R} (hs : IsSumSq s)) : 1 + s != 0

中文:
类 是Semireal
  参数: [加法 R] [乘法 R] [幺 R] [零 R]
  公理与运算 (1 个):
    - one_add_ne_zero({s : R} (hs : 是SumSq s)) : 1 + s != 0
-/
class IsSemireal [Add R] [Mul R] [One R] [Zero R] : Prop where
  one_add_ne_zero {s : R} (hs : IsSumSq s) : 1 + s != 0

/--
theorem `IsSemireal.not_isSumSq_neg_one` / 定理 `IsSemireal.not_isSumSq_neg_one`

English:
theorem IsSemireal.not_isSumSq_neg_one
  given: [AddGroup R] [One R] [Mul R] [IsSemireal R]
  proof: (by simpa using one_add_ne_zero ·)

中文:
定理 是Semireal.not_isSumSq_neg_one
  条件: [加法群 R] [幺 R] [乘法 R] [是Semireal R]
  证明: (by simpa using one_add_ne_zero ·)

Depends on / 依赖: one_add_ne_zero
-/
theorem IsSemireal.not_isSumSq_neg_one [AddGroup R] [One R] [Mul R] [IsSemireal R] :
    ¬ IsSumSq (-1 : R) := (by simpa using one_add_ne_zero ·)

variable {R} in
/--
theorem `isSemireal_iff_not_isSumSq_neg_one` / 定理 `isSemireal_iff_not_isSumSq_neg_one`

English:
theorem isSemireal_iff_not_isSumSq_neg_one
  given: [AddGroup R] [One R] [Mul R]
  proof: IsSemireal.not_isSumSq_neg_one _
  mpr h := ⟨by aesop (add simp add_eq_zero_iff_neg_eq)⟩

alias ⟨_, IsSemireal.of_not_isSumSq_neg_one⟩ := isSemireal_iff_not_isSumSq_neg_one

中文:
定理 isSemireal_iff_not_isSumSq_neg_one
  条件: [加法群 R] [幺 R] [乘法 R]
  证明: IsSemireal.not_isSumSq_neg_one _
  mpr h := ⟨by aesop (add simp add_eq_zero_iff_neg_eq)⟩

alias ⟨_, IsSemireal.of_not_isSumSq_neg_one⟩ := isSemireal_iff_not_isSumSq_neg_one

Depends on / 依赖: IsSemireal, IsSemireal.not_isSumSq_neg_one, not_isSumSq_neg_one
-/
theorem isSemireal_iff_not_isSumSq_neg_one [AddGroup R] [One R] [Mul R] :
    IsSemireal R ↔ ¬ IsSumSq (-1 : R) where
  mp _ := IsSemireal.not_isSumSq_neg_one _
  mpr h := ⟨by aesop (add simp add_eq_zero_iff_neg_eq)⟩

alias ⟨_, IsSemireal.of_not_isSumSq_neg_one⟩ := isSemireal_iff_not_isSumSq_neg_one

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] : IsSemireal R where
  body: zero_ne_one' R (le_antisymm zero_le_one
                              (le_of_le_of_eq (le_add_of_nonneg_right hs.nonneg) amo))

中文:
实例 [半环
  签名: R] [线性序 R] [是StrictOrdered环 R] [ExistsAddOfLE R] : 是Semireal R where
  定义体: zero_ne_one' R (le_antisymm zero_le_one
                              (le_of_le_of_eq (le_add_of_nonneg_right hs.nonneg) amo))

Depends on / 依赖: le_antisymm, zero_le_one, zero_ne_one
-/
instance [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] : IsSemireal R where
  one_add_ne_zero hs amo := zero_ne_one' R (le_antisymm zero_le_one
                              (le_of_le_of_eq (le_add_of_nonneg_right hs.nonneg) amo))

instance (priority := 90) [NonAssocRing R] [IsSemireal R] : CharZero R :=
  charZero_of_inj_zero fun n hn => by
    cases n with
    | zero => rfl
    | succ n =>
      rw [add_comm] at hn
      push_cast at hn
      simpa using IsSemireal.one_add_ne_zero (by simp) hn
