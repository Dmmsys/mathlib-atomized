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
/-
**IsSemireal** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Add R] → [Mul R] → [One R] → [Zero R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semireal ring is a commutative ring (with unit) in which `-1` is *not* a sum o
f
squares. We define the predicate `IsSemireal R` for structures `R` equipped with
a multiplication, an addition, a multiplicative unit and an additive unit.
-/
class IsSemireal [Add R] [Mul R] [One R] [Zero R] : Prop where
  one_add_ne_zero {s : R} (hs : IsSumSq s) : 1 + s ≠ 0

/-- In a semireal ring, `-1` is not a sum of squares. -/
/-
**IsSemireal.not_isSumSq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemireal.not_isSumSq_neg_one [AddGroup R] [One R] [Mul R] [IsSemireal R]
 : ¬ IsSumSq (-1 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `IsSemireal.one_add_ne_zero`：∀ {R : Type u_1} {inst : Add R} {inst_1 : Mu
l R} {inst_2 : One R} {inst_3 : Zero R} [self : IsSemireal R] {s : R},   IsSumSq
 s → 1 + s ≠ 0

--- 原说明 ---
In a semireal ring, `-1` is not a sum of squares.
-/
theorem IsSemireal.not_isSumSq_neg_one [AddGroup R] [One R] [Mul R] [IsSemireal R] :
    ¬ IsSumSq (-1 : R) := (by simpa using one_add_ne_zero ·)

variable {R} in
/-
**isSemireal_iff_not_isSumSq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSemireal_iff_not_isSumSq_neg_one [AddGroup R] [One R] [Mul R] : IsSemire
al R ↔ ¬ IsSumSq (-1 : R) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemireal.not_isSumSq_neg_one`：IsSemireal.not_isSumSq_neg_one [AddGroup
 R] [One R] [Mul R] [IsSemireal R] : ¬ IsSumSq (-1 : R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem isSemireal_iff_not_isSumSq_neg_one [AddGroup R] [One R] [Mul R] :
    IsSemireal R ↔ ¬ IsSumSq (-1 : R) where
  mp _ := IsSemireal.not_isSumSq_neg_one _
  mpr h := ⟨by aesop (add simp add_eq_zero_iff_neg_eq)⟩

alias ⟨_, IsSemireal.of_not_isSumSq_neg_one⟩ := isSemireal_iff_not_isSumSq_neg_one

/--
Linearly ordered semirings with the property `a ≤ b → ∃ c, a + c = b` (e.g. `ℕ`)
are semireal.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linearly ordered semirings with the property `a ≤ b → ∃ c, a + c = b` (e.g. `ℕ`)
are semireal.
-/
instance [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] : IsSemireal R where
  one_add_ne_zero hs amo := zero_ne_one' R (le_antisymm zero_le_one
                              (le_of_le_of_eq (le_add_of_nonneg_right hs.nonneg) amo))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) [NonAssocRing R] [IsSemireal R] : CharZero R :=
  charZero_of_inj_zero fun n hn ↦ by
    cases n with
    | zero => rfl
    | succ n =>
      rw [add_comm] at hn
      push_cast at hn
      simpa using IsSemireal.one_add_ne_zero (by simp) hn
