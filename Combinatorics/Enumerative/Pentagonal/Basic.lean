/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Data.Int.SuccPred

/-!
# Pentagonal numbers

This file introduces (generalized) pentagonal numbers $k(3k-1)/2$ for integer $k$.

Some sources, such as A001318 in the OEIS, order generalized pentagonal numbers by indices
$k = 0, 1, -1, 2, -2, \cdots$ to form a strictly monotone sequence. This file doesn't follow this
convention, but implicitly shows the monotonicity in `pentagonal_lt_pentagonal_neg` and
`pentagonal_neg_lt_pentagonal_add_one`.

## Main definitions

* `pentagonal`: pentagonal numbers as a function `ℤ → ℕ`.

## References

* https://en.wikipedia.org/wiki/Pentagonal_number
-/

public section

/-- Pentagonal numbers $k(3k-1)/2$ for integer $k$. -/
/-
**pentagonal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pentagonal (k : Int) : Nat
参数：k : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pentagonal numbers $k(3k-1)/2$ for integer $k$.
-/
def pentagonal (k : ℤ) : ℕ := (k * (3 * k - 1) / 2).toNat
/-
**pentagonal_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pentagonal_def (k : Int) : pentagonal k = (k * (3 * k - 1) / 2).toNat
参数：k : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pentagonal_def (k : ℤ) : pentagonal k = (k * (3 * k - 1) / 2).toNat := by rfl
/-
**pentagonal_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pentagonal_neg (k : Int) : pentagonal (-k) = (k * (3 * k + 1) / 2).toNat
参数：k : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pentagonal_neg (k : ℤ) : pentagonal (-k) = (k * (3 * k + 1) / 2).toNat := by
  grind [pentagonal_def]
/-
**natCast_pentagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：natCast_pentagonal (k : Int) : (pentagonal k : Int) = k * (3 * k - 1) / 2
参数：k : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_pentagonal (k : ℤ) : (pentagonal k : ℤ) = k * (3 * k - 1) / 2 := by
  rcases k with (_ | _) | _ <;> grind [pentagonal_def]
/-
**two_mul_natCast_pentagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：two_mul_natCast_pentagonal (k : Int) : 2 * (pentagonal k : Int) = k * (3 *
 k - 1)
参数：k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_pentagonal`：natCast_pentagonal (k : Int) : (pentagonal k : Int) 
= k * (3 * k - 1) / 2
· 使用引理 `Int.two_mul_ediv_two_of_even`：two_mul_ediv_two_of_even : Even n -> 2 * (
n / 2) = n
-/
theorem two_mul_natCast_pentagonal (k : ℤ) : 2 * (pentagonal k : ℤ) = k * (3 * k - 1) := by
  rw [natCast_pentagonal]
  exact Int.two_mul_ediv_two_of_even (by grind)
/-
**two_mul_natCast_pentagonal_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：two_mul_natCast_pentagonal_neg (k : Int) : 2 * (pentagonal (-k) : Int) = k
 * (3 * k + 1)
参数：k : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem two_mul_natCast_pentagonal_neg (k : ℤ) : 2 * (pentagonal (-k) : ℤ) = k * (3 * k + 1) := by
  grind [two_mul_natCast_pentagonal]
/-
**pentagonal_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pentagonal_injective : Function.Injective pentagonal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
-/
theorem pentagonal_injective : Function.Injective pentagonal := by
  intro x y h
  replace h : (3 * (x + y) - 1) * (x - y) = 0 := by grind [two_mul_natCast_pentagonal]
  cases mul_eq_zero.mp h <;> grind

@[simp]
/-
**pentagonal_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pentagonal_inj {x y : Int} : pentagonal x = pentagonal y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `pentagonal_injective`：pentagonal_injective : Function.Injective pentagon
al
-/
theorem pentagonal_inj {x y : ℤ} : pentagonal x = pentagonal y ↔ x = y :=
  pentagonal_injective.eq_iff
/-
**pentagonal_lt_pentagonal_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pentagonal_lt_pentagonal_neg {k : Int} (h : 0 < k) : pentagonal k < pentag
onal (-k)
参数：h : 0 < k。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pentagonal_lt_pentagonal_neg {k : ℤ} (h : 0 < k) : pentagonal k < pentagonal (-k) := by
  grind [natCast_pentagonal]
/-
**pentagonal_neg_lt_pentagonal_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pentagonal_neg_lt_pentagonal_add_one {k : Int} (h : 0 <= k) : pentagonal (
-k) < pentagonal (k + 1)
参数：h : 0 <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pentagonal_neg_lt_pentagonal_add_one {k : ℤ} (h : 0 ≤ k) :
    pentagonal (-k) < pentagonal (k + 1) := by
  grind [natCast_pentagonal]
/-
**pentagonal_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pentagonal_strictMonoOn : StrictMonoOn pentagonal (Set.Ici 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMonoOn_of_lt_add_one`：strictMonoOn_of_lt_add_one (hs : s.OrdConnec
ted) : (forall a, ¬ IsMax a -> a in s -> a + 1 in s -> f a < f (a + 1)) -> Stric
tMonoOn f s
· 使用定理 `Int.instIsSuccArchimedean`：IsSuccArchimedean ℤ
-/
theorem pentagonal_strictMonoOn : StrictMonoOn pentagonal (Set.Ici 0) := by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Ici
  grind [natCast_pentagonal]
/-
**pentagonal_strictAntiOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pentagonal_strictAntiOn : StrictAntiOn pentagonal (Set.Iic 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictAntiOn_of_add_one_lt`：strictAntiOn_of_add_one_lt (hs : s.OrdConnec
ted) : (forall a, ¬ IsMax a -> a in s -> a + 1 in s -> f (a + 1) < f a) -> Stric
tAntiOn f s
· 使用定理 `Int.instIsSuccArchimedean`：IsSuccArchimedean ℤ
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
-/
theorem pentagonal_strictAntiOn : StrictAntiOn pentagonal (Set.Iic 0) := by
  apply strictAntiOn_of_add_one_lt Set.ordConnected_Iic
  grind [natCast_pentagonal]
