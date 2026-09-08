/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Schröder numbers

The Schröder numbers (https://oeis.org/A006318) are a sequence of integers that appear in various
combinatorial contexts.

## Main definitions

* `largeSchroder n`: the `n`th large Schröder number, defined recursively as `L 0 = 1` and
  `L (n + 1) = L n + ∑ i ≤ n, L i * L (n - i)`.
* `smallSchroder n`: the `n`th small Schröder number, defined as `S 0 = 1` and `S n = L n / 2`
  for `n > 0`.

## Main results

* `largeSchroder_even` : The large Schröder numbers are positive and even for `n > 0`.
* `smallSchroder_succ` : A recursive formula for small Schröder numbers:
  `S (n + 1) = 3 * S n + 2 * ∑ i < n - 2, S (i + 2) * S (n - 1 - i)`.

## Tags

Schroeder, Schroder
-/

@[expose] public section

open Finset

namespace Nat
variable {n : ℕ}

/-- The recursive definition of the sequence of the large Schröder numbers :
`a (n + 1) = a n + ∑ i : Fin n.succ, a i * a (n - i)` -/
/-
**Nat.largeSchroder** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The recursive definition of the sequence of the large Schröder numbers :
`a (n + 1) = a n + ∑ i : Fin n.succ, a i * a (n - i)`
-/
def largeSchroder : ℕ → ℕ
  | 0 => 1
  | n + 1 => largeSchroder n + ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)
/-
**Nat.largeSchroder_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.largeSchroder 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.largeSchroder.eq_1`：Nat.largeSchroder 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem largeSchroder_zero : largeSchroder 0 = 1 := by simp [largeSchroder]
/-
**Nat.largeSchroder_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.largeSchroder 1 = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.largeSchroder.eq_2`：∀ (n : ℕ), n.succ.largeSchroder = n.largeSchrode
r + ∑ i, (↑i).largeSchroder * (n - ↑i).largeSchroder
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.largeSchroder_zero`：Nat.largeSchroder 0 = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem largeSchroder_one : largeSchroder 1 = 2 := by simp [largeSchroder]
/-
**Nat.largeSchroder_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.largeSchroder 2 = 6
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.largeSchroder.eq_2`：∀ (n : ℕ), n.succ.largeSchroder = n.largeSchrode
r + ∑ i, (↑i).largeSchroder * (n - ↑i).largeSchroder
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.largeSchroder_one`：Nat.largeSchroder 1 = 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Nat.largeSchroder_zero`：Nat.largeSchroder 0 = 1
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem largeSchroder_two : largeSchroder 2 = 6 := by simp [largeSchroder]
/-
**Nat.largeSchroder_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：largeSchroder_succ (n : Nat) : largeSchroder (n + 1) = largeSchroder n + ∑
 i <= n, largeSchroder i * largeSchroder (n - i)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.largeSchroder.eq_2`：∀ (n : ℕ), n.succ.largeSchroder = n.largeSchrode
r + ∑ i, (↑i).largeSchroder * (n - ↑i).largeSchroder
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.Iio_eq_range`：Iio_eq_range : Iio a = range a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem largeSchroder_succ (n : ℕ) :
    largeSchroder (n + 1) = largeSchroder n + ∑ i ≤ n, largeSchroder i * largeSchroder (n - i) := by
  simp [largeSchroder, ← Iio_add_one_eq_Iic, Nat.Iio_eq_range, ← Fin.sum_univ_eq_sum_range]
/-
**Nat.even_largeSchroder** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：even_largeSchroder : forall {n : Nat}, n != 0 -> Even (largeSchroder n) | 
1, _ => by simp | n + 2, _ => by rw [largeSchroder_succ] refine .add (even_large
Schroder n.succ_ne_zero) even_sum _ fun k hk => ?_ obtain _ | k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.even_largeSchroder._unary`：∀ (_x : (n : ℕ) ×' n ≠ 0), Even _x.1.larg
eSchroder
-/
theorem even_largeSchroder : ∀ {n : ℕ}, n ≠ 0 → Even (largeSchroder n)
  | 1, _ => by simp
  | n + 2, _ => by
    rw [largeSchroder_succ]
    refine .add (even_largeSchroder n.succ_ne_zero) <| even_sum _ fun k hk ↦ ?_
    obtain _ | k := k
    · simpa using even_largeSchroder n.succ_ne_zero
    have : k < n + 1 := by simp at hk; lia
    exact .mul_right (even_largeSchroder k.succ_ne_zero) _

/-- The small Schröder number is equal to : `largeSchroder n = 2 * smallSchroder (n + 1), n ≥ 1` -/
/-
**Nat.smallSchroder** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The small Schröder number is equal to : `largeSchroder n = 2 * smallSchroder (n 
+ 1), n ≥ 1`
-/
def smallSchroder : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 1 => largeSchroder n / 2
/-
**Nat.smallSchroder_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.smallSchroder 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma smallSchroder_zero : smallSchroder 0 = 1 := by simp [smallSchroder]
/-
**Nat.smallSchroder_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.smallSchroder 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.Schroder.0.Nat.smallSchroder.
match_1.eq_2`：∀ (motive : ℕ → Sort u_1) (h_1 : Unit → motive 0) (h_2 : Unit → mo
tive 1) (h_3 : (n : ℕ) → motive n.succ),   (match 1 with     | 0 => h_1 ()…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma smallSchroder_one : smallSchroder 1 = 1 := by simp [smallSchroder]
/-
**Nat.smallSchroder_succ_eq_largeSchroder_div_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat
`。
形式化陈述：smallSchroder_succ_eq_largeSchroder_div_two (h : n != 0) : smallSchroder (
n + 1) = largeSchroder n / 2
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.Schroder.0.Nat.smallSchroder.
match_1.eq_3`：∀ (motive : ℕ → Sort u_1) (n : ℕ) (h_1 : Unit → motive 0) (h_2 : U
nit → motive 1) (h_3 : (n : ℕ) → motive n.succ),   (n = 0 → False) →     (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smallSchroder_succ_eq_largeSchroder_div_two (h : n ≠ 0) :
    smallSchroder (n + 1) = largeSchroder n / 2 := by simp [smallSchroder]
/-
**Nat.two_mul_smallSchroder_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_mul_smallSchroder_succ (hn : n != 0) : 2 * smallSchroder (n + 1) = lar
geSchroder n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smallSchroder_succ_eq_largeSchroder_div_two`：smallSchroder_succ_eq_l
argeSchroder_div_two (h : n != 0) : smallSchroder (n + 1) = largeSchroder n / 2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mul_div_cancel_left'`：∀ {a b : ℕ}, a ∣ b → a * (b / a) = b
· 使用定理 `Even.two_dvd`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → 2 ∣
 a
· 使用定理 `Nat.even_largeSchroder`：even_largeSchroder : forall {n : Nat}, n != 0 ->
 Even (largeSchroder n) | 1, _ => by simp | n + 2, _ => by rw [largeSchroder_suc
c] refine .a…
-/
lemma two_mul_smallSchroder_succ (hn : n ≠ 0) : 2 * smallSchroder (n + 1) = largeSchroder n := by
  rw [smallSchroder_succ_eq_largeSchroder_div_two hn,
    Nat.mul_div_cancel_left' (even_largeSchroder hn).two_dvd]
/-
**Nat.smallSchroder_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：smallSchroder_succ (hn : 1 < n) : smallSchroder (n + 1) = 3 * n.smallSchro
der + 2 * ∑ i in Ioo 0 (n - 1), (i + 1).smallSchroder * (n - i).smallSchroder
参数：hn : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.mul_left_cancel`：∀ {n m k : ℕ}, 0 < n → n * m = n * k → m = k
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Nat.two_mul_smallSchroder_succ`：two_mul_smallSchroder_succ (hn : n != 0)
 : 2 * smallSchroder (n + 1) = largeSchroder n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.largeSchroder_succ`：largeSchroder_succ (n : Nat) : largeSchroder (n 
+ 1) = largeSchroder n + ∑ i <= n, largeSchroder i * largeSchroder (n - i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Icc_bot`：Icc_bot [OrderBot α] : Icc (⊥ : α) a = Iic a
· 使用定理 `Finset.sum_Ioc_add_eq_sum_Icc`：∀ {α : Type u_1} {M : Type u_2} [inst : A
ddCommMonoid M] {f : α → M} {a b : α} [inst_1 : PartialOrder α]   [inst_2 : Loca
llyFiniteOrder α], …
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Finset.sum_Ioo_add_eq_sum_Ioc`：∀ {α : Type u_1} {M : Type u_2} [inst : A
ddCommMonoid M] {f : α → M} {a b : α} [inst_1 : PartialOrder α]   [inst_2 : Loca
llyFiniteOrder α], …
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
（共 37 条，此处仅展示前 30 条）
-/
theorem smallSchroder_succ (hn : 1 < n) :
    smallSchroder (n + 1) =
      3 * n.smallSchroder +
          2 * ∑ i ∈ Ioo 0 (n - 1), (i + 1).smallSchroder * (n - i).smallSchroder := by
  obtain _ | _ | n := n
  · simp at hn
  · simp at hn
  refine Nat.mul_left_cancel zero_lt_two ?_
  calc
        2 * (n + 3).smallSchroder
    _ = 3 * (n + 1).largeSchroder +
          ∑ i ∈ Ioo 0 (n + 1), i.largeSchroder * (n + 1 - i).largeSchroder := by
      rw [two_mul_smallSchroder_succ, largeSchroder_succ, ← Icc_bot, ← sum_Ioc_add_eq_sum_Icc,
        ← sum_Ioo_add_eq_sum_Ioc] <;> simp; lia
    _ = 3 * (n + 1).largeSchroder +
          ∑ i ∈ Ioo 0 (n + 1), (2 * (i + 1).smallSchroder) * (2 * (n + 2 - i).smallSchroder) := by
      congr! 2 with i hi
      simp at hi
      rw [← two_mul_smallSchroder_succ, ← two_mul_smallSchroder_succ] <;>
      · #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
        we need to re-enable model-based theory combination in `lia` for this to go through. -/
        lia +mbtc
    _ = 6 * (n + 2).smallSchroder +
          4 * ∑ i ∈ Ioo 0 (n + 1), (i + 1).smallSchroder * (n + 2 - i).smallSchroder := by
      rw [← two_mul_smallSchroder_succ (by lia)]
      simp [mul_mul_mul_comm _ _ 2, ← Finset.mul_sum]
      lia
    _ = _ := by lia

end Nat

