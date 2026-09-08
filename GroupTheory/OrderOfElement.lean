/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Julian Kuelshammer
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Group.Action
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Order of an element

This file defines the order of an element of a finite group. For a finite group `G` the order of
`x ∈ G` is the minimal `n ≥ 1` such that `x ^ n = 1`.

## Main definitions

* `IsOfFinOrder` is a predicate on an element `x` of a monoid `G` saying that `x` is of finite
  order.
* `IsOfFinAddOrder` is the additive analogue of `IsOfFinOrder`.
* `orderOf x` defines the order of an element `x` of a monoid `G`, by convention its value is `0`
  if `x` has infinite order.
* `addOrderOf` is the additive analogue of `orderOf`.

## Tags
order of an element
-/

@[expose] public section

assert_not_exists Field

open Function Fintype Nat Pointwise Subgroup Submonoid
open scoped Finset

variable {G H A α β : Type*}

section Monoid
variable [Monoid G] {a b x y : G} {n m : ℕ}

section IsOfFinOrder

@[to_additive]
/-
**isPeriodicPt_mul_iff_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPeriodicPt_mul_iff_pow_eq_one (x : G) : IsPeriodicPt (x * ·) n 1 ↔ x ^ n
 = 1
参数：x : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.IsPeriodicPt.eq_1`：∀ {α : Type u_1} (f : α → α) (n : ℕ) (x : α)
, Function.IsPeriodicPt f n x = Function.IsFixedPt f^[n] x
· 使用定理 `Function.IsFixedPt.eq_1`：∀ {α : Type u₁} (f : α → α) (x : α), Function.I
sFixedPt f x = (f x = x)
· 使用引理 `mul_left_iterate_apply_one`：mul_left_iterate_apply_one (a : M) : (a * ·)
^[n] 1 = a ^ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPeriodicPt_mul_iff_pow_eq_one (x : G) : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1 := by
  rw [IsPeriodicPt, IsFixedPt, mul_left_iterate_apply_one]

/-- `IsOfFinOrder` is a predicate on an element `x` of a monoid to be of finite order, i.e. there
exists `n ≥ 1` such that `x ^ n = 1`. -/
@[to_additive /-- `IsOfFinAddOrder` is a predicate on an element `a` of an
additive monoid to be of finite order, i.e. there exists `n ≥ 1` such that `n • a = 0`. -/]
/-
**IsOfFinOrder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsOfFinOrder (x : G) : Prop
参数：x : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsOfFinOrder (x : G) : Prop :=
  (1 : G) ∈ periodicPts (x * ·)
/-
**isOfFinAddOrder_ofMul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOfFinAddOrder_ofMul_iff : IsOfFinAddOrder (Additive.ofMul x) ↔ IsOfFinOr
der x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOfFinAddOrder_ofMul_iff : IsOfFinAddOrder (Additive.ofMul x) ↔ IsOfFinOrder x :=
  Iff.rfl
/-
**isOfFinOrder_ofAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOfFinOrder_ofAdd_iff {α : Type*} [AddMonoid α] {x : α} : IsOfFinOrder (M
ultiplicative.ofAdd x) ↔ IsOfFinAddOrder x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOfFinOrder_ofAdd_iff {α : Type*} [AddMonoid α] {x : α} :
    IsOfFinOrder (Multiplicative.ofAdd x) ↔ IsOfFinAddOrder x := Iff.rfl

@[to_additive]
/-
**isOfFinOrder_iff_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder x ↔ exists n, 0 < n ∧ x ^ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOfFinOrder_iff_pow_eq_one : IsOfFinOrder x ↔ ∃ n, 0 < n ∧ x ^ n = 1 := by
  simp [IsOfFinOrder, mem_periodicPts, isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.exists_pow_eq_one, _⟩ := isOfFinOrder_iff_pow_eq_one

@[to_additive]
/-
**isOfFinOrder_iff_zpow_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOfFinOrder_iff_zpow_eq_one {G} [DivisionMonoid G] {x : G} : IsOfFinOrder
 x ↔ exists (n : Int), n != 0 ∧ x ^ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero_iff_pos`：∀ {n : ℕ}, ↑n ≠ 0 ↔ 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.natAbs_pos`：∀ {a : ℤ}, 0 < a.natAbs ↔ a ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natAbs_eq_iff`：∀ {a : ℤ} {n : ℕ}, a.natAbs = n ↔ a = ↑n ∨ a = -↑n
· 使用定理 `inv_eq_one`：inv_eq_one : a⁻¹ = 1 ↔ a = 1
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
-/
lemma isOfFinOrder_iff_zpow_eq_one {G} [DivisionMonoid G] {x : G} :
    IsOfFinOrder x ↔ ∃ (n : ℤ), n ≠ 0 ∧ x ^ n = 1 := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, hn, hn'⟩ ↦ ⟨n, Int.natCast_ne_zero_iff_pos.mpr hn, zpow_natCast x n ▸ hn'⟩,
    fun ⟨n, hn, hn'⟩ ↦ ⟨n.natAbs, Int.natAbs_pos.mpr hn, ?_⟩⟩
  rcases (Int.natAbs_eq_iff (a := n)).mp rfl with h | h
  · rwa [h, zpow_natCast] at hn'
  · rwa [h, zpow_neg, inv_eq_one, zpow_natCast] at hn'

/-- See also `injective_pow_iff_not_isOfFinOrder`. -/
@[to_additive /-- See also `injective_nsmul_iff_not_isOfFinAddOrder`. -/]
/-
**not_isOfFinOrder_of_injective_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isOfFinOrder_of_injective_pow {x : G} (h : Injective fun n : Nat => x 
^ n) : ¬IsOfFinOrder x
参数：h : Injective fun n : Nat => x ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1

--- 原说明 ---
See also `injective_pow_iff_not_isOfFinOrder`.
-/
theorem not_isOfFinOrder_of_injective_pow {x : G} (h : Injective fun n : ℕ => x ^ n) :
    ¬IsOfFinOrder x := by
  simp_rw [isOfFinOrder_iff_pow_eq_one, not_exists, not_and]
  intro n hn_pos hnx
  rw [← pow_zero x] at hnx
  rw [h hnx] at hn_pos
  exact irrefl 0 hn_pos

/-- 1 is of finite order in any monoid. -/
@[to_additive (attr := simp) /-- 0 is of finite order in any additive monoid. -/]
/-
**IsOfFinOrder.one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.one : IsOfFinOrder (1 : G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a

--- 原说明 ---
1 is of finite order in any monoid.
-/
theorem IsOfFinOrder.one : IsOfFinOrder (1 : G) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.one_pos, one_pow 1⟩

@[to_additive]
/-
**IsOfFinOrder.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.pow {n : Nat} : IsOfFinOrder a -> IsOfFinOrder (a ^ n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_right_comm`：pow_right_comm (a : M) (m n : Nat) : (a ^ m) ^ n = (a ^ 
n) ^ m
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsOfFinOrder.pow {n : ℕ} : IsOfFinOrder a → IsOfFinOrder (a ^ n) := by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨m, hm, ha⟩
  exact ⟨m, hm, by simp [pow_right_comm _ n, ha]⟩

@[to_additive]
/-
**IsOfFinOrder.of_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.of_pow {n : Nat} (h : IsOfFinOrder (a ^ n)) (hn : n != 0) : I
sOfFinOrder a
参数：h : IsOfFinOrder (a ^ n)；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
lemma IsOfFinOrder.of_pow {n : ℕ} (h : IsOfFinOrder (a ^ n)) (hn : n ≠ 0) : IsOfFinOrder a := by
  rw [isOfFinOrder_iff_pow_eq_one] at *
  rcases h with ⟨m, hm, ha⟩
  exact ⟨n * m, mul_pos hn.bot_lt hm, by rwa [pow_mul]⟩

@[to_additive (attr := simp)]
/-
**isOfFinOrder_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOfFinOrder_pow {n : Nat} : IsOfFinOrder (a ^ n) ↔ IsOfFinOrder a ∨ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsOfFinOrder.of_pow`：IsOfFinOrder.of_pow {n : Nat} (h : IsOfFinOrder (a 
^ n)) (hn : n != 0) : IsOfFinOrder a
· 使用引理 `IsOfFinOrder.pow`：IsOfFinOrder.pow {n : Nat} : IsOfFinOrder a -> IsOfFin
Order (a ^ n)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
-/
lemma isOfFinOrder_pow {n : ℕ} : IsOfFinOrder (a ^ n) ↔ IsOfFinOrder a ∨ n = 0 := by
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · simp
  · exact ⟨fun h ↦ .inl <| h.of_pow hn, fun h ↦ (h.resolve_right hn).pow⟩

@[to_additive]
/-
**not_isOfFinOrder_of_isMulTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_isOfFinOrder_of_isMulTorsionFree [IsMulTorsionFree G] (ha : a != 1) : 
¬ IsOfFinOrder a
参数：ha : a != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用引理 `pow_left_injective`：pow_left_injective (hn : n != 0) : Injective fun a :
 M => a ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
lemma not_isOfFinOrder_of_isMulTorsionFree [IsMulTorsionFree G] (ha : a ≠ 1) :
    ¬ IsOfFinOrder a := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, han⟩
  exact ha <| pow_left_injective hn.ne' <| by simpa using han

@[to_additive]
/-
**IsOfFinOrder.eq_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.eq_one' [IsMulTorsionFree G] {a : G} (ha : IsOfFinOrder a) : 
a = 1
参数：ha : IsOfFinOrder a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `not_isOfFinOrder_of_isMulTorsionFree`：not_isOfFinOrder_of_isMulTorsionFr
ee [IsMulTorsionFree G] (ha : a != 1) : ¬ IsOfFinOrder a
-/
lemma IsOfFinOrder.eq_one' [IsMulTorsionFree G] {a : G} (ha : IsOfFinOrder a) :
    a = 1 := by
  contrapose! ha
  apply not_isOfFinOrder_of_isMulTorsionFree ha

@[to_additive]
/-
**isOfFinOrder_iff_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOfFinOrder_iff_eq_one [IsMulTorsionFree G] (a : G) : IsOfFinOrder a ↔ a 
= 1
参数：a : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOfFinOrder.eq_one'`：IsOfFinOrder.eq_one' [IsMulTorsionFree G] {a : G} 
(ha : IsOfFinOrder a) : a = 1
· 使用定理 `IsOfFinOrder.one`：IsOfFinOrder.one : IsOfFinOrder (1 : G)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isOfFinOrder_iff_eq_one [IsMulTorsionFree G] (a : G) : IsOfFinOrder a ↔ a = 1 :=
  ⟨IsOfFinOrder.eq_one', fun h => h.symm ▸ IsOfFinOrder.one⟩

/-- Elements of finite order are of finite order in submonoids. -/
@[to_additive /-- Elements of finite order are of finite order in submonoids. -/]
/-
**Submonoid.isOfFinOrder_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.isOfFinOrder_coe {H : Submonoid G} {x : H} : IsOfFinOrder (x : G
) ↔ IsOfFinOrder x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Elements of finite order are of finite order in submonoids.
-/
theorem Submonoid.isOfFinOrder_coe {H : Submonoid G} {x : H} :
    IsOfFinOrder (x : G) ↔ IsOfFinOrder x := by
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  norm_cast
/-
**IsConj.isOfFinOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConj.isOfFinOrder (h : IsConj x y) : IsOfFinOrder x -> IsOfFinOrder y
参数：h : IsConj x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isConj_one_right`：isConj_one_right {a : α} : IsConj 1 a ↔ a = 1
· 使用定理 `IsConj.pow`：∀ {α : Type u} [inst : Monoid α] {a b : α} (n : ℕ), IsConj a
 b → IsConj (a ^ n) (b ^ n)
-/
theorem IsConj.isOfFinOrder (h : IsConj x y) : IsOfFinOrder x → IsOfFinOrder y := by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, n_gt_0, eq'⟩
  exact ⟨n, n_gt_0, by rw [← isConj_one_right, ← eq']; exact h.pow n⟩

/-- The image of an element of finite order has finite order. -/
@[to_additive /-- The image of an element of finite additive order has finite additive order. -/]
/-
**MonoidHom.isOfFinOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.isOfFinOrder [Monoid H] (f : G ->* H) {x : G} (h : IsOfFinOrder 
x) : IsOfFinOrder f x
参数：f : G ->* H；h : IsOfFinOrder x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `IsOfFinOrder.exists_pow_eq_one`：∀ {G : Type u_1} [inst : Monoid G] {x : 
G}, IsOfFinOrder x → ∃ n, 0 < n ∧ x ^ n = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1

--- 原说明 ---
The image of an element of finite order has finite order.
-/
theorem MonoidHom.isOfFinOrder [Monoid H] (f : G →* H) {x : G} (h : IsOfFinOrder x) :
    IsOfFinOrder <| f x :=
  isOfFinOrder_iff_pow_eq_one.mpr <| by
    obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
    exact ⟨n, npos, by rw [← f.map_pow, hn, f.map_one]⟩

/-- If a direct product has finite order then so does each component. -/
@[to_additive /-- If a direct product has finite additive order then so does each component. -/]
/-
**IsOfFinOrder.apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.apply {η : Type*} {Gs : η -> Type*} [forall i, Monoid (Gs i)]
 {x : forall i, Gs i} (h : IsOfFinOrder x) : forall i, IsOfFinOrder (x i)
参数：Gs i；h : IsOfFinOrder x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.exists_pow_eq_one`：∀ {G : Type u_1} [inst : Monoid G] {x : 
G}, IsOfFinOrder x → ∃ n, 0 < n ∧ x ^ n = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
If a direct product has finite order then so does each component.
-/
theorem IsOfFinOrder.apply {η : Type*} {Gs : η → Type*} [∀ i, Monoid (Gs i)] {x : ∀ i, Gs i}
    (h : IsOfFinOrder x) : ∀ i, IsOfFinOrder (x i) := by
  obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
  exact fun _ => isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, (congr_fun hn.symm _).symm⟩

/-- The submonoid generated by an element is a group if that element has finite order. -/
@[to_additive /-- The additive submonoid generated by an element is
an additive group if that element has finite order. -/]
/-
**IsOfFinOrder.groupPowers** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsOfFinOrder.groupPowers (hx : IsOfFinOrder x) : Group (Submonoid.powers x
)
参数：hx : IsOfFinOrder x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.exists_pow_eq_one`：∀ {G : Type u_1} [inst : Monoid G] {x : 
G}, IsOfFinOrder x → ∃ n, 0 < n ∧ x ^ n = 1
-/
noncomputable abbrev IsOfFinOrder.groupPowers (hx : IsOfFinOrder x) :
    Group (Submonoid.powers x) := by
  obtain ⟨hpos, hx⟩ := hx.exists_pow_eq_one.choose_spec
  exact Submonoid.groupPowers hpos hx

end IsOfFinOrder

/-- `orderOf x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `x ^ n = 1` if it exists.
Otherwise, i.e. if `x` is of infinite order, then `orderOf x` is `0` by convention. -/
@[to_additive
  /-- `addOrderOf a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it
  exists. Otherwise, i.e. if `a` is of infinite order, then `addOrderOf a` is `0` by convention. -/]
/-
**orderOf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：orderOf (x : G) : Nat
参数：x : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def orderOf (x : G) : ℕ :=
  minimalPeriod (x * ·) 1

@[to_additive (attr := nontriviality)]
/-
**Subsingleton.orderOf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.orderOf_eq [Subsingleton G] (x : G) : orderOf x = 1
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.minimalPeriod_eq_one_of_subsingleton`：minimalPeriod_eq_one_of_s
ubsingleton [Subsingleton α] : minimalPeriod f x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Subsingleton.orderOf_eq [Subsingleton G] (x : G) : orderOf x = 1 := by
  simp [orderOf, nontriviality]

@[simp]
/-
**addOrderOf_ofMul_eq_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：addOrderOf_ofMul_eq_orderOf (x : G) : addOrderOf (Additive.ofMul x) = orde
rOf x
参数：x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem addOrderOf_ofMul_eq_orderOf (x : G) : addOrderOf (Additive.ofMul x) = orderOf x :=
  rfl

@[simp]
/-
**orderOf_ofAdd_eq_addOrderOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_ofAdd_eq_addOrderOf {α : Type*} [AddMonoid α] (a : α) : orderOf (M
ultiplicative.ofAdd a) = addOrderOf a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderOf_ofAdd_eq_addOrderOf {α : Type*} [AddMonoid α] (a : α) :
    orderOf (Multiplicative.ofAdd a) = addOrderOf a := rfl

@[to_additive]
/-
**IsOfFinOrder.orderOf_pos** 是 Mathlib 中的一个定理，位于命名空间 `IsOfFinOrder`。
形式化陈述：∀ {G : Type u_1} [inst : Monoid G] {x : G}, IsOfFinOrder x → 0 < orderOf x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_pos_of_mem_periodicPts`：minimalPeriod_pos_of_mem_
periodicPts (hx : x in periodicPts f) : 0 < minimalPeriod f x
-/
protected lemma IsOfFinOrder.orderOf_pos (h : IsOfFinOrder x) : 0 < orderOf x :=
  minimalPeriod_pos_of_mem_periodicPts h

@[to_additive (attr := simp) addOrderOf_nsmul_eq_zero]
/-
**pow_orderOf_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf.eq_1`：∀ {G : Type u_1} [inst : Monoid G] (x : G), orderOf x = Fu
nction.minimalPeriod (fun x_1 => x * x_1) 1
· 使用引理 `mul_left_iterate_apply_one`：mul_left_iterate_apply_one (a : M) : (a * ·)
^[n] 1 = a ^ n
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
-/
theorem pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1 := by
  convert! Eq.trans _ (isPeriodicPt_minimalPeriod (x * ·) 1)
  rw [orderOf, mul_left_iterate_apply_one]

@[to_additive]
/-
**orderOf_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0
参数：h : ¬IsOfFinOrder x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf.eq_1`：∀ {G : Type u_1} [inst : Monoid G] (x : G), orderOf x = Fu
nction.minimalPeriod (fun x_1 => x * x_1) 1
· 使用定理 `Function.minimalPeriod.eq_1`：∀ {α : Type u_1} (f : α → α) (x : α),   Fun
ction.minimalPeriod f x = if h : x ∈ Function.periodicPts f then Nat.find h else
 0
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem orderOf_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0 := by
  rwa [orderOf, minimalPeriod, dif_neg]

@[to_additive (attr := simp)]
/-
**orderOf_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用定理 `orderOf_eq_zero`：orderOf_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0
-/
theorem orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder x :=
  ⟨fun h H ↦ H.orderOf_pos.ne' h, orderOf_eq_zero⟩

@[to_additive]
/-
**orderOf_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_zero_iff' : orderOf x = 0 ↔ forall n : Nat, 0 < n -> x ^ n != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem orderOf_eq_zero_iff' : orderOf x = 0 ↔ ∀ n : ℕ, 0 < n → x ^ n ≠ 1 := by
  simp_rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one, not_exists, not_and]

@[to_additive]
/-
**orderOf_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_ne_zero_iff : orderOf x != 0 ↔ IsOfFinOrder x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `orderOf_eq_zero_iff`：orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder
 x
-/
lemma orderOf_ne_zero_iff : orderOf x ≠ 0 ↔ IsOfFinOrder x := orderOf_eq_zero_iff.not_left

/-- In a nontrivial monoid with zero, the order of the zero element is zero. -/
@[simp]
/-
**orderOf_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_zero (M₀ : Type*) [MonoidWithZero M₀] [Nontrivial M₀] : orderOf (0
 : M₀) = 0
参数：M₀ : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_eq_zero_iff`：orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder
 x
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
In a nontrivial monoid with zero, the order of the zero element is zero.
-/
lemma orderOf_zero (M₀ : Type*) [MonoidWithZero M₀] [Nontrivial M₀] : orderOf (0 : M₀) = 0 := by
  rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one]
  simp +contextual [ne_of_gt]

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**orderOf_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_iff {n} (h : 0 < n) : orderOf x = n ↔ x ^ n = 1 ∧ forall m, m <
 n -> 0 < m -> x ^ m != 1
参数：h : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Nat.find_eq_iff`：find_eq_iff (h : exists n : Nat, p n) : Nat.find h = m 
↔ p m ∧ forall n < m, ¬p n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `iff_false_left`：∀ {a b : Prop}, ¬a → ((a ↔ b) ↔ ¬b)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem orderOf_eq_iff {n} (h : 0 < n) :
    orderOf x = n ↔ x ^ n = 1 ∧ ∀ m, m < n → 0 < m → x ^ m ≠ 1 := by
  simp_rw [Ne, ← isPeriodicPt_mul_iff_pow_eq_one, orderOf, minimalPeriod]
  split_ifs with h1
  · classical
    rw [find_eq_iff]
    simp only [h, true_and, not_and]
  · rw [iff_false_left h.ne]
    rintro ⟨h', -⟩
    exact h1 ⟨n, h, h'⟩

/-- A group element has finite order iff its order is positive. -/
@[to_additive (attr := simp)
/-- A group element has finite additive order iff its order is positive. -/]
/-
**orderOf_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `orderOf_eq_zero_iff`：orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder
 x
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x := by
  rw [iff_not_comm.mp orderOf_eq_zero_iff, pos_iff_ne_zero]

@[to_additive]
/-
**IsOfFinOrder.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.mono [Monoid β] {y : β} (hx : IsOfFinOrder x) (h : orderOf y 
∣ orderOf x) : IsOfFinOrder y
参数：hx : IsOfFinOrder x；h : orderOf y ∣ orderOf x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_pos_iff`：orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x
· 使用定理 `Nat.pos_of_dvd_of_pos`：∀ {m n : ℕ}, m ∣ n → 0 < n → 0 < m
-/
theorem IsOfFinOrder.mono [Monoid β] {y : β} (hx : IsOfFinOrder x) (h : orderOf y ∣ orderOf x) :
    IsOfFinOrder y := by rw [← orderOf_pos_iff] at hx ⊢; exact Nat.pos_of_dvd_of_pos h hx

@[to_additive]
/-
**pow_ne_one_of_lt_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_ne_one_of_lt_orderOf (n0 : n != 0) (h : n < orderOf x) : x ^ n != 1
参数：n0 : n != 0；h : n < orderOf x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod`：∀ {α : Type u_1} {
f : α → α} {x : α} {n : ℕ}, n ≠ 0 → n < Function.minimalPeriod f x → ¬Function.I
sPeriodicPt f n x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPeriodicPt_mul_iff_pow_eq_one`：isPeriodicPt_mul_iff_pow_eq_one (x : G)
 : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
-/
theorem pow_ne_one_of_lt_orderOf (n0 : n ≠ 0) (h : n < orderOf x) : x ^ n ≠ 1 := fun j =>
  not_isPeriodicPt_of_pos_of_lt_minimalPeriod n0 h ((isPeriodicPt_mul_iff_pow_eq_one x).mpr j)
@[to_additive]
/-
**orderOf_le_of_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_le_of_pow_eq_one (hn : 0 < n) (h : x ^ n = 1) : orderOf x <= n
参数：hn : 0 < n；h : x ^ n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_le`：∀ {α : Type u_1} {f : α → α} {x 
: α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → Function.minimalPeriod f x ≤
 n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPeriodicPt_mul_iff_pow_eq_one`：isPeriodicPt_mul_iff_pow_eq_one (x : G)
 : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
-/
theorem orderOf_le_of_pow_eq_one (hn : 0 < n) (h : x ^ n = 1) : orderOf x ≤ n :=
  IsPeriodicPt.minimalPeriod_le hn (by rwa [isPeriodicPt_mul_iff_pow_eq_one])

@[to_additive (attr := simp)]
/-
**orderOf_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_one : orderOf (1 : G) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf.eq_1`：∀ {G : Type u_1} [inst : Monoid G] (x : G), orderOf x = Fu
nction.minimalPeriod (fun x_1 => x * x_1) 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.minimalPeriod_id`：∀ {α : Type u_1} {x : α}, Function.minimalPer
iod id x = 1
· 使用定理 `one_mul_eq_id`：one_mul_eq_id : ((1 : M) * ·) = id
-/
theorem orderOf_one : orderOf (1 : G) = 1 := by
  rw [orderOf, ← minimalPeriod_id (x := (1 : G)), ← one_mul_eq_id]

@[to_additive (attr := simp) AddMonoid.addOrderOf_eq_one_iff]
/-
**orderOf_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf.eq_1`：∀ {G : Type u_1} [inst : Monoid G] (x : G), orderOf x = Fu
nction.minimalPeriod (fun x_1 => x * x_1) 1
· 使用定理 `Function.minimalPeriod_eq_one_iff_isFixedPt`：minimalPeriod_eq_one_iff_is
FixedPt : minimalPeriod f x = 1 ↔ IsFixedPt f x
· 使用定理 `Function.IsFixedPt.eq_1`：∀ {α : Type u₁} (f : α → α) (x : α), Function.I
sFixedPt f x = (f x = x)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1 := by
  rw [orderOf, minimalPeriod_eq_one_iff_isFixedPt, IsFixedPt, mul_one]

@[to_additive (attr := simp) mod_addOrderOf_nsmul]
/-
**pow_mod_orderOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x) = x ^ n
参数：x : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
-/
lemma pow_mod_orderOf (x : G) (n : ℕ) : x ^ (n % orderOf x) = x ^ n :=
  calc
    x ^ (n % orderOf x) = x ^ (n % orderOf x + orderOf x * (n / orderOf x)) := by
        simp [pow_add, pow_mul, pow_orderOf_eq_one]
    _ = x ^ n := by rw [Nat.mod_add_div]

@[to_additive]
/-
**orderOf_dvd_of_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : orderOf x ∣ n
参数：h : x ^ n = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_dvd`：∀ {α : Type u_1} {f : α → α} {x
 : α} {n : ℕ}, Function.IsPeriodicPt f n x → Function.minimalPeriod f x ∣ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPeriodicPt_mul_iff_pow_eq_one`：isPeriodicPt_mul_iff_pow_eq_one (x : G)
 : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
-/
theorem orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : orderOf x ∣ n :=
  IsPeriodicPt.minimalPeriod_dvd ((isPeriodicPt_mul_iff_pow_eq_one _).mpr h)

@[to_additive]
/-
**orderOf_dvd_iff_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_dvd_iff_pow_eq_one {n : Nat} : orderOf x ∣ n ↔ x ^ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
· 使用定理 `Nat.mod_eq_zero_of_dvd`：∀ {m n : ℕ}, m ∣ n → n % m = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
-/
theorem orderOf_dvd_iff_pow_eq_one {n : ℕ} : orderOf x ∣ n ↔ x ^ n = 1 :=
  ⟨fun h => by rw [← pow_mod_orderOf, Nat.mod_eq_zero_of_dvd h, _root_.pow_zero],
    orderOf_dvd_of_pow_eq_one⟩

/-- If `x ^ p = 1` for some odd `p`, then every power of `x` is an even power of `x`. -/
@[to_additive /-- If `p • x = 0` for some odd `p`, then every multiple of `x` is an even
multiple of `x`. -/]
/-
**exists_pow_eq_pow_two_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pow_eq_pow_two_mul {p : Nat} (hx : x ^ p = 1) (hp : Odd p) (n : Nat
) : exists m, x ^ n = x ^ (2 * m)
参数：hx : x ^ p = 1；hp : Odd p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem exists_pow_eq_pow_two_mul {p : ℕ} (hx : x ^ p = 1) (hp : Odd p) (n : ℕ) :
    ∃ m, x ^ n = x ^ (2 * m) := by
  obtain ⟨r, rfl⟩ := hp
  have key : x ^ (2 * (r + 1)) = x := by
    have h2 : 2 * (r + 1) = 2 * r + 1 + 1 := by omega
    rw [h2, pow_succ, hx, one_mul]
  exact ⟨(r + 1) * n, by rw [← mul_assoc, pow_mul, key]⟩

@[to_additive addOrderOf_smul_dvd]
/-
**orderOf_pow_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_pow_dvd (n : Nat) : orderOf (x ^ n) ∣ orderOf x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用引理 `pow_right_comm`：pow_right_comm (a : M) (m n : Nat) : (a ^ m) ^ n = (a ^ 
n) ^ m
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem orderOf_pow_dvd (n : ℕ) : orderOf (x ^ n) ∣ orderOf x := by
  rw [orderOf_dvd_iff_pow_eq_one, pow_right_comm, pow_orderOf_eq_one, one_pow]

@[to_additive]
/-
**pow_injOn_Iio_orderOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_injOn_Iio_orderOf : (Set.Iio <| orderOf x).InjOn (x ^ ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_left_iterate_apply_one`：mul_left_iterate_apply_one (a : M) : (a * ·)
^[n] 1 = a ^ n
· 使用定理 `Function.iterate_injOn_Iio_minimalPeriod`：iterate_injOn_Iio_minimalPerio
d : (Iio <| minimalPeriod f x).InjOn (f^[·] x)
-/
lemma pow_injOn_Iio_orderOf : (Set.Iio <| orderOf x).InjOn (x ^ ·) := by
  simpa only [mul_left_iterate_apply_one]
    using! iterate_injOn_Iio_minimalPeriod (f := (x * ·)) (x := 1)

@[to_additive]
/-
**IsOfFinOrder.mem_powers_iff_mem_range_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `IsOfF
inOrder`。
形式化陈述：∀ {G : Type u_1} [inst : Monoid G] {x y : G} [inst_1 : DecidableEq G],   I
sOfFinOrder x → (y ∈ Submonoid.powers x ↔ y ∈ Finset.image (fun x_1 => x ^ x_1) 
(Finset.range (orderOf x)))
参数：y ∈ Submonoid.powers x ↔ y ∈ Finset.image (fun x_1 => x ^ x_1) (Finset.range 
(orderOf x))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_range_iff_mem_finset_range_of_mod_eq'`：mem_range_iff_mem_fins
et_range_of_mod_eq' [DecidableEq α] {f : Nat -> α} {a : α} {n : Nat} (hn : 0 < n
) (h : forall i, f (i % n) = f i) : a …
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
-/
protected lemma IsOfFinOrder.mem_powers_iff_mem_range_orderOf [DecidableEq G]
    (hx : IsOfFinOrder x) :
    y ∈ Submonoid.powers x ↔ y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
  Finset.mem_range_iff_mem_finset_range_of_mod_eq' hx.orderOf_pos <| pow_mod_orderOf _

@[to_additive]
/-
**IsOfFinOrder.powers_eq_image_range_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `IsOfFinO
rder`。
形式化陈述：∀ {G : Type u_1} [inst : Monoid G] {x : G} [inst_1 : DecidableEq G],   IsO
fFinOrder x → ↑(Submonoid.powers x) = ↑(Finset.image (fun x_1 => x ^ x_1) (Finse
t.range (orderOf x)))
参数：Submonoid.powers x；Finset.image (fun x_1 => x ^ x_1) (Finset.range (orderOf x
))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsOfFinOrder.mem_powers_iff_mem_range_orderOf`：∀ {G : Type u_1} [inst : 
Monoid G] {x y : G} [inst_1 : DecidableEq G],   IsOfFinOrder x → (y ∈ Submonoid.
powers x ↔ y ∈ Finset.image (fun x_…
-/
protected lemma IsOfFinOrder.powers_eq_image_range_orderOf [DecidableEq G] (hx : IsOfFinOrder x) :
    (Submonoid.powers x : Set G) = (Finset.range (orderOf x)).image (x ^ ·) :=
  Set.ext fun _ ↦ hx.mem_powers_iff_mem_range_orderOf

@[to_additive]
/-
**pow_eq_pow_of_modEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_eq_pow_of_modEq {a b : Nat} (h : a ≡ b [MOD n]) (hx : x ^ n = 1) : x ^
 a = x ^ b
参数：h : a ≡ b [MOD n]；hx : x ^ n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_exists_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = a + c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pow_eq_pow_of_modEq {a b : ℕ} (h : a ≡ b [MOD n]) (hx : x ^ n = 1) : x ^ a = x ^ b := by
  obtain hle | hle := le_total a b
  all_goals
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp hle
    obtain ⟨c, rfl⟩ : n ∣ c := by simpa using h
    simp [pow_add, pow_mul, hx]

@[to_additive]
/-
**pow_eq_one_iff_modEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_eq_one_iff_modEq : x ^ n = 1 ↔ n ≡ 0 [MOD orderOf x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pow_eq_one_iff_modEq : x ^ n = 1 ↔ n ≡ 0 [MOD orderOf x] := by
  rw [modEq_zero_iff_dvd, orderOf_dvd_iff_pow_eq_one]

@[to_additive]
/-
**orderOf_map_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_map_dvd {H : Type*} [Monoid H] (ψ : G ->* H) (x : G) : orderOf (ψ 
x) ∣ orderOf x
参数：ψ : G ->* H；x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem orderOf_map_dvd {H : Type*} [Monoid H] (ψ : G →* H) (x : G) :
    orderOf (ψ x) ∣ orderOf x := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow, pow_orderOf_eq_one]
  apply map_one

@[to_additive]
/-
**exists_pow_eq_self_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pow_eq_self_of_coprime (h : n.Coprime (orderOf x)) : exists m : Nat
, (x ^ n) ^ m = x
参数：h : n.Coprime (orderOf x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.coprime_zero_right`：∀ (n : ℕ), n.Coprime 0 ↔ n = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orderOf_eq_one_iff`：orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.exists_mul_mod_eq_one_of_coprime`：exists_mul_mod_eq_one_of_coprime {
k n : Nat} (hkn : Coprime n k) (hk : 1 < k) : exists m < k, n * m % k = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
-/
theorem exists_pow_eq_self_of_coprime (h : n.Coprime (orderOf x)) : ∃ m : ℕ, (x ^ n) ^ m = x := by
  by_cases h0 : orderOf x = 0
  · rw [h0, coprime_zero_right] at h
    exact ⟨1, by rw [h, pow_one, pow_one]⟩
  by_cases h1 : orderOf x = 1
  · exact ⟨0, by rw [orderOf_eq_one_iff.mp h1, one_pow, one_pow]⟩
  obtain ⟨m, -, h⟩ := exists_mul_mod_eq_one_of_coprime h (by lia)
  exact ⟨m, by rw [← pow_mul, ← pow_mod_orderOf, h, pow_one]⟩

/-- If `x^n = 1`, but `x^(n/p) ≠ 1` for all prime factors `p` of `n`,
then `x` has order `n` in `G`. -/
@[to_additive addOrderOf_eq_of_nsmul_and_div_prime_nsmul /-- If `n * x = 0`, but `n/p * x ≠ 0` for
all prime factors `p` of `n`, then `x` has order `n` in `G`. -/]
/-
**orderOf_eq_of_pow_and_pow_div_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_of_pow_and_pow_div_prime (hn : 0 < n) (hx : x ^ n = 1) (hd : fo
rall p : Nat, p.Prime -> p ∣ n -> x ^ (n / p) != 1) : orderOf x = n
参数：hn : 0 < n；hx : x ^ n = 1；hd : forall p : Nat, p.Prime -> p ∣ n -> x ^ (n / p
) != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_mul_right_of_dvd`：exists_eq_mul_right_of_dvd (h : a ∣ b) : exi
sts c, b = a * c
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `exists_eq_mul_left_of_dvd`：exists_eq_mul_left_of_dvd (h : a ∣ b) : exist
s c, b = c * a
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `Nat.dvd_div_iff_mul_dvd`：∀ {a b c : ℕ}, c ∣ b → (a ∣ b / c ↔ c * a ∣ b)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.mul_dvd_mul_iff_left`：∀ {a b c : ℕ}, 0 < a → (a * b ∣ a * c ↔ b ∣ c)
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orderOf_eq_of_pow_and_pow_div_prime (hn : 0 < n) (hx : x ^ n = 1)
    (hd : ∀ p : ℕ, p.Prime → p ∣ n → x ^ (n / p) ≠ 1) : orderOf x = n := by
  -- Let `a` be `n/(orderOf x)`, and show `a = 1`
  obtain ⟨a, ha⟩ := exists_eq_mul_right_of_dvd (orderOf_dvd_of_pow_eq_one hx)
  suffices a = 1 by simp [this, ha]
  -- Assume `a` is not one...
  by_contra h
  have a_min_fac_dvd_p_sub_one : a.minFac ∣ n := by
    obtain ⟨b, hb⟩ : ∃ b : ℕ, a = b * a.minFac := exists_eq_mul_left_of_dvd a.minFac_dvd
    rw [hb, ← mul_assoc] at ha
    exact Dvd.intro_left (orderOf x * b) ha.symm
  -- Use the minimum prime factor of `a` as `p`.
  refine hd a.minFac (Nat.minFac_prime h) a_min_fac_dvd_p_sub_one ?_
  rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_div_iff_mul_dvd a_min_fac_dvd_p_sub_one, ha, mul_comm,
    Nat.mul_dvd_mul_iff_left (IsOfFinOrder.orderOf_pos _)]
  · exact Nat.minFac_dvd a
  · rw [isOfFinOrder_iff_pow_eq_one]
    exact Exists.intro n (id ⟨hn, hx⟩)

@[to_additive]
/-
**orderOf_eq_orderOf_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_orderOf_iff {H : Type*} [Monoid H] {y : H} : orderOf x = orderO
f y ↔ forall n : Nat, x ^ n = 1 ↔ y ^ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem orderOf_eq_orderOf_iff {H : Type*} [Monoid H] {y : H} :
    orderOf x = orderOf y ↔ ∀ n : ℕ, x ^ n = 1 ↔ y ^ n = 1 := by
  simp_rw [← isPeriodicPt_mul_iff_pow_eq_one, ← minimalPeriod_eq_minimalPeriod_iff, orderOf]

/-- An injective homomorphism of monoids preserves orders of elements. -/
@[to_additive /-- An injective homomorphism of additive monoids preserves orders of elements. -/]
/-
**orderOf_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H) (hf : Function.Inje
ctive f) (x : G) : orderOf (f x) = orderOf x
参数：f : G ->* H；hf : Function.Injective f；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
An injective homomorphism of monoids preserves orders of elements.
-/
theorem orderOf_injective {H : Type*} [Monoid H] (f : G →* H) (hf : Function.Injective f) (x : G) :
    orderOf (f x) = orderOf x := by
  simp_rw [orderOf_eq_orderOf_iff, ← f.map_pow, ← f.map_one, hf.eq_iff, forall_const]

/-- A multiplicative equivalence preserves orders of elements. -/
@[to_additive (attr := simp) /-- An additive equivalence preserves orders of elements. -/]
/-
**MulEquiv.orderOf_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulEquiv.orderOf_eq {H : Type*} [Monoid H] (e : G ≃* H) (x : G) : orderOf 
(e x) = orderOf x
参数：e : G ≃* H；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e

--- 原说明 ---
A multiplicative equivalence preserves orders of elements.
-/
lemma MulEquiv.orderOf_eq {H : Type*} [Monoid H] (e : G ≃* H) (x : G) :
    orderOf (e x) = orderOf x :=
  orderOf_injective e.toMonoidHom e.injective x

@[to_additive]
/-
**Function.Injective.isOfFinOrder_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.isOfFinOrder_iff [Monoid H] {f : G ->* H} (hf : Injecti
ve f) : IsOfFinOrder (f x) ↔ IsOfFinOrder x
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_pos_iff`：orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Function.Injective.isOfFinOrder_iff [Monoid H] {f : G →* H} (hf : Injective f) :
    IsOfFinOrder (f x) ↔ IsOfFinOrder x := by
  rw [← orderOf_pos_iff, orderOf_injective f hf x, ← orderOf_pos_iff]

@[to_additive (attr := norm_cast, simp)]
/-
**orderOf_submonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_submonoid {H : Submonoid G} (y : H) : orderOf (y : G) = orderOf y
参数：y : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem orderOf_submonoid {H : Submonoid G} (y : H) : orderOf (y : G) = orderOf y :=
  orderOf_injective H.subtype Subtype.coe_injective y

@[to_additive (attr := norm_cast)]
/-
**orderOf_units** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
-/
theorem orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y :=
  orderOf_injective (Units.coeHom G) Units.val_injective y

@[to_additive]
/-
**IsUnit.orderOf_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.orderOf_eq_one [Subsingleton Gˣ] {x : G} (h : IsUnit x) : orderOf x
 = 1
参数：h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isUnit_iff_eq_one`：isUnit_iff_eq_one : IsUnit a ↔ a = 1 where mp
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsUnit.orderOf_eq_one [Subsingleton Gˣ] {x : G} (h : IsUnit x) :
    orderOf x = 1 := by
  simp [isUnit_iff_eq_one.mp h]

@[to_additive (attr := norm_cast)]
/-
**Units.isOfFinOrder_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.isOfFinOrder_val {u : Gˣ} : IsOfFinOrder (u : G) ↔ IsOfFinOrder u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOfFinOrder_iff`：Function.Injective.isOfFinOrder_iff
 [Monoid H] {f : G ->* H} (hf : Injective f) : IsOfFinOrder (f x) ↔ IsOfFinOrder
 x
· 使用定理 `Units.coeHom_injective`：coeHom_injective : Function.Injective (coeHom M)
-/
theorem Units.isOfFinOrder_val {u : Gˣ} : IsOfFinOrder (u : G) ↔ IsOfFinOrder u :=
  Units.coeHom_injective.isOfFinOrder_iff

/-- If the order of `x` is finite, then `x` is a unit with inverse `x ^ (orderOf x - 1)`. -/
@[to_additive (attr := simps) /-- If the additive order of `x` is finite, then `x` is an additive
unit with inverse `(addOrderOf x - 1) • x`. -/]
/-
**IsOfFinOrder.unit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsOfFinOrder.unit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : Mˣ
参数：hx : IsOfFinOrder x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def IsOfFinOrder.unit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : Mˣ :=
  ⟨x, x ^ (orderOf x - 1),
    by rw [← _root_.pow_succ', tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one],
    by rw [← _root_.pow_succ, tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one]⟩

@[to_additive]
/-
**IsOfFinOrder.isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.isUnit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : IsUnit 
x
参数：hx : IsOfFinOrder x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsOfFinOrder.isUnit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : IsUnit x := ⟨hx.unit, rfl⟩

variable (x)

@[to_additive]
/-
**orderOf_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_pow' (h : n != 0) : orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf
 x) n
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.minimalPeriod_iterate_eq_div_gcd`：minimalPeriod_iterate_eq_div_
gcd (h : n != 0) : minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalP
eriod f x) n
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
-/
theorem orderOf_pow' (h : n ≠ 0) : orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf x) n := by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd h, mul_left_iterate]

@[to_additive]
/-
**orderOf_pow_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_pow_of_dvd {x : G} {n : Nat} (hn : n != 0) (dvd : n ∣ orderOf x) :
 orderOf (x ^ n) = orderOf x / n
参数：hn : n != 0；dvd : n ∣ orderOf x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_pow'`：orderOf_pow' (h : n != 0) : orderOf (x ^ n) = orderOf x / 
Nat.gcd (orderOf x) n
· 使用定理 `Nat.gcd_eq_right`：∀ {m n : ℕ}, n ∣ m → m.gcd n = n
-/
lemma orderOf_pow_of_dvd {x : G} {n : ℕ} (hn : n ≠ 0) (dvd : n ∣ orderOf x) :
    orderOf (x ^ n) = orderOf x / n := by rw [orderOf_pow' _ hn, Nat.gcd_eq_right dvd]

@[to_additive]
/-
**orderOf_pow_orderOf_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_pow_orderOf_div {x : G} {n : Nat} (hx : orderOf x != 0) (hn : n ∣ 
orderOf x) : orderOf (x ^ (orderOf x / n)) = n
参数：hx : orderOf x != 0；hn : n ∣ orderOf x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `orderOf_pow_of_dvd`：orderOf_pow_of_dvd {x : G} {n : Nat} (hn : n != 0) (
dvd : n ∣ orderOf x) : orderOf (x ^ n) = orderOf x / n
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `Nat.div_dvd_of_dvd`：∀ {n m : ℕ}, n ∣ m → m / n ∣ m
· 使用定理 `Nat.div_div_self`：∀ {n m : ℕ}, n ∣ m → m ≠ 0 → m / (m / n) = n
-/
lemma orderOf_pow_orderOf_div {x : G} {n : ℕ} (hx : orderOf x ≠ 0) (hn : n ∣ orderOf x) :
    orderOf (x ^ (orderOf x / n)) = n := by
  rw [orderOf_pow_of_dvd _ (Nat.div_dvd_of_dvd hn), Nat.div_div_self hn hx]
  rw [← Nat.div_mul_cancel hn] at hx; exact left_ne_zero_of_mul hx

variable (n)

@[to_additive]
/-
**IsOfFinOrder.orderOf_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsOfFinOrder`。
形式化陈述：∀ {G : Type u_1} [inst : Monoid G] (x : G) (n : ℕ), IsOfFinOrder x → order
Of (x ^ n) = orderOf x / (orderOf x).gcd n
参数：x : G；n : ℕ；x ^ n；orderOf x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.minimalPeriod_iterate_eq_div_gcd'`：minimalPeriod_iterate_eq_div
_gcd' (h : x in periodicPts f) : minimalPeriod f^[n] x = minimalPeriod f x / Nat
.gcd (minimalPeriod f x) n
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
-/
protected lemma IsOfFinOrder.orderOf_pow (h : IsOfFinOrder x) :
    orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf x) n := by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd' h, mul_left_iterate]

@[to_additive]
/-
**Nat.Coprime.orderOf_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Coprime.orderOf_pow (h : (orderOf y).Coprime m) : orderOf (y ^ m) = or
derOf y
参数：h : (orderOf y).Coprime m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOfFinOrder.orderOf_pow`：∀ {G : Type u_1} [inst : Monoid G] (x : G) (n 
: ℕ), IsOfFinOrder x → orderOf (x ^ n) = orderOf x / (orderOf x).gcd n
· 使用定理 `Nat.Coprime.gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n → m.gcd n = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用定理 `orderOf_eq_zero`：orderOf_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma Nat.Coprime.orderOf_pow (h : (orderOf y).Coprime m) : orderOf (y ^ m) = orderOf y := by
  by_cases hg : IsOfFinOrder y
  · rw [hg.orderOf_pow y m, h.gcd_eq_one, Nat.div_one]
  · rw [m.coprime_zero_left.1 (orderOf_eq_zero hg ▸ h), pow_one]

@[to_additive]
/-
**IsOfFinOrder.natCard_powers_le_orderOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.natCard_powers_le_orderOf (ha : IsOfFinOrder a) : Nat.card (p
owers a : Set G) <= orderOf a
参数：ha : IsOfFinOrder a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOfFinOrder.powers_eq_image_range_orderOf`：∀ {G : Type u_1} [inst : Mon
oid G] {x : G} [inst_1 : DecidableEq G],   IsOfFinOrder x → ↑(Submonoid.powers x
) = ↑(Finset.image (fun x_1 => x…
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Set.toFinset_Iio`：∀ {α : Type u_3} [inst : Preorder α] [inst_1 : Locally
FiniteOrderBot α] (a : α) [inst_2 : Fintype ↑(Set.Iio a)],   (Set.Iio a).toFinse
t = Fi…
· 使用定理 `Nat.Iio_eq_range`：Iio_eq_range : Iio a = range a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
lemma IsOfFinOrder.natCard_powers_le_orderOf (ha : IsOfFinOrder a) :
    Nat.card (powers a : Set G) ≤ orderOf a := by
  classical
  simpa [ha.powers_eq_image_range_orderOf, Finset.card_range, Nat.Iio_eq_range]
    using Finset.card_image_le (s := Finset.range (orderOf a))

@[to_additive]
/-
**IsOfFinOrder.finite_powers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.finite_powers (ha : IsOfFinOrder a) : (powers a : Set G).Fini
te
参数：ha : IsOfFinOrder a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOfFinOrder.powers_eq_image_range_orderOf`：∀ {G : Type u_1} [inst : Mon
oid G] {x : G} [inst_1 : DecidableEq G],   IsOfFinOrder x → ↑(Submonoid.powers x
) = ↑(Finset.image (fun x_1 => x…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
lemma IsOfFinOrder.finite_powers (ha : IsOfFinOrder a) : (powers a : Set G).Finite := by
  classical rw [ha.powers_eq_image_range_orderOf]; exact Finset.finite_toSet _

namespace Commute

variable {x}

@[to_additive]
/-
**Commute.orderOf_mul_dvd_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：orderOf_mul_dvd_lcm (h : Commute x y) : orderOf (x * y) ∣ Nat.lcm (orderOf
 x) (orderOf y)
参数：h : Commute x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf.eq_1`：∀ {G : Type u_1} [inst : Monoid G] (x : G), orderOf x = Fu
nction.minimalPeriod (fun x_1 => x * x_1) 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comp_mul_left`：comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·)
· 使用定理 `Function.Commute.minimalPeriod_of_comp_dvd_lcm`：∀ {α : Type u_1} {f : α 
→ α} {x : α} {g : α → α},   Function.Commute f g →     Function.minimalPeriod (f
 ∘ g) x ∣ (Function.minimalPeriod f …
· 使用引理 `Commute.function_commute_mul_left`：Commute.function_commute_mul_left (h 
: Commute a b) : Function.Commute (a * ·) (b * ·)
-/
theorem orderOf_mul_dvd_lcm (h : Commute x y) :
    orderOf (x * y) ∣ Nat.lcm (orderOf x) (orderOf y) := by
  rw [orderOf, ← comp_mul_left]
  exact Function.Commute.minimalPeriod_of_comp_dvd_lcm h.function_commute_mul_left

@[to_additive]
/-
**Commute.orderOf_dvd_lcm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：orderOf_dvd_lcm_mul (h : Commute x y) : orderOf y ∣ Nat.lcm (orderOf x) (o
rderOf (x * y))
参数：h : Commute x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lcm_zero_left`：∀ (m : ℕ), Nat.lcm 0 m = 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Commute.orderOf_mul_dvd_lcm`：orderOf_mul_dvd_lcm (h : Commute x y) : ord
erOf (x * y) ∣ Nat.lcm (orderOf x) (orderOf y)
· 使用定理 `Commute.pow_left`：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n)
 b
· 使用定理 `Commute.mul_right`：mul_right (hab : Commute a b) (hac : Commute a c) : C
ommute a (b * c)
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lcm_dvd_iff`：∀ {m n k : ℕ}, m.lcm n ∣ k ↔ m ∣ k ∧ n ∣ k
· 使用定理 `orderOf_pow_dvd`：orderOf_pow_dvd (n : Nat) : orderOf (x ^ n) ∣ orderOf x
· 使用定理 `Nat.dvd_lcm_left`：∀ (m n : ℕ), m ∣ m.lcm n
· 使用定理 `Nat.dvd_lcm_right`：∀ (m n : ℕ), n ∣ m.lcm n
-/
theorem orderOf_dvd_lcm_mul (h : Commute x y) :
    orderOf y ∣ Nat.lcm (orderOf x) (orderOf (x * y)) := by
  by_cases h0 : orderOf x = 0
  · rw [h0, lcm_zero_left]
    apply dvd_zero
  conv_lhs =>
    rw [← one_mul y, ← pow_orderOf_eq_one x, ← succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0),
      _root_.pow_succ, mul_assoc]
  exact
    (((Commute.refl x).mul_right h).pow_left _).orderOf_mul_dvd_lcm.trans
      (Nat.lcm_dvd_iff.2 ⟨(orderOf_pow_dvd _).trans (Nat.dvd_lcm_left _ _), Nat.dvd_lcm_right _ _⟩)

@[to_additive addOrderOf_add_dvd_mul_addOrderOf]
/-
**Commute.orderOf_mul_dvd_mul_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：orderOf_mul_dvd_mul_orderOf (h : Commute x y) : orderOf (x * y) ∣ orderOf 
x * orderOf y
参数：h : Commute x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Commute.orderOf_mul_dvd_lcm`：orderOf_mul_dvd_lcm (h : Commute x y) : ord
erOf (x * y) ∣ Nat.lcm (orderOf x) (orderOf y)
· 使用定理 `Nat.lcm_dvd_mul`：∀ (m n : ℕ), m.lcm n ∣ m * n
-/
theorem orderOf_mul_dvd_mul_orderOf (h : Commute x y) :
    orderOf (x * y) ∣ orderOf x * orderOf y :=
  dvd_trans h.orderOf_mul_dvd_lcm (Nat.lcm_dvd_mul _ _)

@[to_additive addOrderOf_add_eq_mul_addOrderOf_of_coprime]
/-
**Commute.orderOf_mul_eq_mul_orderOf_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Commu
te`。
形式化陈述：orderOf_mul_eq_mul_orderOf_of_coprime (h : Commute x y) (hco : (orderOf x)
.Coprime (orderOf y)) : orderOf (x * y) = orderOf x * orderOf y
参数：h : Commute x y；hco : (orderOf x).Coprime (orderOf y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf.eq_1`：∀ {G : Type u_1} [inst : Monoid G] (x : G), orderOf x = Fu
nction.minimalPeriod (fun x_1 => x * x_1) 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comp_mul_left`：comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·)
· 使用定理 `Function.Commute.minimalPeriod_of_comp_eq_mul_of_coprime`：∀ {α : Type u_
1} {f : α → α} {x : α} {g : α → α},   Function.Commute f g →     (Function.minim
alPeriod f x).Coprime (Function.minimalPeriod …
· 使用引理 `Commute.function_commute_mul_left`：Commute.function_commute_mul_left (h 
: Commute a b) : Function.Commute (a * ·) (b * ·)
-/
theorem orderOf_mul_eq_mul_orderOf_of_coprime (h : Commute x y)
    (hco : (orderOf x).Coprime (orderOf y)) : orderOf (x * y) = orderOf x * orderOf y := by
  rw [orderOf, ← comp_mul_left]
  exact h.function_commute_mul_left.minimalPeriod_of_comp_eq_mul_of_coprime hco

/-- Commuting elements of finite order are closed under multiplication. -/
@[to_additive /-- Commuting elements of finite additive order are closed under addition. -/]
/-
**Commute.isOfFinOrder_mul** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：isOfFinOrder_mul (h : Commute x y) (hx : IsOfFinOrder x) (hy : IsOfFinOrde
r y) : IsOfFinOrder (x * y)
参数：h : Commute x y；hx : IsOfFinOrder x；hy : IsOfFinOrder y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orderOf_pos_iff`：orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x
· 使用定理 `Nat.pos_of_dvd_of_pos`：∀ {m n : ℕ}, m ∣ n → 0 < n → 0 < m
· 使用定理 `Commute.orderOf_mul_dvd_mul_orderOf`：orderOf_mul_dvd_mul_orderOf (h : Co
mmute x y) : orderOf (x * y) ∣ orderOf x * orderOf y
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x

--- 原说明 ---
Commuting elements of finite order are closed under multiplication.
-/
theorem isOfFinOrder_mul (h : Commute x y) (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) :
    IsOfFinOrder (x * y) :=
  orderOf_pos_iff.mp <|
    pos_of_dvd_of_pos h.orderOf_mul_dvd_mul_orderOf <| mul_pos hx.orderOf_pos hy.orderOf_pos

/-- If each prime factor of `orderOf x` has higher multiplicity in `orderOf y`, and `x` commutes
  with `y`, then `x * y` has the same order as `y`. -/
@[to_additive addOrderOf_add_eq_right_of_forall_prime_mul_dvd
  /-- If each prime factor of
  `addOrderOf x` has higher multiplicity in `addOrderOf y`, and `x` commutes with `y`,
  then `x + y` has the same order as `y`. -/]
/-
**Commute.orderOf_mul_eq_right_of_forall_prime_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间
 `Commute`。
形式化陈述：orderOf_mul_eq_right_of_forall_prime_mul_dvd (h : Commute x y) (hy : IsOfF
inOrder y) (hdvd : forall p : Nat, p.Prime -> p ∣ orderOf x -> p * orderOf x ∣ o
rderOf y) : orderOf (x * y) = orderOf y
参数：h : Commute x y；hy : IsOfFinOrder y；hdvd : forall p : Nat, p.Prime -> p ∣ ord
erOf x -> p * orderOf x ∣ orderOf y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用定理 `Nat.dvd_of_forall_prime_mul_dvd`：dvd_of_forall_prime_mul_dvd {a b : Nat}
 (hdvd : forall p : Nat, p.Prime -> p ∣ a -> p * a ∣ b) : a ∣ b
· 使用定理 `orderOf_eq_of_pow_and_pow_div_prime`：orderOf_eq_of_pow_and_pow_div_prime
 (hn : 0 < n) (hx : x ^ n = 1) (hd : forall p : Nat, p.Prime -> p ∣ n -> x ^ (n 
/ p) != 1) : orderOf x = …
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Commute.orderOf_mul_dvd_lcm`：orderOf_mul_dvd_lcm (h : Commute x y) : ord
erOf (x * y) ∣ Nat.lcm (orderOf x) (orderOf y)
· 使用定理 `Nat.lcm_dvd`：∀ {m n k : ℕ}, m ∣ k → n ∣ k → m.lcm n ∣ k
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `mul_dvd_mul_iff_right`：mul_dvd_mul_iff_right [CommMonoidWithZero α] [IsC
ancelMulZero α] {a b c : α} (hc : c != 0) : a * c ∣ b * c ↔ a ∣ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.dvd_div_iff_mul_dvd`：∀ {a b c : ℕ}, c ∣ b → (a ∣ b / c ↔ c * a ∣ b)
· 使用定理 `Commute.orderOf_dvd_lcm_mul`：orderOf_dvd_lcm_mul (h : Commute x y) : ord
erOf y ∣ Nat.lcm (orderOf x) (orderOf (x * y))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Coprime.mul_dvd_of_dvd_of_dvd`：∀ {m n a : ℕ}, m.Coprime n → m ∣ a → 
n ∣ a → m * n ∣ a
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
-/
theorem orderOf_mul_eq_right_of_forall_prime_mul_dvd (h : Commute x y) (hy : IsOfFinOrder y)
    (hdvd : ∀ p : ℕ, p.Prime → p ∣ orderOf x → p * orderOf x ∣ orderOf y) :
    orderOf (x * y) = orderOf y := by
  have hoy := hy.orderOf_pos
  have hxy := dvd_of_forall_prime_mul_dvd hdvd
  apply orderOf_eq_of_pow_and_pow_div_prime hoy <;> simp only [Ne, ← orderOf_dvd_iff_pow_eq_one]
  · exact h.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd hxy dvd_rfl)
  refine fun p hp hpy hd => hp.ne_one ?_
  rw [← Nat.dvd_one, ← mul_dvd_mul_iff_right hoy.ne', one_mul, ← dvd_div_iff_mul_dvd hpy]
  refine (orderOf_dvd_lcm_mul h).trans (Nat.lcm_dvd ((dvd_div_iff_mul_dvd hpy).2 ?_) hd)
  by_cases h : p ∣ orderOf x
  exacts [hdvd p hp h, (hp.coprime_iff_not_dvd.2 h).mul_dvd_of_dvd_of_dvd hpy hxy]

/-- If each prime factor of `orderOf y` has higher multiplicity in `orderOf x`, and `x` commutes
  with `y`, then `x * y` has the same order as `x`. -/
@[to_additive addOrderOf_add_eq_left_of_forall_prime_mul_dvd
  /-- If each prime factor of
  `addOrderOf y` has higher multiplicity in `addOrderOf x`, and `x` commutes with `y`,
  then `x + y` has the same order as `x`. -/]
/-
**Commute.orderOf_mul_eq_left_of_forall_prime_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 
`Commute`。
形式化陈述：orderOf_mul_eq_left_of_forall_prime_mul_dvd (h : Commute x y) (hx : IsOfFi
nOrder x) (hdvd : forall p : Nat, p.Prime -> p ∣ orderOf y -> p * orderOf y ∣ or
derOf x) : orderOf (x * y) = orderOf x
参数：h : Commute x y；hx : IsOfFinOrder x；hdvd : forall p : Nat, p.Prime -> p ∣ ord
erOf y -> p * orderOf y ∣ orderOf x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.orderOf_mul_eq_right_of_forall_prime_mul_dvd`：orderOf_mul_eq_rig
ht_of_forall_prime_mul_dvd (h : Commute x y) (hy : IsOfFinOrder y) (hdvd : foral
l p : Nat, p.Prime -> p ∣ orderOf x -> p *…
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
-/
theorem orderOf_mul_eq_left_of_forall_prime_mul_dvd (h : Commute x y) (hx : IsOfFinOrder x)
    (hdvd : ∀ p : ℕ, p.Prime → p ∣ orderOf y → p * orderOf y ∣ orderOf x) :
    orderOf (x * y) = orderOf x := by
  simpa [h.eq] using
    orderOf_mul_eq_right_of_forall_prime_mul_dvd (x := y) (y := x) h.symm hx hdvd

end Commute

section PPrime
variable {x n} {p : ℕ} [hp : Fact p.Prime]

@[to_additive]
/-
**orderOf_eq_prime_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_prime_iff : orderOf x = p ↔ x ^ p = 1 ∧ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf.eq_1`：∀ {G : Type u_1} [inst : Monoid G] (x : G), orderOf x = Fu
nction.minimalPeriod (fun x_1 => x * x_1) 1
· 使用定理 `Function.minimalPeriod_eq_prime_iff`：minimalPeriod_eq_prime_iff {p : Nat
} [hp : Fact p.Prime] : minimalPeriod f x = p ↔ IsPeriodicPt f p x ∧ ¬IsFixedPt 
f x
· 使用定理 `isPeriodicPt_mul_iff_pow_eq_one`：isPeriodicPt_mul_iff_pow_eq_one (x : G)
 : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
· 使用定理 `Function.IsFixedPt.eq_1`：∀ {α : Type u₁} (f : α → α) (x : α), Function.I
sFixedPt f x = (f x = x)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem orderOf_eq_prime_iff : orderOf x = p ↔ x ^ p = 1 ∧ x ≠ 1 := by
  rw [orderOf, minimalPeriod_eq_prime_iff, isPeriodicPt_mul_iff_pow_eq_one, IsFixedPt, mul_one]

/-- The backward direction of `orderOf_eq_prime_iff`. -/
@[to_additive /-- The backward direction of `addOrderOf_eq_prime_iff`. -/]
/-
**orderOf_eq_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_prime (hg : x ^ p = 1) (hg1 : x != 1) : orderOf x = p
参数：hg : x ^ p = 1；hg1 : x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `orderOf_eq_prime_iff`：orderOf_eq_prime_iff : orderOf x = p ↔ x ^ p = 1 ∧
 x != 1

--- 原说明 ---
The backward direction of `orderOf_eq_prime_iff`.
-/
theorem orderOf_eq_prime (hg : x ^ p = 1) (hg1 : x ≠ 1) : orderOf x = p :=
  orderOf_eq_prime_iff.mpr ⟨hg, hg1⟩

@[to_additive addOrderOf_eq_prime_pow]
/-
**orderOf_eq_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_eq_prime_pow (hnot : ¬x ^ p ^ n = 1) (hfin : x ^ p ^ (n + 1) = 1) 
: orderOf x = p ^ (n + 1)
参数：hnot : ¬x ^ p ^ n = 1；hfin : x ^ p ^ (n + 1) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_eq_prime_pow`：minimalPeriod_eq_prime_pow {p k : N
at} [hp : Fact p.Prime] (hk : ¬IsPeriodicPt f (p ^ k) x) (hk1 : IsPeriodicPt f (
p ^ (k + 1)) x) : minimal…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPeriodicPt_mul_iff_pow_eq_one`：isPeriodicPt_mul_iff_pow_eq_one (x : G)
 : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
-/
theorem orderOf_eq_prime_pow (hnot : ¬x ^ p ^ n = 1) (hfin : x ^ p ^ (n + 1) = 1) :
    orderOf x = p ^ (n + 1) := by
  apply minimalPeriod_eq_prime_pow <;> rwa [isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive exists_addOrderOf_eq_prime_pow_iff]
/-
**exists_orderOf_eq_prime_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_orderOf_eq_prime_pow_iff : (exists k : Nat, orderOf x = p ^ k) ↔ ex
ists m : Nat, x ^ (p : Nat) ^ m = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
-/
theorem exists_orderOf_eq_prime_pow_iff :
    (∃ k : ℕ, orderOf x = p ^ k) ↔ ∃ m : ℕ, x ^ (p : ℕ) ^ m = 1 :=
  ⟨fun ⟨k, hk⟩ => ⟨k, by rw [← hk, pow_orderOf_eq_one]⟩, fun ⟨_, hm⟩ => by
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp.elim).mp (orderOf_dvd_of_pow_eq_one hm)
    exact ⟨k, hk⟩⟩

@[simp]
/-
**orderOf_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_neg_one {R} [Ring R] [Nontrivial R] : orderOf (-1 : R) = if ringCh
ar R = 2 then 1 else 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_one_eq_one_iff`：neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ r
ingChar R = 2
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `orderOf_eq_prime`：orderOf_eq_prime (hg : x ^ p = 1) (hg1 : x != 1) : ord
erOf x = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orderOf_neg_one {R} [Ring R] [Nontrivial R] :
    orderOf (-1 : R) = if ringChar R = 2 then 1 else 2 := by
  split_ifs with h
  · rw [neg_one_eq_one_iff.2 h, orderOf_one]
  apply orderOf_eq_prime
  · simp
  simpa [neg_one_eq_one_iff] using h
/-
**CharP.orderOf_eq_two_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CharP.orderOf_eq_two_iff {R} [Ring R] [Nontrivial R] [NoZeroDivisors R] (p
 : Nat) (hp : p != 2) [CharP R p] {x : R} : orderOf x = 2 ↔ x = -1
参数：p : Nat；hp : p != 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_one_eq_one_iff`：neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ r
ingChar R = 2
· 使用引理 `ringChar.eq`：eq (p : Nat) [C : CharP R p] : ringChar R = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma CharP.orderOf_eq_two_iff {R} [Ring R] [Nontrivial R] [NoZeroDivisors R] (p : ℕ)
    (hp : p ≠ 2) [CharP R p] {x : R} : orderOf x = 2 ↔ x = -1 := by
  simp only [orderOf_eq_prime_iff, sq_eq_one_iff, ne_eq, or_and_right, and_not_self, false_or,
    and_iff_left_iff_imp]
  rintro rfl
  exact fun h ↦ hp ((ringChar.eq R p) ▸ (neg_one_eq_one_iff.1 h))

end PPrime

/-- The equivalence between `Fin (orderOf x)` and `Submonoid.powers x`, sending `i` to `x ^ i` -/
@[to_additive /-- The equivalence between `Fin (addOrderOf a)` and
`AddSubmonoid.multiples a`, sending `i` to `i • a` -/]
/-
**finEquivPowers** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finEquivPowers {x : G} (hx : IsOfFinOrder x) : Fin (orderOf x) ≃ powers x
参数：hx : IsOfFinOrder x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def finEquivPowers {x : G} (hx : IsOfFinOrder x) : Fin (orderOf x) ≃ powers x :=
  Equiv.ofBijective (fun n ↦ ⟨x ^ (n : ℕ), ⟨n, rfl⟩⟩) ⟨fun ⟨_, h₁⟩ ⟨_, h₂⟩ ij ↦
    Fin.ext (pow_injOn_Iio_orderOf h₁ h₂ (Subtype.mk_eq_mk.1 ij)), fun ⟨_, i, rfl⟩ ↦
      ⟨⟨i % orderOf x, mod_lt _ hx.orderOf_pos⟩, Subtype.ext <| pow_mod_orderOf _ _⟩⟩

@[to_additive (attr := simp)]
/-
**finEquivPowers_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finEquivPowers_apply {x : G} (hx : IsOfFinOrder x) {n : Fin (orderOf x)} :
 finEquivPowers hx n = ⟨x ^ (n : Nat), n, rfl⟩
参数：hx : IsOfFinOrder x；orderOf x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finEquivPowers_apply {x : G} (hx : IsOfFinOrder x) {n : Fin (orderOf x)} :
    finEquivPowers hx n = ⟨x ^ (n : ℕ), n, rfl⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**finEquivPowers_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finEquivPowers_symm_apply {x : G} (hx : IsOfFinOrder x) (n : Nat) : (finEq
uivPowers hx).symm ⟨x ^ n, _, rfl⟩ = ⟨n % orderOf x, Nat.mod_lt _ hx.orderOf_pos
⟩
参数：hx : IsOfFinOrder x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用引理 `finEquivPowers_apply`：finEquivPowers_apply {x : G} (hx : IsOfFinOrder x)
 {n : Fin (orderOf x)} : finEquivPowers hx n = ⟨x ^ (n : Nat), n, rfl⟩
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
-/
lemma finEquivPowers_symm_apply {x : G} (hx : IsOfFinOrder x) (n : ℕ) :
    (finEquivPowers hx).symm ⟨x ^ n, _, rfl⟩ = ⟨n % orderOf x, Nat.mod_lt _ hx.orderOf_pos⟩ := by
  rw [Equiv.symm_apply_eq, finEquivPowers_apply, Subtype.mk_eq_mk, ← pow_mod_orderOf, Fin.val_mk]

variable {x n} (hx : IsOfFinOrder x)
include hx

@[to_additive]
/-
**IsOfFinOrder.pow_eq_pow_iff_modEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `IsUnit.mul_eq_left`：mul_eq_left (h : IsUnit a) : a * b = a ↔ b = 1
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用引理 `IsOfFinOrder.isUnit`：IsOfFinOrder.isUnit {M} [Monoid M] {x : M} (hx : Is
OfFinOrder x) : IsUnit x
· 使用定理 `pow_eq_one_iff_modEq`：pow_eq_one_iff_modEq : x ^ n = 1 ↔ n ≡ 0 [MOD orde
rOf x]
· 使用定理 `Nat.ModEq.add_left`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c + a ≡ c + b
 [MOD n]
· 使用定理 `Nat.ModEq.add_left_cancel'`：∀ {n a b : ℕ} (c : ℕ), c + a ≡ c + b [MOD n]
 → a ≡ b [MOD n]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.ModEq.comm`：∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ b ≡ a [MOD n]
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsOfFinOrder.pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
  wlog hmn : m ≤ n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, (hx.isUnit.pow _).mul_eq_left, pow_eq_one_iff_modEq]
  exact ⟨fun h ↦ Nat.ModEq.add_left _ h, fun h ↦ Nat.ModEq.add_left_cancel' _ h⟩

@[to_additive]
/-
**IsOfFinOrder.pow_inj_mod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.pow_inj_mod {n m : Nat} : x ^ n = x ^ m ↔ n % orderOf x = m %
 orderOf x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.pow_eq_pow_iff_modEq`：IsOfFinOrder.pow_eq_pow_iff_modEq : x
 ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
-/
lemma IsOfFinOrder.pow_inj_mod {n m : ℕ} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x :=
  hx.pow_eq_pow_iff_modEq

end Monoid

section CancelMonoid
variable [LeftCancelMonoid G] {x y : G} {a : G} {m n : ℕ}

@[to_additive]
/-
**pow_eq_pow_iff_modEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_left_cancel_iff`：mul_left_cancel_iff : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `pow_eq_one_iff_modEq`：pow_eq_one_iff_modEq : x ^ n = 1 ↔ n ≡ 0 [MOD orde
rOf x]
· 使用定理 `Nat.ModEq.add_left`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c + a ≡ c + b
 [MOD n]
· 使用定理 `Nat.ModEq.add_left_cancel'`：∀ {n a b : ℕ} (c : ℕ), c + a ≡ c + b [MOD n]
 → a ≡ b [MOD n]
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.ModEq.comm`：∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ b ≡ a [MOD n]
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
  wlog hmn : m ≤ n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [← mul_one (x ^ m), pow_add, mul_left_cancel_iff, pow_eq_one_iff_modEq]
  exact ⟨fun h => Nat.ModEq.add_left _ h, fun h => Nat.ModEq.add_left_cancel' _ h⟩

@[to_additive (attr := simp)]
/-
**injective_pow_iff_not_isOfFinOrder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：injective_pow_iff_not_isOfFinOrder : Injective (fun n : Nat => x ^ n) ↔ ¬I
sOfFinOrder x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isOfFinOrder_of_injective_pow`：not_isOfFinOrder_of_injective_pow {x 
: G} (h : Injective fun n : Nat => x ^ n) : ¬IsOfFinOrder x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_zero_iff`：∀ {a b : ℕ}, a ≡ b [MOD 0] ↔ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `orderOf_eq_zero_iff`：orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder
 x
· 使用定理 `pow_eq_pow_iff_modEq`：pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD 
orderOf x]
-/
lemma injective_pow_iff_not_isOfFinOrder : Injective (fun n : ℕ ↦ x ^ n) ↔ ¬IsOfFinOrder x := by
  refine ⟨fun h => not_isOfFinOrder_of_injective_pow h, fun h n m hnm => ?_⟩
  rwa [pow_eq_pow_iff_modEq, orderOf_eq_zero_iff.mpr h, modEq_zero_iff] at hnm

@[to_additive]
/-
**pow_inj_mod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_inj_mod {n m : Nat} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_eq_pow_iff_modEq`：pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD 
orderOf x]
-/
lemma pow_inj_mod {n m : ℕ} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x := pow_eq_pow_iff_modEq

@[to_additive]
/-
**pow_inj_iff_of_orderOf_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_inj_iff_of_orderOf_eq_zero (h : orderOf x = 0) {n m : Nat} : x ^ n = x
 ^ m ↔ n = m
参数：h : orderOf x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_eq_pow_iff_modEq`：pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD 
orderOf x]
· 使用定理 `Nat.modEq_zero_iff`：∀ {a b : ℕ}, a ≡ b [MOD 0] ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pow_inj_iff_of_orderOf_eq_zero (h : orderOf x = 0) {n m : ℕ} : x ^ n = x ^ m ↔ n = m := by
  rw [pow_eq_pow_iff_modEq, h, modEq_zero_iff]

@[to_additive]
/-
**infinite_not_isOfFinOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infinite_not_isOfFinOrder {x : G} (h : ¬IsOfFinOrder x) : { y : G | ¬IsOfF
inOrder y }.Infinite
参数：h : ¬IsOfFinOrder x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.not_injOn_infinite_finite_image`：not_injOn_infinite_finite_image {f 
: α -> β} {s : Set α} (h_inf : s.Infinite) (h_fin : (f '' s).Finite) : ¬InjOn f 
s
· 使用定理 `Set.Ioi_infinite`：Ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `injective_pow_iff_not_isOfFinOrder`：injective_pow_iff_not_isOfFinOrder :
 Injective (fun n : Nat => x ^ n) ↔ ¬IsOfFinOrder x
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
-/
theorem infinite_not_isOfFinOrder {x : G} (h : ¬IsOfFinOrder x) :
    { y : G | ¬IsOfFinOrder y }.Infinite := by
  let s := { n | 0 < n }.image fun n : ℕ => x ^ n
  have hs : s ⊆ { y : G | ¬IsOfFinOrder y } := by
    rintro - ⟨n, hn : 0 < n, rfl⟩ (contra : IsOfFinOrder (x ^ n))
    apply h
    rw [isOfFinOrder_iff_pow_eq_one] at contra ⊢
    obtain ⟨m, hm, hm'⟩ := contra
    exact ⟨n * m, mul_pos hn hm, by rwa [pow_mul]⟩
  suffices s.Infinite by exact this.mono hs
  contrapose! h
  have : ¬Injective fun n : ℕ => x ^ n := by
    have := Set.not_injOn_infinite_finite_image (Set.Ioi_infinite 0) h
    contrapose this
    exact Set.injOn_of_injective this
  rwa [injective_pow_iff_not_isOfFinOrder, Classical.not_not] at this

@[to_additive (attr := simp)]
/-
**finite_powers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finite_powers : (powers a : Set G).Finite ↔ IsOfFinOrder a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_lt_map_eq_of_forall_mem`：∀ {α : Type u_2} {β : Type u_
3} [inst : LinearOrder α] {t : Set β} {f : α → β} [Infinite α],   (∀ (a : α), f 
a ∈ t) → t.Finite → ∃ a b, a < …
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_cancel_iff`：mul_left_cancel_iff : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `IsOfFinOrder.finite_powers`：IsOfFinOrder.finite_powers (ha : IsOfFinOrde
r a) : (powers a : Set G).Finite
-/
lemma finite_powers : (powers a : Set G).Finite ↔ IsOfFinOrder a := by
  refine ⟨fun h ↦ ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ ↦ a ^ n)
    (fun n ↦ by simp [mem_powers_iff])
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  rw [← mul_left_cancel_iff (a := a ^ m), ← pow_add, add_tsub_cancel_of_le hmn.le, ha, mul_one]

@[to_additive (attr := simp)]
/-
**infinite_powers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：infinite_powers : (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `finite_powers`：finite_powers : (powers a : Set G).Finite ↔ IsOfFinOrder 
a
-/
lemma infinite_powers : (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a := finite_powers.not

/-- See also `orderOf_eq_card_powers`. -/
@[to_additive /-- See also `addOrder_eq_card_multiples`. -/]
/-
**Nat.card_submonoidPowers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.card_submonoidPowers : Nat.card (powers a) = orderOf a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `infinite_powers`：infinite_powers : (powers a : Set G).Infinite ↔ ¬ IsOfF
inOrder a
· 使用定理 `orderOf_eq_zero`：orderOf_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0

--- 原说明 ---
See also `orderOf_eq_card_powers`.
-/
lemma Nat.card_submonoidPowers : Nat.card (powers a) = orderOf a := by
  by_cases ha : IsOfFinOrder a
  · exact (Nat.card_congr (finEquivPowers ha).symm).trans <| by simp
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha, Nat.card_eq_zero_of_infinite]

end CancelMonoid

section RightCancelMonoid
variable [RightCancelMonoid G] {x y : G} {a : G} {m n : ℕ}

namespace RightCancelMonoid

@[to_additive]
/-
**RightCancelMonoid.pow_eq_pow_iff_modEq** 是 Mathlib 中的一个定理，位于命名空间 `RightCancelM
onoid`。
形式化陈述：pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_right_cancel_iff`：mul_right_cancel_iff : b * a = c * a ↔ b = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.ModEq.add_left`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c + a ≡ c + b
 [MOD n]
· 使用定理 `pow_eq_one_iff_modEq`：pow_eq_one_iff_modEq : x ^ n = 1 ↔ n ≡ 0 [MOD orde
rOf x]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ModEq.add_left_cancel'`：∀ {n a b : ℕ} (c : ℕ), c + a ≡ c + b [MOD n]
 → a ≡ b [MOD n]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.ModEq.comm`：∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ b ≡ a [MOD n]
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
  wlog hmn : m ≤ n generalizing m n
  · rw [eq_comm, Nat.ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  constructor
  · intro h
    have hk : x ^ k = 1 := by
      apply (mul_right_cancel_iff (a := x ^ m)).1
      calc
        x ^ k * x ^ m = x ^ (k + m) := (pow_add _ _ _).symm
        _ = x ^ (m + k) := by simp [Nat.add_comm]
        _ = x ^ m := h
        _ = 1 * x ^ m := by simp
    exact by simpa using Nat.ModEq.add_left m (pow_eq_one_iff_modEq.1 hk)
  · intro h
    have hk : x ^ k = 1 := by
      apply pow_eq_one_iff_modEq.2
      exact Nat.ModEq.add_left_cancel' m (by simpa using h)
    calc
      x ^ (m + k) = x ^ m * x ^ k := by rw [pow_add]
      _ = x ^ m := by simp [hk]

@[to_additive (attr := simp)]
/-
**RightCancelMonoid.injective_pow_iff_not_isOfFinOrder** 是 Mathlib 中的一个引理，位于命名空间
 `RightCancelMonoid`。
形式化陈述：injective_pow_iff_not_isOfFinOrder : Function.Injective (fun n : Nat => x 
^ n) ↔ ¬IsOfFinOrder x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isOfFinOrder_of_injective_pow`：not_isOfFinOrder_of_injective_pow {x 
: G} (h : Injective fun n : Nat => x ^ n) : ¬IsOfFinOrder x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_zero_iff`：∀ {a b : ℕ}, a ≡ b [MOD 0] ↔ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `orderOf_eq_zero_iff`：orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder
 x
· 使用定理 `RightCancelMonoid.pow_eq_pow_iff_modEq`：pow_eq_pow_iff_modEq : x ^ n = x
 ^ m ↔ n ≡ m [MOD orderOf x]
-/
lemma injective_pow_iff_not_isOfFinOrder : Function.Injective (fun n : ℕ ↦ x ^ n) ↔
    ¬IsOfFinOrder x := by
  refine ⟨fun h => not_isOfFinOrder_of_injective_pow h, fun h n m hnm => ?_⟩
  rwa [pow_eq_pow_iff_modEq, orderOf_eq_zero_iff.mpr h, Nat.modEq_zero_iff] at hnm

@[to_additive]
/-
**RightCancelMonoid.pow_inj_mod** 是 Mathlib 中的一个引理，位于命名空间 `RightCancelMonoid`。
形式化陈述：pow_inj_mod {n m : Nat} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightCancelMonoid.pow_eq_pow_iff_modEq`：pow_eq_pow_iff_modEq : x ^ n = x
 ^ m ↔ n ≡ m [MOD orderOf x]
-/
lemma pow_inj_mod {n m : ℕ} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x :=
  pow_eq_pow_iff_modEq

@[to_additive]
/-
**RightCancelMonoid.pow_inj_iff_of_orderOf_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ri
ghtCancelMonoid`。
形式化陈述：pow_inj_iff_of_orderOf_eq_zero (h : orderOf x = 0) {n m : Nat} : x ^ n = x
 ^ m ↔ n = m
参数：h : orderOf x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RightCancelMonoid.pow_eq_pow_iff_modEq`：pow_eq_pow_iff_modEq : x ^ n = x
 ^ m ↔ n ≡ m [MOD orderOf x]
· 使用定理 `Nat.modEq_zero_iff`：∀ {a b : ℕ}, a ≡ b [MOD 0] ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pow_inj_iff_of_orderOf_eq_zero (h : orderOf x = 0) {n m : ℕ} : x ^ n = x ^ m ↔ n = m := by
  rw [pow_eq_pow_iff_modEq, h, Nat.modEq_zero_iff]

@[to_additive]
/-
**RightCancelMonoid.infinite_not_isOfFinOrder** 是 Mathlib 中的一个定理，位于命名空间 `RightCa
ncelMonoid`。
形式化陈述：infinite_not_isOfFinOrder {x : G} (h : ¬IsOfFinOrder x) : { y : G | ¬IsOfF
inOrder y }.Infinite
参数：h : ¬IsOfFinOrder x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.not_injOn_infinite_finite_image`：not_injOn_infinite_finite_image {f 
: α -> β} {s : Set α} (h_inf : s.Infinite) (h_fin : (f '' s).Finite) : ¬InjOn f 
s
· 使用定理 `Set.Ioi_infinite`：Ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `RightCancelMonoid.injective_pow_iff_not_isOfFinOrder`：injective_pow_iff_
not_isOfFinOrder : Function.Injective (fun n : Nat => x ^ n) ↔ ¬IsOfFinOrder x
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
-/
theorem infinite_not_isOfFinOrder {x : G} (h : ¬IsOfFinOrder x) :
    { y : G | ¬IsOfFinOrder y }.Infinite := by
  let s := { n | 0 < n }.image fun n : ℕ => x ^ n
  have hs : s ⊆ { y : G | ¬IsOfFinOrder y } := by
    rintro - ⟨n, hn : 0 < n, rfl⟩ (contra : IsOfFinOrder (x ^ n))
    apply h
    rw [isOfFinOrder_iff_pow_eq_one] at contra ⊢
    obtain ⟨m, hm, hm'⟩ := contra
    exact ⟨n * m, mul_pos hn hm, by rwa [pow_mul]⟩
  suffices s.Infinite by exact this.mono hs
  contrapose! h
  have : ¬Function.Injective fun n : ℕ => x ^ n := by
    have := Set.not_injOn_infinite_finite_image (Set.Ioi_infinite 0) h
    contrapose this
    exact Set.injOn_of_injective this
  rwa [injective_pow_iff_not_isOfFinOrder, Classical.not_not] at this

@[to_additive (attr := simp)]
/-
**RightCancelMonoid.finite_powers** 是 Mathlib 中的一个引理，位于命名空间 `RightCancelMonoid`。
形式化陈述：finite_powers : (powers a : Set G).Finite ↔ IsOfFinOrder a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_lt_map_eq_of_forall_mem`：∀ {α : Type u_2} {β : Type u_
3} [inst : LinearOrder α] {t : Set β} {f : α → β} [Infinite α],   (∀ (a : α), f 
a ∈ t) → t.Finite → ∃ a b, a < …
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_right_cancel_iff`：mul_right_cancel_iff : b * a = c * a ↔ b = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `IsOfFinOrder.finite_powers`：IsOfFinOrder.finite_powers (ha : IsOfFinOrde
r a) : (powers a : Set G).Finite
-/
lemma finite_powers : (powers a : Set G).Finite ↔ IsOfFinOrder a := by
  refine ⟨fun h ↦ ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ ↦ a ^ n)
    (fun n ↦ by simp [mem_powers_iff])
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  apply (mul_right_cancel_iff (a := a ^ m)).1
  calc
    a ^ (n - m) * a ^ m = a ^ (n - m + m) := (pow_add _ _ _).symm
    _ = a ^ n := by simp [tsub_add_cancel_of_le hmn.le]
    _ = a ^ m := ha.symm
    _ = 1 * a ^ m := by simp

@[to_additive (attr := simp)]
/-
**RightCancelMonoid.infinite_powers** 是 Mathlib 中的一个引理，位于命名空间 `RightCancelMonoid
`。
形式化陈述：infinite_powers : (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `RightCancelMonoid.finite_powers`：finite_powers : (powers a : Set G).Fini
te ↔ IsOfFinOrder a
-/
lemma infinite_powers : (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a := finite_powers.not

/-- See also `orderOf_eq_card_powers`. -/
@[to_additive /-- See also `addOrder_eq_card_multiples`. -/]
/-
**RightCancelMonoid.Nat.card_submonoidPowers** 是 Mathlib 中的一个定理，位于命名空间 `RightCan
celMonoid.Nat`。
形式化陈述：∀ {G : Type u_1} [inst : RightCancelMonoid G] {a : G}, Nat.card ↥(Submonoi
d.powers a) = orderOf a
参数：Submonoid.powers a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RightCancelMonoid.infinite_powers`：infinite_powers : (powers a : Set G).
Infinite ↔ ¬ IsOfFinOrder a
· 使用定理 `orderOf_eq_zero`：orderOf_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0

--- 原说明 ---
See also `orderOf_eq_card_powers`.
-/
lemma Nat.card_submonoidPowers : Nat.card (powers a) = orderOf a := by
  by_cases ha : IsOfFinOrder a
  · exact (Nat.card_congr (finEquivPowers ha).symm).trans <| by simp
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha, Nat.card_eq_zero_of_infinite]

end RightCancelMonoid

end RightCancelMonoid

section Group

variable [Group G] {x y : G} {i : ℤ}

/-- Inverses of elements of finite order have finite order. -/
@[to_additive (attr := simp) /-- Inverses of elements of finite additive order
have finite additive order. -/]
/-
**isOfFinOrder_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOfFinOrder_inv_iff {x : G} : IsOfFinOrder x⁻¹ ↔ IsOfFinOrder x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOfFinOrder_inv_iff {x : G} : IsOfFinOrder x⁻¹ ↔ IsOfFinOrder x := by
  simp [isOfFinOrder_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.of_inv, IsOfFinOrder.inv⟩ := isOfFinOrder_inv_iff

@[to_additive]
/-
**orderOf_dvd_iff_zpow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_dvd_iff_zpow_eq_one : (orderOf x : Int) ∣ i ↔ x ^ i = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_eq_one`：inv_eq_one : a⁻¹ = 1 ↔ a = 1
-/
theorem orderOf_dvd_iff_zpow_eq_one : (orderOf x : ℤ) ∣ i ↔ x ^ i = 1 := by
  rcases Int.eq_nat_or_neg i with ⟨i, rfl | rfl⟩
  · rw [Int.natCast_dvd_natCast, orderOf_dvd_iff_pow_eq_one, zpow_natCast]
  · rw [dvd_neg, Int.natCast_dvd_natCast, zpow_neg, inv_eq_one, zpow_natCast,
      orderOf_dvd_iff_pow_eq_one]

@[to_additive (attr := simp)]
/-
**orderOf_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_inv (x : G) : orderOf x⁻¹ = orderOf x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem orderOf_inv (x : G) : orderOf x⁻¹ = orderOf x := by simp [orderOf_eq_orderOf_iff]

@[to_additive]
/-
**orderOf_dvd_sub_iff_zpow_eq_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_dvd_sub_iff_zpow_eq_zpow {a b : Int} : (orderOf x : Int) ∣ a - b ↔
 x ^ a = x ^ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_dvd_iff_zpow_eq_one`：orderOf_dvd_iff_zpow_eq_one : (orderOf x : 
Int) ∣ i ↔ x ^ i = 1
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem orderOf_dvd_sub_iff_zpow_eq_zpow {a b : ℤ} : (orderOf x : ℤ) ∣ a - b ↔ x ^ a = x ^ b := by
  rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, mul_inv_eq_one]

namespace Subgroup
variable {H : Subgroup G}

@[to_additive (attr := norm_cast)]
/-
**Subgroup.orderOf_coe** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：orderOf_coe (a : H) : orderOf (a : G) = orderOf a
参数：a : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma orderOf_coe (a : H) : orderOf (a : G) = orderOf a :=
  orderOf_injective H.subtype Subtype.coe_injective _

@[to_additive (attr := simp)]
/-
**Subgroup.orderOf_mk** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：orderOf_mk (a : G) (ha) : orderOf (⟨a, ha⟩ : H) = orderOf a
参数：a : G；ha。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.orderOf_coe`：orderOf_coe (a : H) : orderOf (a : G) = orderOf a
-/
lemma orderOf_mk (a : G) (ha) : orderOf (⟨a, ha⟩ : H) = orderOf a := (orderOf_coe _).symm

end Subgroup

@[to_additive mod_addOrderOf_zsmul]
/-
**zpow_mod_orderOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_mod_orderOf (x : G) (z : Int) : x ^ (z % (orderOf x : Int)) = x ^ z
参数：x : G；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.emod_add_mul_ediv`：∀ (a b : ℤ), a % b + b * (a / b) = a
-/
lemma zpow_mod_orderOf (x : G) (z : ℤ) : x ^ (z % (orderOf x : ℤ)) = x ^ z :=
  calc
    x ^ (z % (orderOf x : ℤ)) = x ^ (z % orderOf x + orderOf x * (z / orderOf x) : ℤ) := by
        simp [zpow_add, zpow_mul, pow_orderOf_eq_one]
    _ = x ^ z := by rw [Int.emod_add_mul_ediv]

@[to_additive (attr := simp) zsmul_smul_addOrderOf]
/-
**zpow_pow_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpow_pow_orderOf : (x ^ i) ^ orderOf x = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `orderOf_eq_zero`：orderOf_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem zpow_pow_orderOf : (x ^ i) ^ orderOf x = 1 := by
  by_cases h : IsOfFinOrder x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · rw [orderOf_eq_zero h, _root_.pow_zero]

@[to_additive]
/-
**IsOfFinOrder.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.zpow (h : IsOfFinOrder x) {i : Int} : IsOfFinOrder (x ^ i)
参数：h : IsOfFinOrder x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用定理 `zpow_pow_orderOf`：zpow_pow_orderOf : (x ^ i) ^ orderOf x = 1
-/
theorem IsOfFinOrder.zpow (h : IsOfFinOrder x) {i : ℤ} : IsOfFinOrder (x ^ i) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf x, h.orderOf_pos, zpow_pow_orderOf⟩

@[to_additive]
/-
**IsOfFinOrder.of_mem_zpowers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.of_mem_zpowers (h : IsOfFinOrder x) (h' : y in Subgroup.zpowe
rs x) : IsOfFinOrder y
参数：h : IsOfFinOrder x；h' : y in Subgroup.zpowers x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
· 使用定理 `IsOfFinOrder.zpow`：IsOfFinOrder.zpow (h : IsOfFinOrder x) {i : Int} : Is
OfFinOrder (x ^ i)
-/
theorem IsOfFinOrder.of_mem_zpowers (h : IsOfFinOrder x) (h' : y ∈ Subgroup.zpowers x) :
    IsOfFinOrder y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h'
  exact h.zpow

@[to_additive]
/-
**orderOf_dvd_of_mem_zpowers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_dvd_of_mem_zpowers (h : y in Subgroup.zpowers x) : orderOf y ∣ ord
erOf x
参数：h : y in Subgroup.zpowers x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `zpow_pow_orderOf`：zpow_pow_orderOf : (x ^ i) ^ orderOf x = 1
-/
theorem orderOf_dvd_of_mem_zpowers (h : y ∈ Subgroup.zpowers x) : orderOf y ∣ orderOf x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [orderOf_dvd_iff_pow_eq_one]
  exact zpow_pow_orderOf
/-
**smul_eq_self_of_mem_zpowers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_eq_self_of_mem_zpowers {α : Type*} [MulAction G α] (hx : x in Subgrou
p.zpowers y) {a : α} (hs : y • a = a) : x • a = a
参数：hx : x in Subgroup.zpowers y；hs : y • a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α]
 [inst_1 : MulAction α β] (a : α) (x : β),   (MulAction.toPerm a) x = a • x
· 使用定理 `MulAction.toPermHom_apply`：∀ (G : Type u_1) (α : Type u_5) [inst : Group
 G] [inst_1 : MulAction G α] (a : G),   (MulAction.toPermHom G α) a = MulAction.
toPerm a
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
· 使用定理 `Function.IsFixedPt.perm_zpow`：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α
}, Function.IsFixedPt (⇑e) x → ∀ (n : ℤ), Function.IsFixedPt (⇑(e ^ n)) x
-/
theorem smul_eq_self_of_mem_zpowers {α : Type*} [MulAction G α] (hx : x ∈ Subgroup.zpowers y)
    {a : α} (hs : y • a = a) : x • a = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAction.toPerm_apply, ← MulAction.toPermHom_apply, map_zpow _ y k,
    MulAction.toPermHom_apply]
  exact Function.IsFixedPt.perm_zpow (by exact hs) k -- Porting note: help elab'n with `by exact`
/-
**vadd_eq_self_of_mem_zmultiples** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vadd_eq_self_of_mem_zmultiples {G : Type*} [AddGroup G] {x y : G} {α : Typ
e*} [AddAction G α] (hx : x in AddSubgroup.zmultiples y) {a : α} (hs : y +ᵥ a = 
a) : x +ᵥ a = a
参数：hx : x in AddSubgroup.zmultiples y；hs : y +ᵥ a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_eq_self_of_mem_zpowers`：smul_eq_self_of_mem_zpowers {α : Type*} [Mu
lAction G α] (hx : x in Subgroup.zpowers y) {a : α} (hs : y • a = a) : x • a = a
-/
theorem vadd_eq_self_of_mem_zmultiples {G : Type*} [AddGroup G] {x y : G} {α : Type*}
    [AddAction G α] (hx : x ∈ AddSubgroup.zmultiples y) {a : α} (hs : y +ᵥ a = a) : x +ᵥ a = a :=
  @smul_eq_self_of_mem_zpowers (Multiplicative G) _ _ _ α _ hx a hs

attribute [to_additive existing] smul_eq_self_of_mem_zpowers

@[to_additive]
/-
**IsOfFinOrder.mem_powers_iff_mem_zpowers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.mem_powers_iff_mem_zpowers (hx : IsOfFinOrder x) : y in power
s x ↔ y in zpowers x
参数：hx : IsOfFinOrder x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero_iff_pos`：∀ {n : ℕ}, ↑n ≠ 0 ↔ 0 < n
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用引理 `zpow_mod_orderOf`：zpow_mod_orderOf (x : G) (z : Int) : x ^ (z % (orderOf
 x : Int)) = x ^ z
-/
lemma IsOfFinOrder.mem_powers_iff_mem_zpowers (hx : IsOfFinOrder x) :
    y ∈ powers x ↔ y ∈ zpowers x :=
  ⟨fun ⟨n, hn⟩ ↦ ⟨n, by simp_all⟩, fun ⟨i, hi⟩ ↦ ⟨(i % orderOf x).natAbs, by
    dsimp only
    rwa [← zpow_natCast, Int.natAbs_of_nonneg <| Int.emod_nonneg _ <|
      Int.natCast_ne_zero_iff_pos.2 <| hx.orderOf_pos, zpow_mod_orderOf]⟩⟩

@[to_additive]
/-
**IsOfFinOrder.powers_eq_zpowers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.powers_eq_zpowers (hx : IsOfFinOrder x) : (powers x : Set G) 
= zpowers x
参数：hx : IsOfFinOrder x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `IsOfFinOrder.mem_powers_iff_mem_zpowers`：IsOfFinOrder.mem_powers_iff_mem
_zpowers (hx : IsOfFinOrder x) : y in powers x ↔ y in zpowers x
-/
lemma IsOfFinOrder.powers_eq_zpowers (hx : IsOfFinOrder x) : (powers x : Set G) = zpowers x :=
  Set.ext fun _ ↦ hx.mem_powers_iff_mem_zpowers

@[to_additive]
/-
**IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf [DecidableEq G] (hx : IsOfF
inOrder x) : y in zpowers x ↔ y in (Finset.range (orderOf x)).image (x ^ ·)
参数：hx : IsOfFinOrder x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `IsOfFinOrder.mem_powers_iff_mem_zpowers`：IsOfFinOrder.mem_powers_iff_mem
_zpowers (hx : IsOfFinOrder x) : y in powers x ↔ y in zpowers x
· 使用定理 `IsOfFinOrder.mem_powers_iff_mem_range_orderOf`：∀ {G : Type u_1} [inst : 
Monoid G] {x y : G} [inst_1 : DecidableEq G],   IsOfFinOrder x → (y ∈ Submonoid.
powers x ↔ y ∈ Finset.image (fun x_…
-/
lemma IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf [DecidableEq G] (hx : IsOfFinOrder x) :
    y ∈ zpowers x ↔ y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
  hx.mem_powers_iff_mem_zpowers.symm.trans hx.mem_powers_iff_mem_range_orderOf

/-- See `Subgroup.closure_toSubmonoid_of_finite` for a version for finite groups. -/
@[to_additive
/-- See `AddSubgroup.closure_toAddSubmonoid_of_finite` for a version for finite additive groups. -/]
/-
**Subgroup.closure_toSubmonoid_of_isOfFinOrder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.closure_toSubmonoid_of_isOfFinOrder {s : Set G} (hs : forall x in
 s, IsOfFinOrder x) : (closure s).toSubmonoid = Submonoid.closure s
参数：hs : forall x in s, IsOfFinOrder x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.closure_toSubmonoid`：closure_toSubmonoid (S : Set G) : (closure
 S).toSubmonoid = Submonoid.closure (S union S⁻¹)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsOfFinOrder.mem_powers_iff_mem_zpowers`：IsOfFinOrder.mem_powers_iff_mem
_zpowers (hx : IsOfFinOrder x) : y in powers x ↔ y in zpowers x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.zpowers_inv`：zpowers_inv : zpowers g⁻¹ = zpowers g
· 使用定理 `Subgroup.le_closure_toSubmonoid`：le_closure_toSubmonoid (S : Set G) : Su
bmonoid.closure S <= (closure S).toSubmonoid
-/
lemma Subgroup.closure_toSubmonoid_of_isOfFinOrder {s : Set G} (hs : ∀ x ∈ s, IsOfFinOrder x) :
    (closure s).toSubmonoid = Submonoid.closure s := by
  refine le_antisymm ?_ (le_closure_toSubmonoid s)
  rw [closure_toSubmonoid]
  refine Submonoid.closure_le.mpr <| Set.union_subset Submonoid.subset_closure
    fun x (hx : x⁻¹ ∈ s) ↦ ?_
  apply Submonoid.powers_le.mpr (Submonoid.subset_closure hx)
  simp [(hs _ hx).mem_powers_iff_mem_zpowers]

/-- The equivalence between `Fin (orderOf x)` and `Subgroup.zpowers x`, sending `i` to `x ^ i`. -/
@[to_additive /-- The equivalence between `Fin (addOrderOf a)` and
`Subgroup.zmultiples a`, sending `i` to `i • a`. -/]
/-
**finEquivZPowers** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finEquivZPowers (hx : IsOfFinOrder x) : Fin (orderOf x) ≃ zpowers x
参数：hx : IsOfFinOrder x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `IsOfFinOrder.powers_eq_zpowers`：IsOfFinOrder.powers_eq_zpowers (hx : IsO
fFinOrder x) : (powers x : Set G) = zpowers x
-/
noncomputable def finEquivZPowers (hx : IsOfFinOrder x) :
    Fin (orderOf x) ≃ zpowers x :=
  (finEquivPowers hx).trans <| Equiv.setCongr hx.powers_eq_zpowers

@[to_additive]
/-
**finEquivZPowers_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finEquivZPowers_apply (hx : IsOfFinOrder x) {n : Fin (orderOf x)} : finEqu
ivZPowers hx n = ⟨x ^ (n : Nat), n, zpow_natCast x n⟩
参数：hx : IsOfFinOrder x；orderOf x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finEquivZPowers_apply (hx : IsOfFinOrder x) {n : Fin (orderOf x)} :
    finEquivZPowers hx n = ⟨x ^ (n : ℕ), n, zpow_natCast x n⟩ := rfl

@[to_additive]
/-
**finEquivZPowers_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finEquivZPowers_symm_apply (hx : IsOfFinOrder x) (n : Nat) : (finEquivZPow
ers hx).symm ⟨x ^ n, ⟨n, by simp⟩⟩ = ⟨n % orderOf x, Nat.mod_lt _ hx.orderOf_pos
⟩
参数：hx : IsOfFinOrder x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `IsOfFinOrder.powers_eq_zpowers`：IsOfFinOrder.powers_eq_zpowers (hx : IsO
fFinOrder x) : (powers x : Set G) = zpowers x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finEquivZPowers.eq_1`：∀ {G : Type u_1} [inst : Group G] {x : G} (hx : Is
OfFinOrder x),   finEquivZPowers hx = (finEquivPowers hx).trans (Equiv.setCongr 
⋯)
· 使用定理 `Equiv.symm_trans_apply`：symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ)
 : (f.trans g).symm a = f.symm (g.symm a)
· 使用引理 `finEquivPowers_symm_apply`：finEquivPowers_symm_apply {x : G} (hx : IsOfF
inOrder x) (n : Nat) : (finEquivPowers hx).symm ⟨x ^ n, _, rfl⟩ = ⟨n % orderOf x
, Nat.mod_lt _ …
-/
lemma finEquivZPowers_symm_apply (hx : IsOfFinOrder x) (n : ℕ) :
    (finEquivZPowers hx).symm ⟨x ^ n, ⟨n, by simp⟩⟩ =
    ⟨n % orderOf x, Nat.mod_lt _ hx.orderOf_pos⟩ := by
  rw [finEquivZPowers, Equiv.symm_trans_apply]; exact finEquivPowers_symm_apply _ n

@[to_additive]
/-
**pow_finEquivZPowers_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_finEquivZPowers_symm_apply (hx : IsOfFinOrder x) (a : Subgroup.zpowers
 x) : x ^ ((finEquivZPowers hx).symm a : Nat) = a
参数：hx : IsOfFinOrder x；a : Subgroup.zpowers x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma pow_finEquivZPowers_symm_apply (hx : IsOfFinOrder x) (a : Subgroup.zpowers x) :
    x ^ ((finEquivZPowers hx).symm a : ℕ) = a := by
  simpa only [finEquivZPowers_apply] using
    congr_arg Subtype.val ((finEquivZPowers hx).apply_symm_apply a)

end Group

section CommMonoid

variable [CommMonoid G] {x y : G}

/-- Elements of finite order are closed under multiplication. -/
@[to_additive /-- Elements of finite additive order are closed under addition. -/]
/-
**IsOfFinOrder.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.mul (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) : IsOfFinOrde
r (x * y)
参数：hx : IsOfFinOrder x；hy : IsOfFinOrder y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.isOfFinOrder_mul`：isOfFinOrder_mul (h : Commute x y) (hx : IsOfF
inOrder x) (hy : IsOfFinOrder y) : IsOfFinOrder (x * y)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
Elements of finite order are closed under multiplication.
-/
theorem IsOfFinOrder.mul (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) : IsOfFinOrder (x * y) :=
  (Commute.all x y).isOfFinOrder_mul hx hy

end CommMonoid

section CommGroup
variable [CommGroup G]

@[to_additive]
/-
**isMulTorsionFree_iff_not_isOfFinOrder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMulTorsionFree_iff_not_isOfFinOrder : IsMulTorsionFree G ↔ forall ⦃a : G
⦄, a != 1 -> ¬ IsOfFinOrder a where mp _ _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_isOfFinOrder_of_isMulTorsionFree`：not_isOfFinOrder_of_isMulTorsionFr
ee [IsMulTorsionFree G] (ha : a != 1) : ¬ IsOfFinOrder a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_one`：div_eq_one : a / b = 1 ↔ a = b
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma isMulTorsionFree_iff_not_isOfFinOrder :
    IsMulTorsionFree G ↔ ∀ ⦃a : G⦄, a ≠ 1 → ¬ IsOfFinOrder a where
  mp _ _ := not_isOfFinOrder_of_isMulTorsionFree
  mpr hG := by
    refine ⟨fun n hn a b hab ↦ ?_⟩
    rw [← div_eq_one] at hab ⊢
    simp only [← div_pow, isOfFinOrder_iff_pow_eq_one] at hab hG
    exact of_not_not fun hab' ↦ hG hab' ⟨n, hn.bot_lt, hab⟩

@[to_additive]
alias ⟨_, IsMulTorsionFree.of_not_isOfFinOrder⟩ := isMulTorsionFree_iff_not_isOfFinOrder

@[to_additive]
/-
**not_isMulTorsionFree_iff_isOfFinOrder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_isMulTorsionFree_iff_isOfFinOrder : ¬ IsMulTorsionFree G ↔ exists a !=
 (1 : G), IsOfFinOrder a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma not_isMulTorsionFree_iff_isOfFinOrder :
    ¬ IsMulTorsionFree G ↔ ∃ a ≠ (1 : G), IsOfFinOrder a := by
  simp [isMulTorsionFree_iff_not_isOfFinOrder]

@[to_additive (attr := simp)]
/-
**zpowers_mabs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpowers_mabs [LinearOrder G] [IsOrderedMonoid G] (g : G) : zpowers |g|ₘ = 
zpowers g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_cases`：mabs_cases (a : G) : |a|ₘ = a ∧ 1 <= a ∨ |a|ₘ = a⁻¹ ∧ a < 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subgroup.zpowers_inv`：zpowers_inv : zpowers g⁻¹ = zpowers g
-/
lemma zpowers_mabs [LinearOrder G] [IsOrderedMonoid G] (g : G) : zpowers |g|ₘ = zpowers g := by
  rcases mabs_cases g with h | h <;> simp only [h, zpowers_inv]

@[to_additive]
/-
**IsMulTorsionFree.orderOf_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulTorsionFree.orderOf_le_one [IsMulTorsionFree G] (g : G) : orderOf g <
= 1
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_eq_zero_iff`：orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder
 x
· 使用引理 `isOfFinOrder_iff_eq_one`：isOfFinOrder_iff_eq_one [IsMulTorsionFree G] (a
 : G) : IsOfFinOrder a ↔ a = 1
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma IsMulTorsionFree.orderOf_le_one [IsMulTorsionFree G] (g : G) :
    orderOf g ≤ 1 := by
  obtain rfl | ha := eq_or_ne g 1
  · simp
  · rw [ne_eq, ← isOfFinOrder_iff_eq_one, ← orderOf_eq_zero_iff] at ha
    simp [ha]

end CommGroup

section FiniteMonoid

variable [Monoid G] {x : G} {n : ℕ}

@[to_additive]
/-
**sum_card_orderOf_eq_card_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_card_orderOf_eq_card_pow_eq_one [Fintype G] [DecidableEq G] (hn : n !=
 0) : ∑ m in divisors n, #{x : G | orderOf x = m} = #{x : G | x ^ n = 1}
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sum_card_orderOf_eq_card_pow_eq_one [Fintype G] [DecidableEq G] (hn : n ≠ 0) :
    ∑ m ∈ divisors n, #{x : G | orderOf x = m} = #{x : G | x ^ n = 1} := by
  refine (Finset.card_biUnion ?_).symm.trans ?_
  · simp +contextual [Set.PairwiseDisjoint, Set.Pairwise, disjoint_iff, Finset.ext_iff]
  · congr; ext; simp [hn, orderOf_dvd_iff_pow_eq_one]

@[to_additive]
/-
**orderOf_le_card_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_le_card_univ [Fintype G] : orderOf x <= Fintype.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.le_card_of_inj_on_range`：le_card_of_inj_on_range (f : Nat -> α) (
hf : forall i < n, f i in s) (f_inj : forall i < n, forall j < n, f i = f j -> i
 = j) : n <= #s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `pow_injOn_Iio_orderOf`：pow_injOn_Iio_orderOf : (Set.Iio <| orderOf x).In
jOn (x ^ ·)
-/
theorem orderOf_le_card_univ [Fintype G] : orderOf x ≤ Fintype.card G :=
  Finset.le_card_of_inj_on_range (x ^ ·) (fun _ _ ↦ Finset.mem_univ _) pow_injOn_Iio_orderOf

@[to_additive]
/-
**orderOf_le_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_le_card [Finite G] : orderOf x <= Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `orderOf_le_card_univ`：orderOf_le_card_univ [Fintype G] : orderOf x <= Fi
ntype.card G
-/
theorem orderOf_le_card [Finite G] : orderOf x ≤ Nat.card G := by
  obtain ⟨⟩ := nonempty_fintype G
  simpa using orderOf_le_card_univ

end FiniteMonoid

section FiniteCancelMonoid
variable [LeftCancelMonoid G]

section Finite
variable [Finite G] {x y : G} {n : ℕ}

@[to_additive]
/-
**isOfFinOrder_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
参数：x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `infinite_not_isOfFinOrder`：infinite_not_isOfFinOrder {x : G} (h : ¬IsOfF
inOrder x) : { y : G | ¬IsOfFinOrder y }.Infinite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
lemma isOfFinOrder_of_finite (x : G) : IsOfFinOrder x := by
  by_contra h; exact infinite_not_isOfFinOrder h <| Set.toFinite _

/-- Every finite left cancellative monoid is a group. -/
@[to_additive (attr := instance_reducible)
  /-- Every finite left cancellative additive monoid is an additive group. -/]
/-
**LeftCancelMonoid.groupOfFinite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LeftCancelMonoid.groupOfFinite : Group G where inv x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def LeftCancelMonoid.groupOfFinite : Group G where
  inv x := x ^ (orderOf x - 1)
  inv_mul_cancel x := by
    rw [← pow_succ, tsub_add_cancel_of_le, pow_orderOf_eq_one]
    exact (isOfFinOrder_of_finite x).orderOf_pos

/-- Every finite right cancellative monoid is a group. -/
@[to_additive (attr := instance_reducible)
  /-- Every finite right cancellative additive monoid is an additive group. -/]
/-
**RightCancelMonoid.groupOfFinite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RightCancelMonoid.groupOfFinite {H : Type*} [RightCancelMonoid H] [Finite 
H] : Group H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def RightCancelMonoid.groupOfFinite {H : Type*} [RightCancelMonoid H] [Finite H] :
    Group H := by
  letI : Finite Hᵐᵒᵖ := Finite.of_equiv H MulOpposite.opEquiv
  letI : Group Hᵐᵒᵖ := LeftCancelMonoid.groupOfFinite (G := Hᵐᵒᵖ)
  exact (MulEquiv.opOp H).toEquiv.group

/-- This is the same as `IsOfFinOrder.orderOf_pos` but with one fewer explicit assumption since this
is automatic in case of a finite cancellative monoid. -/
@[to_additive /-- This is the same as `IsOfFinAddOrder.addOrderOf_pos` but with one fewer explicit
assumption since this is automatic in case of a finite cancellative additive monoid. -/]
/-
**orderOf_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_pos (x : G) : 0 < orderOf x
参数：x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
-/
lemma orderOf_pos (x : G) : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos

/-- This is the same as `orderOf_pow'` and `orderOf_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid. -/
@[to_additive /-- This is the same as `addOrderOf_nsmul'` and
`addOrderOf_nsmul` but with one assumption less which is automatic in the case of a
finite cancellative additive monoid. -/]
/-
**orderOf_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_pow (x : G) : orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf x) n
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.orderOf_pow`：∀ {G : Type u_1} [inst : Monoid G] (x : G) (n 
: ℕ), IsOfFinOrder x → orderOf (x ^ n) = orderOf x / (orderOf x).gcd n
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
-/
theorem orderOf_pow (x : G) : orderOf (x ^ n) = orderOf x / Nat.gcd (orderOf x) n :=
  (isOfFinOrder_of_finite _).orderOf_pow ..

@[to_additive]
/-
**mem_powers_iff_mem_range_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_powers_iff_mem_range_orderOf [DecidableEq G] : y in powers x ↔ y in (F
inset.range (orderOf x)).image (x ^ ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_range_iff_mem_finset_range_of_mod_eq'`：mem_range_iff_mem_fins
et_range_of_mod_eq' [DecidableEq α] {f : Nat -> α} {a : α} {n : Nat} (hn : 0 < n
) (h : forall i, f (i % n) = f i) : a …
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
-/
theorem mem_powers_iff_mem_range_orderOf [DecidableEq G] :
    y ∈ powers x ↔ y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
  Finset.mem_range_iff_mem_finset_range_of_mod_eq' (orderOf_pos x) <| pow_mod_orderOf _

/-- The equivalence between `Submonoid.powers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive
  /-- The equivalence between `Submonoid.multiples` of two elements `a, b` of the same additive
  order, mapping `i • a` to `i • b`. -/]
/-
**powersEquivPowers** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：powersEquivPowers (h : orderOf x = orderOf y) : powers x ≃ powers y
参数：h : orderOf x = orderOf y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
-/
noncomputable def powersEquivPowers (h : orderOf x = orderOf y) : powers x ≃ powers y :=
  (finEquivPowers <| isOfFinOrder_of_finite _).symm.trans <|
    (finCongr h).trans <| finEquivPowers <| isOfFinOrder_of_finite _

@[to_additive (attr := simp)]
/-
**powersEquivPowers_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：powersEquivPowers_apply (h : orderOf x = orderOf y) (n : Nat) : powersEqui
vPowers h ⟨x ^ n, n, rfl⟩ = ⟨y ^ n, n, rfl⟩
参数：h : orderOf x = orderOf y；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `powersEquivPowers.eq_1`：∀ {G : Type u_1} [inst : LeftCancelMonoid G] [in
st_1 : Finite G] {x y : G} (h : orderOf x = orderOf y),   powersEquivPowers h = 
(finEquivPow…
· 使用定理 `Equiv.trans_apply`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) 
(g : β ≃ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用引理 `finEquivPowers_symm_apply`：finEquivPowers_symm_apply {x : G} (hx : IsOfF
inOrder x) (n : Nat) : (finEquivPowers hx).symm ⟨x ^ n, _, rfl⟩ = ⟨n % orderOf x
, Nat.mod_lt _ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powersEquivPowers_apply (h : orderOf x = orderOf y) (n : ℕ) :
    powersEquivPowers h ⟨x ^ n, n, rfl⟩ = ⟨y ^ n, n, rfl⟩ := by
  rw [powersEquivPowers, Equiv.trans_apply, Equiv.trans_apply, finEquivPowers_symm_apply, ←
    Equiv.eq_symm_apply, finEquivPowers_symm_apply]
  simp [h]

end Finite

variable [Fintype G] {x : G}

@[to_additive]
/-
**orderOf_eq_card_powers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_eq_card_powers : orderOf x = Fintype.card (powers x : Submonoid G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma orderOf_eq_card_powers : orderOf x = Fintype.card (powers x : Submonoid G) :=
  (Fintype.card_fin (orderOf x)).symm.trans <|
    Fintype.card_eq.2 ⟨finEquivPowers <| isOfFinOrder_of_finite _⟩

end FiniteCancelMonoid

/-
**isOfFinOrder_iff_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOfFinOrder_iff_isUnit [Monoid G] [Finite Gˣ] {x : G} : IsOfFinOrder x ↔ 
IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOfFinOrder.isUnit`：IsOfFinOrder.isUnit {M} [Monoid M] {x : M} (hx : Is
OfFinOrder x) : IsUnit x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.isOfFinOrder_val`：Units.isOfFinOrder_val {u : Gˣ} : IsOfFinOrder (
u : G) ↔ IsOfFinOrder u
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
-/
lemma isOfFinOrder_iff_isUnit [Monoid G] [Finite Gˣ] {x : G} : IsOfFinOrder x ↔ IsUnit x := by
  use IsOfFinOrder.isUnit
  rintro ⟨u, rfl⟩
  rw [Units.isOfFinOrder_val]
  apply isOfFinOrder_of_finite

alias ⟨_, IsUnit.isOfFinOrder⟩ := isOfFinOrder_iff_isUnit
/-
**orderOf_eq_zero_iff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_eq_zero_iff_eq_zero {G₀ : Type*} [GroupWithZero G₀] [Finite G₀] {a
 : G₀} : orderOf a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma orderOf_eq_zero_iff_eq_zero {G₀ : Type*} [GroupWithZero G₀] [Finite G₀] {a : G₀} :
    orderOf a = 0 ↔ a = 0 := by
  -- Prove an instance inline to avoid extra imports.
  -- TODO: move this instance elsewhere?
  have : Finite G₀ˣ := .of_injective _ Units.val_injective
  simp [isOfFinOrder_iff_isUnit]

section FiniteGroup
variable [Group G] {x y : G}

@[to_additive]
/-
**zpow_eq_one_iff_modEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpow_eq_one_iff_modEq {n : Int} : x ^ n = 1 ↔ n ≡ 0 [ZMOD orderOf x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a
· 使用定理 `orderOf_dvd_iff_zpow_eq_one`：orderOf_dvd_iff_zpow_eq_one : (orderOf x : 
Int) ∣ i ↔ x ^ i = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zpow_eq_one_iff_modEq {n : ℤ} : x ^ n = 1 ↔ n ≡ 0 [ZMOD orderOf x] := by
  rw [Int.modEq_zero_iff_dvd, orderOf_dvd_iff_zpow_eq_one]


@[to_additive]
/-
**zpow_eq_zpow_iff_modEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpow_eq_zpow_iff_modEq {m n : Int} : x ^ m = x ^ n ↔ m ≡ n [ZMOD orderOf x
]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
· 使用定理 `zpow_eq_one_iff_modEq`：zpow_eq_one_iff_modEq {n : Int} : x ^ n = 1 ↔ n ≡
 0 [ZMOD orderOf x]
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zpow_eq_zpow_iff_modEq {m n : ℤ} : x ^ m = x ^ n ↔ m ≡ n [ZMOD orderOf x] := by
  rw [← mul_inv_eq_one, ← zpow_sub, zpow_eq_one_iff_modEq, Int.modEq_iff_dvd, Int.modEq_iff_dvd,
    zero_sub, neg_sub]

@[to_additive (attr := simp)]
/-
**injective_zpow_iff_not_isOfFinOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_zpow_iff_not_isOfFinOrder : (Injective fun n : Int => x ^ n) ↔ ¬
IsOfFinOrder x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Int.modEq_zero_iff`：modEq_zero_iff : a ≡ b [ZMOD 0] ↔ a = b
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `orderOf_eq_zero_iff`：orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder
 x
· 使用定理 `zpow_eq_zpow_iff_modEq`：zpow_eq_zpow_iff_modEq {m n : Int} : x ^ m = x ^
 n ↔ m ≡ n [ZMOD orderOf x]
-/
theorem injective_zpow_iff_not_isOfFinOrder : (Injective fun n : ℤ => x ^ n) ↔ ¬IsOfFinOrder x := by
  refine ⟨?_, fun h n m hnm => ?_⟩
  · simp_rw [isOfFinOrder_iff_pow_eq_one]
    rintro h ⟨n, hn, hx⟩
    exact Nat.cast_ne_zero.2 hn.ne' (h <| by simpa using hx)
  rwa [zpow_eq_zpow_iff_modEq, orderOf_eq_zero_iff.2 h, Nat.cast_zero, Int.modEq_zero_iff] at hnm

@[to_additive]
/-
**Subgroup.zpowers_eq_zpowers_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.zpowers_eq_zpowers_iff {x y : G} (hx : ¬IsOfFinOrder x) : zpowers
 x = zpowers y ↔ x = y ∨ x⁻¹ = y
参数：hx : ¬IsOfFinOrder x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_zpow_iff_not_isOfFinOrder`：injective_zpow_iff_not_isOfFinOrder
 : (Injective fun n : Int => x ^ n) ↔ ¬IsOfFinOrder x
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用引理 `Int.mul_eq_one_iff_eq_one_or_neg_one`：mul_eq_one_iff_eq_one_or_neg_one :
 u * v = 1 ↔ u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Subgroup.zpowers_inv`：zpowers_inv : zpowers g⁻¹ = zpowers g
-/
lemma Subgroup.zpowers_eq_zpowers_iff {x y : G} (hx : ¬IsOfFinOrder x) :
    zpowers x = zpowers y ↔ x = y ∨ x⁻¹ = y := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl) <;> simp⟩
  have hx_mem : x ∈ zpowers y := by simp [← h]
  have hy_mem : y ∈ zpowers x := by simp [h]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy_mem
  obtain ⟨l, hl⟩ := mem_zpowers_iff.mp hx_mem
  rw [← zpow_mul] at hl
  nth_rewrite 2 [← zpow_one x] at hl
  have h1 := (injective_zpow_iff_not_isOfFinOrder.mpr hx) hl
  rcases (Int.mul_eq_one_iff_eq_one_or_neg_one).mp h1 with (h | h) <;> simp [h.1]

@[to_additive]
/-
**mem_zpowers_zpow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_zpowers_zpow_iff {g : G} {k : Int} : g in Subgroup.zpowers (g ^ k) ↔ k
.gcd (orderOf g) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_zpowers_zpow_iff {g : G} {k : ℤ} :
    g ∈ Subgroup.zpowers (g ^ k) ↔ k.gcd (orderOf g) = 1 := by
  simp_rw [← Nat.dvd_one, Int.gcd_dvd_iff, Nat.cast_one, ← Int.sub_eq_iff_eq_add', ← dvd_def,
    ← Int.modEq_iff_dvd, ← zpow_eq_zpow_iff_modEq, zpow_one, zpow_mul, ← mem_zpowers_iff]

@[to_additive]
/-
**mem_zpowers_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_zpowers_pow_iff {g : G} {k : Nat} : g in Subgroup.zpowers (g ^ k) ↔ k.
gcd (orderOf g) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `mem_zpowers_zpow_iff`：mem_zpowers_zpow_iff {g : G} {k : Int} : g in Subg
roup.zpowers (g ^ k) ↔ k.gcd (orderOf g) = 1
· 使用定理 `Int.gcd_natCast_natCast`：∀ (a b : ℕ), (↑a).gcd ↑b = a.gcd b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_zpowers_pow_iff {g : G} {k : ℕ} :
    g ∈ Subgroup.zpowers (g ^ k) ↔ k.gcd (orderOf g) = 1 := by
  rw [← zpow_natCast g k, mem_zpowers_zpow_iff, Int.gcd_natCast_natCast]

section Finite
variable [Finite G]

@[to_additive]
/-
**exists_zpow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_zpow_eq_one (x : G) : exists (i : Int) (_ : i != 0), x ^ (i : Int) 
= 1
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPeriodicPt_mul_iff_pow_eq_one`：isPeriodicPt_mul_iff_pow_eq_one (x : G)
 : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
-/
theorem exists_zpow_eq_one (x : G) : ∃ (i : ℤ) (_ : i ≠ 0), x ^ (i : ℤ) = 1 := by
  obtain ⟨w, hw1, hw2⟩ := isOfFinOrder_of_finite x
  refine ⟨w, Int.natCast_ne_zero.mpr (_root_.ne_of_gt hw1), ?_⟩
  rw [zpow_natCast]
  exact (isPeriodicPt_mul_iff_pow_eq_one _).mp hw2

@[to_additive]
/-
**mem_powers_iff_mem_zpowers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_powers_iff_mem_zpowers : y in powers x ↔ y in zpowers x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOfFinOrder.mem_powers_iff_mem_zpowers`：IsOfFinOrder.mem_powers_iff_mem
_zpowers (hx : IsOfFinOrder x) : y in powers x ↔ y in zpowers x
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
-/
lemma mem_powers_iff_mem_zpowers : y ∈ powers x ↔ y ∈ zpowers x :=
  (isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers

@[to_additive]
/-
**powers_eq_zpowers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：powers_eq_zpowers (x : G) : (powers x : Set G) = zpowers x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOfFinOrder.powers_eq_zpowers`：IsOfFinOrder.powers_eq_zpowers (hx : IsO
fFinOrder x) : (powers x : Set G) = zpowers x
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
-/
lemma powers_eq_zpowers (x : G) : (powers x : Set G) = zpowers x :=
  (isOfFinOrder_of_finite _).powers_eq_zpowers

@[to_additive]
/-
**mem_zpowers_iff_mem_range_orderOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_zpowers_iff_mem_range_orderOf [DecidableEq G] : y in zpowers x ↔ y in 
(Finset.range (orderOf x)).image (x ^ ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf`：IsOfFinOrder.mem_zpowers
_iff_mem_range_orderOf [DecidableEq G] (hx : IsOfFinOrder x) : y in zpowers x ↔ 
y in (Finset.range (orderOf x)).imag…
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
-/
lemma mem_zpowers_iff_mem_range_orderOf [DecidableEq G] :
    y ∈ zpowers x ↔ y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
  (isOfFinOrder_of_finite _).mem_zpowers_iff_mem_range_orderOf

/-- The equivalence between `Subgroup.zpowers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive
  /-- The equivalence between `Subgroup.zmultiples` of two elements `a, b` of the same additive
  order, mapping `i • a` to `i • b`. -/]
/-
**zpowersEquivZPowers** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zpowersEquivZPowers (h : orderOf x = orderOf y) : Subgroup.zpowers x ≃ Sub
group.zpowers y
参数：h : orderOf x = orderOf y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
noncomputable def zpowersEquivZPowers (h : orderOf x = orderOf y) :
    Subgroup.zpowers x ≃ Subgroup.zpowers y :=
  (finEquivZPowers <| isOfFinOrder_of_finite _).symm.trans <| (finCongr h).trans <|
    finEquivZPowers <| isOfFinOrder_of_finite _

@[to_additive (attr := simp) zmultiples_equiv_zmultiples_apply]
/-
**zpowersEquivZPowers_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpowersEquivZPowers_apply (h : orderOf x = orderOf y) (n : Nat) : zpowersE
quivZPowers h ⟨x ^ n, n, zpow_natCast x n⟩ = ⟨y ^ n, n, zpow_natCast y n⟩
参数：h : orderOf x = orderOf y；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpowersEquivZPowers.eq_1`：∀ {G : Type u_1} [inst : Group G] {x y : G} [i
nst_1 : Finite G] (h : orderOf x = orderOf y),   zpowersEquivZPowers h = (finEqu
ivZPowers ⋯).s…
· 使用定理 `Equiv.trans_apply`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) 
(g : β ≃ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用引理 `finEquivZPowers_symm_apply`：finEquivZPowers_symm_apply (hx : IsOfFinOrde
r x) (n : Nat) : (finEquivZPowers hx).symm ⟨x ^ n, ⟨n, by simp⟩⟩ = ⟨n % orderOf 
x, Nat.mod_lt _ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zpowersEquivZPowers_apply (h : orderOf x = orderOf y) (n : ℕ) :
    zpowersEquivZPowers h ⟨x ^ n, n, zpow_natCast x n⟩ = ⟨y ^ n, n, zpow_natCast y n⟩ := by
  rw [zpowersEquivZPowers, Equiv.trans_apply, Equiv.trans_apply, finEquivZPowers_symm_apply, ←
    Equiv.eq_symm_apply, finEquivZPowers_symm_apply]
  simp [h]

/-- See `Subgroup.closure_toSubmonoid_of_isOfFinOrder` for a version with weaker assumptions. -/
@[to_additive
/-- See `AddSubgroup.closure_toAddSubmonoid_of_isOfFinOrder` for a version with weaker
assumptions. -/]
/-
**Subgroup.closure_toSubmonoid_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.closure_toSubmonoid_of_finite {s : Set G} : (closure s).toSubmono
id = Submonoid.closure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.closure_toSubmonoid_of_isOfFinOrder`：Subgroup.closure_toSubmono
id_of_isOfFinOrder {s : Set G} (hs : forall x in s, IsOfFinOrder x) : (closure s
).toSubmonoid = Submonoid.closure …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Subgroup.closure_toSubmonoid_of_finite {s : Set G} :
    (closure s).toSubmonoid = Submonoid.closure s :=
  closure_toSubmonoid_of_isOfFinOrder <| by simp [isOfFinOrder_of_finite]

end Finite

variable [Fintype G] {x : G} {n : ℕ}

/-- See also `Nat.card_zpowers`. -/
@[to_additive /-- See also `Nat.card_zmultiples`. -/]
/-
**Fintype.card_zpowers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_zpowers : Fintype.card (zpowers x) = orderOf x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n

--- 原说明 ---
See also `Nat.card_zpowers`.
-/
theorem Fintype.card_zpowers : Fintype.card (zpowers x) = orderOf x :=
  (Fintype.card_eq.2 ⟨finEquivZPowers <| isOfFinOrder_of_finite _⟩).symm.trans <|
    Fintype.card_fin (orderOf x)

@[to_additive]
/-
**card_zpowers_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_zpowers_le (a : G) {k : Nat} (k_pos : k != 0) (ha : a ^ k = 1) : Fint
ype.card (Subgroup.zpowers a) <= k
参数：a : G；k_pos : k != 0；ha : a ^ k = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_zpowers`：Fintype.card_zpowers : Fintype.card (zpowers x) = 
orderOf x
· 使用定理 `orderOf_le_of_pow_eq_one`：orderOf_le_of_pow_eq_one (hn : 0 < n) (h : x ^
 n = 1) : orderOf x <= n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem card_zpowers_le (a : G) {k : ℕ} (k_pos : k ≠ 0)
    (ha : a ^ k = 1) : Fintype.card (Subgroup.zpowers a) ≤ k := by
  rw [Fintype.card_zpowers]
  apply orderOf_le_of_pow_eq_one k_pos.bot_lt ha

open QuotientGroup

@[to_additive]
/-
**orderOf_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_dvd_card : orderOf x ∣ Fintype.card G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_zpowers`：Fintype.card_zpowers : Fintype.card (zpowers x) = 
orderOf x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem orderOf_dvd_card : orderOf x ∣ Fintype.card G := by
  use Fintype.card (G ⧸ zpowers x)
  rw [← card_zpowers, mul_comm, ← Fintype.card_prod,
    ← Fintype.card_congr groupEquivQuotientProdSubgroup]

@[to_additive]
/-
**orderOf_dvd_natCard** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) : orderOf x ∣ Nat.card G
参数：x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
-/
theorem orderOf_dvd_natCard {G : Type*} [Group G] (x : G) : orderOf x ∣ Nat.card G := by
  obtain h | h := fintypeOrInfinite G
  · simp only [Nat.card_eq_fintype_card, orderOf_dvd_card]
  · simp only [card_eq_zero_of_infinite, dvd_zero]

@[to_additive]
nonrec lemma Subgroup.orderOf_dvd_natCard {G : Type*} [Group G] (s : Subgroup G) {x} (hx : x ∈ s) :
    orderOf x ∣ Nat.card s := by
  simpa using orderOf_dvd_natCard (⟨x, hx⟩ : s)

@[to_additive]
/-
**Subgroup.orderOf_le_card** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.orderOf_le_card {G : Type*} [Group G] (s : Subgroup G) (hs : (s :
 Set G).Finite) {x} (hx : x in s) : orderOf x <= Nat.card s
参数：s : Subgroup G；hs : (s : Set G).Finite；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.card_pos_iff`：card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `OneMemClass.coe_nonempty`：OneMemClass.coe_nonempty {S M : Type*} [One M]
 [SetLike S M] [OneMemClass S M] (s : S) : (s : Set M).Nonempty
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Subgroup.orderOf_dvd_natCard`：∀ {G : Type u_6} [inst : Group G] (s : Sub
group G) {x : G}, x ∈ s → orderOf x ∣ Nat.card ↥s
-/
lemma Subgroup.orderOf_le_card {G : Type*} [Group G] (s : Subgroup G) (hs : (s : Set G).Finite)
    {x} (hx : x ∈ s) : orderOf x ≤ Nat.card s :=
  le_of_dvd (Nat.card_pos_iff.2 <| ⟨(OneMemClass.coe_nonempty s).to_subtype, hs.to_subtype⟩) <|
    s.orderOf_dvd_natCard hx

@[to_additive]
/-
**Submonoid.orderOf_le_card** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.orderOf_le_card {G : Type*} [Group G] (s : Submonoid G) (hs : (s
 : Set G).Finite) {x} (hx : x in s) : orderOf x <= Nat.card s
参数：s : Submonoid G；hs : (s : Set G).Finite；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.card_submonoidPowers`：Nat.card_submonoidPowers : Nat.card (powers a)
 = orderOf a
· 使用引理 `Nat.card_mono`：card_mono (ht : t.Finite) (h : s subseteq t) : Nat.card s
 <= Nat.card t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
-/
lemma Submonoid.orderOf_le_card {G : Type*} [Group G] (s : Submonoid G) (hs : (s : Set G).Finite)
    {x} (hx : x ∈ s) : orderOf x ≤ Nat.card s := by
  rw [← Nat.card_submonoidPowers]; exact Nat.card_mono hs <| powers_le.2 hx

@[to_additive (attr := simp) card_nsmul_eq_zero']
/-
**pow_card_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ Nat.card G = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
-/
theorem pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ Nat.card G = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp <| orderOf_dvd_natCard _

/- TODO: Generalise to `Finite` + `CancelMonoid`. -/
@[to_additive (attr := simp) card_nsmul_eq_zero]
/-
**pow_card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_card_eq_one : x ^ Fintype.card G = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `pow_card_eq_one'`：pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ N
at.card G = 1

--- 原说明 ---
TODO: Generalise to `Finite` + `CancelMonoid`.
-/
theorem pow_card_eq_one : x ^ Fintype.card G = 1 := by
  rw [← Nat.card_eq_fintype_card, pow_card_eq_one']

@[to_additive]
/-
**Subgroup.pow_index_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.pow_index_mem {G : Type*} [Group G] (H : Subgroup G) [Normal H] (
g : G) : g ^ index H in H
参数：H : Subgroup G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
· 使用定理 `QuotientGroup.mk_pow`：mk_pow (a : G) (n : Nat) : ((a ^ n : G) : Q) = (a 
: Q) ^ n
· 使用定理 `Subgroup.index.eq_1`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G),
 H.index = Nat.card (G ⧸ H)
· 使用定理 `pow_card_eq_one'`：pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ N
at.card G = 1
-/
theorem Subgroup.pow_index_mem {G : Type*} [Group G] (H : Subgroup G) [Normal H] (g : G) :
    g ^ index H ∈ H := by rw [← eq_one_iff, QuotientGroup.mk_pow H, index, pow_card_eq_one']

@[to_additive]
/-
**Subgroup.pow_relIndex_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.pow_relIndex_mem {G : Type*} [Group G] (H : Subgroup G) [H.Normal
] {K : Subgroup G} {g : G} (hg : g in K) : g ^ H.relIndex K in H
参数：H : Subgroup G；hg : g in K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.pow_index_mem`：Subgroup.pow_index_mem {G : Type*} [Group G] (H 
: Subgroup G) [Normal H] (g : G) : g ^ index H in H
· 使用定理 `Subgroup.normal_subgroupOf`：∀ {G : Type u_1} [inst : Group G] {H N : Sub
group G} [N.Normal], (N.subgroupOf H).Normal
-/
lemma Subgroup.pow_relIndex_mem {G : Type*} [Group G] (H : Subgroup G) [H.Normal] {K : Subgroup G}
    {g : G} (hg : g ∈ K) : g ^ H.relIndex K ∈ H :=
  pow_index_mem (H.subgroupOf K) ⟨g, hg⟩

@[to_additive (attr := simp) mod_card_nsmul]
/-
**pow_mod_card** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_mod_card (a : G) (n : Nat) : a ^ (n % card G) = a ^ n
参数：a : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `orderOf_dvd_card`：orderOf_dvd_card : orderOf x ∣ Fintype.card G
-/
lemma pow_mod_card (a : G) (n : ℕ) : a ^ (n % card G) = a ^ n := by
  rw [eq_comm, ← pow_mod_orderOf, ← Nat.mod_mod_of_dvd n orderOf_dvd_card, pow_mod_orderOf]

@[to_additive (attr := simp) mod_card_zsmul]
/-
**zpow_mod_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpow_mod_card (a : G) (n : Int) : a ^ (n % Fintype.card G : Int) = a ^ n
参数：a : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_mod_orderOf`：zpow_mod_orderOf (x : G) (z : Int) : x ^ (z % (orderOf
 x : Int)) = x ^ z
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `orderOf_dvd_card`：orderOf_dvd_card : orderOf x ∣ Fintype.card G
-/
theorem zpow_mod_card (a : G) (n : ℤ) : a ^ (n % Fintype.card G : ℤ) = a ^ n := by
  rw [eq_comm, ← zpow_mod_orderOf, ← Int.emod_emod_of_dvd n
    (Int.natCast_dvd_natCast.2 orderOf_dvd_card), zpow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_nsmul]
/-
**pow_mod_natCard** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_mod_natCard {G} [Group G] (a : G) (n : Nat) : a ^ (n % Nat.card G) = a
 ^ n
参数：a : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
-/
lemma pow_mod_natCard {G} [Group G] (a : G) (n : ℕ) : a ^ (n % Nat.card G) = a ^ n := by
  rw [eq_comm, ← pow_mod_orderOf, ← Nat.mod_mod_of_dvd n <| orderOf_dvd_natCard _, pow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_zsmul]
/-
**zpow_mod_natCard** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_mod_natCard {G} [Group G] (a : G) (n : Int) : a ^ (n % Nat.card G : I
nt) = a ^ n
参数：a : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_mod_orderOf`：zpow_mod_orderOf (x : G) (z : Int) : x ^ (z % (orderOf
 x : Int)) = x ^ z
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
-/
lemma zpow_mod_natCard {G} [Group G] (a : G) (n : ℤ) : a ^ (n % Nat.card G : ℤ) = a ^ n := by
  rw [eq_comm, ← zpow_mod_orderOf, ← Int.emod_emod_of_dvd n <|
    Int.natCast_dvd_natCast.2 <| orderOf_dvd_natCard _, zpow_mod_orderOf]

/-- If `gcd(|G|,n)=1` then the `n`th power map is a bijection -/
@[to_additive (attr := simps) /-- If `gcd(|G|,n)=1` then the smul by `n` is a bijection -/]
/-
**powCoprime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：powCoprime {G : Type*} [Group G] (h : (Nat.card G).Coprime n) : G ≃ G wher
e toFun g
参数：h : (Nat.card G).Coprime n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `gcd(|G|,n)=1` then the `n`th power map is a bijection
-/
noncomputable def powCoprime {G : Type*} [Group G] (h : (Nat.card G).Coprime n) : G ≃ G where
  toFun g := g ^ n
  invFun g := g ^ (Nat.card G).gcdB n
  left_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    rwa [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key
  right_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    rwa [zpow_add, zpow_mul, zpow_mul', zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key

@[to_additive]
/-
**powCoprime_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：powCoprime_one {G : Type*} [Group G] (h : (Nat.card G).Coprime n) : powCop
rime h 1 = 1
参数：h : (Nat.card G).Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem powCoprime_one {G : Type*} [Group G] (h : (Nat.card G).Coprime n) : powCoprime h 1 = 1 :=
  one_pow n

@[to_additive]
/-
**powCoprime_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：powCoprime_inv {G : Type*} [Group G] (h : (Nat.card G).Coprime n) {g : G} 
: powCoprime h g⁻¹ = (powCoprime h g)⁻¹
参数：h : (Nat.card G).Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
-/
theorem powCoprime_inv {G : Type*} [Group G] (h : (Nat.card G).Coprime n) {g : G} :
    powCoprime h g⁻¹ = (powCoprime h g)⁻¹ :=
  inv_pow g n

@[to_additive Nat.Coprime.nsmul_right_bijective]
/-
**Nat.Coprime.pow_left_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Coprime.pow_left_bijective {G} [Group G] (hn : (Nat.card G).Coprime n)
 : Bijective (· ^ n : G -> G)
参数：hn : (Nat.card G).Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma Nat.Coprime.pow_left_bijective {G} [Group G] (hn : (Nat.card G).Coprime n) :
    Bijective (· ^ n : G → G) :=
  (powCoprime hn).bijective

/- TODO: Generalise to `Submonoid.powers`. -/
@[to_additive]
/-
**image_range_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_range_orderOf [DecidableEq G] : letI : Fintype (zpowers x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用引理 `mem_zpowers_iff_mem_range_orderOf`：mem_zpowers_iff_mem_range_orderOf [De
cidableEq G] : y in zpowers x ↔ y in (Finset.range (orderOf x)).image (x ^ ·)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
TODO: Generalise to `Submonoid.powers`.
-/
theorem image_range_orderOf [DecidableEq G] :
    letI : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
    Finset.image (fun i => x ^ i) (Finset.range (orderOf x)) = (zpowers x : Set G).toFinset := by
  let : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
  ext x
  rw [Set.mem_toFinset, SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf]
/-
**smul_eq_of_le_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_of_le_smul {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOr
der α] {g : G} {a : α} [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h
 : a <= g • a) : g • a = a
参数：h : a <= g • a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
· 使用引理 `le_pow_smul`：le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α]
 {g : G} {a : α} [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : a <
=…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `pow_card_eq_one'`：pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ N
at.card G = 1
· 使用定理 `Nat.sub_one_add_one_eq_of_pos`：∀ {n : ℕ}, 0 < n → n - 1 + 1 = n
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
lemma smul_eq_of_le_smul
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : a ≤ g • a) : g • a = a := by
  have key := smul_mono_right g (le_pow_smul h (Nat.card G - 1))
  rw [smul_smul, ← _root_.pow_succ',
    Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one', one_smul] at key
  exact le_antisymm key h
/-
**smul_eq_of_smul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_of_smul_le {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOr
der α] {g : G} {a : α} [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h
 : g • a <= a) : g • a = a
参数：h : g • a <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
· 使用引理 `pow_smul_le`：pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α]
 {g : G} {a : α} [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : g •
 …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `pow_card_eq_one'`：pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ N
at.card G = 1
· 使用定理 `Nat.sub_one_add_one_eq_of_pos`：∀ {n : ℕ}, 0 < n → n - 1 + 1 = n
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
lemma smul_eq_of_smul_le
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : g • a ≤ a) : g • a = a := by
  have key := smul_mono_right g (pow_smul_le h (Nat.card G - 1))
  rw [smul_smul, ← _root_.pow_succ',
    Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one', one_smul] at key
  exact le_antisymm h key

end FiniteGroup

section PowIsSubgroup

/-- A nonempty idempotent subset of a finite cancellative monoid is a submonoid -/
@[to_additive
/-- A nonempty idempotent subset of a finite cancellative additive monoid is a submonoid -/]
/-
**submonoidOfIdempotent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：submonoidOfIdempotent {M : Type*} [LeftCancelMonoid M] [Finite M] (S : Set
 M) (hS1 : S.Nonempty) (hS2 : S * S = S) : Submonoid M
参数：S : Set M；hS1 : S.Nonempty；hS2 : S * S = S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def submonoidOfIdempotent {M : Type*} [LeftCancelMonoid M] [Finite M] (S : Set M)
    (hS1 : S.Nonempty) (hS2 : S * S = S) : Submonoid M :=
  have pow_mem (a : M) (ha : a ∈ S) (n : ℕ) : a ^ (n + 1) ∈ S := by
    induction n with
    | zero => rwa [zero_add, pow_one]
    | succ n ih =>
      rw [← hS2, pow_succ]
      exact Set.mul_mem_mul ih ha
  { carrier := S
    one_mem' := by
      obtain ⟨a, ha⟩ := hS1
      rw [← pow_orderOf_eq_one a, ← tsub_add_cancel_of_le (succ_le_of_lt (orderOf_pos a))]
      exact pow_mem a ha (orderOf a - 1)
    mul_mem' := fun ha hb => (congr_arg₂ (· ∈ ·) rfl hS2).mp (Set.mul_mem_mul ha hb) }

/-- A nonempty idempotent subset of a finite group is a subgroup -/
@[to_additive /-- A nonempty idempotent subset of a finite additive group is a subgroup -/]
/-
**subgroupOfIdempotent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：subgroupOfIdempotent {G : Type*} [Group G] [Finite G] (S : Set G) (hS1 : S
.Nonempty) (hS2 : S * S = S) : Subgroup G
参数：S : Set G；hS1 : S.Nonempty；hS2 : S * S = S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonempty idempotent subset of a finite group is a subgroup
-/
def subgroupOfIdempotent {G : Type*} [Group G] [Finite G] (S : Set G) (hS1 : S.Nonempty)
    (hS2 : S * S = S) : Subgroup G :=
  { submonoidOfIdempotent S hS1 hS2 with
    carrier := S
    inv_mem' := fun {a} ha => show a⁻¹ ∈ submonoidOfIdempotent S hS1 hS2 by
      rw [← one_mul a⁻¹, ← pow_one a, ← pow_orderOf_eq_one a, ← pow_sub a (orderOf_pos a)]
      exact pow_mem ha (orderOf a - 1) }

/-- If `S` is a nonempty subset of a finite group `G`, then `S ^ |G|` is a subgroup -/
@[to_additive (attr := simps!) smulCardAddSubgroup
  /-- If `S` is a nonempty subset of a finite additive group `G`, then `|G| • S` is a subgroup -/]
/-
**powCardSubgroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：powCardSubgroup {G : Type*} [Group G] [Fintype G] (S : Set G) (hS : S.None
mpty) : Subgroup G
参数：S : Set G；hS : S.Nonempty。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
def powCardSubgroup {G : Type*} [Group G] [Fintype G] (S : Set G) (hS : S.Nonempty) : Subgroup G :=
  have one_mem : (1 : G) ∈ S ^ Fintype.card G := by
    obtain ⟨a, ha⟩ := hS
    rw [← pow_card_eq_one]
    exact Set.pow_mem_pow ha
  subgroupOfIdempotent (S ^ Fintype.card G) ⟨1, one_mem⟩ <| by
    classical
    apply (Set.eq_of_subset_of_card_le (Set.subset_mul_left _ one_mem) (ge_of_eq _)).symm
    simp_rw [← pow_add,
        Group.card_pow_eq_card_pow_card_univ S (Fintype.card G + Fintype.card G) le_add_self]

end PowIsSubgroup

section LinearOrderedSemiring
variable [Semiring G] [LinearOrder G] [IsStrictOrderedRing G] {a : G}

/-
**IsOfFinOrder.eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsOfFinOrder`。
形式化陈述：∀ {G : Type u_1} [inst : Semiring G] [inst_1 : LinearOrder G] [IsStrictOrd
eredRing G] {a : G},   0 ≤ a → IsOfFinOrder a → a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.exists_pow_eq_one`：∀ {G : Type u_1} [inst : Monoid G] {x : 
G}, IsOfFinOrder x → ∃ n, 0 < n ∧ x ^ n = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `pow_eq_one_iff_of_nonneg`：pow_eq_one_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : a ^ n = 1 ↔ a = 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
protected lemma IsOfFinOrder.eq_one (ha₀ : 0 ≤ a) (ha : IsOfFinOrder a) : a = 1 := by
  obtain ⟨n, hn, ha⟩ := ha.exists_pow_eq_one
  exact (pow_eq_one_iff_of_nonneg ha₀ hn.ne').1 ha

end LinearOrderedSemiring

section LinearOrderedRing

variable [Ring G] [LinearOrder G] [IsStrictOrderedRing G] {a x : G}

/-
**IsOfFinOrder.eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `IsOfFinOrder`。
形式化陈述：∀ {G : Type u_1} [inst : Ring G] [inst_1 : LinearOrder G] [IsStrictOrdered
Ring G] {a : G},   a ≤ 0 → IsOfFinOrder a → a = -1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOfFinOrder.eq_one`：∀ {G : Type u_1} [inst : Semiring G] [inst_1 : Line
arOrder G] [IsStrictOrderedRing G] {a : G},   0 ≤ a → IsOfFinOrder a → a = 1
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用引理 `IsOfFinOrder.pow`：IsOfFinOrder.pow {n : Nat} : IsOfFinOrder a -> IsOfFin
Order (a ^ n)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected lemma IsOfFinOrder.eq_neg_one (ha₀ : a ≤ 0) (ha : IsOfFinOrder a) : a = -1 :=
  (sq_eq_one_iff.1 <| ha.pow.eq_one <| sq_nonneg a).resolve_left <| by
    rintro rfl; exact one_pos.not_ge ha₀
/-
**orderOf_abs_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_abs_ne_one (h : |x| != 1) : orderOf x = 0
参数：h : |x| != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_eq_zero_iff'`：orderOf_eq_zero_iff' : orderOf x = 0 ↔ forall n : 
Nat, 0 < n -> x ^ n != 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `pow_lt_one₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [PosMulMono M₀],   0 ≤ a → a < 1 → ∀ {n : ℕ}, n ≠ 0 → a ^ n < 
1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
-/
theorem orderOf_abs_ne_one (h : |x| ≠ 1) : orderOf x = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn hx
  replace hx : |x| ^ n = 1 := by simpa only [abs_one, abs_pow] using congr_arg abs hx
  rcases h.lt_or_gt with h | h
  · exact ((pow_lt_one₀ (abs_nonneg x) h hn.ne').ne hx).elim
  · exact ((one_lt_pow₀ h hn.ne').ne' hx).elim
/-
**LinearOrderedRing.orderOf_le_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearOrderedRing.orderOf_le_two : orderOf x <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_abs_ne_one`：orderOf_abs_ne_one (h : |x| != 1) : orderOf x = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_or_eq_neg_of_abs_eq`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : L
inearOrder α] {a b : α}, |a| = b → a = b ∨ a = -b
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_le_of_pow_eq_one`：orderOf_le_of_pow_eq_one (hn : 0 < n) (h : x ^
 n = 1) : orderOf x <= n
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearOrderedRing.orderOf_le_two : orderOf x ≤ 2 := by
  rcases ne_or_eq |x| 1 with h | h
  · simp [orderOf_abs_ne_one h]
  rcases eq_or_eq_neg_of_abs_eq h with (rfl | rfl)
  · simp
  exact orderOf_le_of_pow_eq_one zero_lt_two (by simp)

end LinearOrderedRing

section Prod

variable [Monoid α] [Monoid β] {x : α × β} {a : α} {b : β}

@[to_additive]
/-
**Prod.orderOf** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} [inst : Monoid α] [inst_1 : Monoid β] (x :
 α × β),   orderOf x = (orderOf x.1).lcm (orderOf x.2)
参数：x : α × β；orderOf x.1；orderOf x.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_prodMap`：minimalPeriod_prodMap (f : α -> α) (g : 
β -> β) (x : α × β) : minimalPeriod (Prod.map f g) x = (minimalPeriod f x.1).lcm
 (minimalPeriod g x.…
-/
protected theorem Prod.orderOf (x : α × β) : orderOf x = (orderOf x.1).lcm (orderOf x.2) :=
  minimalPeriod_prodMap _ _ _

@[to_additive]
/-
**orderOf_fst_dvd_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_fst_dvd_orderOf : orderOf x.1 ∣ orderOf x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_fst_dvd`：minimalPeriod_fst_dvd : minimalPeriod f 
x.1 ∣ minimalPeriod (Prod.map f g) x
-/
theorem orderOf_fst_dvd_orderOf : orderOf x.1 ∣ orderOf x :=
  minimalPeriod_fst_dvd

@[to_additive]
/-
**orderOf_snd_dvd_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_snd_dvd_orderOf : orderOf x.2 ∣ orderOf x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_snd_dvd`：minimalPeriod_snd_dvd : minimalPeriod g 
x.2 ∣ minimalPeriod (Prod.map f g) x
-/
theorem orderOf_snd_dvd_orderOf : orderOf x.2 ∣ orderOf x :=
  minimalPeriod_snd_dvd

@[to_additive]
/-
**IsOfFinOrder.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.fst (hx : IsOfFinOrder x) : IsOfFinOrder x.1
参数：hx : IsOfFinOrder x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.mono`：IsOfFinOrder.mono [Monoid β] {y : β} (hx : IsOfFinOrd
er x) (h : orderOf y ∣ orderOf x) : IsOfFinOrder y
· 使用定理 `orderOf_fst_dvd_orderOf`：orderOf_fst_dvd_orderOf : orderOf x.1 ∣ orderOf
 x
-/
theorem IsOfFinOrder.fst (hx : IsOfFinOrder x) : IsOfFinOrder x.1 :=
  hx.mono orderOf_fst_dvd_orderOf

@[to_additive]
/-
**IsOfFinOrder.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.snd (hx : IsOfFinOrder x) : IsOfFinOrder x.2
参数：hx : IsOfFinOrder x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.mono`：IsOfFinOrder.mono [Monoid β] {y : β} (hx : IsOfFinOrd
er x) (h : orderOf y ∣ orderOf x) : IsOfFinOrder y
· 使用定理 `orderOf_snd_dvd_orderOf`：orderOf_snd_dvd_orderOf : orderOf x.2 ∣ orderOf
 x
-/
theorem IsOfFinOrder.snd (hx : IsOfFinOrder x) : IsOfFinOrder x.2 :=
  hx.mono orderOf_snd_dvd_orderOf

@[to_additive IsOfFinAddOrder.prod_mk]
/-
**IsOfFinOrder.prod_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.prod_mk : IsOfFinOrder a -> IsOfFinOrder b -> IsOfFinOrder (a
, b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.orderOf`：∀ {α : Type u_4} {β : Type u_5} [inst : Monoid α] [inst_1 
: Monoid β] (x : α × β),   orderOf x = (orderOf x.1).lcm (orderOf x.2)
· 使用定理 `Nat.lcm_pos`：∀ {m n : ℕ}, 0 < m → 0 < n → 0 < m.lcm n
-/
theorem IsOfFinOrder.prod_mk : IsOfFinOrder a → IsOfFinOrder b → IsOfFinOrder (a, b) := by
  simpa only [← orderOf_pos_iff, Prod.orderOf] using Nat.lcm_pos

@[to_additive IsOfFinAddOrder.prod_iff]
/-
**IsOfFinOrder.prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOfFinOrder.prod_iff : IsOfFinOrder x ↔ IsOfFinOrder x.1 ∧ IsOfFinOrder x
.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.fst`：IsOfFinOrder.fst (hx : IsOfFinOrder x) : IsOfFinOrder 
x.1
· 使用定理 `IsOfFinOrder.snd`：IsOfFinOrder.snd (hx : IsOfFinOrder x) : IsOfFinOrder 
x.2
· 使用定理 `IsOfFinOrder.prod_mk`：IsOfFinOrder.prod_mk : IsOfFinOrder a -> IsOfFinOr
der b -> IsOfFinOrder (a, b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsOfFinOrder.prod_iff : IsOfFinOrder x ↔ IsOfFinOrder x.1 ∧ IsOfFinOrder x.2 :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ .prod_mk h.1 h.2⟩

@[to_additive]
/-
**Prod.orderOf_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prod.orderOf_mk : orderOf (a, b) = Nat.lcm (orderOf a) (orderOf b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.orderOf`：∀ {α : Type u_4} {β : Type u_5} [inst : Monoid α] [inst_1 
: Monoid β] (x : α × β),   orderOf x = (orderOf x.1).lcm (orderOf x.2)
-/
lemma Prod.orderOf_mk : orderOf (a, b) = Nat.lcm (orderOf a) (orderOf b) :=
  (a, b).orderOf

end Prod

section Pi

variable {ι : Type*} {α : ι → Type*} [∀ i, Monoid (α i)] {x : ∀ i, α i}

@[to_additive]
/-
**Pi.orderOf_eq_sInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.orderOf_eq_sInf (x : forall i, α i) : orderOf x = sInf { n > 0 | forall
 i, orderOf (x i) ∣ n }
参数：x : forall i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_piMap`：minimalPeriod_piMap : minimalPeriod (Pi.ma
p f) x = sInf { n > 0 | forall i, minimalPeriod (f i) (x i) ∣ n }
-/
lemma Pi.orderOf_eq_sInf (x : ∀ i, α i) : orderOf x = sInf { n > 0 | ∀ i, orderOf (x i) ∣ n } :=
  minimalPeriod_piMap

@[to_additive]
/-
**Pi.orderOf** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : (i : ι) → Monoid (α i)] [inst_
1 : Fintype ι] (x : (i : ι) → α i),   orderOf x = Finset.univ.lcm fun i => order
Of (x i)
参数：i : ι；α i；x : (i : ι) → α i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_piMap_fintype`：minimalPeriod_piMap_fintype [Finty
pe ι] : minimalPeriod (Pi.map f) x = Finset.univ.lcm (fun i => minimalPeriod (f 
i) (x i))
-/
protected lemma Pi.orderOf [Fintype ι] (x : ∀ i, α i) :
    orderOf x = Finset.univ.lcm (fun i => orderOf (x i)) :=
  minimalPeriod_piMap_fintype

@[to_additive]
/-
**orderOf_apply_dvd_orderOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orderOf_apply_dvd_orderOf : forall i, orderOf (x i) ∣ orderOf x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_single_dvd_minimalPeriod_piMap`：minimalPeriod_sin
gle_dvd_minimalPeriod_piMap (i : ι) : minimalPeriod (f i) (x i) ∣ minimalPeriod 
(Pi.map f) x
-/
theorem orderOf_apply_dvd_orderOf : ∀ i, orderOf (x i) ∣ orderOf x :=
  minimalPeriod_single_dvd_minimalPeriod_piMap

@[to_additive]
/-
**IsOfFinOrder.pi** 是 Mathlib 中的一个定理，位于命名空间 `IsOfFinOrder`。
形式化陈述：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : (i : ι) → Monoid (α i)] {x : (
i : ι) → α i} [Finite ι],   (∀ (i : ι), IsOfFinOrder (x i)) → IsOfFinOrder x
参数：i : ι；α i；i : ι；∀ (i : ι), IsOfFinOrder (x i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.orderOf`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : (i : ι) → Monoid
 (α i)] [inst_1 : Fintype ι] (x : (i : ι) → α i),   orderOf x = Finset.univ.lcm 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
protected theorem IsOfFinOrder.pi [Finite ι] : (∀ i, IsOfFinOrder (x i)) → IsOfFinOrder x := by
  have := Fintype.ofFinite ι
  simp only [← orderOf_ne_zero_iff, Pi.orderOf]
  simp [Finset.lcm_eq_zero_iff]

end Pi

@[simp]
/-
**Nat.cast_card_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fintype R] : (Fintype.card 
R : R) = 0
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `card_nsmul_eq_zero`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1 : Finty
pe G] {x : G}, Fintype.card G • x = 0
-/
lemma Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fintype R] : (Fintype.card R : R) = 0 := by
  rw [← nsmul_one, card_nsmul_eq_zero]

section NonAssocRing
variable (R : Type*) [NonAssocRing R] (p : ℕ)

/-
**CharP.addOrderOf_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CharP.addOrderOf_one : CharP R (addOrderOf (1 : R)) where cast_eq_zero_iff
 n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.smul_one_eq_cast`：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring
 R] (m : Nat) : m • (1 : R) = ↑m
· 使用定理 `addOrderOf_dvd_iff_nsmul_eq_zero`：∀ {G : Type u_1} [inst : AddMonoid G] 
{x : G} {n : ℕ}, addOrderOf x ∣ n ↔ n • x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma CharP.addOrderOf_one : CharP R (addOrderOf (1 : R)) where
  cast_eq_zero_iff n := by rw [← Nat.smul_one_eq_cast, addOrderOf_dvd_iff_nsmul_eq_zero]

variable [Fintype R]

variable {R} in
/-
**charP_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：charP_of_ne_zero (hn : card R = p) (hR : forall i < p, (i : R) = 0 -> i = 
0) : CharP R p where cast_eq_zero_iff n
参数：hn : card R = p；hR : forall i < p, (i : R) = 0 -> i = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_card_eq_zero`：Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fi
ntype R] : (Fintype.card R : R) = 0
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
-/
lemma charP_of_ne_zero (hn : card R = p) (hR : ∀ i < p, (i : R) = 0 → i = 0) : CharP R p where
  cast_eq_zero_iff n := by
    have H : (p : R) = 0 := by rw [← hn, Nat.cast_card_eq_zero]
    constructor
    · intro h
      rw [← Nat.mod_add_div n p, Nat.cast_add, Nat.cast_mul, H, zero_mul, add_zero] at h
      rw [Nat.dvd_iff_mod_eq_zero]
      apply hR _ (Nat.mod_lt _ _) h
      rw [← hn, Fintype.card_pos_iff]
      exact ⟨0⟩
    · rintro ⟨n, rfl⟩
      rw [Nat.cast_mul, H, zero_mul]

end NonAssocRing

/-
**charP_of_prime_pow_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：charP_of_prime_pow_injective (R) [Ring R] [Fintype R] (p n : Nat) [hp : Fa
ct p.Prime] (hn : card R = p ^ n) (hR : forall i <= n, (p : R) ^ i = 0 -> i = n)
 : CharP R (p ^ n)
参数：R；p n : Nat；hn : card R = p ^ n；hR : forall i <= n, (p : R) ^ i = 0 -> i = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用引理 `Nat.cast_card_eq_zero`：Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fi
ntype R] : (Fintype.card R : R) = 0
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
-/
lemma charP_of_prime_pow_injective (R) [Ring R] [Fintype R] (p n : ℕ) [hp : Fact p.Prime]
    (hn : card R = p ^ n) (hR : ∀ i ≤ n, (p : R) ^ i = 0 → i = n) : CharP R (p ^ n) := by
  obtain ⟨c, hc⟩ := CharP.exists R
  have hcpn : c ∣ p ^ n := by rw [← CharP.cast_eq_zero_iff R c, ← hn, Nat.cast_card_eq_zero]
  obtain ⟨i, hi, rfl⟩ : ∃ i ≤ n, c = p ^ i := by rwa [Nat.dvd_prime_pow hp.1] at hcpn
  obtain rfl : i = n := hR i hi <| by rw [← Nat.cast_pow, CharP.cast_eq_zero]
  assumption

namespace SemiconjBy

@[to_additive]
/-
**SemiconjBy.orderOf_eq** 是 Mathlib 中的一个引理，位于命名空间 `SemiconjBy`。
形式化陈述：orderOf_eq [Group G] (a : G) {x y : G} (h : SemiconjBy a x y) : orderOf x 
= orderOf y
参数：a : G；h : SemiconjBy a x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_eq_orderOf_iff`：orderOf_eq_orderOf_iff {H : Type*} [Monoid H] {y
 : H} : orderOf x = orderOf y ↔ forall n : Nat, x ^ n = 1 ↔ y ^ n = 1
· 使用定理 `SemiconjBy.eq_one_iff`：∀ {G : Type u_1} [inst : Group G] (a : G) {x y : 
G}, SemiconjBy a x y → (x = 1 ↔ y = 1)
· 使用定理 `SemiconjBy.pow_right`：pow_right {a x y : M} (h : SemiconjBy a x y) (n : 
Nat) : SemiconjBy a (x ^ n) (y ^ n)
-/
lemma orderOf_eq [Group G] (a : G) {x y : G} (h : SemiconjBy a x y) : orderOf x = orderOf y := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  exact (h.pow_right n).eq_one_iff

end SemiconjBy

section single

/-
**orderOf_piMulSingle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_piMulSingle {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [(i : ι) 
-> Monoid (M i)] (i : ι) (g : M i) : orderOf (Pi.mulSingle i g) = orderOf g
参数：i : ι；M i；i : ι；g : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用引理 `Pi.mulSingle_injective`：mulSingle_injective (i : ι) : Function.Injective
 (mulSingle i : M i -> forall i, M i)
-/
lemma orderOf_piMulSingle {ι : Type*} [DecidableEq ι] {M : ι → Type*} [(i : ι) → Monoid (M i)]
    (i : ι) (g : M i) :
    orderOf (Pi.mulSingle i g) = orderOf g :=
  orderOf_injective (MonoidHom.mulSingle M i) (Pi.mulSingle_injective i) g

end single

