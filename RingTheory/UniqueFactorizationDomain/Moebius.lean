/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# The Moebius function on a unique factorization monoid

We define the Moebius function on a unique factorization monoid.

## Main definitions

* `UniqueFactorizationMonoid.moebius`: The Moebius function on a unique factorization monoid,
  defined to be `((-1) ^ (factors a).card)` if `a` is squarefree and `0` otherwise.

## Main statements

* `IsRelPrime.moebius_mul`: The Moebius function is a multiplicative function.
-/

@[expose] public section

namespace UniqueFactorizationMonoid

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α] {a b : α}

/-- The Moebius function on a unique factorization monoid, defined to be
  `((-1) ^ (factors a).card)` if `a` is squarefree and `0` otherwise. -/
/-
**UniqueFactorizationMonoid.moebius** 是 Mathlib 中的一个定义，位于命名空间 `UniqueFactorizati
onMonoid`。
形式化陈述：moebius (a : α) : Int
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Moebius function on a unique factorization monoid, defined to be
  `((-1) ^ (factors a).card)` if `a` is squarefree and `0` otherwise.
-/
noncomputable def moebius (a : α) : ℤ :=
  open scoped Classical in
  if Squarefree a then ((-1) ^ (factors a).card) else 0

-- Todo: prove `Int.moebius_eq` as well.
/-
**UniqueFactorizationMonoid._root_.Nat.moebius_eq** 是 Mathlib 中的一个定理，位于命名空间 `Uni
queFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Nat.moebius_eq (n : ℕ) : moebius n = ArithmeticFunction.moebius n := by
  rw [moebius]
  congr
  simp [Nat.factors_eq, ArithmeticFunction.cardFactors_apply]

@[simp]
/-
**UniqueFactorizationMonoid._root_.Squarefree.moebius_eq** 是 Mathlib 中的一个定理，位于命名
空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Squarefree.moebius_eq (ha : Squarefree a) : moebius a = (-1) ^ (factors a).card :=
  if_pos ha

@[simp]
/-
**UniqueFactorizationMonoid.moebius_of_not_squarefree** 是 Mathlib 中的一个定理，位于命名空间 
`UniqueFactorizationMonoid`。
形式化陈述：moebius_of_not_squarefree (ha : ¬ Squarefree a) : moebius a = 0
参数：ha : ¬ Squarefree a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem moebius_of_not_squarefree (ha : ¬ Squarefree a) : moebius a = 0 :=
  if_neg ha
/-
**UniqueFactorizationMonoid.moebius_zero** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactor
izationMonoid`。
形式化陈述：moebius_zero [Nontrivial α] : moebius (0 : α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.moebius_of_not_squarefree`：moebius_of_not_squa
refree (ha : ¬ Squarefree a) : moebius a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem moebius_zero [Nontrivial α] : moebius (0 : α) = 0 := by
  simp
/-
**UniqueFactorizationMonoid.moebius_one** 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactori
zationMonoid`。
形式化陈述：moebius_one : moebius (1 : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Squarefree.moebius_eq`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [i
nst_1 : UniqueFactorizationMonoid α] {a : α},   Squarefree a → UniqueFactorizati
onMonoid.mo…
· 使用定理 `UniqueFactorizationMonoid.factors_one`：factors_one : factors (1 : α) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem moebius_one : moebius (1 : α) = 1 := by
  simp
/-
**UniqueFactorizationMonoid._root_.Associated.moebius_eq** 是 Mathlib 中的一个定理，位于命名
空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Associated.moebius_eq (h : Associated a b) : moebius a = moebius b := by
  rw [moebius, moebius, h.squarefree_iff, h.card_factors_eq]
/-
**UniqueFactorizationMonoid._root_.IsUnit.moebius_eq** 是 Mathlib 中的一个定理，位于命名空间 `
UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUnit.moebius_eq (ha : IsUnit a) : moebius a = 1 := by
  rw [(associated_one_iff_isUnit.mpr ha).moebius_eq, moebius_one]
/-
**UniqueFactorizationMonoid._root_.Irreducible.moebius_eq** 是 Mathlib 中的一个定理，位于命
名空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Irreducible.moebius_eq (ha : Irreducible a) : moebius a = -1 := by
  rw [ha.squarefree.moebius_eq, card_factors_of_irreducible ha, pow_one]
/-
**UniqueFactorizationMonoid._root_.IsRelPrime.moebius_mul** 是 Mathlib 中的一个定理，位于命
名空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsRelPrime.moebius_mul (h : IsRelPrime a b) :
    moebius (a * b) = moebius a * moebius b := by
  rcases subsingleton_or_nontrivial α
  · rw [Subsingleton.elim a 1, moebius_one, one_mul, one_mul]
  by_cases ha : Squarefree a; swap
  · simp [ha, mt Squarefree.of_mul_left ha]
  by_cases hb : Squarefree b; swap
  · simp [hb, mt Squarefree.of_mul_right hb]
  have hab : Squarefree (a * b) := squarefree_mul_iff.mpr ⟨h, ha, hb⟩
  rw [hab.moebius_eq, Multiset.card_eq_card_of_rel (factors_mul ha.ne_zero hb.ne_zero),
    Multiset.card_add, pow_add, ha.moebius_eq, hb.moebius_eq]

end UniqueFactorizationMonoid

