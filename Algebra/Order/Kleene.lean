/-
Copyright (c) 2022 Siddhartha Prasad, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Prasad, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Kleene algebras

This file defines idempotent semirings and Kleene algebras, which are used extensively in the theory
of computation.

An idempotent semiring is a semiring whose addition is idempotent. An idempotent semiring is
naturally a semilattice by setting `a ≤ b` if `a + b = b`.

A Kleene algebra is an idempotent semiring equipped with an additional unary operator `∗`, the
Kleene star, such that (informally) `a∗ = 1 + a + a * a + a * a * a + ...`

## Main declarations

* `IdemSemiring`: Idempotent semiring
* `IdemCommSemiring`: Idempotent commutative semiring
* `KleeneAlgebra`: Kleene algebra

## Notation

`a∗` is notation for `kstar a` in scope `Computability`.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*]
  [kozen1994]
* https://planetmath.org/idempotentsemiring
* https://encyclopediaofmath.org/wiki/Idempotent_semi-ring
* https://planetmath.org/kleene_algebra

## TODO

Instances for `AddOpposite`, `MulOpposite`, `ULift`, `Subsemiring`, `Subring`, `Subalgebra`.

## Tags

kleene algebra, idempotent semiring
-/

@[expose] public section

open Function

variable {α β ι : Type*} {π : ι → Type*}

/-- An idempotent semiring is a semiring with the additional property that addition is idempotent.
-/
/-
**IdemSemiring** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：IdemSemiring (α : Type*) extends Semiring α, SemilatticeSup α, OrderBot α 
where protected add_eq_sup (a b : α) : a + b = a ⊔ b
参数：α : Type*；a b : α。
继承自：Semiring α, SemilatticeSup α, OrderBot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An idempotent semiring is a semiring with the additional property that addition 
is idempotent.
-/
class IdemSemiring (α : Type*) extends Semiring α, SemilatticeSup α, OrderBot α where
  protected add_eq_sup (a b : α) : a + b = a ⊔ b := by intros; rfl

/-- An idempotent commutative semiring is a commutative semiring with the additional property that
addition is idempotent. -/
/-
**IdemCommSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An idempotent commutative semiring is a commutative semiring with the additional
 property that
addition is idempotent.
-/
class IdemCommSemiring (α : Type*) extends CommSemiring α, IdemSemiring α

/-- Notation typeclass for the Kleene star `∗`. -/
/-
**KStar** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation typeclass for the Kleene star `∗`.
-/
class KStar (α : Type*) where
  /-- The Kleene star operator on a Kleene algebra -/
  protected kstar : α → α

@[inherit_doc] scoped[Computability] postfix:1024 "∗" => KStar.kstar

open Computability

/-- A Kleene algebra is an idempotent semiring with an additional unary operator `kstar`
(for Kleene star) that satisfies the following properties:
* `1 ≤ a∗`
* `a * a∗ ≤ a∗`
* `a∗ * a ≤ a∗`
* If `b * a ≤ b`, then `b * a∗ ≤ b`
* If `a * b ≤ b`, then `a∗ * b ≤ b`
-/
/-
**KleeneAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Kleene algebra is an idempotent semiring with an additional unary operator `ks
tar`
(for Kleene star) that satisfies the following properties:
* `1 ≤ a∗`
* `a * a∗ ≤ a∗`
* `a∗ * a ≤ a∗`
* If `b * a ≤ b`, then `b * a∗ ≤ b`
* If `a * b ≤ b`, then `a∗ * b ≤ b`
-/
class KleeneAlgebra (α : Type*) extends IdemSemiring α, KStar α where
  protected one_le_kstar (a : α) : 1 ≤ a∗
  protected mul_kstar_le_kstar (a : α) : a * a∗ ≤ a∗
  protected kstar_mul_le_kstar (a : α) : a∗ * a ≤ a∗
  protected mul_kstar_le_self (a b : α) : b * a ≤ b → b * a∗ ≤ b
  protected kstar_mul_le_self (a b : α) : a * b ≤ b → a∗ * b ≤ b

-- See note [reducible non-instances]
/-- Construct an idempotent semiring from an idempotent addition. -/
/-
**IdemSemiring.ofSemiring** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IdemSemiring.ofSemiring [Semiring α] (h : forall a : α, a + a = a) : IdemS
emiring α where le a b
参数：h : forall a : α, a + a = a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an idempotent semiring from an idempotent addition.
-/
abbrev IdemSemiring.ofSemiring [Semiring α] (h : ∀ a : α, a + a = a) : IdemSemiring α where
  le a b := a + b = b
  le_refl := h
  le_trans a b c hab hbc := by rw [← hbc, ← add_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, add_comm]
  sup := (· + ·)
  le_sup_left a b := by rw [← add_assoc, h]
  le_sup_right a b := by rw [add_comm, add_assoc, h]
  sup_le a b c hab hbc := by rwa [add_assoc, hbc]
  bot := 0
  bot_le := zero_add

section IdemSemiring

variable [IdemSemiring α] {a b c : α}

/-
**add_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_eq_sup (a b : α) : a + b = a ⊔ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IdemSemiring.add_eq_sup`：∀ {α : Type u_5} [self : IdemSemiring α] (a b :
 α), a + b = a ⊔ b
-/
theorem add_eq_sup (a b : α) : a + b = a ⊔ b :=
  IdemSemiring.add_eq_sup _ _

scoped[Computability] attribute [simp] add_eq_sup
/-
**add_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_idem (a : α) : a + a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_sup`：add_eq_sup (a b : α) : a + b = a ⊔ b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_idem (a : α) : a + a = a := by simp
/-
**natCast_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：natCast_eq_one {n : Nat} (nezero : n != 0) : (n : α) = 1
参数：nezero : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_idem`：add_idem (a : α) : a + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma natCast_eq_one {n : ℕ} (nezero : n ≠ 0) : (n : α) = 1 := by
  rw [← Nat.one_le_iff_ne_zero] at nezero
  induction n, nezero using Nat.le_induction with
  | base => exact Nat.cast_one
  | succ x _ hx => rw [Nat.cast_add, hx, Nat.cast_one, add_idem 1]
/-
**ofNat_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ofNat_eq_one {n : Nat} [n.AtLeastTwo] : (ofNat(n) : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `natCast_eq_one`：natCast_eq_one {n : Nat} (nezero : n != 0) : (n : α) = 1
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Nat.AtLeastTwo.prop`：∀ {n : ℕ} [self : n.AtLeastTwo], 2 ≤ n
-/
lemma ofNat_eq_one {n : ℕ} [n.AtLeastTwo] : (ofNat(n) : α) = 1 :=
  natCast_eq_one <| Nat.ne_zero_of_lt Nat.AtLeastTwo.prop
/-
**nsmul_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : IdemSemiring α] {n : ℕ}, n ≠ 0 → ∀ (a : α), n • a
 = a
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nsmul_eq_self : ∀ {n : ℕ} (_ : n ≠ 0) (a : α), n • a = a
  | 0, h => (h rfl).elim
  | 1, _ => one_nsmul
  | n + 2, _ => fun a ↦ by rw [succ_nsmul, nsmul_eq_self n.succ_ne_zero, add_idem]
/-
**add_eq_left_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_eq_left_iff_le : a + b = a ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_sup`：add_eq_sup (a b : α) : a + b = a ⊔ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_eq_left_iff_le : a + b = a ↔ b ≤ a := by simp
/-
**add_eq_right_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_eq_right_iff_le : a + b = b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_sup`：add_eq_sup (a b : α) : a + b = a ⊔ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_eq_right_iff_le : a + b = b ↔ a ≤ b := by simp

alias ⟨_, LE.le.add_eq_left⟩ := add_eq_left_iff_le

alias ⟨_, LE.le.add_eq_right⟩ := add_eq_right_iff_le
/-
**add_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le_iff : a + b <= c ↔ a <= c ∧ b <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_sup`：add_eq_sup (a b : α) : a + b = a ⊔ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_le_iff : a + b ≤ c ↔ a ≤ c ∧ b ≤ c := by simp
/-
**add_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le (ha : a <= c) (hb : b <= c) : a + b <= c
参数：ha : a <= c；hb : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_le_iff`：add_le_iff : a + b <= c ↔ a <= c ∧ b <= c
-/
theorem add_le (ha : a ≤ c) (hb : b ≤ c) : a + b ≤ c :=
  add_le_iff.2 ⟨ha, hb⟩

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IdemSemiring.toIsOrderedAddMonoid : IsOrderedAddMonoid α where
  add_le_add_left a b hbc c := by
    simp_rw [add_eq_sup]
    grw [hbc]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IdemSemiring.toCanonicallyOrderedAdd : CanonicallyOrderedAdd α where
  exists_add_of_le h := ⟨_, h.add_eq_right.symm⟩
  le_add_self a b := add_eq_left_iff_le.1 <| by rw [add_assoc, add_idem]
  le_self_add a b := add_eq_right_iff_le.1 <| by rw [← add_assoc, add_idem]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IdemSemiring.toMulLeftMono : MulLeftMono α where
  elim a b c hbc := add_eq_left_iff_le.1 <| by rw [← mul_add, hbc.add_eq_left]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IdemSemiring.toMulRightMono : MulRightMono α where
  elim a b c hbc := add_eq_left_iff_le.1 <| by rw [← add_mul, hbc.add_eq_left]

end IdemSemiring

section KleeneAlgebra

variable [KleeneAlgebra α] {a b c : α}

@[simp]
/-
**one_le_kstar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_kstar : 1 <= a∗
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `KleeneAlgebra.one_le_kstar`：∀ {α : Type u_5} [self : KleeneAlgebra α] (a
 : α), 1 ≤ KStar.kstar a
-/
theorem one_le_kstar : 1 ≤ a∗ :=
  KleeneAlgebra.one_le_kstar _
/-
**mul_kstar_le_kstar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_kstar_le_kstar : a * a∗ <= a∗
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `KleeneAlgebra.mul_kstar_le_kstar`：∀ {α : Type u_5} [self : KleeneAlgebra
 α] (a : α), a * KStar.kstar a ≤ KStar.kstar a
-/
theorem mul_kstar_le_kstar : a * a∗ ≤ a∗ :=
  KleeneAlgebra.mul_kstar_le_kstar _
/-
**kstar_mul_le_kstar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_mul_le_kstar : a∗ * a <= a∗
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `KleeneAlgebra.kstar_mul_le_kstar`：∀ {α : Type u_5} [self : KleeneAlgebra
 α] (a : α), KStar.kstar a * a ≤ KStar.kstar a
-/
theorem kstar_mul_le_kstar : a∗ * a ≤ a∗ :=
  KleeneAlgebra.kstar_mul_le_kstar _
/-
**mul_kstar_le_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_kstar_le_self : b * a <= b -> b * a∗ <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `KleeneAlgebra.mul_kstar_le_self`：∀ {α : Type u_5} [self : KleeneAlgebra 
α] (a b : α), b * a ≤ b → b * KStar.kstar a ≤ b
-/
theorem mul_kstar_le_self : b * a ≤ b → b * a∗ ≤ b :=
  KleeneAlgebra.mul_kstar_le_self _ _
/-
**kstar_mul_le_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_mul_le_self : a * b <= b -> a∗ * b <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `KleeneAlgebra.kstar_mul_le_self`：∀ {α : Type u_5} [self : KleeneAlgebra 
α] (a b : α), a * b ≤ b → KStar.kstar a * b ≤ b
-/
theorem kstar_mul_le_self : a * b ≤ b → a∗ * b ≤ b :=
  KleeneAlgebra.kstar_mul_le_self _ _
/-
**mul_kstar_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_kstar_le (hb : b <= c) (ha : c * a <= c) : b * a∗ <= c
参数：hb : b <= c；ha : c * a <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IdemSemiring.toMulLeftMono`：∀ {α : Type u_1} [inst : IdemSemiring α], Mu
lLeftMono α
· 使用定理 `IdemSemiring.toMulRightMono`：∀ {α : Type u_1} [inst : IdemSemiring α], M
ulRightMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_kstar_le_self`：mul_kstar_le_self : b * a <= b -> b * a∗ <= b
-/
theorem mul_kstar_le (hb : b ≤ c) (ha : c * a ≤ c) : b * a∗ ≤ c := by grw [hb, mul_kstar_le_self ha]
/-
**kstar_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_mul_le (hb : b <= c) (ha : a * c <= c) : a∗ * b <= c
参数：hb : b <= c；ha : a * c <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IdemSemiring.toMulLeftMono`：∀ {α : Type u_1} [inst : IdemSemiring α], Mu
lLeftMono α
· 使用定理 `IdemSemiring.toMulRightMono`：∀ {α : Type u_1} [inst : IdemSemiring α], M
ulRightMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `kstar_mul_le_self`：kstar_mul_le_self : a * b <= b -> a∗ * b <= b
-/
theorem kstar_mul_le (hb : b ≤ c) (ha : a * c ≤ c) : a∗ * b ≤ c := by grw [hb, kstar_mul_le_self ha]
/-
**kstar_le_of_mul_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_le_of_mul_le_left (hb : 1 <= b) : b * a <= b -> a∗ <= b
参数：hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_kstar_le`：mul_kstar_le (hb : b <= c) (ha : c * a <= c) : b * a∗ <= c
-/
theorem kstar_le_of_mul_le_left (hb : 1 ≤ b) : b * a ≤ b → a∗ ≤ b := by
  simpa using mul_kstar_le hb
/-
**kstar_le_of_mul_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_le_of_mul_le_right (hb : 1 <= b) : a * b <= b -> a∗ <= b
参数：hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `kstar_mul_le`：kstar_mul_le (hb : b <= c) (ha : a * c <= c) : a∗ * b <= c
-/
theorem kstar_le_of_mul_le_right (hb : 1 ≤ b) : a * b ≤ b → a∗ ≤ b := by
  simpa using kstar_mul_le hb

@[simp]
/-
**le_kstar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_kstar : a <= a∗
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `IdemSemiring.toMulRightMono`：∀ {α : Type u_1} [inst : IdemSemiring α], M
ulRightMono α
· 使用定理 `one_le_kstar`：one_le_kstar : 1 <= a∗
· 使用定理 `kstar_mul_le_kstar`：kstar_mul_le_kstar : a∗ * a <= a∗
-/
theorem le_kstar : a ≤ a∗ :=
  le_trans (le_mul_of_one_le_left' one_le_kstar) kstar_mul_le_kstar

@[gcongr, mono]
/-
**kstar_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_mono : Monotone (KStar.kstar : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `kstar_le_of_mul_le_left`：kstar_le_of_mul_le_left (hb : 1 <= b) : b * a <
= b -> a∗ <= b
· 使用定理 `one_le_kstar`：one_le_kstar : 1 <= a∗
· 使用定理 `kstar_mul_le`：kstar_mul_le (hb : b <= c) (ha : a * c <= c) : a∗ * b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_kstar`：le_kstar : a <= a∗
· 使用定理 `mul_kstar_le_kstar`：mul_kstar_le_kstar : a * a∗ <= a∗
-/
theorem kstar_mono : Monotone (KStar.kstar : α → α) :=
  fun _ _ h ↦
    kstar_le_of_mul_le_left one_le_kstar <| kstar_mul_le (h.trans le_kstar) <| mul_kstar_le_kstar

@[simp]
/-
**kstar_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_eq_one : a∗ = 1 ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_kstar`：le_kstar : a <= a∗
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `one_le_kstar`：one_le_kstar : 1 <= a∗
· 使用定理 `kstar_le_of_mul_le_left`：kstar_le_of_mul_le_left (hb : 1 <= b) : b * a <
= b -> a∗ <= b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem kstar_eq_one : a∗ = 1 ↔ a ≤ 1 :=
  ⟨le_kstar.trans_eq,
    fun h ↦ one_le_kstar.antisymm' <| kstar_le_of_mul_le_left le_rfl <| by rwa [one_mul]⟩
/-
**kstar_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : KleeneAlgebra α], KStar.kstar 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `kstar_eq_one`：kstar_eq_one : a∗ = 1 ↔ a <= 1
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `IdemSemiring.toCanonicallyOrderedAdd`：∀ {α : Type u_1} [inst : IdemSemir
ing α], CanonicallyOrderedAdd α
-/
@[simp] lemma kstar_zero : (0 : α)∗ = 1 := kstar_eq_one.2 zero_le

@[simp]
/-
**kstar_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_one : (1 : α)∗ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `kstar_eq_one`：kstar_eq_one : a∗ = 1 ↔ a <= 1
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem kstar_one : (1 : α)∗ = 1 :=
  kstar_eq_one.2 le_rfl

@[simp]
/-
**kstar_mul_kstar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_mul_kstar (a : α) : a∗ * a∗ = a∗
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `mul_kstar_le`：mul_kstar_le (hb : b <= c) (ha : c * a <= c) : b * a∗ <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `kstar_mul_le_kstar`：kstar_mul_le_kstar : a∗ * a <= a∗
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `IdemSemiring.toMulRightMono`：∀ {α : Type u_1} [inst : IdemSemiring α], M
ulRightMono α
· 使用定理 `one_le_kstar`：one_le_kstar : 1 <= a∗
-/
theorem kstar_mul_kstar (a : α) : a∗ * a∗ = a∗ :=
  (mul_kstar_le le_rfl <| kstar_mul_le_kstar).antisymm <| le_mul_of_one_le_left' one_le_kstar

@[simp]
/-
**kstar_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_eq_self : a∗ = a ↔ a * a = a ∧ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `kstar_mul_kstar`：kstar_mul_kstar (a : α) : a∗ * a∗ = a∗
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `one_le_kstar`：one_le_kstar : 1 <= a∗
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `kstar_le_of_mul_le_left`：kstar_le_of_mul_le_left (hb : 1 <= b) : b * a <
= b -> a∗ <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_kstar`：le_kstar : a <= a∗
-/
theorem kstar_eq_self : a∗ = a ↔ a * a = a ∧ 1 ≤ a :=
  ⟨fun h ↦ ⟨by rw [← h, kstar_mul_kstar], one_le_kstar.trans_eq h⟩,
    fun h ↦ (kstar_le_of_mul_le_left h.2 h.1.le).antisymm le_kstar⟩

@[simp]
/-
**kstar_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kstar_idem (a : α) : a∗∗ = a∗
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `kstar_eq_self`：kstar_eq_self : a∗ = a ↔ a * a = a ∧ 1 <= a
· 使用定理 `kstar_mul_kstar`：kstar_mul_kstar (a : α) : a∗ * a∗ = a∗
· 使用定理 `one_le_kstar`：one_le_kstar : 1 <= a∗
-/
theorem kstar_idem (a : α) : a∗∗ = a∗ :=
  kstar_eq_self.2 ⟨kstar_mul_kstar _, one_le_kstar⟩

@[simp]
/-
**pow_le_kstar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : KleeneAlgebra α] {a : α} {n : ℕ}, a ^ n ≤ KStar.k
star a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_le_kstar : ∀ {n : ℕ}, a ^ n ≤ a∗
  | 0 => (pow_zero _).trans_le one_le_kstar
  | n + 1 => by grw [pow_succ', pow_le_kstar, mul_kstar_le_kstar]
/-
**one_add_mul_kstar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_add_mul_kstar : 1 + a * a∗ = a∗
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_le_iff`：add_le_iff : a + b <= c ↔ a <= c ∧ b <= c
· 使用定理 `one_le_kstar`：one_le_kstar : 1 <= a∗
· 使用定理 `mul_kstar_le_kstar`：mul_kstar_le_kstar : a * a∗ <= a∗
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IdemSemiring.toIsOrderedAddMonoid`：∀ {α : Type u_1} [inst : IdemSemiring
 α], IsOrderedAddMonoid α
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
· 使用定理 `IdemSemiring.toMulLeftMono`：∀ {α : Type u_1} [inst : IdemSemiring α], Mu
lLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `kstar_mul_le_self`：kstar_mul_le_self : a * b <= b -> a∗ * b <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem one_add_mul_kstar : 1 + a * a∗ = a∗ := by
  have h : 1 + a * a∗ ≤ a∗ := by
    rw [add_le_iff]
    exact ⟨one_le_kstar, mul_kstar_le_kstar⟩
  apply le_antisymm h
  suffices 1 + a * (1 + a * a∗) ≤ 1 + a * a∗ by
    rw [add_le_iff] at this
    nth_rw 1 [← mul_one a∗]
    exact (mul_right_mono this.1).trans (kstar_mul_le_self this.2)
  apply add_le_add_right (mul_right_mono h)
/-
**one_add_kstar_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_add_kstar_mul : 1 + a∗ * a = a∗
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_le_iff`：add_le_iff : a + b <= c ↔ a <= c ∧ b <= c
· 使用定理 `one_le_kstar`：one_le_kstar : 1 <= a∗
· 使用定理 `kstar_mul_le_kstar`：kstar_mul_le_kstar : a∗ * a <= a∗
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IdemSemiring.toIsOrderedAddMonoid`：∀ {α : Type u_1} [inst : IdemSemiring
 α], IsOrderedAddMonoid α
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
· 使用定理 `IdemSemiring.toMulRightMono`：∀ {α : Type u_1} [inst : IdemSemiring α], M
ulRightMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_kstar_le_self`：mul_kstar_le_self : b * a <= b -> b * a∗ <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem one_add_kstar_mul : 1 + a∗ * a = a∗ := by
  have h : 1 + a∗ * a ≤ a∗ := by
    rw [add_le_iff]
    exact ⟨one_le_kstar, kstar_mul_le_kstar⟩
  apply le_antisymm h
  suffices 1 + (1 + a∗ * a) * a ≤ 1 + a∗ * a by
    rw [add_le_iff] at this
    nth_rw 1 [← one_mul a∗]
    exact (mul_left_mono this.1).trans (mul_kstar_le_self this.2)
  apply add_le_add_right (mul_left_mono h)

end KleeneAlgebra

namespace Prod

/-
**Prod.instIdemSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instIdemSemiring [IdemSemiring α] [IdemSemiring β] : IdemSemiring (α × β) 
where add_eq_sup _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIdemSemiring [IdemSemiring α] [IdemSemiring β] : IdemSemiring (α × β) where
  add_eq_sup _ _ := Prod.ext (add_eq_sup _ _) (add_eq_sup _ _)
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IdemCommSemiring α] [IdemCommSemiring β] : IdemCommSemiring (α × β) where
  __ := Prod.instCommSemiring
  __ := Prod.instIdemSemiring

variable [KleeneAlgebra α] [KleeneAlgebra β]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : KleeneAlgebra (α × β) where
  kstar a := (a.1∗, a.2∗)
  one_le_kstar _ := ⟨one_le_kstar, one_le_kstar⟩
  mul_kstar_le_kstar _ := ⟨mul_kstar_le_kstar, mul_kstar_le_kstar⟩
  kstar_mul_le_kstar _ := ⟨kstar_mul_le_kstar, kstar_mul_le_kstar⟩
  mul_kstar_le_self _ _ := And.imp mul_kstar_le_self mul_kstar_le_self
  kstar_mul_le_self _ _ := And.imp kstar_mul_le_self kstar_mul_le_self
/-
**Prod.kstar_def** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：kstar_def (a : α × β) : a∗ = (a.1∗, a.2∗)
参数：a : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kstar_def (a : α × β) : a∗ = (a.1∗, a.2∗) :=
  rfl

@[simp]
/-
**Prod.fst_kstar** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_kstar (a : α × β) : a∗.1 = a.1∗
参数：a : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_kstar (a : α × β) : a∗.1 = a.1∗ :=
  rfl

@[simp]
/-
**Prod.snd_kstar** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_kstar (a : α × β) : a∗.2 = a.2∗
参数：a : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_kstar (a : α × β) : a∗.2 = a.2∗ :=
  rfl

end Prod

namespace Pi

/-
**Pi.instIdemSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instIdemSemiring [forall i, IdemSemiring (π i)] : IdemSemiring (forall i, 
π i) where add_eq_sup _ _
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIdemSemiring [∀ i, IdemSemiring (π i)] : IdemSemiring (∀ i, π i) where
  add_eq_sup _ _ := funext fun _ ↦ add_eq_sup _ _
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, IdemCommSemiring (π i)] : IdemCommSemiring (∀ i, π i) where
  __ := Pi.commSemiring
  __ := Pi.instIdemSemiring

variable [∀ i, KleeneAlgebra (π i)]
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : KleeneAlgebra (∀ i, π i) where
  kstar a i := (a i)∗
  one_le_kstar _ _ := one_le_kstar
  mul_kstar_le_kstar _ _ := mul_kstar_le_kstar
  kstar_mul_le_kstar _ _ := kstar_mul_le_kstar
  mul_kstar_le_self _ _ h _ := mul_kstar_le_self (h _)
  kstar_mul_le_self _ _ h _ := kstar_mul_le_self (h _)

@[push ←]
/-
**Pi.kstar_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：kstar_def (a : forall i, π i) : a∗ = fun i => (a i)∗
参数：a : forall i, π i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kstar_def (a : ∀ i, π i) : a∗ = fun i ↦ (a i)∗ :=
  rfl

@[simp]
/-
**Pi.kstar_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：kstar_apply (a : forall i, π i) (i : ι) : a∗ i = (a i)∗
参数：a : forall i, π i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kstar_apply (a : ∀ i, π i) (i : ι) : a∗ i = (a i)∗ :=
  rfl

end Pi

namespace Function.Injective

-- See note [reducible non-instances]
/-- Pullback an `IdemSemiring` instance along an injective function. -/
/-
**Function.Injective.idemSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`
。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : IdemSemiring α] →       [i
nst_1 : LE β] →         [inst_2 : LT β] →           [inst_3 : Zero β] →         
    [inst_4 : One β] →               [inst_5 : Add β] →                 [inst_6 
: Mul β] →                   [inst_7 : Pow β ℕ] →                     [inst_8 : 
SMul ℕ β] →                       [inst_9 : NatCast β] →                        
 [inst_10 : Max β] →                           [inst_11 : Bot β] →              
               (f : β → α) →                               Function.Injective f 
→                                 (∀ {x y : β}, f x ≤ f y ↔ x ≤ y) →            
                       (∀ {x y : β}, f x < f y ↔ x < y) →                       
              f 0 = 0 →                                       f 1 = 1 →         
                                (∀ (x y : β), f (x + y) = f x + f y) →          
                                 (∀ (x y : β), f (x * y) = f x * f y) →         
                                    (∀ (n : ℕ) (x : β), f (n • x) = n • f x) →  
                                             (∀ (x : β) (n : ℕ), f (x ^ n) = f x
 ^ n) →                                                 (∀ (n : ℕ), f ↑n = ↑n) →
                                                   (∀ (a b : β), f (a ⊔ b) = f a
 ⊔ f b) → f ⊥ = ⊥ → IdemSemiring β
参数：f : β → α；∀ {x y : β}, f x ≤ f y ↔ x ≤ y；∀ {x y : β}, f x < f y ↔ x < y；∀ (x 
y : β), f (x + y) = f x + f y；∀ (x y : β), f (x * y) = f x * f y；∀ (n : ℕ) (x : 
β), f (n • x) = n • f x；∀ (x : β) (n : ℕ), f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n =
 ↑n；∀ (a b : β), f (a ⊔ b) = f a ⊔ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback an `IdemSemiring` instance along an injective function.
-/
protected abbrev idemSemiring [IdemSemiring α] [LE β] [LT β] [Zero β] [One β]
    [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β] [NatCast β] [Max β] [Bot β] (f : β → α)
    (hf : Injective f) (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemSemiring β where
  __ := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.semilatticeSup f le lt sup
  add_eq_sup a b := hf <| by rw [sup, add, add_eq_sup]
  bot_le a := le.1 <| bot.trans_le bot_le

-- See note [reducible non-instances]
/-- Pullback an `IdemCommSemiring` instance along an injective function. -/
/-
**Function.Injective.idemCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inject
ive`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : IdemCommSemiring α] →     
  [inst_1 : LE β] →         [inst_2 : LT β] →           [inst_3 : Zero β] →     
        [inst_4 : One β] →               [inst_5 : Add β] →                 [ins
t_6 : Mul β] →                   [inst_7 : Pow β ℕ] →                     [inst_
8 : SMul ℕ β] →                       [inst_9 : NatCast β] →                    
     [inst_10 : Max β] →                           [inst_11 : Bot β] →          
                   (f : β → α) →                               Function.Injectiv
e f →                                 (∀ {x y : β}, f x ≤ f y ↔ x ≤ y) →        
                           (∀ {x y : β}, f x < f y ↔ x < y) →                   
                  f 0 = 0 →                                       f 1 = 1 →     
                                    (∀ (x y : β), f (x + y) = f x + f y) →      
                                     (∀ (x y : β), f (x * y) = f x * f y) →     
                                        (∀ (n : ℕ) (x : β), f (n • x) = n • f x)
 →                                               (∀ (x : β) (n : ℕ), f (x ^ n) =
 f x ^ n) →                                                 (∀ (n : ℕ), f ↑n = ↑
n) →                                                   (∀ (a b : β), f (a ⊔ b) =
 f a ⊔ f b) → f ⊥ = ⊥ → IdemCommSemiring β
参数：f : β → α；∀ {x y : β}, f x ≤ f y ↔ x ≤ y；∀ {x y : β}, f x < f y ↔ x < y；∀ (x 
y : β), f (x + y) = f x + f y；∀ (x y : β), f (x * y) = f x * f y；∀ (n : ℕ) (x : 
β), f (n • x) = n • f x；∀ (x : β) (n : ℕ), f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n =
 ↑n；∀ (a b : β), f (a ⊔ b) = f a ⊔ f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IdemSemiring.add_eq_sup`：∀ {α : Type u_5} [self : IdemSemiring α] (a b :
 α), a + b = a ⊔ b

--- 原说明 ---
Pullback an `IdemCommSemiring` instance along an injective function.
-/
protected abbrev idemCommSemiring [IdemCommSemiring α] [LE β] [LT β] [Zero β] [One β]
    [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β] [NatCast β] [Max β] [Bot β] (f : β → α)
    (hf : Injective f) (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemCommSemiring β where
  __ := hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.idemSemiring f le lt zero one add mul nsmul npow natCast sup bot

-- See note [reducible non-instances]
/-- Pullback a `KleeneAlgebra` instance along an injective function. -/
/-
**Function.Injective.kleeneAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective
`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : KleeneAlgebra α] →       [
inst_1 : LE β] →         [inst_2 : LT β] →           [inst_3 : Zero β] →        
     [inst_4 : One β] →               [inst_5 : Add β] →                 [inst_6
 : Mul β] →                   [inst_7 : Pow β ℕ] →                     [inst_8 :
 SMul ℕ β] →                       [inst_9 : NatCast β] →                       
  [inst_10 : Max β] →                           [inst_11 : Bot β] →             
                [inst_12 : KStar β] →                               (f : β → α) 
→                                 Function.Injective f →                        
           (∀ {x y : β}, f x ≤ f y ↔ x ≤ y) →                                   
  (∀ {x y : β}, f x < f y ↔ x < y) →                                       f 0 =
 0 →                                         f 1 = 1 →                          
                 (∀ (x y : β), f (x + y) = f x + f y) →                         
                    (∀ (x y : β), f (x * y) = f x * f y) →                      
                         (∀ (n : ℕ) (x : β), f (n • x) = n • f x) →             
                                    (∀ (x : β) (n : ℕ), f (x ^ n) = f x ^ n) →  
                                                 (∀ (n : ℕ), f ↑n = ↑n) →       
                                              (∀ (a b : β), f (a ⊔ b) = f a ⊔ f 
b) →                                                       f ⊥ = ⊥ →            
                                             (∀ (a : β), f (KStar.kstar a) = KSt
ar.kstar (f a)) →                                                           Klee
neAlgebra β
参数：f : β → α；∀ {x y : β}, f x ≤ f y ↔ x ≤ y；∀ {x y : β}, f x < f y ↔ x < y；∀ (x 
y : β), f (x + y) = f x + f y；∀ (x y : β), f (x * y) = f x * f y；∀ (n : ℕ) (x : 
β), f (n • x) = n • f x；∀ (x : β) (n : ℕ), f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n =
 ↑n；∀ (a b : β), f (a ⊔ b) = f a ⊔ f b；∀ (a : β), f (KStar.kstar a) = KStar.ksta
r (f a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a `KleeneAlgebra` instance along an injective function.
-/
protected abbrev kleeneAlgebra [KleeneAlgebra α] [LE β] [LT β] [Zero β] [One β]
    [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β] [NatCast β] [Max β] [Bot β] [KStar β] (f : β → α)
    (hf : Injective f) (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥)
    (kstar : ∀ a, f a∗ = (f a)∗) : KleeneAlgebra β where
  __ := hf.idemSemiring f le lt zero one add mul nsmul npow natCast sup bot
  one_le_kstar a := by
    rw [← le, one, kstar]
    exact one_le_kstar
  mul_kstar_le_kstar a := by
    rw [← le, mul, kstar]
    exact mul_kstar_le_kstar
  kstar_mul_le_kstar a := by
    rw [← le, mul, kstar]
    exact kstar_mul_le_kstar
  mul_kstar_le_self a b h := by
    rw [← le, mul, kstar]
    rw [← le, mul] at h
    exact mul_kstar_le_self h
  kstar_mul_le_self a b h := by
    rw [← le, mul, kstar]
    rw [← le, mul] at h
    exact kstar_mul_le_self h

end Function.Injective

