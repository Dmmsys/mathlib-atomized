/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Conv
public import Batteries.Tactic.SeqFocus

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `GroupWithZero` and `CommGroupWithZero`.
To reduce import dependencies, the type-classes themselves are in
`Algebra.GroupWithZero.Defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

open Function

variable {M₀ G₀ : Type*}

section

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

/-
**left_ne_zero_of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_ne_zero_of_mul : a * b != 0 -> a != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `mul_eq_zero_of_left`：mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) :
 a * b = 0
-/
theorem left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 :=
  mt fun h => mul_eq_zero_of_left h b
/-
**right_ne_zero_of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_ne_zero_of_mul : a * b != 0 -> b != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
-/
theorem right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 :=
  mt (mul_eq_zero_of_right a)
/-
**ne_zero_and_ne_zero_of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_zero_and_ne_zero_of_mul (h : a * b != 0) : a != 0 ∧ b != 0
参数：h : a * b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
-/
theorem ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
/-
**mul_eq_zero_of_ne_zero_imp_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a != 0 -> b = 0) : a * 
b = 0
参数：h : a != 0 -> b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) : a * b = 0 := by
  have : Decidable (a = 0) := Classical.propDecidable (a = 0)
  exact if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

/-- To match `one_mul_eq_id`. -/
/-
**zero_mul_eq_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_mul_eq_const : ((0 : M₀) * ·) = Function.const _ 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
To match `one_mul_eq_id`.
-/
theorem zero_mul_eq_const : ((0 : M₀) * ·) = Function.const _ 0 :=
  funext zero_mul

/-- To match `mul_one_eq_id`. -/
/-
**mul_zero_eq_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_zero_eq_const : (· * (0 : M₀)) = Function.const _ 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
To match `mul_one_eq_id`.
-/
theorem mul_zero_eq_const : (· * (0 : M₀)) = Function.const _ 0 :=
  funext mul_zero

end MulZeroClass

section Mul

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

/-
**eq_zero_of_mul_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0
参数：h : a * a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
-/
theorem eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 :=
  (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id
/-
**mul_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  mt eq_zero_or_eq_zero_of_mul_eq_zero <| not_or.mpr ⟨ha, hb⟩

end Mul

namespace NeZero

/-
**NeZero.mul** 是 Mathlib 中的一个实例，位于命名空间 `NeZero`。
形式化陈述：mul [Zero M₀] [Mul M₀] [NoZeroDivisors M₀] {x y : M₀} [NeZero x] [NeZero y
] : NeZero (x * y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
instance mul [Zero M₀] [Mul M₀] [NoZeroDivisors M₀] {x y : M₀} [NeZero x] [NeZero y] :
    NeZero (x * y) :=
  ⟨mul_ne_zero out out⟩

end NeZero

end

section

variable [MulZeroOneClass M₀]

/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
/-
**eq_zero_of_zero_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0
参数：h : (0 : M₀) = 1；a : M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
In a monoid with zero, if zero equals one, then zero is the only element.
-/
theorem eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 := by
  rw [← mul_one a, ← h, mul_zero]

/-- In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitionally equal. -/
@[instance_reducible]
/-
**uniqueOfZeroEqOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uniqueOfZeroEqOne (h : (0 : M₀) = 1) : Unique M₀ where default
参数：h : (0 : M₀) = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_zero_eq_one`：eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M
₀) : a = 0

--- 原说明 ---
In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitiona
lly equal.
-/
def uniqueOfZeroEqOne (h : (0 : M₀) = 1) : Unique M₀ where
  default := 0
  uniq := eq_zero_of_zero_eq_one h

/-- In a monoid with zero, zero equals one if and only if all elements of that semiring
are equal. -/
/-
**subsingleton_iff_zero_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
In a monoid with zero, zero equals one if and only if all elements of that semir
ing
are equal.
-/
theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀ :=
  ⟨fun h => haveI := uniqueOfZeroEqOne h; inferInstance, fun h => @Subsingleton.elim _ h _ _⟩

alias ⟨subsingleton_of_zero_eq_one, _⟩ := subsingleton_iff_zero_eq_one
/-
**eq_of_zero_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b
参数：h : (0 : M₀) = 1；a b : M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `subsingleton_of_zero_eq_one`：∀ {M₀ : Type u_1} [inst : MulZeroOneClass M
₀], 0 = 1 → Subsingleton M₀
-/
theorem eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
  @Subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b

/-- In a monoid with zero, either zero and one are nonequal, or zero is the only element. -/
/-
**zero_ne_one_or_forall_eq_0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_ne_one_or_forall_eq_0 : (0 : M₀) != 1 ∨ forall a : M₀, a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_or_of_imp`：not_or_of_imp : (a -> b) -> ¬a ∨ b
· 使用定理 `eq_zero_of_zero_eq_one`：eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M
₀) : a = 0

--- 原说明 ---
In a monoid with zero, either zero and one are nonequal, or zero is the only ele
ment.
-/
theorem zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ ∀ a : M₀, a = 0 :=
  not_or_of_imp eq_zero_of_zero_eq_one

end

section

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

/-
**left_ne_zero_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_ne_zero_of_mul_eq_one (h : a * b = 1) : a != 0
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用引理 `ne_zero_of_eq_one`：ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h
 : a = 1) : a != 0
-/
theorem left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
  left_ne_zero_of_mul <| ne_zero_of_eq_one h
/-
**right_ne_zero_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_ne_zero_of_mul_eq_one (h : a * b = 1) : b != 0
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用引理 `ne_zero_of_eq_one`：ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h
 : a = 1) : a != 0
-/
theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
  right_ne_zero_of_mul <| ne_zero_of_eq_one h

end

section Nilpotent

variable {R S : Type*} {x y : R}

/-- An element is said to be nilpotent if some natural-number-power of it equals zero.

Note that we require only the bare minimum assumptions for the definition to make sense. Even
`MonoidWithZero` is too strong since nilpotency is important in the study of rings that are only
power-associative. -/
/-
**IsNilpotent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsNilpotent [Zero R] [Pow R Nat] (x : R) : Prop
参数：x : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element is said to be nilpotent if some natural-number-power of it equals zer
o.

Note that we require only the bare minimum assumptions for the definition to mak
e sense. Even
`MonoidWithZero` is too strong since nilpotency is important in the study of rin
gs that are only
power-associative.
-/
def IsNilpotent [Zero R] [Pow R ℕ] (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0
/-
**IsNilpotent.mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.mk [Zero R] [Pow R Nat] (x : R) (n : Nat) (e : x ^ n = 0) : Is
Nilpotent x
参数：x : R；n : Nat；e : x ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsNilpotent.mk [Zero R] [Pow R ℕ] (x : R) (n : ℕ) (e : x ^ n = 0) : IsNilpotent x :=
  ⟨n, e⟩
/-
**isNilpotent_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_3} {x : R} [inst : Zero R] [inst_1 : Pow R ℕ] [Subsingleton 
R], IsNilpotent x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
@[simp] lemma isNilpotent_of_subsingleton [Zero R] [Pow R ℕ] [Subsingleton R] : IsNilpotent x :=
  ⟨0, Subsingleton.elim _ _⟩
/-
**IsNilpotent.zero** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：∀ {R : Type u_3} [inst : MonoidWithZero R], IsNilpotent 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
@[simp] theorem IsNilpotent.zero [MonoidWithZero R] : IsNilpotent (0 : R) :=
  ⟨1, pow_one 0⟩
/-
**not_isNilpotent_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isNilpotent_one [MonoidWithZero R] [Nontrivial R] : ¬ IsNilpotent (1 :
 R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem not_isNilpotent_one [MonoidWithZero R] [Nontrivial R] :
    ¬ IsNilpotent (1 : R) := fun ⟨_, H⟩ ↦ zero_ne_one (H.symm.trans (one_pow _))
/-
**IsNilpotent.pow_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNilpotent.pow_succ (n : Nat) {S : Type*} [MonoidWithZero S] {x : S} (hx 
: IsNilpotent x) : IsNilpotent (x ^ n.succ)
参数：n : Nat；hx : IsNilpotent x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma IsNilpotent.pow_succ (n : ℕ) {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) : IsNilpotent (x ^ n.succ) :=
  have ⟨N, hN⟩ := hx
  ⟨N, by rw [← pow_mul, Nat.succ_mul, pow_add, hN, mul_zero]⟩
/-
**IsNilpotent.of_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.of_pow [MonoidWithZero R] {x : R} {m : Nat} (h : IsNilpotent (
x ^ m)) : IsNilpotent x
参数：h : IsNilpotent (x ^ m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem IsNilpotent.of_pow [MonoidWithZero R] {x : R} {m : ℕ}
    (h : IsNilpotent (x ^ m)) : IsNilpotent x :=
  have ⟨n, h⟩ := h
  ⟨m * n, by rw [← h, pow_mul x m n]⟩
/-
**IsNilpotent.pow_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNilpotent.pow_of_pos {n} {S : Type*} [MonoidWithZero S] {x : S} (hx : Is
Nilpotent x) (hn : n != 0) : IsNilpotent (x ^ n)
参数：hx : IsNilpotent x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsNilpotent.pow_succ`：IsNilpotent.pow_succ (n : Nat) {S : Type*} [Monoid
WithZero S] {x : S} (hx : IsNilpotent x) : IsNilpotent (x ^ n.succ)
-/
lemma IsNilpotent.pow_of_pos {n} {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) (hn : n ≠ 0) : IsNilpotent (x ^ n) := by
  cases n with
  | zero => contradiction
  | succ => exact IsNilpotent.pow_succ _ hx

@[simp]
/-
**IsNilpotent.pow_iff_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNilpotent.pow_iff_pos {n} {S : Type*} [MonoidWithZero S] {x : S} (hn : n
 != 0) : IsNilpotent (x ^ n) ↔ IsNilpotent x
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNilpotent.of_pow`：IsNilpotent.of_pow [MonoidWithZero R] {x : R} {m : N
at} (h : IsNilpotent (x ^ m)) : IsNilpotent x
· 使用引理 `IsNilpotent.pow_of_pos`：IsNilpotent.pow_of_pos {n} {S : Type*} [MonoidWi
thZero S] {x : S} (hx : IsNilpotent x) (hn : n != 0) : IsNilpotent (x ^ n)
-/
lemma IsNilpotent.pow_iff_pos {n} {S : Type*} [MonoidWithZero S] {x : S} (hn : n ≠ 0) :
    IsNilpotent (x ^ n) ↔ IsNilpotent x :=
  ⟨of_pow, (pow_of_pos · hn)⟩

/-- A structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
@[mk_iff]
/-
**IsReduced** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_5) → [Zero R] → [Pow R ℕ] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure that has zero and pow is reduced if it has no nonzero nilpotent elem
ents.
-/
class IsReduced (R : Type*) [Zero R] [Pow R ℕ] : Prop where
  /-- A reduced structure has no nonzero nilpotent elements. -/
  eq_zero : ∀ x : R, IsNilpotent x → x = 0
/-
**eq_zero_of_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsReduced R] {n : Nat} (h : x
 ^ n = 0) : x = 0
参数：h : x ^ n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsReduced.eq_zero`：∀ {R : Type u_5} {inst : Zero R} {inst_1 : Pow R ℕ} [
self : IsReduced R] (x : R), IsNilpotent x → x = 0
-/
theorem eq_zero_of_pow_eq_zero [Zero R] [Pow R ℕ] [IsReduced R] {n : ℕ} (h : x ^ n = 0) :
    x = 0 := IsReduced.eq_zero x ⟨n, h⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) isReduced_of_subsingleton [Zero R] [Pow R ℕ] [Subsingleton R] :
    IsReduced R :=
  ⟨fun _ _ => Subsingleton.elim ..⟩
/-
**IsNilpotent.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced R] (h : IsNilpotent x)
 : x = 0
参数：h : IsNilpotent x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsReduced.eq_zero`：∀ {R : Type u_5} {inst : Zero R} {inst_1 : Pow R ℕ} [
self : IsReduced R] (x : R), IsNilpotent x → x = 0
-/
theorem IsNilpotent.eq_zero [Zero R] [Pow R ℕ] [IsReduced R] (h : IsNilpotent x) : x = 0 :=
  IsReduced.eq_zero x h

@[simp]
/-
**isNilpotent_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNilpotent_iff_eq_zero [MonoidWithZero R] [IsReduced R] : IsNilpotent x ↔
 x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `IsNilpotent.zero`：∀ {R : Type u_3} [inst : MonoidWithZero R], IsNilpoten
t 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNilpotent_iff_eq_zero [MonoidWithZero R] [IsReduced R] : IsNilpotent x ↔ x = 0 :=
  ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩
/-
**exists_isNilpotent_of_not_isReduced** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_isNilpotent_of_not_isReduced {R : Type*} [Zero R] [Pow R Nat] (h : 
¬IsReduced R) : exists x : R, x != 0 ∧ IsNilpotent x
参数：h : ¬IsReduced R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma exists_isNilpotent_of_not_isReduced {R : Type*} [Zero R] [Pow R ℕ] (h : ¬IsReduced R) :
    ∃ x : R, x ≠ 0 ∧ IsNilpotent x := by
  simpa [isReduced_iff, not_forall, and_comm] using h

end Nilpotent

section MonoidWithZero
variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

/-
**zero_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
参数：_ : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
@[simp] lemma zero_pow : ∀ {n : ℕ}, n ≠ 0 → (0 : M₀) ^ n = 0
  | n + 1, _ => by rw [pow_succ, mul_zero]
/-
**zero_pow_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_pow_eq (n : Nat) : (0 : M₀) ^ n = if n = 0 then 1 else 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
-/
lemma zero_pow_eq (n : ℕ) : (0 : M₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, pow_zero]
  · rw [zero_pow h]
/-
**zero_pow_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_pow_eq_one₀ [Nontrivial M₀] : (0 : M₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_pow_eq, one_ne_zero.ite_eq_left_iff]
/-
**pow_eq_zero_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {m n : ℕ}, m ≤ n → a
 ^ m = 0 → a ^ n = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_eq_zero_of_le : ∀ {m n}, m ≤ n → a ^ m = 0 → a ^ n = 0
  | _, _, Nat.le.refl, ha => ha
  | _, _, Nat.le.step hmn, ha => by rw [pow_succ, pow_eq_zero_of_le hmn ha, zero_mul]
/-
**ne_zero_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ne_zero_pow (hn : n != 0) (ha : a ^ n != 0) : a != 0
参数：hn : n != 0；ha : a ^ n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_zero_pow (hn : n ≠ 0) (ha : a ^ n ≠ 0) : a ≠ 0 := by rintro rfl; exact ha <| zero_pow hn

@[simp]
/-
**zero_pow_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_pow_eq_zero [Nontrivial M₀] : (0 : M₀) ^ n = 0 ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
-/
lemma zero_pow_eq_zero [Nontrivial M₀] : (0 : M₀) ^ n = 0 ↔ n ≠ 0 :=
  ⟨by rintro h rfl; simp at h, zero_pow⟩
/-
**pow_mul_eq_zero_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_mul_eq_zero_of_le {a b : M₀} {m n : Nat} (hmn : m <= n) (h : a ^ m * b
 = 0) : a ^ n * b = 0
参数：hmn : m <= n；h : a ^ m * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pow_mul_eq_zero_of_le {a b : M₀} {m n : ℕ} (hmn : m ≤ n)
    (h : a ^ m * b = 0) : a ^ n * b = 0 := by
  rw [show n = n - m + m by lia, pow_add, mul_assoc, h]
  simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) isReduced_of_noZeroDivisors [NoZeroDivisors M₀] :
    IsReduced M₀ :=
  ⟨fun a ⟨n, ha⟩ ↦ by
    induction n with
    | zero => simpa using congr_arg (a * ·) ha
    | succ n ih => rw [pow_succ, mul_eq_zero] at ha; exact ha.elim ih id⟩

variable [IsReduced M₀]
/-
**pow_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {n : ℕ} [IsReduced M
₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
参数：a ^ n = 0 ↔ a = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma pow_eq_zero_iff (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨eq_zero_of_pow_eq_zero, (·.symm ▸ zero_pow hn)⟩
/-
**pow_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_ne_zero_iff (hn : n != 0) : a ^ n != 0 ↔ a != 0
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `pow_eq_zero_iff`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {
n : ℕ} [IsReduced M₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
-/
lemma pow_ne_zero_iff (hn : n ≠ 0) : a ^ n ≠ 0 ↔ a ≠ 0 := (pow_eq_zero_iff hn).not
/-
**pow_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
参数：n : Nat；h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
-/
lemma pow_ne_zero (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 := mt eq_zero_of_pow_eq_zero h
/-
**NeZero.pow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NeZero.pow [NeZero a] : NeZero (a ^ n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
instance NeZero.pow [NeZero a] : NeZero (a ^ n) := ⟨pow_ne_zero n NeZero.out⟩
/-
**sq_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_eq_zero_iff`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {
n : ℕ} [IsReduced M₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0 := pow_eq_zero_iff two_ne_zero

/-- A variant of `pow_eq_zero_iff` assuming `M₀` is not trivial. -/
/-
**pow_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {n : ℕ} [IsReduced M
₀] [Nontrivial M₀], a ^ n = 0 ↔ a = 0 ∧ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
A variant of `pow_eq_zero_iff` assuming `M₀` is not trivial.
-/
@[simp] lemma pow_eq_zero_iff' [Nontrivial M₀] : a ^ n = 0 ↔ a = 0 ∧ n ≠ 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero := eq_zero_of_pow_eq_zero
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero_iff := pow_eq_zero_iff
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_ne_zero_iff := pow_ne_zero_iff
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_ne_zero := pow_ne_zero
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero_iff' := pow_eq_zero_iff'
/-
**exists_right_inv_of_exists_left_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_right_inv_of_exists_left_inv {α} [MonoidWithZero α] (h : forall a :
 α, a != 0 -> exists b : α, b * a = 1) {a : α} (ha : a != 0) : exists b : α, a *
 b = 1
参数：h : forall a : α, a != 0 -> exists b : α, b * a = 1；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `Eq.trans_ne`：∀ {α : Sort u_1} {a b c : α}, a = b → b ≠ c → a ≠ c
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem exists_right_inv_of_exists_left_inv {α} [MonoidWithZero α]
    (h : ∀ a : α, a ≠ 0 → ∃ b : α, b * a = 1) {a : α} (ha : a ≠ 0) : ∃ b : α, a * b = 1 := by
  obtain _ | _ := subsingleton_or_nontrivial α
  · exact ⟨a, Subsingleton.elim _ _⟩
  obtain ⟨b, hb⟩ := h a ha
  obtain ⟨c, hc⟩ := h b (left_ne_zero_of_mul <| hb.trans_ne one_ne_zero)
  refine ⟨b, ?_⟩
  conv_lhs => rw [← one_mul (a * b), ← hc, mul_assoc, ← mul_assoc b, hb, one_mul, hc]

end MonoidWithZero

section CancelMonoidWithZero

variable {a b c : M₀}
variable [MulZeroOneClass M₀]

/-
**mul_right_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_right_eq_self₀ [IsLeftCancelMulZero M₀] : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff
/-
**mul_left_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_left_eq_self₀ [IsRightCancelMulZero M₀] : a * b = b ↔ a = 1 ∨ b = 0 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff

@[simp]
/-
**mul_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_left : a * b = a ↔ b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_left_cancel_iff`：mul_left_cancel_iff : a * b = a * c ↔ b = c
-/
theorem mul_eq_left₀ [IsLeftCancelMulZero M₀] (ha : a ≠ 0) : a * b = a ↔ b = 1 := by
  rw [Iff.comm, ← mul_right_inj' ha, mul_one]

@[simp]
/-
**mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_right : a * b = b ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_right_cancel_iff`：mul_right_cancel_iff : b * a = c * a ↔ b = c
-/
theorem mul_eq_right₀ [IsRightCancelMulZero M₀] (hb : b ≠ 0) : a * b = b ↔ a = 1 := by
  rw [Iff.comm, ← mul_left_inj' hb, one_mul]

@[simp]
/-
**left_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_eq_mul : a = a * b ↔ b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_eq_left`：mul_eq_left : a * b = a ↔ b = 1
-/
theorem left_eq_mul₀ [IsLeftCancelMulZero M₀] (ha : a ≠ 0) : a = a * b ↔ b = 1 := by
  rw [eq_comm, mul_eq_left₀ ha]

@[simp]
/-
**right_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_eq_mul : b = a * b ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_eq_right`：mul_eq_right : a * b = b ↔ a = 1
-/
theorem right_eq_mul₀ [IsRightCancelMulZero M₀] (hb : b ≠ 0) : b = a * b ↔ a = 1 := by
  rw [eq_comm, mul_eq_right₀ hb]

/-- An element of a left-cancellative `MulZeroOneClass` fixed by right multiplication by
an element other than one must be zero. -/
/-
**eq_zero_of_mul_eq_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_mul_eq_self_right [IsLeftCancelMulZero M₀] (h₁ : b != 1) (h₂ : 
a * b = a) : a = 0
参数：h₁ : b != 1；h₂ : a * b = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
An element of a left-cancellative `MulZeroOneClass` fixed by right multiplicatio
n by
an element other than one must be zero.
-/
theorem eq_zero_of_mul_eq_self_right [IsLeftCancelMulZero M₀] (h₁ : b ≠ 1) (h₂ : a * b = a) :
    a = 0 :=
  Classical.byContradiction fun ha => h₁ <| mul_left_cancel₀ ha <| h₂.symm ▸ (mul_one a).symm

/-- An element of a right-cancellative `MulZeroOneClass` fixed by left multiplication by
an element other than one must be zero. -/
/-
**eq_zero_of_mul_eq_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_mul_eq_self_left [IsRightCancelMulZero M₀] (h₁ : b != 1) (h₂ : 
b * a = a) : a = 0
参数：h₁ : b != 1；h₂ : b * a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
An element of a right-cancellative `MulZeroOneClass` fixed by left multiplicatio
n by
an element other than one must be zero.
-/
theorem eq_zero_of_mul_eq_self_left [IsRightCancelMulZero M₀] (h₁ : b ≠ 1) (h₂ : b * a = a) :
    a = 0 :=
  Classical.byContradiction fun ha => h₁ <| mul_right_cancel₀ ha <| h₂.symm ▸ (one_mul a).symm

variable {M₀ : Type*} [MonoidWithZero M₀]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsLeftCancelMulZero M₀] : IsDedekindFiniteMonoid M₀ where
  mul_eq_one_symm h := by
    cases subsingleton_or_nontrivial M₀
    · exact Subsingleton.elim _ _
    exact (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (left_ne_zero_of_mul_eq_one h)).mul_eq_one_symm h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsRightCancelMulZero M₀] : IsDedekindFiniteMonoid M₀ where
  mul_eq_one_symm h := by
    cases subsingleton_or_nontrivial M₀
    · exact Subsingleton.elim _ _
    exact (IsRightCancelMulZero.mul_right_cancel_of_ne_zero
      (right_ne_zero_of_mul_eq_one h)).mul_eq_one_symm h

end CancelMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b x : G₀}

/-
**GroupWithZero.mul_right_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GroupWithZero.mul_right_injective (h : x != 0) : Function.Injective fun y 
=> x * y
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem GroupWithZero.mul_right_injective (h : x ≠ 0) :
    Function.Injective fun y => x * y := fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel₀ h, one_mul] using congr_arg (fun y => x⁻¹ * y) w
/-
**GroupWithZero.mul_left_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GroupWithZero.mul_left_injective (h : x != 0) : Function.Injective fun y =
> y * x
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem GroupWithZero.mul_left_injective (h : x ≠ 0) :
    Function.Injective fun y => y * x := fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel₀ h, mul_one] using congr_arg (fun y => y * x⁻¹) w

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_right`
/-
**inv_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]


@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_left`
/-
**inv_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
/-
**inv_eq_of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) GroupWithZero.toDivisionMonoid : DivisionMonoid G₀ where
  inv_inv a := by
    by_cases h : a = 0
    · simp [h]
    · exact left_inv_eq_right_inv (inv_mul_cancel₀ <| inv_ne_zero h) (inv_mul_cancel₀ h)
  mul_inv_rev a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    apply inv_eq_of_mul
    simp [mul_assoc, ha, hb]
  inv_eq_of_mul _ _ := by exact inv_eq_of_mul

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) : IsCancelMulZero G₀ where
  mul_left_cancel_of_ne_zero {x} hx y z h := by
    dsimp only at h; rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z]
  mul_right_cancel_of_ne_zero {x} hx y z h := by
    dsimp only at h; rw [← mul_inv_cancel_right₀ hx y, h, mul_inv_cancel_right₀ hx z]

end GroupWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a : G₀}

@[simp]
/-
**zero_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_div (a : G₀) : 0 / a = 0
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem zero_div (a : G₀) : 0 / a = 0 := by rw [div_eq_mul_inv, zero_mul]

@[simp]
/-
**div_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_zero (a : G₀) : a / 0 = 0
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem div_zero (a : G₀) : a / 0 = 0 := by rw [div_eq_mul_inv, inv_zero, mul_zero]

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp]
/-
**mul_self_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero).
-/
theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_assoc, mul_inv_cancel₀ h, mul_one]


/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp]
/-
**mul_inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_mul_cancel (a : G₀) : a * a⁻¹ * a = a
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero).
-/
theorem mul_inv_mul_cancel (a : G₀) : a * a⁻¹ * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_inv_cancel₀ h, one_mul]


/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp]
/-
**inv_mul_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero).
-/
theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [inv_mul_cancel₀ h, one_mul]


/-- Multiplying `a` by itself and then dividing by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
/-
**mul_self_div_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_div_self (a : G₀) : a * a / a = a
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_self_mul_inv`：mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a

--- 原说明 ---
Multiplying `a` by itself and then dividing by itself results in `a`, whether or
 not `a` is
zero.
-/
theorem mul_self_div_self (a : G₀) : a * a / a = a := by rw [div_eq_mul_inv, mul_self_mul_inv a]

/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
/-
**div_self_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_self_mul_self (a : G₀) : a / a * a = a
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_mul_cancel`：mul_inv_mul_cancel (a : G₀) : a * a⁻¹ * a = a

--- 原说明 ---
Dividing `a` by itself and then multiplying by itself results in `a`, whether or
 not `a` is
zero.
-/
theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_cancel a]

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

@[simp]
/-
**div_self_mul_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_mul_self`：inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a
-/
theorem div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
  calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by simp [mul_inv_rev]
    _ = a⁻¹ := inv_mul_mul_self _
/-
**one_div_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_div_ne_zero {a : G₀} (h : a != 0) : 1 / a != 0
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 := by
  simpa only [one_div] using inv_ne_zero h

@[simp]
/-
**inv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 := by rw [inv_eq_iff_eq_inv, inv_zero]

@[simp]
/-
**zero_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
-/
theorem zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a :=
  eq_comm.trans <| inv_eq_zero.trans eq_comm

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp]
/-
**div_div_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_self (a : G₀) : a / (a / a) = a
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用定理 `mul_self_div_self`：mul_self_div_self (a : G₀) : a * a / a = a

--- 原说明 ---
Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero).
-/
theorem div_div_self (a : G₀) : a / (a / a) = a := by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a
/-
**ne_zero_of_one_div_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a != 0) : a != 0
参数：h : 1 / a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
-/
theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 := fun ha : a = 0 => by
  rw [ha, div_zero] at h
  contradiction
/-
**eq_zero_of_one_div_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0
参数：h : 1 / a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byCases`：∀ {p q : Prop}, (p → q) → (¬p → q) → q
· 使用定理 `one_div_ne_zero`：one_div_ne_zero {a : G₀} (h : a != 0) : 1 / a != 0
-/
theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
  Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim
/-
**mul_left_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_left_surjective (a : G) : Surjective (a * ·)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem mul_left_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => a * g := fun g =>
  ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel₀ h]⟩
/-
**mul_right_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_surjective (a : G) : Function.Surjective fun x => x * a
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem mul_right_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => g * a := fun g =>
  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel₀ h]⟩
/-
**zero_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 0 ^ n = 0
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_zpow : ∀ n : ℤ, n ≠ 0 → (0 : G₀) ^ n = 0
  | (n : ℕ), h => by rw [zpow_natCast, zero_pow]; simpa [Int.natCast_eq_zero] using h
  | .negSucc n, _ => by simp
/-
**zero_zpow_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_zpow_eq (n : Int) : (0 : G₀) ^ n = if n = 0 then 1 else 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
-/
lemma zero_zpow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]
/-
**zero_zpow_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_zpow_eq_one₀ {n : ℤ} : (0 : G₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_zpow_eq, one_ne_zero.ite_eq_left_iff]
/-
**zpow_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n + 1) = a ^ n * a
参数：a : G；n : ℤ；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.add_left_neg`：∀ (a : ℤ), -a + a = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Int.negSucc_eq`：∀ (n : ℕ), Int.negSucc n = -(↑n + 1)
· 使用定理 `Int.neg_add`：∀ {a b : ℤ}, -(a + b) = -a + -b
· 使用定理 `Int.neg_add_cancel_right`：∀ (a b : ℤ), a + -b + b = a
-/
lemma zpow_add_one₀ (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.natCast_succ, zpow_natCast, pow_succ]
  | -1 => by simp [ha]
  | .negSucc (n + 1) => by
    rw [Int.negSucc_eq, zpow_neg, Int.neg_add, Int.neg_add_cancel_right, zpow_neg,
      ← Int.natCast_succ, zpow_natCast, zpow_natCast, pow_succ' _ (n + 1), mul_inv_rev, mul_assoc,
      inv_mul_cancel₀ ha, mul_one]
/-
**zpow_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_sub_one (a : G) (n : Int) : a ^ (n - 1) = a ^ n * a⁻¹
参数：a : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `Int.sub_add_cancel`：∀ (a b : ℤ), a - b + b = a
-/
lemma zpow_sub_one₀ (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one₀ ha, Int.sub_add_cancel]
/-
**zpow_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
参数：a : G；m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_zero`：∀ (a : ℤ), a + 0 = a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `zpow_sub_one`：zpow_sub_one (a : G) (n : Int) : a ^ (n - 1) = a ^ n * a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.add_sub_assoc`：∀ (a b c : ℤ), a + b - c = a + (b - c)
-/
lemma zpow_add₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one₀ ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, Int.add_sub_assoc]
/-
**zpow_add'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_add' {m n : Int} (h : a != 0 ∨ m + n != 0 ∨ m = 0 ∧ n = 0) : a ^ (m +
 n) = a ^ m * a ^ n
参数：h : a != 0 ∨ m + n != 0 ∨ m = 0 ∧ n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.zero_add`：∀ (a : ℤ), 0 + a = a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.add_zero`：∀ (a : ℤ), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
-/
lemma zpow_add' {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
    a ^ (m + n) = a ^ m * a ^ n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · subst a
    simp only [false_or, not_true, Ne, hm, hn, false_and, or_false] at h
    rw [zero_zpow _ h, zero_zpow _ hm, zero_mul]
  · exact zpow_add₀ ha m n
/-
**zpow_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_one_add (a : G) (n : Int) : a ^ (1 + n) = a * a ^ n
参数：a : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
-/
lemma zpow_one_add₀ (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by rw [zpow_add₀ h, zpow_one]

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀]

/-
**div_mul_eq_mul_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_eq_mul_div : a / b * c = a * c / b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * b / c := by
  simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]
/-
**div_sq_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b
参数：a b : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
-/
lemma div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [sq, mul_assoc, mul_div_cancel_left₀ _ ha]

end CommGroupWithZero

