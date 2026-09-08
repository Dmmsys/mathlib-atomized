/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Semiconj.Defs

/-!
# Commuting pairs of elements in monoids

We define the predicate `Commute a b := a * b = b * a` and provide some operations on terms
`(h : Commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that
`hb : Commute a b` and `hc : Commute a c`.  Then `hb.pow_left 5` proves `Commute (a ^ 5) b` and
`(hb.pow_right 2).add_right (hb.mul_right hc)` proves `Commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc).  Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `SemiconjBy`.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {G M S : Type*}

/-- Two elements commute if `a * b = b * a`. -/
@[to_additive /-- Two elements additively commute if `a + b = b + a` -/]
/-
**Commute** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Commute [Mul S] (a b : S) : Prop
参数：a b : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two elements commute if `a * b = b * a`.
-/
def Commute [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b

/--
Two elements `a` and `b` commute if `a * b = b * a`.
-/
@[to_additive]
/-
**commute_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b = b * a
参数：a b : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two elements `a` and `b` commute if `a * b = b * a`.
-/
theorem commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b = b * a := Iff.rfl

namespace Commute

section Mul

variable [Mul S]

/-- Equality behind `Commute a b`; useful for rewriting. -/
@[to_additive (attr := grind →) /-- Equality behind `AddCommute a b`; useful for rewriting. -/]
/-
**Commute.eq** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a * b = b * a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equality behind `Commute a b`; useful for rewriting.
-/
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h

/-- Any element commutes with itself. -/
@[to_additive (attr := refl, simp) /-- Any element commutes with itself. -/]
/-
**Commute.refl** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
参数：a : S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any element commutes with itself.
-/
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[to_additive (attr := symm) /-- If `a` commutes with `b`, then `b` commutes with `a`. -/]
/-
**Commute.symm** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → Commute b a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `a` commutes with `b`, then `b` commutes with `a`.
-/
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h

@[to_additive]
/-
**Commute.semiconjBy** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → SemiconjBy a b b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem semiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h

@[to_additive (attr := grind =)]
/-
**Commute.symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b ↔ Commute b a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
-/
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩

@[to_additive]
/-
**Commute.** 是 Mathlib 中的一个实例，位于命名空间 `Commute`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Refl S Commute :=
  ⟨Commute.refl⟩

@[to_additive]
/-
**Commute.** 是 Mathlib 中的一个实例，位于命名空间 `Commute`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Symm S Commute where
  symm _ _ := .symm

-- This instance is useful for `Finset.noncommProd`
@[to_additive]
/-
**Commute.on_refl** 是 Mathlib 中的一个实例，位于命名空间 `Commute`。
形式化陈述：on_refl {f : G -> S} : Std.Refl fun a b => Commute (f a) (f b)
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
instance on_refl {f : G → S} : Std.Refl fun a b => Commute (f a) (f b) :=
  ⟨fun _ => Commute.refl _⟩

end Mul

section Semigroup

variable [Semigroup S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[to_additive (attr := simp)
/-- If `a` commutes with both `b` and `c`, then it commutes with their sum. -/]
/-
**Commute.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c)
参数：hab : Commute a b；hac : Commute a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.mul_right`：mul_right (h : SemiconjBy a x y) (h' : SemiconjBy 
a x' y') : SemiconjBy a (x * x') (y * y')
-/
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  SemiconjBy.mul_right hab hac

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[to_additive (attr := simp)
/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/]
/-
**Commute.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c
参数：hac : Commute a c；hbc : Commute b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.mul_left`：mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b
 x y) : SemiconjBy (a * b) x z
-/
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  SemiconjBy.mul_left hac hbc

@[to_additive]
/-
**Commute.right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Commute b c → ∀ (a : S), 
a * b * c = a * c * b
参数：a : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b := by
  simp only [mul_assoc, h.eq]

@[to_additive]
/-
**Commute.left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, Commute a b → ∀ (c : S), 
a * (b * c) = b * (a * c)
参数：c : S；b * c；a * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) := by
  simp only [← mul_assoc, h.eq]

@[to_additive]
/-
**Commute.mul_mul_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Commute b c → ∀ (a d : S)
, a * b * (c * d) = a * c * (b * d)
参数：a d : S；c * d；b * d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Commute.left_comm`：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, Comm
ute a b → ∀ (c : S), a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mul_mul_mul_comm (hbc : Commute b c) (a d : S) :
    a * b * (c * d) = a * c * (b * d) := by simp only [hbc.left_comm, mul_assoc]

end Semigroup

@[to_additive]
/-
**Commute.all** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a b
参数：a b : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
protected theorem all [CommMagma S] (a b : S) : Commute a b :=
  mul_comm a b

section MulOneClass

variable [MulOneClass M]

@[to_additive (attr := simp)]
/-
**Commute.one_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：one_right (a : M) : Commute a 1
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.one_right`：one_right (a : M) : SemiconjBy a 1 1
-/
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a

@[to_additive (attr := simp)]
/-
**Commute.one_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：one_left (a : M) : Commute 1 a
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.one_left`：one_left (x : M) : SemiconjBy 1 x x
-/
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a

end MulOneClass

section Monoid

variable [Monoid M] {a b : M}

@[to_additive (attr := simp)]
/-
**Commute.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：pow_right (h : Commute a b) (n : Nat) : Commute a (b ^ n)
参数：h : Commute a b；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.pow_right`：pow_right {a x y : M} (h : SemiconjBy a x y) (n : 
Nat) : SemiconjBy a (x ^ n) (y ^ n)
-/
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  SemiconjBy.pow_right h n

@[to_additive (attr := simp)]
/-
**Commute.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n) b
参数：h : Commute a b；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Commute.pow_right`：pow_right (h : Commute a b) (n : Nat) : Commute a (b 
^ n)
-/
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm

-- todo: should nat power be called `nsmul` here?
@[to_additive]
/-
**Commute.pow_pow** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m) (b ^ n)
参数：h : Commute a b；m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) := by
  simp [h]

@[to_additive]
/-
**Commute.self_pow** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：self_pow (a : M) (n : Nat) : Commute a (a ^ n)
参数：a : M；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.pow_right`：pow_right (h : Commute a b) (n : Nat) : Commute a (b 
^ n)
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n

@[to_additive]
/-
**Commute.pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：pow_self (a : M) (n : Nat) : Commute (a ^ n) a
参数：a : M；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.pow_left`：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n)
 b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n

@[to_additive]
/-
**Commute.pow_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：pow_pow_self (a : M) (m n : Nat) : Commute (a ^ m) (a ^ n)
参数：a : M；m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n
/-
**Commute.mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a b → ∀ (n : ℕ), (a 
* b) ^ n = a ^ n * b ^ n
参数：n : ℕ；a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma mul_pow (h : Commute a b) : ∀ n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [pow_zero, pow_zero, pow_zero, one_mul]
  | n + 1 => by simp only [pow_succ', h.mul_pow n, ← mul_assoc, (h.pow_left n).right_comm]

end Monoid

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive]
/-
**Commute.mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, Commute a b → (a * b
)⁻¹ = a⁻¹ * b⁻¹
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
-/
protected theorem mul_inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]

@[to_additive]
/-
**Commute.inv** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, Commute a b → (a * b
)⁻¹ = a⁻¹ * b⁻¹
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
-/
protected theorem inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]

@[to_additive AddCommute.zsmul_add]
/-
**Commute.mul_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, Commute a b → ∀ (n :
 ℤ), (a * b) ^ n = a ^ n * b ^ n
参数：n : ℤ；a * b。
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
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
-/
protected lemma mul_zpow (h : Commute a b) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
  | (n : ℕ) => by simp [zpow_natCast, h.mul_pow n]
  | .negSucc n => by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev]

end DivisionMonoid

section Group

variable [Group G] {a b : G}

@[to_additive]
/-
**Commute.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a b : G}, Commute a b → a * b * a⁻¹ = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

@[to_additive]
/-
**Commute.mul_inv_cancel_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b
参数：h : Commute a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Commute.mul_inv_cancel`：∀ {G : Type u_1} [inst : Group G] {a b : G}, Com
mute a b → a * b * a⁻¹ = b
-/
theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, h.mul_inv_cancel]

end Group

end Commute

/-
**IsLeftRegular.commute_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLeftRegular`。
形式化陈述：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, IsLeftRegular a → (Commut
e (a * b) a ↔ Commute a b)
参数：Commute (a * b) a ↔ Commute a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] protected lemma IsLeftRegular.commute_mul_left_iff [Semigroup S] {a b : S}
    (reg : IsLeftRegular a) : Commute (a * b) a ↔ Commute a b := by
  simp [commute_iff_eq, mul_assoc, reg.eq_iff, eq_comm]
/-
**IsRightRegular.commute_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRightRegular
`。
形式化陈述：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, IsRightRegular a → (Commu
te (b * a) a ↔ Commute a b)
参数：Commute (b * a) a ↔ Commute a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] protected lemma IsRightRegular.commute_mul_right_iff [Semigroup S] {a b : S}
    (reg : IsRightRegular a) : Commute (b * a) a ↔ Commute a b := by
  simp [commute_iff_eq, ← mul_assoc, reg.eq_iff, eq_comm]
