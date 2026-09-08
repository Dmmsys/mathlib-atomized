/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Aesop
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Int.Init
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.SplitIfs

/-!
# Basic lemmas about semigroups, monoids, and groups

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`Mathlib/Algebra/Group/Defs.lean`.
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open Function

variable {α β G M : Type*}

section ite
variable [Pow α β]

@[to_additive (attr := simp, to_additive) dite_smul]
/-
**pow_dite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_dite (p : Prop) [Decidable p] (a : α) (b : p -> β) (c : ¬ p -> β) : a 
^ (if h : p then b h else c h) = if h : p then a ^ b h else a ^ c h
参数：p : Prop；a : α；b : p -> β；c : ¬ p -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma pow_dite (p : Prop) [Decidable p] (a : α) (b : p → β) (c : ¬ p → β) :
    a ^ (if h : p then b h else c h) = if h : p then a ^ b h else a ^ c h := by split_ifs <;> rfl

@[to_additive (attr := simp, to_additive) smul_dite]
/-
**dite_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dite_pow (p : Prop) [Decidable p] (a : p -> α) (b : ¬ p -> α) (c : β) : (i
f h : p then a h else b h) ^ c = if h : p then a h ^ c else b h ^ c
参数：p : Prop；a : p -> α；b : ¬ p -> α；c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma dite_pow (p : Prop) [Decidable p] (a : p → α) (b : ¬ p → α) (c : β) :
    (if h : p then a h else b h) ^ c = if h : p then a h ^ c else b h ^ c := by split_ifs <;> rfl

@[to_additive (attr := simp, to_additive) ite_smul]
/-
**pow_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) : a ^ (if p then b else
 c) = if p then a ^ b else a ^ c
参数：p : Prop；a : α；b c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_dite`：pow_dite (p : Prop) [Decidable p] (a : α) (b : p -> β) (c : ¬ 
p -> β) : a ^ (if h : p then b h else c h) = if h : p then a ^ b h else a ^ c …
-/
lemma pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) :
    a ^ (if p then b else c) = if p then a ^ b else a ^ c := pow_dite _ _ _ _

@[to_additive (attr := simp, to_additive) smul_ite]
/-
**ite_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) : (if p then a else b) 
^ c = if p then a ^ c else b ^ c
参数：p : Prop；a b : α；c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dite_pow`：dite_pow (p : Prop) [Decidable p] (a : p -> α) (b : ¬ p -> α) 
(c : β) : (if h : p then a h else b h) ^ c = if h : p then a h ^ c else b h ^ …
-/
lemma ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) :
    (if p then a else b) ^ c = if p then a ^ c else b ^ c := dite_pow _ _ _ _

end ite

section Semigroup
variable [Semigroup α]

@[to_additive]
/-
**Semigroup.to_isAssociative** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Semigroup.to_isAssociative : Std.Associative (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
instance Semigroup.to_isAssociative : Std.Associative (α := α) (· * ·) := ⟨mul_assoc⟩

/-- Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[to_additive (attr := simp) /-- Composing two additions on the left by `y` then `x`
is equal to an addition on the left by `x + y`. -/]
/-
**comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·) := by
  ext z
  simp [mul_assoc]

/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[to_additive (attr := simp) /-- Composing two additions on the right by `y` and `x`
is equal to an addition on the right by `y + x`. -/]
/-
**comp_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y * x))
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) := by
  ext z
  simp [mul_assoc]

end Semigroup

section MulOneClass

variable [MulOneClass M]

@[to_additive]
/-
**Semigroup.to_isLawfulIdentity** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Semigroup.to_isLawfulIdentity : Std.LawfulIdentity (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
instance Semigroup.to_isLawfulIdentity : Std.LawfulIdentity (α := M) (· * ·) 1 where
  left_id := one_mul
  right_id := mul_one

@[to_additive]
/-
**ite_mul_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_mul_one {P : Prop} [Decidable P] {a b : M} : ite P (a * b) 1 = ite P a
 1 * ite P b 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} :
    ite P (a * b) 1 = ite P a 1 * ite P b 1 := by
  by_cases h : P <;> simp [h]

@[to_additive]
/-
**ite_one_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_one_mul {P : Prop} [Decidable P] {a b : M} : ite P 1 (a * b) = ite P 1
 a * ite P 1 b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} :
    ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  by_cases h : P <;> simp [h]

@[to_additive]
/-
**eq_one_iff_eq_one_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1
参数：h : a * b = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;> (rintro rfl; simpa using h)

@[to_additive]
/-
**one_mul_eq_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_mul_eq_id : ((1 : M) * ·) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_mul_eq_id : ((1 : M) * ·) = id :=
  funext one_mul

@[to_additive]
/-
**mul_one_eq_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_one_eq_id : (· * (1 : M)) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one

end MulOneClass

section CommSemigroup

variable [CommSemigroup G]

@[to_additive]
/-
**mul_left_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mul_left_comm (a b c : G) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a, mul_assoc]

@[to_additive]
/-
**mul_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_comm (a b c : G) : a * b * c = a * c * b
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mul_right_comm (a b c : G) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm b, mul_assoc]

@[to_additive]
/-
**mul_mul_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d)
参数：a b c d : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  simp only [mul_left_comm, mul_assoc]

@[to_additive]
/-
**mul_mul_mul_comm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mul_mul_comm' (a b c d : G) : a * b * c * d = a * c * b * d
参数：a b c d : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_mul_mul_comm' (a b c d : G) : a * b * c * d = a * c * b * d := by
  grind

@[to_additive]
/-
**mul_rotate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_rotate (a b c : G) : a * b * c = b * c * a
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by
  simp only [mul_left_comm, mul_comm]

@[to_additive]
/-
**mul_rotate'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_rotate' (a b c : G) : a * (b * c) = b * (c * a)
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by
  simp only [mul_left_comm, mul_comm]

end CommSemigroup

attribute [local simp] mul_assoc sub_eq_add_neg

section Monoid
variable [Monoid M] {a b : M} {m n : ℕ}

@[to_additive boole_nsmul]
/-
**pow_boole** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_boole (P : Prop) [Decidable P] (a : M) : (a ^ if P then 1 else 0) = if
 P then a else 1
参数：P : Prop；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_ite`：pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) : a ^ (if p 
then b else c) = if p then a ^ b else a ^ c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pow_boole (P : Prop) [Decidable P] (a : M) :
    (a ^ if P then 1 else 0) = if P then a else 1 := by simp only [pow_ite, pow_one, pow_zero]

@[to_additive nsmul_add_sub_nsmul]
/-
**pow_mul_pow_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_mul_pow_sub (a : M) (h : m <= n) : a ^ m * a ^ (n - m) = a ^ n
参数：a : M；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
lemma pow_mul_pow_sub (a : M) (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]

@[to_additive sub_nsmul_nsmul_add]
/-
**pow_sub_mul_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sub_mul_pow (a : M) (h : m <= n) : a ^ (n - m) * a ^ m = a ^ n
参数：a : M；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
lemma pow_sub_mul_pow (a : M) (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]

@[to_additive sub_one_nsmul_add]
/-
**mul_pow_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_pow_sub_one (hn : n != 0) (a : M) : a * a ^ (n - 1) = a ^ n
参数：hn : n != 0；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma mul_pow_sub_one (hn : n ≠ 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ', Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

@[to_additive add_sub_one_nsmul]
/-
**pow_sub_one_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sub_one_mul (hn : n != 0) (a : M) : a ^ (n - 1) * a = a ^ n
参数：hn : n != 0；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma pow_sub_one_mul (hn : n ≠ 0) (a : M) : a ^ (n - 1) * a = a ^ n := by
  rw [← pow_succ, Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
@[to_additive nsmul_eq_mod_nsmul /-- If `n • x = 0`, then `m • x` is the same as `(m % n) • x` -/]
/-
**pow_eq_pow_mod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_pow_mod (m : Nat) (ha : a ^ n = 1) : a ^ m = a ^ (m % n)
参数：m : Nat；ha : a ^ n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)`
-/
lemma pow_eq_pow_mod (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  calc
    a ^ m = a ^ (m % n + n * (m / n)) := by rw [Nat.mod_add_div]
    _ = a ^ (m % n) := by simp [pow_add, pow_mul, ha]
/-
**pow_mul_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] {a b : M} (n : ℕ), a * b = 1 → a ^ n * 
b ^ n = 1
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma pow_mul_pow_eq_one : ∀ n, a * b = 1 → a ^ n * b ^ n = 1
  | 0, _ => by simp
  | n + 1, h =>
    calc
      a ^ n.succ * b ^ n.succ = a ^ n * a * (b * b ^ n) := by rw [pow_succ, pow_succ']
      _ = a ^ n * (a * b) * b ^ n := by simp only [mul_assoc]
      _ = 1 := by simp [h, pow_mul_pow_eq_one]

@[to_additive (attr := simp)]
/-
**mul_left_iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (fun x => a * x)^[n] =
 fun x => a ^ n * x
参数：a : M；n : ℕ；fun x => a * x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_left_iterate (a : M) : ∀ n : ℕ, (a * ·)^[n] = (a ^ n * ·)
  | 0 => by ext; simp
  | n + 1 => by simp [pow_succ, mul_left_iterate]

@[to_additive (attr := simp)]
/-
**mul_right_iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (fun x => x * a)^[n] =
 fun x => x * a ^ n
参数：a : M；n : ℕ；fun x => x * a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_right_iterate (a : M) : ∀ n : ℕ, (· * a)^[n] = (· * a ^ n)
  | 0 => by ext; simp
  | n + 1 => by simp [pow_succ', mul_right_iterate]

/-- Version of `mul_left_iterate` that is fully applied, for `rw`. -/
@[to_additive /-- Version of `add_left_iterate` that is fully applied, for `rw`. -/]
/-
**mul_left_iterate_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_left_iterate_apply (a b : M) : (a * ·)^[n] b = a ^ n * b
参数：a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Version of `mul_left_iterate` that is fully applied, for `rw`.
-/
lemma mul_left_iterate_apply (a b : M) : (a * ·)^[n] b = a ^ n * b := by simp

/-- Version of `mul_right_iterate` that is fully applied, for `rw`. -/
@[to_additive /-- Version of `add_right_iterate` that is fully applied, for `rw`. -/ ]
/-
**mul_right_iterate_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_right_iterate_apply (a b : M) : (· * a)^[n] b = b * a ^ n
参数：a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_right_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (
fun x => x * a)^[n] = fun x => x * a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Version of `mul_right_iterate` that is fully applied, for `rw`.
-/
lemma mul_right_iterate_apply (a b : M) : (· * a)^[n] b = b * a ^ n := by simp

@[to_additive]
/-
**mul_left_iterate_apply_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_left_iterate_apply_one (a : M) : (a * ·)^[n] 1 = a ^ n
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_left_iterate_apply_one (a : M) : (a * ·)^[n] 1 = a ^ n := by simp

@[to_additive]
/-
**mul_right_iterate_apply_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_right_iterate_apply_one (a : M) : (· * a)^[n] 1 = a ^ n
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_right_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (
fun x => x * a)^[n] = fun x => x * a ^ n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_right_iterate_apply_one (a : M) : (· * a)^[n] 1 = a ^ n := by simp [mul_right_iterate]

@[to_additive, simp]
/-
**pow_iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] (k n : ℕ), (fun x => x ^ k)^[n] = fun x
 => x ^ k ^ n
参数：k n : ℕ；fun x => x ^ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_iterate (k : ℕ) : ∀ n : ℕ, (fun x : M ↦ x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by ext; simp
  | n + 1 => by ext; simp [pow_iterate, Nat.pow_succ', pow_mul]

end Monoid

section CommMonoid
variable [CommMonoid M] {x y z : M}

@[to_additive]
/-
**inv_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z
参数：hy : x * y = 1；hz : x * z = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz
/-
**mul_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂) : 
(xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
参数：_ : ea₁ * b = c₁；_ : a₂ ^ b = c₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive nsmul_add] lemma mul_pow (a b : M) : ∀ n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [pow_zero, pow_zero, pow_zero, one_mul]
  | n + 1 => by rw [pow_succ', pow_succ', pow_succ', mul_pow, mul_mul_mul_comm]

end CommMonoid

section LeftCancelMonoid

variable [Monoid M] [IsLeftCancelMul M] {a b : M}

@[to_additive (attr := simp)]
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
theorem mul_eq_left : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff

@[to_additive (attr := simp)]
/-
**left_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_eq_mul : a = a * b ↔ b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_eq_left`：mul_eq_left : a * b = a ↔ b = 1
-/
theorem left_eq_mul : a = a * b ↔ b = 1 :=
  eq_comm.trans mul_eq_left

@[to_additive]
/-
**mul_ne_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ne_left : a * b != a ↔ b != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `mul_eq_left`：mul_eq_left : a * b = a ↔ b = 1
-/
theorem mul_ne_left : a * b ≠ a ↔ b ≠ 1 := mul_eq_left.not

@[to_additive]
/-
**left_ne_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_ne_mul : a != a * b ↔ b != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `left_eq_mul`：left_eq_mul : a = a * b ↔ b = 1
-/
theorem left_ne_mul : a ≠ a * b ↔ b ≠ 1 := left_eq_mul.not

end LeftCancelMonoid

section RightCancelMonoid

variable [Monoid M] [IsRightCancelMul M] {a b : M}

@[to_additive (attr := simp)]
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
theorem mul_eq_right : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff

@[to_additive (attr := simp)]
/-
**right_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_eq_mul : b = a * b ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_eq_right`：mul_eq_right : a * b = b ↔ a = 1
-/
theorem right_eq_mul : b = a * b ↔ a = 1 :=
  eq_comm.trans mul_eq_right

@[to_additive]
/-
**mul_ne_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ne_right : a * b != b ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `mul_eq_right`：mul_eq_right : a * b = b ↔ a = 1
-/
theorem mul_ne_right : a * b ≠ b ↔ a ≠ 1 := mul_eq_right.not

@[to_additive]
/-
**right_ne_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_ne_mul : b != a * b ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `right_eq_mul`：right_eq_mul : b = a * b ↔ a = 1
-/
theorem right_ne_mul : b ≠ a * b ↔ a ≠ 1 := right_eq_mul.not

end RightCancelMonoid

section CancelCommMonoid
variable [CancelCommMonoid α] {a b c d : α}

/-
**eq_iff_eq_of_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : CancelCommMonoid α] {a b c d : α}, a * b = c * d 
→ (a = c ↔ b = d)
参数：a = c ↔ b = d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
-/
@[to_additive] lemma eq_iff_eq_of_mul_eq_mul (h : a * b = c * d) : a = c ↔ b = d := by aesop
/-
**ne_iff_ne_of_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : CancelCommMonoid α] {a b c d : α}, a * b = c * d 
→ (a ≠ c ↔ b ≠ d)
参数：a ≠ c ↔ b ≠ d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
@[to_additive] lemma ne_iff_ne_of_mul_eq_mul (h : a * b = c * d) : a ≠ c ↔ b ≠ d := by aesop

end CancelCommMonoid

section InvolutiveInv

variable [InvolutiveInv G] {a b : G}

@[to_additive (attr := simp)]
/-
**inv_involutive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_involutive : Function.Involutive (Inv.inv : G -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem inv_involutive : Function.Involutive (Inv.inv : G → G) :=
  inv_inv

@[to_additive]
/-
**inv_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_bijective : Function.Bijective (Inv.inv : G -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `inv_involutive`：inv_involutive : Function.Involutive (Inv.inv : G -> G)
-/
theorem inv_bijective : Function.Bijective (Inv.inv : G → G) :=
  inv_involutive.bijective

@[to_additive (attr := simp)]
/-
**inv_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_surjective : Function.Surjective (Inv.inv : G -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `inv_involutive`：inv_involutive : Function.Involutive (Inv.inv : G -> G)
-/
theorem inv_surjective : Function.Surjective (Inv.inv : G → G) :=
  inv_involutive.surjective

@[to_additive]
/-
**inv_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_injective : Function.Injective (Inv.inv : G -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `inv_involutive`：inv_involutive : Function.Involutive (Inv.inv : G -> G)
-/
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.injective

@[to_additive (attr := simp)]
/-
**inv_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
-/
theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff

@[to_additive]
/-
**inv_eq_iff_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `inv_involutive`：inv_involutive : Function.Involutive (Inv.inv : G -> G)
-/
theorem inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹ :=
  inv_involutive.eq_iff

variable (G)

@[to_additive]
/-
**inv_comp_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_comp_inv : Inv.inv ∘ Inv.inv = @id G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.comp_self`：comp_self : f ∘ f = id
· 使用定理 `inv_involutive`：inv_involutive : Function.Involutive (Inv.inv : G -> G)
-/
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self

@[to_additive]
/-
**leftInverse_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftInverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem leftInverse_inv : LeftInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ :=
  inv_inv

@[to_additive]
/-
**rightInverse_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightInverse_inv : RightInverse (fun a : G => a⁻¹) fun a => a⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem rightInverse_inv : RightInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ :=
  inv_inv

end InvolutiveInv

section DivInvMonoid

variable [DivInvMonoid G]

@[to_additive]
/-
**mul_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_one_div (x y : G) : x * (1 / y) = x / y
参数：x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

@[to_additive]
/-
**mul_div_assoc'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
-/
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm

@[to_additive]
/-
**mul_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div (a b c : G) : a * (b / c) = a * b / c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]

@[to_additive]
/-
**div_eq_mul_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_mul_one_div (a b : G) : a / b = a * (1 / b)
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]

end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

@[to_additive (attr := simp)]
/-
**div_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_one (a : G) : a / 1 = a
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]

@[to_additive]
/-
**one_div_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_div_one : (1 : G) / 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c d : α}

attribute [local simp] mul_assoc div_eq_mul_inv

@[to_additive]
/-
**eq_inv_of_mul_eq_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
-/
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
/-
**eq_one_div_of_mul_eq_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a
参数：h : b * a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_left h, one_div]

@[to_additive]
/-
**eq_one_div_of_mul_eq_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_inv_of_mul_eq_one_right`：eq_inv_of_mul_eq_one_right (h : a * b = 1) :
 b = a⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_right h, one_div]

@[to_additive]
/-
**eq_of_div_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_div_eq_one (h : a / b = 1) : a = b
参数：h : a / b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]

@[to_additive]
/-
**eq_of_inv_mul_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b
参数：h : a⁻¹ * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
-/
lemma eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]
/-
**eq_of_mul_inv_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b
参数：h : a * b⁻¹ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
-/
lemma eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]
/-
**div_ne_one_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_ne_one_of_ne : a != b -> a / b != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `eq_of_div_eq_one`：eq_of_div_eq_one (h : a / b = 1) : a = b
-/
theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 :=
  mt eq_of_div_eq_one

variable (a b c)

@[to_additive]
/-
**one_div_mul_one_div_rev** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp

@[to_additive]
/-
**inv_div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_div_left : a⁻¹ / b = (b * a)⁻¹
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp

@[to_additive (attr := simp)]
/-
**inv_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_div : (a / b)⁻¹ = b / a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_div : (a / b)⁻¹ = b / a := by simp

@[to_additive]
/-
**one_div_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_div_div : 1 / (a / b) = b / a
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_div_div : 1 / (a / b) = b / a := by simp

@[to_additive]
/-
**one_div_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_div_one_div : 1 / (1 / a) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_div_one_div : 1 / (1 / a) = a := by simp

@[to_additive]
/-
**div_eq_div_iff_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_div_iff_comm : a / b = c / d ↔ b / a = d / c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem div_eq_div_iff_comm : a / b = c / d ↔ b / a = d / c :=
  inv_inj.symm.trans <| by simp only [inv_div]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid with
    inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }

@[to_additive (attr := simp)]
/-
**inv_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹ ^ n = (a ^
 n)⁻¹
参数：a : α；n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_pow (a : α) : ∀ n : ℕ, a⁻¹ ^ n = (a ^ n)⁻¹
  | 0 => by rw [pow_zero, pow_zero, inv_one]
  | n + 1 => by rw [pow_succ', pow_succ, inv_pow _ n, mul_inv_rev]

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
@[to_additive zsmul_zero, simp]
/-
**one_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
lemma one_zpow : ∀ n : ℤ, (1 : α) ^ n = 1
  | (n : ℕ) => by rw [zpow_natCast, one_pow]
  | .negSucc n => by rw [zpow_negSucc, one_pow, inv_one]

@[to_additive (attr := simp) neg_zsmul]
/-
**zpow_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a ^ (-n) = (a 
^ n)⁻¹
参数：a : α；n : ℤ；-n；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivInvMonoid.zpow_neg'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) (
a : G), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
lemma zpow_neg (a : α) : ∀ n : ℤ, a ^ (-n) = (a ^ n)⁻¹
  | (_ + 1 : ℕ) => DivInvMonoid.zpow_neg' _ _
  | 0 => by simp
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_inv, ← zpow_natCast]
    rfl

@[to_additive neg_one_zsmul_add]
/-
**mul_zpow_neg_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : Int) = b ^ (-1 : Int) * a ^ (
-1 : Int)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : ℤ) = b ^ (-1 : ℤ) * a ^ (-1 : ℤ) := by
  simp only [zpow_neg, zpow_one, mul_inv_rev]

@[to_additive zsmul_neg]
/-
**inv_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a⁻¹ ^ n = (a ^
 n)⁻¹
参数：a : α；n : ℤ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
lemma inv_zpow (a : α) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, inv_pow]
  | .negSucc n => by rw [zpow_negSucc, zpow_negSucc, inv_pow]

@[to_additive (attr := simp) zsmul_neg']
/-
**inv_zpow'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_zpow' (a : α) (n : Int) : a⁻¹ ^ n = a ^ (-n)
参数：a : α；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a⁻
¹ ^ n = (a ^ n)⁻¹
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
-/
lemma inv_zpow' (a : α) (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]

@[to_additive nsmul_zero_sub]
/-
**one_div_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_div_pow (a : α) (n : Nat) : (1 / a) ^ n = 1 / a ^ n
参数：a : α；n : Nat。
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
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_div_pow (a : α) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_pow]

@[to_additive zsmul_zero_sub]
/-
**one_div_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_div_zpow (a : α) (n : Int) : (1 / a) ^ n = 1 / a ^ n
参数：a : α；n : Int。
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
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a⁻
¹ ^ n = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_div_zpow (a : α) (n : ℤ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_zpow]

variable {a b c}

@[to_additive (attr := simp)]
/-
**inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_eq_one : a⁻¹ = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  inv_injective.eq_iff' inv_one

@[to_additive (attr := simp)]
/-
**one_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_eq_inv : 1 = a⁻¹ ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `inv_eq_one`：inv_eq_one : a⁻¹ = 1 ↔ a = 1
-/
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  eq_comm.trans inv_eq_one

@[to_additive]
/-
**inv_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_ne_one : a⁻¹ != 1 ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `inv_eq_one`：inv_eq_one : a⁻¹ = 1 ↔ a = 1
-/
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  inv_eq_one.not

@[to_additive]
/-
**eq_of_one_div_eq_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b
参数：h : 1 / a = 1 / b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div_one_div`：one_div_one_div : 1 / (1 / a) = a
-/
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by
  rw [← one_div_one_div a, h, one_div_one_div]

-- Note that `mul_zsmul` and `zpow_mul` have the primes swapped
-- when additivised since their argument order,
-- and therefore the more "natural" choice of lemma, is reversed.
/-
**zpow_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), a ^ (m * n) 
= (a ^ m) ^ n
参数：a : α；m n : ℤ；m * n；a ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Int.ofNat_mul_negSucc`：∀ (m n : ℕ), ↑m * Int.negSucc n = -↑(m * n.succ)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Int.negSucc_mul_ofNat`：∀ (m n : ℕ), Int.negSucc m * ↑n = -↑(m.succ * n)
· 使用定理 `Int.negSucc_mul_negSucc`：∀ (m n : ℕ), Int.negSucc m * Int.negSucc n = ↑m
.succ * ↑n.succ
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
@[to_additive mul_zsmul'] lemma zpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    rw [zpow_natCast, zpow_natCast, ← pow_mul, ← zpow_natCast]
    rfl
  | (m : ℕ), .negSucc n => by
    rw [zpow_natCast, zpow_negSucc, ← pow_mul, Int.ofNat_mul_negSucc, zpow_neg, inv_inj,
      ← zpow_natCast]
  | .negSucc m, (n : ℕ) => by
    rw [zpow_natCast, zpow_negSucc, ← inv_pow, ← pow_mul, Int.negSucc_mul_ofNat, zpow_neg, inv_pow,
      inv_inj, ← zpow_natCast]
  | .negSucc m, .negSucc n => by
    rw [zpow_negSucc, zpow_negSucc, Int.negSucc_mul_negSucc, inv_pow, inv_inv, ← pow_mul, ←
      zpow_natCast]
    rfl

@[to_additive mul_zsmul]
/-
**zpow_mul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_mul' (a : α) (m n : Int) : a ^ (m * n) = (a ^ n) ^ m
参数：a : α；m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.mul_comm`：∀ (a b : ℤ), a * b = b * a
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
-/
lemma zpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Int.mul_comm, zpow_mul]

@[to_additive]
/-
**zpow_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpow_comm (a : α) (m n : Int) : (a ^ m) ^ n = (a ^ n) ^ m
参数：a : α；m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用引理 `zpow_mul'`：zpow_mul' (a : α) (m n : Int) : a ^ (m * n) = (a ^ n) ^ m
-/
theorem zpow_comm (a : α) (m n : ℤ) : (a ^ m) ^ n = (a ^ n) ^ m := by rw [← zpow_mul, zpow_mul']

variable (a b c)

@[to_additive]
/-
**div_div_eq_mul_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_eq_mul_div : a / (b / c) = a * c / b
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
-/
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp

@[to_additive (attr := simp)]
/-
**div_inv_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_inv_eq_mul : a / b⁻¹ = a * b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp

@[to_additive]
/-
**div_mul_eq_div_div_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_eq_div_div_swap : a / (b * c) = a / c / b
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
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by
  simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]

end DivisionMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive neg_add]
/-
**mul_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp

@[to_additive]
/-
**inv_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp

@[to_additive]
/-
**div_eq_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_inv_mul : a / b = b⁻¹ * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp

@[to_additive]
/-
**inv_mul_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_eq_div : a⁻¹ * b = b / a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp
/-
**inv_div_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α), a⁻¹ / b = b⁻¹ / 
a
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma inv_div_comm (a b : α) : a⁻¹ / b = b⁻¹ / a := by simp

@[to_additive]
/-
**inv_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul' : (a * b)⁻¹ = a⁻¹ / b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp

@[to_additive]
/-
**inv_div_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_div_inv : a⁻¹ / b⁻¹ = b / a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp

@[to_additive]
/-
**inv_inv_div_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp

@[to_additive]
/-
**one_div_mul_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp

@[to_additive]
/-
**div_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_right_comm : a / b / c = a / c / b
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
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_right_comm : a / b / c = a / c / b := by simp

@[to_additive]
/-
**div_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div : a / b / c = a / (b * c)
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
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_div : a / b / c = a / (b * c) := by simp

@[to_additive]
/-
**div_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul : a / b * c = a / (b / c)
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
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_mul : a / b * c = a / (b / c) := by simp

@[to_additive]
/-
**mul_div_left_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_left_comm : a * (b / c) = b * (a / c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp

@[to_additive]
/-
**mul_div_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_right_comm : a * b / c = a / c * b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_div_right_comm : a * b / c = a / c * b := by simp

@[to_additive]
/-
**div_mul_eq_div_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_eq_div_div : a / (b * c) = a / b / c
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp

@[to_additive]
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
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp

@[to_additive]
/-
**one_div_mul_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_div_mul_eq_div : 1 / a * b = b / a
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_div_mul_eq_div : 1 / a * b = b / a := by simp

@[to_additive]
/-
**mul_comm_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_comm_div : a / b * c = a * (c / b)
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_comm_div : a / b * c = a * (c / b) := by simp

@[to_additive]
/-
**div_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_comm : a / b * c = c / b * a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_mul_comm : a / b * c = c / b * a := by simp

@[to_additive]
/-
**div_mul_eq_div_mul_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c)
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp

@[to_additive]
/-
**div_div_div_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_div_eq : a / b / (c / d) = a * d / (b * c)
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
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp

@[to_additive]
/-
**div_div_div_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_div_comm : a / b / (c / d) = a / c / (b / d)
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
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by simp

@[to_additive]
/-
**div_mul_div_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by simp

@[to_additive]
/-
**mul_div_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_mul_comm : a * b / (c * d) = a / c * (b / d)
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by simp
/-
**mul_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : ℤ), (a * b) 
^ n = a ^ n * b ^ n
参数：a b : α；n : ℤ；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
-/
@[to_additive zsmul_add] lemma mul_zpow : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
  | (n : ℕ) => by simp_rw [zpow_natCast, mul_pow]
  | .negSucc n => by simp_rw [zpow_negSucc, ← inv_pow, mul_inv, mul_pow]

@[to_additive nsmul_sub]
/-
**div_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
参数：a b : α；n : Nat。
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
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]

@[to_additive zsmul_sub]
/-
**div_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_zpow (a b : α) (n : Int) : (a / b) ^ n = a ^ n / b ^ n
参数：a b : α；n : Int。
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
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `inv_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a⁻
¹ ^ n = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma div_zpow (a b : α) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_zpow, inv_zpow]

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G} {n : ℤ}

@[to_additive (attr := simp)]
/-
**div_eq_inv_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_inv_self : a / b = b⁻¹ ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_eq_right`：mul_eq_right : a * b = b ↔ a = 1
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_eq_right]

@[to_additive]
/-
**mul_left_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_left_surjective (a : G) : Surjective (a * ·)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem mul_left_surjective (a : G) : Surjective (a * ·) :=
  fun x ↦ ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]
/-
**mul_right_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_surjective (a : G) : Function.Surjective fun x => x * a
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem mul_right_surjective (a : G) : Function.Surjective fun x ↦ x * a := fun x ↦
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

@[to_additive]
/-
**eq_mul_inv_of_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹
参数：h : a * c = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by simp [h.symm]

@[to_additive]
/-
**eq_inv_mul_of_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c
参数：h : b * a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by simp [h.symm]

@[to_additive]
/-
**inv_mul_eq_of_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c
参数：h : b = a * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by simp [h]

@[to_additive]
/-
**mul_inv_eq_of_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c
参数：h : a = c * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]

@[to_additive]
/-
**eq_mul_of_mul_inv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c
参数：h : a * c⁻¹ = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by simp [h.symm]

@[to_additive]
/-
**eq_mul_of_inv_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c
参数：h : b⁻¹ * a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]

@[to_additive]
/-
**mul_eq_of_eq_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c
参数：h : b = a⁻¹ * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]

@[to_additive]
/-
**mul_eq_of_eq_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c
参数：h : a = c * b⁻¹。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by simp [h]

@[to_additive]
/-
**mul_eq_one_iff_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h ↦ by rw [h, inv_mul_cancel]⟩

@[to_additive]
/-
**mul_eq_one_iff_inv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by
  rw [mul_eq_one_iff_eq_inv, inv_eq_iff_eq_inv]

/-- Variant of `mul_eq_one_iff_eq_inv` with swapped equality. -/
@[to_additive]
/-
**mul_eq_one_iff_eq_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_one_iff_eq_inv' : a * b = 1 ↔ b = a⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_iff_inv_eq`：mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Variant of `mul_eq_one_iff_eq_inv` with swapped equality.
-/
theorem mul_eq_one_iff_eq_inv' : a * b = 1 ↔ b = a⁻¹ := by
  rw [mul_eq_one_iff_inv_eq, eq_comm]

/-- Variant of `mul_eq_one_iff_inv_eq` with swapped equality. -/
@[to_additive]
/-
**mul_eq_one_iff_inv_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_one_iff_inv_eq' : a * b = 1 ↔ b⁻¹ = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Variant of `mul_eq_one_iff_inv_eq` with swapped equality.
-/
theorem mul_eq_one_iff_inv_eq' : a * b = 1 ↔ b⁻¹ = a := by
  rw [mul_eq_one_iff_eq_inv, eq_comm]

@[to_additive]
/-
**eq_inv_iff_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
-/
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm

@[to_additive]
/-
**inv_eq_iff_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_eq_one_iff_inv_eq`：mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b
-/
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm

@[to_additive]
/-
**eq_mul_inv_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h ↦ by rw [h, inv_mul_cancel_right], fun h ↦ by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
/-
**eq_inv_mul_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h ↦ by rw [h, mul_inv_cancel_left], fun h ↦ by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
/-
**inv_mul_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h ↦ by rw [← h, mul_inv_cancel_left], fun h ↦ by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
/-
**mul_inv_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h ↦ by rw [← h, inv_mul_cancel_right], fun h ↦ by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
/-
**mul_inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]

@[to_additive]
/-
**inv_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]

@[to_additive (attr := simp)]
/-
**conj_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `mul_eq_left`：mul_eq_left : a * b = a ↔ b = 1
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1 := by
  rw [mul_inv_eq_one, mul_eq_left]

@[to_additive]
/-
**div_left_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_left_injective : Function.Injective fun a => a / b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
-/
theorem div_left_injective : Function.Injective fun a ↦ a / b := by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ mul_left_injective b⁻¹ h

@[to_additive]
/-
**div_right_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_right_injective : Function.Injective fun a => b / a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem div_right_injective : Function.Injective fun a ↦ b / a := by
  -- FIXME see above
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ inv_injective (mul_right_injective b h)

@[to_additive (attr := simp)]
/-
**div_mul_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_mul_cancel_right (a b : G) : a / (b * a) = b⁻¹
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `mul_div_cancel_right`：mul_div_cancel_right (a b : G) : a * b / b = a
-/
lemma div_mul_cancel_right (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel_right]

@[to_additive (attr := simp)]
/-
**mul_div_mul_right_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_eq_div_div_swap`：div_mul_eq_div_div_swap : a / (b * c) = a / c /
 b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_div_cancel_right`：mul_div_cancel_right (a b : G) : a * b / b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap]; simp only [mul_div_cancel_right]

@[to_additive eq_sub_of_add_eq]
/-
**eq_div_of_mul_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_div_of_mul_eq' (h : a * c = b) : a = b / c
参数：h : a * c = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_cancel_right`：mul_div_cancel_right (a b : G) : a * b / b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]

@[to_additive sub_eq_of_eq_add]
/-
**div_eq_of_eq_mul''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_of_eq_mul'' (h : a = c * b) : a / b = c
参数：h : a = c * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_cancel_right`：mul_div_cancel_right (a b : G) : a * b / b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]

@[to_additive]
/-
**eq_mul_of_div_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_of_div_eq (h : a / c = b) : a = b * c
参数：h : a / c = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]

@[to_additive]
/-
**mul_eq_of_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_of_eq_div (h : a = c / b) : a * b = c
参数：h : a = c / b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]

@[to_additive (attr := simp)]
/-
**div_right_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_right_inj : a / b = a / c ↔ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `div_right_injective`：div_right_injective : Function.Injective fun a => b
 / a
-/
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff

@[to_additive (attr := simp)]
/-
**div_left_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_left_inj : b / a = c / a ↔ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_left_inj`：mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
-/
theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _

@[to_additive (attr := simp)]
/-
**div_mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a / c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
theorem div_mul_div_cancel (a b c : G) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel]

@[to_additive (attr := simp)]
/-
**mul_mul_inv_mul_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_mul_inv_mul_cancel (a b c : G) : a * b * (b⁻¹ * c) = a * c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma mul_mul_inv_mul_cancel (a b c : G) : a * b * (b⁻¹ * c) = a * c := by
  rw [mul_assoc, ← mul_assoc b, mul_inv_cancel, one_mul]

@[to_additive (attr := simp)]
/-
**mul_inv_mul_mul_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_inv_mul_mul_cancel (a b c : G) : a * b⁻¹ * (b * c) = a * c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma mul_inv_mul_mul_cancel (a b c : G) : a * b⁻¹ * (b * c) = a * c := by
  rw [mul_assoc, ← mul_assoc b⁻¹, inv_mul_cancel, one_mul]

@[to_additive (attr := simp)]
/-
**div_div_div_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_div_cancel_right (a b c : G) : a / c / (b / c) = a / b
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
-/
theorem div_div_div_cancel_right (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel]

@[to_additive]
/-
**div_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_one : a / b = 1 ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_div_eq_one`：eq_of_div_eq_one (h : a / b = 1) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
-/
theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h ↦ by rw [h, div_self']⟩

alias ⟨_, div_eq_one_of_eq⟩ := div_eq_one

alias ⟨_, sub_eq_zero_of_eq⟩ := sub_eq_zero

@[to_additive]
/-
**div_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_ne_one : a / b != 1 ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `div_eq_one`：div_eq_one : a / b = 1 ↔ a = b
-/
theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
  not_congr div_eq_one

@[to_additive (attr := simp)]
/-
**div_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_self : a / b = a ↔ b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_eq_left`：mul_eq_left : a * b = a ↔ b = 1
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `inv_eq_one`：inv_eq_one : a⁻¹ = 1 ↔ a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_eq_left, inv_eq_one]

@[to_additive eq_sub_iff_add_eq]
/-
**eq_div_iff_mul_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_div_iff_mul_eq' : a = b / c ↔ a * c = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

@[to_additive]
/-
**div_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_iff_eq_mul : a / b = c ↔ a = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

@[to_additive]
/-
**eq_iff_eq_of_div_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d
参数：H : a / b = c / d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_one`：div_eq_one : a / b = 1 ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by
  rw [← div_eq_one, H, div_eq_one]

@[to_additive]
/-
**leftInverse_div_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftInverse_div_mul_left (c : G) : Function.LeftInverse (fun x => x / c) f
un x => x * c
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_div_cancel_right`：mul_div_cancel_right (a b : G) : a * b / b = a
-/
theorem leftInverse_div_mul_left (c : G) : Function.LeftInverse (fun x ↦ x / c) fun x ↦ x * c :=
  fun x ↦ mul_div_cancel_right x c

@[to_additive]
/-
**leftInverse_mul_left_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftInverse_mul_left_div (c : G) : Function.LeftInverse (fun x => x * c) f
un x => x / c
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
theorem leftInverse_mul_left_div (c : G) : Function.LeftInverse (fun x ↦ x * c) fun x ↦ x / c :=
  fun x ↦ div_mul_cancel x c

@[to_additive]
/-
**leftInverse_mul_right_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftInverse_mul_right_inv_mul (c : G) : Function.LeftInverse (fun x => c *
 x) fun x => c⁻¹ * x
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem leftInverse_mul_right_inv_mul (c : G) :
    Function.LeftInverse (fun x ↦ c * x) fun x ↦ c⁻¹ * x :=
  fun x ↦ mul_inv_cancel_left c x

@[to_additive]
/-
**leftInverse_inv_mul_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftInverse_inv_mul_mul_right (c : G) : Function.LeftInverse (fun x => c⁻¹
 * x) fun x => c * x
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem leftInverse_inv_mul_mul_right (c : G) :
    Function.LeftInverse (fun x ↦ c⁻¹ * x) fun x ↦ c * x :=
  fun x ↦ inv_mul_cancel_left c x

@[to_additive (attr := simp) natAbs_nsmul_eq_zero]
/-
**pow_natAbs_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_natAbs_eq_one : a ^ n.natAbs = 1 ↔ a ^ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
lemma pow_natAbs_eq_one : a ^ n.natAbs = 1 ↔ a ^ n = 1 := by cases n <;> simp

@[to_additive sub_nsmul]
/-
**pow_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sub (a : G) {m n : Nat} (h : n <= m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹
参数：a : G；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_mul_inv_of_mul_eq`：eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
lemma pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by rw [← pow_add, Nat.sub_add_cancel h]

@[to_additive sub_nsmul_neg]
/-
**inv_pow_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_pow_sub (a : G) {m n : Nat} (h : n <= m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ *
 a ^ n
参数：a : G；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_sub`：pow_sub (a : G) {m n : Nat} (h : n <= m) : a ^ (m - n) = a ^ m 
* (a ^ n)⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub a⁻¹ h, inv_pow, inv_pow, inv_inv]

@[to_additive add_one_zsmul]
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
lemma zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.natCast_succ, zpow_natCast, pow_succ]
  | -1 => by simp [Int.add_left_neg]
  | .negSucc (n + 1) => by
    rw [zpow_negSucc, pow_succ', mul_inv_rev, inv_mul_cancel_right]
    rw [Int.negSucc_eq, Int.neg_add, Int.neg_add_cancel_right]
    exact zpow_negSucc _ _

@[to_additive sub_one_zsmul]
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
lemma zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, Int.sub_add_cancel]

@[to_additive add_zsmul]
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
lemma zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, Int.add_sub_assoc]

@[to_additive one_add_zsmul]
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
lemma zpow_one_add (a : G) (n : ℤ) : a ^ (1 + n) = a * a ^ n := by rw [zpow_add, zpow_one]

@[to_additive add_zsmul_self]
/-
**mul_self_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_self_zpow (a : G) (n : Int) : a * a ^ n = a ^ (n + 1)
参数：a : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_comm`：∀ (a b : ℤ), a + b = b + a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
-/
lemma mul_self_zpow (a : G) (n : ℤ) : a * a ^ n = a ^ (n + 1) := by
  rw [Int.add_comm, zpow_add, zpow_one]

@[to_additive add_self_zsmul]
/-
**mul_zpow_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_zpow_self (a : G) (n : Int) : a ^ n * a = a ^ (n + 1)
参数：a : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
-/
lemma mul_zpow_self (a : G) (n : ℤ) : a ^ n * a = a ^ (n + 1) := (zpow_add_one ..).symm
/-
**zpow_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - n) = a ^ m *
 (a ^ n)⁻¹
参数：a : G；m n : ℤ；m - n；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.sub_eq_add_neg`：∀ {a b : ℤ}, a - b = a + -b
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
-/
@[to_additive sub_zsmul] lemma zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [Int.sub_eq_add_neg, zpow_add, zpow_neg]

@[to_additive natCast_sub_natCast_zsmul]
/-
**zpow_natCast_sub_natCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_natCast_sub_natCast (a : G) (m n : Nat) : a ^ (m - n : Int) = a ^ m /
 a ^ n
参数：a : G；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
-/
lemma zpow_natCast_sub_natCast (a : G) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a m n

@[to_additive natCast_sub_one_zsmul]
/-
**zpow_natCast_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_natCast_sub_one (a : G) (n : Nat) : a ^ (n - 1 : Int) = a ^ n / a
参数：a : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
-/
lemma zpow_natCast_sub_one (a : G) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  simpa [div_eq_mul_inv] using zpow_sub a n 1

@[to_additive one_sub_natCast_zsmul]
/-
**zpow_one_sub_natCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_one_sub_natCast (a : G) (n : Nat) : a ^ (1 - n : Int) = a / a ^ n
参数：a : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
-/
lemma zpow_one_sub_natCast (a : G) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a 1 n
/-
**zpow_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ m * a ^ n = a ^ n
 * a ^ m
参数：a : G；m n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Int.add_comm`：∀ (a b : ℤ), a + b = b + a
-/
@[to_additive] lemma zpow_mul_comm (a : G) (m n : ℤ) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← zpow_add, Int.add_comm, zpow_add]
/-
**mul_zpow_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} [inst : Group G] (a b : G) (n : ℤ), (a * b) ^ n * a = a *
 (b * a) ^ n
参数：a b : G；n : ℤ；a * b；b * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `mul_pow_mul`：mul_pow_mul {ea₁ b c₁ : Nat} {xa₁ c₃ d : R} (_ : ea₁ * b = 
c₁) (_ : a₂ ^ b = c₂) (_ : xa₁ ^ c₁ * (nat_lit 1).rawCast = c₃) (_ : c₃ * c₂ = d
)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
@[to_additive] lemma mul_zpow_mul (a b : G) : ∀ n : ℤ, (a * b) ^ n * a = a * (b * a) ^ n
  | (n : ℕ) => by simp [mul_pow_mul]
  | .negSucc n => by simp [inv_mul_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq, mul_assoc, mul_pow_mul]
/-
**zpow_eq_zpow_emod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpow_eq_zpow_emod {x : G} (m : Int) {n : Int} (h : x ^ n = 1) : x ^ m = x 
^ (m % n)
参数：m : Int；h : x ^ n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.emod_add_mul_ediv`：∀ (a b : ℤ), a % b + b * (a / b) = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zpow_eq_zpow_emod {x : G} (m : ℤ) {n : ℤ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) :=
  calc
    x ^ m = x ^ (m % n + n * (m / n)) := by rw [Int.emod_add_mul_ediv]
    _ = x ^ (m % n) := by simp [zpow_add, zpow_mul, h]
/-
**zpow_eq_zpow_emod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zpow_eq_zpow_emod' {x : G} (m : Int) {n : Nat} (h : x ^ n = 1) : x ^ m = x
 ^ (m % (n : Int))
参数：m : Int；h : x ^ n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zpow_eq_zpow_emod`：zpow_eq_zpow_emod {x : G} (m : Int) {n : Int} (h : x 
^ n = 1) : x ^ m = x ^ (m % n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem zpow_eq_zpow_emod' {x : G} (m : ℤ) {n : ℕ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % (n : ℤ)) := zpow_eq_zpow_emod m (by simpa)

@[to_additive, simp]
/-
**zpow_iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} [inst : Group G] (k : ℤ) (n : ℕ), (fun x => x ^ k)^[n] = 
fun x => x ^ k ^ n
参数：k : ℤ；n : ℕ；fun x => x ^ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_iterate (k : ℤ) : ∀ n : ℕ, (fun x : G ↦ x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by ext; simp [Int.pow_zero]
  | n + 1 => by ext; simp [zpow_iterate, Int.pow_succ', zpow_mul]

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the left. For subgroups generated by more than one element, see
`Subgroup.closure_induction_left`. -/
@[to_additive /-- To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the left. For additive subgroups generated by more than one element, see
`AddSubgroup.closure_induction_left`. -/]
/-
**zpow_induction_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_induction_left {g : G} {P : G -> Prop} (h_one : P (1 : G)) (h_mul : f
orall a, P a -> P (g * a)) (h_inv : forall a, P a -> P (g⁻¹ * a)) (n : Int) : P 
(g ^ n)
参数：h_one : P (1 : G)；h_mul : forall a, P a -> P (g * a)；h_inv : forall a, P a ->
 P (g⁻¹ * a)；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `Int.add_comm`：∀ (a b : ℤ), a + b = b + a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `Int.sub_eq_add_neg`：∀ {a b : ℤ}, a - b = a + -b
· 使用引理 `zpow_neg_one`：zpow_neg_one (x : G) : x ^ (-1 : Int) = x⁻¹
-/
lemma zpow_induction_left {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (g * a)) (h_inv : ∀ a, P a → P (g⁻¹ * a)) (n : ℤ) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [Int.add_comm, zpow_add, zpow_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [Int.sub_eq_add_neg, Int.add_comm, zpow_add, zpow_neg_one]
    exact h_inv _ ih

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the right. For subgroups generated by more than one element, see
`Subgroup.closure_induction_right`. -/
@[to_additive /-- To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the right. For additive subgroups generated by more than one element,
see `AddSubgroup.closure_induction_right`. -/]
/-
**zpow_induction_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_induction_right {g : G} {P : G -> Prop} (h_one : P (1 : G)) (h_mul : 
forall a, P a -> P (a * g)) (h_inv : forall a, P a -> P (a * g⁻¹)) (n : Int) : P
 (g ^ n)
参数：h_one : P (1 : G)；h_mul : forall a, P a -> P (a * g)；h_inv : forall a, P a ->
 P (a * g⁻¹)；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用引理 `zpow_sub_one`：zpow_sub_one (a : G) (n : Int) : a ^ (n - 1) = a ^ n * a⁻¹
-/
lemma zpow_induction_right {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (a * g)) (h_inv : ∀ a, P a → P (a * g⁻¹)) (n : ℤ) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [zpow_add_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [zpow_sub_one]
    exact h_inv _ ih

end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive]
/-
**div_eq_of_eq_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c
参数：h : a = b * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]

@[to_additive (attr := simp)]
/-
**mul_div_mul_left_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_comm_assoc`：∀ {G : Type u_1} [inst : CommGroup G] (a b : 
G), a * (b * a⁻¹) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by
  simp

@[to_additive eq_sub_of_add_eq']
/-
**eq_div_of_mul_eq''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_div_of_mul_eq'' (h : c * a = b) : a = b / c
参数：h : c * a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]

@[to_additive]
/-
**eq_mul_of_div_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_of_div_eq' (h : a / b = c) : a = b * c
参数：h : a / b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]

@[to_additive]
/-
**mul_eq_of_eq_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_of_eq_div' (h : b = c / a) : a * b = c
参数：h : b = c / a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  rw [h, div_eq_mul_inv, mul_comm c, mul_inv_cancel_left]

@[to_additive sub_sub_self]
/-
**div_div_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_self' (a b : G) : a / (a / b) = b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_cancel_comm_assoc`：∀ {G : Type u_1} [inst : CommGroup G] (a b : 
G), a * (b * a⁻¹) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_div_self' (a b : G) : a / (a / b) = b := by simp

@[to_additive]
/-
**div_eq_div_mul_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c)
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]

@[to_additive (attr := simp)]
/-
**div_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_cancel (a b : G) : a / (a / b) = b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_div_self'`：div_div_self' (a b : G) : a / (a / b) = b
-/
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b

@[to_additive (attr := simp)]
/-
**div_div_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_cancel_left (a b : G) : a / b / a = b⁻¹
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp

@[to_additive eq_sub_iff_add_eq']
/-
**eq_div_iff_mul_eq''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_div_iff_mul_eq'`：eq_div_iff_mul_eq' : a = b / c ↔ a * c = b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]

@[to_additive]
/-
**div_eq_iff_eq_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_iff_eq_mul' : a / b = c ↔ a = b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_iff_eq_mul`：div_eq_iff_eq_mul : a / b = c ↔ a = c * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]

@[to_additive]
/-
**div_eq_iff_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_iff_comm : a / b = c ↔ a / c = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_iff_eq_mul'`：div_eq_iff_eq_mul' : a / b = c ↔ a = b * c
· 使用定理 `div_eq_iff_eq_mul`：div_eq_iff_eq_mul : a / b = c ↔ a = c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_eq_iff_comm : a / b = c ↔ a / c = b := by rw [div_eq_iff_eq_mul', div_eq_iff_eq_mul]

@[to_additive (attr := simp)]
/-
**mul_div_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_cancel_left (a b : G) : a * b / a = b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem mul_div_cancel_left (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]

@[to_additive (attr := simp)]
/-
**mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_cancel (a b : G) : a * (b / a) = b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
-/
theorem mul_div_cancel (a b : G) : a * (b / a) = b := by
  rw [← mul_div_assoc, mul_div_cancel_left]

@[to_additive (attr := simp)]
/-
**div_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_cancel_left (a b : G) : a / (a * b) = b⁻¹
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
-/
theorem div_mul_cancel_left (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel_left]

-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined in `Algebra.Group.Commute`
@[to_additive]
/-
**mul_mul_inv_cancel'_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} [inst : CommGroup G] (a b : G), a * (b * a⁻¹) = b
参数：a b : G；b * a⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_div_cancel`：mul_div_cancel (a b : G) : a * (b / a) = b
-/
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv, mul_div_cancel a b]

@[to_additive (attr := simp)]
/-
**mul_mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_cancel`：mul_div_cancel (a b : G) : a * (b / a) = b
-/
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  rw [mul_assoc, mul_div_cancel]

@[to_additive (attr := simp)]
/-
**div_mul_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by
  rw [mul_left_comm, div_mul_cancel, mul_comm]

@[to_additive (attr := simp)]
/-
**div_mul_div_cancel'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_div_cancel' (a b c : G) : a / b * (c / a) = c / b
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
-/
theorem div_mul_div_cancel' (a b c : G) : a / b * (c / a) = c / b := by
  rw [mul_comm]; apply div_mul_div_cancel

@[to_additive (attr := simp)]
/-
**mul_div_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul`：div_mul : a / b * c = a / (b / c)
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
-/
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  rw [← div_mul, mul_div_cancel_left]

@[to_additive (attr := simp)]
/-
**div_div_div_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
-/
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel]

@[to_additive]
/-
**div_eq_div_iff_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_iff_eq_mul`：div_eq_iff_eq_mul : a / b = c ↔ a = c * b
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `div_eq_iff_eq_mul'`：div_eq_iff_eq_mul' : a / b = c ↔ a = b * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]

@[to_additive]
/-
**mul_inv_eq_mul_inv_iff_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_eq_mul_inv_iff_mul_eq_mul : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `div_eq_div_iff_mul_eq_mul`：div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a
 * d = c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_eq_mul_inv_iff_mul_eq_mul : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]

@[to_additive]
/-
**inv_mul_eq_inv_mul_iff_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_eq_inv_mul_iff_mul_eq_mul : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `div_eq_div_iff_mul_eq_mul`：div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a
 * d = c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_eq_inv_mul_iff_mul_eq_mul : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [← div_eq_inv_mul, ← div_eq_inv_mul, div_eq_div_iff_mul_eq_mul]

@[to_additive]
/-
**div_eq_div_iff_div_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_iff_eq_mul`：div_eq_iff_eq_mul : a / b = c ↔ a = c * b
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `div_eq_iff_eq_mul'`：div_eq_iff_eq_mul' : a / b = c ↔ a = b * c
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]

@[to_additive (attr := simp)]
/-
**const_div_involutive** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：const_div_involutive (a : G) : Function.Involutive (a / ·)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_div_cancel`：div_div_cancel (a b : G) : a / (a / b) = b
-/
lemma const_div_involutive (a : G) : Function.Involutive (a / ·) :=
  fun _ ↦ div_div_cancel ..

end CommGroup

section multiplicative

variable [Monoid β] (p r : α → α → Prop) [Std.Total r] (f : α → α → β)

@[to_additive additive_of_symm_of_total]
/-
**multiplicative_of_symm_of_total** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multiplicative_of_symm_of_total [Std.Symm p] (hf_swap : forall {a b}, p a 
b -> f a b * f b a = 1) (hmul : forall {a b c}, r a b -> r b c -> p a b -> p b c
 -> p a c -> f a c = f a b * f b c) {a b c : α} (pab : p a b) (pbc : p b c) (pac
 : p a c) : f a c = f a b * f b c
参数：hf_swap : forall {a b}, p a b -> f a b * f b a = 1；hmul : forall {a b c}, r a
 b -> r b c -> p a b -> p b c -> p a c -> f a c = f a b * f b c；pab : p a b；pbc 
: p b c；pac : p a c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma multiplicative_of_symm_of_total [Std.Symm p]
    (hf_swap : ∀ {a b}, p a b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a b → p b c → p a c → f a c = f a b * f b c)
    {a b c : α} (pab : p a b) (pbc : p b c) (pac : p a c) : f a c = f a b * f b c := by
  have hmul' : ∀ {b c}, r b c → p a b → p b c → p a c → f a c = f a b * f b c := by
    intro b c rbc pab pbc pac
    obtain rab | rba := total_of r a b
    · exact hmul rab rbc pab pbc pac
    rw [← one_mul (f a c), ← hf_swap pab, mul_assoc]
    obtain rac | rca := total_of r a c
    · rw [hmul rba rac (symm pab) pac pbc]
    · rw [hmul rbc rca pbc (symm pac) (symm pab), mul_assoc, hf_swap (symm pac), mul_one]
  obtain rbc | rcb := total_of r b c
  · exact hmul' rbc pab pbc pac
  · rw [hmul' rcb pac (symm pbc) pab, mul_assoc, hf_swap (symm pbc), mul_one]

@[deprecated (since := "2026-06-10")]
alias additive_of_symmetric_of_total := additive_of_symm_of_total
@[to_additive existing additive_of_symmetric_of_total, deprecated (since := "2026-06-10")]
alias multiplicative_of_symmetric_of_total := multiplicative_of_symm_of_total

@[deprecated (since := "2026-01-09")]
alias additive_of_symmetric_of_isTotal := additive_of_symm_of_total
@[to_additive existing additive_of_symmetric_of_isTotal, deprecated (since := "2026-01-09")]
alias multiplicative_of_symmetric_of_isTotal := multiplicative_of_symm_of_total

/-- If a binary function from a type equipped with a total relation `r` to a monoid is
  anti-symmetric (i.e. satisfies `f a b * f b a = 1`), in order to show it is multiplicative
  (i.e. satisfies `f a c = f a b * f b c`), we may assume `r a b` and `r b c` are satisfied.
  We allow restricting to a subset specified by a predicate `p`. -/
@[to_additive additive_of_total /-- If a binary function from a type equipped with a total
  relation `r` to an additive monoid is anti-symmetric (i.e. satisfies `f a b + f b a = 0`), in
  order to show it is additive (i.e. satisfies `f a c = f a b + f b c`), we may assume `r a b` and
  `r b c` are satisfied. We allow restricting to a subset specified by a predicate `p`. -/]
/-
**multiplicative_of_total** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicative_of_total (p : α -> Prop) (hswap : forall {a b}, p a -> p b 
-> f a b * f b a = 1) (hmul : forall {a b c}, r a b -> r b c -> p a -> p b -> p 
c -> f a c = f a b * f b c) {a b c : α} (pa : p a) (pb : p b) (pc : p c) : f a c
 = f a b * f b c
参数：p : α -> Prop；hswap : forall {a b}, p a -> p b -> f a b * f b a = 1；hmul : fo
rall {a b c}, r a b -> r b c -> p a -> p b -> p c -> f a c = f a b * f b c；pa : 
p a；pb : p b；pc : p c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用引理 `multiplicative_of_symm_of_total`：multiplicative_of_symm_of_total [Std.Sy
mm p] (hf_swap : forall {a b}, p a b -> f a b * f b a = 1) (hmul : forall {a b c
}, r a b -> r b c -> …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem multiplicative_of_total (p : α → Prop) (hswap : ∀ {a b}, p a → p b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a → p b → p c → f a c = f a b * f b c) {a b c : α}
    (pa : p a) (pb : p b) (pc : p c) : f a c = f a b * f b c := by
  have : Std.Symm (p · ∧ p ·) := { symm _ _ := And.symm }
  apply multiplicative_of_symm_of_total (p · ∧ p ·) r f
  · simp_rw [and_imp]; exact @hswap
  · exact fun rab rbc pab _pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts [⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]

@[deprecated (since := "2026-01-09")]
alias additive_of_isTotal := additive_of_total
@[to_additive existing additive_of_isTotal, deprecated (since := "2026-01-09")]
alias multiplicative_of_isTotal := multiplicative_of_total

end multiplicative

/-- An auxiliary lemma that can be used to prove `⇑(f ^ n) = ⇑f^[n]`. -/
@[to_additive]
/-
**hom_coe_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_4} {F : Type u_5} [inst : Monoid F] (c : F → M → M),   c 1 =
 id → (∀ (f g : F), c (f * g) = c f ∘ c g) → ∀ (f : F) (n : ℕ), c (f ^ n) = (c f
)^[n]
参数：c : F → M → M；∀ (f g : F), c (f * g) = c f ∘ c g；f : F；n : ℕ；f ^ n；c f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma that can be used to prove `⇑(f ^ n) = ⇑f^[n]`.
-/
lemma hom_coe_pow {F : Type*} [Monoid F] (c : F → M → M) (h1 : c 1 = id)
    (hmul : ∀ f g, c (f * g) = c f ∘ c g) (f : F) : ∀ n, c (f ^ n) = (c f)^[n]
  | 0 => by
    rw [pow_zero, h1]
    rfl
  | n + 1 => by rw [pow_succ, iterate_succ, hmul, hom_coe_pow c h1 hmul f n]

/-!
### Instances for `grind`.
-/

open Lean

variable (α : Type*)

/-
**AddCommMonoid.toGrindNatModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommMonoid.toGrindNatModule [s : AddCommMonoid α] : Grind.NatModule α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommMonoid.add_comm`：∀ {M : Type u} [self : AddCommMonoid M] (a b : M
), a + b = b + a
-/
instance AddCommMonoid.toGrindNatModule [s : AddCommMonoid α] :
    Grind.NatModule α :=
  { s with
    nsmul := ⟨s.nsmul⟩
    zero_nsmul := AddMonoid.nsmul_zero
    add_one_nsmul n a := by change (n + 1) • a = n • a + a; rw [add_nsmul, one_nsmul] }
/-
**AddCommGroup.toGrindIntModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommGroup.toGrindIntModule [s : AddCommGroup α] : Grind.IntModule α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.add_comm`：∀ {G : Type u} [self : AddCommGroup G] (a b : G),
 a + b = b + a
-/
instance AddCommGroup.toGrindIntModule [s : AddCommGroup α] :
    Grind.IntModule α :=
  { s with
    nsmul := ⟨s.nsmul⟩
    zsmul := ⟨s.zsmul⟩
    zero_zsmul := SubNegMonoid.zsmul_zero'
    one_zsmul := one_zsmul
    add_zsmul n m a := add_zsmul a n m
    zsmul_natCast_eq_nsmul n a := by simp }
/-
**IsRightCancelAdd.toGrindAddRightCancel** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsRightCancelAdd.toGrindAddRightCancel [AddSemigroup α] [IsRightCancelAdd 
α] : Grind.AddRightCancel α where add_right_cancel _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
-/
instance IsRightCancelAdd.toGrindAddRightCancel [AddSemigroup α] [IsRightCancelAdd α] :
    Grind.AddRightCancel α where
  add_right_cancel _ _ _ := add_right_cancel
