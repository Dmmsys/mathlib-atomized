/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Order.Group.Lattice
public meta import Mathlib.Tactic.ToDual

/-!
# Absolute values in ordered groups

The absolute value of an element in a group which is also a lattice is its supremum with its
negation. This generalizes the usual absolute value on real numbers (`|x| = max x (-x)`).

## Notation

- `|a|`: The *absolute value* of an element `a` of an additive lattice ordered group
- `|a|ₘ`: The *absolute value* of an element `a` of a multiplicative lattice ordered group
-/

@[expose] public section

open Function

variable {α : Type*}

section Lattice
variable [Lattice α]

section Group
variable [Group α] {a b : α}

/-- `mabs a`, denoted `|a|ₘ`, is the absolute value of `a`. -/
@[to_additive (attr := grind) /-- `abs a`, denoted `|a|`, is the absolute value of `a` -/]
/-
**mabs** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mabs (a : α) : α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mabs a`, denoted `|a|ₘ`, is the absolute value of `a`.
-/
def mabs (a : α) : α := a ⊔ a⁻¹

@[inherit_doc mabs]
macro:max atomic("|" noWs) a:term noWs "|ₘ" : term => `(mabs $a)

@[inherit_doc abs]
macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)

/-- Unexpander for the notation `|a|ₘ` for `mabs a`.
Tries to add discretionary parentheses in unparsable cases. -/
@[app_unexpander mabs]
meta def mabs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(|$_|ₘ) | `(-$_) => `(|($a)|ₘ)
    | _ => `(|$a|ₘ)
  | _ => throw ()

/-- Unexpander for the notation `|a|` for `abs a`.
Tries to add discretionary parentheses in unparsable cases. -/
@[app_unexpander abs]
meta def abs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(|$_|ₘ) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()

/-
**mabs_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a b : α}, |a|ₘ ≤ b
 ↔ a ≤ b ∧ a⁻¹ ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
-/
@[to_additive] lemma mabs_le' : |a|ₘ ≤ b ↔ a ≤ b ∧ a⁻¹ ≤ b := sup_le_iff
/-
**le_mabs_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α), a ≤ |a|ₘ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
@[to_additive] lemma le_mabs_self (a : α) : a ≤ |a|ₘ := le_sup_left
/-
**inv_le_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α), a⁻¹ ≤ |a|ₘ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
@[to_additive] lemma inv_le_mabs (a : α) : a⁻¹ ≤ |a|ₘ := le_sup_right
/-
**mabs_le_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a b : α}, a ≤ b → 
a⁻¹ ≤ b → |a|ₘ ≤ |b|ₘ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mabs_le'`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a b : 
α}, |a|ₘ ≤ b ↔ a ≤ b ∧ a⁻¹ ≤ b
· 使用定理 `le_mabs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a 
: α), a ≤ |a|ₘ
-/
@[to_additive] lemma mabs_le_mabs (h₀ : a ≤ b) (h₁ : a⁻¹ ≤ b) : |a|ₘ ≤ |b|ₘ :=
  (mabs_le'.2 ⟨h₀, h₁⟩).trans (le_mabs_self b)
/-
**mabs_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α), |a⁻¹|ₘ = |
a|ₘ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive (attr := simp)] lemma mabs_inv (a : α) : |a⁻¹|ₘ = |a|ₘ := by simp [mabs, sup_comm]
/-
**mabs_div_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a b : α), |a / b|ₘ
 = |b / a|ₘ
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
@[to_additive] lemma mabs_div_comm (a b : α) : |a / b|ₘ = |b / a|ₘ := by rw [← mabs_inv, inv_div]
/-
**mabs_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a b : α} (p : Prop
) [inst_2 : Decidable p],   |if p then a else b|ₘ = if p then |a|ₘ else |b|ₘ
参数：p : Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
-/
@[to_additive] lemma mabs_ite (p : Prop) [Decidable p] :
    |if p then a else b|ₘ = if p then |a|ₘ else |b|ₘ :=
  apply_ite _ _ _ _
/-
**mabs_dite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (p : Prop) [inst_2 
: Decidable p] (a : p → α) (b : ¬p → α),   |if h : p then a h else b h|ₘ = if h 
: p then |a h|ₘ else |b h|ₘ
参数：p : Prop；a : p → α；b : ¬p → α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
-/
@[to_additive] lemma mabs_dite (p : Prop) [Decidable p] (a : p → α) (b : ¬p → α) :
    |if h : p then a h else b h|ₘ = if h : p then |a h|ₘ else |b h|ₘ :=
  apply_dite _ _ _ _

variable [MulLeftMono α]
/-
**mabs_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a : α} [MulLeftMon
o α], 1 ≤ a → |a|ₘ = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inv_le_one'`：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMon
o α] {a : α}, a⁻¹ ≤ 1 ↔ 1 ≤ a
-/
@[to_additive] lemma mabs_of_one_le (h : 1 ≤ a) : |a|ₘ = a :=
  sup_eq_left.2 <| (inv_le_one'.2 h).trans h
/-
**mabs_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a : α} [MulLeftMon
o α], 1 < a → |a|ₘ = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[to_additive] lemma mabs_of_one_lt (h : 1 < a) : |a|ₘ = a := mabs_of_one_le h.le
/-
**mabs_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a : α} [MulLeftMon
o α], a ≤ 1 → |a|ₘ = a⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `one_le_inv'`：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMon
o α] {a : α}, 1 ≤ a⁻¹ ↔ a ≤ 1
-/
@[to_additive] lemma mabs_of_le_one (h : a ≤ 1) : |a|ₘ = a⁻¹ :=
  sup_eq_right.2 <| h.trans (one_le_inv'.2 h)
/-
**mabs_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a : α} [MulLeftMon
o α], a < 1 → |a|ₘ = a⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_of_le_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], a ≤ 1 → |a|ₘ = a⁻¹
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[to_additive] lemma mabs_of_lt_one (h : a < 1) : |a|ₘ = a⁻¹ := mabs_of_le_one h.le
/-
**mabs_le_mabs_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a b : α} [MulLeftM
ono α], 1 ≤ a → a ≤ b → |a|ₘ ≤ |b|ₘ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
@[to_additive] lemma mabs_le_mabs_of_one_le (ha : 1 ≤ a) (hab : a ≤ b) : |a|ₘ ≤ |b|ₘ := by
  rwa [mabs_of_one_le ha, mabs_of_one_le (ha.trans hab)]

attribute [gcongr] abs_le_abs_of_nonneg
/-
**mabs_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α], |1
|ₘ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
@[to_additive (attr := simp)] lemma mabs_one : |(1 : α)|ₘ = 1 := mabs_of_one_le le_rfl

variable [MulRightMono α]
/-
**one_le_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] [Mu
lRightMono α] (a : α), 1 ≤ |a|ₘ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_two_semiclosed`：pow_two_semiclosed {a : α} (ha : 1 <= a ^ 2) : 1 <= 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs.eq_1`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α
), |a|ₘ = a ⊔ a⁻¹
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `mul_sup`：mul_sup [MulLeftMono α] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c *
 b
· 使用引理 `sup_mul`：sup_mul [MulRightMono α] (a b c : α) : (a ⊔ b) * c = a * c ⊔ b 
* c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
@[to_additive (attr := simp) abs_nonneg] lemma one_le_mabs (a : α) : 1 ≤ |a|ₘ := by
  apply pow_two_semiclosed _
  rw [mabs, pow_two, mul_sup, sup_mul, ← pow_two, inv_mul_cancel, sup_comm, ← sup_assoc]
  apply le_sup_right
/-
**mabs_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] [Mu
lRightMono α] (a : α), |(|a|ₘ)|ₘ = |a|ₘ
参数：a : α；|a|ₘ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
-/
@[to_additive (attr := simp)] lemma mabs_mabs (a : α) : |(|a|ₘ)|ₘ = |a|ₘ :=
  mabs_of_one_le <| one_le_mabs a

end Group

section CommGroup
variable [CommGroup α] [MulLeftMono α]

-- Banasiak Proposition 2.12, Zaanen 2nd lecture
/-- The absolute value satisfies the triangle inequality. -/
@[to_additive /-- The absolute value satisfies the triangle inequality. -/]
/-
**mabs_mul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mabs_mul_le (a b : α) : |a * b|ₘ <= |a|ₘ * |b|ₘ
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_mabs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a 
: α), a ≤ |a|ₘ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `inv_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a :
 α), a⁻¹ ≤ |a|ₘ

--- 原说明 ---
The absolute value satisfies the triangle inequality.
-/
lemma mabs_mul_le (a b : α) : |a * b|ₘ ≤ |a|ₘ * |b|ₘ := by
  apply sup_le
  · exact mul_le_mul' (le_mabs_self a) (le_mabs_self b)
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_mabs _) (inv_le_mabs _)

@[to_additive]
/-
**mabs_mabs_div_mabs_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mabs_mabs_div_mabs_le (a b : α) : |(|a|ₘ / |b|ₘ)|ₘ <= |a / b|ₘ
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs.eq_1`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α
), |a|ₘ = a ⊔ a⁻¹
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_le_iff_le_mul`：div_le_iff_le_mul : a / c <= b ↔ a <= b * c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用引理 `mabs_mul_le`：mabs_mul_le (a b : α) : |a * b|ₘ <= |a|ₘ * |b|ₘ
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_le_iff_le_mul`：mul_inv_le_iff_le_mul : a * b⁻¹ <= c ↔ a <= c * b
· 使用定理 `mabs_div_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a
 b : α), |a / b|ₘ = |b / a|ₘ
-/
lemma mabs_mabs_div_mabs_le (a b : α) : |(|a|ₘ / |b|ₘ)|ₘ ≤ |a / b|ₘ := by
  rw [mabs, sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert! mabs_mul_le (a / b) b
    rw [div_mul_cancel]
  · rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, mabs_div_comm]
    convert! mabs_mul_le (b / a) a
    · rw [div_mul_cancel]
/-
**sup_div_inf_eq_mabs_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : CommGroup α] [MulLeftMono α]
 (a b : α), (a ⊔ b) / (a ⊓ b) = |b / a|ₘ
参数：a b : α；a ⊔ b；a ⊓ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `sup_div`：sup_div [MulRightMono α] (a b c : α) : (a ⊔ b) / c = a / c ⊔ b 
/ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `div_inf`：div_inf (a b c : α) : c / (a ⊓ b) = c / a ⊔ c / b
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `mabs.eq_1`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α
), |a|ₘ = a ⊔ a⁻¹
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
-/
@[to_additive] lemma sup_div_inf_eq_mabs_div (a b : α) : (a ⊔ b) / (a ⊓ b) = |b / a|ₘ := by
  simp_rw [sup_div, div_inf, div_self', sup_comm, sup_sup_sup_comm, sup_idem]
  rw [← inv_div, sup_comm (b := _ / _), ← mabs, sup_eq_left]
  exact one_le_mabs _

@[to_additive two_nsmul_sup_eq_add_add_abs_sub]
/-
**sup_sq_eq_mul_mul_mabs_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_sq_eq_mul_mul_mabs_div (a b : α) : (a ⊔ b) ^ 2 = a * b * |b / a|ₘ
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inf_mul_sup`：inf_mul_sup [MulLeftMono α] (a b : α) : (a ⊓ b) * (a ⊔ b) =
 a * b
· 使用定理 `sup_div_inf_eq_mabs_div`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : C
ommGroup α] [MulLeftMono α] (a b : α), (a ⊔ b) / (a ⊓ b) = |b / a|ₘ
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
lemma sup_sq_eq_mul_mul_mabs_div (a b : α) : (a ⊔ b) ^ 2 = a * b * |b / a|ₘ := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_mabs_div, div_eq_mul_inv, ← mul_assoc, mul_comm,
     mul_assoc, ← pow_two, inv_mul_cancel_left]

@[to_additive two_nsmul_inf_eq_add_sub_abs_sub]
/-
**inf_sq_eq_mul_div_mabs_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_sq_eq_mul_div_mabs_div (a b : α) : (a ⊓ b) ^ 2 = a * b / |b / a|ₘ
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inf_mul_sup`：inf_mul_sup [MulLeftMono α] (a b : α) : (a ⊓ b) * (a ⊔ b) =
 a * b
· 使用定理 `sup_div_inf_eq_mabs_div`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : C
ommGroup α] [MulLeftMono α] (a b : α), (a ⊔ b) / (a ⊓ b) = |b / a|ₘ
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_comm_assoc`：∀ {G : Type u_1} [inst : CommGroup G] (a b : 
G), a * (b * a⁻¹) = b
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
lemma inf_sq_eq_mul_div_mabs_div (a b : α) : (a ⊓ b) ^ 2 = a * b / |b / a|ₘ := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_mabs_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev,
    inv_inv, mul_assoc, mul_inv_cancel_comm_assoc, ← pow_two]

-- See, e.g. Zaanen, Lectures on Riesz Spaces
-- 3rd lecture
@[to_additive]
/-
**mabs_div_sup_mul_mabs_div_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mabs_div_sup_mul_mabs_div_inf (a b c : α) : |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c
) / (b ⊓ c)|ₘ = |a / b|ₘ
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_div_inf_eq_mabs_div`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : C
ommGroup α] [MulLeftMono α] (a b : α), (a ⊔ b) / (a ⊓ b) = |b / a|ₘ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_right_idem`：sup_right_idem (a b : α) : a ⊔ b ⊔ b = a ⊔ b
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_right_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ 
b ⊓ b = a ⊓ b
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `inf_mul_sup`：inf_mul_sup [MulLeftMono α] (a b : α) : (a ⊓ b) * (a ⊔ b) =
 a * b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
lemma mabs_div_sup_mul_mabs_div_inf (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ = |a / b|ₘ := by
  let : DistribLattice α := CommGroup.toDistribLattice α
  calc
    |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ =
        (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * |(a ⊓ c) / (b ⊓ c)|ₘ := by
        rw [sup_div_inf_eq_mabs_div]
    _ = (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * ((b ⊓ c ⊔ a ⊓ c) / (b ⊓ c ⊓ (a ⊓ c))) := by
        rw [sup_div_inf_eq_mabs_div (b ⊓ c) (a ⊓ c)]
    _ = (b ⊔ a ⊔ c) / (b ⊓ a ⊔ c) * (((b ⊔ a) ⊓ c) / (b ⊓ a ⊓ c)) := by
        rw [← sup_inf_right, ← inf_sup_right, sup_assoc, sup_comm c (a ⊔ c), sup_right_idem,
          sup_assoc, inf_assoc, inf_comm c (a ⊓ c), inf_right_idem, inf_assoc]
    _ = (b ⊔ a ⊔ c) * ((b ⊔ a) ⊓ c) / ((b ⊓ a ⊔ c) * (b ⊓ a ⊓ c)) := by rw [div_mul_div_comm]
    _ = (b ⊔ a) * c / ((b ⊓ a) * c) := by
        rw [mul_comm, inf_mul_sup, mul_comm (b ⊓ a ⊔ c), inf_mul_sup]
    _ = (b ⊔ a) / (b ⊓ a) := by
        rw [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← div_eq_mul_inv]
    _ = |a / b|ₘ := by rw [sup_div_inf_eq_mabs_div]
/-
**mabs_sup_div_sup_le_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : CommGroup α] [MulLeftMono α]
 (a b c : α), |(a ⊔ c) / (b ⊔ c)|ₘ ≤ |a / b|ₘ
参数：a b c : α；a ⊔ c；b ⊔ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_of_one_le_left`：le_of_mul_le_of_one_le_left [MulLeftMono α]
 {a b c : α} (h : a * b <= c) (hle : 1 <= b) : a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mabs_div_sup_mul_mabs_div_inf`：mabs_div_sup_mul_mabs_div_inf (a b c : α)
 : |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ = |a / b|ₘ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
-/
@[to_additive] lemma mabs_sup_div_sup_le_mabs (a b c : α) : |(a ⊔ c) / (b ⊔ c)|ₘ ≤ |a / b|ₘ := by
  apply le_of_mul_le_of_one_le_left _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]
/-
**mabs_inf_div_inf_le_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : CommGroup α] [MulLeftMono α]
 (a b c : α), |(a ⊓ c) / (b ⊓ c)|ₘ ≤ |a / b|ₘ
参数：a b c : α；a ⊓ c；b ⊓ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_of_one_le_right`：le_of_mul_le_of_one_le_right [MulRightMono
 α] {a b c : α} (h : a * b <= c) (hle : 1 <= a) : b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mabs_div_sup_mul_mabs_div_inf`：mabs_div_sup_mul_mabs_div_inf (a b c : α)
 : |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ = |a / b|ₘ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
-/
@[to_additive] lemma mabs_inf_div_inf_le_mabs (a b c : α) : |(a ⊓ c) / (b ⊓ c)|ₘ ≤ |a / b|ₘ := by
  apply le_of_mul_le_of_one_le_right _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]

-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
@[to_additive Birkhoff_inequalities]
/-
**m_Birkhoff_inequalities** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：m_Birkhoff_inequalities (a b c : α) : |(a ⊔ c) / (b ⊔ c)|ₘ ⊔ |(a ⊓ c) / (b
 ⊓ c)|ₘ <= |a / b|ₘ
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `mabs_sup_div_sup_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : 
CommGroup α] [MulLeftMono α] (a b c : α), |(a ⊔ c) / (b ⊔ c)|ₘ ≤ |a / b|ₘ
· 使用定理 `mabs_inf_div_inf_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : 
CommGroup α] [MulLeftMono α] (a b c : α), |(a ⊓ c) / (b ⊓ c)|ₘ ≤ |a / b|ₘ
-/
lemma m_Birkhoff_inequalities (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)|ₘ ⊔ |(a ⊓ c) / (b ⊓ c)|ₘ ≤ |a / b|ₘ :=
  sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)

end CommGroup
end Lattice

section LinearOrder
variable [Group α] [LinearOrder α] {a b : α}

/-
**mabs_choice** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] (x : α), |x|ₘ =
 x ∨ |x|ₘ = x⁻¹
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_choice`：∀ {α : Type u} [inst : LinearOrder α] (a b : α), max a b = a
 ∨ max a b = b
-/
@[to_additive] lemma mabs_choice (x : α) : |x|ₘ = x ∨ |x|ₘ = x⁻¹ := max_choice _ _
/-
**le_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {a b : α}, a ≤ 
|b|ₘ ↔ a ≤ b ∨ a ≤ b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
-/
@[to_additive] lemma le_mabs : a ≤ |b|ₘ ↔ a ≤ b ∨ a ≤ b⁻¹ := le_max_iff
/-
**mabs_eq_max_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {a : α}, |a|ₘ =
 max a a⁻¹
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma mabs_eq_max_inv : |a|ₘ = max a a⁻¹ := rfl
/-
**lt_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {a b : α}, a < 
|b|ₘ ↔ a < b ∨ a < b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_max_iff`：lt_max_iff : a < max b c ↔ a < b ∨ a < c
-/
@[to_additive] lemma lt_mabs : a < |b|ₘ ↔ a < b ∨ a < b⁻¹ := lt_max_iff
/-
**mabs_by_cases** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {a : α} (P : α 
→ Prop), P a → P a⁻¹ → P |a|ₘ
参数：P : α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_ind`：sup_ind (a b : α) {p : α -> Prop} (ha : p a) (hb : p b) : p (a 
⊔ b)
-/
@[to_additive] lemma mabs_by_cases (P : α → Prop) (h1 : P a) (h2 : P a⁻¹) : P |a|ₘ :=
  sup_ind _ _ h1 h2
/-
**eq_or_eq_inv_of_mabs_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {a b : α}, |a|ₘ
 = b → a = b ∨ a = b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mabs_choice`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
(x : α), |x|ₘ = x ∨ |x|ₘ = x⁻¹
-/
@[to_additive] lemma eq_or_eq_inv_of_mabs_eq (h : |a|ₘ = b) : a = b ∨ a = b⁻¹ := by
  simpa only [← h, eq_comm (a := |a|ₘ), inv_eq_iff_eq_inv] using mabs_choice a
/-
**mabs_eq_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {a b : α}, |a|ₘ
 = |b|ₘ ↔ a = b ∨ a = b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_eq_inv_of_mabs_eq`：∀ {α : Type u_1} [inst : Group α] [inst_1 : Lin
earOrder α] {a b : α}, |a|ₘ = b → a = b ∨ a = b⁻¹
· 使用定理 `mabs_choice`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
(x : α), |x|ₘ = x ∨ |x|ₘ = x⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
-/
@[to_additive] lemma mabs_eq_mabs : |a|ₘ = |b|ₘ ↔ a = b ∨ a = b⁻¹ := by
  refine ⟨fun h ↦ ?_, by rintro (h | h) <;> simp [h]⟩
  obtain rfl | rfl := eq_or_eq_inv_of_mabs_eq h <;>
    simpa only [inv_eq_iff_eq_inv (a := |b|ₘ), inv_inv, inv_inj, or_comm] using mabs_choice b
/-
**isSquare_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {a : α}, IsSqua
re |a|ₘ ↔ IsSquare a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_by_cases`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α
] {a : α} (P : α → Prop), P a → P a⁻¹ → P |a|ₘ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `isSquare_inv`：∀ {α : Type u_2} [inst : DivisionMonoid α] {a : α}, IsSqua
re a⁻¹ ↔ IsSquare a
-/
@[to_additive] lemma isSquare_mabs : IsSquare |a|ₘ ↔ IsSquare a :=
  mabs_by_cases (IsSquare · ↔ _) Iff.rfl isSquare_inv
/-
**lt_of_mabs_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {a b : α}, |a|ₘ
 < b → a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_mabs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a 
: α), a ≤ |a|ₘ
-/
@[to_additive] lemma lt_of_mabs_lt : |a|ₘ < b → a < b := (le_mabs_self _).trans_lt
/-
**map_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {β : Type u_2} 
{F : Type u_3} [inst_2 : Group β]   [inst_3 : LinearOrder β] [inst_4 : FunLike F
 α β] [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) (a : α),   f |a|ₘ = |
f a|ₘ
参数：f : F；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs.eq_1`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α
), |a|ₘ = a ⊔ a⁻¹
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
@[to_additive (attr := simp)] lemma map_mabs {β F : Type*} [Group β] [LinearOrder β] [FunLike F α β]
    [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) (a : α) :
    f |a|ₘ = |f a|ₘ := by
  rw [mabs, mabs, (OrderHomClass.mono f).map_max, map_inv]

variable [MulLeftMono α] {a b : α}
/-
**one_lt_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 {a : α}, 1 < |a|ₘ ↔ a ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_of_lt_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], a < 1 → |a|ₘ = a⁻¹
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `mabs_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLef
tMono α], |1|ₘ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mabs_of_one_lt`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 < a → |a|ₘ = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
@[to_additive (attr := simp) abs_pos] lemma one_lt_mabs : 1 < |a|ₘ ↔ a ≠ 1 := by
  obtain ha | rfl | ha := lt_trichotomy a 1
  · simp [mabs_of_lt_one ha, ha.ne, ha]
  · simp
  · simp [mabs_of_one_lt ha, ha, ha.ne']
/-
**one_lt_mabs_pos_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 {a : α}, 1 < a → 1 < |a|ₘ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_lt_mabs`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
[MulLeftMono α] {a : α}, 1 < |a|ₘ ↔ a ≠ 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
@[to_additive abs_pos_of_pos] lemma one_lt_mabs_pos_of_one_lt (h : 1 < a) : 1 < |a|ₘ :=
  one_lt_mabs.2 h.ne'
/-
**one_lt_mabs_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 {a : α}, a < 1 → 1 < |a|ₘ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_lt_mabs`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
[MulLeftMono α] {a : α}, 1 < |a|ₘ ↔ a ≠ 1
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
@[to_additive abs_pos_of_neg] lemma one_lt_mabs_of_lt_one (h : a < 1) : 1 < |a|ₘ :=
  one_lt_mabs.2 h.ne
/-
**inv_mabs_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 (a : α), |a|ₘ⁻¹ ≤ a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_one'`：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMon
o α] {a : α}, a⁻¹ ≤ 1 ↔ 1 ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mabs_of_le_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], a ≤ 1 → |a|ₘ = a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
@[to_additive] lemma inv_mabs_le (a : α) : |a|ₘ⁻¹ ≤ a := by
  obtain h | h := le_total 1 a
  · simpa [mabs_of_one_le h] using (inv_le_one'.2 h).trans h
  · simp [mabs_of_le_one h]
/-
**one_le_mul_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 (a : α), 1 ≤ a * |a|ₘ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `inv_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a :
 α), a⁻¹ ≤ |a|ₘ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[to_additive add_abs_nonneg] lemma one_le_mul_mabs (a : α) : 1 ≤ a * |a|ₘ := by
  grw [← mul_inv_cancel a, inv_le_mabs a]
/-
**inv_mabs_le_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 (a : α), |a|ₘ⁻¹ ≤ a⁻¹
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
· 使用定理 `inv_mabs_le`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
[MulLeftMono α] (a : α), |a|ₘ⁻¹ ≤ a
-/
@[to_additive] lemma inv_mabs_le_inv (a : α) : |a|ₘ⁻¹ ≤ a⁻¹ := by simpa using inv_mabs_le a⁻¹

variable [MulRightMono α]
/-
**mabs_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 {a : α} [MulRightMono α], |a|ₘ ≠ 1 ↔ a ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.lt_iff_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (b < a ↔ a ≠ b)
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
· 使用定理 `one_lt_mabs`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
[MulLeftMono α] {a : α}, 1 < |a|ₘ ↔ a ≠ 1
-/
@[to_additive] lemma mabs_ne_one : |a|ₘ ≠ 1 ↔ a ≠ 1 :=
  (one_le_mabs a).lt_iff_ne'.symm.trans one_lt_mabs
/-
**mabs_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 {a : α} [MulRightMono α], |a|ₘ = 1 ↔ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `mabs_ne_one`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
[MulLeftMono α] {a : α} [MulRightMono α], |a|ₘ ≠ 1 ↔ a ≠ 1
-/
@[to_additive (attr := simp)] lemma mabs_eq_one : |a|ₘ = 1 ↔ a = 1 := not_iff_not.1 mabs_ne_one
/-
**mabs_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 {a : α} [MulRightMono α], |a|ₘ ≤ 1 ↔ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
· 使用定理 `mabs_eq_one`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
[MulLeftMono α] {a : α} [MulRightMono α], |a|ₘ = 1 ↔ a = 1
-/
@[to_additive (attr := simp) abs_nonpos_iff] lemma mabs_le_one : |a|ₘ ≤ 1 ↔ a = 1 :=
  (one_le_mabs a).ge_iff_eq'.trans mabs_eq_one
/-
**mabs_le_mabs_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 {a b : α} [MulRightMono α],   a ≤ 1 → b ≤ a → |a|ₘ ≤ |b|ₘ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_of_le_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], a ≤ 1 → |a|ₘ = a⁻¹
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
-/
@[to_additive] lemma mabs_le_mabs_of_le_one (ha : a ≤ 1) (hab : b ≤ a) : |a|ₘ ≤ |b|ₘ := by
  rw [mabs_of_le_one ha, mabs_of_le_one (hab.trans ha)]; exact inv_le_inv_iff.mpr hab
/-
**mabs_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 {a b : α} [MulRightMono α],   |a|ₘ < b ↔ b⁻¹ < a ∧ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_lt'`：inv_lt' : a⁻¹ < b ↔ b⁻¹ < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma mabs_lt : |a|ₘ < b ↔ b⁻¹ < a ∧ a < b :=
  max_lt_iff.trans <| and_comm.trans <| by rw [inv_lt']
/-
**inv_lt_of_mabs_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 {a b : α} [MulRightMono α],   |a|ₘ < b → b⁻¹ < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mabs_lt`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [Mul
LeftMono α] {a b : α} [MulRightMono α],   |a|ₘ < b ↔ b⁻¹ < a ∧ a < b
-/
@[to_additive] lemma inv_lt_of_mabs_lt (h : |a|ₘ < b) : b⁻¹ < a := (mabs_lt.mp h).1
/-
**max_div_min_eq_mabs'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 [MulRightMono α] (a b : α),   max a b / min a b = |a / b|ₘ
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `mabs_of_le_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], a ≤ 1 → |a|ₘ = a⁻¹
· 使用定理 `div_le_one'`：div_le_one' : a / b <= 1 ↔ a <= b
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `one_le_div'`：one_le_div' : 1 <= a / b ↔ b <= a
-/
@[to_additive] lemma max_div_min_eq_mabs' (a b : α) : max a b / min a b = |a / b|ₘ := by
  rcases le_total a b with ab | ba
  · rw [max_eq_right ab, min_eq_left ab, mabs_of_le_one, inv_div]
    rwa [div_le_one']
  · rw [max_eq_left ba, min_eq_right ba, mabs_of_one_le]
    rwa [one_le_div']
/-
**max_div_min_eq_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [MulLeftMono α]
 [MulRightMono α] (a b : α),   max a b / min a b = |b / a|ₘ
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_div_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a
 b : α), |a / b|ₘ = |b / a|ₘ
· 使用定理 `max_div_min_eq_mabs'`：∀ {α : Type u_1} [inst : Group α] [inst_1 : Linear
Order α] [MulLeftMono α] [MulRightMono α] (a b : α),   max a b / min a b = |a / 
b|ₘ
-/
@[to_additive] lemma max_div_min_eq_mabs (a b : α) : max a b / min a b = |b / a|ₘ := by
  rw [mabs_div_comm, max_div_min_eq_mabs']

end LinearOrder

namespace LatticeOrderedAddCommGroup
variable [Lattice α] [AddCommGroup α] {s t : Set α}

/-- A set `s` in a lattice ordered group is *solid* if for all `x ∈ s` and all `y ∈ α` such that
`|y| ≤ |x|`, then `y ∈ s`. -/
/-
**LatticeOrderedAddCommGroup.IsSolid** 是 Mathlib 中的一个定义，位于命名空间 `LatticeOrderedAd
dCommGroup`。
形式化陈述：IsSolid (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` in a lattice ordered group is *solid* if for all `x ∈ s` and all `y ∈ 
α` such that
`|y| ≤ |x|`, then `y ∈ s`.
-/
def IsSolid (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, |y| ≤ |x| → y ∈ s

/-- The solid closure of a subset `s` is the smallest superset of `s` that is solid. -/
/-
**LatticeOrderedAddCommGroup.solidClosure** 是 Mathlib 中的一个定义，位于命名空间 `LatticeOrde
redAddCommGroup`。
形式化陈述：solidClosure (s : Set α) : Set α
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The solid closure of a subset `s` is the smallest superset of `s` that is solid.
-/
def solidClosure (s : Set α) : Set α := {y | ∃ x ∈ s, |y| ≤ |x|}
/-
**LatticeOrderedAddCommGroup.isSolid_solidClosure** 是 Mathlib 中的一个引理，位于命名空间 `Lat
ticeOrderedAddCommGroup`。
形式化陈述：isSolid_solidClosure (s : Set α) : IsSolid (solidClosure s)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma isSolid_solidClosure (s : Set α) : IsSolid (solidClosure s) :=
  fun _ ⟨y, hy, hxy⟩ _ hzx ↦ ⟨y, hy, hzx.trans hxy⟩
/-
**LatticeOrderedAddCommGroup.solidClosure_min** 是 Mathlib 中的一个引理，位于命名空间 `Lattice
OrderedAddCommGroup`。
形式化陈述：solidClosure_min (hst : s subseteq t) (ht : IsSolid t) : solidClosure s su
bseteq t
参数：hst : s subseteq t；ht : IsSolid t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma solidClosure_min (hst : s ⊆ t) (ht : IsSolid t) : solidClosure s ⊆ t :=
  fun _ ⟨_, hy, hxy⟩ ↦ ht (hst hy) hxy

end LatticeOrderedAddCommGroup

namespace Pi

variable {ι : Type*} {α : ι → Type*} [∀ i, Group (α i)] (f : (i : ι) → α i)

@[to_additive (attr := simp)]
/-
**Pi.mabs_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mabs_apply [forall i, Lattice (α i)] (i : ι) : |f|ₘ i = |f i|ₘ
参数：α i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mabs_apply [∀ i, Lattice (α i)] (i : ι) : |f|ₘ i = |f i|ₘ := rfl

@[to_additive (attr := push ←)]
/-
**Pi.mabs_def** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mabs_def [forall i, Lattice (α i)] : |f|ₘ = fun i => |f i|ₘ
参数：α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mabs_def [∀ i, Lattice (α i)] : |f|ₘ = fun i ↦ |f i|ₘ := rfl

@[to_additive (attr := simp)]
/-
**Pi.mabs_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mabs_eq_one [forall i, LinearOrder (α i)] [forall i, MulLeftMono (α i)] [f
orall i, MulRightMono (α i)] : |f|ₘ = 1 ↔ f = 1
参数：α i；α i；α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mabs_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLef
tMono α], |1|ₘ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mabs_eq_one [∀ i, LinearOrder (α i)] [∀ i, MulLeftMono (α i)] [∀ i, MulRightMono (α i)] :
    |f|ₘ = 1 ↔ f = 1 :=
  ⟨fun h ↦ funext fun i ↦ by simpa using congr_fun h i, fun h ↦ funext fun i ↦ by simp [h]⟩

end Pi

