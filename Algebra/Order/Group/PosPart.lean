/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Notation

/-!
# Positive & negative parts

Mathematical structures possessing an absolute value often also possess a unique decomposition of
elements into "positive" and "negative" parts which are in some sense "disjoint" (e.g. the Jordan
decomposition of a measure).

This file provides instances of `PosPart` and `NegPart`, the positive and negative parts of an
element in a lattice ordered group.

## Main statements

* `posPart_sub_negPart`: Every element `a` can be decomposed into `a⁺ - a⁻`, the difference of its
  positive and negative parts.
* `posPart_inf_negPart_eq_zero`: The positive and negative parts are coprime.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

positive part, negative part
-/

@[expose] public section

open Function

variable {α : Type*}

section Lattice
variable [Lattice α]

section DivInvMonoid
variable [DivInvMonoid α] {a b : α}

/-- The *positive part* of an element `a` in a lattice ordered group is `a ⊔ 1`, denoted `a⁺ᵐ`. -/
@[to_additive
/-- The *positive part* of an element `a` in a lattice ordered group is `a ⊔ 0`, denoted `a⁺`. -/]
/-
**instOneLePart** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instOneLePart : OneLePart α where oneLePart a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOneLePart : OneLePart α where
  oneLePart a := a ⊔ 1

/-- The *negative part* of an element `a` in a lattice ordered group is `a⁻¹ ⊔ 1`, denoted `a⁻ᵐ `.
-/
@[to_additive
/-- The *negative part* of an element `a` in a lattice ordered group is `(-a) ⊔ 0`, denoted `a⁻`.
-/]
/-
**instLeOnePart** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instLeOnePart : LeOnePart α where leOnePart a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLeOnePart : LeOnePart α where
  leOnePart a := a⁻¹ ⊔ 1
/-
**leOnePart_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] (a : α), a⁻ᵐ
 = a⁻¹ ⊔ 1
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma leOnePart_def (a : α) : a⁻ᵐ = a⁻¹ ⊔ 1 := rfl
/-
**oneLePart_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] (a : α), a⁺ᵐ
 = a ⊔ 1
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma oneLePart_def (a : α) : a⁺ᵐ = a ⊔ 1 := rfl
/-
**oneLePart_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α], Monotone fu
n x => x⁺ᵐ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
-/
@[to_additive] lemma oneLePart_mono : Monotone (·⁺ᵐ : α → α) :=
  fun _a _b hab ↦ sup_le_sup_right hab _
/-
**oneLePart_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α], 1⁺ᵐ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
@[to_additive (attr := simp high)] lemma oneLePart_one : (1 : α)⁺ᵐ = 1 := sup_idem _

@[to_additive (attr := simp) posPart_nonneg]
/-
**one_le_oneLePart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_oneLePart (a : α) : 1 <= a⁺ᵐ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma one_le_oneLePart (a : α) : 1 ≤ a⁺ᵐ := le_sup_right

@[to_additive (attr := simp) negPart_nonneg]
/-
**one_le_leOnePart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_leOnePart (a : α) : 1 <= a⁻ᵐ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma one_le_leOnePart (a : α) : 1 ≤ a⁻ᵐ := le_sup_right

-- TODO: `to_additive` guesses `nonposPart`
/-
**le_oneLePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] (a : α), a ≤
 a⁺ᵐ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
@[to_additive le_posPart] lemma le_oneLePart (a : α) : a ≤ a⁺ᵐ := le_sup_left
/-
**inv_le_leOnePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] (a : α), a⁻¹
 ≤ a⁻ᵐ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
@[to_additive] lemma inv_le_leOnePart (a : α) : a⁻¹ ≤ a⁻ᵐ := le_sup_left
/-
**oneLePart_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] {a : α}, a⁺ᵐ
 = a ↔ 1 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
-/
@[to_additive (attr := simp)] lemma oneLePart_eq_self : a⁺ᵐ = a ↔ 1 ≤ a := sup_eq_left
/-
**oneLePart_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] {a : α}, a⁺ᵐ
 = 1 ↔ a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
@[to_additive (attr := simp)] lemma oneLePart_eq_one : a⁺ᵐ = 1 ↔ a ≤ 1 := sup_eq_right

@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_one_le⟩ := oneLePart_eq_self
@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_le_one⟩ := oneLePart_eq_one

/-- See also `leOnePart_eq_inv`. -/
@[to_additive /-- See also `negPart_eq_neg`. -/]
/-
**leOnePart_eq_inv'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：leOnePart_eq_inv' : a⁻ᵐ = a⁻¹ ↔ 1 <= a⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a

--- 原说明 ---
See also `leOnePart_eq_inv`.
-/
lemma leOnePart_eq_inv' : a⁻ᵐ = a⁻¹ ↔ 1 ≤ a⁻¹ := sup_eq_left

/-- See also `leOnePart_eq_one`. -/
@[to_additive /-- See also `negPart_eq_zero`. -/]
/-
**leOnePart_eq_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：leOnePart_eq_one' : a⁻ᵐ = 1 ↔ a⁻¹ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b

--- 原说明 ---
See also `leOnePart_eq_one`.
-/
lemma leOnePart_eq_one' : a⁻ᵐ = 1 ↔ a⁻¹ ≤ 1 := sup_eq_right
/-
**oneLePart_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] {a : α}, a⁺ᵐ
 ≤ 1 ↔ a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] lemma oneLePart_le_one : a⁺ᵐ ≤ 1 ↔ a ≤ 1 := by simp [oneLePart]

/-- See also `leOnePart_le_one`. -/
@[to_additive /-- See also `negPart_nonpos`. -/]
/-
**leOnePart_le_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：leOnePart_le_one' : a⁻ᵐ <= 1 ↔ a⁻¹ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `leOnePart_le_one`.
-/
lemma leOnePart_le_one' : a⁻ᵐ ≤ 1 ↔ a⁻¹ ≤ 1 := by simp [leOnePart]
/-
**one_lt_oneLePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] {a : α}, 1 <
 a → 1 < a⁺ᵐ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `oneLePart_eq_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvM
onoid α] {a : α}, a⁺ᵐ = a ↔ 1 ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[to_additive (attr := simp) posPart_pos] lemma one_lt_oneLePart (ha : 1 < a) : 1 < a⁺ᵐ := by
  rwa [oneLePart_eq_self.2 ha.le]
/-
**oneLePart_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] (a : α), a⁻¹
⁺ᵐ = a⁻ᵐ
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma oneLePart_inv (a : α) : a⁻¹⁺ᵐ = a⁻ᵐ := rfl
/-
**oneLePart_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoid α] (a b : α), (
a ⊔ b)⁺ᵐ = a⁺ᵐ ⊔ b⁺ᵐ
参数：a b : α；a ⊔ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_sup_distrib_right`：sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a
 ⊔ c ⊔ (b ⊔ c)
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma oneLePart_max (a b : α) : (max a b)⁺ᵐ = max a⁺ᵐ b⁺ᵐ := by
  simp [oneLePart, sup_sup_distrib_right]

end DivInvMonoid

section Group
variable [Group α] {a b : α}

/-
**leOnePart_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α], 1⁻ᵐ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive (attr := simp)] lemma leOnePart_one : (1 : α)⁻ᵐ = 1 := by simp [leOnePart]
/-
**leOnePart_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α), a⁻¹⁻ᵐ = a⁺
ᵐ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive (attr := simp)] lemma leOnePart_inv (a : α) : a⁻¹⁻ᵐ = a⁺ᵐ := by
  simp [oneLePart, leOnePart]

section MulLeftMono
variable [MulLeftMono α]

/-
**leOnePart_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a : α} [MulLeftMon
o α], a⁻ᵐ = a⁻¹ ↔ a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive (attr := simp)] lemma leOnePart_eq_inv : a⁻ᵐ = a⁻¹ ↔ a ≤ 1 := by simp [leOnePart]

@[to_additive (attr := simp)]
/-
**leOnePart_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：leOnePart_eq_one : a⁻ᵐ = 1 ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma leOnePart_eq_one : a⁻ᵐ = 1 ↔ 1 ≤ a := by simp [leOnePart_eq_one']

@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_le_one⟩ := leOnePart_eq_inv
@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_one_le⟩ := leOnePart_eq_one
/-
**leOnePart_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a : α} [MulLeftMon
o α], a⁻ᵐ ≤ 1 ↔ 1 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] lemma leOnePart_le_one : a⁻ᵐ ≤ 1 ↔ 1 ≤ a := by simp [leOnePart]
/-
**one_lt_leOnePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a : α} [MulLeftMon
o α], a < 1 → 1 < a⁻ᵐ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `leOnePart_eq_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α]
 {a : α} [MulLeftMono α], a⁻ᵐ = a⁻¹ ↔ a ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_lt_inv'`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulLeftStr
ictMono α] {a : α}, 1 < a⁻¹ ↔ a < 1
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
-/
@[to_additive (attr := simp) negPart_pos] lemma one_lt_leOnePart (ha : a < 1) : 1 < a⁻ᵐ := by
  rwa [leOnePart_eq_inv.2 ha.le, one_lt_inv']

-- Bourbaki A.VI.12 Prop 9 a)
/-
**oneLePart_div_leOnePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] (a 
: α), a⁺ᵐ / a⁻ᵐ = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `leOnePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁻ᵐ = a⁻¹ ⊔ 1
· 使用引理 `mul_sup`：mul_sup [MulLeftMono α] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c *
 b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `oneLePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁺ᵐ = a ⊔ 1
-/
@[to_additive (attr := simp)] lemma oneLePart_div_leOnePart (a : α) : a⁺ᵐ / a⁻ᵐ = a := by
  rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul, leOnePart_def, mul_sup, mul_one, mul_inv_cancel,
    sup_comm, oneLePart_def]
/-
**leOnePart_div_oneLePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] (a 
: α), a⁻ᵐ / a⁺ᵐ = a⁻¹
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `oneLePart_div_leOnePart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : G
roup α] [MulLeftMono α] (a : α), a⁺ᵐ / a⁻ᵐ = a
-/
@[to_additive (attr := simp)] lemma leOnePart_div_oneLePart (a : α) : a⁻ᵐ / a⁺ᵐ = a⁻¹ := by
  rw [← inv_div, oneLePart_div_leOnePart]

@[to_additive]
/-
**oneLePart_leOnePart_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：oneLePart_leOnePart_injective : Injective fun a : α => (a⁺ᵐ, a⁻ᵐ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `oneLePart_div_leOnePart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : G
roup α] [MulLeftMono α] (a : α), a⁺ᵐ / a⁻ᵐ = a
-/
lemma oneLePart_leOnePart_injective : Injective fun a : α ↦ (a⁺ᵐ, a⁻ᵐ) := by
  simp only [Injective, Prod.mk.injEq, and_imp]
  rintro a b hpos hneg
  rw [← oneLePart_div_leOnePart a, ← oneLePart_div_leOnePart b, hpos, hneg]

@[to_additive]
/-
**oneLePart_leOnePart_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：oneLePart_leOnePart_inj : a⁺ᵐ = b⁺ᵐ ∧ a⁻ᵐ = b⁻ᵐ ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `oneLePart_leOnePart_injective`：oneLePart_leOnePart_injective : Injective
 fun a : α => (a⁺ᵐ, a⁻ᵐ)
-/
lemma oneLePart_leOnePart_inj : a⁺ᵐ = b⁺ᵐ ∧ a⁻ᵐ = b⁻ᵐ ↔ a = b :=
  Prod.mk_inj.symm.trans oneLePart_leOnePart_injective.eq_iff

section MulRightMono
variable [MulRightMono α]

/-
**leOnePart_anti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] [Mu
lRightMono α], Antitone leOnePart
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
-/
@[to_additive] lemma leOnePart_anti : Antitone (leOnePart : α → α) :=
  fun _a _b hab ↦ sup_le_sup_right (inv_le_inv_iff.2 hab) _

@[to_additive]
/-
**leOnePart_eq_inv_inf_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：leOnePart_eq_inv_inf_one (a : α) : a⁻ᵐ = (a ⊓ 1)⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `leOnePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁻ᵐ = a⁻¹ ⊔ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `inv_sup`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeft
Mono α] [MulRightMono α] (a b : α), (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
lemma leOnePart_eq_inv_inf_one (a : α) : a⁻ᵐ = (a ⊓ 1)⁻¹ := by
  rw [leOnePart_def, ← inv_inj, inv_sup, inv_inv, inv_inv, inv_one]

-- Bourbaki A.VI.12 Prop 9 d)
/-
**oneLePart_mul_leOnePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] [Mu
lRightMono α] (a : α), a⁺ᵐ * a⁻ᵐ = |a|ₘ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `oneLePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁺ᵐ = a ⊔ 1
· 使用引理 `sup_mul`：sup_mul [MulRightMono α] (a b c : α) : (a ⊔ b) * c = a * c ⊔ b 
* c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `leOnePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁻ᵐ = a⁻¹ ⊔ 1
· 使用引理 `mul_sup`：mul_sup [MulLeftMono α] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c *
 b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
-/
@[to_additive] lemma oneLePart_mul_leOnePart (a : α) : a⁺ᵐ * a⁻ᵐ = |a|ₘ := by
  rw [oneLePart_def, sup_mul, one_mul, leOnePart_def, mul_sup, mul_one, mul_inv_cancel, sup_assoc,
    ← sup_assoc a, sup_eq_right.2 le_sup_right]
  exact sup_eq_left.2 <| one_le_mabs a
/-
**leOnePart_mul_oneLePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] [Mu
lRightMono α] (a : α), a⁻ᵐ * a⁺ᵐ = |a|ₘ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `oneLePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁺ᵐ = a ⊔ 1
· 使用引理 `mul_sup`：mul_sup [MulLeftMono α] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c *
 b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `leOnePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁻ᵐ = a⁻¹ ⊔ 1
· 使用引理 `sup_mul`：sup_mul [MulRightMono α] (a b c : α) : (a ⊔ b) * c = a * c ⊔ b 
* c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
-/
@[to_additive] lemma leOnePart_mul_oneLePart (a : α) : a⁻ᵐ * a⁺ᵐ = |a|ₘ := by
  rw [oneLePart_def, mul_sup, mul_one, leOnePart_def, sup_mul, one_mul, inv_mul_cancel, sup_assoc,
    ← @sup_assoc _ _ a, sup_eq_right.2 le_sup_right]
  exact sup_eq_left.2 <| one_le_mabs a

-- Bourbaki A.VI.12 Prop 9 a)
-- a⁺ᵐ ⊓ a⁻ᵐ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
/-
**oneLePart_inf_leOnePart_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] [Mu
lRightMono α] (a : α), a⁺ᵐ ⊓ a⁻ᵐ = 1
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_inj`：mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用引理 `inf_mul`：inf_mul [MulRightMono α] (a b c : α) : (a ⊓ b) * c = a * c ⊓ b 
* c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `oneLePart_div_leOnePart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : G
roup α] [MulLeftMono α] (a : α), a⁺ᵐ / a⁻ᵐ = a
· 使用引理 `leOnePart_eq_inv_inf_one`：leOnePart_eq_inv_inf_one (a : α) : a⁻ᵐ = (a ⊓ 
1)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
@[to_additive] lemma oneLePart_inf_leOnePart_eq_one (a : α) : a⁺ᵐ ⊓ a⁻ᵐ = 1 := by
  rw [← mul_left_inj a⁻ᵐ⁻¹, inf_mul, one_mul, mul_inv_cancel, ← div_eq_mul_inv,
    oneLePart_div_leOnePart, leOnePart_eq_inv_inf_one, inv_inv]
/-
**leOnePart_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] [Mu
lRightMono α] (a b : α), (a ⊓ b)⁻ᵐ = a⁻ᵐ ⊔ b⁻ᵐ
参数：a b : α；a ⊓ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inf`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeft
Mono α] [MulRightMono α] (a b : α), (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹
· 使用定理 `sup_sup_distrib_right`：sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a
 ⊔ c ⊔ (b ⊔ c)
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma leOnePart_min (a b : α) : (min a b)⁻ᵐ = max a⁻ᵐ b⁻ᵐ := by
  simp [leOnePart, inv_inf, sup_sup_distrib_right]

end MulRightMono

end MulLeftMono

end Group

section CommGroup
variable [CommGroup α] [MulLeftMono α]

-- Bourbaki A.VI.12 (with a and b swapped)
/-
**sup_eq_mul_oneLePart_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : CommGroup α] [MulLeftMono α]
 (a b : α), a ⊔ b = b * (a / b)⁺ᵐ
参数：a b : α；a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_sup`：mul_sup [MulLeftMono α] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c *
 b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_div_cancel`：mul_div_cancel (a b : G) : a * (b / a) = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma sup_eq_mul_oneLePart_div (a b : α) : a ⊔ b = b * (a / b)⁺ᵐ := by
  simp [oneLePart, mul_sup]

-- Bourbaki A.VI.12 (with a and b swapped)
/-
**inf_eq_div_oneLePart_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : CommGroup α] [MulLeftMono α]
 (a b : α), a ⊓ b = a / (a / b)⁺ᵐ
参数：a b : α；a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_sup`：div_sup (a b c : α) : c / (a ⊔ b) = c / a ⊓ c / b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_div_cancel`：div_div_cancel (a b : G) : a / (a / b) = b
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma inf_eq_div_oneLePart_div (a b : α) : a ⊓ b = a / (a / b)⁺ᵐ := by
  simp [oneLePart, div_sup, inf_comm]

-- Bourbaki A.VI.12 Prop 9 c)
/-
**le_iff_oneLePart_leOnePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : CommGroup α] [MulLeftMono α]
 (a b : α), a ≤ b ↔ a⁺ᵐ ≤ b⁺ᵐ ∧ b⁻ᵐ ≤ a⁻ᵐ
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `oneLePart_mono`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMono
id α], Monotone fun x => x⁺ᵐ
· 使用定理 `leOnePart_anti`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [
MulLeftMono α] [MulRightMono α], Antitone leOnePart
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `oneLePart_div_leOnePart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : G
roup α] [MulLeftMono α] (a : α), a⁺ᵐ / a⁻ᵐ = a
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_additive] lemma le_iff_oneLePart_leOnePart (a b : α) : a ≤ b ↔ a⁺ᵐ ≤ b⁺ᵐ ∧ b⁻ᵐ ≤ a⁻ᵐ := by
  refine ⟨fun h ↦ ⟨oneLePart_mono h, leOnePart_anti h⟩, fun h ↦ ?_⟩
  rw [← oneLePart_div_leOnePart a, ← oneLePart_div_leOnePart b]
  exact div_le_div'' h.1 h.2

@[to_additive abs_add_eq_two_nsmul_posPart]
/-
**mabs_mul_eq_oneLePart_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mabs_mul_eq_oneLePart_sq (a : α) : |a|ₘ * a = a⁺ᵐ ^ 2
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_mul_div_cancel`：mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a
 * b
· 使用定理 `oneLePart_mul_leOnePart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : G
roup α] [MulLeftMono α] [MulRightMono α] (a : α), a⁺ᵐ * a⁻ᵐ = |a|ₘ
· 使用定理 `oneLePart_div_leOnePart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : G
roup α] [MulLeftMono α] (a : α), a⁺ᵐ / a⁻ᵐ = a
-/
lemma mabs_mul_eq_oneLePart_sq (a : α) : |a|ₘ * a = a⁺ᵐ ^ 2 := by
  rw [sq, ← mul_mul_div_cancel a⁺ᵐ, oneLePart_mul_leOnePart, oneLePart_div_leOnePart]

@[to_additive add_abs_eq_two_nsmul_posPart]
/-
**mul_mabs_eq_oneLePart_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_mabs_eq_oneLePart_sq (a : α) : a * |a|ₘ = a⁺ᵐ ^ 2
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `mabs_mul_eq_oneLePart_sq`：mabs_mul_eq_oneLePart_sq (a : α) : |a|ₘ * a = 
a⁺ᵐ ^ 2
-/
lemma mul_mabs_eq_oneLePart_sq (a : α) : a * |a|ₘ = a⁺ᵐ ^ 2 := by
  rw [mul_comm, mabs_mul_eq_oneLePart_sq]

@[to_additive abs_sub_eq_two_nsmul_negPart]
/-
**mabs_div_eq_leOnePart_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mabs_div_eq_leOnePart_sq (a : α) : |a|ₘ / a = a⁻ᵐ ^ 2
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_div_cancel`：mul_div_div_cancel (a b c : G) : a * b / (a / c) = b
 * c
· 使用定理 `oneLePart_mul_leOnePart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : G
roup α] [MulLeftMono α] [MulRightMono α] (a : α), a⁺ᵐ * a⁻ᵐ = |a|ₘ
· 使用定理 `oneLePart_div_leOnePart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : G
roup α] [MulLeftMono α] (a : α), a⁺ᵐ / a⁻ᵐ = a
-/
lemma mabs_div_eq_leOnePart_sq (a : α) : |a|ₘ / a = a⁻ᵐ ^ 2 := by
  rw [sq, ← mul_div_div_cancel, oneLePart_mul_leOnePart, oneLePart_div_leOnePart]

@[to_additive sub_abs_eq_neg_two_nsmul_negPart]
/-
**div_mabs_eq_inv_leOnePart_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_mabs_eq_inv_leOnePart_sq (a : α) : a / |a|ₘ = (a⁻ᵐ ^ 2)⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mabs_div_eq_leOnePart_sq`：mabs_div_eq_leOnePart_sq (a : α) : |a|ₘ / a = 
a⁻ᵐ ^ 2
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
lemma div_mabs_eq_inv_leOnePart_sq (a : α) : a / |a|ₘ = (a⁻ᵐ ^ 2)⁻¹ := by
  rw [← mabs_div_eq_leOnePart_sq, inv_div]

end CommGroup
end Lattice

section DistribLattice
variable [DistribLattice α] [Group α]

/-
**oneLePart_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : Group α] (a b : α), (
a ⊓ b)⁺ᵐ = a⁺ᵐ ⊓ b⁺ᵐ
参数：a b : α；a ⊓ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma oneLePart_min (a b : α) : (min a b)⁺ᵐ = min a⁺ᵐ b⁺ᵐ := by
  simp [oneLePart, sup_inf_right]

variable [MulLeftMono α] [MulRightMono α]
/-
**leOnePart_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : Group α] [MulLeftMono
 α] [MulRightMono α] (a b : α),   (a ⊔ b)⁻ᵐ = a⁻ᵐ ⊓ b⁻ᵐ
参数：a b : α；a ⊔ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_sup`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeft
Mono α] [MulRightMono α] (a b : α), (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma leOnePart_max (a b : α) : (max a b)⁻ᵐ = min a⁻ᵐ b⁻ᵐ := by
  simp [leOnePart, inv_sup, sup_inf_right]

end DistribLattice

section LinearOrder
variable [LinearOrder α] [Group α] {a b : α}

/-
**oneLePart_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Group α] {a : α}, a⁺ᵐ = 
if 1 ≤ a then a else 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `oneLePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁺ᵐ = a ⊔ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `maxDefault.eq_1`：∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α]
 (a b : α), maxDefault a b = if a ≤ b then b else a
· 使用定理 `sup_eq_maxDefault`：sup_eq_maxDefault [SemilatticeSup α] [DecidableLE α] 
[@Std.Total α (· <= ·)] : (· ⊔ ·) = (maxDefault : α -> α -> α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma oneLePart_eq_ite : a⁺ᵐ = if 1 ≤ a then a else 1 := by
  rw [oneLePart_def, ← maxDefault, ← sup_eq_maxDefault]; simp_rw [sup_comm]
/-
**oneLePart_eq_ite_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Group α] {a : α}, a⁺ᵐ = 
if 1 < a then a else 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma oneLePart_eq_ite_lt : a⁺ᵐ = if 1 < a then a else 1 := by
  grind [oneLePart_eq_ite]
/-
**one_lt_oneLePart_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Group α] {a : α}, 1 < a⁺
ᵐ ↔ 1 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用引理 `one_le_oneLePart`：one_le_oneLePart (a : α) : 1 <= a⁺ᵐ
· 使用定理 `oneLePart_eq_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMo
noid α] {a : α}, a⁺ᵐ = 1 ↔ a ≤ 1
-/
@[to_additive (attr := simp) posPart_pos_iff] lemma one_lt_oneLePart_iff : 1 < a⁺ᵐ ↔ 1 < a :=
  lt_iff_lt_of_le_iff_le <| (one_le_oneLePart _).ge_iff_eq'.trans oneLePart_eq_one

@[to_additive posPart_eq_of_posPart_pos]
/-
**oneLePart_of_one_lt_oneLePart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：oneLePart_of_one_lt_oneLePart (ha : 1 < a⁺ᵐ) : a⁺ᵐ = a
参数：ha : 1 < a⁺ᵐ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `oneLePart_eq_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvM
onoid α] {a : α}, a⁺ᵐ = a ↔ 1 ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `right_lt_sup`：right_lt_sup : b < a ⊔ b ↔ ¬a <= b
· 使用定理 `oneLePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁺ᵐ = a ⊔ 1
-/
lemma oneLePart_of_one_lt_oneLePart (ha : 1 < a⁺ᵐ) : a⁺ᵐ = a := by
  rw [oneLePart_def, right_lt_sup, not_le] at ha; exact oneLePart_eq_self.2 ha.le
/-
**oneLePart_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Group α] {a b : α}, a⁺ᵐ 
< b ↔ a < b ∧ 1 < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_lt_iff`：sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a
-/
@[to_additive (attr := simp)] lemma oneLePart_lt : a⁺ᵐ < b ↔ a < b ∧ 1 < b := sup_lt_iff

section covariantmul
variable [MulLeftMono α]

/-
**leOnePart_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Group α] {a : α} [MulLef
tMono α], a⁻ᵐ = if a ≤ 1 then a⁻¹ else 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `leOnePart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DivInvMonoi
d α] (a : α), a⁻ᵐ = a⁻¹ ⊔ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `maxDefault.eq_1`：∀ {α : Type u_1} [inst : LE α] [inst_1 : DecidableLE α]
 (a b : α), maxDefault a b = if a ≤ b then b else a
· 使用定理 `sup_eq_maxDefault`：sup_eq_maxDefault [SemilatticeSup α] [DecidableLE α] 
[@Std.Total α (· <= ·)] : (· ⊔ ·) = (maxDefault : α -> α -> α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma leOnePart_eq_ite : a⁻ᵐ = if a ≤ 1 then a⁻¹ else 1 := by
  simp_rw [← one_le_inv']; rw [leOnePart_def, ← maxDefault, ← sup_eq_maxDefault]; simp_rw [sup_comm]
/-
**leOnePart_eq_ite_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Group α] {a : α} [MulLef
tMono α], a⁻ᵐ = if a < 1 then a⁻¹ else 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma leOnePart_eq_ite_lt : a⁻ᵐ = if a < 1 then a⁻¹ else 1 := by
  grind [leOnePart_eq_ite, inv_one]
/-
**one_lt_leOnePart_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Group α] {a : α} [MulLef
tMono α], 1 < a⁻ᵐ ↔ a < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用引理 `one_le_leOnePart`：one_le_leOnePart (a : α) : 1 <= a⁻ᵐ
· 使用引理 `leOnePart_eq_one`：leOnePart_eq_one : a⁻ᵐ = 1 ↔ 1 <= a
-/
@[to_additive (attr := simp) negPart_pos_iff] lemma one_lt_leOnePart_iff : 1 < a⁻ᵐ ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le <| (one_le_leOnePart _).ge_iff_eq'.trans leOnePart_eq_one

variable [MulRightMono α]
/-
**leOnePart_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Group α] {a b : α} [MulL
eftMono α] [MulRightMono α],   a⁻ᵐ < b ↔ b⁻¹ < a ∧ 1 < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `sup_lt_iff`：sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_lt'`：inv_lt' : a⁻¹ < b ↔ b⁻¹ < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma leOnePart_lt : a⁻ᵐ < b ↔ b⁻¹ < a ∧ 1 < b :=
  sup_lt_iff.trans <| by rw [inv_lt']

end covariantmul
end LinearOrder

namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, Lattice (α i)] [∀ i, Group (α i)]

/-
**Pi.oneLePart_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_2} {α : ι → Type u_3} [inst : (i : ι) → Lattice (α i)] [inst
_1 : (i : ι) → Group (α i)]   (f : (i : ι) → α i) (i : ι), f⁺ᵐ i = (f i)⁺ᵐ
参数：i : ι；α i；i : ι；α i；f : (i : ι) → α i；i : ι；f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma oneLePart_apply (f : ∀ i, α i) (i : ι) : f⁺ᵐ i = (f i)⁺ᵐ := rfl
/-
**Pi.leOnePart_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_2} {α : ι → Type u_3} [inst : (i : ι) → Lattice (α i)] [inst
_1 : (i : ι) → Group (α i)]   (f : (i : ι) → α i) (i : ι), f⁻ᵐ i = (f i)⁻ᵐ
参数：i : ι；α i；i : ι；α i；f : (i : ι) → α i；i : ι；f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma leOnePart_apply (f : ∀ i, α i) (i : ι) : f⁻ᵐ i = (f i)⁻ᵐ := rfl
/-
**Pi.oneLePart_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_2} {α : ι → Type u_3} [inst : (i : ι) → Lattice (α i)] [inst
_1 : (i : ι) → Group (α i)]   (f : (i : ι) → α i), f⁺ᵐ = fun i => (f i)⁺ᵐ
参数：i : ι；α i；i : ι；α i；f : (i : ι) → α i；f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := push ←)] lemma oneLePart_def (f : ∀ i, α i) : f⁺ᵐ = fun i ↦ (f i)⁺ᵐ := rfl
/-
**Pi.leOnePart_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_2} {α : ι → Type u_3} [inst : (i : ι) → Lattice (α i)] [inst
_1 : (i : ι) → Group (α i)]   (f : (i : ι) → α i), f⁻ᵐ = fun i => (f i)⁻ᵐ
参数：i : ι；α i；i : ι；α i；f : (i : ι) → α i；f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := push ←)] lemma leOnePart_def (f : ∀ i, α i) : f⁻ᵐ = fun i ↦ (f i)⁻ᵐ := rfl

end Pi

