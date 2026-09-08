/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Subtype
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.Prop
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Spread
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Inhabit
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.GCongr.Core
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.FastInstance

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

### Transferring orders

- `Order.Preimage`, `Preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `PartialOrder.lift`, `LinearOrder.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra class

* `DenselyOrdered`: An order with no gap, i.e. for any two elements `a < b` there exists `c` such
  that `a < c < b`.

## Notes

`≤` and `<` are highly favored over `≥` and `>` in mathlib. The reason is that we can formulate all
lemmas using `≤`/`<`, and `rw` has trouble unifying `≤` and `≥`. Hence choosing one direction spares
us useless duplication.

Dot notation is particularly useful on `≤` (`LE.le`) and `<` (`LT.lt`). To that end, we
provide many aliases to dot notation-less lemmas. For example, `le_trans` is aliased with
`LE.le.trans` and can be used to construct `hab.trans hbc : a ≤ c` when `hab : a ≤ b`,
`hbc : b ≤ c`, `lt_of_le_of_lt` is aliased as `LE.le.trans_lt` and can be used to construct
`hab.trans hbc : a < c` when `hab : a ≤ b`, `hbc : b < c`.

## TODO

- expand module docs

## Tags

preorder, order, partial order, poset, linear order, chain
-/

@[expose] public section


open Function

variable {ι α β : Type*} {π : ι → Type*}

/-! ### Bare relations -/

attribute [ext] LE

section LE

variable [LE α] {a b c : α}

/-
**LE.le.ge** 是 Mathlib 中的一个定理，位于命名空间 `LE.le`。
形式化陈述：∀ {α : Type u_2} [inst : LE α] {a b : α}, a ≤ b → b ≥ a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual self] protected lemma LE.le.ge (h : a ≤ b) : b ≥ a := h
/-
**GE.ge.le** 是 Mathlib 中的一个定理，位于命名空间 `GE.ge`。
形式化陈述：∀ {α : Type u_2} [inst : LE α] {a b : α}, a ≥ b → b ≤ a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual self] protected lemma GE.ge.le (h : a ≥ b) : b ≤ a := h

@[to_dual trans_eq'] alias LE.le.trans_eq := le_of_le_of_eq
@[to_dual trans_ge] alias Eq.trans_le := le_of_eq_of_le

end LE

section LT

variable [LT α] {a b c : α}

/-
**LT.lt.gt** 是 Mathlib 中的一个定理，位于命名空间 `LT.lt`。
形式化陈述：∀ {α : Type u_2} [inst : LT α] {a b : α}, a < b → b > a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual self] protected lemma LT.lt.gt (h : a < b) : b > a := h
/-
**GT.gt.lt** 是 Mathlib 中的一个定理，位于命名空间 `GT.gt`。
形式化陈述：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual self] protected lemma GT.gt.lt (h : a > b) : b < a := h

@[to_dual trans_eq'] alias LT.lt.trans_eq := lt_of_lt_of_eq
@[to_dual trans_gt] alias Eq.trans_lt := lt_of_eq_of_lt

end LT

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `RelEmbedding` (assuming `f`
is injective). -/
@[simp]
/-
**Order.Preimage** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Order.Preimage (f : α -> β) (s : β -> β -> Prop) (x y : α) : Prop
参数：f : α -> β；s : β -> β -> Prop；x y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on
 `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `RelEmbedd
ing` (assuming `f`
is injective).
-/
def Order.Preimage (f : α → β) (s : β → β → Prop) (x y : α) : Prop := s (f x) (f y)

@[inherit_doc] infixl:80 " ⁻¹'o " => Order.Preimage

/-- The preimage of a decidable order is decidable. -/
/-
**Order.Preimage.decidable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Order.Preimage.decidable (f : α -> β) (s : β -> β -> Prop) [H : DecidableR
el s] : DecidableRel (f ⁻¹'o s)
参数：f : α -> β；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a decidable order is decidable.
-/
instance Order.Preimage.decidable (f : α → β) (s : β → β → Prop) [H : DecidableRel s] :
    DecidableRel (f ⁻¹'o s) := fun _ _ ↦ H _ _

/-! ### Preorders -/

section Preorder

variable [Preorder α] {a b c d : α}

@[to_dual self]
/-
**not_lt_iff_not_le_or_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_lt_iff_not_le_or_ge : ¬a < b ↔ ¬a <= b ∨ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `Classical.not_and_iff_not_or_not`：∀ {a b : Prop}, ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_lt_iff_not_le_or_ge : ¬a < b ↔ ¬a ≤ b ∨ b ≤ a := by
  rw [lt_iff_le_not_ge, Classical.not_and_iff_not_or_not, Classical.not_not]

-- Unnecessary brackets are here for readability
@[to_dual self]
/-
**not_lt_iff_le_imp_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_lt_iff_le_imp_ge : ¬ a < b ↔ (a <= b -> b <= a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma not_lt_iff_le_imp_ge : ¬ a < b ↔ (a ≤ b → b ≤ a) := by
  simp [not_lt_iff_not_le_or_ge, or_iff_not_imp_left]

@[simp]
/-
**lt_self_iff_false** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_self_iff_false (x : α) : x < x ↔ False
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
lemma lt_self_iff_false (x : α) : x < x ↔ False := ⟨lt_irrefl x, False.elim⟩

@[to_dual ge_trans'] alias le_trans' := ge_trans
@[to_dual gt_trans'] alias lt_trans' := gt_trans
@[to_dual trans'] alias LE.le.trans := le_trans
@[to_dual trans'] alias LT.lt.trans := lt_trans
@[to_dual trans_lt'] alias LE.le.trans_lt := lt_of_le_of_lt
@[to_dual trans_le'] alias LT.lt.trans_le := lt_of_lt_of_le

@[to_dual self] alias LE.le.lt_of_not_ge := lt_of_le_not_ge
@[to_dual self] alias LT.lt.le := le_of_lt
@[to_dual self] alias LT.lt.asymm := lt_asymm
@[to_dual self] alias LT.lt.not_gt := lt_asymm

@[to_dual ne'] alias LT.lt.ne := ne_of_lt
@[to_dual ge] alias Eq.le := le_of_eq
/-
**LT.lt.false** 是 Mathlib 中的一个定理，位于命名空间 `LT.lt`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
protected lemma LT.lt.false : a < a → False := lt_irrefl a
/-
**Eq.not_lt** 是 Mathlib 中的一个定理，位于命名空间 `Eq`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
@[to_dual not_gt] protected lemma Eq.not_lt (hab : a = b) : ¬a < b := fun h' ↦ h'.ne hab

@[to_dual ne_of_not_ge]
/-
**ne_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_of_not_le (h : ¬a <= b) : a != b
参数：h : ¬a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem ne_of_not_le (h : ¬a ≤ b) : a ≠ b := fun hab ↦ h (le_of_eq hab)

@[simp, to_dual self]
/-
**le_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_of_subsingleton [Subsingleton α] : a <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma le_of_subsingleton [Subsingleton α] : a ≤ b := (Subsingleton.elim a b).le

-- Making this a @[simp] lemma causes confluence problems downstream.
@[nontriviality, to_dual self]
/-
**not_lt_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_lt_of_subsingleton [Subsingleton α] : ¬a < b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma not_lt_of_subsingleton [Subsingleton α] : ¬a < b := (Subsingleton.elim a b).not_lt

@[to_dual le_of_forall_ge]
/-
**le_of_forall_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_le (H : forall c, c <= a -> c <= b) : a <= b
参数：H : forall c, c <= a -> c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_of_forall_le (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b := H _ le_rfl

@[to_dual forall_ge_iff_le]
/-
**forall_le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_le_iff_le : (forall ⦃c⦄, c <= a -> c <= b) ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_le`：le_of_forall_le (H : forall c, c <= a -> c <= b) : a <=
 b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem forall_le_iff_le : (∀ ⦃c⦄, c ≤ a → c ≤ b) ↔ a ≤ b :=
  ⟨le_of_forall_le, fun h _ hca ↦ le_trans hca h⟩

/-- monotonicity of `≤` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
/-
**le_imp_le_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d) : a <= b -> c <= d
参数：h₁ : c <= a；h₂ : b <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
monotonicity of `≤` with respect to `→`
-/
theorem le_imp_le_of_le_of_le (h₁ : c ≤ a) (h₂ : b ≤ d) : a ≤ b → c ≤ d :=
  fun hab ↦ (h₁.trans hab).trans h₂

/-- monotonicity of `<` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
/-
**lt_imp_lt_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d) : a < b -> c < d
参数：h₁ : c <= a；h₂ : b <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
monotonicity of `<` with respect to `→`
-/
theorem lt_imp_lt_of_le_of_le (h₁ : c ≤ a) (h₂ : b ≤ d) : a < b → c < d :=
  fun hab ↦ (h₁.trans_lt hab).trans_le h₂

/-- monotonicity of `≥` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
/-
**ge_imp_ge_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ge_imp_ge_of_le_of_le (h₁ : a <= c) (h₂ : d <= b) : a >= b -> c >= d
参数：h₁ : a <= c；h₂ : d <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
monotonicity of `≥` with respect to `→`
-/
theorem ge_imp_ge_of_le_of_le (h₁ : a ≤ c) (h₂ : d ≤ b) : a ≥ b → c ≥ d :=
  fun hab ↦ (h₂.trans hab).trans h₁

/-- monotonicity of `>` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
/-
**gt_imp_gt_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gt_imp_gt_of_le_of_le (h₁ : a <= c) (h₂ : d <= b) : a > b -> c > d
参数：h₁ : a <= c；h₂ : d <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
monotonicity of `>` with respect to `→`
-/
theorem gt_imp_gt_of_le_of_le (h₁ : a ≤ c) (h₂ : d ≤ b) : a > b → c > d :=
  fun hab ↦ (h₂.trans_lt hab).trans_le h₁

attribute [gcongr strict] lt_of_lt_of_le lt_of_lt_of_le'

namespace Mathlib.Tactic.GCongr
open Lean Meta

/-- See if the term is `a < b` and the goal is `a ≤ b`. -/
@[gcongr_forward] meta def exactLeOfLt : ForwardExt where
  eval h goal := do
    let le_of_lt := .const ``le_of_lt [← mkFreshLevelMVar]
    let (mvars, _, _) ← forallMetaTelescope (← inferType le_of_lt)
    mvars[4]!.mvarId!.assignIfDefEq h
    goal.assignIfDefEq (mkAppN le_of_lt mvars)

end Mathlib.Tactic.GCongr

end Preorder

/-! ### Partial order -/

section PartialOrder

variable [PartialOrder α] {a b : α}

@[to_dual lt_of_le'] -- TODO: should be called `gt_of_ge`
/-
**Ne.lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.lt_of_le : a != b -> a <= b -> a < b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
-/
theorem Ne.lt_of_le : a ≠ b → a ≤ b → a < b :=
  flip lt_of_le_of_ne

namespace LE.le

@[to_dual antisymm'] alias antisymm := le_antisymm
@[to_dual lt_of_ne'] alias lt_of_ne := lt_of_le_of_ne

@[to_dual lt_iff_ne']
/-
**LE.le.lt_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `LE.le`。
形式化陈述：lt_iff_ne (h : a <= b) : a < b ↔ a != b
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
theorem lt_iff_ne (h : a ≤ b) : a < b ↔ a ≠ b := ⟨ne_of_lt, h.lt_of_ne⟩

@[to_dual not_lt_iff_eq']
/-
**LE.le.not_lt_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `LE.le`。
形式化陈述：not_lt_iff_eq (h : a <= b) : ¬a < b ↔ a = b
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
-/
theorem not_lt_iff_eq (h : a ≤ b) : ¬a < b ↔ a = b := h.lt_iff_ne.not_left

@[to_dual ge_iff_eq']
/-
**LE.le.ge_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `LE.le`。
形式化陈述：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem ge_iff_eq (h : a ≤ b) : b ≤ a ↔ a = b := ⟨h.antisymm, Eq.ge⟩

end LE.le

-- Unnecessary brackets are here for readability
@[to_dual le_imp_eq_iff_le_imp_ge']
/-
**le_imp_eq_iff_le_imp_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_imp_eq_iff_le_imp_ge : (a <= b -> a = b) ↔ (a <= b -> b <= a) where mp 
h hab
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
-/
lemma le_imp_eq_iff_le_imp_ge : (a ≤ b → a = b) ↔ (a ≤ b → b ≤ a) where
  mp h hab := (h hab).ge
  mpr h hab := hab.antisymm (h hab)

-- See Note [decidable namespace]
@[to_dual le_iff_eq_or_lt']
/-
**Decidable.le_iff_eq_or_lt** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α} [DecidableLE α], a ≤ b 
↔ a = b ∨ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Decidable.le_iff_lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b
 : α} [DecidableLE α], a ≤ b ↔ a < b ∨ a = b
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
protected theorem Decidable.le_iff_eq_or_lt [DecidableLE α] : a ≤ b ↔ a = b ∨ a < b :=
  Decidable.le_iff_lt_or_eq.trans or_comm

@[to_dual le_iff_eq_or_lt']
/-
**le_iff_eq_or_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem le_iff_eq_or_lt : a ≤ b ↔ a = b ∨ a < b := le_iff_lt_or_eq.trans or_comm

@[to_dual lt_iff_le_and_ne']
/-
**lt_iff_le_and_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
theorem lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h ↦ ⟨le_of_lt h, ne_of_lt h⟩, fun ⟨h1, h2⟩ ↦ h1.lt_of_ne h2⟩

-- See Note [decidable namespace]
@[to_dual eq_iff_ge_not_gt]
/-
**Decidable.eq_iff_le_not_lt** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α} [DecidableLE α], a = b 
↔ a ≤ b ∧ ¬a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
-/
protected theorem Decidable.eq_iff_le_not_lt [DecidableLE α] : a = b ↔ a ≤ b ∧ ¬a < b :=
  ⟨fun h ↦ ⟨h.le, h ▸ lt_irrefl _⟩, fun ⟨h₁, h₂⟩ ↦
    h₁.antisymm <| Decidable.byContradiction fun h₃ ↦ h₂ (h₁.lt_of_not_ge h₃)⟩

@[to_dual eq_iff_ge_not_gt]
/-
**eq_iff_le_not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.eq_iff_le_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a 
b : α} [DecidableLE α], a = b ↔ a ≤ b ∧ ¬a < b
-/
theorem eq_iff_le_not_lt : a = b ↔ a ≤ b ∧ ¬a < b := open scoped Classical in
  Decidable.eq_iff_le_not_lt

-- See Note [decidable namespace]
@[to_dual eq_or_lt_of_le']
/-
**Decidable.eq_or_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α} [DecidableLE α], a ≤ b 
→ a = b ∨ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Decidable.lt_or_eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b 
: α} [DecidableLE α], a ≤ b → a < b ∨ a = b
-/
protected theorem Decidable.eq_or_lt_of_le [DecidableLE α] (h : a ≤ b) : a = b ∨ a < b :=
  (Decidable.lt_or_eq_of_le h).symm

@[to_dual eq_or_lt_of_le']
/-
**eq_or_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
-/
theorem eq_or_lt_of_le (h : a ≤ b) : a = b ∨ a < b := (lt_or_eq_of_le h).symm

@[to_dual lt_or_eq_dec'] alias LE.le.lt_or_eq_dec := Decidable.lt_or_eq_of_le
@[to_dual eq_or_lt_dec'] alias LE.le.eq_or_lt_dec := Decidable.eq_or_lt_of_le
@[to_dual lt_or_eq'] alias LE.le.lt_or_eq := lt_or_eq_of_le
@[to_dual eq_or_lt'] alias LE.le.eq_or_lt := eq_or_lt_of_le

@[to_dual eq_of_le_of_not_lt']
/-
**eq_of_le_of_not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a = b
参数：h₁ : a <= b；h₂ : ¬a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
-/
theorem eq_of_le_of_not_lt (h₁ : a ≤ b) (h₂ : ¬a < b) : a = b := h₁.eq_or_lt.resolve_right h₂

@[to_dual eq_of_not_lt'] alias LE.le.eq_of_not_lt := eq_of_le_of_not_lt

@[to_dual ge_iff_gt]
/-
**Ne.le_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.le_iff_lt (h : a != b) : a <= b ↔ a < b
参数：h : a != b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Ne.le_iff_lt (h : a ≠ b) : a ≤ b ↔ a < b := ⟨fun h' ↦ lt_of_le_of_ne h' h, fun h ↦ h.le⟩

@[to_dual not_ge_or_not_le]
/-
**Ne.not_le_or_not_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.not_le_or_not_ge (h : a != b) : ¬a <= b ∨ ¬b <= a
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
-/
theorem Ne.not_le_or_not_ge (h : a ≠ b) : ¬a ≤ b ∨ ¬b ≤ a := not_and_or.1 <| le_antisymm_iff.not.1 h

-- See Note [decidable namespace]
@[to_dual ne_iff_gt_iff_ge]
/-
**Decidable.ne_iff_lt_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α} [DecidableEq α], (a ≠ b
 ↔ a < b) ↔ a ≤ b
参数：a ≠ b ↔ a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
protected theorem Decidable.ne_iff_lt_iff_le [DecidableEq α] : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  ⟨fun h ↦ Decidable.byCases le_of_eq (le_of_lt ∘ h.mp), fun h ↦ ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[to_dual (attr := simp) ne_iff_gt_iff_ge]
/-
**ne_iff_lt_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_iff_lt_iff_le : (a != b ↔ a < b) ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.ne_iff_lt_iff_le`：∀ {α : Type u_2} [inst : PartialOrder α] {a 
b : α} [DecidableEq α], (a ≠ b ↔ a < b) ↔ a ≤ b
-/
theorem ne_iff_lt_iff_le : (a ≠ b ↔ a < b) ↔ a ≤ b := open scoped Classical in
  Decidable.ne_iff_lt_iff_le

@[to_dual eq_of_forall_ge_iff]
/-
**eq_of_forall_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b) : a = b
参数：H : forall c, c <= a ↔ c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma eq_of_forall_le_iff (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
  ((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

/-- To prove commutativity of a binary operation `○`, we only to check `a ○ b ≤ b ○ a` for all `a`,
`b`. -/
/-
**commutative_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：commutative_of_le {f : β -> β -> α} (comm : forall a b, f a b <= f b a) : 
forall a b, f a b = f b a
参数：comm : forall a b, f a b <= f b a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b

--- 原说明 ---
To prove commutativity of a binary operation `○`, we only to check `a ○ b ≤ b ○ 
a` for all `a`,
`b`.
-/
lemma commutative_of_le {f : β → β → α} (comm : ∀ a b, f a b ≤ f b a) : ∀ a b, f a b = f b a :=
  fun _ _ ↦ (comm _ _).antisymm <| comm _ _

/-- To prove associativity of a commutative binary operation `○`, we only to check
`(a ○ b) ○ c ≤ a ○ (b ○ c)` for all `a`, `b`, `c`. -/
/-
**associative_of_commutative_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：associative_of_commutative_of_le {f : α -> α -> α} (comm : Std.Commutative
 f) (assoc : forall a b c, f (f a b) c <= f a (f b c)) : Std.Associative f where
 assoc a b c
参数：comm : Std.Commutative f；assoc : forall a b c, f (f a b) c <= f a (f b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a

--- 原说明 ---
To prove associativity of a commutative binary operation `○`, we only to check
`(a ○ b) ○ c ≤ a ○ (b ○ c)` for all `a`, `b`, `c`.
-/
lemma associative_of_commutative_of_le {f : α → α → α} (comm : Std.Commutative f)
    (assoc : ∀ a b c, f (f a b) c ≤ f a (f b c)) : Std.Associative f where
  assoc a b c :=
    le_antisymm (assoc _ _ _) <| by
      rw [comm.comm, comm.comm b, comm.comm _ c, comm.comm a]
      exact assoc ..

end PartialOrder

section LinearOrder
variable [LinearOrder α] {a b : α}

namespace LE.le

@[to_dual lt_or_ge]
/-
**LE.le.gt_or_le** 是 Mathlib 中的一个引理，位于命名空间 `LE.le`。
形式化陈述：gt_or_le (h : a <= b) (c : α) : a < c ∨ c <= b
参数：h : a <= b；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
-/
lemma gt_or_le (h : a ≤ b) (c : α) : a < c ∨ c ≤ b := (lt_or_ge a c).imp id h.trans'

@[to_dual le_or_gt]
/-
**LE.le.ge_or_lt** 是 Mathlib 中的一个引理，位于命名空间 `LE.le`。
形式化陈述：ge_or_lt (h : a <= b) (c : α) : a <= c ∨ c < b
参数：h : a <= b；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
-/
lemma ge_or_lt (h : a ≤ b) (c : α) : a ≤ c ∨ c < b := (le_or_gt a c).imp id h.trans_lt'

@[to_dual le_or_ge]
/-
**LE.le.ge_or_le** 是 Mathlib 中的一个引理，位于命名空间 `LE.le`。
形式化陈述：ge_or_le (h : a <= b) (c : α) : a <= c ∨ c <= b
参数：h : a <= b；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `LE.le.gt_or_le`：gt_or_le (h : a <= b) (c : α) : a < c ∨ c <= b
-/
lemma ge_or_le (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b := (h.gt_or_le c).imp le_of_lt id

end LE.le

namespace LT.lt

@[to_dual lt_or_gt]
/-
**LT.lt.gt_or_lt** 是 Mathlib 中的一个引理，位于命名空间 `LT.lt`。
形式化陈述：gt_or_lt (h : a < b) (c : α) : a < c ∨ c < b
参数：h : a < b；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
-/
lemma gt_or_lt (h : a < b) (c : α) : a < c ∨ c < b := (le_or_gt b c).imp h.trans_le id

end LT.lt

@[to_dual gt_or_lt]
/-
**Ne.lt_or_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
参数：h : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
-/
theorem Ne.lt_or_gt (h : a ≠ b) : a < b ∨ b < a :=
  lt_or_gt_of_ne h

/-- A version of `ne_iff_lt_or_gt` with LHS and RHS reversed. -/
@[to_dual lt_or_gt_iff_ne', simp]
/-
**lt_or_lt_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `ne_iff_lt_or_gt`：ne_iff_lt_or_gt : a != b ↔ a < b ∨ b < a

--- 原说明 ---
A version of `ne_iff_lt_or_gt` with LHS and RHS reversed.
-/
theorem lt_or_lt_iff_ne : a < b ∨ b < a ↔ a ≠ b :=
  ne_iff_lt_or_gt.symm

@[to_dual not_lt_iff_eq_or_lt']
/-
**not_lt_iff_eq_or_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_lt_iff_eq_or_lt : ¬a < b ↔ a = b ∨ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Decidable.le_iff_eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b
 : α} [DecidableLE α], a ≤ b ↔ a = b ∨ a < b
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_lt_iff_eq_or_lt : ¬a < b ↔ a = b ∨ b < a :=
  not_lt.trans <| Decidable.le_iff_eq_or_lt.trans <| or_congr eq_comm Iff.rfl

@[to_dual exists_le_of_linear]
/-
**exists_ge_of_linear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ge_of_linear (a b : α) : exists c, a <= c ∧ b <= c
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem exists_ge_of_linear (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  match le_total a b with
  | Or.inl h => ⟨_, h, le_rfl⟩
  | Or.inr h => ⟨_, le_rfl, h⟩

@[to_dual exists_forall_le_and]
/-
**exists_forall_ge_and** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_forall_ge_and {p q : α -> Prop} : (exists i, forall j >= i, p j) ->
 (exists i, forall j >= i, q j) -> exists i, forall j >= i, p j ∧ q j | ⟨a, ha⟩,
 ⟨b, hb⟩ => let ⟨c, hac, hbc⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ge_of_linear`：exists_ge_of_linear (a b : α) : exists c, a <= c ∧ 
b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma exists_forall_ge_and {p q : α → Prop} :
    (∃ i, ∀ j ≥ i, p j) → (∃ i, ∀ j ≥ i, q j) → ∃ i, ∀ j ≥ i, p j ∧ q j
  | ⟨a, ha⟩, ⟨b, hb⟩ =>
    let ⟨c, hac, hbc⟩ := exists_ge_of_linear a b
    ⟨c, fun _d hcd ↦ ⟨ha _ <| hac.trans hcd, hb _ <| hbc.trans hcd⟩⟩

@[to_dual le_of_forall_gt]
/-
**le_of_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
参数：H : forall c, c < a -> c < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem le_of_forall_lt (H : ∀ c, c < a → c < b) : a ≤ b :=
  le_of_not_gt fun h ↦ lt_irrefl _ (H _ h)

@[to_dual forall_gt_iff_le]
/-
**forall_lt_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_lt_iff_le : (forall ⦃c⦄, c < a -> c < b) ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem forall_lt_iff_le : (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
  ⟨le_of_forall_lt, fun h _ hca ↦ lt_of_lt_of_le hca h⟩

@[to_dual le_of_forall_gt_imp_ne]
/-
**le_of_forall_lt_imp_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_lt_imp_ne (H : forall c < a, c != b) : a <= b
参数：H : forall c < a, c != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
-/
theorem le_of_forall_lt_imp_ne (H : ∀ c < a, c ≠ b) : a ≤ b :=
  le_of_not_gt fun hb ↦ H b hb rfl

@[to_dual lt_of_forall_ge_imp_ne]
/-
**lt_of_forall_le_imp_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_forall_le_imp_ne (H : forall c <= a, c != b) : a < b
参数：H : forall c <= a, c != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
theorem lt_of_forall_le_imp_ne (H : ∀ c ≤ a, c ≠ b) : a < b :=
  lt_of_not_ge fun hb ↦ H b hb rfl

@[to_dual forall_gt_imp_ne_iff_le]
/-
**forall_lt_imp_ne_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_lt_imp_ne_iff_le : (forall c < a, c != b) ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt_imp_ne`：le_of_forall_lt_imp_ne (H : forall c < a, c != b
) : a <= b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem forall_lt_imp_ne_iff_le : (∀ c < a, c ≠ b) ↔ a ≤ b :=
  ⟨le_of_forall_lt_imp_ne, fun ha _ hc ↦ (hc.trans_le ha).ne⟩

@[to_dual forall_ge_imp_ne_iff_lt]
/-
**forall_le_imp_ne_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_le_imp_ne_iff_lt : (forall c <= a, c != b) ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_forall_le_imp_ne`：lt_of_forall_le_imp_ne (H : forall c <= a, c != 
b) : a < b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem forall_le_imp_ne_iff_lt : (∀ c ≤ a, c ≠ b) ↔ a < b :=
  ⟨lt_of_forall_le_imp_ne, fun ha _ hc ↦ (hc.trans_lt ha).ne⟩

@[to_dual eq_of_forall_gt_iff]
/-
**eq_of_forall_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_forall_lt_iff (h : forall c, c < a ↔ c < b) : a = b
参数：h : forall c, c < a ↔ c < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem eq_of_forall_lt_iff (h : ∀ c, c < a ↔ c < b) : a = b :=
  (le_of_forall_lt fun _ ↦ (h _).1).antisymm <| le_of_forall_lt fun _ ↦ (h _).2

@[to_dual self (reorder := ltc gtc)]
/-
**eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt {x y x' y' : α} (ltc : x < y ↔ x' < y'
) (gtc : y < x ↔ y' < x') : x = y ↔ x' = y'
参数：ltc : x < y ↔ x' < y'；gtc : y < x ↔ y' < x'。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt {x y x' y' : α}
    (ltc : x < y ↔ x' < y') (gtc : y < x ↔ y' < x') :
    x = y ↔ x' = y' := by grind

/-! #### `min`/`max` recursors -/

section MinMaxRec
variable {p : α → Prop}

@[to_dual]
/-
**min_rec** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_rec (ha : a <= b -> p a) (hb : b <= a -> p b) : p (min a b)
参数：ha : a <= b -> p a；hb : b <= a -> p b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
lemma min_rec (ha : a ≤ b → p a) (hb : b ≤ a → p b) : p (min a b) := by
  obtain hab | hba := le_total a b <;> simp [min_eq_left, min_eq_right, *]

@[to_dual]
/-
**min_rec'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_rec' (p : α -> Prop) (ha : p a) (hb : p b) : p (min a b)
参数：p : α -> Prop；ha : p a；hb : p b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `min_rec`：min_rec (ha : a <= b -> p a) (hb : b <= a -> p b) : p (min a b)
-/
lemma min_rec' (p : α → Prop) (ha : p a) (hb : p b) : p (min a b) :=
  min_rec (fun _ ↦ ha) fun _ ↦ hb

@[to_dual max_def_lt']
/-
**min_def_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_def_lt (a b : α) : min a b = if a < b then a else b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用引理 `min_def`：min_def (a b : α) : min a b = if a <= b then a else b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma min_def_lt (a b : α) : min a b = if a < b then a else b := by
  rw [min_comm, min_def, ← ite_not]; simp only [not_le]

@[to_dual min_def_lt']
/-
**max_def_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：max_def_lt (a b : α) : max a b = if a < b then b else a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用引理 `max_def`：max_def (a b : α) : max a b = if a <= b then b else a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma max_def_lt (a b : α) : max a b = if a < b then b else a := by
  rw [max_comm, max_def, ← ite_not]; simp only [not_le]

end MinMaxRec
end LinearOrder

/-! ### Implications -/

@[to_dual self]
/-
**lt_imp_lt_of_le_imp_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preorder β] {a b : α} {c d : β
} (H : a <= b -> c <= d) (h : d < c) : b < a
参数：H : a <= b -> c <= d；h : d < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a

--- 原说明 ---
### Implications
-/
lemma lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
  lt_of_not_ge fun h' ↦ (H h').not_gt h

@[to_dual self]
/-
**le_imp_le_iff_lt_imp_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d
 : β} : a <= b -> c <= d ↔ d < c -> b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `le_imp_le_of_lt_imp_lt`：le_imp_le_of_lt_imp_lt {α β} [Preorder α] [Linea
rOrder β] {a b : α} {c d : β} (H : d < c -> b < a) (h : a <= b) : c <= d
-/
lemma le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    a ≤ b → c ≤ d ↔ d < c → b < a :=
  ⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

@[to_dual self]
/-
**lt_iff_lt_of_le_iff_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preorder β] {a b : α} {c d : β} 
(H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a ↔ d < c
参数：H : a <= b ↔ c <= d；H' : b <= a ↔ d <= c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
lemma lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
  lt_iff_le_not_ge.trans <| (and_congr H' (not_congr H)).trans lt_iff_le_not_ge.symm

@[to_dual self]
/-
**lt_iff_lt_of_le_iff_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d 
: β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
参数：H : a <= b ↔ c <= d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
lemma lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c := not_le.symm.trans <| (not_congr H).trans <| not_le

@[to_dual self]
/-
**le_iff_le_iff_lt_iff_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d
 : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
lemma le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
  ⟨lt_iff_lt_of_le_iff_le, fun H ↦ not_lt.symm.trans <| (not_congr H).trans <| not_lt⟩

/-- A symmetric relation implies two values are equal, when it implies they're less-equal. -/
/-
**rel_imp_eq_of_rel_imp_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rel_imp_eq_of_rel_imp_le [PartialOrder β] (r : α -> α -> Prop) [Std.Symm r
] {f : α -> β} (h : forall a b, r a b -> f a <= f b) {a b : α} : r a b -> f a = 
f b
参数：r : α -> α -> Prop；h : forall a b, r a b -> f a <= f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a

--- 原说明 ---
A symmetric relation implies two values are equal, when it implies they're less-
equal.
-/
lemma rel_imp_eq_of_rel_imp_le [PartialOrder β] (r : α → α → Prop) [Std.Symm r] {f : α → β}
    (h : ∀ a b, r a b → f a ≤ f b) {a b : α} : r a b → f a = f b := fun hab ↦
  le_antisymm (h a b hab) (h b a <| symm hab)

/-! ### Extensionality lemmas -/

@[ext]
/-
**Preorder.toLE_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Preorder.toLE_injective : Function.Injective (@Preorder.toLE α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
### Extensionality lemmas
-/
lemma Preorder.toLE_injective : Function.Injective (@Preorder.toLE α) :=
  fun
  | { lt := A_lt, lt_iff_le_not_ge := A_iff, .. },
    { lt := B_lt, lt_iff_le_not_ge := B_iff, .. } => by
    rintro ⟨⟩
    have : A_lt = B_lt := by
      funext a b
      rw [A_iff, B_iff]
    cases this
    congr

@[ext]
/-
**PartialOrder.toPreorder_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PartialOrder.toPreorder_injective : Function.Injective (@PartialOrder.toPr
eorder α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma PartialOrder.toPreorder_injective : Function.Injective (@PartialOrder.toPreorder α) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; congr

@[ext]
/-
**LinearOrder.toPartialOrder_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearOrder.toPartialOrder_injective : Function.Injective (@LinearOrder.to
PartialOrder α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
lemma LinearOrder.toPartialOrder_injective : Function.Injective (@LinearOrder.toPartialOrder α) :=
  fun
  | { le := A_le, lt := A_lt,
      toDecidableLE := A_decidableLE, toDecidableEq := A_decidableEq, toDecidableLT := A_decidableLT
      min := A_min, max := A_max, min_def := A_min_def, max_def := A_max_def,
      compare := A_compare, compare_eq_compareOfLessAndEq := A_compare_canonical, .. },
    { le := B_le, lt := B_lt,
      toDecidableLE := B_decidableLE, toDecidableEq := B_decidableEq, toDecidableLT := B_decidableLT
      min := B_min, max := B_max, min_def := B_min_def, max_def := B_max_def,
      compare := B_compare, compare_eq_compareOfLessAndEq := B_compare_canonical, .. } => by
    rintro ⟨⟩
    obtain rfl : A_decidableLE = B_decidableLE := Subsingleton.elim _ _
    obtain rfl : A_decidableEq = B_decidableEq := Subsingleton.elim _ _
    obtain rfl : A_decidableLT = B_decidableLT := Subsingleton.elim _ _
    have : A_min = B_min := by
      funext a b
      exact (A_min_def _ _).trans (B_min_def _ _).symm
    cases this
    have : A_max = B_max := by
      funext a b
      exact (A_max_def _ _).trans (B_max_def _ _).symm
    cases this
    have : A_compare = B_compare := by
      funext a b
      exact (A_compare_canonical _ _).trans (B_compare_canonical _ _).symm
    congr

@[to_dual self]
/-
**Preorder.ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Preorder.ext {A B : Preorder α} (H : forall x y : α, (haveI
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Preorder.toLE_injective`：Preorder.toLE_injective : Function.Injective (@
Preorder.toLE α)
· 使用定理 `LE.ext`：∀ {α : Type u} {x y : LE α}, LE.le = LE.le → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma Preorder.ext {A B : Preorder α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) : A = B := by
  ext x y; exact H x y

@[to_dual self]
/-
**PartialOrder.ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PartialOrder.ext {A B : PartialOrder α} (H : forall x y : α, (haveI
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PartialOrder.toPreorder_injective`：PartialOrder.toPreorder_injective : F
unction.Injective (@PartialOrder.toPreorder α)
· 使用引理 `Preorder.toLE_injective`：Preorder.toLE_injective : Function.Injective (@
Preorder.toLE α)
· 使用定理 `LE.ext`：∀ {α : Type u} {x y : LE α}, LE.le = LE.le → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma PartialOrder.ext {A B : PartialOrder α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by ext x y; exact H x y

@[to_dual self]
/-
**PartialOrder.ext_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PartialOrder.ext_lt {A B : PartialOrder α} (H : forall x y : α, (haveI
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PartialOrder.toPreorder_injective`：PartialOrder.toPreorder_injective : F
unction.Injective (@PartialOrder.toPreorder α)
· 使用引理 `Preorder.toLE_injective`：Preorder.toLE_injective : Function.Injective (@
Preorder.toLE α)
· 使用定理 `LE.ext`：∀ {α : Type u} {x y : LE α}, LE.le = LE.le → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma PartialOrder.ext_lt {A B : PartialOrder α} (H : ∀ x y : α, (haveI := A; x < y) ↔ x < y) :
    A = B := by ext x y; rw [le_iff_lt_or_eq, @le_iff_lt_or_eq _ A, H]

@[to_dual self]
/-
**LinearOrder.ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearOrder.ext {A B : LinearOrder α} (H : forall x y : α, (haveI
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearOrder.toPartialOrder_injective`：LinearOrder.toPartialOrder_injecti
ve : Function.Injective (@LinearOrder.toPartialOrder α)
· 使用引理 `PartialOrder.toPreorder_injective`：PartialOrder.toPreorder_injective : F
unction.Injective (@PartialOrder.toPreorder α)
· 使用引理 `Preorder.toLE_injective`：Preorder.toLE_injective : Function.Injective (@
Preorder.toLE α)
· 使用定理 `LE.ext`：∀ {α : Type u} {x y : LE α}, LE.le = LE.le → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma LinearOrder.ext {A B : LinearOrder α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by ext x y; exact H x y

@[to_dual self]
/-
**LinearOrder.ext_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearOrder.ext_lt {A B : LinearOrder α} (H : forall x y : α, (haveI
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearOrder.toPartialOrder_injective`：LinearOrder.toPartialOrder_injecti
ve : Function.Injective (@LinearOrder.toPartialOrder α)
· 使用引理 `PartialOrder.ext_lt`：PartialOrder.ext_lt {A B : PartialOrder α} (H : for
all x y : α, (haveI
-/
lemma LinearOrder.ext_lt {A B : LinearOrder α} (H : ∀ x y : α, (haveI := A; x < y) ↔ x < y) :
    A = B := LinearOrder.toPartialOrder_injective (PartialOrder.ext_lt H)

/-! ### `Compl` -/


/-
**Prop.instCompl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instCompl : Compl Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `Compl`
-/
instance Prop.instCompl : Compl Prop :=
  ⟨Not⟩

@[to_dual instHNot]
/-
**Pi.instCompl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instCompl [forall i, Compl (π i)] : Compl (forall i, π i)
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instCompl [∀ i, Compl (π i)] : Compl (∀ i, π i) :=
  ⟨fun x i ↦ (x i)ᶜ⟩

@[to_dual (attr := push ←) hnot_def]
/-
**Pi.compl_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.compl_def [forall i, Compl (π i)] (x : forall i, π i) : xᶜ = fun i => (
x i)ᶜ
参数：π i；x : forall i, π i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.compl_def [∀ i, Compl (π i)] (x : ∀ i, π i) :
    xᶜ = fun i ↦ (x i)ᶜ :=
  rfl

@[to_dual (attr := simp) hnot_apply]
/-
**Pi.compl_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.compl_apply [forall i, Compl (π i)] (x : forall i, π i) (i : ι) : xᶜ i 
= (x i)ᶜ
参数：π i；x : forall i, π i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.compl_apply [∀ i, Compl (π i)] (x : ∀ i, π i) (i : ι) :
    xᶜ i = (x i)ᶜ :=
  rfl
/-
**Std.Irrefl.compl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Irrefl.compl (r : α -> α -> Prop) [Std.Irrefl r] : Std.Refl rᶜ
参数：r : α -> α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Irrefl.irrefl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Irrefl 
r] (a : α), ¬r a a
-/
instance Std.Irrefl.compl (r : α → α → Prop) [Std.Irrefl r] : Std.Refl rᶜ :=
  ⟨@irrefl α r _⟩
/-
**Std.Refl.compl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Refl.compl (r : α -> α -> Prop) [Std.Refl r] : Std.Irrefl rᶜ
参数：r : α -> α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
-/
instance Std.Refl.compl (r : α → α → Prop) [Std.Refl r] : Std.Irrefl rᶜ :=
  ⟨fun a ↦ not_not_intro (refl a)⟩
/-
**compl_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_lt [LinearOrder α] : (· < · : α -> α -> _)ᶜ = (· >= ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_lt [LinearOrder α] : (· < · : α → α → _)ᶜ = (· ≥ ·) := by simp [compl]
/-
**compl_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_le [LinearOrder α] : (· <= · : α -> α -> _)ᶜ = (· > ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_le [LinearOrder α] : (· ≤ · : α → α → _)ᶜ = (· > ·) := by simp [compl]
/-
**compl_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_gt [LinearOrder α] : (· > · : α -> α -> _)ᶜ = (· <= ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_gt [LinearOrder α] : (· > · : α → α → _)ᶜ = (· ≤ ·) := by simp [compl]
/-
**compl_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_ge [LinearOrder α] : (· >= · : α -> α -> _)ᶜ = (· < ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_ge [LinearOrder α] : (· ≥ · : α → α → _)ᶜ = (· < ·) := by simp [compl]
/-
**Ne.instIsEquiv_compl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ne.instIsEquiv_compl : IsEquiv α (· != ·)ᶜ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Ne.instIsEquiv_compl : IsEquiv α (· ≠ ·)ᶜ := by
  convert! eq_isEquiv α
  simp [compl]

/-! ### Order instances on the function space -/

/-
**Pi.preorder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.preorder [forall i, Preorder (π i)] : Preorder (forall i, π i) where __
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Order instances on the function space
-/
instance Pi.preorder [∀ i, Preorder (π i)] : Preorder (∀ i, π i) where
  __ := (inferInstance : LE (∀ i, π i))
  le_refl := fun a i ↦ le_refl (a i)
  le_trans := fun _ _ _ h₁ h₂ i ↦ le_trans (h₁ i) (h₂ i)

@[to_dual self]
/-
**Pi.lt_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : x < y ↔ x <= 
y ∧ exists i, x i < y i
参数：π i。
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
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Pi.lt_def [∀ i, Preorder (π i)] {x y : ∀ i, π i} :
    x < y ↔ x ≤ y ∧ ∃ i, x i < y i := by
  simp +contextual [lt_iff_le_not_ge, Pi.le_def]
/-
**Pi.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.partialOrder [forall i, PartialOrder (π i)] : PartialOrder (forall i, π
 i) where __
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.partialOrder [∀ i, PartialOrder (π i)] : PartialOrder (∀ i, π i) where
  __ := Pi.preorder
  le_antisymm := fun _ _ h1 h2 ↦ funext fun b ↦ (h1 b).antisymm (h2 b)

namespace Sum

variable {α₁ α₂ : Type*} [LE β]

@[simp]
/-
**Sum.elim_le_elim_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sum`。
形式化陈述：elim_le_elim_iff {u₁ v₁ : α₁ -> β} {u₂ v₂ : α₂ -> β} : Sum.elim u₁ u₂ <= S
um.elim v₁ v₂ ↔ u₁ <= v₁ ∧ u₂ <= v₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.forall`：∀ {α : Type u_1} {β : Type u_2} {p : α ⊕ β → Prop},   (∀ (x 
: α ⊕ β), p x) ↔ (∀ (a : α), p (Sum.inl a)) ∧ ∀ (b : β), p (Sum.inr b)
-/
lemma elim_le_elim_iff {u₁ v₁ : α₁ → β} {u₂ v₂ : α₂ → β} :
    Sum.elim u₁ u₂ ≤ Sum.elim v₁ v₂ ↔ u₁ ≤ v₁ ∧ u₂ ≤ v₂ :=
  Sum.forall
/-
**Sum.const_le_elim_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sum`。
形式化陈述：const_le_elim_iff {b : β} {v₁ : α₁ -> β} {v₂ : α₂ -> β} : Function.const _
 b <= Sum.elim v₁ v₂ ↔ Function.const _ b <= v₁ ∧ Function.const _ b <= v₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sum.elim_le_elim_iff`：elim_le_elim_iff {u₁ v₁ : α₁ -> β} {u₂ v₂ : α₂ -> 
β} : Sum.elim u₁ u₂ <= Sum.elim v₁ v₂ ↔ u₁ <= v₁ ∧ u₂ <= v₂
· 使用定理 `Sum.elim_const_const`：∀ {γ : Sort u_1} {α : Type u_2} {β : Type u_3} (c 
: γ),   Sum.elim (Function.const α c) (Function.const β c) = Function.const (α ⊕
 β) c
-/
lemma const_le_elim_iff {b : β} {v₁ : α₁ → β} {v₂ : α₂ → β} :
    Function.const _ b ≤ Sum.elim v₁ v₂ ↔ Function.const _ b ≤ v₁ ∧ Function.const _ b ≤ v₂ :=
  elim_const_const b ▸ elim_le_elim_iff ..
/-
**Sum.elim_le_const_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sum`。
形式化陈述：elim_le_const_iff {b : β} {u₁ : α₁ -> β} {u₂ : α₂ -> β} : Sum.elim u₁ u₂ <
= Function.const _ b ↔ u₁ <= Function.const _ b ∧ u₂ <= Function.const _ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sum.elim_le_elim_iff`：elim_le_elim_iff {u₁ v₁ : α₁ -> β} {u₂ v₂ : α₂ -> 
β} : Sum.elim u₁ u₂ <= Sum.elim v₁ v₂ ↔ u₁ <= v₁ ∧ u₂ <= v₂
· 使用定理 `Sum.elim_const_const`：∀ {γ : Sort u_1} {α : Type u_2} {β : Type u_3} (c 
: γ),   Sum.elim (Function.const α c) (Function.const β c) = Function.const (α ⊕
 β) c
-/
lemma elim_le_const_iff {b : β} {u₁ : α₁ → β} {u₂ : α₂ → β} :
    Sum.elim u₁ u₂ ≤ Function.const _ b ↔ u₁ ≤ Function.const _ b ∧ u₂ ≤ Function.const _ b :=
  elim_const_const b ▸ elim_le_elim_iff ..

end Sum

section Pi

/-- A function `a` is strongly less than a function `b` if `a i < b i` for all `i`. -/
@[to_dual self (reorder := a b)]
/-
**StrongLT** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrongLT [forall i, LT (π i)] (a b : forall i, π i) : Prop
参数：π i；a b : forall i, π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `a` is strongly less than a function `b` if `a i < b i` for all `i`.
-/
def StrongLT [∀ i, LT (π i)] (a b : ∀ i, π i) : Prop :=
  ∀ i, a i < b i

@[inherit_doc]
local infixl:50 " ≺ " => StrongLT

variable [∀ i, Preorder (π i)] {a b c : ∀ i, π i}

@[to_dual self]
/-
**le_of_strongLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_strongLT (h : a ≺ b) : a <= b
参数：h : a ≺ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem le_of_strongLT (h : a ≺ b) : a ≤ b := fun _ ↦ (h _).le

@[to_dual self]
/-
**lt_of_strongLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_strongLT [Nonempty ι] (h : a ≺ b) : a < b
参数：h : a ≺ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `le_of_strongLT`：le_of_strongLT (h : a ≺ b) : a <= b
-/
theorem lt_of_strongLT [Nonempty ι] (h : a ≺ b) : a < b := by
  inhabit ι
  exact Pi.lt_def.2 ⟨le_of_strongLT h, default, h _⟩

@[to_dual (reorder := hab hbc) strongLT_of_le_of_strongLT]
/-
**strongLT_of_strongLT_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strongLT_of_strongLT_of_le (hab : a ≺ b) (hbc : b <= c) : a ≺ c
参数：hab : a ≺ b；hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem strongLT_of_strongLT_of_le (hab : a ≺ b) (hbc : b ≤ c) : a ≺ c := fun _ ↦
  (hab _).trans_le <| hbc _

@[to_dual self] alias StrongLT.le := le_of_strongLT

@[to_dual self] alias StrongLT.lt := lt_of_strongLT

@[to_dual (reorder := hab hbc) LE.le.trans_strongLT]
alias StrongLT.trans_le := strongLT_of_strongLT_of_le

end Pi

section Function

variable [DecidableEq ι] [∀ i, Preorder (π i)] {x y : ∀ i, π i} {i : ι} {a b : π i}

@[to_dual update_le_iff]
/-
**le_update_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_update_iff : x <= Function.update y i a ↔ x i <= a ∧ forall (j) (_ : j 
!= i), x j <= y j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.forall_update_iff`：forall_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (forall x, p x (update f a b x)) ↔ p a
 b ∧ forall x, x…
-/
theorem le_update_iff : x ≤ Function.update y i a ↔ x i ≤ a ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z ↦ x j ≤ z

@[to_dual self]
/-
**update_le_update_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：update_le_update_iff : Function.update x i a <= Function.update y i b ↔ a 
<= b ∧ forall (j) (_ : j != i), x j <= y j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem update_le_update_iff :
    Function.update x i a ≤ Function.update y i b ↔ a ≤ b ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j := by
  simp +contextual [update_le_iff]

@[simp, to_dual self]
/-
**update_le_update_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：update_le_update_iff' : update x i a <= update x i b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `instIsPreorder_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.IsPreo
rder α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem update_le_update_iff' : update x i a ≤ update x i b ↔ a ≤ b := by
  simp [update_le_update_iff]

@[simp, to_dual self]
/-
**update_lt_update_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：update_lt_update_iff : update x i a < update x i b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `update_le_update_iff'`：update_le_update_iff' : update x i a <= update x 
i b ↔ a <= b
-/
theorem update_lt_update_iff : update x i a < update x i b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' update_le_update_iff' update_le_update_iff'

@[to_dual (attr := simp) update_le_self_iff]
/-
**le_update_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_update_self_iff : x <= update x i a ↔ x i <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `instIsPreorder_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.IsPreo
rder α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_update_self_iff : x ≤ update x i a ↔ x i ≤ a := by simp [le_update_iff]

@[to_dual (attr := simp) update_lt_self_iff]
/-
**lt_update_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_update_self_iff : x < update x i a ↔ x i < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_update_self_iff : x < update x i a ↔ x i < a := by simp [lt_iff_le_not_ge]

end Function

@[to_dual instHImp]
/-
**Pi.instSDiff** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instSDiff [forall i, SDiff (π i)] : SDiff (forall i, π i)
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instSDiff [∀ i, SDiff (π i)] : SDiff (∀ i, π i) :=
  ⟨fun x y i ↦ x i \ y i⟩

@[to_dual (attr := push ←) himp_def]
/-
**Pi.sdiff_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.sdiff_def [forall i, SDiff (π i)] (x y : forall i, π i) : x \ y = fun i
 => x i \ y i
参数：π i；x y : forall i, π i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.sdiff_def [∀ i, SDiff (π i)] (x y : ∀ i, π i) :
    x \ y = fun i ↦ x i \ y i :=
  rfl

@[to_dual (attr := simp) himp_apply]
/-
**Pi.sdiff_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.sdiff_apply [forall i, SDiff (π i)] (x y : forall i, π i) (i : ι) : (x 
\ y) i = x i \ y i
参数：π i；x y : forall i, π i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.sdiff_apply [∀ i, SDiff (π i)] (x y : ∀ i, π i) (i : ι) :
    (x \ y) i = x i \ y i :=
  rfl

namespace Function

variable [Preorder α] [Nonempty β] {a b : α}

@[simp, to_dual self]
/-
**Function.const_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_le_const : const β a <= const β b ↔ a <= b
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
theorem const_le_const : const β a ≤ const β b ↔ a ≤ b := by simp [Pi.le_def]

@[simp, to_dual self]
/-
**Function.const_lt_const** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_lt_const : const β a < const β b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem const_lt_const : const β a < const β b ↔ a < b := by simpa [Pi.lt_def] using le_of_lt

end Function

/-! ### Pullbacks of order instances -/

/-- Pull back a `Preorder` instance along an injective function.

See note [reducible non-instances]. -/
@[to_dual self]
/-
**Function.Injective.preorder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Injective.preorder [Preorder β] [LE α] [LT α] (f : α -> β) (le : 
forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y) : Preo
rder α where le_refl _
参数：f : α -> β；le : forall {x y}, f x <= f y ↔ x <= y；lt : forall {x y}, f x < f 
y ↔ x < y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a `Preorder` instance along an injective function.

See note [reducible non-instances].
-/
abbrev Function.Injective.preorder [Preorder β] [LE α] [LT α] (f : α → β)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y) :
    Preorder α where
  le_refl _ := le.1 <| le_refl _
  le_trans _ _ _ h₁ h₂ := le.1 <| le_trans (le.2 h₁) (le.2 h₂)
  lt_iff_le_not_ge _ _ := by
    rw [← le, ← le, ← lt, lt_iff_le_not_ge]

/-- Pull back a `PartialOrder` instance along an injective function.

See note [reducible non-instances]. -/
@[to_dual self]
/-
**Function.Injective.partialOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Injective.partialOrder [PartialOrder β] [LE α] [LT α] (f : α -> β
) (hf : Function.Injective f) (le : forall {x y}, f x <= f y ↔ x <= y) (lt : for
all {x y}, f x < f y ↔ x < y) : PartialOrder α where __
参数：f : α -> β；hf : Function.Injective f；le : forall {x y}, f x <= f y ↔ x <= y；l
t : forall {x y}, f x < f y ↔ x < y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a `PartialOrder` instance along an injective function.

See note [reducible non-instances].
-/
abbrev Function.Injective.partialOrder [PartialOrder β] [LE α] [LT α] (f : α → β)
    (hf : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y) :
    PartialOrder α where
  __ := Function.Injective.preorder f le lt
  le_antisymm _ _ h₁ h₂ := hf <| le_antisymm (le.2 h₁) (le.2 h₂)

/-- Pull back a `LinearOrder` instance along an injective function.

See note [reducible non-instances]. -/
/-
**Function.Injective.linearOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Injective.linearOrder [LinearOrder β] [LE α] [LT α] [Max α] [Min 
α] [Ord α] [DecidableEq α] [DecidableLE α] [DecidableLT α] (f : α -> β) (hf : Fu
nction.Injective f) (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y},
 f x < f y ↔ x < y) (min : forall x y, f (x ⊓ y) = f x ⊓ f y) (max : forall x y,
 f (x ⊔ y) = f x ⊔ f y) (compare : forall x y, compare (f x) (f y) = compare x y
) : LinearOrder α where toPartialOrder
参数：f : α -> β；hf : Function.Injective f；le : forall {x y}, f x <= f y ↔ x <= y；l
t : forall {x y}, f x < f y ↔ x < y；min : forall x y, f (x ⊓ y) = f x ⊓ f y；max 
: forall x y, f (x ⊔ y) = f x ⊔ f y；compare : forall x y, compare (f x) (f y) = 
compare x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a `LinearOrder` instance along an injective function.

See note [reducible non-instances].
-/
abbrev Function.Injective.linearOrder [LinearOrder β] [LE α] [LT α] [Max α] [Min α] [Ord α]
    [DecidableEq α] [DecidableLE α] [DecidableLT α] (f : α → β)
    (hf : Function.Injective f) (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (min : ∀ x y, f (x ⊓ y) = f x ⊓ f y) (max : ∀ x y, f (x ⊔ y) = f x ⊔ f y)
    (compare : ∀ x y, compare (f x) (f y) = compare x y) :
    LinearOrder α where
  toPartialOrder := hf.partialOrder _ le lt
  toDecidableLE := ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total _ _ := by simp only [← le, le_total]
  min_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← min_def, min]
  max_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← max_def, max]
  compare_eq_compareOfLessAndEq _ _ := by
    simp_rw [← compare, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, ← lt,
      hf.eq_iff]

/-!
### Lifts of order instances

Unlike the constructions above, these construct new data fields.
They should be avoided if the types already define any order or decidability instances.
-/

/-- Transfer a `Preorder` on `β` to a `Preorder` on `α` using a function `f : α → β`.

See also `Function.Injective.preorder` when only the proof fields need to be transferred.

See note [reducible non-instances]. -/
/-
**Preorder.lift** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Preorder.lift [Preorder β] (f : α -> β) : Preorder α
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `Preorder` on `β` to a `Preorder` on `α` using a function `f : α → β`
.

See also `Function.Injective.preorder` when only the proof fields need to be tra
nsferred.

See note [reducible non-instances].
-/
abbrev Preorder.lift [Preorder β] (f : α → β) : Preorder α :=
  letI _instLE : LE α := ⟨fun a b ↦ f a ≤ f b⟩
  letI _instLT : LT α := ⟨fun a b ↦ f a < f b⟩
  Function.Injective.preorder f .rfl .rfl

/-- Transfer a `PartialOrder` on `β` to a `PartialOrder` on `α` using an injective
function `f : α → β`.

See also `Function.Injective.partialOrder` when only the proof fields need to be transferred.

See note [reducible non-instances]. -/
/-
**PartialOrder.lift** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PartialOrder.lift [PartialOrder β] (f : α -> β) (inj : Injective f) : Part
ialOrder α
参数：f : α -> β；inj : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `PartialOrder` on `β` to a `PartialOrder` on `α` using an injective
function `f : α → β`.

See also `Function.Injective.partialOrder` when only the proof fields need to be
 transferred.

See note [reducible non-instances].
-/
abbrev PartialOrder.lift [PartialOrder β] (f : α → β) (inj : Injective f) : PartialOrder α :=
  letI _instLE : LE α := ⟨fun a b ↦ f a ≤ f b⟩
  letI _instLT : LT α := ⟨fun a b ↦ f a < f b⟩
  Function.Injective.partialOrder f inj .rfl .rfl
/-
**compare_of_injective_eq_compareOfLessAndEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compare_of_injective_eq_compareOfLessAndEq (a b : α) [LinearOrder β] [Deci
dableEq α] (f : α -> β) (inj : Injective f) [Decidable (LT.lt (self
参数：a b : α；f : α -> β；inj : Injective f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_2} [self : Line
arOrder α] (a b : α), compare a b = compareOfLessAndEq a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem compare_of_injective_eq_compareOfLessAndEq (a b : α) [LinearOrder β]
    [DecidableEq α] (f : α → β) (inj : Injective f)
    [Decidable (LT.lt (self := PartialOrder.lift f inj |>.toLT) a b)] :
    compare (f a) (f b) =
      @compareOfLessAndEq _ a b (PartialOrder.lift f inj |>.toLT) _ _ := by
  have h := LinearOrder.compare_eq_compareOfLessAndEq (f a) (f b)
  simp only [h, compareOfLessAndEq]
  split_ifs <;> try (first | rfl | contradiction)
  · have : ¬ f a = f b := by rename_i h; exact inj.ne h
    contradiction
  · grind

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Max α]` and `[Min α]` as arguments, then uses
them for `max` and `min` fields. See `LinearOrder.lift'` for a version that autogenerates `min` and
`max` fields, and `LinearOrder.liftWithOrd` for one that does not auto-generate `compare`
fields.

See also `Function.Injective.linearOrder` when only the proof fields need to be transferred.

See note [reducible non-instances]. -/
@[to_dual self (reorder := 4 5, hsup hinf)]
/-
**LinearOrder.lift** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearOrder.lift [LinearOrder β] [Max α] [Min α] (f : α -> β) (inj : Injec
tive f) (hsup : forall x y, f (x ⊔ y) = max (f x) (f y)) (hinf : forall x y, f (
x ⊓ y) = min (f x) (f y)) : LinearOrder α
参数：f : α -> β；inj : Injective f；hsup : forall x y, f (x ⊔ y) = max (f x) (f y)；h
inf : forall x y, f (x ⊓ y) = min (f x) (f y)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b

--- 原说明 ---
Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Max α]` and `[Min α]` as arguments, t
hen uses
them for `max` and `min` fields. See `LinearOrder.lift'` for a version that auto
generates `min` and
`max` fields, and `LinearOrder.liftWithOrd` for one that does not auto-generate 
`compare`
fields.

See also `Function.Injective.linearOrder` when only the proof fields need to be 
transferred.

See note [reducible non-instances].
-/
abbrev LinearOrder.lift [LinearOrder β] [Max α] [Min α] (f : α → β) (inj : Injective f)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrder α :=
  letI _instLE : LE α := ⟨fun a b ↦ f a ≤ f b⟩
  letI _instLT : LT α := ⟨fun a b ↦ f a < f b⟩
  letI _instOrdα : Ord α := ⟨fun a b ↦ compare (f a) (f b)⟩
  letI _decidableLE := fun x y ↦ (inferInstance : Decidable (f x ≤ f y))
  letI _decidableLT := fun x y ↦ (inferInstance : Decidable (f x < f y))
  letI _decidableEq := fun x y ↦ decidable_of_iff (f x = f y) inj.eq_iff
  inj.linearOrder _ .rfl .rfl hinf hsup (fun _ _ => rfl)

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version autogenerates `min` and `max` fields. See `LinearOrder.lift`
for a version that takes `[Max α]` and `[Min α]`, then uses them as `max` and `min`. See
`LinearOrder.liftWithOrd'` for a version which does not auto-generate `compare` fields.
See note [reducible non-instances]. -/
/-
**LinearOrder.lift'** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearOrder.lift' [LinearOrder β] (f : α -> β) (inj : Injective f) : Linea
rOrder α
参数：f : α -> β；inj : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version autogenerates `min` and `max` fields. See `Li
nearOrder.lift`
for a version that takes `[Max α]` and `[Min α]`, then uses them as `max` and `m
in`. See
`LinearOrder.liftWithOrd'` for a version which does not auto-generate `compare` 
fields.
See note [reducible non-instances].
-/
abbrev LinearOrder.lift' [LinearOrder β] (f : α → β) (inj : Injective f) : LinearOrder α :=
  @LinearOrder.lift α β _ ⟨fun x y ↦ if f x ≤ f y then y else x⟩
    ⟨fun x y ↦ if f x ≤ f y then x else y⟩ f inj
    (fun _ _ ↦ (apply_ite f _ _ _).trans (max_def _ _).symm) fun _ _ ↦
    (apply_ite f _ _ _).trans (min_def _ _).symm

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Max α]` and `[Min α]` as arguments, then uses
them for `max` and `min` fields. It also takes `[Ord α]` as an argument and uses them for `compare`
fields. See `LinearOrder.lift` for a version that autogenerates `compare` fields, and
`LinearOrder.liftWithOrd'` for one that auto-generates `min` and `max` fields.
fields. See note [reducible non-instances]. -/
@[to_dual self (reorder := 4 5, hsup hinf)]
/-
**LinearOrder.liftWithOrd** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearOrder.liftWithOrd [LinearOrder β] [Max α] [Min α] [Ord α] (f : α -> 
β) (inj : Injective f) (hsup : forall x y, f (x ⊔ y) = max (f x) (f y)) (hinf : 
forall x y, f (x ⊓ y) = min (f x) (f y)) (compare_f : forall a b : α, compare a 
b = compare (f a) (f b)) : LinearOrder α
参数：f : α -> β；inj : Injective f；hsup : forall x y, f (x ⊔ y) = max (f x) (f y)；h
inf : forall x y, f (x ⊓ y) = min (f x) (f y)；compare_f : forall a b : α, compar
e a b = compare (f a) (f b)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b

--- 原说明 ---
Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Max α]` and `[Min α]` as arguments, t
hen uses
them for `max` and `min` fields. It also takes `[Ord α]` as an argument and uses
 them for `compare`
fields. See `LinearOrder.lift` for a version that autogenerates `compare` fields
, and
`LinearOrder.liftWithOrd'` for one that auto-generates `min` and `max` fields.
fields. See note [reducible non-instances].
-/
abbrev LinearOrder.liftWithOrd [LinearOrder β] [Max α] [Min α] [Ord α] (f : α → β)
    (inj : Injective f) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y))
    (compare_f : ∀ a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  letI _instLE : LE α := ⟨fun a b ↦ f a ≤ f b⟩
  letI _instLE : LT α := ⟨fun a b ↦ f a < f b⟩
  letI _decidableLE := fun x y ↦ (inferInstance : Decidable (f x ≤ f y))
  letI _decidableLT := fun x y ↦ (inferInstance : Decidable (f x < f y))
  letI _decidableEq := fun x y ↦ decidable_of_iff (f x = f y) inj.eq_iff
  inj.linearOrder _ .rfl .rfl hinf hsup (fun _ _ => (compare_f _ _).symm)

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version auto-generates `min` and `max` fields. It also takes `[Ord α]`
as an argument and uses them for `compare` fields. See `LinearOrder.lift` for a version that
autogenerates `compare` fields, and `LinearOrder.liftWithOrd` for one that doesn't auto-generate
`min` and `max` fields. fields. See note [reducible non-instances]. -/
/-
**LinearOrder.liftWithOrd'** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearOrder.liftWithOrd' [LinearOrder β] [Ord α] (f : α -> β) (inj : Injec
tive f) (compare_f : forall a b : α, compare a b = compare (f a) (f b)) : Linear
Order α
参数：f : α -> β；inj : Injective f；compare_f : forall a b : α, compare a b = compar
e (f a) (f b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version auto-generates `min` and `max` fields. It als
o takes `[Ord α]`
as an argument and uses them for `compare` fields. See `LinearOrder.lift` for a 
version that
autogenerates `compare` fields, and `LinearOrder.liftWithOrd` for one that doesn
't auto-generate
`min` and `max` fields. fields. See note [reducible non-instances].
-/
abbrev LinearOrder.liftWithOrd' [LinearOrder β] [Ord α] (f : α → β)
    (inj : Injective f)
    (compare_f : ∀ a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  @LinearOrder.liftWithOrd α β _ ⟨fun x y ↦ if f x ≤ f y then y else x⟩
    ⟨fun x y ↦ if f x ≤ f y then x else y⟩ _ f inj
    (fun _ _ ↦ (apply_ite f _ _ _).trans (max_def _ _).symm)
    (fun _ _ ↦ (apply_ite f _ _ _).trans (min_def _ _).symm)
    compare_f

/-! ### Subtype of an order -/


namespace Subtype

@[simp, gcongr, to_dual self]
/-
**Subtype.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：mk_le_mk [LE α] {p : α -> Prop} {x y : α} {hx : p x} {hy : p y} : (⟨x, hx⟩
 : Subtype p) <= ⟨y, hy⟩ ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk [LE α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl

@[simp, gcongr, to_dual self]
/-
**Subtype.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {hy : p y} : (⟨x, hx⟩
 : Subtype p) < ⟨y, hy⟩ ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_lt_mk [LT α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]
/-
**Subtype.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} : (x : α) <= y ↔ x <= 
y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe [LE α] {p : α → Prop} {x y : Subtype p} : (x : α) ≤ y ↔ x ≤ y :=
  Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]
/-
**Subtype.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} : (x : α) < y ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_lt_coe [LT α] {p : α → Prop} {x y : Subtype p} : (x : α) < y ↔ x < y :=
  Iff.rfl
/-
**Subtype.preorder** 是 Mathlib 中的一个实例，位于命名空间 `Subtype`。
形式化陈述：preorder [Preorder α] (p : α -> Prop) : Preorder (Subtype p)
参数：p : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preorder [Preorder α] (p : α → Prop) : Preorder (Subtype p) :=
  fast_instance% Preorder.lift (fun (a : Subtype p) ↦ (a : α))
/-
**Subtype.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `IsLprojection`。
形式化陈述：Subtype.partialOrder [FaithfulSMul M X] : PartialOrder { P : M // IsLproje
ction X P } where le P Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder [PartialOrder α] (p : α → Prop) : PartialOrder (Subtype p) :=
  fast_instance% PartialOrder.lift (fun (a : Subtype p) ↦ (a : α)) Subtype.coe_injective
/-
**Subtype.decidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Subtype`。
形式化陈述：decidableLE [Preorder α] [h : DecidableLE α] {p : α -> Prop} : DecidableLE
 (Subtype p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLE [Preorder α] [h : DecidableLE α] {p : α → Prop} :
    DecidableLE (Subtype p) := fun a b ↦ h a b
/-
**Subtype.decidableLT** 是 Mathlib 中的一个实例，位于命名空间 `Subtype`。
形式化陈述：decidableLT [Preorder α] [h : DecidableLT α] {p : α -> Prop} : DecidableLT
 (Subtype p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLT [Preorder α] [h : DecidableLT α] {p : α → Prop} :
    DecidableLT (Subtype p) := fun a b ↦ h a b

/-- A subtype of a linear order is a linear order. We explicitly give the proofs of decidable
equality and decidable order in order to ensure the decidability instances are all definitionally
equal. -/
/-
**Subtype.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Subtype`。
形式化陈述：instLinearOrder [LinearOrder α] (p : α -> Prop) : LinearOrder (Subtype p)
参数：p : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype of a linear order is a linear order. We explicitly give the proofs of 
decidable
equality and decidable order in order to ensure the decidability instances are a
ll definitionally
equal.
-/
instance instLinearOrder [LinearOrder α] (p : α → Prop) : LinearOrder (Subtype p) :=
  fast_instance% @LinearOrder.lift (Subtype p) _ _ ⟨fun x y ↦ ⟨max x y, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y ↦ ⟨min x y, min_rec' _ x.2 y.2⟩⟩ (fun (a : Subtype p) ↦ (a : α))
    Subtype.coe_injective (fun _ _ ↦ rfl) fun _ _ ↦
    rfl

end Subtype

/-!
### Pointwise order on `α × β`

The lexicographic order is defined in `Data.Prod.Lex`, and the instances are available via the
type synonym `α ×ₗ β = α × β`.
-/


namespace Prod
section LE
variable [LE α] [LE β] {x y : α × β} {a a₁ a₂ : α} {b b₁ b₂ : β}

/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (α × β) where le p q := p.1 ≤ q.1 ∧ p.2 ≤ q.2

@[to_dual self]
/-
**Prod.instDecidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instDecidableLE [Decidable (x.1 <= y.1)] [Decidable (x.2 <= y.2)] : Decida
ble (x <= y)
参数：x.1 <= y.1；x.2 <= y.2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableLE [Decidable (x.1 ≤ y.1)] [Decidable (x.2 ≤ y.2)] : Decidable (x ≤ y) :=
  inferInstanceAs <| Decidable (x.1 ≤ y.1 ∧ x.2 ≤ y.2)
/-
**Prod.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] {x y : α × β
}, x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_dual self] lemma le_def : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 := .rfl
/-
**Prod.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] {a₁ a₂ : α} 
{b₁ b₂ : β},   (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂
参数：a₁, b₁；a₂, b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, to_dual self] lemma mk_le_mk : (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂ := .rfl

@[gcongr, to_dual self]
/-
**Prod.GCongr.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod.GCongr`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] {a₁ a₂ : α} 
{b₁ b₂ : β},   a₁ ≤ a₂ → b₁ ≤ b₂ → (a₁, b₁) ≤ (a₂, b₂)
参数：a₁, b₁；a₂, b₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma GCongr.mk_le_mk (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : (a₁, b₁) ≤ (a₂, b₂) := ⟨ha, hb⟩
/-
**Prod.swap_le_swap** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] {x y : α × β
}, x.swap ≤ y.swap ↔ x ≤ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
@[simp, to_dual self] lemma swap_le_swap : x.swap ≤ y.swap ↔ x ≤ y := and_comm

@[to_dual (attr := simp) mk_le_swap]
/-
**Prod.swap_le_mk** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：swap_le_mk : x.swap <= (b, a) ↔ x <= (a, b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
lemma swap_le_mk : x.swap ≤ (b, a) ↔ x ≤ (a, b) := and_comm

end LE

section Preorder

variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (α × β) where
  __ := (inferInstance : LE (α × β))
  le_refl := fun ⟨a, b⟩ ↦ ⟨le_refl a, le_refl b⟩
  le_trans := fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ ↦ ⟨le_trans hac hce, le_trans hbd hdf⟩

@[simp, to_dual self]
/-
**Prod.swap_lt_swap** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_lt_swap : x.swap < y.swap ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Prod.swap_le_swap`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1
 : LE β] {x y : α × β}, x.swap ≤ y.swap ↔ x ≤ y
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
theorem swap_lt_swap : x.swap < y.swap ↔ x < y :=
  and_congr swap_le_swap (not_congr swap_le_swap)

@[to_dual (attr := simp) mk_lt_swap]
/-
**Prod.swap_lt_mk** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：swap_lt_mk : x.swap < (b, a) ↔ x < (a, b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.swap_lt_swap`：swap_lt_swap : x.swap < y.swap ↔ x < y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α × β), x.swap.swap
 = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma swap_lt_mk : x.swap < (b, a) ↔ x < (a, b) := by rw [← swap_lt_swap]; simp

@[gcongr, to_dual self]
/-
**Prod.mk_le_mk_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_le_mk_iff_left : (a₁, b) <= (a₂, b) ↔ a₁ <= a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mk_le_mk_iff_left : (a₁, b) ≤ (a₂, b) ↔ a₁ ≤ a₂ :=
  and_iff_left le_rfl

@[gcongr, to_dual self]
/-
**Prod.mk_le_mk_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_le_mk_iff_right : (a, b₁) <= (a, b₂) ↔ b₁ <= b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mk_le_mk_iff_right : (a, b₁) ≤ (a, b₂) ↔ b₁ ≤ b₂ :=
  and_iff_right le_rfl

@[gcongr, to_dual self]
/-
**Prod.mk_lt_mk_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `Prod.mk_le_mk_iff_left`：mk_le_mk_iff_left : (a₁, b) <= (a₂, b) ↔ a₁ <= a
₂
-/
theorem mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

@[gcongr, to_dual self]
/-
**Prod.mk_lt_mk_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `Prod.mk_le_mk_iff_right`：mk_le_mk_iff_right : (a, b₁) <= (a, b₂) ↔ b₁ <=
 b₂
-/
theorem mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

@[to_dual self]
/-
**Prod.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 < y.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 ≤ y.2 ∨ x.1 ≤ y.1 ∧ x.2 < y.2 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases h₁ : y.1 ≤ x.1
    · exact Or.inr ⟨h.1.1, LE.le.lt_of_not_ge h.1.2 fun h₂ ↦ h.2 ⟨h₁, h₂⟩⟩
    · exact Or.inl ⟨LE.le.lt_of_not_ge h.1.1 h₁, h.1.2⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁.le, h₂⟩, fun h ↦ h₁.not_ge h.1⟩
    · exact ⟨⟨h₁, h₂.le⟩, fun h ↦ h₂.not_ge h.2⟩

@[simp, to_dual self]
/-
**Prod.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ <= b₂ ∨ a₁ <= a₂ ∧ b₁ < b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.lt_iff`：lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 
< y.2
-/
theorem mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₁ < b₂ :=
  lt_iff

@[to_dual self]
/-
**Prod.lt_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
{x y : α × β}, x.1 < y.1 → x.2 ≤ y.2 → x < y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
protected lemma lt_of_lt_of_le (h₁ : x.1 < y.1) (h₂ : x.2 ≤ y.2) : x < y := by simp [lt_iff, *]

@[to_dual self]
/-
**Prod.lt_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
{x y : α × β}, x.1 ≤ y.1 → x.2 < y.2 → x < y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
protected lemma lt_of_le_of_lt (h₁ : x.1 ≤ y.1) (h₂ : x.2 < y.2) : x < y := by simp [lt_iff, *]

@[to_dual self]
/-
**Prod.mk_lt_mk_of_lt_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：mk_lt_mk_of_lt_of_le (h₁ : a₁ < a₂) (h₂ : b₁ <= b₂) : (a₁, b₁) < (a₂, b₂)
参数：h₁ : a₁ < a₂；h₂ : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma mk_lt_mk_of_lt_of_le (h₁ : a₁ < a₂) (h₂ : b₁ ≤ b₂) : (a₁, b₁) < (a₂, b₂) := by
  simp [lt_iff, *]

@[to_dual self]
/-
**Prod.mk_lt_mk_of_le_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：mk_lt_mk_of_le_of_lt (h₁ : a₁ <= a₂) (h₂ : b₁ < b₂) : (a₁, b₁) < (a₂, b₂)
参数：h₁ : a₁ <= a₂；h₂ : b₁ < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma mk_lt_mk_of_le_of_lt (h₁ : a₁ ≤ a₂) (h₂ : b₁ < b₂) : (a₁, b₁) < (a₂, b₂) := by
  simp [lt_iff, *]

end Preorder

/-- The pointwise partial order on a product.
(The lexicographic ordering is defined in `Order.Lexicographic`, and the instances are
available via the type synonym `α ×ₗ β = α × β`.) -/
/-
**Prod.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instPartialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] : Partial
Order (α × β) where __
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pointwise partial order on a product.
(The lexicographic ordering is defined in `Order.Lexicographic`, and the instanc
es are
available via the type synonym `α ×ₗ β = α × β`.)
-/
instance instPartialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] :
    PartialOrder (α × β) where
  __ := (inferInstance : Preorder (α × β))
  le_antisymm := fun _ _ ⟨hac, hbd⟩ ⟨hca, hdb⟩ ↦ Prod.ext (hac.antisymm hca) (hbd.antisymm hdb)

end Prod

/-! ### Additional order classes -/

/-- An order is dense if there is an element between any pair of distinct comparable elements. -/
/-
**DenselyOrdered** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_5) → [LT α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order is dense if there is an element between any pair of distinct comparable
 elements.
-/
class DenselyOrdered (α : Type*) [LT α] : Prop where
  /-- An order is dense if there is an element between any pair of distinct elements. -/
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

@[to_dual existing dense]
/-
**DenselyOrdered.dense'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenselyOrdered.dense' [LT α] [DenselyOrdered α] : forall a₁ a₂ : α, a₁ < a
₂ -> exists a, a < a₂ ∧ a₁ < a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DenselyOrdered.dense`：∀ {α : Type u_5} {inst : LT α} [self : DenselyOrde
red α] (a₁ a₂ : α), a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂
-/
theorem DenselyOrdered.dense' [LT α] [DenselyOrdered α] :
    ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a < a₂ ∧ a₁ < a := by
  simp_rw [and_comm]; exact dense

@[to_dual exists_between']
/-
**exists_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a₁ < a₂ -> exists a
, a₁ < a ∧ a < a₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenselyOrdered.dense`：∀ {α : Type u_5} {inst : LT α} [self : DenselyOrde
red α] (a₁ a₂ : α), a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂
-/
theorem exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
  DenselyOrdered.dense _ _


/-- Any ordered subsingleton is densely ordered. Not an instance to avoid a heavy subsingleton
typeclass search. -/
/-
**Subsingleton.instDenselyOrdered** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subsingleton.instDenselyOrdered {X : Type*} [Subsingleton X] [LT X] : Dens
elyOrdered X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
Any ordered subsingleton is densely ordered. Not an instance to avoid a heavy su
bsingleton
typeclass search.
-/
lemma Subsingleton.instDenselyOrdered {X : Type*} [Subsingleton X] [LT X] :
    DenselyOrdered X :=
  ⟨fun _ _ h ↦ ⟨_, h.trans_eq (Subsingleton.elim _ _), h⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] : DenselyOrdered (α × β) :=
  ⟨fun a b ↦ by
    simp_rw [Prod.lt_iff]
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · obtain ⟨c, ha, hb⟩ := exists_between h₁
      exact ⟨(c, _), Or.inl ⟨ha, h₂⟩, Or.inl ⟨hb, le_rfl⟩⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h₂
      exact ⟨(_, c), Or.inr ⟨h₁, ha⟩, Or.inr ⟨le_rfl, hb⟩⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Preorder (π i)] [∀ i, DenselyOrdered (π i)] :
    DenselyOrdered (∀ i, π i) :=
  ⟨fun a b ↦ by
    classical
      simp_rw [Pi.lt_def]
      rintro ⟨hab, i, hi⟩
      obtain ⟨c, ha, hb⟩ := exists_between hi
      exact
        ⟨Function.update a i c,
          ⟨le_update_iff.2 ⟨ha.le, fun _ _ ↦ le_rfl⟩, i, by rwa [update_self]⟩,
          update_le_iff.2 ⟨hb.le, fun _ _ ↦ hab _⟩, i, by rwa [update_self]⟩⟩

section LinearOrder
variable [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}

@[to_dual le_of_forall_lt_imp_le_of_dense]
/-
**le_of_forall_gt_imp_ge_of_dense** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_gt_imp_ge_of_dense (h : forall a, a₂ < a -> a₁ <= a) : a₁ <= 
a₂
参数：h : forall a, a₂ < a -> a₁ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem le_of_forall_gt_imp_ge_of_dense (h : ∀ a, a₂ < a → a₁ ≤ a) : a₁ ≤ a₂ :=
  le_of_not_gt fun ha ↦
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irrefl a <| lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

@[to_dual forall_lt_imp_le_iff_le_of_dense]
/-
**forall_gt_imp_ge_iff_le_of_dense** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：forall_gt_imp_ge_iff_le_of_dense : (forall a, a₂ < a -> a₁ <= a) ↔ a₁ <= a
₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma forall_gt_imp_ge_iff_le_of_dense : (∀ a, a₂ < a → a₁ ≤ a) ↔ a₁ ≤ a₂ :=
  ⟨le_of_forall_gt_imp_ge_of_dense, fun ha _a ha₂ ↦ ha.trans ha₂.le⟩

-- TODO: these two lemma names are the wrong way around
@[to_dual eq_of_le_of_forall_gt_imp_ge_of_dense]
/-
**eq_of_le_of_forall_lt_imp_le_of_dense** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_of_le_of_forall_lt_imp_le_of_dense (h₁ : a₂ <= a₁) (h₂ : forall a, a₂ <
 a -> a₁ <= a) : a₁ = a₂
参数：h₁ : a₂ <= a₁；h₂ : forall a, a₂ < a -> a₁ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
-/
lemma eq_of_le_of_forall_lt_imp_le_of_dense (h₁ : a₂ ≤ a₁) (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
  le_antisymm (le_of_forall_gt_imp_ge_of_dense h₂) h₁

end LinearOrder

@[to_dual dense_or_discrete']
/-
**dense_or_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_or_discrete [LinearOrder α] (a₁ a₂ : α) : (exists a, a₁ < a ∧ a < a₂
) ∨ (forall a, a₁ < a -> a₂ <= a) ∧ forall a < a₂, a <= a₁
参数：a₁ a₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
-/
theorem dense_or_discrete [LinearOrder α] (a₁ a₂ : α) :
    (∃ a, a₁ < a ∧ a < a₂) ∨ (∀ a, a₁ < a → a₂ ≤ a) ∧ ∀ a < a₂, a ≤ a₁ :=
  or_iff_not_imp_left.2 fun h ↦
    ⟨fun a ha₁ ↦ le_of_not_gt fun ha₂ ↦ h ⟨a, ha₁, ha₂⟩,
     fun a ha₂ ↦ le_of_not_gt fun ha₁ ↦ h ⟨a, ha₁, ha₂⟩⟩

/-- If a linear order has no elements `x < y < z`, then it has at most two elements. -/
@[to_dual self (reorder := h (x z, 4 5))]
/-
**eq_or_eq_or_eq_of_forall_not_lt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_or_eq_or_eq_of_forall_not_lt_lt [LinearOrder α] (h : forall ⦃x y z : α⦄
, x < y -> y < z -> False) (x y z : α) : x = y ∨ y = z ∨ x = z
参数：h : forall ⦃x y z : α⦄, x < y -> y < z -> False；x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a linear order has no elements `x < y < z`, then it has at most two elements.
-/
lemma eq_or_eq_or_eq_of_forall_not_lt_lt [LinearOrder α]
    (h : ∀ ⦃x y z : α⦄, x < y → y < z → False) (x y z : α) : x = y ∨ y = z ∨ x = z := by
  by_contra hne
  simp only [not_or, ← Ne.eq_def] at hne
  rcases hne.1.lt_or_gt with h₁ | h₁ <;>
  rcases hne.2.1.lt_or_gt with h₂ | h₂ <;>
  rcases hne.2.2.lt_or_gt with h₃ | h₃
  exacts [h h₁ h₂, h h₂ h₃, h h₃ h₂, h h₃ h₁, h h₁ h₃, h h₂ h₃, h h₁ h₃, h h₂ h₁]

/-- Construct the trivial linear order on any type with at most one element. -/
/-
**LinearOrder.ofSubsingleton** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearOrder.ofSubsingleton {α : Type*} [Subsingleton α] : LinearOrder α wh
ere le _ _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
Construct the trivial linear order on any type with at most one element.
-/
abbrev LinearOrder.ofSubsingleton {α : Type*} [Subsingleton α] : LinearOrder α where
  le _ _ := True
  lt _ _ := False
  le_refl _ := trivial
  le_trans x y z _ _ := trivial
  le_antisymm x y _ _ := Subsingleton.elim x y
  le_total _ _ := .inl trivial
  lt_iff_le_not_ge _ _ := by simp
  toDecidableLE _ _ := instDecidableTrue
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder Empty := .ofSubsingleton
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder PEmpty := .ofSubsingleton

namespace PUnit

variable (a b : PUnit)

/-
**PUnit.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：instLinearOrder : LinearOrder PUnit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
instance instLinearOrder : LinearOrder PUnit := .ofSubsingleton

@[to_dual]
/-
**PUnit.max_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：max_eq : max a b = unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem max_eq : max a b = unit :=
  rfl

@[to_dual self]
/-
**PUnit.le** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：∀ (a b : PUnit.{u_5 + 1}), a ≤ b
参数：a b : PUnit.{u_5 + 1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
protected theorem le : a ≤ b :=
  trivial

@[to_dual self]
/-
**PUnit.not_lt** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：not_lt : ¬a < b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_false`：¬False
-/
theorem not_lt : ¬a < b :=
  not_false
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DenselyOrdered PUnit :=
  ⟨fun _ _ ↦ False.elim⟩

end PUnit

section «Prop»

/-
**subrelation_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subrelation_iff_le {r s : α -> α -> Prop} : Subrelation r s ↔ r <= s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subrelation_iff_le {r s : α → α → Prop} : Subrelation r s ↔ r ≤ s :=
  Iff.rfl
/-
**Prop.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.partialOrder : PartialOrder Prop where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prop.partialOrder : PartialOrder Prop where
  __ := Prop.le
  le_refl _ := id
  le_trans _ _ _ f g := g ∘ f
  le_antisymm _ _ Hab Hba := propext ⟨Hab, Hba⟩

end «Prop»

