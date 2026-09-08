/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Minchao Wu
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lex
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.FastInstance

/-!
# Lexicographic order

This file defines the lexicographic relation for pairs of orders, partial orders and linear orders.

## Main declarations

* `Prod.Lex.<pre/partial/linear>Order`: Instances lifting the orders on `α` and `β` to `α ×ₗ β`.

## Notation

* `α ×ₗ β`: `α × β` equipped with the lexicographic order

## See also

Related files are:
* `Data.Finset.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i`.

# TODO

Some lemmas could be automatically generated with `to_dual`.
See [https://github.com/leanprover-community/mathlib4/pull/37939#discussion_r3367855484]

-/

@[expose] public section


variable {α β : Type*}

namespace Prod.Lex

@[inherit_doc] notation:35 α " ×ₗ " β:34 => Lex (Prod α β)

/-- Dictionary / lexicographic ordering on pairs. -/
/-
**Prod.Lex.instLE** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：instLE (α β : Type*) [LT α] [LE β] : LE (α ×ₗ β) where le
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dictionary / lexicographic ordering on pairs.
-/
instance instLE (α β : Type*) [LT α] [LE β] : LE (α ×ₗ β) where le := Prod.Lex (· < ·) (· ≤ ·)
/-
**Prod.Lex.instLT** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：instLT (α β : Type*) [LT α] [LT β] : LT (α ×ₗ β) where lt
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLT (α β : Type*) [LT α] [LT β] : LT (α ×ₗ β) where lt := Prod.Lex (· < ·) (· < ·)
/-
**Prod.Lex.toLex_le_toLex** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：toLex_le_toLex [LT α] [LE β] {x y : α × β} : toLex x <= toLex y ↔ x.1 < y.
1 ∨ x.1 = y.1 ∧ x.2 <= y.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.lex_def`：∀ {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β 
→ Prop} {p q : α × β},   Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2
-/
theorem toLex_le_toLex [LT α] [LE β] {x y : α × β} :
    toLex x ≤ toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 ≤ y.2 :=
  Prod.lex_def

@[to_dual existing toLex_le_toLex]
/-
**Prod.Lex.toLex_ge_toLex** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：toLex_ge_toLex [LT α] [LE β] {x y : α × β} : toLex y <= toLex x ↔ y.1 < x.
1 ∨ x.1 = y.1 ∧ y.2 <= x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Prod.Lex.toLex_le_toLex`：toLex_le_toLex [LT α] [LE β] {x y : α × β} : to
Lex x <= toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 <= y.2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toLex_ge_toLex [LT α] [LE β] {x y : α × β} :
    toLex y ≤ toLex x ↔ y.1 < x.1 ∨ x.1 = y.1 ∧ y.2 ≤ x.2 := by
  rw [eq_comm, toLex_le_toLex]
/-
**Prod.Lex.toLex_lt_toLex** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：toLex_lt_toLex [LT α] [LT β] {x y : α × β} : toLex x < toLex y ↔ x.1 < y.1
 ∨ x.1 = y.1 ∧ x.2 < y.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.lex_def`：∀ {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β 
→ Prop} {p q : α × β},   Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2
-/
theorem toLex_lt_toLex [LT α] [LT β] {x y : α × β} :
    toLex x < toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2 :=
  Prod.lex_def

@[to_dual existing toLex_lt_toLex]
/-
**Prod.Lex.toLex_gt_toLex** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：toLex_gt_toLex [LT α] [LT β] {x y : α × β} : toLex y < toLex x ↔ y.1 < x.1
 ∨ x.1 = y.1 ∧ y.2 < x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Prod.Lex.toLex_lt_toLex`：toLex_lt_toLex [LT α] [LT β] {x y : α × β} : to
Lex x < toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toLex_gt_toLex [LT α] [LT β] {x y : α × β} :
    toLex y < toLex x ↔ y.1 < x.1 ∨ x.1 = y.1 ∧ y.2 < x.2 := by
  rw [eq_comm, toLex_lt_toLex]

@[to_dual none]
/-
**Prod.Lex.le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Prod.Lex`。
形式化陈述：le_iff [LT α] [LE β] {x y : α ×ₗ β} : x <= y ↔ (ofLex x).1 < (ofLex y).1 ∨
 (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 <= (ofLex y).2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.Lex.toLex_le_toLex`：toLex_le_toLex [LT α] [LE β] {x y : α × β} : to
Lex x <= toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 <= y.2
-/
lemma le_iff [LT α] [LE β] {x y : α ×ₗ β} :
    x ≤ y ↔ (ofLex x).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 ≤ (ofLex y).2 :=
  toLex_le_toLex

@[to_dual none]
/-
**Prod.Lex.lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Prod.Lex`。
形式化陈述：lt_iff [LT α] [LT β] {x y : α ×ₗ β} : x < y ↔ (ofLex x).1 < (ofLex y).1 ∨ 
(ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.Lex.toLex_lt_toLex`：toLex_lt_toLex [LT α] [LT β] {x y : α × β} : to
Lex x < toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2
-/
lemma lt_iff [LT α] [LT β] {x y : α ×ₗ β} :
    x < y ↔ (ofLex x).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2 :=
  toLex_lt_toLex
/-
**Prod.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedLT (α ×ₗ β) :=
  instIsWellFounded
/-
**Prod.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedRelation (α ×ₗ β) :=
  ⟨(· < ·), wellFounded_lt⟩

/-- Dictionary / lexicographic preorder for pairs. -/
/-
**Prod.Lex.instPreorder** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：instPreorder (α β : Type*) [Preorder α] [Preorder β] : Preorder (α ×ₗ β) w
here le_refl
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dictionary / lexicographic preorder for pairs.
-/
instance instPreorder (α β : Type*) [Preorder α] [Preorder β] : Preorder (α ×ₗ β) where
  le_refl := refl_of <| Prod.Lex _ _
  le_trans _ _ _ := trans_of <| Prod.Lex _ _
  lt_iff_le_not_ge x₁ x₂ := by grind [le_iff, lt_iff, lt_iff_le_not_ge]

/-- See also `monotone_fst_ofLex` for a version stated in terms of `Monotone`. -/
/-
**Prod.Lex.monotone_fst** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：monotone_fst [Preorder α] [LE β] (t c : α ×ₗ β) (h : t <= c) : (ofLex t).1
 <= (ofLex c).1
参数：t c : α ×ₗ β；h : t <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.Lex.toLex_le_toLex`：toLex_le_toLex [LT α] [LE β] {x y : α × β} : to
Lex x <= toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 <= y.2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
See also `monotone_fst_ofLex` for a version stated in terms of `Monotone`.
-/
theorem monotone_fst [Preorder α] [LE β] (t c : α ×ₗ β) (h : t ≤ c) :
    (ofLex t).1 ≤ (ofLex c).1 := by
  cases toLex_le_toLex.mp h with
  | inl h' => exact h'.le
  | inr h' => exact h'.1.le

section Preorder

variable [Preorder α] [Preorder β]

/-
**Prod.Lex.monotone_fst_ofLex** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：monotone_fst_ofLex : Monotone fun x : α ×ₗ β => (ofLex x).1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.Lex.monotone_fst`：monotone_fst [Preorder α] [LE β] (t c : α ×ₗ β) (
h : t <= c) : (ofLex t).1 <= (ofLex c).1
-/
theorem monotone_fst_ofLex : Monotone fun x : α ×ₗ β ↦ (ofLex x).1 := monotone_fst

@[to_dual self]
/-
**Prod.Lex._root_.WCovBy.fst_ofLex** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.WCovBy.fst_ofLex {a b : α ×ₗ β} (h : a ⩿ b) : (ofLex a).1 ⩿ (ofLex b).1 :=
  ⟨monotone_fst _ _ h.1, fun c hac hcb ↦ h.2 (c := toLex (c, a.2)) (.left _ _ hac) (.left _ _ hcb)⟩

@[to_dual none]
/-
**Prod.Lex.toLex_covBy_toLex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：toLex_covBy_toLex_iff {a₁ a₂ : α} {b₁ b₂ : β} : toLex (a₁, b₁) ⋖ toLex (a₂
, b₂) ↔ a₁ = a₂ ∧ b₁ ⋖ b₂ ∨ a₁ ⋖ a₂ ∧ IsMax b₁ ∧ IsMin b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem toLex_covBy_toLex_iff {a₁ a₂ : α} {b₁ b₂ : β} :
    toLex (a₁, b₁) ⋖ toLex (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ ⋖ b₂ ∨ a₁ ⋖ a₂ ∧ IsMax b₁ ∧ IsMin b₂ := by
  simp only [CovBy, toLex_lt_toLex, toLex.surjective.forall, Prod.forall, isMax_iff_forall_not_lt,
    isMin_iff_forall_not_lt]
  grind

@[to_dual none]
/-
**Prod.Lex.covBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：covBy_iff {a b : α ×ₗ β} : a ⋖ b ↔ (ofLex a).1 = (ofLex b).1 ∧ (ofLex a).2
 ⋖ (ofLex b).2 ∨ (ofLex a).1 ⋖ (ofLex b).1 ∧ IsMax (ofLex a).2 ∧ IsMin (ofLex b)
.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.Lex.toLex_covBy_toLex_iff`：toLex_covBy_toLex_iff {a₁ a₂ : α} {b₁ b₂
 : β} : toLex (a₁, b₁) ⋖ toLex (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ ⋖ b₂ ∨ a₁ ⋖ a₂ ∧ IsMax b₁
 ∧ IsMin b₂
-/
theorem covBy_iff {a b : α ×ₗ β} :
    a ⋖ b ↔ (ofLex a).1 = (ofLex b).1 ∧ (ofLex a).2 ⋖ (ofLex b).2 ∨
      (ofLex a).1 ⋖ (ofLex b).1 ∧ IsMax (ofLex a).2 ∧ IsMin (ofLex b).2 :=
  toLex_covBy_toLex_iff

end Preorder

section PartialOrderPreorder

variable [PartialOrder α] [Preorder β] {x y : α × β}

/-- Variant of `Prod.Lex.toLex_le_toLex` for partial orders. -/
@[to_dual none]
/-
**Prod.Lex.toLex_le_toLex'** 是 Mathlib 中的一个引理，位于命名空间 `Prod.Lex`。
形式化陈述：toLex_le_toLex' : toLex x <= toLex y ↔ x.1 <= y.1 ∧ (x.1 = y.1 -> x.2 <= y
.2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p

--- 原说明 ---
Variant of `Prod.Lex.toLex_le_toLex` for partial orders.
-/
lemma toLex_le_toLex' : toLex x ≤ toLex y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 ≤ y.2) := by
  simp only [toLex_le_toLex, lt_iff_le_not_ge, le_antisymm_iff]
  tauto

/-- Variant of `Prod.Lex.toLex_lt_toLex` for partial orders. -/
@[to_dual none]
/-
**Prod.Lex.toLex_lt_toLex'** 是 Mathlib 中的一个引理，位于命名空间 `Prod.Lex`。
形式化陈述：toLex_lt_toLex' : toLex x < toLex y ↔ x.1 <= y.1 ∧ (x.1 = y.1 -> x.2 < y.2
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.Lex.toLex_lt_toLex`：toLex_lt_toLex [LT α] [LT β] {x y : α × β} : to
Lex x < toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p

--- 原说明 ---
Variant of `Prod.Lex.toLex_lt_toLex` for partial orders.
-/
lemma toLex_lt_toLex' : toLex x < toLex y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 < y.2) := by
  rw [toLex_lt_toLex]
  simp only [lt_iff_le_not_ge, le_antisymm_iff]
  tauto

/-- Variant of `Prod.Lex.le_iff` for partial orders. -/
@[to_dual none]
/-
**Prod.Lex.le_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Prod.Lex`。
形式化陈述：le_iff' {x y : α ×ₗ β} : x <= y ↔ (ofLex x).1 <= (ofLex y).1 ∧ ((ofLex x).
1 = (ofLex y).1 -> (ofLex x).2 <= (ofLex y).2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Prod.Lex.toLex_le_toLex'`：toLex_le_toLex' : toLex x <= toLex y ↔ x.1 <= 
y.1 ∧ (x.1 = y.1 -> x.2 <= y.2)

--- 原说明 ---
Variant of `Prod.Lex.le_iff` for partial orders.
-/
lemma le_iff' {x y : α ×ₗ β} :
    x ≤ y ↔ (ofLex x).1 ≤ (ofLex y).1 ∧ ((ofLex x).1 = (ofLex y).1 → (ofLex x).2 ≤ (ofLex y).2) :=
  toLex_le_toLex'

/-- Variant of `Prod.Lex.lt_iff` for partial orders. -/
@[to_dual none]
/-
**Prod.Lex.lt_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Prod.Lex`。
形式化陈述：lt_iff' {x y : α ×ₗ β} : x < y ↔ (ofLex x).1 <= (ofLex y).1 ∧ ((ofLex x).1
 = (ofLex y).1 -> (ofLex x).2 < (ofLex y).2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Prod.Lex.toLex_lt_toLex'`：toLex_lt_toLex' : toLex x < toLex y ↔ x.1 <= y
.1 ∧ (x.1 = y.1 -> x.2 < y.2)

--- 原说明 ---
Variant of `Prod.Lex.lt_iff` for partial orders.
-/
lemma lt_iff' {x y : α ×ₗ β} :
    x < y ↔ (ofLex x).1 ≤ (ofLex y).1 ∧ ((ofLex x).1 = (ofLex y).1 → (ofLex x).2 < (ofLex y).2) :=
  toLex_lt_toLex'
/-
**Prod.Lex.toLex_mono** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：toLex_mono : Monotone (toLex : α × β -> α ×ₗ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Prod.Lex.toLex_le_toLex'`：toLex_le_toLex' : toLex x <= toLex y ↔ x.1 <= 
y.1 ∧ (x.1 = y.1 -> x.2 <= y.2)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem toLex_mono : Monotone (toLex : α × β → α ×ₗ β) :=
  fun _x _y hxy ↦ toLex_le_toLex'.2 ⟨hxy.1, fun _ ↦ hxy.2⟩
/-
**Prod.Lex.toLex_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：toLex_strictMono : StrictMono (toLex : α × β -> α ×ₗ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.mk_lt_mk_iff_right`：mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b
₂
-/
theorem toLex_strictMono : StrictMono (toLex : α × β → α ×ₗ β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  obtain rfl | ha : a₁ = a₂ ∨ _ := h.le.1.eq_or_lt
  · exact right _ (Prod.mk_lt_mk_iff_right.1 h)
  · exact left _ _ ha

end PartialOrderPreorder

/-- Dictionary / lexicographic partial order for pairs. -/
/-
**Prod.Lex.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：instPartialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] : Partial
Order (α ×ₗ β) where le_antisymm _ _
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dictionary / lexicographic partial order for pairs.
-/
instance instPartialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] :
    PartialOrder (α ×ₗ β) where
  le_antisymm _ _ := antisymm_of (Prod.Lex _ _)
/-
**Prod.Lex.instOrdLexProd** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：instOrdLexProd [Ord α] [Ord β] : Ord (α ×ₗ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrdLexProd [Ord α] [Ord β] : Ord (α ×ₗ β) := fast_instance% lexOrd
/-
**Prod.Lex.compare_def** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：compare_def [Ord α] [Ord β] : @compare (α ×ₗ β) _ = compareLex (compareOn 
fun x => (ofLex x).1) (compareOn fun x => (ofLex x).2)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compare_def [Ord α] [Ord β] : @compare (α ×ₗ β) _ =
    compareLex (compareOn fun x => (ofLex x).1) (compareOn fun x => (ofLex x).2) := rfl
/-
**Prod.Lex._root_.lexOrd_eq** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.lexOrd_eq [Ord α] [Ord β] : @lexOrd α β _ _ = instOrdLexProd := rfl
/-
**Prod.Lex._root_.Ord.lex_eq** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ord.lex_eq [oα : Ord α] [oβ : Ord β] : Ord.lex oα oβ = instOrdLexProd := rfl
/-
**Prod.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ord α] [Ord β] [Std.OrientedOrd α] [Std.OrientedOrd β] : Std.OrientedOrd (α ×ₗ β) :=
  inferInstanceAs (@Std.OrientedCmp (α × β) (compareLex _ _))
/-
**Prod.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ord α] [Ord β] [Std.TransOrd α] [Std.TransOrd β] : Std.TransOrd (α ×ₗ β) :=
  inferInstanceAs (@Std.TransCmp (α × β) (compareLex _ _))

/-- Dictionary / lexicographic linear order for pairs. -/
/-
**Prod.Lex.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：instLinearOrder (α β : Type*) [LinearOrder α] [LinearOrder β] : LinearOrde
r (α ×ₗ β) where le_total
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dictionary / lexicographic linear order for pairs.
-/
instance instLinearOrder (α β : Type*) [LinearOrder α] [LinearOrder β] : LinearOrder (α ×ₗ β) where
  le_total := total_of (Prod.Lex _ _)
  toDecidableLE := Prod.Lex.decidable _ _
  toDecidableLT := Prod.Lex.decidable _ _
  toDecidableEq := instDecidableEqLex _
  compare_eq_compareOfLessAndEq := fun a b => by
    have : DecidableLT (α ×ₗ β) := Prod.Lex.decidable _ _
    have : Std.LawfulBEqOrd (α ×ₗ β) := ⟨by
      simp [compare_def, compareLex, compareOn, Ordering.then_eq_eq]⟩
    have : Std.LawfulLTOrd (α ×ₗ β) := ⟨by
      simp [compare_def, compareLex, compareOn, Ordering.then_eq_lt, toLex_lt_toLex,
        compare_lt_iff_lt]⟩
    convert! Std.LawfulLTCmp.eq_compareOfLessAndEq (cmp := compare) a b

@[to_dual]
/-
**Prod.Lex.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：orderBot [PartialOrder α] [Preorder β] [OrderBot α] [OrderBot β] : OrderBo
t (α ×ₗ β) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderBot [PartialOrder α] [Preorder β] [OrderBot α] [OrderBot β] : OrderBot (α ×ₗ β) where
  bot := toLex ⊥
  bot_le _ := toLex_mono bot_le
/-
**Prod.Lex.boundedOrder** 是 Mathlib 中的一个定义，位于命名空间 `Prod.Lex`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : PartialOrder α] → [inst_1 
: Preorder β] → [BoundedOrder α] → [BoundedOrder β] → BoundedOrder (Lex (α × β))
参数：Lex (α × β)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance boundedOrder [PartialOrder α] [Preorder β] [BoundedOrder α] [BoundedOrder β] :
    BoundedOrder (α ×ₗ β) where
/-
**Prod.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense := by
    rintro _ _ (@⟨a₁, b₁, a₂, b₂, h⟩ | @⟨a, b₁, b₂, h⟩)
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(c, b₁), left _ _ h₁, left _ _ h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(a, c), right _ h₁, right _ h₂⟩
/-
**Prod.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [Preorder β] [NoMinOrder β] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense x y h := by
    cases x with | h x
    cases y with | h y
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_lt y.2
      use toLex (y.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h.1, htv, hvu]

@[to_dual existing]
/-
**Prod.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [Preorder β] [NoMaxOrder β] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense x y h := by
    cases x with | h x
    cases y with | h y
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_gt x.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h.1, htv, hvu]

@[to_dual]
/-
**Prod.Lex.noMaxOrder_of_left** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：noMaxOrder_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (
α ×ₗ β) where exists_gt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lex.forall`：∀ {α : Type u_1} {p : Lex α → Prop}, (∀ (a : Lex α), p a) ↔ 
∀ (a : α), p (toLex a)
· 使用定理 `Prod.forall`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∀ (x :
 α × β), p x) ↔ ∀ (a : α) (b : β), p (a, b)
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
instance noMaxOrder_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rw [Lex.forall, Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt a
    use toLex (c, b)
    simpa [lt_iff]

@[to_dual]
/-
**Prod.Lex.noMaxOrder_of_right** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：noMaxOrder_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder 
(α ×ₗ β) where exists_gt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Lex.forall`：∀ {α : Type u_1} {p : Lex α → Prop}, (∀ (a : Lex α), p a) ↔ 
∀ (a : α), p (toLex a)
· 使用定理 `Prod.forall`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∀ (x :
 α × β), p x) ↔ ∀ (a : α) (b : β), p (a, b)
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
instance noMaxOrder_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rw [Lex.forall, Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt b
    use toLex (a, c)
    simpa [lt_iff]

end Prod.Lex

