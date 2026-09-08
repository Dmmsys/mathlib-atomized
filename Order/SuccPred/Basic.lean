/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Cover
public import Mathlib.Order.Iterate

/-!
# Successor and predecessor

This file defines successor and predecessor orders. `succ a`, the successor of an element `a : α` is
the least element greater than `a`. `pred a` is the greatest element less than `a`. Typical examples
include `ℕ`, `ℤ`, `ℕ+`, `Fin n`, but also `ENat`, the lexicographic order of a successor/predecessor
order...

## Typeclasses

* `SuccOrder`: Order equipped with a sensible successor function.
* `PredOrder`: Order equipped with a sensible predecessor function.

## Implementation notes

Maximal elements don't have a sensible successor. Thus the naïve typeclass
```lean
class NaiveSuccOrder (α : Type*) [Preorder α] where
  (succ : α → α)
  (succ_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
  (lt_succ_iff : ∀ {a b}, a < succ b ↔ a ≤ b)
```
can't apply to an `OrderTop` because plugging in `a = b = ⊤` into either of `succ_le_iff` and
`lt_succ_iff` yields `⊤ < ⊤` (or more generally `m < m` for a maximal element `m`).
The solution taken here is to remove the implications `≤ → <` and instead require that `a < succ a`
for all non-maximal elements (enforced by the combination of `le_succ` and the contrapositive of
`max_of_succ_le`).
The stricter condition of every element having a sensible successor can be obtained through the
combination of `SuccOrder α` and `NoMaxOrder α`.
-/

@[expose] public section

open Function OrderDual Set

variable {α β : Type*}

/-- Order equipped with a sensible successor function. -/
/-
**SuccOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [Preorder α] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order equipped with a sensible successor function.
-/
class SuccOrder (α : Type*) [Preorder α] where
  /-- Successor function -/
  succ : α → α
  /-- Proof of basic ordering with respect to `succ` -/
  le_succ : ∀ a, a ≤ succ a
  /-- Proof of interaction between `succ` and maximal element -/
  max_of_succ_le {a} : succ a ≤ a → IsMax a
  /-- Proof that `succ a` is the least element greater than `a` -/
  succ_le_of_lt {a b} : a < b → succ a ≤ b

/-- Order equipped with a sensible predecessor function. -/
@[to_dual (attr := ext)]
/-
**PredOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [Preorder α] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order equipped with a sensible predecessor function.
-/
class PredOrder (α : Type*) [Preorder α] where
  /-- Predecessor function -/
  pred : α → α
  /-- Proof of basic ordering with respect to `pred` -/
  pred_le : ∀ a, pred a ≤ a
  /-- Proof of interaction between `pred` and minimal element -/
  min_of_le_pred {a} : a ≤ pred a → IsMin a
  /-- Proof that `pred b` is the greatest element less than `b` -/
  le_pred_of_lt {a b} : a < b → a ≤ pred b

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [SuccOrder α] : PredOrder αᵒᵈ where
  pred := toDual ∘ SuccOrder.succ ∘ ofDual
  pred_le := by simp [SuccOrder.le_succ]
  min_of_le_pred h := by apply SuccOrder.max_of_succ_le h
  le_pred_of_lt {a b} h := SuccOrder.succ_le_of_lt h

section Preorder

variable [Preorder α]

/-- A constructor for `SuccOrder α` usable when `α` has no maximal element. -/
@[to_dual (attr := instance_reducible)
/-- A constructor for `PredOrder α` usable when `α` has no minimal element. -/]
/-
**SuccOrder.ofSuccLeIff** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SuccOrder.ofSuccLeIff (succ : α -> α) (hsucc_le_iff : forall {a b}, succ a
 <= b ↔ a < b) : SuccOrder α where succ
参数：succ : α -> α；hsucc_le_iff : forall {a b}, succ a <= b ↔ a < b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def SuccOrder.ofSuccLeIff (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) :
    SuccOrder α where
  succ := succ
  le_succ _ := (hsucc_le_iff.1 le_rfl).le
  max_of_succ_le ha := (lt_irrefl _ <| hsucc_le_iff.1 ha).elim
  succ_le_of_lt := hsucc_le_iff.2

end Preorder

section LinearOrder

variable [LinearOrder α]

/-- A constructor for `SuccOrder α` for `α` a linear order. -/
@[to_dual (attr := simps, instance_reducible)
/-- A constructor for `PredOrder α` for `α` a linear order. -/]
/-
**SuccOrder.ofCore** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SuccOrder.ofCore (succ : α -> α) (hn : forall {a}, ¬IsMax a -> forall b, a
 < b ↔ succ a <= b) (hm : forall a, IsMax a -> succ a = a) : SuccOrder α where s
ucc
参数：succ : α -> α；hn : forall {a}, ¬IsMax a -> forall b, a < b ↔ succ a <= b；hm :
 forall a, IsMax a -> succ a = a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def SuccOrder.ofCore (succ : α → α) (hn : ∀ {a}, ¬IsMax a → ∀ b, a < b ↔ succ a ≤ b)
    (hm : ∀ a, IsMax a → succ a = a) : SuccOrder α where
  succ := succ
  succ_le_of_lt {a b} := by_cases (fun h hab ↦ (hm a h).symm ▸ hab.le) fun h ↦ (hn h b).mp
  le_succ a := by_cases (fun h ↦ (hm a h).symm.le) fun h ↦ le_of_lt <| by simpa using (hn h a).not
  max_of_succ_le {a} := not_imp_not.mp fun h ↦ by simpa using (hn h a).not

variable (α)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- A well-order is a `SuccOrder`. -/
@[to_dual (attr := instance_reducible)
/-- A linear order with well-founded greater-than relation is a `PredOrder`. -/]
/-
**SuccOrder.ofLinearWellFoundedLT** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SuccOrder.ofLinearWellFoundedLT [WellFoundedLT α] : SuccOrder α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def SuccOrder.ofLinearWellFoundedLT [WellFoundedLT α] : SuccOrder α :=
  ofCore (fun a ↦ if h : (Ioi a).Nonempty then wellFounded_lt.min _ h else a)
    (fun ha _ ↦ by
      rw [not_isMax_iff] at ha
      simp_rw [Set.Nonempty, mem_Ioi, dif_pos ha]
      exact ⟨wellFounded_lt.min_le (s := Ioi _), lt_of_lt_of_le (wellFounded_lt.prop_min ha)⟩)
    fun _ ha ↦ dif_neg (not_not_intro ha <| not_isMax_iff.mpr ·)

end LinearOrder

/-! ### Successor and predecessor orders -/

namespace Order

section Preorder

variable [Preorder α] [SuccOrder α] {a b : α}

/-- The successor of an element. If `a` is not maximal, then `succ a` is the least element greater
than `a`. If `a` is maximal, then `succ a = a`. -/
@[to_dual /-- The predecessor of an element. If `a` is not minimal, then `pred a` is the greatest
element less than `a`. If `a` is minimal, then `pred a = a`. -/]
/-
**Order.succ** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：succ : α -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def succ : α → α :=
  SuccOrder.succ

@[to_dual pred_le]
/-
**Order.le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_succ : forall a : α, a <= succ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.le_succ`：∀ {α : Type u_3} {inst : Preorder α} [self : SuccOrde
r α] (a : α), a ≤ SuccOrder.succ a
-/
theorem le_succ : ∀ a : α, a ≤ succ a :=
  SuccOrder.le_succ

@[to_dual min_of_le_pred]
/-
**Order.max_of_succ_le** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：max_of_succ_le {a : α} : succ a <= a -> IsMax a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.max_of_succ_le`：∀ {α : Type u_3} {inst : Preorder α} [self : S
uccOrder α] {a : α}, SuccOrder.succ a ≤ a → IsMax a
-/
theorem max_of_succ_le {a : α} : succ a ≤ a → IsMax a :=
  SuccOrder.max_of_succ_le

@[to_dual le_pred_of_lt]
/-
**Order.succ_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_le_of_lt {a b : α} : a < b -> succ a <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.succ_le_of_lt`：∀ {α : Type u_3} {inst : Preorder α} [self : Su
ccOrder α] {a b : α}, a < b → SuccOrder.succ a ≤ b
-/
theorem succ_le_of_lt {a b : α} : a < b → succ a ≤ b :=
  SuccOrder.succ_le_of_lt

@[to_dual le_pred]
alias _root_.LT.lt.succ_le := succ_le_of_lt

@[to_dual (attr := simp) le_pred_iff_isMin]
/-
**Order.succ_le_iff_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_le_iff_isMax : succ a <= a ↔ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.max_of_succ_le`：max_of_succ_le {a : α} : succ a <= a -> IsMax a
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
-/
theorem succ_le_iff_isMax : succ a ≤ a ↔ IsMax a :=
  ⟨max_of_succ_le, fun h => h <| le_succ _⟩

alias ⟨_root_.IsMax.of_succ_le, _root_.IsMax.succ_le⟩ := succ_le_iff_isMax

attribute [to_dual of_le_pred] IsMax.of_succ_le
attribute [to_dual le_pred] IsMax.succ_le

@[to_dual (attr := simp) pred_lt_iff_not_isMin]
/-
**Order.lt_succ_iff_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_iff_not_isMax : a < succ a ↔ ¬IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isMax_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Order.max_of_succ_le`：max_of_succ_le {a : α} : succ a <= a -> IsMax a
-/
theorem lt_succ_iff_not_isMax : a < succ a ↔ ¬IsMax a :=
  ⟨not_isMax_of_lt, fun ha => (le_succ a).lt_of_not_ge fun h => ha <| max_of_succ_le h⟩

@[to_dual pred_lt_of_not_isMin]
alias ⟨_, lt_succ_of_not_isMax⟩ := lt_succ_iff_not_isMax

@[to_dual pred_wcovBy]
/-
**Order.wcovBy_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：wcovBy_succ (a : α) : a ⩿ succ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
-/
theorem wcovBy_succ (a : α) : a ⩿ succ a :=
  ⟨le_succ a, fun _ hb => (succ_le_of_lt hb).not_gt⟩

@[to_dual pred_covBy_of_not_isMin]
/-
**Order.covBy_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：covBy_succ_of_not_isMax (h : ¬IsMax a) : a ⋖ succ a
参数：h : ¬IsMax a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.covBy_of_lt`：WCovBy.covBy_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b
· 使用定理 `Order.wcovBy_succ`：wcovBy_succ (a : α) : a ⩿ succ a
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
-/
theorem covBy_succ_of_not_isMax (h : ¬IsMax a) : a ⋖ succ a :=
  (wcovBy_succ a).covBy_of_lt <| lt_succ_of_not_isMax h

@[to_dual pred_lt_of_le_of_not_isMin]
/-
**Order.lt_succ_of_le_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_of_le_of_not_isMax (hab : b <= a) (ha : ¬IsMax a) : b < succ a
参数：hab : b <= a；ha : ¬IsMax a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
-/
theorem lt_succ_of_le_of_not_isMax (hab : b ≤ a) (ha : ¬IsMax a) : b < succ a :=
  hab.trans_lt <| lt_succ_of_not_isMax ha

@[to_dual le_pred_iff_of_not_isMin]
/-
**Order.succ_le_iff_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_le_iff_of_not_isMax (ha : ¬IsMax a) : succ a <= b ↔ a < b
参数：ha : ¬IsMax a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
-/
theorem succ_le_iff_of_not_isMax (ha : ¬IsMax a) : succ a ≤ b ↔ a < b :=
  ⟨(lt_succ_of_not_isMax ha).trans_le, succ_le_of_lt⟩

@[to_dual le_pred_iff_of_not_isMin']
/-
**Order.succ_le_iff_of_not_isMax'** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_le_iff_of_not_isMax' (hb : ¬IsMax b) : succ a <= b ↔ a < b
参数：hb : ¬IsMax b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
-/
theorem succ_le_iff_of_not_isMax' (hb : ¬IsMax b) : succ a ≤ b ↔ a < b := by
  by_cases ha : IsMax a
  · grind [le_succ, IsMax.mono]
  · exact succ_le_iff_of_not_isMax ha

@[to_dual]
/-
**Order.succ_lt_succ_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：succ_lt_succ_of_not_isMax (h : a < b) (hb : ¬ IsMax b) : succ a < succ b
参数：h : a < b；hb : ¬ IsMax b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_succ_of_le_of_not_isMax`：lt_succ_of_le_of_not_isMax (hab : b <=
 a) (ha : ¬IsMax a) : b < succ a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
-/
lemma succ_lt_succ_of_not_isMax (h : a < b) (hb : ¬ IsMax b) : succ a < succ b :=
  lt_succ_of_le_of_not_isMax (succ_le_of_lt h) hb

@[to_dual (attr := simp, mono, gcongr)]
/-
**Order.succ_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_le_succ (h : a <= b) : succ a <= succ b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `IsMax.mono`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, IsMax a → a 
≤ b → IsMax b
· 使用定理 `Order.lt_succ_of_le_of_not_isMax`：lt_succ_of_le_of_not_isMax (hab : b <=
 a) (ha : ¬IsMax a) : b < succ a
-/
theorem succ_le_succ (h : a ≤ b) : succ a ≤ succ b := by
  by_cases hb : IsMax b
  · by_cases hba : b ≤ a
    · exact (hb <| hba.trans <| le_succ _).trans (le_succ _)
    · exact succ_le_of_lt ((h.lt_of_not_ge hba).trans_le <| le_succ b)
  · rw [succ_le_iff_of_not_isMax fun ha => hb <| ha.mono h]
    apply lt_succ_of_le_of_not_isMax h hb

@[to_dual]
/-
**Order.succ_mono** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_mono : Monotone (succ : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.succ_le_succ`：succ_le_succ (h : a <= b) : succ a <= succ b
-/
theorem succ_mono : Monotone (succ : α → α) := fun _ _ => succ_le_succ

/-- See also `Order.succ_eq_of_covBy`. -/
@[to_dual pred_le_of_wcovBy /-- See also `Order.pred_eq_of_covBy`. -/]
/-
**Order.le_succ_of_wcovBy** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：le_succ_of_wcovBy (h : a ⩿ b) : b <= succ a
参数：h : a ⩿ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.covBy_or_le_and_le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α
}, a ⩿ b → a ⋖ b ∨ a ≤ b ∧ b ≤ a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `LT.lt.not_isMax`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
· 使用定理 `LT.lt.succ_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : SuccOrder 
α] {a b : α}, a < b → Order.succ a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a

--- 原说明 ---
See also `Order.succ_eq_of_covBy`.
-/
lemma le_succ_of_wcovBy (h : a ⩿ b) : b ≤ succ a := by
  obtain hab | ⟨-, hba⟩ := h.covBy_or_le_and_le
  · by_contra hba
    exact h.2 (lt_succ_of_not_isMax hab.lt.not_isMax) <| hab.lt.succ_le.lt_of_not_ge hba
  · exact hba.trans (le_succ _)

@[to_dual pred_le]
alias _root_.WCovBy.le_succ := le_succ_of_wcovBy

@[to_dual pred_iterate_le]
/-
**Order.le_succ_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_succ_iterate (k : Nat) (x : α) : x <= succ^[k] x
参数：k : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.id_le_iterate_of_id_le`：id_le_iterate_of_id_le (h : id <= f) (n
 : Nat) : id <= f^[n]
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
-/
theorem le_succ_iterate (k : ℕ) (x : α) : x ≤ succ^[k] x :=
  id_le_iterate_of_id_le le_succ _ _

-- `to_dual` doesn't support `Monotone.monotone_iterate_of_le_map`, so we can't use `to_dual` here.
/-
**Order.isMax_iterate_succ_of_eq_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isMax_iterate_succ_of_eq_of_lt {n m : Nat} (h_eq : succ^[n] a = succ^[m] a
) (h_lt : n < m) : IsMax (succ^[n] a)
参数：h_eq : succ^[n] a = succ^[m] a；h_lt : n < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.max_of_succ_le`：max_of_succ_le {a : α} : succ a <= a -> IsMax a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Monotone.monotone_iterate_of_le_map`：monotone_iterate_of_le_map (hf : Mo
notone f) (hx : x <= f x) : Monotone fun n => f^[n] x
· 使用定理 `Order.succ_mono`：succ_mono : Monotone (succ : α -> α)
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem isMax_iterate_succ_of_eq_of_lt {n m : ℕ} (h_eq : succ^[n] a = succ^[m] a)
    (h_lt : n < m) : IsMax (succ^[n] a) := by
  refine max_of_succ_le (le_trans ?_ h_eq.symm.le)
  rw [← iterate_succ_apply' succ]
  have h_le : n + 1 ≤ m := Nat.succ_le_of_lt h_lt
  exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ a) h_le
/-
**Order.isMax_iterate_succ_of_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isMax_iterate_succ_of_eq_of_ne {n m : Nat} (h_eq : succ^[n] a = succ^[m] a
) (h_ne : n != m) : IsMax (succ^[n] a)
参数：h_eq : succ^[n] a = succ^[m] a；h_ne : n != m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Order.isMax_iterate_succ_of_eq_of_lt`：isMax_iterate_succ_of_eq_of_lt {n 
m : Nat} (h_eq : succ^[n] a = succ^[m] a) (h_lt : n < m) : IsMax (succ^[n] a)
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem isMax_iterate_succ_of_eq_of_ne {n m : ℕ} (h_eq : succ^[n] a = succ^[m] a)
    (h_ne : n ≠ m) : IsMax (succ^[n] a) := by
  rcases le_total n m with h | h
  · exact isMax_iterate_succ_of_eq_of_lt h_eq (lt_of_le_of_ne h h_ne)
  · rw [h_eq]
    exact isMax_iterate_succ_of_eq_of_lt h_eq.symm (lt_of_le_of_ne h h_ne.symm)

@[to_dual (attr := deprecated "use `gcongr`/`grw` and `lt_succ_of_not_isMax"
  (since := "2026-06-06"))]
/-
**Order.Iic_subset_Iio_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iic_subset_Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iic a subseteq Iio (suc
c a)
参数：ha : ¬IsMax a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iic_subset_Iio._gcongr_3`：∀ {α : Type u_1} [inst : Preorder α] {a b 
: α}, a < b → Set.Iic a ⊆ Set.Iio b
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
-/
theorem Iic_subset_Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iic a ⊆ Iio (succ a) := by
  gcongr
  exact lt_succ_of_not_isMax ha

@[to_dual]
/-
**Order.Ici_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici (succ a) = Ioi a
参数：ha : ¬IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
-/
theorem Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici (succ a) = Ioi a :=
  Set.ext fun _ => succ_le_iff_of_not_isMax ha

@[to_dual Icc_subset_Ioc_pred_left_of_not_isMin]
/-
**Order.Icc_subset_Ico_succ_right_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`
。
形式化陈述：Icc_subset_Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Icc a b subseteq 
Ico a (succ b)
参数：hb : ¬IsMax b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_subset_Ico_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ < a₁ → Set.Icc b a₂ ⊆ Set.Ico b a₁
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
-/
theorem Icc_subset_Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Icc a b ⊆ Ico a (succ b) := by
  gcongr
  exact lt_succ_of_not_isMax hb

@[to_dual Ico_subset_Ioo_pred_left_of_not_isMin]
/-
**Order.Ioc_subset_Ioo_succ_right_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`
。
形式化陈述：Ioc_subset_Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioc a b subseteq 
Ioo a (succ b)
参数：hb : ¬IsMax b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_subset_Ioo_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ < a₁ → Set.Ioc b a₂ ⊆ Set.Ioo b a₁
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
-/
theorem Ioc_subset_Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioc a b ⊆ Ioo a (succ b) := by
  gcongr
  exact lt_succ_of_not_isMax hb

@[to_dual Icc_pred_right_of_not_isMin]
/-
**Order.Icc_succ_left_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Icc_succ_left_of_not_isMax (ha : ¬IsMax a) : Icc (succ a) b = Ioc a b
参数：ha : ¬IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
· 使用定理 `Order.Ici_succ_of_not_isMax`：Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici
 (succ a) = Ioi a
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
-/
theorem Icc_succ_left_of_not_isMax (ha : ¬IsMax a) : Icc (succ a) b = Ioc a b := by
  rw [← Ici_inter_Iic, Ici_succ_of_not_isMax ha, Ioi_inter_Iic]

@[to_dual Ioc_pred_right_of_not_isMin]
/-
**Order.Ico_succ_left_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ico_succ_left_of_not_isMax (ha : ¬IsMax a) : Ico (succ a) b = Ioo a b
参数：ha : ¬IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iio b = Set.Ico a b
· 使用定理 `Order.Ici_succ_of_not_isMax`：Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici
 (succ a) = Ioi a
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
-/
theorem Ico_succ_left_of_not_isMax (ha : ¬IsMax a) : Ico (succ a) b = Ioo a b := by
  rw [← Ici_inter_Iio, Ici_succ_of_not_isMax ha, Ioi_inter_Iio]

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual pred_lt]
/-
**Order.lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ (a : α) : a < succ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem lt_succ (a : α) : a < succ a :=
  lt_succ_of_not_isMax <| not_isMax a

@[to_dual (attr := simp) pred_lt_of_le]
/-
**Order.lt_succ_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_of_le : a <= b -> a < succ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_succ_of_le_of_not_isMax`：lt_succ_of_le_of_not_isMax (hab : b <=
 a) (ha : ¬IsMax a) : b < succ a
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem lt_succ_of_le : a ≤ b → a < succ b :=
  (lt_succ_of_le_of_not_isMax · <| not_isMax b)

@[to_dual (attr := simp) le_pred_iff]
/-
**Order.succ_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_le_iff : succ a <= b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem succ_le_iff : succ a ≤ b ↔ a < b :=
  succ_le_iff_of_not_isMax <| not_isMax a

@[to_dual (attr := gcongr)]
/-
**Order.succ_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_lt_succ (hab : a < b) : succ a < succ b
参数：hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem succ_lt_succ (hab : a < b) : succ a < succ b := by simp [hab]

@[to_dual]
/-
**Order.succ_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_strictMono : StrictMono (succ : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.succ_lt_succ`：succ_lt_succ (hab : a < b) : succ a < succ b
-/
theorem succ_strictMono : StrictMono (succ : α → α) := fun _ _ => succ_lt_succ

@[to_dual pred_covBy]
/-
**Order.covBy_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：covBy_succ (a : α) : a ⋖ succ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.covBy_succ_of_not_isMax`：covBy_succ_of_not_isMax (h : ¬IsMax a) : 
a ⋖ succ a
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem covBy_succ (a : α) : a ⋖ succ a :=
  covBy_succ_of_not_isMax <| not_isMax a

@[to_dual]
/-
**Order.Iic_subset_Iio_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iic_subset_Iio_succ (a : α) : Iic a subseteq Iio (succ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Iic_subset_Iio_succ (a : α) : Iic a ⊆ Iio (succ a) := by simp

@[to_dual (attr := simp)]
/-
**Order.Ici_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ici_succ (a : α) : Ici (succ a) = Ioi a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ici_succ_of_not_isMax`：Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici
 (succ a) = Ioi a
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Ici_succ (a : α) : Ici (succ a) = Ioi a :=
  Ici_succ_of_not_isMax <| not_isMax _

@[to_dual (attr := simp) Icc_subset_Ioc_pred_left]
/-
**Order.Icc_subset_Ico_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Icc_subset_Ico_succ_right (a b : α) : Icc a b subseteq Ico a (succ b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Icc_subset_Ico_succ_right_of_not_isMax`：Icc_subset_Ico_succ_right_
of_not_isMax (hb : ¬IsMax b) : Icc a b subseteq Ico a (succ b)
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Icc_subset_Ico_succ_right (a b : α) : Icc a b ⊆ Ico a (succ b) :=
  Icc_subset_Ico_succ_right_of_not_isMax <| not_isMax _

@[to_dual (attr := simp) Ico_subset_Ioo_pred_left]
/-
**Order.Ioc_subset_Ioo_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ioc_subset_Ioo_succ_right (a b : α) : Ioc a b subseteq Ioo a (succ b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ioc_subset_Ioo_succ_right_of_not_isMax`：Ioc_subset_Ioo_succ_right_
of_not_isMax (hb : ¬IsMax b) : Ioc a b subseteq Ioo a (succ b)
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Ioc_subset_Ioo_succ_right (a b : α) : Ioc a b ⊆ Ioo a (succ b) :=
  Ioc_subset_Ioo_succ_right_of_not_isMax <| not_isMax _

@[to_dual (attr := simp) Icc_pred_right]
/-
**Order.Icc_succ_left** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Icc_succ_left_of_not_isMax`：Icc_succ_left_of_not_isMax (ha : ¬IsMa
x a) : Icc (succ a) b = Ioc a b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_of_not_isMax <| not_isMax _

@[to_dual (attr := simp) Ioc_pred_right]
/-
**Order.Ico_succ_left** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ico_succ_left (a b : α) : Ico (succ a) b = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ico_succ_left_of_not_isMax`：Ico_succ_left_of_not_isMax (ha : ¬IsMa
x a) : Ico (succ a) b = Ioo a b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Ico_succ_left (a b : α) : Ico (succ a) b = Ioo a b :=
  Ico_succ_left_of_not_isMax <| not_isMax _

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α}

@[to_dual (attr := simp)]
/-
**Order.succ_eq_iff_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_eq_iff_isMax : succ a = a ↔ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.max_of_succ_le`：max_of_succ_le {a : α} : succ a <= a -> IsMax a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsMax.eq_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMa
x a → a ≤ b → b = a
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
-/
theorem succ_eq_iff_isMax : succ a = a ↔ IsMax a :=
  ⟨fun h => max_of_succ_le h.le, fun h => h.eq_of_ge <| le_succ _⟩

@[to_dual]
alias ⟨_, _root_.IsMax.succ_eq⟩ := succ_eq_iff_isMax

@[to_dual le_iff_eq_or_le_pred']
/-
**Order.le_iff_eq_or_succ_le** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：le_iff_eq_or_succ_le : a <= b ↔ a = b ∨ succ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsMax.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a : α}, IsMax a → Order.succ a = a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_iff_eq_or_succ_le : a ≤ b ↔ a = b ∨ succ a ≤ b := by
  by_cases ha : IsMax a
  · simpa [ha.succ_eq] using le_of_eq
  · rw [succ_le_iff_of_not_isMax ha, le_iff_eq_or_lt]

@[to_dual le_iff_eq_or_le_pred]
/-
**Order.le_iff_eq_or_succ_le'** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：le_iff_eq_or_succ_le' : a <= b ↔ b = a ∨ succ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Order.le_iff_eq_or_succ_le`：le_iff_eq_or_succ_le : a <= b ↔ a = b ∨ succ
 a <= b
-/
lemma le_iff_eq_or_succ_le' : a ≤ b ↔ b = a ∨ succ a ≤ b := by
  rw [eq_comm]
  exact le_iff_eq_or_succ_le

@[to_dual le_and_pred_le_iff]
/-
**Order.le_and_le_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_and_le_succ_iff : a <= b ∧ b <= succ a ↔ b = a ∨ b = succ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_and_le_succ_iff : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a := by
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hba : b ≠ a ↦
    h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm), ?_⟩
  rintro (rfl | rfl)
  · exact ⟨le_rfl, le_succ b⟩
  · exact ⟨le_succ a, le_rfl⟩

@[to_dual pred_le_and_le_iff]
/-
**Order.le_succ_and_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_succ_and_le_iff : b <= succ a ∧ a <= b ↔ b = a ∨ b = succ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Order.le_and_le_succ_iff`：le_and_le_succ_iff : a <= b ∧ b <= succ a ↔ b 
= a ∨ b = succ a
-/
theorem le_succ_and_le_iff : b ≤ succ a ∧ a ≤ b ↔ b = a ∨ b = succ a := by
  rw [and_comm]
  exact le_and_le_succ_iff

/-- See also `Order.le_succ_of_wcovBy`. -/
@[to_dual /-- See also `Order.pred_le_of_wcovBy`. -/]
/-
**Order.succ_eq_of_covBy** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：succ_eq_of_covBy (h : a ⋖ b) : succ a = b
参数：h : a ⋖ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `WCovBy.le_succ`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : SuccOrder
 α] {a b : α}, a ⩿ b → b ≤ Order.succ a
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b

--- 原说明 ---
See also `Order.le_succ_of_wcovBy`.
-/
lemma succ_eq_of_covBy (h : a ⋖ b) : succ a = b := (succ_le_of_lt h.lt).antisymm h.wcovBy.le_succ

@[to_dual]
alias _root_.CovBy.succ_eq := succ_eq_of_covBy

@[to_dual]
/-
**Order._root_.OrderIso.map_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrderIso.map_succ [PartialOrder β] [SuccOrder β] (f : α ≃o β) (a : α) :
    f (succ a) = succ (f a) := by
  by_cases h : IsMax a
  · rw [h.succ_eq, (f.isMax_apply.2 h).succ_eq]
  · exact ((apply_covBy_apply_iff f).2 <| covBy_succ_of_not_isMax h).succ_eq.symm

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
/-
**Order.succ_eq_iff_covBy** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_eq_iff_covBy : succ a = b ↔ a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.covBy_succ`：covBy_succ (a : α) : a ⋖ succ a
· 使用定理 `CovBy.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a b : α}, a ⋖ b → Order.succ a = b
-/
theorem succ_eq_iff_covBy : succ a = b ↔ a ⋖ b :=
  ⟨by rintro rfl; exact covBy_succ _, CovBy.succ_eq⟩

end NoMaxOrder

section OrderTop

variable [OrderTop α]

@[to_dual (attr := simp)]
/-
**Order.succ_top** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_top : succ (⊤ : α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
· 使用定理 `isMax_iff_eq_top`：isMax_iff_eq_top : IsMax a ↔ a = ⊤
-/
theorem succ_top : succ (⊤ : α) = ⊤ := by
  rw [succ_eq_iff_isMax, isMax_iff_eq_top]

@[to_dual le_pred_iff_eq_bot]
/-
**Order.succ_le_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_le_iff_eq_top : succ a <= a ↔ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Order.succ_le_iff_isMax`：succ_le_iff_isMax : succ a <= a ↔ IsMax a
· 使用定理 `isMax_iff_eq_top`：isMax_iff_eq_top : IsMax a ↔ a = ⊤
-/
theorem succ_le_iff_eq_top : succ a ≤ a ↔ a = ⊤ :=
  succ_le_iff_isMax.trans isMax_iff_eq_top

@[to_dual pred_lt_iff_ne_bot]
/-
**Order.lt_succ_iff_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_iff_ne_top : a < succ a ↔ a != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Order.lt_succ_iff_not_isMax`：lt_succ_iff_not_isMax : a < succ a ↔ ¬IsMax
 a
· 使用定理 `not_isMax_iff_ne_top`：not_isMax_iff_ne_top : ¬IsMax a ↔ a != ⊤
-/
theorem lt_succ_iff_ne_top : a < succ a ↔ a ≠ ⊤ :=
  lt_succ_iff_not_isMax.trans not_isMax_iff_ne_top

end OrderTop

section OrderBot

variable [OrderBot α] [Nontrivial α]

@[to_dual pred_lt_top]
/-
**Order.bot_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：bot_lt_succ (a : α) : ⊥ < succ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `not_isMax_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot
 α] [Nontrivial α], ¬IsMax ⊥
· 使用定理 `Order.succ_le_succ`：succ_le_succ (h : a <= b) : succ a <= succ b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem bot_lt_succ (a : α) : ⊥ < succ a :=
  (lt_succ_of_not_isMax not_isMax_bot).trans_le <| succ_le_succ bot_le

@[to_dual]
/-
**Order.succ_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_ne_bot (a : α) : succ a != ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Order.bot_lt_succ`：bot_lt_succ (a : α) : ⊥ < succ a
-/
theorem succ_ne_bot (a : α) : succ a ≠ ⊥ :=
  (bot_lt_succ a).ne'

end OrderBot

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] {a b : α}

/-
**Order.succ_max** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : SuccOrder α] (a b : α), 
  Order.succ (max a b) = max (Order.succ a) (Order.succ b)
参数：a b : α；max a b；Order.succ a；Order.succ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Order.succ_mono`：succ_mono : Monotone (succ : α -> α)
-/
@[to_dual] lemma succ_max (a b : α) : succ (max a b) = max (succ a) (succ b) := succ_mono.map_max
/-
**Order.succ_min** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : SuccOrder α] (a b : α), 
  Order.succ (min a b) = min (Order.succ a) (Order.succ b)
参数：a b : α；min a b；Order.succ a；Order.succ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `Order.succ_mono`：succ_mono : Monotone (succ : α -> α)
-/
@[to_dual] lemma succ_min (a b : α) : succ (min a b) = min (succ a) (succ b) := succ_mono.map_min

@[to_dual le_of_pred_lt]
/-
**Order.le_of_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_of_lt_succ {a b : α} : a < succ b -> a <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
-/
theorem le_of_lt_succ {a b : α} : a < succ b → a ≤ b := by
  contrapose!
  exact succ_le_of_lt

@[to_dual pred_lt_iff_of_not_isMin]
/-
**Order.lt_succ_iff_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_iff_of_not_isMax (ha : ¬IsMax a) : b < succ a ↔ b <= a
参数：ha : ¬IsMax a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
-/
theorem lt_succ_iff_of_not_isMax (ha : ¬IsMax a) : b < succ a ↔ b ≤ a := by
  contrapose!
  exact succ_le_iff_of_not_isMax ha

@[to_dual pred_lt_iff_of_not_isMin']
/-
**Order.lt_succ_iff_of_not_isMax'** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_iff_of_not_isMax' (hb : ¬IsMax b) : b < succ a ↔ b <= a
参数：hb : ¬IsMax b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_le_iff_of_not_isMax'`：succ_le_iff_of_not_isMax' (hb : ¬IsMax 
b) : succ a <= b ↔ a < b
-/
theorem lt_succ_iff_of_not_isMax' (hb : ¬IsMax b) : b < succ a ↔ b ≤ a := by
  contrapose!
  exact succ_le_iff_of_not_isMax' hb

@[to_dual (reorder := ha hb)]
/-
**Order.succ_lt_succ_iff_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_lt_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) : succ a < s
ucc b ↔ a < b
参数：ha : ¬IsMax a；hb : ¬IsMax b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem succ_lt_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a < succ b ↔ a < b := by
  rw [lt_succ_iff_of_not_isMax hb, succ_le_iff_of_not_isMax ha]

@[to_dual (reorder := ha hb)]
/-
**Order.succ_le_succ_iff_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_le_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) : succ a <= 
succ b ↔ a <= b
参数：ha : ¬IsMax a；hb : ¬IsMax b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem succ_le_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a ≤ succ b ↔ a ≤ b := by
  rw [succ_le_iff_of_not_isMax ha, lt_succ_iff_of_not_isMax hb]

@[to_dual]
/-
**Order.Iio_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio (succ a) = Iic a
参数：ha : ¬IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
-/
theorem Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio (succ a) = Iic a :=
  Set.ext fun _ => lt_succ_iff_of_not_isMax ha

@[to_dual Ioc_pred_left_of_not_isMin]
/-
**Order.Ico_succ_right_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Ico a (succ b) = Icc a b
参数：hb : ¬IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iio b = Set.Ico a b
· 使用定理 `Order.Iio_succ_of_not_isMax`：Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio
 (succ a) = Iic a
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
-/
theorem Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Ico a (succ b) = Icc a b := by
  rw [← Ici_inter_Iio, Iio_succ_of_not_isMax hb, Ici_inter_Iic]

@[to_dual Ioo_pred_left_of_not_isMin]
/-
**Order.Ioo_succ_right_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioo a (succ b) = Ioc a b
参数：hb : ¬IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
· 使用定理 `Order.Iio_succ_of_not_isMax`：Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio
 (succ a) = Iic a
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
-/
theorem Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioo a (succ b) = Ioc a b := by
  rw [← Ioi_inter_Iio, Iio_succ_of_not_isMax hb, Ioi_inter_Iic]

@[to_dual]
/-
**Order.succ_eq_succ_iff_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_eq_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) : succ a = s
ucc b ↔ a = b
参数：ha : ¬IsMax a；hb : ¬IsMax b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_iff_le_not_lt`：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
· 使用定理 `Order.succ_le_succ_iff_of_not_isMax`：succ_le_succ_iff_of_not_isMax (ha :
 ¬IsMax a) (hb : ¬IsMax b) : succ a <= succ b ↔ a <= b
· 使用定理 `Order.succ_lt_succ_iff_of_not_isMax`：succ_lt_succ_iff_of_not_isMax (ha :
 ¬IsMax a) (hb : ¬IsMax b) : succ a < succ b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem succ_eq_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a = succ b ↔ a = b := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, succ_le_succ_iff_of_not_isMax ha hb,
    succ_lt_succ_iff_of_not_isMax ha hb]

@[to_dual pred_le_iff_eq_or_le]
/-
**Order.le_succ_iff_eq_or_le** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_succ_iff_eq_or_le : a <= succ b ↔ a = succ b ∨ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMax.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a : α}, IsMax a → Order.succ a = a
· 使用定理 `or_iff_right_of_imp`：∀ {a b : Prop}, (a → b) → (a ∨ b ↔ b)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
-/
theorem le_succ_iff_eq_or_le : a ≤ succ b ↔ a = succ b ∨ a ≤ b := by
  by_cases hb : IsMax b
  · rw [hb.succ_eq, or_iff_right_of_imp le_of_eq]
  · rw [← lt_succ_iff_of_not_isMax hb, le_iff_eq_or_lt]

@[to_dual pred_lt_iff_eq_or_lt_of_not_isMin]
/-
**Order.lt_succ_iff_eq_or_lt_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_iff_eq_or_lt_of_not_isMax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a
 < b
参数：hb : ¬IsMax b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
-/
theorem lt_succ_iff_eq_or_lt_of_not_isMax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b :=
  (lt_succ_iff_of_not_isMax hb).trans le_iff_eq_or_lt

@[to_dual]
/-
**Order.not_isMin_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isMin_succ [Nontrivial α] (a : α) : ¬ IsMin (succ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `IsMax.not_isMin`：∀ {β : Type u_2} [inst : PartialOrder β] [Nontrivial β]
 [IsDirectedOrder β] {b : β}, IsMax b → ¬IsMin b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_isMin_of_lt`：not_isMin_of_lt (h : b < a) : ¬IsMin a
-/
theorem not_isMin_succ [Nontrivial α] (a : α) : ¬ IsMin (succ a) := by
  obtain ha | ha := (le_succ a).eq_or_lt
  · exact (ha ▸ succ_eq_iff_isMax.1 ha.symm).not_isMin
  · exact not_isMin_of_lt ha

@[to_dual]
/-
**Order.Iic_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Order.le_succ_iff_eq_or_le`：le_succ_iff_eq_or_le : a <= succ b ↔ a = suc
c b ∨ a <= b
-/
theorem Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a) :=
  ext fun _ => le_succ_iff_eq_or_le

@[to_dual Icc_pred_left]
/-
**Order.Icc_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Icc_succ_right (h : a <= succ b) : Icc a (succ b) = insert (succ b) (Icc a
 b)
参数：h : a <= succ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.Iic_succ`：Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_insert_of_mem`：inter_insert_of_mem (h : a in s) : s inter inse
rt a t = insert a (s inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_succ_right (h : a ≤ succ b) : Icc a (succ b) = insert (succ b) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]

@[to_dual Ico_pred_left]
/-
**Order.Ioc_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ioc_succ_right (h : a < succ b) : Ioc a (succ b) = insert (succ b) (Ioc a 
b)
参数：h : a < succ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.Iic_succ`：Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_insert_of_mem`：inter_insert_of_mem (h : a in s) : s inter inse
rt a t = insert a (s inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ioc_succ_right (h : a < succ b) : Ioc a (succ b) = insert (succ b) (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]

@[to_dual]
/-
**Order.Iio_succ_eq_insert_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iio_succ_eq_insert_of_not_isMax (h : ¬IsMax a) : Iio (succ a) = insert a (
Iio a)
参数：h : ¬IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Order.lt_succ_iff_eq_or_lt_of_not_isMax`：lt_succ_iff_eq_or_lt_of_not_isM
ax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b
-/
theorem Iio_succ_eq_insert_of_not_isMax (h : ¬IsMax a) : Iio (succ a) = insert a (Iio a) :=
  ext fun _ => lt_succ_iff_eq_or_lt_of_not_isMax h

@[to_dual Ioc_pred_left_eq_insert_of_not_isMin]
/-
**Order.Ico_succ_right_eq_insert_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ico_succ_right_eq_insert_of_not_isMax (h₁ : a <= b) (h₂ : ¬IsMax b) : Ico 
a (succ b) = insert b (Ico a b)
参数：h₁ : a <= b；h₂ : ¬IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.Iio_succ_eq_insert_of_not_isMax`：Iio_succ_eq_insert_of_not_isMax (
h : ¬IsMax a) : Iio (succ a) = insert a (Iio a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.insert_inter_of_mem`：insert_inter_of_mem (h : a in t) : insert a s i
nter t = insert a (s inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ico_succ_right_eq_insert_of_not_isMax (h₁ : a ≤ b) (h₂ : ¬IsMax b) :
    Ico a (succ b) = insert b (Ico a b) := by
  simp_rw [← Iio_inter_Ici, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ici.2 h₁)]

@[to_dual Ioo_pred_left_eq_insert_of_not_isMin]
/-
**Order.Ioo_succ_right_eq_insert_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ioo_succ_right_eq_insert_of_not_isMax (h₁ : a < b) (h₂ : ¬IsMax b) : Ioo a
 (succ b) = insert b (Ioo a b)
参数：h₁ : a < b；h₂ : ¬IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.Iio_succ_eq_insert_of_not_isMax`：Iio_succ_eq_insert_of_not_isMax (
h : ¬IsMax a) : Iio (succ a) = insert a (Iio a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.insert_inter_of_mem`：insert_inter_of_mem (h : a in t) : insert a s i
nter t = insert a (s inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ioo_succ_right_eq_insert_of_not_isMax (h₁ : a < b) (h₂ : ¬IsMax b) :
    Ioo a (succ b) = insert b (Ioo a b) := by
  simp_rw [← Iio_inter_Ioi, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual (attr := simp) pred_lt_iff]
/-
**Order.lt_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_iff : a < succ b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem lt_succ_iff : a < succ b ↔ a ≤ b :=
  lt_succ_iff_of_not_isMax <| not_isMax b
/-
**Order.succ_le_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : SuccOrder α] {a b : α} [
NoMaxOrder α],   Order.succ a ≤ Order.succ b ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_dual] theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := by simp
/-
**Order.succ_lt_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : SuccOrder α] {a b : α} [
NoMaxOrder α],   Order.succ a < Order.succ b ↔ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_dual] theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := by simp

@[to_dual] alias ⟨le_of_succ_le_succ, _⟩ := succ_le_succ_iff
@[to_dual] alias ⟨lt_of_succ_lt_succ, _⟩ := succ_lt_succ_iff

-- TODO: prove for a succ-archimedean non-linear order with bottom
@[to_dual (attr := simp)]
/-
**Order.Iio_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iio_succ (a : α) : Iio (succ a) = Iic a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Iio_succ_of_not_isMax`：Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio
 (succ a) = Iic a
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Iio_succ (a : α) : Iio (succ a) = Iic a :=
  Iio_succ_of_not_isMax <| not_isMax _

@[to_dual (attr := simp) Ioc_pred_left]
/-
**Order.Ico_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ico_succ_right (a b : α) : Ico a (succ b) = Icc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ico_succ_right_of_not_isMax`：Ico_succ_right_of_not_isMax (hb : ¬Is
Max b) : Ico a (succ b) = Icc a b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Ico_succ_right (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_of_not_isMax <| not_isMax _

-- TODO: prove for a succ-archimedean non-linear order
@[to_dual (attr := simp) Ioo_pred_left]
/-
**Order.Ioo_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ioo_succ_right_of_not_isMax`：Ioo_succ_right_of_not_isMax (hb : ¬Is
Max b) : Ioo a (succ b) = Ioc a b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_of_not_isMax <| not_isMax _

@[to_dual (attr := simp)]
/-
**Order.succ_eq_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_eq_succ_iff : succ a = succ b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.succ_eq_succ_iff_of_not_isMax`：succ_eq_succ_iff_of_not_isMax (ha :
 ¬IsMax a) (hb : ¬IsMax b) : succ a = succ b ↔ a = b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem succ_eq_succ_iff : succ a = succ b ↔ a = b :=
  succ_eq_succ_iff_of_not_isMax (not_isMax a) (not_isMax b)

@[to_dual]
/-
**Order.succ_injective** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_injective : Injective (succ : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.succ_eq_succ_iff`：succ_eq_succ_iff : succ a = succ b ↔ a = b
-/
theorem succ_injective : Injective (succ : α → α) := fun _ _ => succ_eq_succ_iff.1

@[to_dual]
/-
**Order.succ_ne_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_ne_succ_iff : succ a != succ b ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Order.succ_injective`：succ_injective : Injective (succ : α -> α)
-/
theorem succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b :=
  succ_injective.ne_iff

@[to_dual]
alias ⟨_, succ_ne_succ⟩ := succ_ne_succ_iff

@[to_dual pred_lt_iff_eq_or_gt]
/-
**Order.lt_succ_iff_eq_or_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
-/
theorem lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ a < b :=
  lt_succ_iff.trans le_iff_eq_or_lt

@[to_dual pred_lt_iff_eq_or_lt]
/-
**Order.lt_succ_iff_eq_or_gt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_iff_eq_or_gt : a < succ b ↔ b = a ∨ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Order.lt_succ_iff_eq_or_lt`：lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ 
a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_succ_iff_eq_or_gt : a < succ b ↔ b = a ∨ a < b := by
  rw [eq_comm, lt_succ_iff_eq_or_lt]

@[to_dual]
/-
**Order.Iio_succ_eq_insert** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iio_succ_eq_insert (a : α) : Iio (succ a) = insert a (Iio a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Iio_succ_eq_insert_of_not_isMax`：Iio_succ_eq_insert_of_not_isMax (
h : ¬IsMax a) : Iio (succ a) = insert a (Iio a)
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Iio_succ_eq_insert (a : α) : Iio (succ a) = insert a (Iio a) :=
  Iio_succ_eq_insert_of_not_isMax <| not_isMax a

@[to_dual Ioc_pred_left_eq_insert]
/-
**Order.Ico_succ_right_eq_insert** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ico_succ_right_eq_insert (h : a <= b) : Ico a (succ b) = insert b (Ico a b
)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ico_succ_right_eq_insert_of_not_isMax`：Ico_succ_right_eq_insert_of
_not_isMax (h₁ : a <= b) (h₂ : ¬IsMax b) : Ico a (succ b) = insert b (Ico a b)
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Ico_succ_right_eq_insert (h : a ≤ b) : Ico a (succ b) = insert b (Ico a b) :=
  Ico_succ_right_eq_insert_of_not_isMax h <| not_isMax b

@[deprecated (since := "2026-04-28")] alias Ico_pred_right_eq_insert := Ioc_pred_left_eq_insert

@[to_dual Ioo_pred_left_eq_insert]
/-
**Order.Ioo_succ_right_eq_insert** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ioo_succ_right_eq_insert (h : a < b) : Ioo a (succ b) = insert b (Ioo a b)
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ioo_succ_right_eq_insert_of_not_isMax`：Ioo_succ_right_eq_insert_of
_not_isMax (h₁ : a < b) (h₂ : ¬IsMax b) : Ioo a (succ b) = insert b (Ioo a b)
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem Ioo_succ_right_eq_insert (h : a < b) : Ioo a (succ b) = insert b (Ioo a b) :=
  Ioo_succ_right_eq_insert_of_not_isMax h <| not_isMax b

@[deprecated (since := "2026-04-28")] alias Ioo_pred_right_eq_insert := Ioo_pred_left_eq_insert

@[to_dual (attr := simp) Ioo_eq_empty_iff_pred_le]
/-
**Order.Ioo_eq_empty_iff_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Ioo_eq_empty_iff_le_succ : Ioo a b = ∅ ↔ b <= succ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.lt_succ_iff_not_isMax`：lt_succ_iff_not_isMax : a < succ a ↔ ¬IsMax
 a
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Order.le_of_lt_succ`：le_of_lt_succ {a b : α} : a < succ b -> a <= b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Order.succ_strictMono`：succ_strictMono : StrictMono (succ : α -> α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
-/
theorem Ioo_eq_empty_iff_le_succ : Ioo a b = ∅ ↔ b ≤ succ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    exact ⟨succ a, lt_succ_iff_not_isMax.mpr (not_isMax a), h⟩
  · ext x
    suffices a < x → b ≤ x by simpa
    exact fun hx ↦ le_of_lt_succ <| lt_of_le_of_lt h <| succ_strictMono hx

end NoMaxOrder

section OrderBot

variable [OrderBot α]

@[to_dual pred_top_lt_iff]
/-
**Order.lt_succ_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_succ_bot_iff [NoMaxOrder α] : a < succ ⊥ ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_succ_bot_iff [NoMaxOrder α] : a < succ ⊥ ↔ a = ⊥ := by rw [lt_succ_iff, le_bot_iff]

@[to_dual pred_top_le_iff]
/-
**Order.le_succ_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_succ_bot_iff : a <= succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.le_succ_iff_eq_or_le`：le_succ_iff_eq_or_le : a <= succ b ↔ a = suc
c b ∨ a <= b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_succ_bot_iff : a ≤ succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥ := by
  rw [le_succ_iff_eq_or_le, le_bot_iff, or_comm]

end OrderBot

end LinearOrder

/-- There is at most one way to define the successors in a `PartialOrder`. -/
@[to_dual
/-- There is at most one way to define the predecessors in a `PartialOrder`. -/]
/-
**Order.** 是 Mathlib 中的一个实例，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder α] : Subsingleton (SuccOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMax a
    · exact (@IsMax.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm
    · exact @CovBy.succ_eq _ _ h₀ _ _ (covBy_succ_of_not_isMax ha)⟩

@[to_dual]
/-
**Order.succ_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_eq_sInf [CompleteLattice α] [SuccOrder α] (a : α) : succ a = sInf (Se
t.Ioi a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_top`：succ_top : succ (⊤ : α) = ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.lt_succ_iff_ne_top`：lt_succ_iff_ne_top : a < succ a ↔ a != ⊤
-/
theorem succ_eq_sInf [CompleteLattice α] [SuccOrder α] (a : α) :
    succ a = sInf (Set.Ioi a) := by
  apply (le_sInf fun b => succ_le_of_lt).antisymm
  obtain rfl | ha := eq_or_ne a ⊤
  · rw [succ_top]
    exact le_top
  · exact sInf_le (lt_succ_iff_ne_top.2 ha)

@[to_dual]
/-
**Order.succ_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_eq_iInf [CompleteLattice α] [SuccOrder α] (a : α) : succ a = ⨅ b > a,
 b
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_sInf`：succ_eq_sInf [CompleteLattice α] [SuccOrder α] (a : 
α) : succ a = sInf (Set.Ioi a)
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.Ioi.eq_1`：∀ {α : Type u_1} [inst : Preorder α] (b : α), Set.Ioi b = 
{x | b < x}
-/
theorem succ_eq_iInf [CompleteLattice α] [SuccOrder α] (a : α) : succ a = ⨅ b > a, b := by
  rw [succ_eq_sInf, iInf_subtype', iInf, Subtype.range_coe_subtype, Ioi]

@[to_dual]
/-
**Order.succ_eq_csInf** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_eq_csInf [ConditionallyCompleteLattice α] [SuccOrder α] [NoMaxOrder α
] (a : α) : succ a = sInf (Set.Ioi a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Set.nonempty_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [NoMaxOrd
er α], (Set.Ioi a).Nonempty
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
-/
theorem succ_eq_csInf [ConditionallyCompleteLattice α] [SuccOrder α] [NoMaxOrder α] (a : α) :
    succ a = sInf (Set.Ioi a) := by
  apply (le_csInf nonempty_Ioi fun b => succ_le_of_lt).antisymm
  exact csInf_le ⟨a, fun b => le_of_lt⟩ <| lt_succ a

section Preorder

variable [Preorder α] [PredOrder α] {a b : α}

-- TODO: auto-generate all of these through `to_dual`

@[to_dual existing]
/-
**Order.isMin_iterate_pred_of_eq_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isMin_iterate_pred_of_eq_of_lt {n m : Nat} (h_eq : pred^[n] a = pred^[m] a
) (h_lt : n < m) : IsMin (pred^[n] a)
参数：h_eq : pred^[n] a = pred^[m] a；h_lt : n < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isMax_iterate_succ_of_eq_of_lt`：isMax_iterate_succ_of_eq_of_lt {n 
m : Nat} (h_eq : succ^[n] a = succ^[m] a) (h_lt : n < m) : IsMax (succ^[n] a)
-/
theorem isMin_iterate_pred_of_eq_of_lt {n m : ℕ} (h_eq : pred^[n] a = pred^[m] a)
    (h_lt : n < m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_lt αᵒᵈ _ _ _ _ _ h_eq h_lt

@[to_dual existing]
/-
**Order.isMin_iterate_pred_of_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isMin_iterate_pred_of_eq_of_ne {n m : Nat} (h_eq : pred^[n] a = pred^[m] a
) (h_ne : n != m) : IsMin (pred^[n] a)
参数：h_eq : pred^[n] a = pred^[m] a；h_ne : n != m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isMax_iterate_succ_of_eq_of_ne`：isMax_iterate_succ_of_eq_of_ne {n 
m : Nat} (h_eq : succ^[n] a = succ^[m] a) (h_ne : n != m) : IsMax (succ^[n] a)
-/
theorem isMin_iterate_pred_of_eq_of_ne {n m : ℕ} (h_eq : pred^[n] a = pred^[m] a)
    (h_ne : n ≠ m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_ne αᵒᵈ _ _ _ _ _ h_eq h_ne

end Preorder

/-! ### Successor-predecessor orders -/

section SuccPredOrder
section Preorder
variable [Preorder α] [SuccOrder α] [PredOrder α] {a b : α}

@[to_dual pred_succ_le]
/-
**Order.le_succ_pred** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：le_succ_pred (a : α) : a <= succ (pred a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.le_succ`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : SuccOrder
 α] {a b : α}, a ⩿ b → b ≤ Order.succ a
· 使用定理 `Order.pred_wcovBy`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOr
der α] (a : α), Order.pred a ⩿ a
-/
lemma le_succ_pred (a : α) : a ≤ succ (pred a) := (pred_wcovBy _).le_succ

@[to_dual le_succ_iff_pred_le]
/-
**Order.pred_le_iff_le_succ** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：pred_le_iff_le_succ : pred a <= b ↔ a <= succ b where mp hab
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Order.le_succ_pred`：le_succ_pred (a : α) : a <= succ (pred a)
· 使用定理 `Order.succ_le_succ`：succ_le_succ (h : a <= b) : succ a <= succ b
· 使用定理 `Order.pred_le_pred`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredO
rder α] {a b : α}, b ≤ a → Order.pred b ≤ Order.pred a
· 使用定理 `Order.pred_succ_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredO
rder α] [inst_2 : SuccOrder α] (a : α),   Order.pred (Order.succ a) ≤ a
-/
lemma pred_le_iff_le_succ : pred a ≤ b ↔ a ≤ succ b where
  mp hab := (le_succ_pred _).trans (succ_le_succ hab)
  mpr hab := (pred_le_pred hab).trans (pred_succ_le _)
/-
**Order.gc_pred_succ** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
形式化陈述：gc_pred_succ : GaloisConnection (pred : α -> α) succ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.pred_le_iff_le_succ`：pred_le_iff_le_succ : pred a <= b ↔ a <= succ
 b where mp hab
-/
lemma gc_pred_succ : GaloisConnection (pred : α → α) succ := fun _ _ ↦ pred_le_iff_le_succ

end Preorder

variable [PartialOrder α] [SuccOrder α] [PredOrder α] {a : α}

@[to_dual (attr := simp)]
/-
**Order.succ_pred_of_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_pred_of_not_isMin (h : ¬IsMin a) : succ (pred a) = a
参数：h : ¬IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a b : α}, a ⋖ b → Order.succ a = b
· 使用定理 `Order.pred_covBy_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] [ins
t_1 : PredOrder α] {a : α}, ¬IsMin a → Order.pred a ⋖ a
-/
theorem succ_pred_of_not_isMin (h : ¬IsMin a) : succ (pred a) = a :=
  CovBy.succ_eq (pred_covBy_of_not_isMin h)

@[to_dual]
/-
**Order.succ_pred** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_pred [NoMinOrder α] (a : α) : succ (pred a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a b : α}, a ⋖ b → Order.succ a = b
· 使用定理 `Order.pred_covBy`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrd
er α] [NoMinOrder α] (a : α), Order.pred a ⋖ a
-/
theorem succ_pred [NoMinOrder α] (a : α) : succ (pred a) = a :=
  CovBy.succ_eq (pred_covBy _)

@[to_dual]
/-
**Order.pred_succ_iterate_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：pred_succ_iterate_of_not_isMax (i : α) (n : Nat) (hin : ¬IsMax (succ^[n - 
1] i)) : pred^[n] (succ^[n] i) = i
参数：i : α；n : Nat；hin : ¬IsMax (succ^[n - 1] i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `Nat.sub_zero`：∀ (n : ℕ), n - 0 = n
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `Order.pred_succ_of_not_isMax`：∀ {α : Type u_1} [inst : PartialOrder α] [
inst_1 : PredOrder α] [inst_2 : SuccOrder α] {a : α},   ¬IsMax a → Order.pred (O
rder.succ a) = a
-/
theorem pred_succ_iterate_of_not_isMax (i : α) (n : ℕ) (hin : ¬IsMax (succ^[n - 1] i)) :
    pred^[n] (succ^[n] i) = i := by
  induction n with
  | zero => simp only [Function.iterate_zero, id]
  | succ n hn =>
    rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hin
    have h_not_max : ¬IsMax (succ^[n - 1] i) := by
      rcases n with - | n
      · simpa using hin
      rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hn ⊢
      have h_sub_le : succ^[n] i ≤ succ^[n.succ] i := by
        rw [Function.iterate_succ']
        exact le_succ _
      refine fun h_max => hin fun j hj => ?_
      have hj_le : j ≤ succ^[n] i := h_max (h_sub_le.trans hj)
      exact hj_le.trans h_sub_le
    rw [Function.iterate_succ, Function.iterate_succ']
    simp only [Function.comp_apply]
    rw [pred_succ_of_not_isMax hin]
    exact hn h_not_max

end SuccPredOrder

end Order

open Order

/-! ### `WithBot`, `WithTop`
Adding a greatest/least element to a `SuccOrder` or to a `PredOrder`.

As far as successors and predecessors are concerned, there are four ways to add a bottom or top
element to an order:
* Adding a `⊤` to an `OrderTop`: Preserves `succ` and `pred`.
* Adding a `⊤` to a `NoMaxOrder`: Preserves `succ`. Never preserves `pred`.
* Adding a `⊥` to an `OrderBot`: Preserves `succ` and `pred`.
* Adding a `⊥` to a `NoMinOrder`: Preserves `pred`. Never preserves `succ`.
  where "preserves `(succ/pred)`" means
  `(Succ/Pred)Order α → (Succ/Pred)Order ((WithTop/WithBot) α)`.
-/

namespace WithTop

section Succ

variable [PartialOrder α] [SuccOrder α] [∀ a : α, Decidable (succ a = a)]

@[to_dual]
/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SuccOrder (WithTop α) where
  succ
    | ⊤ => ⊤
    | Option.some a => ite (succ a = a) ⊤ (some (succ a))
  le_succ a := by
    obtain - | a := a
    · exact le_top
    change _ ≤ ite _ _ _
    split_ifs
    · exact le_top
    · exact coe_le_coe.2 (le_succ a)
  max_of_succ_le {a} ha := by
    cases a
    · exact isMax_top
    dsimp only at ha
    split_ifs at ha with ha'
    · exact (not_top_le_coe _ ha).elim
    · rw [coe_le_coe, succ_le_iff_isMax, ← succ_eq_iff_isMax] at ha
      exact (ha' ha).elim
  succ_le_of_lt {a b} h := by
    cases b
    · exact le_top
    cases a
    · exact (not_top_lt h).elim
    rw [coe_lt_coe] at h
    change ite _ _ _ ≤ _
    split_ifs with ha
    · rw [succ_eq_iff_isMax] at ha
      exact (ha.not_lt h).elim
    · exact coe_le_coe.2 (succ_le_of_lt h)

@[to_dual (attr := simp)]
/-
**WithTop.succ_coe_of_isMax** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：succ_coe_of_isMax {a : α} (h : IsMax a) : succ ↑a = (⊤ : WithTop α)
参数：h : IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
-/
theorem succ_coe_of_isMax {a : α} (h : IsMax a) : succ ↑a = (⊤ : WithTop α) :=
  dif_pos (succ_eq_iff_isMax.2 h)

@[to_dual]
/-
**WithTop.succ_coe_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：succ_coe_of_not_isMax {a : α} (h : ¬ IsMax a) : succ (↑a : WithTop α) = ↑(
succ a)
参数：h : ¬ IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
-/
theorem succ_coe_of_not_isMax {a : α} (h : ¬ IsMax a) : succ (↑a : WithTop α) = ↑(succ a) :=
  dif_neg (succ_eq_iff_isMax.not.2 h)

@[to_dual (attr := simp)]
/-
**WithTop.succ_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：succ_coe [NoMaxOrder α] {a : α} : succ (↑a : WithTop α) = ↑(succ a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.succ_coe_of_not_isMax`：succ_coe_of_not_isMax {a : α} (h : ¬ IsMa
x a) : succ (↑a : WithTop α) = ↑(succ a)
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem succ_coe [NoMaxOrder α] {a : α} : succ (↑a : WithTop α) = ↑(succ a) :=
  succ_coe_of_not_isMax <| not_isMax a

end Succ

section Pred

variable [Preorder α] [OrderTop α] [PredOrder α]

@[to_dual]
/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PredOrder (WithTop α) where
  pred
    | ⊤ => some ⊤
    | Option.some a => some (pred a)
  pred_le a :=
    match a with
    | ⊤ => le_top
    | Option.some a => coe_le_coe.2 (pred_le a)
  min_of_le_pred {a} ha := by
    cases a
    · exact ((coe_lt_top (⊤ : α)).not_ge ha).elim
    · exact (min_of_le_pred <| coe_le_coe.1 ha).withTop
  le_pred_of_lt {a b} h := by
    cases a
    · exact (le_top.not_gt h).elim
    cases b
    · exact coe_le_coe.2 le_top
    exact coe_le_coe.2 (le_pred_of_lt <| coe_lt_coe.1 h)

/-- Not to be confused with `WithTop.pred_bot`, which is about `WithTop.pred`. -/
/-
**WithTop.orderPred_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α], Order.pred ⊤ = ↑⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not to be confused with `WithTop.pred_bot`, which is about `WithTop.pred`.
-/
@[to_dual (attr := simp)] lemma orderPred_top : pred (⊤ : WithTop α) = ↑(⊤ : α) := rfl

/-- Not to be confused with `WithTop.pred_coe`, which is about `WithTop.pred`. -/
/-
**WithTop.orderPred_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α] (a : α),   Order.pred ↑a = ↑(Order.pred a)
参数：a : α；Order.pred a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not to be confused with `WithTop.pred_coe`, which is about `WithTop.pred`.
-/
@[to_dual (attr := simp)] lemma orderPred_coe (a : α) : pred (↑a : WithTop α) = ↑(pred a) := rfl

@[to_dual (attr := simp)]
/-
**WithTop.pred_untop** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α] (a : WithTop α) (ha : a ≠ ⊤),   Order.pred (a.untop ha) = (Order.pred a)
.untop ⋯
参数：a : WithTop α；ha : a ≠ ⊤；a.untop ha；Order.pred a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not to be confused with `WithTop.pred_coe`, which is about `WithTop.pred`.
-/
theorem pred_untop :
    ∀ (a : WithTop α) (ha : a ≠ ⊤),
      pred (a.untop ha) = (pred a).untop (by induction a <;> simp)
  | ⊤, ha => (ha rfl).elim
  | (a : α), _ => rfl

end Pred

section Pred

variable [Preorder α] [NoMaxOrder α]

@[to_dual]
/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hα : Nonempty α] : IsEmpty (PredOrder (WithTop α)) :=
  ⟨by
    intro
    cases h : pred (⊤ : WithTop α) with
    | top => exact hα.elim fun a => (min_of_le_pred h.ge).not_lt <| coe_lt_top a
    | coe a =>
      obtain ⟨c, hc⟩ := exists_gt a
      rw [← coe_lt_coe, ← h] at hc
      exact (le_pred_of_lt (coe_lt_top c)).not_gt hc⟩

end Pred

end WithTop

section OrderIso

variable {X Y : Type*} [Preorder X] [Preorder Y]

-- See note [reducible non-instances]
/-- `SuccOrder` transfers across equivalences between orders. -/
@[to_dual
/-- `PredOrder` transfers across equivalences between orders. -/]
/-
**SuccOrder.ofOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `SuccOrder`。
形式化陈述：{X : Type u_3} → {Y : Type u_4} → [inst : Preorder X] → [inst_1 : Preorder
 Y] → [SuccOrder X] → X ≃o Y → SuccOrder Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev SuccOrder.ofOrderIso [SuccOrder X] (f : X ≃o Y) : SuccOrder Y where
  succ y := f (succ (f.symm y))
  le_succ y := by rw [← map_inv_le_iff f]; exact le_succ (f.symm y)
  max_of_succ_le h := by
    rw [← f.symm.isMax_apply]
    refine max_of_succ_le ?_
    simp [f.le_symm_apply, h]
  succ_le_of_lt h := by rw [← le_map_inv_iff]; exact succ_le_of_lt (by simp [h])

end OrderIso

section OrdConnected

variable {α : Type*} [PartialOrder α] {s : Set α} [s.OrdConnected]

open scoped Classical in
/-
**Set.OrdConnected.predOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.OrdConnected.predOrder [PredOrder α] : PredOrder s where pred x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Set.OrdConnected.predOrder [PredOrder α] : PredOrder s where
  pred x := if h : Order.pred x.1 ∈ s then ⟨Order.pred x.1, h⟩ else x
  pred_le := fun ⟨x, hx⟩ ↦ by dsimp; split <;> simp_all [Order.pred_le]
  min_of_le_pred := @fun ⟨x, hx⟩ h ↦ by
    dsimp at h
    split_ifs at h with h'
    · simp only [Subtype.mk_le_mk, Order.le_pred_iff_isMin] at h
      rintro ⟨y, _⟩ hy
      simp [h hy]
    · rintro ⟨y, hy⟩ h
      rcases h.lt_or_eq with h | h
      · simp only [Subtype.mk_lt_mk] at h
        have := h.le_pred
        absurd h'
        apply out' hy hx
        simp [this, Order.pred_le]
      · simp [h]
  le_pred_of_lt := @fun ⟨b, hb⟩ ⟨c, hc⟩ h ↦ by
    rw [Subtype.mk_lt_mk] at h
    dsimp only
    split
    · exact h.le_pred
    · exact h.le

@[simp, norm_cast]
/-
**coe_pred_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_pred_of_mem [PredOrder α] {a : s} (h : pred a.1 in s) : (pred a).1 = p
red ↑a
参数：h : pred a.1 in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_pred_of_mem [PredOrder α] {a : s} (h : pred a.1 ∈ s) :
    (pred a).1 = pred ↑a := by classical
  change Subtype.val (dite ..) = _
  simp [h]
/-
**isMin_of_pred_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMin_of_pred_notMem [PredOrder α] {a : s} (h : pred ↑a ∉ s) : IsMin a
参数：h : pred ↑a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_iff_isMin`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_
1 : PredOrder α] {a : α}, Order.pred a = a ↔ IsMin a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isMin_of_pred_notMem [PredOrder α] {a : s} (h : pred ↑a ∉ s) : IsMin a := by classical
  rw [← pred_eq_iff_isMin]
  change dite .. = _
  simp [h]
/-
**pred_notMem_iff_isMin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pred_notMem_iff_isMin [PredOrder α] [NoMinOrder α] {a : s} : pred ↑a ∉ s ↔
 IsMin a where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMin_of_pred_notMem`：isMin_of_pred_notMem [PredOrder α] {a : s} (h : pr
ed ↑a ∉ s) : IsMin a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMin.pred_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : PredOr
der α] {a : α}, IsMin a → Order.pred a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `coe_pred_of_mem`：coe_pred_of_mem [PredOrder α] {a : s} (h : pred a.1 in 
s) : (pred a).1 = pred ↑a
-/
lemma pred_notMem_iff_isMin [PredOrder α] [NoMinOrder α] {a : s} :
    pred ↑a ∉ s ↔ IsMin a where
  mp := isMin_of_pred_notMem
  mpr h nh := by
    replace h := congr($h.pred_eq.1)
    rw [coe_pred_of_mem nh] at h
    simp at h
/-
**Set.OrdConnected.succOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.OrdConnected.succOrder [SuccOrder α] : SuccOrder s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Set.OrdConnected.succOrder [SuccOrder α] :
    SuccOrder s :=
  letI : PredOrder sᵒᵈ := inferInstanceAs (PredOrder (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (SuccOrder sᵒᵈᵒᵈ)

set_option backward.isDefEq.respectTransparency false in
@[simp, norm_cast]
/-
**coe_succ_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_succ_of_mem [SuccOrder α] {a : s} (h : succ ↑a in s) : (succ a).1 = su
cc ↑a
参数：h : succ ↑a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma coe_succ_of_mem [SuccOrder α] {a : s} (h : succ ↑a ∈ s) :
    (succ a).1 = succ ↑a := by classical
  change Subtype.val (dite ..) = _
  split_ifs <;> trivial

set_option backward.isDefEq.respectTransparency false in
/-
**isMax_of_succ_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMax_of_succ_notMem [SuccOrder α] {a : s} (h : succ ↑a ∉ s) : IsMax a
参数：h : succ ↑a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma isMax_of_succ_notMem [SuccOrder α] {a : s} (h : succ ↑a ∉ s) : IsMax a := by
  classical
  rw [← succ_eq_iff_isMax]
  change dite .. = _
  split_ifs <;> trivial
/-
**succ_notMem_iff_isMax** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：succ_notMem_iff_isMax [SuccOrder α] [NoMaxOrder α] {a : s} : succ ↑a ∉ s ↔
 IsMax a where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMax_of_succ_notMem`：isMax_of_succ_notMem [SuccOrder α] {a : s} (h : su
cc ↑a ∉ s) : IsMax a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMax.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a : α}, IsMax a → Order.succ a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `coe_succ_of_mem`：coe_succ_of_mem [SuccOrder α] {a : s} (h : succ ↑a in s
) : (succ a).1 = succ ↑a
-/
lemma succ_notMem_iff_isMax [SuccOrder α] [NoMaxOrder α] {a : s} :
    succ ↑a ∉ s ↔ IsMax a where
  mp := isMax_of_succ_notMem
  mpr h nh := by
    replace h := congr($h.succ_eq.1)
    rw [coe_succ_of_mem nh] at h
    simp at h

end OrdConnected

