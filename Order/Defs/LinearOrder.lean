/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Batteries.Classes.Order
public import Batteries.Tactic.Trans
public import Mathlib.Data.Ordering.Basic
public import Mathlib.Tactic.ExtendDoc
public import Mathlib.Tactic.Push.Attr
public import Mathlib.Tactic.Simps.Basic
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Order.Defs.PartialOrder

/-!
# Orders

Defines classes for linear orders and proves some basic lemmas about them.

We intentionally avoid using `grind` in this fundamental file to keep the proofs understandable,
rather than hiding the reasoning behind automation.
-/

@[expose] public section

variable {α : Type*}

section LinearOrder

/-!
### Definition of `LinearOrder` and lemmas about types with a linear order
-/

/-- Default definition of `max`. -/
/-
**maxDefault** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：maxDefault [LE α] [DecidableLE α] (a b : α)
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Default definition of `max`.
-/
def maxDefault [LE α] [DecidableLE α] (a b : α) :=
  if a ≤ b then b else a

/-- Default definition of `min`. -/
/-
**minDefault** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：minDefault [LE α] [DecidableLE α] (a b : α)
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Default definition of `min`.
-/
def minDefault [LE α] [DecidableLE α] (a b : α) :=
  if a ≤ b then a else b

/-- This attempts to prove that a given instance of `compare` is equal to `compareOfLessAndEq` by
introducing the arguments and trying the following approaches in order:

1. seeing if `rfl` works
2. seeing if the `compare` at hand is nonetheless essentially `compareOfLessAndEq`, but, because of
   implicit arguments, requires us to unfold the defs and split the `if`s in the definition of
   `compareOfLessAndEq`
3. seeing if we can split by cases on the arguments, then see if the defs work themselves out
   (useful when `compare` is defined via a `match` statement, as it is for `Bool`)
-/
macro "compareOfLessAndEq_rfl" : tactic =>
  `(tactic| (intro a b; first | rfl |
    (simp only [compare, compareOfLessAndEq]; split_ifs <;> rfl) |
    (induction a <;> induction b <;> simp +decide only)))

/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
/-
**LinearOrder** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：LinearOrder (α : Type*) extends PartialOrder α, Min α, Max α, Ord α where 
/-- A linear order is total. -/ protected le_total (a b : α) : a <= b ∨ b <= a /
-- In a linearly ordered type, we assume the order relations are all decidable. 
-/ toDecidableLE : DecidableLE α /-- In a linearly ordered type, we assume the o
rder relations are all decidable. -/ toDecidableEq : DecidableEq α
参数：α : Type*；a b : α。
继承自：PartialOrder α, Min α, Max α, Ord α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`.
-/
class LinearOrder (α : Type*) extends PartialOrder α, Min α, Max α, Ord α where
  /-- A linear order is total. -/
  protected le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  /-- The minimum function is equivalent to the one you get from `minOfLe`. -/
  protected min_def : ∀ a b, min a b = if a ≤ b then a else b := by intros; rfl
  /-- The minimum function is equivalent to the one you get from `maxOfLe`. -/
  protected max_def : ∀ a b, max a b = if a ≤ b then b else a := by intros; rfl
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

attribute [to_dual existing] LinearOrder.toMax

variable [LinearOrder α] {a b c : α}

attribute [instance_reducible, instance 900] LinearOrder.toDecidableLT
attribute [instance_reducible, instance 900] LinearOrder.toDecidableLE
attribute [instance_reducible, instance 900] LinearOrder.toDecidableEq
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.IsLinearOrder α where
  le_total := LinearOrder.le_total
/-
**le_total** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤ a
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrder.le_total`：∀ {α : Type u_2} [self : LinearOrder α] (a b : α),
 a ≤ b ∨ b ≤ a
-/
@[to_dual self] lemma le_total : ∀ a b : α, a ≤ b ∨ b ≤ a := LinearOrder.le_total
/-
**le_of_not_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b → b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
-/
@[to_dual self] lemma le_of_not_ge : ¬a ≤ b → b ≤ a := (le_total a b).resolve_left
/-
**lt_of_not_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a → a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
@[to_dual self] lemma lt_of_not_ge (h : ¬b ≤ a) : a < b := lt_of_le_not_ge (le_of_not_ge h) h
/-
**lt_or_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤ a
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
@[to_dual self] lemma lt_or_ge (a b : α) : a < b ∨ b ≤ a :=
  if hba : b ≤ a then Or.inr hba else Or.inl <| lt_of_not_ge hba
/-
**le_or_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b < a
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
-/
@[to_dual self] lemma le_or_gt (a b : α) : a ≤ b ∨ b < a := (lt_or_ge b a).symm

@[to_dual gt_trichotomy]
/-
**lt_trichotomy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Decidable.lt_or_eq_of_le'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b
 : α} [DecidableLE α], b ≤ a → b < a ∨ a = b
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
-/
lemma lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a :=
  (lt_or_ge a b).imp_right (fun h ↦ (Decidable.lt_or_eq_of_le' h).symm)

@[to_dual self]
/-
**le_of_not_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_of_not_gt (h : ¬b < a) : a <= b
参数：h : ¬b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
-/
lemma le_of_not_gt (h : ¬b < a) : a ≤ b := (le_or_gt a b).resolve_right h

@[to_dual gt_or_lt_of_ne]
/-
**lt_or_gt_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
参数：h : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
-/
lemma lt_or_gt_of_ne (h : a ≠ b) : a < b ∨ b < a :=
  (lt_trichotomy a b).imp_right (fun h' ↦ h'.resolve_left h)

@[to_dual ne_iff_gt_or_lt]
/-
**ne_iff_lt_or_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ne_iff_lt_or_gt : a != b ↔ a < b ∨ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma ne_iff_lt_or_gt : a ≠ b ↔ a < b ∨ b < a := ⟨lt_or_gt_of_ne, (Or.elim · ne_of_lt ne_of_gt)⟩
/-
**lt_iff_not_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b ↔ ¬b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
@[to_dual self] lemma lt_iff_not_ge : a < b ↔ ¬b ≤ a := ⟨not_le_of_gt, lt_of_not_ge⟩
/-
**not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
@[simp, push, to_dual self] lemma not_lt : ¬a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩
/-
**not_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
-/
@[simp, push, to_dual self] lemma not_le : ¬a ≤ b ↔ b < a := lt_iff_not_ge.symm

@[to_dual eq_or_lt_of_not_gt]
/-
**eq_or_gt_of_not_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_or_gt_of_not_lt (h : ¬a < b) : a = b ∨ b < a
参数：h : ¬a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
-/
lemma eq_or_gt_of_not_lt (h : ¬a < b) : a = b ∨ b < a :=
  if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))

@[to_dual self]
/-
**le_imp_le_of_lt_imp_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_imp_le_of_lt_imp_lt {α β} [Preorder α] [LinearOrder β] {a b : α} {c d :
 β} (H : d < c -> b < a) (h : a <= b) : c <= d
参数：H : d < c -> b < a；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem le_imp_le_of_lt_imp_lt {α β} [Preorder α] [LinearOrder β] {a b : α} {c d : β}
    (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
  le_of_not_gt fun h' => not_le_of_gt (H h') h

@[grind =]
/-
**min_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_def (a b : α) : min a b = if a <= b then a else b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrder.min_def`：∀ {α : Type u_2} [self : LinearOrder α] (a b : α), 
min a b = if a ≤ b then a else b
-/
lemma min_def (a b : α) : min a b = if a ≤ b then a else b := LinearOrder.min_def a b
@[grind =]
/-
**max_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：max_def (a b : α) : max a b = if a <= b then b else a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrder.max_def`：∀ {α : Type u_2} [self : LinearOrder α] (a b : α), 
max a b = if a ≤ b then b else a
-/
lemma max_def (a b : α) : max a b = if a ≤ b then b else a := LinearOrder.max_def a b
/-
**min_ind** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_ind {motive : α -> Prop} (ha : a <= b -> motive a) (hb : b <= a -> mot
ive b) : motive (min a b)
参数：ha : a <= b -> motive a；hb : b <= a -> motive b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_def`：min_def (a b : α) : min a b = if a <= b then a else b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem min_ind {motive : α → Prop} (ha : a ≤ b → motive a) (hb : b ≤ a → motive b) :
    motive (min a b) := by
  rw [min_def]; split_ifs with h
  exacts [ha h, hb (le_of_not_ge h)]

@[to_dual existing (attr := elab_as_elim)]
/-
**max_ind** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_ind {motive : α -> Prop} (ha : b <= a -> motive a) (hb : a <= b -> mot
ive b) : motive (max a b)
参数：ha : b <= a -> motive a；hb : a <= b -> motive b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `max_def`：max_def (a b : α) : max a b = if a <= b then b else a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem max_ind {motive : α → Prop} (ha : b ≤ a → motive a) (hb : a ≤ b → motive b) :
    motive (max a b) := by
  rw [max_def]; split_ifs with h
  exacts [hb h, ha (le_of_not_ge h)]

@[to_dual existing max_def]
/-
**min_def'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_def' (a b : α) : min a b = if b <= a then b else a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_def`：min_def (a b : α) : min a b = if a <= b then a else b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `instIsPreorder_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.IsPreo
rder α
-/
theorem min_def' (a b : α) : min a b = if b ≤ a then b else a := by
  obtain h | h | h := lt_trichotomy a b <;> simp [le_of_lt, not_le_of_gt, h, min_def]

@[to_dual existing min_def]
/-
**max_def'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_def' (a b : α) : max a b = if b <= a then a else b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `max_def`：max_def (a b : α) : max a b = if a <= b then b else a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `instIsPreorder_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.IsPreo
rder α
-/
theorem max_def' (a b : α) : max a b = if b ≤ a then a else b := by
  obtain h | h | h := lt_trichotomy a b <;> simp [le_of_lt, not_le_of_gt, h, max_def]

@[to_dual le_max_left]
/-
**min_le_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_le_left (a b : α) : min a b <= a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_def`：min_def (a b : α) : min a b = if a <= b then a else b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `instIsPreorder_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.IsPreo
rder α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma min_le_left (a b : α) : min a b ≤ a := by
  rw [min_def]
  split_ifs with h <;> simp [h, le_of_not_ge]

@[to_dual le_max_right]
/-
**min_le_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_le_right (a b : α) : min a b <= b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_def`：min_def (a b : α) : min a b = if a <= b then a else b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `instIsPreorder_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.IsPreo
rder α
-/
lemma min_le_right (a b : α) : min a b ≤ b := by
  rw [min_def]
  split_ifs with h <;> simp [h]

@[to_dual max_le]
/-
**le_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
参数：h₁ : c <= a；h₂ : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_def`：min_def (a b : α) : min a b = if a <= b then a else b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma le_min (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b := by
  rw [min_def]
  split_ifs <;> assumption

@[to_dual]
/-
**eq_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_min (h₁ : c <= a) (h₂ : c <= b) (h₃ : forall {d}, d <= a -> d <= b -> d
 <= c) : c = min a b
参数：h₁ : c <= a；h₂ : c <= b；h₃ : forall {d}, d <= a -> d <= b -> d <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
lemma eq_min (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀ {d}, d ≤ a → d ≤ b → d ≤ c) : c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

@[to_dual]
/-
**min_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_comm (a b : α) : min a b = min b a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_min`：eq_min (h₁ : c <= a) (h₂ : c <= b) (h₃ : forall {d}, d <= a -> d
 <= b -> d <= c) : c = min a b
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
-/
lemma min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) fun h₁ h₂ => le_min h₂ h₁

@[to_dual]
/-
**min_assoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_assoc (a b c : α) : min (min a b) c = min a (min b c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_min`：eq_min (h₁ : c <= a) (h₂ : c <= b) (h₃ : forall {d}, d <= a -> d
 <= b -> d <= c) : c = min a b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
lemma min_assoc (a b c : α) : min (min a b) c = min a (min b c) :=
  eq_min
    (le_trans (min_le_left ..) (min_le_left ..))
    (le_min (le_trans (min_le_left ..) (min_le_right ..)) (min_le_right ..))
    (fun h₁ h₂ ↦
      le_min (le_min h₁ (le_trans h₂ (min_le_left ..))) (le_trans h₂ (min_le_right ..)))

@[to_dual]
/-
**min_left_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_left_comm (a b c : α) : min a (min b c) = min b (min a c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `min_assoc`：min_assoc (a b c : α) : min (min a b) c = min a (min b c)
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
-/
lemma min_left_comm (a b c : α) : min a (min b c) = min b (min a c) := by
  rw [← min_assoc, min_comm a, min_assoc]
/-
**min_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_def`：min_def (a b : α) : min a b = if a <= b then a else b
· 使用定理 `ite_id`：∀ {c : Prop} [inst : Decidable c] {α : Sort u_1} (t : α), (if c 
then t else t) = t
-/
@[to_dual (attr := simp)] lemma min_self (a : α) : min a a = a := by rw [min_def, ite_id]

@[to_dual]
/-
**min_eq_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_eq_left (h : a <= b) : min a b = a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `eq_min`：eq_min (h₁ : c <= a) (h₂ : c <= b) (h₃ : forall {d}, d <= a -> d
 <= b -> d <= c) : c = min a b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma min_eq_left (h : a ≤ b) : min a b = a := (eq_min le_rfl h (fun h _ ↦ h)).symm

@[to_dual]
/-
**min_eq_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_eq_right (h : b <= a) : min a b = b
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
-/
lemma min_eq_right (h : b ≤ a) : min a b = b := min_comm b a ▸ min_eq_left h
/-
**min_eq_left_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b → min a b = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[to_dual] lemma min_eq_left_of_lt (h : a < b) : min a b = a := min_eq_left (le_of_lt h)
/-
**min_eq_right_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b < a → min a b = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[to_dual] lemma min_eq_right_of_lt (h : b < a) : min a b = b := min_eq_right (le_of_lt h)

@[to_dual max_lt]
/-
**lt_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
参数：h₁ : a < b；h₂ : a < c。
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
lemma lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c := by
  cases le_total b c <;> simp [min_eq_left, min_eq_right, *]

section Ord

/-
**compare_lt_iff_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compare_lt_iff_lt : compare a b = .lt ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_2} [self : Line
arOrder α] (a b : α), compare a b = compareOfLessAndEq a b
· 使用定理 `compareOfLessAndEq_eq_lt`：∀ {α : Type u} [inst : LT α] [LE α] [inst_2 : 
DecidableLT α] [inst_3 : DecidableEq α] {x y : α},   compareOfLessAndEq x y = Or
dering.lt ↔ x …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma compare_lt_iff_lt : compare a b = .lt ↔ a < b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq_eq_lt]
/-
**compare_eq_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compare_eq_iff_eq : compare a b = .eq ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_2} [self : Line
arOrder α] (a b : α), compare a b = compareOfLessAndEq a b
· 使用定理 `compareOfLessAndEq_eq_eq`：∀ {α : Type u} [inst : LT α] [inst_1 : LE α] [
inst_2 : DecidableLT α] [DecidableLE α] [inst_4 : DecidableEq α],   (∀ (x : α), 
x ≤ x) → (∀ {x…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma compare_eq_iff_eq : compare a b = .eq ↔ a = b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq_eq_eq le_refl not_le]
/-
**compare_gt_iff_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compare_gt_iff_gt : compare a b = .gt ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_2} [self : Line
arOrder α] (a b : α), compare a b = compareOfLessAndEq a b
· 使用定理 `compareOfLessAndEq_eq_gt`：∀ {α : Type u} [inst : LT α] [inst_1 : LE α] [
inst_2 : DecidableLT α] [inst_3 : DecidableEq α],   (∀ {x y : α}, x ≤ y → y ≤ x 
→ x = y) →    …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma compare_gt_iff_gt : compare a b = .gt ↔ b < a := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq,
    compareOfLessAndEq_eq_gt le_antisymm le_total not_le]
/-
**compare_le_iff_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compare_le_iff_le : compare a b != .gt ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `compare_lt_iff_lt`：compare_lt_iff_lt : compare a b = .lt ↔ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `compare_eq_iff_eq`：compare_eq_iff_eq : compare a b = .eq ↔ a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用引理 `compare_gt_iff_gt`：compare_gt_iff_gt : compare a b = .gt ↔ b < a
-/
lemma compare_le_iff_le : compare a b ≠ .gt ↔ a ≤ b := by
  cases h : compare a b
  · simpa using le_of_lt <| compare_lt_iff_lt.1 h
  · simpa using le_of_eq <| compare_eq_iff_eq.1 h
  · simpa using compare_gt_iff_gt.1 h
/-
**compare_ge_iff_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compare_ge_iff_ge : compare a b != .lt ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `compare_lt_iff_lt`：compare_lt_iff_lt : compare a b = .lt ↔ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `compare_eq_iff_eq`：compare_eq_iff_eq : compare a b = .eq ↔ a = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `compare_gt_iff_gt`：compare_gt_iff_gt : compare a b = .gt ↔ b < a
-/
lemma compare_ge_iff_ge : compare a b ≠ .lt ↔ b ≤ a := by
  cases h : compare a b
  · simpa using compare_lt_iff_lt.1 h
  · simpa using le_of_eq <| (·.symm) <| compare_eq_iff_eq.1 h
  · simpa using le_of_lt <| compare_gt_iff_gt.1 h
/-
**compare_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compare_iff (a b : α) {o : Ordering} : compare a b = o ↔ o.Compares a b
参数：a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `compare_lt_iff_lt`：compare_lt_iff_lt : compare a b = .lt ↔ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `compare_eq_iff_eq`：compare_eq_iff_eq : compare a b = .eq ↔ a = b
· 使用引理 `compare_gt_iff_gt`：compare_gt_iff_gt : compare a b = .gt ↔ b < a
-/
lemma compare_iff (a b : α) {o : Ordering} : compare a b = o ↔ o.Compares a b := by
  cases o <;> simp only [Ordering.Compares]
  · exact compare_lt_iff_lt
  · exact compare_eq_iff_eq
  · exact compare_gt_iff_gt
/-
**cmp_eq_compare** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_eq_compare (a b : α) : cmp a b = compare a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `compare_iff`：compare_iff (a b : α) {o : Ordering} : compare a b = o ↔ o.
Compares a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem cmp_eq_compare (a b : α) : cmp a b = compare a b := by
  refine ((compare_iff ..).2 ?_).symm
  unfold cmp cmpUsing; split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)
/-
**cmp_eq_compareOfLessAndEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_eq_compareOfLessAndEq (a b : α) : cmp a b = compareOfLessAndEq a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `cmp_eq_compare`：cmp_eq_compare (a b : α) : cmp a b = compare a b
· 使用定理 `LinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_2} [self : Line
arOrder α] (a b : α), compare a b = compareOfLessAndEq a b
-/
theorem cmp_eq_compareOfLessAndEq (a b : α) : cmp a b = compareOfLessAndEq a b :=
  (cmp_eq_compare ..).trans (LinearOrder.compare_eq_compareOfLessAndEq ..)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.LawfulBCmp (compare (α := α)) where
  eq_swap {a b} := by
    cases _ : compare b a <;>
      simp_all [Ordering.swap, compare_eq_iff_eq, compare_lt_iff_lt, compare_gt_iff_gt]
  isLE_trans h₁ h₂ := by
    simp only [← Ordering.ne_gt_iff_isLE, compare_le_iff_le] at *
    exact le_trans h₁ h₂
  compare_eq_iff_beq := by simp [compare_eq_iff_eq]
  eq_lt_iff_lt := by simp [compare_lt_iff_lt]
  isLE_iff_le := by simp [← Ordering.ne_gt_iff_isLE, compare_le_iff_le]

end Ord

/-- The category of linear orders.

This will get reused to define `OrderType`. -/
/-
**LinOrd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_2 + 1)
参数：u_2 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of linear orders.

This will get reused to define `OrderType`.
-/
structure LinOrd where
  /-- Construct a bundled `LinOrd` from the underlying type and typeclass. -/
  of ::
  /-- The underlying linearly ordered type. -/
  (carrier : Type*)
  [str : LinearOrder carrier]

attribute [instance] LinOrd.str

initialize_simps_projections LinOrd (carrier → coe, -str)

namespace LinOrd

/-
**LinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `LinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort LinOrd (Type _) :=
  ⟨LinOrd.carrier⟩

attribute [coe] LinOrd.carrier

end LinOrd

end LinearOrder

