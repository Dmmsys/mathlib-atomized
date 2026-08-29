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

/--
Definition of `maxDefault` / `maxDefault` 的定义

English:
definition maxDefault
  signature: [LE α] [DecidableLE α] (a b : α)
  body: if a <= b then b else a

中文:
定义 maxDefault
  签名: [LE α] [DecidableLE α] (a b : α)
  定义体: if a <= b then b else a
-/
def maxDefault [LE α] [DecidableLE α] (a b : α) :=
  if a <= b then b else a

/--
Definition of `minDefault` / `minDefault` 的定义

English:
definition minDefault
  signature: [LE α] [DecidableLE α] (a b : α)
  body: if a <= b then a else b

中文:
定义 minDefault
  签名: [LE α] [DecidableLE α] (a b : α)
  定义体: if a <= b then a else b
-/
def minDefault [LE α] [DecidableLE α] (a b : α) :=
  if a <= b then a else b

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

/--
Definition of `LinearOrder` / `LinearOrder` 的定义

English:
class LinearOrder
  parameters: (α : Type*)
  extends: PartialOrder α, Min α, Max α, Ord α
  axioms and operations (10):
    - le_total((a b : α)) : a <= b ∨ b <= a
    - toDecidableLE : DecidableLE α
    - toDecidableEq : DecidableEq α  [default: @decidableEqOfDecidableLE _ _ toDecidableLE]
    - toDecidableLT : DecidableLT α  [default: @decidableLTOfDecidableLE _ _ toDecidableLE]
    - min : = fun a b => if a <= b then a else b
    - max : = fun a b => if a <= b then b else a
    - min_def : forall a b, min a b = if a <= b then a else b  [default: by intros; rfl]
    - max_def : forall a b, max a b = if a <= b then b else a  [default: by intros; rfl]
    - compare(a b) : = compareOfLessAndEq a b
    - compare_eq_compareOfLessAndEq : forall a b, compare a b = compareOfLessAndEq a b  [default: by compareOfLessAndEq_rfl]

中文:
类 线性序
  参数: (α : 类型)
  继承: 偏序 α, 最小值 α, 最大值 α, 序 α
  公理与运算 (10 个):
    - le_total((a b : α)) : a <= b ∨ b <= a
    - toDecidableLE : DecidableLE α
    - toDecidableEq : DecidableEq α  [默认: @decidableEqOfDecidableLE _ _ toDecidableLE]
    - toDecidableLT : DecidableLT α  [默认: @decidableLTOfDecidableLE _ _ toDecidableLE]
    - min : = fun a b => if a <= b then a else b
    - max : = fun a b => if a <= b then b else a
    - min_def : 对任意 a b, 最小值 a b = if a <= b then a else b  [默认: by intros; rfl]
    - max_def : 对任意 a b, 最大值 a b = if a <= b then b else a  [默认: by intros; rfl]
    - compare(a b) : = compareOfLessAndEq a b
    - compare_eq_compareOfLessAndEq : 对任意 a b, compare a b = compareOfLessAndEq a b  [默认: by compareOfLessAndEq_rfl]

Depends on / 依赖: decidableEqOfDecidableLE, toDecidableLE
-/
class LinearOrder (α : Type*) extends PartialOrder α, Min α, Max α, Ord α where
  /-- A linear order is total. -/
  protected le_total (a b : α) : a <= b ∨ b <= a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  min := fun a b => if a <= b then a else b
  max := fun a b => if a <= b then b else a
  /-- The minimum function is equivalent to the one you get from `minOfLe`. -/
  protected min_def : forall a b, min a b = if a <= b then a else b := by intros; rfl
  /-- The minimum function is equivalent to the one you get from `maxOfLe`. -/
  protected max_def : forall a b, max a b = if a <= b then b else a := by intros; rfl
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : forall a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

attribute [to_dual existing] LinearOrder.toMax

variable [LinearOrder α] {a b c : α}

attribute [instance_reducible, instance 900] LinearOrder.toDecidableLT
attribute [instance_reducible, instance 900] LinearOrder.toDecidableLE
attribute [instance_reducible, instance 900] LinearOrder.toDecidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.IsLinearOrder α
  body: LinearOrder.le_total

中文:
实例 :
  签名: Std.是线性序 α
  定义体: LinearOrder.le_total

Depends on / 依赖: LinearOrder, LinearOrder.le_total, le_total
-/
instance : Std.IsLinearOrder α where
  le_total := LinearOrder.le_total

/--
lemma `le_total` / 引理 `le_total`

English:
lemma le_total
  statement: forall a b : α, a <= b ∨ b <= a
  proof: LinearOrder.le_total

中文:
引理 le_total
  结论: 对任意 a b : α, a <= b ∨ b <= a
  证明: LinearOrder.le_total
-/
@[to_dual self] lemma le_total : forall a b : α, a <= b ∨ b <= a := LinearOrder.le_total

/--
lemma `le_of_not_ge` / 引理 `le_of_not_ge`

English:
lemma le_of_not_ge
  statement: ¬a <= b -> b <= a
  proof: (le_total a b).resolve_left

中文:
引理 le_of_not_ge
  结论: ¬a <= b -> b <= a
  证明: (le_total a b).resolve_left
-/
@[to_dual self] lemma le_of_not_ge : ¬a <= b -> b <= a := (le_total a b).resolve_left
/--
lemma `lt_of_not_ge` / 引理 `lt_of_not_ge`

English:
lemma lt_of_not_ge
  given: (h : ¬b <= a)
  statement: a < b
  proof: lt_of_le_not_ge (le_of_not_ge h) h

中文:
引理 lt_of_not_ge
  条件: (h : ¬b <= a)
  结论: a < b
  证明: lt_of_le_not_ge (le_of_not_ge h) h
-/
@[to_dual self] lemma lt_of_not_ge (h : ¬b <= a) : a < b := lt_of_le_not_ge (le_of_not_ge h) h

/--
lemma `lt_or_ge` / 引理 `lt_or_ge`

English:
lemma lt_or_ge
  given: (a b : α)
  statement: a < b ∨ b <= a
  proof: if hba : b <= a then Or.inr hba else Or.inl lt_of_not_ge hba

中文:
引理 lt_or_ge
  条件: (a b : α)
  结论: a < b ∨ b <= a
  证明: if hba : b <= a then Or.inr hba else Or.inl lt_of_not_ge hba
-/
@[to_dual self] lemma lt_or_ge (a b : α) : a < b ∨ b <= a :=
if hba : b <= a then Or.inr hba else Or.inl lt_of_not_ge hba

/--
lemma `le_or_gt` / 引理 `le_or_gt`

English:
lemma le_or_gt
  given: (a b : α)
  statement: a <= b ∨ b < a
  proof: (lt_or_ge b a).symm

@[to_dual gt_trichotomy]

中文:
引理 le_or_gt
  条件: (a b : α)
  结论: a <= b ∨ b < a
  证明: (lt_or_ge b a).symm

@[to_dual gt_trichotomy]
-/
@[to_dual self] lemma le_or_gt (a b : α) : a <= b ∨ b < a := (lt_or_ge b a).symm

@[to_dual gt_trichotomy]
/--
lemma `lt_trichotomy` / 引理 `lt_trichotomy`

English:
lemma lt_trichotomy
  given: (a b : α)
  statement: a < b ∨ a = b ∨ b < a
  proof: (lt_or_ge a b).imp_right (fun h => (Decidable.lt_or_eq_of_le' h).symm)

@[to_dual self]

中文:
引理 lt_trichotomy
  条件: (a b : α)
  结论: a < b ∨ a = b ∨ b < a
  证明: (lt_or_ge a b).imp_right (fun h => (Decidable.lt_or_eq_of_le' h).symm)

@[to_dual self]

Depends on / 依赖: Decidable, Decidable.lt_or_eq_of_le, imp_right, lt_or_eq_of_le, lt_or_ge
-/
lemma lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a :=
  (lt_or_ge a b).imp_right (fun h => (Decidable.lt_or_eq_of_le' h).symm)

@[to_dual self]
/--
lemma `le_of_not_gt` / 引理 `le_of_not_gt`

English:
lemma le_of_not_gt
  given: (h : ¬b < a)
  statement: a <= b
  proof: (le_or_gt a b).resolve_right h

@[to_dual gt_or_lt_of_ne]

中文:
引理 le_of_not_gt
  条件: (h : ¬b < a)
  结论: a <= b
  证明: (le_or_gt a b).resolve_right h

@[to_dual gt_or_lt_of_ne]

Depends on / 依赖: le_or_gt, resolve_right
-/
lemma le_of_not_gt (h : ¬b < a) : a <= b := (le_or_gt a b).resolve_right h

@[to_dual gt_or_lt_of_ne]
/--
lemma `lt_or_gt_of_ne` / 引理 `lt_or_gt_of_ne`

English:
lemma lt_or_gt_of_ne
  given: (h : a != b)
  statement: a < b ∨ b < a
  proof: (lt_trichotomy a b).imp_right (fun h' => h'.resolve_left h)

@[to_dual ne_iff_gt_or_lt]

中文:
引理 lt_or_gt_of_ne
  条件: (h : a != b)
  结论: a < b ∨ b < a
  证明: (lt_trichotomy a b).imp_right (fun h' => h'.resolve_left h)

@[to_dual ne_iff_gt_or_lt]

Depends on / 依赖: imp_right, lt_trichotomy, resolve_left
-/
lemma lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a :=
  (lt_trichotomy a b).imp_right (fun h' => h'.resolve_left h)

@[to_dual ne_iff_gt_or_lt]
/--
lemma `ne_iff_lt_or_gt` / 引理 `ne_iff_lt_or_gt`

English:
lemma ne_iff_lt_or_gt
  statement: a != b ↔ a < b ∨ b < a
  proof: ⟨lt_or_gt_of_ne, (Or.elim · ne_of_lt ne_of_gt)⟩

中文:
引理 ne_iff_lt_or_gt
  结论: a != b ↔ a < b ∨ b < a
  证明: ⟨lt_or_gt_of_ne, (Or.elim · ne_of_lt ne_of_gt)⟩

Depends on / 依赖: Or.elim, lt_or_gt_of_ne, ne_of_gt, ne_of_lt
-/
lemma ne_iff_lt_or_gt : a != b ↔ a < b ∨ b < a := ⟨lt_or_gt_of_ne, (Or.elim · ne_of_lt ne_of_gt)⟩

/--
lemma `lt_iff_not_ge` / 引理 `lt_iff_not_ge`

English:
lemma lt_iff_not_ge
  statement: a < b ↔ ¬b <= a
  proof: ⟨not_le_of_gt, lt_of_not_ge⟩

中文:
引理 lt_iff_not_ge
  结论: a < b ↔ ¬b <= a
  证明: ⟨not_le_of_gt, lt_of_not_ge⟩
-/
@[to_dual self] lemma lt_iff_not_ge : a < b ↔ ¬b <= a := ⟨not_le_of_gt, lt_of_not_ge⟩

/--
lemma `not_lt` / 引理 `not_lt`

English:
lemma not_lt
  statement: ¬a < b ↔ b <= a
  proof: ⟨le_of_not_gt, not_lt_of_ge⟩

中文:
引理 not_lt
  结论: ¬a < b ↔ b <= a
  证明: ⟨le_of_not_gt, not_lt_of_ge⟩
-/
@[simp, push, to_dual self] lemma not_lt : ¬a < b ↔ b <= a := ⟨le_of_not_gt, not_lt_of_ge⟩
/--
lemma `not_le` / 引理 `not_le`

English:
lemma not_le
  statement: ¬a <= b ↔ b < a
  proof: lt_iff_not_ge.symm

@[to_dual eq_or_lt_of_not_gt]

中文:
引理 not_le
  结论: ¬a <= b ↔ b < a
  证明: lt_iff_not_ge.symm

@[to_dual eq_or_lt_of_not_gt]
-/
@[simp, push, to_dual self] lemma not_le : ¬a <= b ↔ b < a := lt_iff_not_ge.symm

@[to_dual eq_or_lt_of_not_gt]
/--
lemma `eq_or_gt_of_not_lt` / 引理 `eq_or_gt_of_not_lt`

English:
lemma eq_or_gt_of_not_lt
  given: (h : ¬a < b)
  statement: a = b ∨ b < a
  proof: if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))

@[to_dual self]

中文:
引理 eq_or_gt_of_not_lt
  条件: (h : ¬a < b)
  结论: a = b ∨ b < a
  证明: if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))

@[to_dual self]

Depends on / 依赖: Or.inl, Or.inr, lt_of_le_of_ne, lt_of_not_ge
-/
lemma eq_or_gt_of_not_lt (h : ¬a < b) : a = b ∨ b < a :=
  if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))

@[to_dual self]
/--
theorem `le_imp_le_of_lt_imp_lt` / 定理 `le_imp_le_of_lt_imp_lt`

English:
theorem le_imp_le_of_lt_imp_lt
  statement: {α β} [Preorder α] [LinearOrder β] {a b : α} {c d : β}
  proof: le_of_not_gt fun h' => not_le_of_gt (H h') h

@[grind =]

中文:
定理 le_imp_le_of_lt_imp_lt
  结论: {α β} [预序 α] [线性序 β] {a b : α} {c d : β}
  证明: le_of_not_gt fun h' => not_le_of_gt (H h') h

@[grind =]

Depends on / 依赖: le_of_not_gt, not_le_of_gt
-/
theorem le_imp_le_of_lt_imp_lt {α β} [Preorder α] [LinearOrder β] {a b : α} {c d : β}
    (H : d < c -> b < a) (h : a <= b) : c <= d :=
  le_of_not_gt fun h' => not_le_of_gt (H h') h

@[grind =]
/--
lemma `min_def` / 引理 `min_def`

English:
lemma min_def
  given: (a b : α)
  statement: min a b = if a <= b then a else b
  proof: LinearOrder.min_def a b
@[grind =]

中文:
引理 min_def
  条件: (a b : α)
  结论: 最小值 a b = if a <= b then a else b
  证明: LinearOrder.min_def a b
@[grind =]

Depends on / 依赖: LinearOrder, LinearOrder.min_def, min_def
-/
lemma min_def (a b : α) : min a b = if a <= b then a else b := LinearOrder.min_def a b
@[grind =]
/--
lemma `max_def` / 引理 `max_def`

English:
lemma max_def
  given: (a b : α)
  statement: max a b = if a <= b then b else a
  proof: LinearOrder.max_def a b

中文:
引理 max_def
  条件: (a b : α)
  结论: 最大值 a b = if a <= b then b else a
  证明: LinearOrder.max_def a b

Depends on / 依赖: LinearOrder, LinearOrder.max_def, max_def
-/
lemma max_def (a b : α) : max a b = if a <= b then b else a := LinearOrder.max_def a b

/--
theorem `min_ind` / 定理 `min_ind`

English:
theorem min_ind
  given: {motive : α -> Prop} (ha : a <= b -> motive a) (hb : b <= a -> motive b)
  proof: by
  rw [min_def]; split_ifs with h
  exacts [ha h, hb (le_of_not_ge h)]

@[to_dual existing (attr := elab_as_elim)]

中文:
定理 min_ind
  条件: {motive : α -> 命题} (ha : a <= b -> motive a) (hb : b <= a -> motive b)
  证明: by
  rw [min_def]; split_ifs with h
  exacts [ha h, hb (le_of_not_ge h)]

@[to_dual existing (attr := elab_as_elim)]

Depends on / 依赖: exacts, le_of_not_ge, min_def, split_ifs
-/
theorem min_ind {motive : α -> Prop} (ha : a <= b -> motive a) (hb : b <= a -> motive b) :
    motive (min a b) := by
  rw [min_def]; split_ifs with h
  exacts [ha h, hb (le_of_not_ge h)]

@[to_dual existing (attr := elab_as_elim)]
/--
theorem `max_ind` / 定理 `max_ind`

English:
theorem max_ind
  given: {motive : α -> Prop} (ha : b <= a -> motive a) (hb : a <= b -> motive b)
  proof: by
  rw [max_def]; split_ifs with h
  exacts [hb h, ha (le_of_not_ge h)]

@[to_dual existing max_def]

中文:
定理 max_ind
  条件: {motive : α -> 命题} (ha : b <= a -> motive a) (hb : a <= b -> motive b)
  证明: by
  rw [max_def]; split_ifs with h
  exacts [hb h, ha (le_of_not_ge h)]

@[to_dual existing max_def]

Depends on / 依赖: exacts, le_of_not_ge, max_def, split_ifs
-/
theorem max_ind {motive : α -> Prop} (ha : b <= a -> motive a) (hb : a <= b -> motive b) :
    motive (max a b) := by
  rw [max_def]; split_ifs with h
  exacts [hb h, ha (le_of_not_ge h)]

@[to_dual existing max_def]
/--
theorem `min_def'` / 定理 `min_def'`

English:
theorem min_def'
  given: (a b : α)
  statement: min a b = if b <= a then b else a
  proof: by
  obtain h | h | h := lt_trichotomy a b <;> simp [le_of_lt, not_le_of_gt, h, min_def]

@[to_dual existing min_def]

中文:
定理 min_def'
  条件: (a b : α)
  结论: 最小值 a b = if b <= a then b else a
  证明: by
  obtain h | h | h := lt_trichotomy a b <;> simp [le_of_lt, not_le_of_gt, h, min_def]

@[to_dual existing min_def]

Depends on / 依赖: le_of_lt, lt_trichotomy, min_def, not_le_of_gt
-/
theorem min_def' (a b : α) : min a b = if b <= a then b else a := by
  obtain h | h | h := lt_trichotomy a b <;> simp [le_of_lt, not_le_of_gt, h, min_def]

@[to_dual existing min_def]
/--
theorem `max_def'` / 定理 `max_def'`

English:
theorem max_def'
  given: (a b : α)
  statement: max a b = if b <= a then a else b
  proof: by
  obtain h | h | h := lt_trichotomy a b <;> simp [le_of_lt, not_le_of_gt, h, max_def]

@[to_dual le_max_left]

中文:
定理 max_def'
  条件: (a b : α)
  结论: 最大值 a b = if b <= a then a else b
  证明: by
  obtain h | h | h := lt_trichotomy a b <;> simp [le_of_lt, not_le_of_gt, h, max_def]

@[to_dual le_max_left]

Depends on / 依赖: le_of_lt, lt_trichotomy, max_def, not_le_of_gt
-/
theorem max_def' (a b : α) : max a b = if b <= a then a else b := by
  obtain h | h | h := lt_trichotomy a b <;> simp [le_of_lt, not_le_of_gt, h, max_def]

@[to_dual le_max_left]
/--
lemma `min_le_left` / 引理 `min_le_left`

English:
lemma min_le_left
  given: (a b : α)
  statement: min a b <= a
  proof: by
  rw [min_def]
  split_ifs with h <;> simp [h, le_of_not_ge]

@[to_dual le_max_right]

中文:
引理 min_le_left
  条件: (a b : α)
  结论: 最小值 a b <= a
  证明: by
  rw [min_def]
  split_ifs with h <;> simp [h, le_of_not_ge]

@[to_dual le_max_right]

Depends on / 依赖: le_of_not_ge, min_def, split_ifs
-/
lemma min_le_left (a b : α) : min a b <= a := by
  rw [min_def]
  split_ifs with h <;> simp [h, le_of_not_ge]

@[to_dual le_max_right]
/--
lemma `min_le_right` / 引理 `min_le_right`

English:
lemma min_le_right
  given: (a b : α)
  statement: min a b <= b
  proof: by
  rw [min_def]
  split_ifs with h <;> simp [h]

@[to_dual max_le]

中文:
引理 min_le_right
  条件: (a b : α)
  结论: 最小值 a b <= b
  证明: by
  rw [min_def]
  split_ifs with h <;> simp [h]

@[to_dual max_le]

Depends on / 依赖: min_def, split_ifs
-/
lemma min_le_right (a b : α) : min a b <= b := by
  rw [min_def]
  split_ifs with h <;> simp [h]

@[to_dual max_le]
/--
lemma `le_min` / 引理 `le_min`

English:
lemma le_min
  given: (h₁ : c <= a) (h₂ : c <= b)
  statement: c <= min a b
  proof: by
  rw [min_def]
  split_ifs <;> assumption

@[to_dual]

中文:
引理 le_min
  条件: (h₁ : c <= a) (h₂ : c <= b)
  结论: c <= 最小值 a b
  证明: by
  rw [min_def]
  split_ifs <;> assumption

@[to_dual]

Depends on / 依赖: min_def, split_ifs
-/
lemma le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b := by
  rw [min_def]
  split_ifs <;> assumption

@[to_dual]
/--
lemma `eq_min` / 引理 `eq_min`

English:
lemma eq_min
  given: (h₁ : c <= a) (h₂ : c <= b) (h₃ : forall {d}, d <= a -> d <= b -> d <= c)
  statement: c = min a b
  proof: le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

@[to_dual]

中文:
引理 eq_min
  条件: (h₁ : c <= a) (h₂ : c <= b) (h₃ : 对任意 {d}, d <= a -> d <= b -> d <= c)
  结论: c = 最小值 a b
  证明: le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

@[to_dual]

Depends on / 依赖: le_antisymm, le_min, min_le_left, min_le_right
-/
lemma eq_min (h₁ : c <= a) (h₂ : c <= b) (h₃ : forall {d}, d <= a -> d <= b -> d <= c) : c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

@[to_dual]
/--
lemma `min_comm` / 引理 `min_comm`

English:
lemma min_comm
  given: (a b : α)
  statement: min a b = min b a
  proof: eq_min (min_le_right a b) (min_le_left a b) fun h₁ h₂ => le_min h₂ h₁

@[to_dual]

中文:
引理 min_comm
  条件: (a b : α)
  结论: 最小值 a b = 最小值 b a
  证明: eq_min (min_le_right a b) (min_le_left a b) fun h₁ h₂ => le_min h₂ h₁

@[to_dual]

Depends on / 依赖: eq_min, le_min, min_le_left, min_le_right
-/
lemma min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) fun h₁ h₂ => le_min h₂ h₁

@[to_dual]
/--
lemma `min_assoc` / 引理 `min_assoc`

English:
lemma min_assoc
  given: (a b c : α)
  statement: min (min a b) c = min a (min b c)
  proof: eq_min
    (le_trans (min_le_left ..) (min_le_left ..))
    (le_min (le_trans (min_le_left ..) (min_le_right ..)) (min_le_right ..))
    (fun h₁ h₂ =>
      le_min (le_min h₁ (le_trans h₂ (min_le_left ..))) (le_trans h₂ (min_le_right ..)))

@[to_dual]

中文:
引理 min_assoc
  条件: (a b c : α)
  结论: 最小值 (最小值 a b) c = 最小值 a (最小值 b c)
  证明: eq_min
    (le_trans (min_le_left ..) (min_le_left ..))
    (le_min (le_trans (min_le_left ..) (min_le_right ..)) (min_le_right ..))
    (fun h₁ h₂ =>
      le_min (le_min h₁ (le_trans h₂ (min_le_left ..))) (le_trans h₂ (min_le_right ..)))

@[to_dual]

Depends on / 依赖: eq_min, le_min, le_trans, min_le_left, min_le_right
-/
lemma min_assoc (a b c : α) : min (min a b) c = min a (min b c) :=
  eq_min
    (le_trans (min_le_left ..) (min_le_left ..))
    (le_min (le_trans (min_le_left ..) (min_le_right ..)) (min_le_right ..))
    (fun h₁ h₂ =>
      le_min (le_min h₁ (le_trans h₂ (min_le_left ..))) (le_trans h₂ (min_le_right ..)))

@[to_dual]
/--
lemma `min_left_comm` / 引理 `min_left_comm`

English:
lemma min_left_comm
  given: (a b c : α)
  statement: min a (min b c) = min b (min a c)
  proof: by
  rw [← min_assoc]; rw [min_comm a]; rw [min_assoc]

中文:
引理 min_left_comm
  条件: (a b c : α)
  结论: 最小值 a (最小值 b c) = 最小值 b (最小值 a c)
  证明: by
  rw [← min_assoc]; rw [min_comm a]; rw [min_assoc]

Depends on / 依赖: min_assoc, min_comm
-/
lemma min_left_comm (a b c : α) : min a (min b c) = min b (min a c) := by
  rw [← min_assoc]; rw [min_comm a]; rw [min_assoc]

/--
lemma `min_self` / 引理 `min_self`

English:
lemma min_self
  given: (a : α)
  statement: min a a = a
  proof: by rw [min_def, ite_id]

@[to_dual]

中文:
引理 min_self
  条件: (a : α)
  结论: 最小值 a a = a
  证明: by rw [min_def, ite_id]

@[to_dual]
-/
@[to_dual (attr := simp)] lemma min_self (a : α) : min a a = a := by rw [min_def, ite_id]

@[to_dual]
/--
lemma `min_eq_left` / 引理 `min_eq_left`

English:
lemma min_eq_left
  given: (h : a <= b)
  statement: min a b = a
  proof: (eq_min le_rfl h (fun h _ => h)).symm

@[to_dual]

中文:
引理 min_eq_left
  条件: (h : a <= b)
  结论: 最小值 a b = a
  证明: (eq_min le_rfl h (fun h _ => h)).symm

@[to_dual]

Depends on / 依赖: eq_min, le_rfl
-/
lemma min_eq_left (h : a <= b) : min a b = a := (eq_min le_rfl h (fun h _ => h)).symm

@[to_dual]
/--
lemma `min_eq_right` / 引理 `min_eq_right`

English:
lemma min_eq_right
  given: (h : b <= a)
  statement: min a b = b
  proof: min_comm b a ▸ min_eq_left h

中文:
引理 min_eq_right
  条件: (h : b <= a)
  结论: 最小值 a b = b
  证明: min_comm b a ▸ min_eq_left h

Depends on / 依赖: min_comm, min_eq_left
-/
lemma min_eq_right (h : b <= a) : min a b = b := min_comm b a ▸ min_eq_left h

/--
lemma `min_eq_left_of_lt` / 引理 `min_eq_left_of_lt`

English:
lemma min_eq_left_of_lt
  given: (h : a < b)
  statement: min a b = a
  proof: min_eq_left (le_of_lt h)

中文:
引理 min_eq_left_of_lt
  条件: (h : a < b)
  结论: 最小值 a b = a
  证明: min_eq_left (le_of_lt h)
-/
@[to_dual] lemma min_eq_left_of_lt (h : a < b) : min a b = a := min_eq_left (le_of_lt h)
/--
lemma `min_eq_right_of_lt` / 引理 `min_eq_right_of_lt`

English:
lemma min_eq_right_of_lt
  given: (h : b < a)
  statement: min a b = b
  proof: min_eq_right (le_of_lt h)

@[to_dual max_lt]

中文:
引理 min_eq_right_of_lt
  条件: (h : b < a)
  结论: 最小值 a b = b
  证明: min_eq_right (le_of_lt h)

@[to_dual max_lt]
-/
@[to_dual] lemma min_eq_right_of_lt (h : b < a) : min a b = b := min_eq_right (le_of_lt h)

@[to_dual max_lt]
/--
lemma `lt_min` / 引理 `lt_min`

English:
lemma lt_min
  given: (h₁ : a < b) (h₂ : a < c)
  statement: a < min b c
  proof: by
  cases le_total b c <;> simp [min_eq_left, min_eq_right, *]

中文:
引理 lt_min
  条件: (h₁ : a < b) (h₂ : a < c)
  结论: a < 最小值 b c
  证明: by
  cases le_total b c <;> simp [min_eq_left, min_eq_right, *]

Depends on / 依赖: le_total, min_eq_left, min_eq_right
-/
lemma lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c := by
  cases le_total b c <;> simp [min_eq_left, min_eq_right, *]

section Ord

/--
lemma `compare_lt_iff_lt` / 引理 `compare_lt_iff_lt`

English:
lemma compare_lt_iff_lt
  statement: compare a b = .lt ↔ a < b
  proof: by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]; rw [compareOfLessAndEq_eq_lt]

中文:
引理 compare_lt_iff_lt
  结论: compare a b = .lt ↔ a < b
  证明: by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]; rw [compareOfLessAndEq_eq_lt]

Depends on / 依赖: CommSemiring, LinearOrder, LinearOrder.compare_eq_compareOfLessAndEq, Semiring, compareOfLessAndEq_eq_lt, compare_eq_compareOfLessAndEq, finiteType
-/
lemma compare_lt_iff_lt : compare a b = .lt ↔ a < b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]; rw [compareOfLessAndEq_eq_lt]

/--
lemma `compare_eq_iff_eq` / 引理 `compare_eq_iff_eq`

English:
lemma compare_eq_iff_eq
  statement: compare a b = .eq ↔ a = b
  proof: by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]; rw [compareOfLessAndEq_eq_eq le_refl not_le]

中文:
引理 compare_eq_iff_eq
  结论: compare a b = .eq ↔ a = b
  证明: by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]; rw [compareOfLessAndEq_eq_eq le_refl not_le]

Depends on / 依赖: LinearOrder, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq_eq_eq, compare_eq_compareOfLessAndEq, le_refl, not_le
-/
lemma compare_eq_iff_eq : compare a b = .eq ↔ a = b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]; rw [compareOfLessAndEq_eq_eq le_refl not_le]

/--
lemma `compare_gt_iff_gt` / 引理 `compare_gt_iff_gt`

English:
lemma compare_gt_iff_gt
  statement: compare a b = .gt ↔ b < a
  proof: by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]; rw [compareOfLessAndEq_eq_gt le_antisymm le_total not_le]

中文:
引理 compare_gt_iff_gt
  结论: compare a b = .gt ↔ b < a
  证明: by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]; rw [compareOfLessAndEq_eq_gt le_antisymm le_total not_le]

Depends on / 依赖: LinearOrder, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq_eq_gt, compare_eq_compareOfLessAndEq, le_antisymm, le_total, not_le
-/
lemma compare_gt_iff_gt : compare a b = .gt ↔ b < a := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]; rw [compareOfLessAndEq_eq_gt le_antisymm le_total not_le]

/--
lemma `compare_le_iff_le` / 引理 `compare_le_iff_le`

English:
lemma compare_le_iff_le
  statement: compare a b != .gt ↔ a <= b
  proof: by
  cases h : compare a b
· simpa using le_of_lt compare_lt_iff_lt.1 h
· simpa using le_of_eq compare_eq_iff_eq.1 h
  · simpa using compare_gt_iff_gt.1 h

中文:
引理 compare_le_iff_le
  结论: compare a b != .gt ↔ a <= b
  证明: by
  cases h : compare a b
· simpa using le_of_lt compare_lt_iff_lt.1 h
· simpa using le_of_eq compare_eq_iff_eq.1 h
  · simpa using compare_gt_iff_gt.1 h

Depends on / 依赖: compare, compare_eq_iff_eq, compare_gt_iff_gt, compare_lt_iff_lt, le_of_eq, le_of_lt
-/
lemma compare_le_iff_le : compare a b != .gt ↔ a <= b := by
  cases h : compare a b
· simpa using le_of_lt compare_lt_iff_lt.1 h
· simpa using le_of_eq compare_eq_iff_eq.1 h
  · simpa using compare_gt_iff_gt.1 h

/--
lemma `compare_ge_iff_ge` / 引理 `compare_ge_iff_ge`

English:
lemma compare_ge_iff_ge
  statement: compare a b != .lt ↔ b <= a
  proof: by
  cases h : compare a b
  · simpa using compare_lt_iff_lt.1 h
· simpa using le_of_eq (·.symm) compare_eq_iff_eq.1 h
· simpa using le_of_lt compare_gt_iff_gt.1 h

中文:
引理 compare_ge_iff_ge
  结论: compare a b != .lt ↔ b <= a
  证明: by
  cases h : compare a b
  · simpa using compare_lt_iff_lt.1 h
· simpa using le_of_eq (·.symm) compare_eq_iff_eq.1 h
· simpa using le_of_lt compare_gt_iff_gt.1 h

Depends on / 依赖: compare, compare_eq_iff_eq, compare_gt_iff_gt, compare_lt_iff_lt, le_of_eq, le_of_lt
-/
lemma compare_ge_iff_ge : compare a b != .lt ↔ b <= a := by
  cases h : compare a b
  · simpa using compare_lt_iff_lt.1 h
· simpa using le_of_eq (·.symm) compare_eq_iff_eq.1 h
· simpa using le_of_lt compare_gt_iff_gt.1 h

/--
lemma `compare_iff` / 引理 `compare_iff`

English:
lemma compare_iff
  given: (a b : α) {o : Ordering}
  statement: compare a b = o ↔ o.Compares a b
  proof: by
  cases o <;> simp only [Ordering.Compares]
  · exact compare_lt_iff_lt
  · exact compare_eq_iff_eq
  · exact compare_gt_iff_gt

中文:
引理 compare_iff
  条件: (a b : α) {o : Ordering}
  结论: compare a b = o ↔ o.Compares a b
  证明: by
  cases o <;> simp only [Ordering.Compares]
  · exact compare_lt_iff_lt
  · exact compare_eq_iff_eq
  · exact compare_gt_iff_gt

Depends on / 依赖: Compares, Ordering, Ordering.Compares, compare_eq_iff_eq, compare_gt_iff_gt, compare_lt_iff_lt
-/
lemma compare_iff (a b : α) {o : Ordering} : compare a b = o ↔ o.Compares a b := by
  cases o <;> simp only [Ordering.Compares]
  · exact compare_lt_iff_lt
  · exact compare_eq_iff_eq
  · exact compare_gt_iff_gt

/--
theorem `cmp_eq_compare` / 定理 `cmp_eq_compare`

English:
theorem cmp_eq_compare
  given: (a b : α)
  statement: cmp a b = compare a b
  proof: by
  refine ((compare_iff ..).2 ?_).symm
  unfold cmp cmpUsing; split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)

中文:
定理 cmp_eq_compare
  条件: (a b : α)
  结论: cmp a b = compare a b
  证明: by
  refine ((compare_iff ..).2 ?_).symm
  unfold cmp cmpUsing; split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)

Depends on / 依赖: cmpUsing, compare_iff, le_antisymm, not_lt, split_ifs
-/
theorem cmp_eq_compare (a b : α) : cmp a b = compare a b := by
  refine ((compare_iff ..).2 ?_).symm
  unfold cmp cmpUsing; split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)

/--
theorem `cmp_eq_compareOfLessAndEq` / 定理 `cmp_eq_compareOfLessAndEq`

English:
theorem cmp_eq_compareOfLessAndEq
  given: (a b : α)
  statement: cmp a b = compareOfLessAndEq a b
  proof: (cmp_eq_compare ..).trans (LinearOrder.compare_eq_compareOfLessAndEq ..)

中文:
定理 cmp_eq_compareOfLessAndEq
  条件: (a b : α)
  结论: cmp a b = compareOfLessAndEq a b
  证明: (cmp_eq_compare ..).trans (LinearOrder.compare_eq_compareOfLessAndEq ..)

Depends on / 依赖: Finset, Finset.coe_image, Finset.coe_univ, Finset.univ.image, LinearOrder, LinearOrder.compare_eq_compareOfLessAndEq, MvPolynomial, MvPolynomial.X, MvPolynomial.adjoin_range_X, Set.image_univ, adjoin_range_X, classical, cmp_eq_compare, coe_image, coe_univ, compare_eq_compareOfLessAndEq, image_univ, nonempty_fintype
-/
theorem cmp_eq_compareOfLessAndEq (a b : α) : cmp a b = compareOfLessAndEq a b :=
  (cmp_eq_compare ..).trans (LinearOrder.compare_eq_compareOfLessAndEq ..)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.LawfulBCmp (compare (α := α))
  body: by
    cases _ : compare b a <;>
      simp_all [Ordering.swap, compare_eq_iff_eq, compare_lt_iff_lt, compare_gt_iff_gt]
  isLE_trans h₁ h₂ := by
    simp only [← Ordering.ne_gt_iff_isLE, compare_le_iff_le] at *
    exact le_trans h₁ h₂
  compare_eq_iff_beq := by simp [compare_eq_iff_eq]
  eq_lt_iff_lt := by simp [compare_lt_iff_lt]
  isLE_iff_le := by simp [← Ordering.ne_gt_iff_isLE, compare_le_iff_le]

中文:
实例 :
  签名: Std.LawfulBCmp (compare (α := α))
  定义体: by
    cases _ : compare b a <;>
      simp_all [Ordering.swap, compare_eq_iff_eq, compare_lt_iff_lt, compare_gt_iff_gt]
  isLE_trans h₁ h₂ := by
    simp only [← Ordering.ne_gt_iff_isLE, compare_le_iff_le] at *
    exact le_trans h₁ h₂
  compare_eq_iff_beq := by simp [compare_eq_iff_eq]
  eq_lt_iff_lt := by simp [compare_lt_iff_lt]
  isLE_iff_le := by simp [← Ordering.ne_gt_iff_isLE, compare_le_iff_le]

Depends on / 依赖: Finset, Finset.coe_image, Finset.coe_univ, Finset.univ.image, FreeAlgebra, FreeAlgebra.adjoin_range_, Set.image_univ, classical, coe_image, coe_univ, image_univ, nonempty_fintype
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

/--
Definition of `LinOrd` / `LinOrd` 的定义

English:
structure LinOrd
  parameters: where
  axioms and operations (3):
    - of : :
    - (carrier : Type*)
    - [str : LinearOrder carrier]

中文:
结构 线性序
  参数: where
  公理与运算 (3 个):
    - of : :
    - (carrier : 类型)
    - [str : 线性序 carrier]
-/
structure LinOrd where
  /-- Construct a bundled `LinOrd` from the underlying type and typeclass. -/
  of ::
  /-- The underlying linearly ordered type. -/
  (carrier : Type*)
  [str : LinearOrder carrier]

attribute [instance] LinOrd.str

initialize_simps_projections LinOrd (carrier -> coe, -str)

namespace LinOrd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort LinOrd (Type _)
  body: ⟨LinOrd.carrier⟩

中文:
实例 :
  签名: CoeSort 线性序 (类型 _)
  定义体: ⟨LinOrd.carrier⟩

Depends on / 依赖: LinOrd, LinOrd.carrier, carrier
-/
instance : CoeSort LinOrd (Type _) :=
  ⟨LinOrd.carrier⟩

attribute [coe] LinOrd.carrier

end LinOrd

end LinearOrder
