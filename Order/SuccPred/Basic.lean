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

/--
Definition of `SuccOrder` / `SuccOrder` 的定义

English:
class SuccOrder
  parameters: (α : Type*) [Preorder α]
  axioms and operations (4):
    - succ : α -> α
    - le_succ : forall a, a <= succ a
    - max_of_succ_le({a}) : succ a <= a -> IsMax a
    - succ_le_of_lt({a b}) : a < b -> succ a <= b

中文:
类 SuccOrder
  参数: (α : 类型) [Preorder α]
  公理与运算 (4 个):
    - succ : α -> α
    - le_succ : 对任意 a, a <= succ a
    - max_of_succ_le({a}) : succ a <= a -> IsMax a
    - succ_le_of_lt({a b}) : a < b -> succ a <= b

Depends on / 依赖: Ideal.Quotient.isScalarTower_of_liesOver, Quotient, isScalarTower_of_liesOver
-/
class SuccOrder (α : Type*) [Preorder α] where
  /-- Successor function -/
  succ : α -> α
  /-- Proof of basic ordering with respect to `succ` -/
  le_succ : forall a, a <= succ a
  /-- Proof of interaction between `succ` and maximal element -/
  max_of_succ_le {a} : succ a <= a -> IsMax a
  /-- Proof that `succ a` is the least element greater than `a` -/
  succ_le_of_lt {a b} : a < b -> succ a <= b

/-- Order equipped with a sensible predecessor function. -/
@[to_dual (attr := ext)]
/--
Definition of `PredOrder` / `PredOrder` 的定义

English:
class PredOrder
  parameters: (α : Type*) [Preorder α]
  axioms and operations (4):
    - pred : α -> α
    - pred_le : forall a, pred a <= a
    - min_of_le_pred({a}) : a <= pred a -> IsMin a
    - le_pred_of_lt({a b}) : a < b -> a <= pred b

中文:
类 PredOrder
  参数: (α : 类型) [Preorder α]
  公理与运算 (4 个):
    - pred : α -> α
    - pred_le : 对任意 a, pred a <= a
    - min_of_le_pred({a}) : a <= pred a -> IsMin a
    - le_pred_of_lt({a b}) : a < b -> a <= pred b

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap_apply, of_algebraMap_eq, residue_surjective
-/
class PredOrder (α : Type*) [Preorder α] where
  /-- Predecessor function -/
  pred : α -> α
  /-- Proof of basic ordering with respect to `pred` -/
  pred_le : forall a, pred a <= a
  /-- Proof of interaction between `pred` and minimal element -/
  min_of_le_pred {a} : a <= pred a -> IsMin a
  /-- Proof that `pred b` is the greatest element less than `b` -/
  le_pred_of_lt {a b} : a < b -> a <= pred b

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [SuccOrder α] : PredOrder αᵒᵈ where
  body: toDual ∘ SuccOrder.succ ∘ ofDual
  pred_le := by simp [SuccOrder.le_succ]
  min_of_le_pred h := by apply SuccOrder.max_of_succ_le h
  le_pred_of_lt {a b} h := SuccOrder.succ_le_of_lt h

中文:
实例 [Preorder
  签名: α] [SuccOrder α] : PredOrder αᵒᵈ where
  定义体: toDual ∘ SuccOrder.succ ∘ ofDual
  pred_le := by simp [SuccOrder.le_succ]
  min_of_le_pred h := by apply SuccOrder.max_of_succ_le h
  le_pred_of_lt {a b} h := SuccOrder.succ_le_of_lt h
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
/--
Definition of `SuccOrder.ofSuccLeIff` / `SuccOrder.ofSuccLeIff` 的定义

English:
definition SuccOrder.ofSuccLeIff
  signature: (succ : α -> α) (hsucc_le_iff : forall {a b}, succ a <= b ↔ a < b)
  body: succ
  le_succ _ := (hsucc_le_iff.1 le_rfl).le
  max_of_succ_le ha := (lt_irrefl _ <| hsucc_le_iff.1 ha).elim
  succ_le_of_lt := hsucc_le_iff.2

中文:
定义 SuccOrder.ofSuccLeIff
  签名: (succ : α -> α) (hsucc_le_iff : 对任意 {a b}, succ a <= b ↔ a < b)
  定义体: succ
  le_succ _ := (hsucc_le_iff.1 le_rfl).le
  max_of_succ_le ha := (lt_irrefl _ <| hsucc_le_iff.1 ha).elim
  succ_le_of_lt := hsucc_le_iff.2
-/
def SuccOrder.ofSuccLeIff (succ : α -> α) (hsucc_le_iff : forall {a b}, succ a <= b ↔ a < b) :
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
/--
Definition of `SuccOrder.ofCore` / `SuccOrder.ofCore` 的定义

English:
definition SuccOrder.ofCore
  signature: (succ : α -> α) (hn : forall {a}, ¬IsMax a -> forall b, a < b ↔ succ a <= b)
  body: succ
  succ_le_of_lt {a b} := by_cases (fun h hab => (hm a h).symm ▸ hab.le) fun h => (hn h b).mp
le_succ a := by_cases (fun h => (hm a h).symm.le) fun h => le_of_lt by simpa using (hn h a).not
  max_of_succ_le {a} := not_imp_not.mp fun h => by simpa using (hn h a).not

中文:
定义 SuccOrder.ofCore
  签名: (succ : α -> α) (hn : 对任意 {a}, ¬IsMax a -> 对任意 b, a < b ↔ succ a <= b)
  定义体: succ
  succ_le_of_lt {a b} := by_cases (fun h hab => (hm a h).symm ▸ hab.le) fun h => (hn h b).mp
le_succ a := by_cases (fun h => (hm a h).symm.le) fun h => le_of_lt by simpa using (hn h a).not
  max_of_succ_le {a} := not_imp_not.mp fun h => by simpa using (hn h a).not
-/
def SuccOrder.ofCore (succ : α -> α) (hn : forall {a}, ¬IsMax a -> forall b, a < b ↔ succ a <= b)
    (hm : forall a, IsMax a -> succ a = a) : SuccOrder α where
  succ := succ
  succ_le_of_lt {a b} := by_cases (fun h hab => (hm a h).symm ▸ hab.le) fun h => (hn h b).mp
le_succ a := by_cases (fun h => (hm a h).symm.le) fun h => le_of_lt by simpa using (hn h a).not
  max_of_succ_le {a} := not_imp_not.mp fun h => by simpa using (hn h a).not

variable (α)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- A well-order is a `SuccOrder`. -/
@[to_dual (attr := instance_reducible)
/-- A linear order with well-founded greater-than relation is a `PredOrder`. -/]
/--
Definition of `SuccOrder.ofLinearWellFoundedLT` / `SuccOrder.ofLinearWellFoundedLT` 的定义

English:
definition SuccOrder.ofLinearWellFoundedLT
  signature: [WellFoundedLT α]
  body: ofCore (fun a => if h : (Ioi a).Nonempty then wellFounded_lt.min _ h else a)
    (fun ha _ => by
      rw [not_isMax_iff] at ha
      simp_rw [Set.Nonempty, mem_Ioi, dif_pos ha]
      exact ⟨wellFounded_lt.min_le (s := Ioi _), lt_of_lt_of_le (wellFounded_lt.prop_min ha)⟩)
    fun _ ha => dif_neg (no

中文:
定义 SuccOrder.ofLinearWellFoundedLT
  签名: [WellFoundedLT α]
  定义体: ofCore (fun a => if h : (Ioi a).Nonempty then wellFounded_lt.min _ h else a)
    (fun ha _ => by
      rw [not_isMax_iff] at ha
      simp_rw [Set.Nonempty, mem_Ioi, dif_pos ha]
      exact ⟨wellFounded_lt.min_le (s := Ioi _), lt_of_lt_of_le (wellFounded_lt.prop_min ha)⟩)
    fun _ ha => dif_neg (no

Depends on / 依赖: Nonempty, Set.Nonempty, dif_neg, dif_pos, lt_of_lt_of_le, mem_Ioi, min_le, not_isMax_iff, not_isMax_iff.mpr, not_not_intro, ofCore, prop_min, simp_rw, wellFounded_lt, wellFounded_lt.min, wellFounded_lt.min_le, wellFounded_lt.prop_min
-/
noncomputable def SuccOrder.ofLinearWellFoundedLT [WellFoundedLT α] : SuccOrder α :=
  ofCore (fun a => if h : (Ioi a).Nonempty then wellFounded_lt.min _ h else a)
    (fun ha _ => by
      rw [not_isMax_iff] at ha
      simp_rw [Set.Nonempty, mem_Ioi, dif_pos ha]
      exact ⟨wellFounded_lt.min_le (s := Ioi _), lt_of_lt_of_le (wellFounded_lt.prop_min ha)⟩)
    fun _ ha => dif_neg (not_not_intro ha <| not_isMax_iff.mpr ·)

end LinearOrder

/-! ### Successor and predecessor orders -/

namespace Order

section Preorder

variable [Preorder α] [SuccOrder α] {a b : α}

/-- The successor of an element. If `a` is not maximal, then `succ a` is the least element greater
than `a`. If `a` is maximal, then `succ a = a`. -/
@[to_dual /-- The predecessor of an element. If `a` is not minimal, then `pred a` is the greatest
element less than `a`. If `a` is minimal, then `pred a = a`. -/]
/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: : α -> α
  body: SuccOrder.succ

@[to_dual pred_le]

中文:
定义 succ
  签名: : α -> α
  定义体: SuccOrder.succ

@[to_dual pred_le]

Depends on / 依赖: SuccOrder, SuccOrder.succ
-/
def succ : α -> α :=
  SuccOrder.succ

@[to_dual pred_le]
/--
theorem `le_succ` / 定理 `le_succ`

English:
theorem le_succ
  statement: forall a : α, a <= succ a
  proof: SuccOrder.le_succ

@[to_dual min_of_le_pred]

中文:
定理 le_succ
  结论: 对任意 a : α, a <= succ a
  证明: SuccOrder.le_succ

@[to_dual min_of_le_pred]

Depends on / 依赖: SuccOrder, SuccOrder.le_succ, le_succ
-/
theorem le_succ : forall a : α, a <= succ a :=
  SuccOrder.le_succ

@[to_dual min_of_le_pred]
/--
theorem `max_of_succ_le` / 定理 `max_of_succ_le`

English:
theorem max_of_succ_le
  given: {a : α}
  statement: succ a <= a -> IsMax a
  proof: SuccOrder.max_of_succ_le

@[to_dual le_pred_of_lt]

中文:
定理 max_of_succ_le
  条件: {a : α}
  结论: succ a <= a -> IsMax a
  证明: SuccOrder.max_of_succ_le

@[to_dual le_pred_of_lt]

Depends on / 依赖: SuccOrder, SuccOrder.max_of_succ_le, max_of_succ_le
-/
theorem max_of_succ_le {a : α} : succ a <= a -> IsMax a :=
  SuccOrder.max_of_succ_le

@[to_dual le_pred_of_lt]
/--
theorem `succ_le_of_lt` / 定理 `succ_le_of_lt`

English:
theorem succ_le_of_lt
  given: {a b : α}
  statement: a < b -> succ a <= b
  proof: SuccOrder.succ_le_of_lt

@[to_dual le_pred]
alias _root_.LT.lt.succ_le := succ_le_of_lt

@[to_dual (attr := simp) le_pred_iff_isMin]

中文:
定理 succ_le_of_lt
  条件: {a b : α}
  结论: a < b -> succ a <= b
  证明: SuccOrder.succ_le_of_lt

@[to_dual le_pred]
alias _root_.LT.lt.succ_le := succ_le_of_lt

@[to_dual (attr := simp) le_pred_iff_isMin]

Depends on / 依赖: SuccOrder, SuccOrder.succ_le_of_lt, succ_le_of_lt
-/
theorem succ_le_of_lt {a b : α} : a < b -> succ a <= b :=
  SuccOrder.succ_le_of_lt

@[to_dual le_pred]
alias _root_.LT.lt.succ_le := succ_le_of_lt

@[to_dual (attr := simp) le_pred_iff_isMin]
/--
theorem `succ_le_iff_isMax` / 定理 `succ_le_iff_isMax`

English:
theorem succ_le_iff_isMax
  statement: succ a <= a ↔ IsMax a
  proof: ⟨max_of_succ_le, fun h => h le_succ _⟩

alias ⟨_root_.IsMax.of_succ_le, _root_.IsMax.succ_le⟩ := succ_le_iff_isMax

中文:
定理 succ_le_iff_isMax
  结论: succ a <= a ↔ IsMax a
  证明: ⟨max_of_succ_le, fun h => h le_succ _⟩

alias ⟨_root_.IsMax.of_succ_le, _root_.IsMax.succ_le⟩ := succ_le_iff_isMax

Depends on / 依赖: le_succ, max_of_succ_le
-/
theorem succ_le_iff_isMax : succ a <= a ↔ IsMax a :=
⟨max_of_succ_le, fun h => h le_succ _⟩

alias ⟨_root_.IsMax.of_succ_le, _root_.IsMax.succ_le⟩ := succ_le_iff_isMax

attribute [to_dual of_le_pred] IsMax.of_succ_le
attribute [to_dual le_pred] IsMax.succ_le

@[to_dual (attr := simp) pred_lt_iff_not_isMin]
/--
theorem `lt_succ_iff_not_isMax` / 定理 `lt_succ_iff_not_isMax`

English:
theorem lt_succ_iff_not_isMax
  statement: a < succ a ↔ ¬IsMax a
  proof: ⟨not_isMax_of_lt, fun ha => (le_succ a).lt_of_not_ge fun h => ha max_of_succ_le h⟩

@[to_dual pred_lt_of_not_isMin]
alias ⟨_, lt_succ_of_not_isMax⟩ := lt_succ_iff_not_isMax

@[to_dual pred_wcovBy]

中文:
定理 lt_succ_iff_not_isMax
  结论: a < succ a ↔ ¬IsMax a
  证明: ⟨not_isMax_of_lt, fun ha => (le_succ a).lt_of_not_ge fun h => ha max_of_succ_le h⟩

@[to_dual pred_lt_of_not_isMin]
alias ⟨_, lt_succ_of_not_isMax⟩ := lt_succ_iff_not_isMax

@[to_dual pred_wcovBy]

Depends on / 依赖: le_succ, lt_of_not_ge, max_of_succ_le, not_isMax_of_lt
-/
theorem lt_succ_iff_not_isMax : a < succ a ↔ ¬IsMax a :=
⟨not_isMax_of_lt, fun ha => (le_succ a).lt_of_not_ge fun h => ha max_of_succ_le h⟩

@[to_dual pred_lt_of_not_isMin]
alias ⟨_, lt_succ_of_not_isMax⟩ := lt_succ_iff_not_isMax

@[to_dual pred_wcovBy]
/--
theorem `wcovBy_succ` / 定理 `wcovBy_succ`

English:
theorem wcovBy_succ
  given: (a : α)
  statement: a ⩿ succ a
  proof: ⟨le_succ a, fun _ hb => (succ_le_of_lt hb).not_gt⟩

@[to_dual pred_covBy_of_not_isMin]

中文:
定理 wcovBy_succ
  条件: (a : α)
  结论: a ⩿ succ a
  证明: ⟨le_succ a, fun _ hb => (succ_le_of_lt hb).not_gt⟩

@[to_dual pred_covBy_of_not_isMin]

Depends on / 依赖: le_succ, not_gt, succ_le_of_lt
-/
theorem wcovBy_succ (a : α) : a ⩿ succ a :=
  ⟨le_succ a, fun _ hb => (succ_le_of_lt hb).not_gt⟩

@[to_dual pred_covBy_of_not_isMin]
/--
theorem `covBy_succ_of_not_isMax` / 定理 `covBy_succ_of_not_isMax`

English:
theorem covBy_succ_of_not_isMax
  given: (h : ¬IsMax a)
  statement: a ⋖ succ a
  proof: (wcovBy_succ a).covBy_of_lt lt_succ_of_not_isMax h

@[to_dual pred_lt_of_le_of_not_isMin]

中文:
定理 covBy_succ_of_not_isMax
  条件: (h : ¬IsMax a)
  结论: a ⋖ succ a
  证明: (wcovBy_succ a).covBy_of_lt lt_succ_of_not_isMax h

@[to_dual pred_lt_of_le_of_not_isMin]

Depends on / 依赖: covBy_of_lt, lt_succ_of_not_isMax, wcovBy_succ
-/
theorem covBy_succ_of_not_isMax (h : ¬IsMax a) : a ⋖ succ a :=
(wcovBy_succ a).covBy_of_lt lt_succ_of_not_isMax h

@[to_dual pred_lt_of_le_of_not_isMin]
/--
theorem `lt_succ_of_le_of_not_isMax` / 定理 `lt_succ_of_le_of_not_isMax`

English:
theorem lt_succ_of_le_of_not_isMax
  given: (hab : b <= a) (ha : ¬IsMax a)
  statement: b < succ a
  proof: hab.trans_lt lt_succ_of_not_isMax ha

@[to_dual le_pred_iff_of_not_isMin]

中文:
定理 lt_succ_of_le_of_not_isMax
  条件: (hab : b <= a) (ha : ¬IsMax a)
  结论: b < succ a
  证明: hab.trans_lt lt_succ_of_not_isMax ha

@[to_dual le_pred_iff_of_not_isMin]

Depends on / 依赖: hab.trans_lt, lt_succ_of_not_isMax, trans_lt
-/
theorem lt_succ_of_le_of_not_isMax (hab : b <= a) (ha : ¬IsMax a) : b < succ a :=
hab.trans_lt lt_succ_of_not_isMax ha

@[to_dual le_pred_iff_of_not_isMin]
/--
theorem `succ_le_iff_of_not_isMax` / 定理 `succ_le_iff_of_not_isMax`

English:
theorem succ_le_iff_of_not_isMax
  given: (ha : ¬IsMax a)
  statement: succ a <= b ↔ a < b
  proof: ⟨(lt_succ_of_not_isMax ha).trans_le, succ_le_of_lt⟩

@[to_dual le_pred_iff_of_not_isMin']

中文:
定理 succ_le_iff_of_not_isMax
  条件: (ha : ¬IsMax a)
  结论: succ a <= b ↔ a < b
  证明: ⟨(lt_succ_of_not_isMax ha).trans_le, succ_le_of_lt⟩

@[to_dual le_pred_iff_of_not_isMin']

Depends on / 依赖: lt_succ_of_not_isMax, succ_le_of_lt, trans_le
-/
theorem succ_le_iff_of_not_isMax (ha : ¬IsMax a) : succ a <= b ↔ a < b :=
  ⟨(lt_succ_of_not_isMax ha).trans_le, succ_le_of_lt⟩

@[to_dual le_pred_iff_of_not_isMin']
/--
theorem `succ_le_iff_of_not_isMax'` / 定理 `succ_le_iff_of_not_isMax'`

English:
theorem succ_le_iff_of_not_isMax'
  given: (hb : ¬IsMax b)
  statement: succ a <= b ↔ a < b
  proof: by
  by_cases ha : IsMax a
  · grind [le_succ, IsMax.mono]
  · exact succ_le_iff_of_not_isMax ha

@[to_dual]

中文:
定理 succ_le_iff_of_not_isMax'
  条件: (hb : ¬IsMax b)
  结论: succ a <= b ↔ a < b
  证明: by
  by_cases ha : IsMax a
  · grind [le_succ, IsMax.mono]
  · exact succ_le_iff_of_not_isMax ha

@[to_dual]

Depends on / 依赖: IsMax.mono, le_succ, succ_le_iff_of_not_isMax
-/
theorem succ_le_iff_of_not_isMax' (hb : ¬IsMax b) : succ a <= b ↔ a < b := by
  by_cases ha : IsMax a
  · grind [le_succ, IsMax.mono]
  · exact succ_le_iff_of_not_isMax ha

@[to_dual]
/--
lemma `succ_lt_succ_of_not_isMax` / 引理 `succ_lt_succ_of_not_isMax`

English:
lemma succ_lt_succ_of_not_isMax
  given: (h : a < b) (hb : ¬ IsMax b)
  statement: succ a < succ b
  proof: lt_succ_of_le_of_not_isMax (succ_le_of_lt h) hb

@[to_dual (attr := simp, mono, gcongr)]

中文:
引理 succ_lt_succ_of_not_isMax
  条件: (h : a < b) (hb : ¬ IsMax b)
  结论: succ a < succ b
  证明: lt_succ_of_le_of_not_isMax (succ_le_of_lt h) hb

@[to_dual (attr := simp, mono, gcongr)]

Depends on / 依赖: lt_succ_of_le_of_not_isMax, succ_le_of_lt
-/
lemma succ_lt_succ_of_not_isMax (h : a < b) (hb : ¬ IsMax b) : succ a < succ b :=
  lt_succ_of_le_of_not_isMax (succ_le_of_lt h) hb

@[to_dual (attr := simp, mono, gcongr)]
/--
theorem `succ_le_succ` / 定理 `succ_le_succ`

English:
theorem succ_le_succ
  given: (h : a <= b)
  statement: succ a <= succ b
  proof: by
  by_cases hb : IsMax b
  · by_cases hba : b <= a
    · exact (hb <| hba.trans <| le_succ _).trans (le_succ _)
    · exact succ_le_of_lt ((h.lt_of_not_ge hba).trans_le <| le_succ b)
  · rw [succ_le_iff_of_not_isMax fun ha => hb <| ha.mono h]
    apply lt_succ_of_le_of_not_isMax h hb

@[to_dual]

中文:
定理 succ_le_succ
  条件: (h : a <= b)
  结论: succ a <= succ b
  证明: by
  by_cases hb : IsMax b
  · by_cases hba : b <= a
    · exact (hb <| hba.trans <| le_succ _).trans (le_succ _)
    · exact succ_le_of_lt ((h.lt_of_not_ge hba).trans_le <| le_succ b)
  · rw [succ_le_iff_of_not_isMax fun ha => hb <| ha.mono h]
    apply lt_succ_of_le_of_not_isMax h hb

@[to_dual]

Depends on / 依赖: h.lt_of_not_ge, ha.mono, hba.trans, le_succ, lt_of_not_ge, lt_succ_of_le_of_not_isMax, succ_le_iff_of_not_isMax, succ_le_of_lt, trans_le
-/
theorem succ_le_succ (h : a <= b) : succ a <= succ b := by
  by_cases hb : IsMax b
  · by_cases hba : b <= a
    · exact (hb <| hba.trans <| le_succ _).trans (le_succ _)
    · exact succ_le_of_lt ((h.lt_of_not_ge hba).trans_le <| le_succ b)
  · rw [succ_le_iff_of_not_isMax fun ha => hb <| ha.mono h]
    apply lt_succ_of_le_of_not_isMax h hb

@[to_dual]
/--
theorem `succ_mono` / 定理 `succ_mono`

English:
theorem succ_mono
  statement: Monotone (succ : α -> α)
  proof: fun _ _ => succ_le_succ

中文:
定理 succ_mono
  结论: Monotone (succ : α -> α)
  证明: fun _ _ => succ_le_succ

Depends on / 依赖: ResidueField, p.ResidueField, succ_le_succ
-/
theorem succ_mono : Monotone (succ : α -> α) := fun _ _ => succ_le_succ

/-- See also `Order.succ_eq_of_covBy`. -/
@[to_dual pred_le_of_wcovBy /-- See also `Order.pred_eq_of_covBy`. -/]
/--
lemma `le_succ_of_wcovBy` / 引理 `le_succ_of_wcovBy`

English:
lemma le_succ_of_wcovBy
  given: (h : a ⩿ b)
  statement: b <= succ a
  proof: by
  obtain hab | ⟨-, hba⟩ := h.covBy_or_le_and_le
  · by_contra hba
exact h.2 (lt_succ_of_not_isMax hab.lt.not_isMax) hab.lt.succ_le.lt_of_not_ge hba
  · exact hba.trans (le_succ _)

@[to_dual pred_le]
alias _root_.WCovBy.le_succ := le_succ_of_wcovBy

@[to_dual pred_iterate_le]

中文:
引理 le_succ_of_wcovBy
  条件: (h : a ⩿ b)
  结论: b <= succ a
  证明: by
  obtain hab | ⟨-, hba⟩ := h.covBy_or_le_and_le
  · by_contra hba
exact h.2 (lt_succ_of_not_isMax hab.lt.not_isMax) hab.lt.succ_le.lt_of_not_ge hba
  · exact hba.trans (le_succ _)

@[to_dual pred_le]
alias _root_.WCovBy.le_succ := le_succ_of_wcovBy

@[to_dual pred_iterate_le]

Depends on / 依赖: Ideal.over_def, Localization, Localization.localRingHom_unique, covBy_or_le_and_le, h.covBy_or_le_and_le, hab.lt.not_isMax, hab.lt.succ_le.lt_of_not_ge, hba.trans, le_succ, localRingHom_unique, lt_of_not_ge, lt_succ_of_not_isMax, not_isMax, over_def, succ_le
-/
lemma le_succ_of_wcovBy (h : a ⩿ b) : b <= succ a := by
  obtain hab | ⟨-, hba⟩ := h.covBy_or_le_and_le
  · by_contra hba
exact h.2 (lt_succ_of_not_isMax hab.lt.not_isMax) hab.lt.succ_le.lt_of_not_ge hba
  · exact hba.trans (le_succ _)

@[to_dual pred_le]
alias _root_.WCovBy.le_succ := le_succ_of_wcovBy

@[to_dual pred_iterate_le]
/--
theorem `le_succ_iterate` / 定理 `le_succ_iterate`

English:
theorem le_succ_iterate
  given: (k : Nat) (x : α)
  statement: x <= succ^[k] x
  proof: id_le_iterate_of_id_le le_succ _ _

中文:
定理 le_succ_iterate
  条件: (k : 自然数) (x : α)
  结论: x <= succ^[k] x
  证明: id_le_iterate_of_id_le le_succ _ _

Depends on / 依赖: id_le_iterate_of_id_le, le_succ
-/
theorem le_succ_iterate (k : Nat) (x : α) : x <= succ^[k] x :=
  id_le_iterate_of_id_le le_succ _ _

-- `to_dual` doesn't support `Monotone.monotone_iterate_of_le_map`, so we can't use `to_dual` here.
/--
theorem `isMax_iterate_succ_of_eq_of_lt` / 定理 `isMax_iterate_succ_of_eq_of_lt`

English:
theorem isMax_iterate_succ_of_eq_of_lt
  statement: {n m : Nat} (h_eq : succ^[n] a = succ^[m] a)
  proof: by
  refine max_of_succ_le (le_trans ?_ h_eq.symm.le)
  rw [← iterate_succ_apply' succ]
  have h_le : n + 1 <= m := Nat.succ_le_of_lt h_lt
  exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ a) h_le

中文:
定理 isMax_iterate_succ_of_eq_of_lt
  结论: {n m : 自然数} (h_eq : succ^[n] a = succ^[m] a)
  证明: by
  refine max_of_succ_le (le_trans ?_ h_eq.symm.le)
  rw [← iterate_succ_apply' succ]
  have h_le : n + 1 <= m := Nat.succ_le_of_lt h_lt
  exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ a) h_le

Depends on / 依赖: Monotone, Monotone.monotone_iterate_of_le_map, Nat.succ_le_of_lt, h_eq, h_eq.symm.le, h_le, h_lt, iterate_succ_apply, le_succ, le_trans, max_of_succ_le, monotone_iterate_of_le_map, succ_le_of_lt, succ_mono
-/
theorem isMax_iterate_succ_of_eq_of_lt {n m : Nat} (h_eq : succ^[n] a = succ^[m] a)
    (h_lt : n < m) : IsMax (succ^[n] a) := by
  refine max_of_succ_le (le_trans ?_ h_eq.symm.le)
  rw [← iterate_succ_apply' succ]
  have h_le : n + 1 <= m := Nat.succ_le_of_lt h_lt
  exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ a) h_le

/--
theorem `isMax_iterate_succ_of_eq_of_ne` / 定理 `isMax_iterate_succ_of_eq_of_ne`

English:
theorem isMax_iterate_succ_of_eq_of_ne
  statement: {n m : Nat} (h_eq : succ^[n] a = succ^[m] a)
  proof: by
  rcases le_total n m with h | h
  · exact isMax_iterate_succ_of_eq_of_lt h_eq (lt_of_le_of_ne h h_ne)
  · rw [h_eq]
    exact isMax_iterate_succ_of_eq_of_lt h_eq.symm (lt_of_le_of_ne h h_ne.symm)

@[to_dual (attr := deprecated "use `gcongr`/`grw` and `lt_succ_of_not_isMax"
  (since := "2026-06-0

中文:
定理 isMax_iterate_succ_of_eq_of_ne
  结论: {n m : 自然数} (h_eq : succ^[n] a = succ^[m] a)
  证明: by
  rcases le_total n m with h | h
  · exact isMax_iterate_succ_of_eq_of_lt h_eq (lt_of_le_of_ne h h_ne)
  · rw [h_eq]
    exact isMax_iterate_succ_of_eq_of_lt h_eq.symm (lt_of_le_of_ne h h_ne.symm)

@[to_dual (attr := deprecated "use `gcongr`/`grw` and `lt_succ_of_not_isMax"
  (since := "2026-06-0

Depends on / 依赖: h_eq, h_eq.symm, h_ne, h_ne.symm, isMax_iterate_succ_of_eq_of_lt, le_total, lt_of_le_of_ne
-/
theorem isMax_iterate_succ_of_eq_of_ne {n m : Nat} (h_eq : succ^[n] a = succ^[m] a)
    (h_ne : n != m) : IsMax (succ^[n] a) := by
  rcases le_total n m with h | h
  · exact isMax_iterate_succ_of_eq_of_lt h_eq (lt_of_le_of_ne h h_ne)
  · rw [h_eq]
    exact isMax_iterate_succ_of_eq_of_lt h_eq.symm (lt_of_le_of_ne h h_ne.symm)

@[to_dual (attr := deprecated "use `gcongr`/`grw` and `lt_succ_of_not_isMax"
  (since := "2026-06-06"))]
/--
theorem `Iic_subset_Iio_succ_of_not_isMax` / 定理 `Iic_subset_Iio_succ_of_not_isMax`

English:
theorem Iic_subset_Iio_succ_of_not_isMax
  given: (ha : ¬IsMax a)
  statement: Iic a subseteq Iio (succ a)
  proof: by
  gcongr
  exact lt_succ_of_not_isMax ha

@[to_dual]

中文:
定理 Iic_subset_Iio_succ_of_not_isMax
  条件: (ha : ¬IsMax a)
  结论: Iic a subseteq Iio (succ a)
  证明: by
  gcongr
  exact lt_succ_of_not_isMax ha

@[to_dual]

Depends on / 依赖: lt_succ_of_not_isMax
-/
theorem Iic_subset_Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iic a subseteq Iio (succ a) := by
  gcongr
  exact lt_succ_of_not_isMax ha

@[to_dual]
/--
theorem `Ici_succ_of_not_isMax` / 定理 `Ici_succ_of_not_isMax`

English:
theorem Ici_succ_of_not_isMax
  given: (ha : ¬IsMax a)
  statement: Ici (succ a) = Ioi a
  proof: Set.ext fun _ => succ_le_iff_of_not_isMax ha

@[to_dual Icc_subset_Ioc_pred_left_of_not_isMin]

中文:
定理 Ici_succ_of_not_isMax
  条件: (ha : ¬IsMax a)
  结论: Ici (succ a) = Ioi a
  证明: Set.ext fun _ => succ_le_iff_of_not_isMax ha

@[to_dual Icc_subset_Ioc_pred_left_of_not_isMin]

Depends on / 依赖: Set.ext, succ_le_iff_of_not_isMax
-/
theorem Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici (succ a) = Ioi a :=
  Set.ext fun _ => succ_le_iff_of_not_isMax ha

@[to_dual Icc_subset_Ioc_pred_left_of_not_isMin]
/--
theorem `Icc_subset_Ico_succ_right_of_not_isMax` / 定理 `Icc_subset_Ico_succ_right_of_not_isMax`

English:
theorem Icc_subset_Ico_succ_right_of_not_isMax
  given: (hb : ¬IsMax b)
  statement: Icc a b subseteq Ico a (succ b)
  proof: by
  gcongr
  exact lt_succ_of_not_isMax hb

@[to_dual Ico_subset_Ioo_pred_left_of_not_isMin]

中文:
定理 Icc_subset_Ico_succ_right_of_not_isMax
  条件: (hb : ¬IsMax b)
  结论: Icc a b subseteq Ico a (succ b)
  证明: by
  gcongr
  exact lt_succ_of_not_isMax hb

@[to_dual Ico_subset_Ioo_pred_left_of_not_isMin]

Depends on / 依赖: lt_succ_of_not_isMax
-/
theorem Icc_subset_Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Icc a b subseteq Ico a (succ b) := by
  gcongr
  exact lt_succ_of_not_isMax hb

@[to_dual Ico_subset_Ioo_pred_left_of_not_isMin]
/--
theorem `Ioc_subset_Ioo_succ_right_of_not_isMax` / 定理 `Ioc_subset_Ioo_succ_right_of_not_isMax`

English:
theorem Ioc_subset_Ioo_succ_right_of_not_isMax
  given: (hb : ¬IsMax b)
  statement: Ioc a b subseteq Ioo a (succ b)
  proof: by
  gcongr
  exact lt_succ_of_not_isMax hb

@[to_dual Icc_pred_right_of_not_isMin]

中文:
定理 Ioc_subset_Ioo_succ_right_of_not_isMax
  条件: (hb : ¬IsMax b)
  结论: Ioc a b subseteq Ioo a (succ b)
  证明: by
  gcongr
  exact lt_succ_of_not_isMax hb

@[to_dual Icc_pred_right_of_not_isMin]

Depends on / 依赖: lt_succ_of_not_isMax
-/
theorem Ioc_subset_Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioc a b subseteq Ioo a (succ b) := by
  gcongr
  exact lt_succ_of_not_isMax hb

@[to_dual Icc_pred_right_of_not_isMin]
/--
theorem `Icc_succ_left_of_not_isMax` / 定理 `Icc_succ_left_of_not_isMax`

English:
theorem Icc_succ_left_of_not_isMax
  given: (ha : ¬IsMax a)
  statement: Icc (succ a) b = Ioc a b
  proof: by
  rw [← Ici_inter_Iic]; rw [Ici_succ_of_not_isMax ha]; rw [Ioi_inter_Iic]

@[to_dual Ioc_pred_right_of_not_isMin]

中文:
定理 Icc_succ_left_of_not_isMax
  条件: (ha : ¬IsMax a)
  结论: Icc (succ a) b = Ioc a b
  证明: by
  rw [← Ici_inter_Iic]; rw [Ici_succ_of_not_isMax ha]; rw [Ioi_inter_Iic]

@[to_dual Ioc_pred_right_of_not_isMin]

Depends on / 依赖: Ici_inter_Iic, Ici_succ_of_not_isMax, Ioi_inter_Iic
-/
theorem Icc_succ_left_of_not_isMax (ha : ¬IsMax a) : Icc (succ a) b = Ioc a b := by
  rw [← Ici_inter_Iic]; rw [Ici_succ_of_not_isMax ha]; rw [Ioi_inter_Iic]

@[to_dual Ioc_pred_right_of_not_isMin]
/--
theorem `Ico_succ_left_of_not_isMax` / 定理 `Ico_succ_left_of_not_isMax`

English:
theorem Ico_succ_left_of_not_isMax
  given: (ha : ¬IsMax a)
  statement: Ico (succ a) b = Ioo a b
  proof: by
  rw [← Ici_inter_Iio]; rw [Ici_succ_of_not_isMax ha]; rw [Ioi_inter_Iio]

中文:
定理 Ico_succ_left_of_not_isMax
  条件: (ha : ¬IsMax a)
  结论: Ico (succ a) b = Ioo a b
  证明: by
  rw [← Ici_inter_Iio]; rw [Ici_succ_of_not_isMax ha]; rw [Ioi_inter_Iio]

Depends on / 依赖: Ici_inter_Iio, Ici_succ_of_not_isMax, Ioi_inter_Iio
-/
theorem Ico_succ_left_of_not_isMax (ha : ¬IsMax a) : Ico (succ a) b = Ioo a b := by
  rw [← Ici_inter_Iio]; rw [Ici_succ_of_not_isMax ha]; rw [Ioi_inter_Iio]

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual pred_lt]
/--
theorem `lt_succ` / 定理 `lt_succ`

English:
theorem lt_succ
  given: (a : α)
  statement: a < succ a
  proof: lt_succ_of_not_isMax not_isMax a

@[to_dual (attr := simp) pred_lt_of_le]

中文:
定理 lt_succ
  条件: (a : α)
  结论: a < succ a
  证明: lt_succ_of_not_isMax not_isMax a

@[to_dual (attr := simp) pred_lt_of_le]

Depends on / 依赖: lt_succ_of_not_isMax, not_isMax
-/
theorem lt_succ (a : α) : a < succ a :=
lt_succ_of_not_isMax not_isMax a

@[to_dual (attr := simp) pred_lt_of_le]
/--
theorem `lt_succ_of_le` / 定理 `lt_succ_of_le`

English:
theorem lt_succ_of_le
  statement: a <= b -> a < succ b
  proof: (lt_succ_of_le_of_not_isMax · <| not_isMax b)

@[to_dual (attr := simp) le_pred_iff]

中文:
定理 lt_succ_of_le
  结论: a <= b -> a < succ b
  证明: (lt_succ_of_le_of_not_isMax · <| not_isMax b)

@[to_dual (attr := simp) le_pred_iff]

Depends on / 依赖: lt_succ_of_le_of_not_isMax, not_isMax
-/
theorem lt_succ_of_le : a <= b -> a < succ b :=
  (lt_succ_of_le_of_not_isMax · <| not_isMax b)

@[to_dual (attr := simp) le_pred_iff]
/--
theorem `succ_le_iff` / 定理 `succ_le_iff`

English:
theorem succ_le_iff
  statement: succ a <= b ↔ a < b
  proof: succ_le_iff_of_not_isMax not_isMax a

@[to_dual (attr := gcongr)]

中文:
定理 succ_le_iff
  结论: succ a <= b ↔ a < b
  证明: succ_le_iff_of_not_isMax not_isMax a

@[to_dual (attr := gcongr)]

Depends on / 依赖: not_isMax, succ_le_iff_of_not_isMax
-/
theorem succ_le_iff : succ a <= b ↔ a < b :=
succ_le_iff_of_not_isMax not_isMax a

@[to_dual (attr := gcongr)]
/--
theorem `succ_lt_succ` / 定理 `succ_lt_succ`

English:
theorem succ_lt_succ
  given: (hab : a < b)
  statement: succ a < succ b
  proof: by simp [hab]

@[to_dual]

中文:
定理 succ_lt_succ
  条件: (hab : a < b)
  结论: succ a < succ b
  证明: by simp [hab]

@[to_dual]
-/
theorem succ_lt_succ (hab : a < b) : succ a < succ b := by simp [hab]

@[to_dual]
/--
theorem `succ_strictMono` / 定理 `succ_strictMono`

English:
theorem succ_strictMono
  statement: StrictMono (succ : α -> α)
  proof: fun _ _ => succ_lt_succ

@[to_dual pred_covBy]

中文:
定理 succ_strictMono
  结论: StrictMono (succ : α -> α)
  证明: fun _ _ => succ_lt_succ

@[to_dual pred_covBy]

Depends on / 依赖: succ_lt_succ
-/
theorem succ_strictMono : StrictMono (succ : α -> α) := fun _ _ => succ_lt_succ

@[to_dual pred_covBy]
/--
theorem `covBy_succ` / 定理 `covBy_succ`

English:
theorem covBy_succ
  given: (a : α)
  statement: a ⋖ succ a
  proof: covBy_succ_of_not_isMax not_isMax a

@[to_dual]

中文:
定理 covBy_succ
  条件: (a : α)
  结论: a ⋖ succ a
  证明: covBy_succ_of_not_isMax not_isMax a

@[to_dual]

Depends on / 依赖: covBy_succ_of_not_isMax, not_isMax
-/
theorem covBy_succ (a : α) : a ⋖ succ a :=
covBy_succ_of_not_isMax not_isMax a

@[to_dual]
/--
theorem `Iic_subset_Iio_succ` / 定理 `Iic_subset_Iio_succ`

English:
theorem Iic_subset_Iio_succ
  given: (a : α)
  statement: Iic a subseteq Iio (succ a)
  proof: by simp

@[to_dual (attr := simp)]

中文:
定理 Iic_subset_Iio_succ
  条件: (a : α)
  结论: Iic a subseteq Iio (succ a)
  证明: by simp

@[to_dual (attr := simp)]
-/
theorem Iic_subset_Iio_succ (a : α) : Iic a subseteq Iio (succ a) := by simp

@[to_dual (attr := simp)]
/--
theorem `Ici_succ` / 定理 `Ici_succ`

English:
theorem Ici_succ
  given: (a : α)
  statement: Ici (succ a) = Ioi a
  proof: Ici_succ_of_not_isMax not_isMax _

@[to_dual (attr := simp) Icc_subset_Ioc_pred_left]

中文:
定理 Ici_succ
  条件: (a : α)
  结论: Ici (succ a) = Ioi a
  证明: Ici_succ_of_not_isMax not_isMax _

@[to_dual (attr := simp) Icc_subset_Ioc_pred_left]

Depends on / 依赖: Ici_succ_of_not_isMax, not_isMax
-/
theorem Ici_succ (a : α) : Ici (succ a) = Ioi a :=
Ici_succ_of_not_isMax not_isMax _

@[to_dual (attr := simp) Icc_subset_Ioc_pred_left]
/--
theorem `Icc_subset_Ico_succ_right` / 定理 `Icc_subset_Ico_succ_right`

English:
theorem Icc_subset_Ico_succ_right
  given: (a b : α)
  statement: Icc a b subseteq Ico a (succ b)
  proof: Icc_subset_Ico_succ_right_of_not_isMax not_isMax _

@[to_dual (attr := simp) Ico_subset_Ioo_pred_left]

中文:
定理 Icc_subset_Ico_succ_right
  条件: (a b : α)
  结论: Icc a b subseteq Ico a (succ b)
  证明: Icc_subset_Ico_succ_right_of_not_isMax not_isMax _

@[to_dual (attr := simp) Ico_subset_Ioo_pred_left]

Depends on / 依赖: Icc_subset_Ico_succ_right_of_not_isMax, not_isMax
-/
theorem Icc_subset_Ico_succ_right (a b : α) : Icc a b subseteq Ico a (succ b) :=
Icc_subset_Ico_succ_right_of_not_isMax not_isMax _

@[to_dual (attr := simp) Ico_subset_Ioo_pred_left]
/--
theorem `Ioc_subset_Ioo_succ_right` / 定理 `Ioc_subset_Ioo_succ_right`

English:
theorem Ioc_subset_Ioo_succ_right
  given: (a b : α)
  statement: Ioc a b subseteq Ioo a (succ b)
  proof: Ioc_subset_Ioo_succ_right_of_not_isMax not_isMax _

@[to_dual (attr := simp) Icc_pred_right]

中文:
定理 Ioc_subset_Ioo_succ_right
  条件: (a b : α)
  结论: Ioc a b subseteq Ioo a (succ b)
  证明: Ioc_subset_Ioo_succ_right_of_not_isMax not_isMax _

@[to_dual (attr := simp) Icc_pred_right]

Depends on / 依赖: Ioc_subset_Ioo_succ_right_of_not_isMax, not_isMax, of_algebraMap_eq
-/
theorem Ioc_subset_Ioo_succ_right (a b : α) : Ioc a b subseteq Ioo a (succ b) :=
Ioc_subset_Ioo_succ_right_of_not_isMax not_isMax _

@[to_dual (attr := simp) Icc_pred_right]
/--
theorem `Icc_succ_left` / 定理 `Icc_succ_left`

English:
theorem Icc_succ_left
  given: (a b : α)
  statement: Icc (succ a) b = Ioc a b
  proof: Icc_succ_left_of_not_isMax not_isMax _

@[to_dual (attr := simp) Ioc_pred_right]

中文:
定理 Icc_succ_left
  条件: (a b : α)
  结论: Icc (succ a) b = Ioc a b
  证明: Icc_succ_left_of_not_isMax not_isMax _

@[to_dual (attr := simp) Ioc_pred_right]

Depends on / 依赖: I.ker_algebraMap_residueField.symm, Icc_succ_left_of_not_isMax, ker_algebraMap_residueField, not_isMax
-/
theorem Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b :=
Icc_succ_left_of_not_isMax not_isMax _

@[to_dual (attr := simp) Ioc_pred_right]
/--
theorem `Ico_succ_left` / 定理 `Ico_succ_left`

English:
theorem Ico_succ_left
  given: (a b : α)
  statement: Ico (succ a) b = Ioo a b
  proof: Ico_succ_left_of_not_isMax not_isMax _

中文:
定理 Ico_succ_left
  条件: (a b : α)
  结论: Ico (succ a) b = Ioo a b
  证明: Ico_succ_left_of_not_isMax not_isMax _

Depends on / 依赖: Ico_succ_left_of_not_isMax, not_isMax
-/
theorem Ico_succ_left (a b : α) : Ico (succ a) b = Ioo a b :=
Ico_succ_left_of_not_isMax not_isMax _

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α}

@[to_dual (attr := simp)]
/--
theorem `succ_eq_iff_isMax` / 定理 `succ_eq_iff_isMax`

English:
theorem succ_eq_iff_isMax
  statement: succ a = a ↔ IsMax a
  proof: ⟨fun h => max_of_succ_le h.le, fun h => h.eq_of_ge le_succ _⟩

@[to_dual]
alias ⟨_, _root_.IsMax.succ_eq⟩ := succ_eq_iff_isMax

@[to_dual le_iff_eq_or_le_pred']

中文:
定理 succ_eq_iff_isMax
  结论: succ a = a ↔ IsMax a
  证明: ⟨fun h => max_of_succ_le h.le, fun h => h.eq_of_ge le_succ _⟩

@[to_dual]
alias ⟨_, _root_.IsMax.succ_eq⟩ := succ_eq_iff_isMax

@[to_dual le_iff_eq_or_le_pred']

Depends on / 依赖: eq_of_ge, h.eq_of_ge, h.le, le_succ, max_of_succ_le
-/
theorem succ_eq_iff_isMax : succ a = a ↔ IsMax a :=
⟨fun h => max_of_succ_le h.le, fun h => h.eq_of_ge le_succ _⟩

@[to_dual]
alias ⟨_, _root_.IsMax.succ_eq⟩ := succ_eq_iff_isMax

@[to_dual le_iff_eq_or_le_pred']
/--
lemma `le_iff_eq_or_succ_le` / 引理 `le_iff_eq_or_succ_le`

English:
lemma le_iff_eq_or_succ_le
  statement: a <= b ↔ a = b ∨ succ a <= b
  proof: by
  by_cases ha : IsMax a
  · simpa [ha.succ_eq] using le_of_eq
  · rw [succ_le_iff_of_not_isMax ha, le_iff_eq_or_lt]

@[to_dual le_iff_eq_or_le_pred]

中文:
引理 le_iff_eq_or_succ_le
  结论: a <= b ↔ a = b ∨ succ a <= b
  证明: by
  by_cases ha : IsMax a
  · simpa [ha.succ_eq] using le_of_eq
  · rw [succ_le_iff_of_not_isMax ha, le_iff_eq_or_lt]

@[to_dual le_iff_eq_or_le_pred]

Depends on / 依赖: ha.succ_eq, isUnit_iff_ne_zero, isUnit_iff_ne_zero.mpr, le_iff_eq_or_lt, le_of_eq, succ_eq, succ_le_iff_of_not_isMax
-/
lemma le_iff_eq_or_succ_le : a <= b ↔ a = b ∨ succ a <= b := by
  by_cases ha : IsMax a
  · simpa [ha.succ_eq] using le_of_eq
  · rw [succ_le_iff_of_not_isMax ha, le_iff_eq_or_lt]

@[to_dual le_iff_eq_or_le_pred]
/--
lemma `le_iff_eq_or_succ_le'` / 引理 `le_iff_eq_or_succ_le'`

English:
lemma le_iff_eq_or_succ_le'
  statement: a <= b ↔ b = a ∨ succ a <= b
  proof: by
  rw [eq_comm]
  exact le_iff_eq_or_succ_le

@[to_dual le_and_pred_le_iff]

中文:
引理 le_iff_eq_or_succ_le'
  结论: a <= b ↔ b = a ∨ succ a <= b
  证明: by
  rw [eq_comm]
  exact le_iff_eq_or_succ_le

@[to_dual le_and_pred_le_iff]

Depends on / 依赖: eq_comm, le_iff_eq_or_succ_le
-/
lemma le_iff_eq_or_succ_le' : a <= b ↔ b = a ∨ succ a <= b := by
  rw [eq_comm]
  exact le_iff_eq_or_succ_le

@[to_dual le_and_pred_le_iff]
/--
theorem `le_and_le_succ_iff` / 定理 `le_and_le_succ_iff`

English:
theorem le_and_le_succ_iff
  statement: a <= b ∧ b <= succ a ↔ b = a ∨ b = succ a
  proof: by
  refine ⟨fun h => or_iff_not_imp_left.2 fun hba : b != a =>
    h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm), ?_⟩
  rintro (rfl | rfl)
  · exact ⟨le_rfl, le_succ b⟩
  · exact ⟨le_succ a, le_rfl⟩

@[to_dual pred_le_and_le_iff]

中文:
定理 le_and_le_succ_iff
  结论: a <= b ∧ b <= succ a ↔ b = a ∨ b = succ a
  证明: by
  refine ⟨fun h => or_iff_not_imp_left.2 fun hba : b != a =>
    h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm), ?_⟩
  rintro (rfl | rfl)
  · exact ⟨le_rfl, le_succ b⟩
  · exact ⟨le_succ a, le_rfl⟩

@[to_dual pred_le_and_le_iff]

Depends on / 依赖: antisymm, hba.symm, le_rfl, le_succ, lt_of_ne, or_iff_not_imp_left, succ_le_of_lt
-/
theorem le_and_le_succ_iff : a <= b ∧ b <= succ a ↔ b = a ∨ b = succ a := by
  refine ⟨fun h => or_iff_not_imp_left.2 fun hba : b != a =>
    h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm), ?_⟩
  rintro (rfl | rfl)
  · exact ⟨le_rfl, le_succ b⟩
  · exact ⟨le_succ a, le_rfl⟩

@[to_dual pred_le_and_le_iff]
/--
theorem `le_succ_and_le_iff` / 定理 `le_succ_and_le_iff`

English:
theorem le_succ_and_le_iff
  statement: b <= succ a ∧ a <= b ↔ b = a ∨ b = succ a
  proof: by
  rw [and_comm]
  exact le_and_le_succ_iff

中文:
定理 le_succ_and_le_iff
  结论: b <= succ a ∧ a <= b ↔ b = a ∨ b = succ a
  证明: by
  rw [and_comm]
  exact le_and_le_succ_iff

Depends on / 依赖: and_comm, le_and_le_succ_iff
-/
theorem le_succ_and_le_iff : b <= succ a ∧ a <= b ↔ b = a ∨ b = succ a := by
  rw [and_comm]
  exact le_and_le_succ_iff

/-- See also `Order.le_succ_of_wcovBy`. -/
@[to_dual /-- See also `Order.pred_le_of_wcovBy`. -/]
/--
lemma `succ_eq_of_covBy` / 引理 `succ_eq_of_covBy`

English:
lemma succ_eq_of_covBy
  given: (h : a ⋖ b)
  statement: succ a = b
  proof: (succ_le_of_lt h.lt).antisymm h.wcovBy.le_succ

@[to_dual]
alias _root_.CovBy.succ_eq := succ_eq_of_covBy

@[to_dual]

中文:
引理 succ_eq_of_covBy
  条件: (h : a ⋖ b)
  结论: succ a = b
  证明: (succ_le_of_lt h.lt).antisymm h.wcovBy.le_succ

@[to_dual]
alias _root_.CovBy.succ_eq := succ_eq_of_covBy

@[to_dual]

Depends on / 依赖: antisymm, h.lt, h.wcovBy.le_succ, le_succ, succ_le_of_lt, wcovBy
-/
lemma succ_eq_of_covBy (h : a ⋖ b) : succ a = b := (succ_le_of_lt h.lt).antisymm h.wcovBy.le_succ

@[to_dual]
alias _root_.CovBy.succ_eq := succ_eq_of_covBy

@[to_dual]
/--
theorem `_root_.OrderIso.map_succ` / 定理 `_root_.OrderIso.map_succ`

English:
theorem _root_.OrderIso.map_succ
  given: [PartialOrder β] [SuccOrder β] (f : α ≃o β) (a : α)
  proof: by
  by_cases h : IsMax a
  · rw [h.succ_eq, (f.isMax_apply.2 h).succ_eq]
  · exact ((apply_covBy_apply_iff f).2 <| covBy_succ_of_not_isMax h).succ_eq.symm

中文:
定理 _root_.OrderIso.map_succ
  条件: [PartialOrder β] [SuccOrder β] (f : α ≃o β) (a : α)
  证明: by
  by_cases h : IsMax a
  · rw [h.succ_eq, (f.isMax_apply.2 h).succ_eq]
  · exact ((apply_covBy_apply_iff f).2 <| covBy_succ_of_not_isMax h).succ_eq.symm

Depends on / 依赖: Algebra, Algebra.linearMap, I.algebraMap_residueField_surjective, algebraMap_residueField_surjective, apply_covBy_apply_iff, covBy_succ_of_not_isMax, f.isMax_apply, h.succ_eq, isMax_apply, linearMap, of_surjective, succ_eq, succ_eq.symm
-/
theorem _root_.OrderIso.map_succ [PartialOrder β] [SuccOrder β] (f : α ≃o β) (a : α) :
    f (succ a) = succ (f a) := by
  by_cases h : IsMax a
  · rw [h.succ_eq, (f.isMax_apply.2 h).succ_eq]
  · exact ((apply_covBy_apply_iff f).2 <| covBy_succ_of_not_isMax h).succ_eq.symm

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
/--
theorem `succ_eq_iff_covBy` / 定理 `succ_eq_iff_covBy`

English:
theorem succ_eq_iff_covBy
  statement: succ a = b ↔ a ⋖ b
  proof: ⟨by rintro rfl; exact covBy_succ _, CovBy.succ_eq⟩

中文:
定理 succ_eq_iff_covBy
  结论: succ a = b ↔ a ⋖ b
  证明: ⟨by rintro rfl; exact covBy_succ _, CovBy.succ_eq⟩

Depends on / 依赖: CovBy.succ_eq, covBy_succ, succ_eq
-/
theorem succ_eq_iff_covBy : succ a = b ↔ a ⋖ b :=
  ⟨by rintro rfl; exact covBy_succ _, CovBy.succ_eq⟩

end NoMaxOrder

section OrderTop

variable [OrderTop α]

@[to_dual (attr := simp)]
/--
theorem `succ_top` / 定理 `succ_top`

English:
theorem succ_top
  statement: succ (⊤ : α) = ⊤
  proof: by
  rw [succ_eq_iff_isMax]; rw [isMax_iff_eq_top]

@[to_dual le_pred_iff_eq_bot]

中文:
定理 succ_top
  结论: succ (⊤ : α) = ⊤
  证明: by
  rw [succ_eq_iff_isMax]; rw [isMax_iff_eq_top]

@[to_dual le_pred_iff_eq_bot]

Depends on / 依赖: isMax_iff_eq_top, succ_eq_iff_isMax
-/
theorem succ_top : succ (⊤ : α) = ⊤ := by
  rw [succ_eq_iff_isMax]; rw [isMax_iff_eq_top]

@[to_dual le_pred_iff_eq_bot]
/--
theorem `succ_le_iff_eq_top` / 定理 `succ_le_iff_eq_top`

English:
theorem succ_le_iff_eq_top
  statement: succ a <= a ↔ a = ⊤
  proof: succ_le_iff_isMax.trans isMax_iff_eq_top

@[to_dual pred_lt_iff_ne_bot]

中文:
定理 succ_le_iff_eq_top
  结论: succ a <= a ↔ a = ⊤
  证明: succ_le_iff_isMax.trans isMax_iff_eq_top

@[to_dual pred_lt_iff_ne_bot]

Depends on / 依赖: isMax_iff_eq_top, succ_le_iff_isMax, succ_le_iff_isMax.trans
-/
theorem succ_le_iff_eq_top : succ a <= a ↔ a = ⊤ :=
  succ_le_iff_isMax.trans isMax_iff_eq_top

@[to_dual pred_lt_iff_ne_bot]
/--
theorem `lt_succ_iff_ne_top` / 定理 `lt_succ_iff_ne_top`

English:
theorem lt_succ_iff_ne_top
  statement: a < succ a ↔ a != ⊤
  proof: lt_succ_iff_not_isMax.trans not_isMax_iff_ne_top

中文:
定理 lt_succ_iff_ne_top
  结论: a < succ a ↔ a != ⊤
  证明: lt_succ_iff_not_isMax.trans not_isMax_iff_ne_top

Depends on / 依赖: lt_succ_iff_not_isMax, lt_succ_iff_not_isMax.trans, not_isMax_iff_ne_top
-/
theorem lt_succ_iff_ne_top : a < succ a ↔ a != ⊤ :=
  lt_succ_iff_not_isMax.trans not_isMax_iff_ne_top

end OrderTop

section OrderBot

variable [OrderBot α] [Nontrivial α]

@[to_dual pred_lt_top]
/--
theorem `bot_lt_succ` / 定理 `bot_lt_succ`

English:
theorem bot_lt_succ
  given: (a : α)
  statement: ⊥ < succ a
  proof: (lt_succ_of_not_isMax not_isMax_bot).trans_le succ_le_succ bot_le

@[to_dual]

中文:
定理 bot_lt_succ
  条件: (a : α)
  结论: ⊥ < succ a
  证明: (lt_succ_of_not_isMax not_isMax_bot).trans_le succ_le_succ bot_le

@[to_dual]

Depends on / 依赖: bot_le, lt_succ_of_not_isMax, not_isMax_bot, succ_le_succ, trans_le
-/
theorem bot_lt_succ (a : α) : ⊥ < succ a :=
(lt_succ_of_not_isMax not_isMax_bot).trans_le succ_le_succ bot_le

@[to_dual]
/--
theorem `succ_ne_bot` / 定理 `succ_ne_bot`

English:
theorem succ_ne_bot
  given: (a : α)
  statement: succ a != ⊥
  proof: (bot_lt_succ a).ne'

中文:
定理 succ_ne_bot
  条件: (a : α)
  结论: succ a != ⊥
  证明: (bot_lt_succ a).ne'

Depends on / 依赖: bot_lt_succ
-/
theorem succ_ne_bot (a : α) : succ a != ⊥ :=
  (bot_lt_succ a).ne'

end OrderBot

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] {a b : α}

/--
lemma `succ_max` / 引理 `succ_max`

English:
lemma succ_max
  given: (a b : α)
  statement: succ (max a b) = max (succ a) (succ b)
  proof: succ_mono.map_max

中文:
引理 succ_max
  条件: (a b : α)
  结论: succ (max a b) = max (succ a) (succ b)
  证明: succ_mono.map_max
-/
@[to_dual] lemma succ_max (a b : α) : succ (max a b) = max (succ a) (succ b) := succ_mono.map_max
/--
lemma `succ_min` / 引理 `succ_min`

English:
lemma succ_min
  given: (a b : α)
  statement: succ (min a b) = min (succ a) (succ b)
  proof: succ_mono.map_min

@[to_dual le_of_pred_lt]

中文:
引理 succ_min
  条件: (a b : α)
  结论: succ (min a b) = min (succ a) (succ b)
  证明: succ_mono.map_min

@[to_dual le_of_pred_lt]

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime
-/
@[to_dual] lemma succ_min (a b : α) : succ (min a b) = min (succ a) (succ b) := succ_mono.map_min

@[to_dual le_of_pred_lt]
/--
theorem `le_of_lt_succ` / 定理 `le_of_lt_succ`

English:
theorem le_of_lt_succ
  given: {a b : α}
  statement: a < succ b -> a <= b
  proof: by
  contrapose!
  exact succ_le_of_lt

@[to_dual pred_lt_iff_of_not_isMin]

中文:
定理 le_of_lt_succ
  条件: {a b : α}
  结论: a < succ b -> a <= b
  证明: by
  contrapose!
  exact succ_le_of_lt

@[to_dual pred_lt_iff_of_not_isMin]

Depends on / 依赖: contrapose, succ_le_of_lt
-/
theorem le_of_lt_succ {a b : α} : a < succ b -> a <= b := by
  contrapose!
  exact succ_le_of_lt

@[to_dual pred_lt_iff_of_not_isMin]
/--
theorem `lt_succ_iff_of_not_isMax` / 定理 `lt_succ_iff_of_not_isMax`

English:
theorem lt_succ_iff_of_not_isMax
  given: (ha : ¬IsMax a)
  statement: b < succ a ↔ b <= a
  proof: by
  contrapose!
  exact succ_le_iff_of_not_isMax ha

@[to_dual pred_lt_iff_of_not_isMin']

中文:
定理 lt_succ_iff_of_not_isMax
  条件: (ha : ¬IsMax a)
  结论: b < succ a ↔ b <= a
  证明: by
  contrapose!
  exact succ_le_iff_of_not_isMax ha

@[to_dual pred_lt_iff_of_not_isMin']

Depends on / 依赖: contrapose, succ_le_iff_of_not_isMax
-/
theorem lt_succ_iff_of_not_isMax (ha : ¬IsMax a) : b < succ a ↔ b <= a := by
  contrapose!
  exact succ_le_iff_of_not_isMax ha

@[to_dual pred_lt_iff_of_not_isMin']
/--
theorem `lt_succ_iff_of_not_isMax'` / 定理 `lt_succ_iff_of_not_isMax'`

English:
theorem lt_succ_iff_of_not_isMax'
  given: (hb : ¬IsMax b)
  statement: b < succ a ↔ b <= a
  proof: by
  contrapose!
  exact succ_le_iff_of_not_isMax' hb

@[to_dual (reorder := ha hb)]

中文:
定理 lt_succ_iff_of_not_isMax'
  条件: (hb : ¬IsMax b)
  结论: b < succ a ↔ b <= a
  证明: by
  contrapose!
  exact succ_le_iff_of_not_isMax' hb

@[to_dual (reorder := ha hb)]

Depends on / 依赖: contrapose, succ_le_iff_of_not_isMax
-/
theorem lt_succ_iff_of_not_isMax' (hb : ¬IsMax b) : b < succ a ↔ b <= a := by
  contrapose!
  exact succ_le_iff_of_not_isMax' hb

@[to_dual (reorder := ha hb)]
/--
theorem `succ_lt_succ_iff_of_not_isMax` / 定理 `succ_lt_succ_iff_of_not_isMax`

English:
theorem succ_lt_succ_iff_of_not_isMax
  given: (ha : ¬IsMax a) (hb : ¬IsMax b)
  proof: by
  rw [lt_succ_iff_of_not_isMax hb]; rw [succ_le_iff_of_not_isMax ha]

@[to_dual (reorder := ha hb)]

中文:
定理 succ_lt_succ_iff_of_not_isMax
  条件: (ha : ¬IsMax a) (hb : ¬IsMax b)
  证明: by
  rw [lt_succ_iff_of_not_isMax hb]; rw [succ_le_iff_of_not_isMax ha]

@[to_dual (reorder := ha hb)]

Depends on / 依赖: lt_succ_iff_of_not_isMax, succ_le_iff_of_not_isMax
-/
theorem succ_lt_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a < succ b ↔ a < b := by
  rw [lt_succ_iff_of_not_isMax hb]; rw [succ_le_iff_of_not_isMax ha]

@[to_dual (reorder := ha hb)]
/--
theorem `succ_le_succ_iff_of_not_isMax` / 定理 `succ_le_succ_iff_of_not_isMax`

English:
theorem succ_le_succ_iff_of_not_isMax
  given: (ha : ¬IsMax a) (hb : ¬IsMax b)
  proof: by
  rw [succ_le_iff_of_not_isMax ha]; rw [lt_succ_iff_of_not_isMax hb]

@[to_dual]

中文:
定理 succ_le_succ_iff_of_not_isMax
  条件: (ha : ¬IsMax a) (hb : ¬IsMax b)
  证明: by
  rw [succ_le_iff_of_not_isMax ha]; rw [lt_succ_iff_of_not_isMax hb]

@[to_dual]

Depends on / 依赖: lt_succ_iff_of_not_isMax, succ_le_iff_of_not_isMax
-/
theorem succ_le_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a <= succ b ↔ a <= b := by
  rw [succ_le_iff_of_not_isMax ha]; rw [lt_succ_iff_of_not_isMax hb]

@[to_dual]
/--
theorem `Iio_succ_of_not_isMax` / 定理 `Iio_succ_of_not_isMax`

English:
theorem Iio_succ_of_not_isMax
  given: (ha : ¬IsMax a)
  statement: Iio (succ a) = Iic a
  proof: Set.ext fun _ => lt_succ_iff_of_not_isMax ha

@[to_dual Ioc_pred_left_of_not_isMin]

中文:
定理 Iio_succ_of_not_isMax
  条件: (ha : ¬IsMax a)
  结论: Iio (succ a) = Iic a
  证明: Set.ext fun _ => lt_succ_iff_of_not_isMax ha

@[to_dual Ioc_pred_left_of_not_isMin]

Depends on / 依赖: Set.ext, lt_succ_iff_of_not_isMax
-/
theorem Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio (succ a) = Iic a :=
  Set.ext fun _ => lt_succ_iff_of_not_isMax ha

@[to_dual Ioc_pred_left_of_not_isMin]
/--
theorem `Ico_succ_right_of_not_isMax` / 定理 `Ico_succ_right_of_not_isMax`

English:
theorem Ico_succ_right_of_not_isMax
  given: (hb : ¬IsMax b)
  statement: Ico a (succ b) = Icc a b
  proof: by
  rw [← Ici_inter_Iio]; rw [Iio_succ_of_not_isMax hb]; rw [Ici_inter_Iic]

@[to_dual Ioo_pred_left_of_not_isMin]

中文:
定理 Ico_succ_right_of_not_isMax
  条件: (hb : ¬IsMax b)
  结论: Ico a (succ b) = Icc a b
  证明: by
  rw [← Ici_inter_Iio]; rw [Iio_succ_of_not_isMax hb]; rw [Ici_inter_Iic]

@[to_dual Ioo_pred_left_of_not_isMin]

Depends on / 依赖: Ici_inter_Iic, Ici_inter_Iio, Iio_succ_of_not_isMax
-/
theorem Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Ico a (succ b) = Icc a b := by
  rw [← Ici_inter_Iio]; rw [Iio_succ_of_not_isMax hb]; rw [Ici_inter_Iic]

@[to_dual Ioo_pred_left_of_not_isMin]
/--
theorem `Ioo_succ_right_of_not_isMax` / 定理 `Ioo_succ_right_of_not_isMax`

English:
theorem Ioo_succ_right_of_not_isMax
  given: (hb : ¬IsMax b)
  statement: Ioo a (succ b) = Ioc a b
  proof: by
  rw [← Ioi_inter_Iio]; rw [Iio_succ_of_not_isMax hb]; rw [Ioi_inter_Iic]

@[to_dual]

中文:
定理 Ioo_succ_right_of_not_isMax
  条件: (hb : ¬IsMax b)
  结论: Ioo a (succ b) = Ioc a b
  证明: by
  rw [← Ioi_inter_Iio]; rw [Iio_succ_of_not_isMax hb]; rw [Ioi_inter_Iic]

@[to_dual]

Depends on / 依赖: Iio_succ_of_not_isMax, Ioi_inter_Iic, Ioi_inter_Iio
-/
theorem Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioo a (succ b) = Ioc a b := by
  rw [← Ioi_inter_Iio]; rw [Iio_succ_of_not_isMax hb]; rw [Ioi_inter_Iic]

@[to_dual]
/--
theorem `succ_eq_succ_iff_of_not_isMax` / 定理 `succ_eq_succ_iff_of_not_isMax`

English:
theorem succ_eq_succ_iff_of_not_isMax
  given: (ha : ¬IsMax a) (hb : ¬IsMax b)
  proof: by
  rw [eq_iff_le_not_lt]; rw [eq_iff_le_not_lt]; rw [succ_le_succ_iff_of_not_isMax ha hb]; rw [succ_lt_succ_iff_of_not_isMax ha hb]

@[to_dual pred_le_iff_eq_or_le]

中文:
定理 succ_eq_succ_iff_of_not_isMax
  条件: (ha : ¬IsMax a) (hb : ¬IsMax b)
  证明: by
  rw [eq_iff_le_not_lt]; rw [eq_iff_le_not_lt]; rw [succ_le_succ_iff_of_not_isMax ha hb]; rw [succ_lt_succ_iff_of_not_isMax ha hb]

@[to_dual pred_le_iff_eq_or_le]

Depends on / 依赖: eq_iff_le_not_lt, succ_le_succ_iff_of_not_isMax, succ_lt_succ_iff_of_not_isMax
-/
theorem succ_eq_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a = succ b ↔ a = b := by
  rw [eq_iff_le_not_lt]; rw [eq_iff_le_not_lt]; rw [succ_le_succ_iff_of_not_isMax ha hb]; rw [succ_lt_succ_iff_of_not_isMax ha hb]

@[to_dual pred_le_iff_eq_or_le]
/--
theorem `le_succ_iff_eq_or_le` / 定理 `le_succ_iff_eq_or_le`

English:
theorem le_succ_iff_eq_or_le
  statement: a <= succ b ↔ a = succ b ∨ a <= b
  proof: by
  by_cases hb : IsMax b
  · rw [hb.succ_eq, or_iff_right_of_imp le_of_eq]
  · rw [← lt_succ_iff_of_not_isMax hb, le_iff_eq_or_lt]

@[to_dual pred_lt_iff_eq_or_lt_of_not_isMin]

中文:
定理 le_succ_iff_eq_or_le
  结论: a <= succ b ↔ a = succ b ∨ a <= b
  证明: by
  by_cases hb : IsMax b
  · rw [hb.succ_eq, or_iff_right_of_imp le_of_eq]
  · rw [← lt_succ_iff_of_not_isMax hb, le_iff_eq_or_lt]

@[to_dual pred_lt_iff_eq_or_lt_of_not_isMin]

Depends on / 依赖: hb.succ_eq, le_iff_eq_or_lt, le_of_eq, lt_succ_iff_of_not_isMax, or_iff_right_of_imp, succ_eq
-/
theorem le_succ_iff_eq_or_le : a <= succ b ↔ a = succ b ∨ a <= b := by
  by_cases hb : IsMax b
  · rw [hb.succ_eq, or_iff_right_of_imp le_of_eq]
  · rw [← lt_succ_iff_of_not_isMax hb, le_iff_eq_or_lt]

@[to_dual pred_lt_iff_eq_or_lt_of_not_isMin]
/--
theorem `lt_succ_iff_eq_or_lt_of_not_isMax` / 定理 `lt_succ_iff_eq_or_lt_of_not_isMax`

English:
theorem lt_succ_iff_eq_or_lt_of_not_isMax
  given: (hb : ¬IsMax b)
  statement: a < succ b ↔ a = b ∨ a < b
  proof: (lt_succ_iff_of_not_isMax hb).trans le_iff_eq_or_lt

@[to_dual]

中文:
定理 lt_succ_iff_eq_or_lt_of_not_isMax
  条件: (hb : ¬IsMax b)
  结论: a < succ b ↔ a = b ∨ a < b
  证明: (lt_succ_iff_of_not_isMax hb).trans le_iff_eq_or_lt

@[to_dual]

Depends on / 依赖: le_iff_eq_or_lt, lt_succ_iff_of_not_isMax
-/
theorem lt_succ_iff_eq_or_lt_of_not_isMax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b :=
  (lt_succ_iff_of_not_isMax hb).trans le_iff_eq_or_lt

@[to_dual]
/--
theorem `not_isMin_succ` / 定理 `not_isMin_succ`

English:
theorem not_isMin_succ
  given: [Nontrivial α] (a : α)
  statement: ¬ IsMin (succ a)
  proof: by
  obtain ha | ha := (le_succ a).eq_or_lt
  · exact (ha ▸ succ_eq_iff_isMax.1 ha.symm).not_isMin
  · exact not_isMin_of_lt ha

@[to_dual]

中文:
定理 not_isMin_succ
  条件: [Nontrivial α] (a : α)
  结论: ¬ IsMin (succ a)
  证明: by
  obtain ha | ha := (le_succ a).eq_or_lt
  · exact (ha ▸ succ_eq_iff_isMax.1 ha.symm).not_isMin
  · exact not_isMin_of_lt ha

@[to_dual]

Depends on / 依赖: eq_or_lt, ha.symm, le_succ, not_isMin, not_isMin_of_lt, succ_eq_iff_isMax
-/
theorem not_isMin_succ [Nontrivial α] (a : α) : ¬ IsMin (succ a) := by
  obtain ha | ha := (le_succ a).eq_or_lt
  · exact (ha ▸ succ_eq_iff_isMax.1 ha.symm).not_isMin
  · exact not_isMin_of_lt ha

@[to_dual]
/--
theorem `Iic_succ` / 定理 `Iic_succ`

English:
theorem Iic_succ
  given: (a : α)
  statement: Iic (succ a) = insert (succ a) (Iic a)
  proof: ext fun _ => le_succ_iff_eq_or_le

@[to_dual Icc_pred_left]

中文:
定理 Iic_succ
  条件: (a : α)
  结论: Iic (succ a) = insert (succ a) (Iic a)
  证明: ext fun _ => le_succ_iff_eq_or_le

@[to_dual Icc_pred_left]

Depends on / 依赖: le_succ_iff_eq_or_le
-/
theorem Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a) :=
  ext fun _ => le_succ_iff_eq_or_le

@[to_dual Icc_pred_left]
/--
theorem `Icc_succ_right` / 定理 `Icc_succ_right`

English:
theorem Icc_succ_right
  given: (h : a <= succ b)
  statement: Icc a (succ b) = insert (succ b) (Icc a b)
  proof: by
  simp_rw [← Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]

@[to_dual Ico_pred_left]

中文:
定理 Icc_succ_right
  条件: (h : a <= succ b)
  结论: Icc a (succ b) = insert (succ b) (Icc a b)
  证明: by
  simp_rw [← Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]

@[to_dual Ico_pred_left]

Depends on / 依赖: Ici_inter_Iic, Iic_succ, inter_insert_of_mem, mem_Ici, simp_rw
-/
theorem Icc_succ_right (h : a <= succ b) : Icc a (succ b) = insert (succ b) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]

@[to_dual Ico_pred_left]
/--
theorem `Ioc_succ_right` / 定理 `Ioc_succ_right`

English:
theorem Ioc_succ_right
  given: (h : a < succ b)
  statement: Ioc a (succ b) = insert (succ b) (Ioc a b)
  proof: by
  simp_rw [← Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]

@[to_dual]

中文:
定理 Ioc_succ_right
  条件: (h : a < succ b)
  结论: Ioc a (succ b) = insert (succ b) (Ioc a b)
  证明: by
  simp_rw [← Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]

@[to_dual]

Depends on / 依赖: Iic_succ, Ioi_inter_Iic, inter_insert_of_mem, mem_Ioi, simp_rw
-/
theorem Ioc_succ_right (h : a < succ b) : Ioc a (succ b) = insert (succ b) (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]

@[to_dual]
/--
theorem `Iio_succ_eq_insert_of_not_isMax` / 定理 `Iio_succ_eq_insert_of_not_isMax`

English:
theorem Iio_succ_eq_insert_of_not_isMax
  given: (h : ¬IsMax a)
  statement: Iio (succ a) = insert a (Iio a)
  proof: ext fun _ => lt_succ_iff_eq_or_lt_of_not_isMax h

@[to_dual Ioc_pred_left_eq_insert_of_not_isMin]

中文:
定理 Iio_succ_eq_insert_of_not_isMax
  条件: (h : ¬IsMax a)
  结论: Iio (succ a) = insert a (Iio a)
  证明: ext fun _ => lt_succ_iff_eq_or_lt_of_not_isMax h

@[to_dual Ioc_pred_left_eq_insert_of_not_isMin]

Depends on / 依赖: lt_succ_iff_eq_or_lt_of_not_isMax
-/
theorem Iio_succ_eq_insert_of_not_isMax (h : ¬IsMax a) : Iio (succ a) = insert a (Iio a) :=
  ext fun _ => lt_succ_iff_eq_or_lt_of_not_isMax h

@[to_dual Ioc_pred_left_eq_insert_of_not_isMin]
/--
theorem `Ico_succ_right_eq_insert_of_not_isMax` / 定理 `Ico_succ_right_eq_insert_of_not_isMax`

English:
theorem Ico_succ_right_eq_insert_of_not_isMax
  given: (h₁ : a <= b) (h₂ : ¬IsMax b)
  proof: by
  simp_rw [← Iio_inter_Ici, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ici.2 h₁)]

@[to_dual Ioo_pred_left_eq_insert_of_not_isMin]

中文:
定理 Ico_succ_right_eq_insert_of_not_isMax
  条件: (h₁ : a <= b) (h₂ : ¬IsMax b)
  证明: by
  simp_rw [← Iio_inter_Ici, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ici.2 h₁)]

@[to_dual Ioo_pred_left_eq_insert_of_not_isMin]

Depends on / 依赖: Iio_inter_Ici, Iio_succ_eq_insert_of_not_isMax, insert_inter_of_mem, mem_Ici, simp_rw
-/
theorem Ico_succ_right_eq_insert_of_not_isMax (h₁ : a <= b) (h₂ : ¬IsMax b) :
    Ico a (succ b) = insert b (Ico a b) := by
  simp_rw [← Iio_inter_Ici, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ici.2 h₁)]

@[to_dual Ioo_pred_left_eq_insert_of_not_isMin]
/--
theorem `Ioo_succ_right_eq_insert_of_not_isMax` / 定理 `Ioo_succ_right_eq_insert_of_not_isMax`

English:
theorem Ioo_succ_right_eq_insert_of_not_isMax
  given: (h₁ : a < b) (h₂ : ¬IsMax b)
  proof: by
  simp_rw [← Iio_inter_Ioi, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]

中文:
定理 Ioo_succ_right_eq_insert_of_not_isMax
  条件: (h₁ : a < b) (h₂ : ¬IsMax b)
  证明: by
  simp_rw [← Iio_inter_Ioi, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]

Depends on / 依赖: Iio_inter_Ioi, Iio_succ_eq_insert_of_not_isMax, insert_inter_of_mem, mem_Ioi, simp_rw
-/
theorem Ioo_succ_right_eq_insert_of_not_isMax (h₁ : a < b) (h₂ : ¬IsMax b) :
    Ioo a (succ b) = insert b (Ioo a b) := by
  simp_rw [← Iio_inter_Ioi, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual (attr := simp) pred_lt_iff]
/--
theorem `lt_succ_iff` / 定理 `lt_succ_iff`

English:
theorem lt_succ_iff
  statement: a < succ b ↔ a <= b
  proof: lt_succ_iff_of_not_isMax not_isMax b

中文:
定理 lt_succ_iff
  结论: a < succ b ↔ a <= b
  证明: lt_succ_iff_of_not_isMax not_isMax b

Depends on / 依赖: lt_succ_iff_of_not_isMax, not_isMax
-/
theorem lt_succ_iff : a < succ b ↔ a <= b :=
lt_succ_iff_of_not_isMax not_isMax b

/--
theorem `succ_le_succ_iff` / 定理 `succ_le_succ_iff`

English:
theorem succ_le_succ_iff
  statement: succ a <= succ b ↔ a <= b
  proof: by simp

中文:
定理 succ_le_succ_iff
  结论: succ a <= succ b ↔ a <= b
  证明: by simp
-/
@[to_dual] theorem succ_le_succ_iff : succ a <= succ b ↔ a <= b := by simp
/--
theorem `succ_lt_succ_iff` / 定理 `succ_lt_succ_iff`

English:
theorem succ_lt_succ_iff
  statement: succ a < succ b ↔ a < b
  proof: by simp

@[to_dual] alias ⟨le_of_succ_le_succ, _⟩ := succ_le_succ_iff
@[to_dual] alias ⟨lt_of_succ_lt_succ, _⟩ := succ_lt_succ_iff

中文:
定理 succ_lt_succ_iff
  结论: succ a < succ b ↔ a < b
  证明: by simp

@[to_dual] alias ⟨le_of_succ_le_succ, _⟩ := succ_le_succ_iff
@[to_dual] alias ⟨lt_of_succ_lt_succ, _⟩ := succ_lt_succ_iff
-/
@[to_dual] theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := by simp

@[to_dual] alias ⟨le_of_succ_le_succ, _⟩ := succ_le_succ_iff
@[to_dual] alias ⟨lt_of_succ_lt_succ, _⟩ := succ_lt_succ_iff

-- TODO: prove for a succ-archimedean non-linear order with bottom
@[to_dual (attr := simp)]
/--
theorem `Iio_succ` / 定理 `Iio_succ`

English:
theorem Iio_succ
  given: (a : α)
  statement: Iio (succ a) = Iic a
  proof: Iio_succ_of_not_isMax not_isMax _

@[to_dual (attr := simp) Ioc_pred_left]

中文:
定理 Iio_succ
  条件: (a : α)
  结论: Iio (succ a) = Iic a
  证明: Iio_succ_of_not_isMax not_isMax _

@[to_dual (attr := simp) Ioc_pred_left]

Depends on / 依赖: Iio_succ_of_not_isMax, not_isMax
-/
theorem Iio_succ (a : α) : Iio (succ a) = Iic a :=
Iio_succ_of_not_isMax not_isMax _

@[to_dual (attr := simp) Ioc_pred_left]
/--
theorem `Ico_succ_right` / 定理 `Ico_succ_right`

English:
theorem Ico_succ_right
  given: (a b : α)
  statement: Ico a (succ b) = Icc a b
  proof: Ico_succ_right_of_not_isMax not_isMax _

中文:
定理 Ico_succ_right
  条件: (a b : α)
  结论: Ico a (succ b) = Icc a b
  证明: Ico_succ_right_of_not_isMax not_isMax _

Depends on / 依赖: Ico_succ_right_of_not_isMax, not_isMax
-/
theorem Ico_succ_right (a b : α) : Ico a (succ b) = Icc a b :=
Ico_succ_right_of_not_isMax not_isMax _

-- TODO: prove for a succ-archimedean non-linear order
@[to_dual (attr := simp) Ioo_pred_left]
/--
theorem `Ioo_succ_right` / 定理 `Ioo_succ_right`

English:
theorem Ioo_succ_right
  given: (a b : α)
  statement: Ioo a (succ b) = Ioc a b
  proof: Ioo_succ_right_of_not_isMax not_isMax _

@[to_dual (attr := simp)]

中文:
定理 Ioo_succ_right
  条件: (a b : α)
  结论: Ioo a (succ b) = Ioc a b
  证明: Ioo_succ_right_of_not_isMax not_isMax _

@[to_dual (attr := simp)]

Depends on / 依赖: Ioo_succ_right_of_not_isMax, not_isMax
-/
theorem Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a b :=
Ioo_succ_right_of_not_isMax not_isMax _

@[to_dual (attr := simp)]
/--
theorem `succ_eq_succ_iff` / 定理 `succ_eq_succ_iff`

English:
theorem succ_eq_succ_iff
  statement: succ a = succ b ↔ a = b
  proof: succ_eq_succ_iff_of_not_isMax (not_isMax a) (not_isMax b)

@[to_dual]

中文:
定理 succ_eq_succ_iff
  结论: succ a = succ b ↔ a = b
  证明: succ_eq_succ_iff_of_not_isMax (not_isMax a) (not_isMax b)

@[to_dual]

Depends on / 依赖: not_isMax, succ_eq_succ_iff_of_not_isMax
-/
theorem succ_eq_succ_iff : succ a = succ b ↔ a = b :=
  succ_eq_succ_iff_of_not_isMax (not_isMax a) (not_isMax b)

@[to_dual]
/--
theorem `succ_injective` / 定理 `succ_injective`

English:
theorem succ_injective
  statement: Injective (succ : α -> α)
  proof: fun _ _ => succ_eq_succ_iff.1

@[to_dual]

中文:
定理 succ_injective
  结论: Injective (succ : α -> α)
  证明: fun _ _ => succ_eq_succ_iff.1

@[to_dual]

Depends on / 依赖: succ_eq_succ_iff
-/
theorem succ_injective : Injective (succ : α -> α) := fun _ _ => succ_eq_succ_iff.1

@[to_dual]
/--
theorem `succ_ne_succ_iff` / 定理 `succ_ne_succ_iff`

English:
theorem succ_ne_succ_iff
  statement: succ a != succ b ↔ a != b
  proof: succ_injective.ne_iff

@[to_dual]
alias ⟨_, succ_ne_succ⟩ := succ_ne_succ_iff

@[to_dual pred_lt_iff_eq_or_gt]

中文:
定理 succ_ne_succ_iff
  结论: succ a != succ b ↔ a != b
  证明: succ_injective.ne_iff

@[to_dual]
alias ⟨_, succ_ne_succ⟩ := succ_ne_succ_iff

@[to_dual pred_lt_iff_eq_or_gt]

Depends on / 依赖: ne_iff, succ_injective, succ_injective.ne_iff
-/
theorem succ_ne_succ_iff : succ a != succ b ↔ a != b :=
  succ_injective.ne_iff

@[to_dual]
alias ⟨_, succ_ne_succ⟩ := succ_ne_succ_iff

@[to_dual pred_lt_iff_eq_or_gt]
/--
theorem `lt_succ_iff_eq_or_lt` / 定理 `lt_succ_iff_eq_or_lt`

English:
theorem lt_succ_iff_eq_or_lt
  statement: a < succ b ↔ a = b ∨ a < b
  proof: lt_succ_iff.trans le_iff_eq_or_lt

@[to_dual pred_lt_iff_eq_or_lt]

中文:
定理 lt_succ_iff_eq_or_lt
  结论: a < succ b ↔ a = b ∨ a < b
  证明: lt_succ_iff.trans le_iff_eq_or_lt

@[to_dual pred_lt_iff_eq_or_lt]

Depends on / 依赖: le_iff_eq_or_lt, lt_succ_iff, lt_succ_iff.trans
-/
theorem lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ a < b :=
  lt_succ_iff.trans le_iff_eq_or_lt

@[to_dual pred_lt_iff_eq_or_lt]
/--
theorem `lt_succ_iff_eq_or_gt` / 定理 `lt_succ_iff_eq_or_gt`

English:
theorem lt_succ_iff_eq_or_gt
  statement: a < succ b ↔ b = a ∨ a < b
  proof: by
  rw [eq_comm]; rw [lt_succ_iff_eq_or_lt]

@[to_dual]

中文:
定理 lt_succ_iff_eq_or_gt
  结论: a < succ b ↔ b = a ∨ a < b
  证明: by
  rw [eq_comm]; rw [lt_succ_iff_eq_or_lt]

@[to_dual]

Depends on / 依赖: eq_comm, lt_succ_iff_eq_or_lt
-/
theorem lt_succ_iff_eq_or_gt : a < succ b ↔ b = a ∨ a < b := by
  rw [eq_comm]; rw [lt_succ_iff_eq_or_lt]

@[to_dual]
/--
theorem `Iio_succ_eq_insert` / 定理 `Iio_succ_eq_insert`

English:
theorem Iio_succ_eq_insert
  given: (a : α)
  statement: Iio (succ a) = insert a (Iio a)
  proof: Iio_succ_eq_insert_of_not_isMax not_isMax a

@[to_dual Ioc_pred_left_eq_insert]

中文:
定理 Iio_succ_eq_insert
  条件: (a : α)
  结论: Iio (succ a) = insert a (Iio a)
  证明: Iio_succ_eq_insert_of_not_isMax not_isMax a

@[to_dual Ioc_pred_left_eq_insert]

Depends on / 依赖: Iio_succ_eq_insert_of_not_isMax, not_isMax
-/
theorem Iio_succ_eq_insert (a : α) : Iio (succ a) = insert a (Iio a) :=
Iio_succ_eq_insert_of_not_isMax not_isMax a

@[to_dual Ioc_pred_left_eq_insert]
/--
theorem `Ico_succ_right_eq_insert` / 定理 `Ico_succ_right_eq_insert`

English:
theorem Ico_succ_right_eq_insert
  given: (h : a <= b)
  statement: Ico a (succ b) = insert b (Ico a b)
  proof: Ico_succ_right_eq_insert_of_not_isMax h not_isMax b

@[deprecated (since := "2026-04-28")] alias Ico_pred_right_eq_insert := Ioc_pred_left_eq_insert

@[to_dual Ioo_pred_left_eq_insert]

中文:
定理 Ico_succ_right_eq_insert
  条件: (h : a <= b)
  结论: Ico a (succ b) = insert b (Ico a b)
  证明: Ico_succ_right_eq_insert_of_not_isMax h not_isMax b

@[deprecated (since := "2026-04-28")] alias Ico_pred_right_eq_insert := Ioc_pred_left_eq_insert

@[to_dual Ioo_pred_left_eq_insert]

Depends on / 依赖: Ico_succ_right_eq_insert_of_not_isMax, not_isMax
-/
theorem Ico_succ_right_eq_insert (h : a <= b) : Ico a (succ b) = insert b (Ico a b) :=
Ico_succ_right_eq_insert_of_not_isMax h not_isMax b

@[deprecated (since := "2026-04-28")] alias Ico_pred_right_eq_insert := Ioc_pred_left_eq_insert

@[to_dual Ioo_pred_left_eq_insert]
/--
theorem `Ioo_succ_right_eq_insert` / 定理 `Ioo_succ_right_eq_insert`

English:
theorem Ioo_succ_right_eq_insert
  given: (h : a < b)
  statement: Ioo a (succ b) = insert b (Ioo a b)
  proof: Ioo_succ_right_eq_insert_of_not_isMax h not_isMax b

@[deprecated (since := "2026-04-28")] alias Ioo_pred_right_eq_insert := Ioo_pred_left_eq_insert

@[to_dual (attr := simp) Ioo_eq_empty_iff_pred_le]

中文:
定理 Ioo_succ_right_eq_insert
  条件: (h : a < b)
  结论: Ioo a (succ b) = insert b (Ioo a b)
  证明: Ioo_succ_right_eq_insert_of_not_isMax h not_isMax b

@[deprecated (since := "2026-04-28")] alias Ioo_pred_right_eq_insert := Ioo_pred_left_eq_insert

@[to_dual (attr := simp) Ioo_eq_empty_iff_pred_le]

Depends on / 依赖: Ioo_succ_right_eq_insert_of_not_isMax, not_isMax
-/
theorem Ioo_succ_right_eq_insert (h : a < b) : Ioo a (succ b) = insert b (Ioo a b) :=
Ioo_succ_right_eq_insert_of_not_isMax h not_isMax b

@[deprecated (since := "2026-04-28")] alias Ioo_pred_right_eq_insert := Ioo_pred_left_eq_insert

@[to_dual (attr := simp) Ioo_eq_empty_iff_pred_le]
/--
theorem `Ioo_eq_empty_iff_le_succ` / 定理 `Ioo_eq_empty_iff_le_succ`

English:
theorem Ioo_eq_empty_iff_le_succ
  statement: Ioo a b = ∅ ↔ b <= succ a
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    exact ⟨succ a, lt_succ_iff_not_isMax.mpr (not_isMax a), h⟩
  · ext x
    suffices a < x -> b <= x by simpa
exact fun hx => le_of_lt_succ lt_of_le_of_lt h succ_strictMono hx

中文:
定理 Ioo_eq_empty_iff_le_succ
  结论: Ioo a b = ∅ ↔ b <= succ a
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    exact ⟨succ a, lt_succ_iff_not_isMax.mpr (not_isMax a), h⟩
  · ext x
    suffices a < x -> b <= x by simpa
exact fun hx => le_of_lt_succ lt_of_le_of_lt h succ_strictMono hx

Depends on / 依赖: contrapose, le_of_lt_succ, lt_of_le_of_lt, lt_succ_iff_not_isMax, lt_succ_iff_not_isMax.mpr, not_isMax, succ_strictMono
-/
theorem Ioo_eq_empty_iff_le_succ : Ioo a b = ∅ ↔ b <= succ a := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    exact ⟨succ a, lt_succ_iff_not_isMax.mpr (not_isMax a), h⟩
  · ext x
    suffices a < x -> b <= x by simpa
exact fun hx => le_of_lt_succ lt_of_le_of_lt h succ_strictMono hx

end NoMaxOrder

section OrderBot

variable [OrderBot α]

@[to_dual pred_top_lt_iff]
/--
theorem `lt_succ_bot_iff` / 定理 `lt_succ_bot_iff`

English:
theorem lt_succ_bot_iff
  given: [NoMaxOrder α]
  statement: a < succ ⊥ ↔ a = ⊥
  proof: by rw [lt_succ_iff, le_bot_iff]

@[to_dual pred_top_le_iff]

中文:
定理 lt_succ_bot_iff
  条件: [NoMaxOrder α]
  结论: a < succ ⊥ ↔ a = ⊥
  证明: by rw [lt_succ_iff, le_bot_iff]

@[to_dual pred_top_le_iff]

Depends on / 依赖: le_bot_iff, lt_succ_iff
-/
theorem lt_succ_bot_iff [NoMaxOrder α] : a < succ ⊥ ↔ a = ⊥ := by rw [lt_succ_iff, le_bot_iff]

@[to_dual pred_top_le_iff]
/--
theorem `le_succ_bot_iff` / 定理 `le_succ_bot_iff`

English:
theorem le_succ_bot_iff
  statement: a <= succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥
  proof: by
  rw [le_succ_iff_eq_or_le]; rw [le_bot_iff]; rw [or_comm]

中文:
定理 le_succ_bot_iff
  结论: a <= succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥
  证明: by
  rw [le_succ_iff_eq_or_le]; rw [le_bot_iff]; rw [or_comm]

Depends on / 依赖: CommRing, DivisionRing, Nontrivial, le_bot_iff, le_succ_iff_eq_or_le, or_comm
-/
theorem le_succ_bot_iff : a <= succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥ := by
  rw [le_succ_iff_eq_or_le]; rw [le_bot_iff]; rw [or_comm]

end OrderBot

end LinearOrder

/-- There is at most one way to define the successors in a `PartialOrder`. -/
@[to_dual
/-- There is at most one way to define the predecessors in a `PartialOrder`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] : Subsingleton (SuccOrder α)
  body: ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMax a
    · exact (@IsMax.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm
    · exact @CovBy.succ_eq _ _ h₀ _ _ (covBy_succ_of_not_isMax ha)⟩

@[to_dual]

中文:
实例 [PartialOrder
  签名: α] : Subsingleton (SuccOrder α)
  定义体: ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMax a
    · exact (@IsMax.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm
    · exact @CovBy.succ_eq _ _ h₀ _ _ (covBy_succ_of_not_isMax ha)⟩

@[to_dual]

Depends on / 依赖: CovBy.succ_eq, IsMax.succ_eq, covBy_succ_of_not_isMax, ha.succ_eq.symm, succ_eq
-/
instance [PartialOrder α] : Subsingleton (SuccOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMax a
    · exact (@IsMax.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm
    · exact @CovBy.succ_eq _ _ h₀ _ _ (covBy_succ_of_not_isMax ha)⟩

@[to_dual]
/--
theorem `succ_eq_sInf` / 定理 `succ_eq_sInf`

English:
theorem succ_eq_sInf
  given: [CompleteLattice α] [SuccOrder α] (a : α)
  proof: by
  apply (le_sInf fun b => succ_le_of_lt).antisymm
  obtain rfl | ha := eq_or_ne a ⊤
  · rw [succ_top]
    exact le_top
  · exact sInf_le (lt_succ_iff_ne_top.2 ha)

@[to_dual]

中文:
定理 succ_eq_sInf
  条件: [CompleteLattice α] [SuccOrder α] (a : α)
  证明: by
  apply (le_sInf fun b => succ_le_of_lt).antisymm
  obtain rfl | ha := eq_or_ne a ⊤
  · rw [succ_top]
    exact le_top
  · exact sInf_le (lt_succ_iff_ne_top.2 ha)

@[to_dual]

Depends on / 依赖: antisymm, eq_or_ne, le_sInf, le_top, lt_succ_iff_ne_top, sInf_le, succ_le_of_lt, succ_top
-/
theorem succ_eq_sInf [CompleteLattice α] [SuccOrder α] (a : α) :
    succ a = sInf (Set.Ioi a) := by
  apply (le_sInf fun b => succ_le_of_lt).antisymm
  obtain rfl | ha := eq_or_ne a ⊤
  · rw [succ_top]
    exact le_top
  · exact sInf_le (lt_succ_iff_ne_top.2 ha)

@[to_dual]
/--
theorem `succ_eq_iInf` / 定理 `succ_eq_iInf`

English:
theorem succ_eq_iInf
  given: [CompleteLattice α] [SuccOrder α] (a : α)
  statement: succ a = ⨅ b > a, b
  proof: by
  rw [succ_eq_sInf]; rw [iInf_subtype']; rw [iInf]; rw [Subtype.range_coe_subtype]; rw [Ioi]

@[to_dual]

中文:
定理 succ_eq_iInf
  条件: [CompleteLattice α] [SuccOrder α] (a : α)
  结论: succ a = ⨅ b > a, b
  证明: by
  rw [succ_eq_sInf]; rw [iInf_subtype']; rw [iInf]; rw [Subtype.range_coe_subtype]; rw [Ioi]

@[to_dual]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, ZMod.ringHom_surjective, iInf_subtype, isLocalHom, range_coe_subtype, ringHom_surjective, succ_eq_sInf
-/
theorem succ_eq_iInf [CompleteLattice α] [SuccOrder α] (a : α) : succ a = ⨅ b > a, b := by
  rw [succ_eq_sInf]; rw [iInf_subtype']; rw [iInf]; rw [Subtype.range_coe_subtype]; rw [Ioi]

@[to_dual]
/--
theorem `succ_eq_csInf` / 定理 `succ_eq_csInf`

English:
theorem succ_eq_csInf
  given: [ConditionallyCompleteLattice α] [SuccOrder α] [NoMaxOrder α] (a : α)
  proof: by
  apply (le_csInf nonempty_Ioi fun b => succ_le_of_lt).antisymm
exact csInf_le ⟨a, fun b => le_of_lt⟩ lt_succ a

中文:
定理 succ_eq_csInf
  条件: [ConditionallyCompleteLattice α] [SuccOrder α] [NoMaxOrder α] (a : α)
  证明: by
  apply (le_csInf nonempty_Ioi fun b => succ_le_of_lt).antisymm
exact csInf_le ⟨a, fun b => le_of_lt⟩ lt_succ a

Depends on / 依赖: antisymm, csInf_le, le_csInf, le_of_lt, lt_succ, nonempty_Ioi, succ_le_of_lt
-/
theorem succ_eq_csInf [ConditionallyCompleteLattice α] [SuccOrder α] [NoMaxOrder α] (a : α) :
    succ a = sInf (Set.Ioi a) := by
  apply (le_csInf nonempty_Ioi fun b => succ_le_of_lt).antisymm
exact csInf_le ⟨a, fun b => le_of_lt⟩ lt_succ a

section Preorder

variable [Preorder α] [PredOrder α] {a b : α}

-- TODO: auto-generate all of these through `to_dual`

@[to_dual existing]
/--
theorem `isMin_iterate_pred_of_eq_of_lt` / 定理 `isMin_iterate_pred_of_eq_of_lt`

English:
theorem isMin_iterate_pred_of_eq_of_lt
  statement: {n m : Nat} (h_eq : pred^[n] a = pred^[m] a)
  proof: @isMax_iterate_succ_of_eq_of_lt αᵒᵈ _ _ _ _ _ h_eq h_lt

@[to_dual existing]

中文:
定理 isMin_iterate_pred_of_eq_of_lt
  结论: {n m : 自然数} (h_eq : pred^[n] a = pred^[m] a)
  证明: @isMax_iterate_succ_of_eq_of_lt αᵒᵈ _ _ _ _ _ h_eq h_lt

@[to_dual existing]

Depends on / 依赖: additive_of_preserves_binary_products, e.eqv.functor.additive_of_preserves_binary_products, functor, h_eq, h_lt, isMax_iterate_succ_of_eq_of_lt
-/
theorem isMin_iterate_pred_of_eq_of_lt {n m : Nat} (h_eq : pred^[n] a = pred^[m] a)
    (h_lt : n < m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_lt αᵒᵈ _ _ _ _ _ h_eq h_lt

@[to_dual existing]
/--
theorem `isMin_iterate_pred_of_eq_of_ne` / 定理 `isMin_iterate_pred_of_eq_of_ne`

English:
theorem isMin_iterate_pred_of_eq_of_ne
  statement: {n m : Nat} (h_eq : pred^[n] a = pred^[m] a)
  proof: @isMax_iterate_succ_of_eq_of_ne αᵒᵈ _ _ _ _ _ h_eq h_ne

中文:
定理 isMin_iterate_pred_of_eq_of_ne
  结论: {n m : 自然数} (h_eq : pred^[n] a = pred^[m] a)
  证明: @isMax_iterate_succ_of_eq_of_ne αᵒᵈ _ _ _ _ _ h_eq h_ne

Depends on / 依赖: h_eq, h_ne, isMax_iterate_succ_of_eq_of_ne
-/
theorem isMin_iterate_pred_of_eq_of_ne {n m : Nat} (h_eq : pred^[n] a = pred^[m] a)
    (h_ne : n != m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_ne αᵒᵈ _ _ _ _ _ h_eq h_ne

end Preorder

/-! ### Successor-predecessor orders -/

section SuccPredOrder
section Preorder
variable [Preorder α] [SuccOrder α] [PredOrder α] {a b : α}

@[to_dual pred_succ_le]
/--
lemma `le_succ_pred` / 引理 `le_succ_pred`

English:
lemma le_succ_pred
  given: (a : α)
  statement: a <= succ (pred a)
  proof: (pred_wcovBy _).le_succ

@[to_dual le_succ_iff_pred_le]

中文:
引理 le_succ_pred
  条件: (a : α)
  结论: a <= succ (pred a)
  证明: (pred_wcovBy _).le_succ

@[to_dual le_succ_iff_pred_le]

Depends on / 依赖: le_succ, pred_wcovBy
-/
lemma le_succ_pred (a : α) : a <= succ (pred a) := (pred_wcovBy _).le_succ

@[to_dual le_succ_iff_pred_le]
/--
lemma `pred_le_iff_le_succ` / 引理 `pred_le_iff_le_succ`

English:
lemma pred_le_iff_le_succ
  statement: pred a <= b ↔ a <= succ b where
  proof: (le_succ_pred _).trans (succ_le_succ hab)
  mpr hab := (pred_le_pred hab).trans (pred_succ_le _)

中文:
引理 pred_le_iff_le_succ
  结论: pred a <= b ↔ a <= succ b where
  证明: (le_succ_pred _).trans (succ_le_succ hab)
  mpr hab := (pred_le_pred hab).trans (pred_succ_le _)

Depends on / 依赖: le_succ_pred, succ_le_succ
-/
lemma pred_le_iff_le_succ : pred a <= b ↔ a <= succ b where
  mp hab := (le_succ_pred _).trans (succ_le_succ hab)
  mpr hab := (pred_le_pred hab).trans (pred_succ_le _)

/--
lemma `gc_pred_succ` / 引理 `gc_pred_succ`

English:
lemma gc_pred_succ
  statement: GaloisConnection (pred : α -> α) succ
  proof: fun _ _ => pred_le_iff_le_succ

中文:
引理 gc_pred_succ
  结论: GaloisConnection (pred : α -> α) succ
  证明: fun _ _ => pred_le_iff_le_succ

Depends on / 依赖: pred_le_iff_le_succ
-/
lemma gc_pred_succ : GaloisConnection (pred : α -> α) succ := fun _ _ => pred_le_iff_le_succ

end Preorder

variable [PartialOrder α] [SuccOrder α] [PredOrder α] {a : α}

@[to_dual (attr := simp)]
/--
theorem `succ_pred_of_not_isMin` / 定理 `succ_pred_of_not_isMin`

English:
theorem succ_pred_of_not_isMin
  given: (h : ¬IsMin a)
  statement: succ (pred a) = a
  proof: CovBy.succ_eq (pred_covBy_of_not_isMin h)

@[to_dual]

中文:
定理 succ_pred_of_not_isMin
  条件: (h : ¬IsMin a)
  结论: succ (pred a) = a
  证明: CovBy.succ_eq (pred_covBy_of_not_isMin h)

@[to_dual]

Depends on / 依赖: CovBy.succ_eq, pred_covBy_of_not_isMin, succ_eq
-/
theorem succ_pred_of_not_isMin (h : ¬IsMin a) : succ (pred a) = a :=
  CovBy.succ_eq (pred_covBy_of_not_isMin h)

@[to_dual]
/--
theorem `succ_pred` / 定理 `succ_pred`

English:
theorem succ_pred
  given: [NoMinOrder α] (a : α)
  statement: succ (pred a) = a
  proof: CovBy.succ_eq (pred_covBy _)

@[to_dual]

中文:
定理 succ_pred
  条件: [NoMinOrder α] (a : α)
  结论: succ (pred a) = a
  证明: CovBy.succ_eq (pred_covBy _)

@[to_dual]

Depends on / 依赖: CovBy.succ_eq, pred_covBy, succ_eq
-/
theorem succ_pred [NoMinOrder α] (a : α) : succ (pred a) = a :=
  CovBy.succ_eq (pred_covBy _)

@[to_dual]
/--
theorem `pred_succ_iterate_of_not_isMax` / 定理 `pred_succ_iterate_of_not_isMax`

English:
theorem pred_succ_iterate_of_not_isMax
  given: (i : α) (n : Nat) (hin : ¬IsMax (succ^[n - 1] i))
  proof: by
  induction n with
  | zero => simp only [Function.iterate_zero, id]
  | succ n hn =>
    rw [Nat.succ_sub_succ_eq_sub]; rw [Nat.sub_zero] at hin
    have h_not_max : ¬IsMax (succ^[n - 1] i) := by
      rcases n with - | n
      · simpa using hin
      rw [Nat.succ_sub_succ_eq_sub]; rw [Nat.sub_z

中文:
定理 pred_succ_iterate_of_not_isMax
  条件: (i : α) (n : 自然数) (hin : ¬IsMax (succ^[n - 1] i))
  证明: by
  induction n with
  | zero => simp only [Function.iterate_zero, id]
  | succ n hn =>
    rw [Nat.succ_sub_succ_eq_sub]; rw [Nat.sub_zero] at hin
    have h_not_max : ¬IsMax (succ^[n - 1] i) := by
      rcases n with - | n
      · simpa using hin
      rw [Nat.succ_sub_succ_eq_sub]; rw [Nat.sub_z

Depends on / 依赖: Function, Function.iterate_succ, Function.iterate_zero, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, h_max, h_not_max, h_sub_le, h_sub_le.trans, hj_le, hj_le.trans, iterate_succ, iterate_zero, le_succ, n.succ, sub_zero, succ_sub_succ_eq_sub
-/
theorem pred_succ_iterate_of_not_isMax (i : α) (n : Nat) (hin : ¬IsMax (succ^[n - 1] i)) :
    pred^[n] (succ^[n] i) = i := by
  induction n with
  | zero => simp only [Function.iterate_zero, id]
  | succ n hn =>
    rw [Nat.succ_sub_succ_eq_sub]; rw [Nat.sub_zero] at hin
    have h_not_max : ¬IsMax (succ^[n - 1] i) := by
      rcases n with - | n
      · simpa using hin
      rw [Nat.succ_sub_succ_eq_sub]; rw [Nat.sub_zero] at hn ⊢
      have h_sub_le : succ^[n] i <= succ^[n.succ] i := by
        rw [Function.iterate_succ']
        exact le_succ _
      refine fun h_max => hin fun j hj => ?_
      have hj_le : j <= succ^[n] i := h_max (h_sub_le.trans hj)
      exact hj_le.trans h_sub_le
    rw [Function.iterate_succ]; rw [Function.iterate_succ']
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

variable [PartialOrder α] [SuccOrder α] [forall a : α, Decidable (succ a = a)]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SuccOrder (WithTop α)
  body: by
    obtain - | a := a
    · exact le_top
    change _ <= ite _ _ _
    split_ifs
    · exact le_top
    · exact coe_le_coe.2 (le_succ a)
  max_of_succ_le {a} ha := by
    cases a
    · exact isMax_top
    dsimp only at ha
    split_ifs at ha with ha'
    · exact (not_top_le_coe _ ha).elim
    · r

中文:
实例 :
  签名: SuccOrder (WithTop α)
  定义体: by
    obtain - | a := a
    · exact le_top
    change _ <= ite _ _ _
    split_ifs
    · exact le_top
    · exact coe_le_coe.2 (le_succ a)
  max_of_succ_le {a} ha := by
    cases a
    · exact isMax_top
    dsimp only at ha
    split_ifs at ha with ha'
    · exact (not_top_le_coe _ ha).elim
    · r

Depends on / 依赖: coe_le_coe, coe_lt_coe, isMax_top, le_succ, le_top, max_of_succ_le, not_top_le_coe, not_top_lt, split_ifs, succ_eq_iff_isM, succ_eq_iff_isMax, succ_le_iff_isMax, succ_le_of_lt
-/
instance : SuccOrder (WithTop α) where
  succ
    | ⊤ => ⊤
    | Option.some a => ite (succ a = a) ⊤ (some (succ a))
  le_succ a := by
    obtain - | a := a
    · exact le_top
    change _ <= ite _ _ _
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
    change ite _ _ _ <= _
    split_ifs with ha
    · rw [succ_eq_iff_isMax] at ha
      exact (ha.not_lt h).elim
    · exact coe_le_coe.2 (succ_le_of_lt h)

@[to_dual (attr := simp)]
/--
theorem `succ_coe_of_isMax` / 定理 `succ_coe_of_isMax`

English:
theorem succ_coe_of_isMax
  given: {a : α} (h : IsMax a)
  statement: succ ↑a = (⊤ : WithTop α)
  proof: dif_pos (succ_eq_iff_isMax.2 h)

@[to_dual]

中文:
定理 succ_coe_of_isMax
  条件: {a : α} (h : IsMax a)
  结论: succ ↑a = (⊤ : WithTop α)
  证明: dif_pos (succ_eq_iff_isMax.2 h)

@[to_dual]

Depends on / 依赖: dif_pos, succ_eq_iff_isMax
-/
theorem succ_coe_of_isMax {a : α} (h : IsMax a) : succ ↑a = (⊤ : WithTop α) :=
  dif_pos (succ_eq_iff_isMax.2 h)

@[to_dual]
/--
theorem `succ_coe_of_not_isMax` / 定理 `succ_coe_of_not_isMax`

English:
theorem succ_coe_of_not_isMax
  given: {a : α} (h : ¬ IsMax a)
  statement: succ (↑a : WithTop α) = ↑(succ a)
  proof: dif_neg (succ_eq_iff_isMax.not.2 h)

@[to_dual (attr := simp)]

中文:
定理 succ_coe_of_not_isMax
  条件: {a : α} (h : ¬ IsMax a)
  结论: succ (↑a : WithTop α) = ↑(succ a)
  证明: dif_neg (succ_eq_iff_isMax.not.2 h)

@[to_dual (attr := simp)]

Depends on / 依赖: dif_neg, succ_eq_iff_isMax, succ_eq_iff_isMax.not
-/
theorem succ_coe_of_not_isMax {a : α} (h : ¬ IsMax a) : succ (↑a : WithTop α) = ↑(succ a) :=
  dif_neg (succ_eq_iff_isMax.not.2 h)

@[to_dual (attr := simp)]
/--
theorem `succ_coe` / 定理 `succ_coe`

English:
theorem succ_coe
  given: [NoMaxOrder α] {a : α}
  statement: succ (↑a : WithTop α) = ↑(succ a)
  proof: succ_coe_of_not_isMax not_isMax a

中文:
定理 succ_coe
  条件: [NoMaxOrder α] {a : α}
  结论: succ (↑a : WithTop α) = ↑(succ a)
  证明: succ_coe_of_not_isMax not_isMax a

Depends on / 依赖: not_isMax, succ_coe_of_not_isMax
-/
theorem succ_coe [NoMaxOrder α] {a : α} : succ (↑a : WithTop α) = ↑(succ a) :=
succ_coe_of_not_isMax not_isMax a

end Succ

section Pred

variable [Preorder α] [OrderTop α] [PredOrder α]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PredOrder (WithTop α)
  body: match a with
    | ⊤ => le_top
    | Option.some a => coe_le_coe.2 (pred_le a)
  min_of_le_pred {a} ha := by
    cases a
    · exact ((coe_lt_top (⊤ : α)).not_ge ha).elim
    · exact (min_of_le_pred <| coe_le_coe.1 ha).withTop
  le_pred_of_lt {a b} h := by
    cases a
    · exact (le_top.not_gt h).e

中文:
实例 :
  签名: PredOrder (WithTop α)
  定义体: match a with
    | ⊤ => le_top
    | Option.some a => coe_le_coe.2 (pred_le a)
  min_of_le_pred {a} ha := by
    cases a
    · exact ((coe_lt_top (⊤ : α)).not_ge ha).elim
    · exact (min_of_le_pred <| coe_le_coe.1 ha).withTop
  le_pred_of_lt {a b} h := by
    cases a
    · exact (le_top.not_gt h).e

Depends on / 依赖: Option.some, coe_le_coe, coe_lt_coe, coe_lt_top, le_pred_of_lt, le_top, le_top.not_gt, min_of_le_pred, not_ge, not_gt, pred_le, withTop
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

/--
lemma `orderPred_top` / 引理 `orderPred_top`

English:
lemma orderPred_top
  statement: pred (⊤ : WithTop α) = ↑(⊤ : α)
  proof: rfl

中文:
引理 orderPred_top
  结论: pred (⊤ : WithTop α) = ↑(⊤ : α)
  证明: rfl
-/
@[to_dual (attr := simp)] lemma orderPred_top : pred (⊤ : WithTop α) = ↑(⊤ : α) := rfl

/--
lemma `orderPred_coe` / 引理 `orderPred_coe`

English:
lemma orderPred_coe
  given: (a : α)
  statement: pred (↑a : WithTop α) = ↑(pred a)
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 orderPred_coe
  条件: (a : α)
  结论: pred (↑a : WithTop α) = ↑(pred a)
  证明: rfl

@[to_dual (attr := simp)]
-/
@[to_dual (attr := simp)] lemma orderPred_coe (a : α) : pred (↑a : WithTop α) = ↑(pred a) := rfl

@[to_dual (attr := simp)]
/--
theorem `pred_untop` / 定理 `pred_untop`

English:
theorem pred_untop

中文:
定理 pred_untop
-/
theorem pred_untop :
    forall (a : WithTop α) (ha : a != ⊤),
      pred (a.untop ha) = (pred a).untop (by induction a <;> simp)
  | ⊤, ha => (ha rfl).elim
  | (a : α), _ => rfl

end Pred

section Pred

variable [Preorder α] [NoMaxOrder α]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hα
  signature: : Nonempty α] : IsEmpty (PredOrder (WithTop α))
  body: ⟨by
    intro
    cases h : pred (⊤ : WithTop α) with
| top => exact hα.elim fun a => (min_of_le_pred h.ge).not_lt coe_lt_top a
    | coe a =>
      obtain ⟨c, hc⟩ := exists_gt a
      rw [← coe_lt_coe]; rw [← h] at hc
      exact (le_pred_of_lt (coe_lt_top c)).not_gt hc⟩

中文:
实例 [hα
  签名: : Nonempty α] : IsEmpty (PredOrder (WithTop α))
  定义体: ⟨by
    intro
    cases h : pred (⊤ : WithTop α) with
| top => exact hα.elim fun a => (min_of_le_pred h.ge).not_lt coe_lt_top a
    | coe a =>
      obtain ⟨c, hc⟩ := exists_gt a
      rw [← coe_lt_coe]; rw [← h] at hc
      exact (le_pred_of_lt (coe_lt_top c)).not_gt hc⟩

Depends on / 依赖: WithTop, coe_lt_coe, coe_lt_top, exists_gt, h.ge, le_pred_of_lt, min_of_le_pred, not_gt, not_lt
-/
instance [hα : Nonempty α] : IsEmpty (PredOrder (WithTop α)) :=
  ⟨by
    intro
    cases h : pred (⊤ : WithTop α) with
| top => exact hα.elim fun a => (min_of_le_pred h.ge).not_lt coe_lt_top a
    | coe a =>
      obtain ⟨c, hc⟩ := exists_gt a
      rw [← coe_lt_coe]; rw [← h] at hc
      exact (le_pred_of_lt (coe_lt_top c)).not_gt hc⟩

end Pred

end WithTop

section OrderIso

variable {X Y : Type*} [Preorder X] [Preorder Y]

-- See note [reducible non-instances]
/-- `SuccOrder` transfers across equivalences between orders. -/
@[to_dual
/-- `PredOrder` transfers across equivalences between orders. -/]
/--
Definition of `SuccOrder.ofOrderIso` / `SuccOrder.ofOrderIso` 的定义

English:
abbreviation SuccOrder.ofOrderIso
  signature: [SuccOrder X] (f : X ≃o Y)
  body: f (succ (f.symm y))
  le_succ y := by rw [← map_inv_le_iff f]; exact le_succ (f.symm y)
  max_of_succ_le h := by
    rw [← f.symm.isMax_apply]
    refine max_of_succ_le ?_
    simp [f.le_symm_apply, h]
  succ_le_of_lt h := by rw [← le_map_inv_iff]; exact succ_le_of_lt (by simp [h])

中文:
缩写 SuccOrder.ofOrderIso
  签名: [SuccOrder X] (f : X ≃o Y)
  定义体: f (succ (f.symm y))
  le_succ y := by rw [← map_inv_le_iff f]; exact le_succ (f.symm y)
  max_of_succ_le h := by
    rw [← f.symm.isMax_apply]
    refine max_of_succ_le ?_
    simp [f.le_symm_apply, h]
  succ_le_of_lt h := by rw [← le_map_inv_iff]; exact succ_le_of_lt (by simp [h])
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
/--
Instance `Set.OrdConnected.predOrder` / 实例 `Set.OrdConnected.predOrder`

English:
instance Set.OrdConnected.predOrder
  signature: [PredOrder α]
  body: if h : Order.pred x.1 in s then ⟨Order.pred x.1, h⟩ else x
  pred_le := fun ⟨x, hx⟩ => by dsimp; split <;> simp_all [Order.pred_le]
  min_of_le_pred := @fun ⟨x, hx⟩ h => by
    dsimp at h
    split_ifs at h with h'
    · simp only [Subtype.mk_le_mk, Order.le_pred_iff_isMin] at h
      rintro ⟨y, _⟩ 

中文:
实例 Set.OrdConnected.predOrder
  签名: [PredOrder α]
  定义体: if h : Order.pred x.1 in s then ⟨Order.pred x.1, h⟩ else x
  pred_le := fun ⟨x, hx⟩ => by dsimp; split <;> simp_all [Order.pred_le]
  min_of_le_pred := @fun ⟨x, hx⟩ h => by
    dsimp at h
    split_ifs at h with h'
    · simp only [Subtype.mk_le_mk, Order.le_pred_iff_isMin] at h
      rintro ⟨y, _⟩ 

Depends on / 依赖: Order.pred
-/
noncomputable instance Set.OrdConnected.predOrder [PredOrder α] : PredOrder s where
  pred x := if h : Order.pred x.1 in s then ⟨Order.pred x.1, h⟩ else x
  pred_le := fun ⟨x, hx⟩ => by dsimp; split <;> simp_all [Order.pred_le]
  min_of_le_pred := @fun ⟨x, hx⟩ h => by
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
  le_pred_of_lt := @fun ⟨b, hb⟩ ⟨c, hc⟩ h => by
    rw [Subtype.mk_lt_mk] at h
    dsimp only
    split
    · exact h.le_pred
    · exact h.le

@[simp, norm_cast]
/--
lemma `coe_pred_of_mem` / 引理 `coe_pred_of_mem`

English:
lemma coe_pred_of_mem
  given: [PredOrder α] {a : s} (h : pred a.1 in s)
  proof: by classical
  change Subtype.val (dite ..) = _
  simp [h]

中文:
引理 coe_pred_of_mem
  条件: [PredOrder α] {a : s} (h : pred a.1 in s)
  证明: by classical
  change Subtype.val (dite ..) = _
  simp [h]

Depends on / 依赖: Subtype, Subtype.val, classical
-/
lemma coe_pred_of_mem [PredOrder α] {a : s} (h : pred a.1 in s) :
    (pred a).1 = pred ↑a := by classical
  change Subtype.val (dite ..) = _
  simp [h]

/--
lemma `isMin_of_pred_notMem` / 引理 `isMin_of_pred_notMem`

English:
lemma isMin_of_pred_notMem
  given: [PredOrder α] {a : s} (h : pred ↑a ∉ s)
  statement: IsMin a
  proof: by classical
  rw [← pred_eq_iff_isMin]
  change dite .. = _
  simp [h]

中文:
引理 isMin_of_pred_notMem
  条件: [PredOrder α] {a : s} (h : pred ↑a ∉ s)
  结论: IsMin a
  证明: by classical
  rw [← pred_eq_iff_isMin]
  change dite .. = _
  simp [h]

Depends on / 依赖: classical, pred_eq_iff_isMin
-/
lemma isMin_of_pred_notMem [PredOrder α] {a : s} (h : pred ↑a ∉ s) : IsMin a := by classical
  rw [← pred_eq_iff_isMin]
  change dite .. = _
  simp [h]

/--
lemma `pred_notMem_iff_isMin` / 引理 `pred_notMem_iff_isMin`

English:
lemma pred_notMem_iff_isMin
  given: [PredOrder α] [NoMinOrder α] {a : s}
  proof: isMin_of_pred_notMem
  mpr h nh := by
    replace h := congr($h.pred_eq.1)
    rw [coe_pred_of_mem nh] at h
    simp at h

中文:
引理 pred_notMem_iff_isMin
  条件: [PredOrder α] [NoMinOrder α] {a : s}
  证明: isMin_of_pred_notMem
  mpr h nh := by
    replace h := congr($h.pred_eq.1)
    rw [coe_pred_of_mem nh] at h
    simp at h

Depends on / 依赖: isMin_of_pred_notMem
-/
lemma pred_notMem_iff_isMin [PredOrder α] [NoMinOrder α] {a : s} :
    pred ↑a ∉ s ↔ IsMin a where
  mp := isMin_of_pred_notMem
  mpr h nh := by
    replace h := congr($h.pred_eq.1)
    rw [coe_pred_of_mem nh] at h
    simp at h

/--
Instance `Set.OrdConnected.succOrder` / 实例 `Set.OrdConnected.succOrder`

English:
instance Set.OrdConnected.succOrder
  signature: [SuccOrder α]
  body: letI : PredOrder sᵒᵈ := inferInstanceAs (PredOrder (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (SuccOrder sᵒᵈᵒᵈ)

中文:
实例 Set.OrdConnected.succOrder
  签名: [SuccOrder α]
  定义体: letI : PredOrder sᵒᵈ := inferInstanceAs (PredOrder (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (SuccOrder sᵒᵈᵒᵈ)

Depends on / 依赖: OrderDual, OrderDual.ofDual, PredOrder, SuccOrder, ofDual
-/
noncomputable instance Set.OrdConnected.succOrder [SuccOrder α] :
    SuccOrder s :=
  letI : PredOrder sᵒᵈ := inferInstanceAs (PredOrder (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (SuccOrder sᵒᵈᵒᵈ)

set_option backward.isDefEq.respectTransparency false in
@[simp, norm_cast]
/--
lemma `coe_succ_of_mem` / 引理 `coe_succ_of_mem`

English:
lemma coe_succ_of_mem
  given: [SuccOrder α] {a : s} (h : succ ↑a in s)
  proof: by classical
  change Subtype.val (dite ..) = _
  split_ifs <;> trivial

中文:
引理 coe_succ_of_mem
  条件: [SuccOrder α] {a : s} (h : succ ↑a in s)
  证明: by classical
  change Subtype.val (dite ..) = _
  split_ifs <;> trivial

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeffEquiv, Subtype, Subtype.val, classical, coeffEquiv, small_map, split_ifs
-/
lemma coe_succ_of_mem [SuccOrder α] {a : s} (h : succ ↑a in s) :
    (succ a).1 = succ ↑a := by classical
  change Subtype.val (dite ..) = _
  split_ifs <;> trivial

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isMax_of_succ_notMem` / 引理 `isMax_of_succ_notMem`

English:
lemma isMax_of_succ_notMem
  given: [SuccOrder α] {a : s} (h : succ ↑a ∉ s)
  statement: IsMax a
  proof: by
  classical
  rw [← succ_eq_iff_isMax]
  change dite .. = _
  split_ifs <;> trivial

中文:
引理 isMax_of_succ_notMem
  条件: [SuccOrder α] {a : s} (h : succ ↑a ∉ s)
  结论: IsMax a
  证明: by
  classical
  rw [← succ_eq_iff_isMax]
  change dite .. = _
  split_ifs <;> trivial

Depends on / 依赖: classical, split_ifs, succ_eq_iff_isMax
-/
lemma isMax_of_succ_notMem [SuccOrder α] {a : s} (h : succ ↑a ∉ s) : IsMax a := by
  classical
  rw [← succ_eq_iff_isMax]
  change dite .. = _
  split_ifs <;> trivial

/--
lemma `succ_notMem_iff_isMax` / 引理 `succ_notMem_iff_isMax`

English:
lemma succ_notMem_iff_isMax
  given: [SuccOrder α] [NoMaxOrder α] {a : s}
  proof: isMax_of_succ_notMem
  mpr h nh := by
    replace h := congr($h.succ_eq.1)
    rw [coe_succ_of_mem nh] at h
    simp at h

中文:
引理 succ_notMem_iff_isMax
  条件: [SuccOrder α] [NoMaxOrder α] {a : s}
  证明: isMax_of_succ_notMem
  mpr h nh := by
    replace h := congr($h.succ_eq.1)
    rw [coe_succ_of_mem nh] at h
    simp at h

Depends on / 依赖: isMax_of_succ_notMem
-/
lemma succ_notMem_iff_isMax [SuccOrder α] [NoMaxOrder α] {a : s} :
    succ ↑a ∉ s ↔ IsMax a where
  mp := isMax_of_succ_notMem
  mpr h nh := by
    replace h := congr($h.succ_eq.1)
    rw [coe_succ_of_mem nh] at h
    simp at h

end OrdConnected
