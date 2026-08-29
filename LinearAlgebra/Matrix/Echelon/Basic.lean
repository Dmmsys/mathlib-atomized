/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.RelClasses

import Mathlib.Order.WellFounded


/-!
# Row echelon forms

This file defines the row echelon form of matrices and the leading entries of their rows.

## Main definitions

- `Matrix.IsRowEchelon` expresses that `A` is in row echelon form: an entry of a lower row
  vanishes whenever a higher row is zero at every column strictly to its left.
- `Matrix.IsLeadingEntry`: `c : n` is the leading position of row `i` of `A`.
- `Matrix.IsReducedRowEchelon` additionally requires each leading entry to be `1` and the
  entries above it to vanish.

## Tags

matrix, echelon form

-/

@[expose] public section

universe v

variable {m n : Type*}
variable {R : Type v} {A : Matrix m n R}

namespace Matrix

variable [Zero R]

/--
Definition of `IsRowEchelon` / `IsRowEchelon` 的定义

English:
definition IsRowEchelon
  signature: [LT m] [LT n] (A : Matrix m n R)
  body: forall ⦃i₁ i₂⦄, i₁ < i₂ -> forall ⦃j₂⦄, (forall j₁ < j₂, A i₁ j₁ = 0) -> A i₂ j₂ = 0

中文:
定义 IsRowEchelon
  签名: [LT m] [LT n] (A : Matrix m n R)
  定义体: forall ⦃i₁ i₂⦄, i₁ < i₂ -> forall ⦃j₂⦄, (forall j₁ < j₂, A i₁ j₁ = 0) -> A i₂ j₂ = 0
-/
def IsRowEchelon [LT m] [LT n] (A : Matrix m n R) : Prop :=
  forall ⦃i₁ i₂⦄, i₁ < i₂ -> forall ⦃j₂⦄, (forall j₁ < j₂, A i₁ j₁ = 0) -> A i₂ j₂ = 0

/--
theorem `IsRowEchelon.row_eq_zero_of_lt` / 定理 `IsRowEchelon.row_eq_zero_of_lt`

English:
theorem IsRowEchelon.row_eq_zero_of_lt
  statement: [LT m] [LT n] {i₁ i₂ : m} (he : A.IsRowEchelon)
  proof: by
  funext j
  exact he hlt fun j₁ _ => congrFun h0 j₁

中文:
定理 IsRowEchelon.row_eq_zero_of_lt
  结论: [LT m] [LT n] {i₁ i₂ : m} (he : A.IsRowEchelon)
  证明: by
  funext j
  exact he hlt fun j₁ _ => congrFun h0 j₁
-/
theorem IsRowEchelon.row_eq_zero_of_lt [LT m] [LT n] {i₁ i₂ : m} (he : A.IsRowEchelon)
    (hlt : i₁ < i₂) (h0 : A i₁ = 0) : A i₂ = 0 := by
  funext j
  exact he hlt fun j₁ _ => congrFun h0 j₁

/-! ### Leading entries -/

/--
Definition of `IsLeadingEntry` / `IsLeadingEntry` 的定义

English:
definition IsLeadingEntry
  signature: [LT n] (A : Matrix m n R) (i : m) (c : n)
  body: (forall j < c, A i j = 0) ∧ A i c != 0

中文:
定义 IsLeadingEntry
  签名: [LT n] (A : Matrix m n R) (i : m) (c : n)
  定义体: (forall j < c, A i j = 0) ∧ A i c != 0
-/
def IsLeadingEntry [LT n] (A : Matrix m n R) (i : m) (c : n) : Prop :=
  (forall j < c, A i j = 0) ∧ A i c != 0

/--
theorem `IsLeadingEntry.row_ne_zero` / 定理 `IsLeadingEntry.row_ne_zero`

English:
theorem IsLeadingEntry.row_ne_zero
  given: [LT n] {i : m} {c : n} (hc : A.IsLeadingEntry i c)
  proof: fun contra => hc.2 (congrFun contra c)

中文:
定理 IsLeadingEntry.row_ne_zero
  条件: [LT n] {i : m} {c : n} (hc : A.IsLeadingEntry i c)
  证明: fun contra => hc.2 (congrFun contra c)

Depends on / 依赖: contra
-/
theorem IsLeadingEntry.row_ne_zero [LT n] {i : m} {c : n} (hc : A.IsLeadingEntry i c) :
    A i != 0 :=
  fun contra => hc.2 (congrFun contra c)

/--
theorem `row_ne_zero_iff_exists_isLeadingEntry` / 定理 `row_ne_zero_iff_exists_isLeadingEntry`

English:
theorem row_ne_zero_iff_exists_isLeadingEntry
  given: [LT n] [WellFoundedLT n] {i : m}
  proof: by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc.row_ne_zero⟩
obtain ⟨c, hc, hmin⟩ := wellFounded_lt.has_min {j | A i j != 0} Function.ne_iff.mp h
  refine ⟨c, ?_, hc⟩
  by_contra
  aesop

中文:
定理 row_ne_zero_iff_exists_isLeadingEntry
  条件: [LT n] [WellFoundedLT n] {i : m}
  证明: by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc.row_ne_zero⟩
obtain ⟨c, hc, hmin⟩ := wellFounded_lt.has_min {j | A i j != 0} Function.ne_iff.mp h
  refine ⟨c, ?_, hc⟩
  by_contra
  aesop

Depends on / 依赖: Function, Function.ne_iff.mp, has_min, hc.row_ne_zero, ne_iff, row_ne_zero, wellFounded_lt, wellFounded_lt.has_min
-/
theorem row_ne_zero_iff_exists_isLeadingEntry [LT n] [WellFoundedLT n] {i : m} :
    A i != 0 ↔ exists c, A.IsLeadingEntry i c := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc.row_ne_zero⟩
obtain ⟨c, hc, hmin⟩ := wellFounded_lt.has_min {j | A i j != 0} Function.ne_iff.mp h
  refine ⟨c, ?_, hc⟩
  by_contra
  aesop

/--
theorem `IsLeadingEntry.unique` / 定理 `IsLeadingEntry.unique`

English:
theorem IsLeadingEntry.unique
  statement: [LinearOrder n] {i : m} {c₁ c₂ : n}
  proof: le_antisymm (not_lt.mp fun hlt => h₂.2 (h₁.1 c₂ hlt)) (not_lt.mp fun hlt => h₁.2 (h₂.1 c₁ hlt))

中文:
定理 IsLeadingEntry.unique
  结论: [LinearOrder n] {i : m} {c₁ c₂ : n}
  证明: le_antisymm (not_lt.mp fun hlt => h₂.2 (h₁.1 c₂ hlt)) (not_lt.mp fun hlt => h₁.2 (h₂.1 c₁ hlt))

Depends on / 依赖: le_antisymm, not_lt, not_lt.mp
-/
theorem IsLeadingEntry.unique [LinearOrder n] {i : m} {c₁ c₂ : n}
    (h₁ : A.IsLeadingEntry i c₁) (h₂ : A.IsLeadingEntry i c₂) : c₁ = c₂ :=
  le_antisymm (not_lt.mp fun hlt => h₂.2 (h₁.1 c₂ hlt)) (not_lt.mp fun hlt => h₁.2 (h₂.1 c₁ hlt))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: R] [Fintype n] [LT n] [DecidableLT n]
  body: decidable_of_iff ((forall j < c, A i j = 0) ∧ A i c != 0) Iff.rfl

中文:
实例 [DecidableEq
  签名: R] [Fintype n] [LT n] [DecidableLT n]
  定义体: decidable_of_iff ((forall j < c, A i j = 0) ∧ A i c != 0) Iff.rfl

Depends on / 依赖: Iff.rfl, decidable_of_iff
-/
instance [DecidableEq R] [Fintype n] [LT n] [DecidableLT n]
    (A : Matrix m n R) (i : m) (c : n) : Decidable (A.IsLeadingEntry i c) :=
  decidable_of_iff ((forall j < c, A i j = 0) ∧ A i c != 0) Iff.rfl

/-! ### Reduced row echelon form -/

/--
Definition of `IsReducedRowEchelon` / `IsReducedRowEchelon` 的定义

English:
structure IsReducedRowEchelon
  parameters: [LT m] [LT n] [One R] (A : Matrix m n R)
  axioms and operations (3):
    - isRowEchelon : A.IsRowEchelon
    - eq_one(⦃i) : m⦄ ⦃c : n⦄ (hA : A.IsLeadingEntry i c) : A i c = 1
    - eq_zero(⦃i₁ i₂) : m⦄ ⦃c : n⦄ (hlt : i₁ < i₂) (hA : A.IsLeadingEntry i₂ c) : A i₁ c = 0

中文:
结构 IsReducedRowEchelon
  参数: [LT m] [LT n] [One R] (A : Matrix m n R)
  公理与运算 (3 个):
    - isRowEchelon : A.IsRowEchelon
    - eq_one(⦃i) : m⦄ ⦃c : n⦄ (hA : A.IsLeadingEntry i c) : A i c = 1
    - eq_zero(⦃i₁ i₂) : m⦄ ⦃c : n⦄ (hlt : i₁ < i₂) (hA : A.IsLeadingEntry i₂ c) : A i₁ c = 0
-/
structure IsReducedRowEchelon [LT m] [LT n] [One R] (A : Matrix m n R) : Prop where
  isRowEchelon : A.IsRowEchelon
  eq_one ⦃i : m⦄ ⦃c : n⦄ (hA : A.IsLeadingEntry i c) : A i c = 1
  eq_zero ⦃i₁ i₂ : m⦄ ⦃c : n⦄ (hlt : i₁ < i₂) (hA : A.IsLeadingEntry i₂ c) : A i₁ c = 0

/--
theorem `IsReducedRowEchelon.eq_zero_of_ne_of_isLeadingEntry` / 定理 `IsReducedRowEchelon.eq_zero_of_ne_of_isLeadingEntry`

English:
theorem IsReducedRowEchelon.eq_zero_of_ne_of_isLeadingEntry
  statement: [LinearOrder m] [LT n] [One R]
  proof: by
  rcases hne.lt_or_gt with hlt | hlt
  · exact hA.eq_zero hlt hlead
  · exact hA.isRowEchelon hlt hlead.1

中文:
定理 IsReducedRowEchelon.eq_zero_of_ne_of_isLeadingEntry
  结论: [LinearOrder m] [LT n] [One R]
  证明: by
  rcases hne.lt_or_gt with hlt | hlt
  · exact hA.eq_zero hlt hlead
  · exact hA.isRowEchelon hlt hlead.1

Depends on / 依赖: eq_zero, hA.eq_zero, hA.isRowEchelon, hne.lt_or_gt, isRowEchelon, lt_or_gt
-/
theorem IsReducedRowEchelon.eq_zero_of_ne_of_isLeadingEntry [LinearOrder m] [LT n] [One R]
    {i₁ i₂ : m} {c : n} (hA : A.IsReducedRowEchelon) (hne : i₁ != i₂)
    (hlead : A.IsLeadingEntry i₂ c) : A i₁ c = 0 := by
  rcases hne.lt_or_gt with hlt | hlt
  · exact hA.eq_zero hlt hlead
  · exact hA.isRowEchelon hlt hlead.1

end Matrix
