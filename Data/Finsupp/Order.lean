/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Aaron Anderson
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Order.Preorder.Finsupp

/-!
# Pointwise order on finitely supported functions

This file lifts order structures on `α` to `ι →₀ α`.

## Main declarations

* `Finsupp.orderEmbeddingToFun`: The order embedding from finitely supported functions to
  functions.
-/

public section

noncomputable section

open Finset

variable {ι κ α β : Type*}

namespace Finsupp

/-! ### Order structures -/


section Zero

variable [Zero α]

section OrderedAddCommMonoid
variable [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β] {f : ι ->₀ α} {h₁ h₂ : ι -> α -> β}

@[gcongr only]
/--
lemma `sum_le_sum` / 引理 `sum_le_sum`

English:
lemma sum_le_sum
  given: (h : forall i in f.support, h₁ i (f i) <= h₂ i (f i))
  statement: f.sum h₁ <= f.sum h₂
  proof: Finset.sum_le_sum h

中文:
引理 sum_le_sum
  条件: (h : 对任意 i in f.support, h₁ i (f i) <= h₂ i (f i))
  结论: f.sum h₁ <= f.sum h₂
  证明: Finset.sum_le_sum h

Depends on / 依赖: Finset, Finset.sum_le_sum, sum_le_sum
-/
lemma sum_le_sum (h : forall i in f.support, h₁ i (f i) <= h₂ i (f i)) : f.sum h₁ <= f.sum h₂ :=
  Finset.sum_le_sum h

/--
theorem `sum_nonneg` / 定理 `sum_nonneg`

English:
theorem sum_nonneg
  given: (h : forall i in f.support, 0 <= h₁ i (f i))
  statement: 0 <= f.sum h₁
  proof: Finset.sum_nonneg h

中文:
定理 sum_nonneg
  条件: (h : 对任意 i in f.support, 0 <= h₁ i (f i))
  结论: 0 <= f.sum h₁
  证明: Finset.sum_nonneg h

Depends on / 依赖: Finset, Finset.sum_nonneg, sum_nonneg
-/
theorem sum_nonneg (h : forall i in f.support, 0 <= h₁ i (f i)) : 0 <= f.sum h₁ := Finset.sum_nonneg h

/--
theorem `sum_nonneg'` / 定理 `sum_nonneg'`

English:
theorem sum_nonneg'
  given: (h : forall i, 0 <= h₁ i (f i))
  statement: 0 <= f.sum h₁
  proof: sum_nonneg fun _ _ => h _

中文:
定理 sum_nonneg'
  条件: (h : 对任意 i, 0 <= h₁ i (f i))
  结论: 0 <= f.sum h₁
  证明: sum_nonneg fun _ _ => h _

Depends on / 依赖: sum_nonneg
-/
theorem sum_nonneg' (h : forall i, 0 <= h₁ i (f i)) : 0 <= f.sum h₁ := sum_nonneg fun _ _ => h _

/--
theorem `sum_nonpos` / 定理 `sum_nonpos`

English:
theorem sum_nonpos
  given: (h : forall i in f.support, h₁ i (f i) <= 0)
  statement: f.sum h₁ <= 0
  proof: Finset.sum_nonpos h

中文:
定理 sum_nonpos
  条件: (h : 对任意 i in f.support, h₁ i (f i) <= 0)
  结论: f.sum h₁ <= 0
  证明: Finset.sum_nonpos h

Depends on / 依赖: Finset, Finset.sum_nonpos, sum_nonpos
-/
theorem sum_nonpos (h : forall i in f.support, h₁ i (f i) <= 0) : f.sum h₁ <= 0 := Finset.sum_nonpos h

end OrderedAddCommMonoid

section IsOrderedCancelAddMonoid

variable [AddCommMonoid β] [Preorder β] [IsOrderedCancelAddMonoid β] [AddLeftStrictMono β]
variable {f : ι ->₀ α} {g : ι -> α -> β}

/--
theorem `sum_pos` / 定理 `sum_pos`

English:
theorem sum_pos
  given: (h : forall i in f.support, 0 < g i (f i)) (hf : f != 0)
  statement: 0 < f.sum g
  proof: Finset.sum_pos h (by simpa)

中文:
定理 sum_pos
  条件: (h : 对任意 i in f.support, 0 < g i (f i)) (hf : f != 0)
  结论: 0 < f.sum g
  证明: Finset.sum_pos h (by simpa)

Depends on / 依赖: Finset, Finset.sum_pos, sum_pos
-/
theorem sum_pos (h : forall i in f.support, 0 < g i (f i)) (hf : f != 0) : 0 < f.sum g :=
  Finset.sum_pos h (by simpa)

/--
theorem `sum_pos'` / 定理 `sum_pos'`

English:
theorem sum_pos'
  given: (h : forall i in f.support, 0 <= g i (f i)) (hf : exists i in f.support, 0 < g i (f i))
  proof: Finset.sum_pos' h hf

中文:
定理 sum_pos'
  条件: (h : 对任意 i in f.support, 0 <= g i (f i)) (hf : 存在 i in f.support, 0 < g i (f i))
  证明: Finset.sum_pos' h hf

Depends on / 依赖: Finset, Finset.sum_pos, sum_pos
-/
theorem sum_pos' (h : forall i in f.support, 0 <= g i (f i)) (hf : exists i in f.support, 0 < g i (f i)) :
    0 < f.sum g := Finset.sum_pos' h hf

end IsOrderedCancelAddMonoid

section Preorder
variable [Preorder α] {f g : ι ->₀ α} {i : ι} {a b : α}

/--
lemma `single_le_single` / 引理 `single_le_single`

English:
lemma single_le_single
  statement: single i a <= single i b ↔ a <= b
  proof: by
  classical exact Pi.single_le_single

中文:
引理 single_le_single
  结论: single i a <= single i b ↔ a <= b
  证明: by
  classical exact Pi.single_le_single
-/
@[simp, gcongr] lemma single_le_single : single i a <= single i b ↔ a <= b := by
  classical exact Pi.single_le_single

/--
lemma `single_mono` / 引理 `single_mono`

English:
lemma single_mono
  statement: Monotone (single i : α -> ι ->₀ α)
  proof: fun _ _ => single_le_single.2

中文:
引理 single_mono
  结论: Monotone (single i : α -> ι ->₀ α)
  证明: fun _ _ => single_le_single.2

Depends on / 依赖: single_le_single
-/
lemma single_mono : Monotone (single i : α -> ι ->₀ α) := fun _ _ => single_le_single.2

/--
lemma `single_nonneg` / 引理 `single_nonneg`

English:
lemma single_nonneg
  statement: 0 <= single i a ↔ 0 <= a
  proof: by classical exact Pi.single_nonneg

中文:
引理 single_nonneg
  结论: 0 <= single i a ↔ 0 <= a
  证明: by classical exact Pi.single_nonneg
-/
@[simp] lemma single_nonneg : 0 <= single i a ↔ 0 <= a := by classical exact Pi.single_nonneg
/--
lemma `single_nonpos` / 引理 `single_nonpos`

English:
lemma single_nonpos
  statement: single i a <= 0 ↔ a <= 0
  proof: by classical exact Pi.single_nonpos

中文:
引理 single_nonpos
  结论: single i a <= 0 ↔ a <= 0
  证明: by classical exact Pi.single_nonpos
-/
@[simp] lemma single_nonpos : single i a <= 0 ↔ a <= 0 := by classical exact Pi.single_nonpos

variable [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]

/--
lemma `sum_le_sum_index` / 引理 `sum_le_sum_index`

English:
lemma sum_le_sum_index
  statement: [DecidableEq ι] {f₁ f₂ : ι ->₀ α} {h : ι -> α -> β} (hf : f₁ <= f₂)
  proof: by
  rw [sum_of_support_subset _ Finset.subset_union_left _ hh₀]; rw [sum_of_support_subset _ Finset.subset_union_right _ hh₀]
  gcongr with i hi
exact hh _ hi hf _

中文:
引理 sum_le_sum_index
  结论: [DecidableEq ι] {f₁ f₂ : ι ->₀ α} {h : ι -> α -> β} (hf : f₁ <= f₂)
  证明: by
  rw [sum_of_support_subset _ Finset.subset_union_left _ hh₀]; rw [sum_of_support_subset _ Finset.subset_union_right _ hh₀]
  gcongr with i hi
exact hh _ hi hf _

Depends on / 依赖: Finset, Finset.subset_union_left, Finset.subset_union_right, subset_union_left, subset_union_right, sum_of_support_subset
-/
lemma sum_le_sum_index [DecidableEq ι] {f₁ f₂ : ι ->₀ α} {h : ι -> α -> β} (hf : f₁ <= f₂)
    (hh : forall i in f₁.support union f₂.support, Monotone (h i))
    (hh₀ : forall i in f₁.support union f₂.support, h i 0 = 0) : f₁.sum h <= f₂.sum h := by
  rw [sum_of_support_subset _ Finset.subset_union_left _ hh₀]; rw [sum_of_support_subset _ Finset.subset_union_right _ hh₀]
  gcongr with i hi
exact hh _ hi hf _

end Preorder

section EmbDomain

@[gcongr]
/--
lemma `embDomain_le_embDomain_iff_le` / 引理 `embDomain_le_embDomain_iff_le`

English:
lemma embDomain_le_embDomain_iff_le
  statement: [LE α] [@Std.Refl α (· <= ·)]
  proof: by
  constructor
  · rw [Finsupp.le_def]
    intro h' x
    simpa [Finsupp.embDomain_apply] using h' (f x)
  intro h
  simp [Finsupp.le_def, embDomain_apply, apply_dite₂, Finsupp.le_def.mp h]

中文:
引理 embDomain_le_embDomain_iff_le
  结论: [LE α] [@Std.Refl α (· <= ·)]
  证明: by
  constructor
  · rw [Finsupp.le_def]
    intro h' x
    simpa [Finsupp.embDomain_apply] using h' (f x)
  intro h
  simp [Finsupp.le_def, embDomain_apply, apply_dite₂, Finsupp.le_def.mp h]

Depends on / 依赖: Finsupp, Finsupp.embDomain_apply, Finsupp.le_def, Finsupp.le_def.mp, embDomain_apply, le_def
-/
lemma embDomain_le_embDomain_iff_le [LE α] [@Std.Refl α (· <= ·)]
    (f : ι ↪ κ) (g₁ g₂ : ι ->₀ α) : g₁.embDomain f <= g₂.embDomain f ↔ g₁ <= g₂ := by
  constructor
  · rw [Finsupp.le_def]
    intro h' x
    simpa [Finsupp.embDomain_apply] using h' (f x)
  intro h
  simp [Finsupp.le_def, embDomain_apply, apply_dite₂, Finsupp.le_def.mp h]

/--
lemma `embDomain_mono` / 引理 `embDomain_mono`

English:
lemma embDomain_mono
  given: [Preorder α] (f : ι ↪ κ)
  statement: Monotone (embDomain f : (ι ->₀ α) -> (κ ->₀ α))
  proof: fun _ _ => (embDomain_le_embDomain_iff_le f _ _).mpr

@[gcongr]

中文:
引理 embDomain_mono
  条件: [Preorder α] (f : ι ↪ κ)
  结论: Monotone (embDomain f : (ι ->₀ α) -> (κ ->₀ α))
  证明: fun _ _ => (embDomain_le_embDomain_iff_le f _ _).mpr

@[gcongr]

Depends on / 依赖: embDomain_le_embDomain_iff_le
-/
lemma embDomain_mono [Preorder α] (f : ι ↪ κ) : Monotone (embDomain f : (ι ->₀ α) -> (κ ->₀ α)) :=
  fun _ _ => (embDomain_le_embDomain_iff_le f _ _).mpr

@[gcongr]
/--
lemma `embDomain_lt_embDomain_iff_lt` / 引理 `embDomain_lt_embDomain_iff_lt`

English:
lemma embDomain_lt_embDomain_iff_lt
  given: [Preorder α] (f : ι ↪ κ) (g₁ g₂ : ι ->₀ α)
  proof: by
  simp [lt_iff_le_not_ge, embDomain_le_embDomain_iff_le]

中文:
引理 embDomain_lt_embDomain_iff_lt
  条件: [Preorder α] (f : ι ↪ κ) (g₁ g₂ : ι ->₀ α)
  证明: by
  simp [lt_iff_le_not_ge, embDomain_le_embDomain_iff_le]

Depends on / 依赖: embDomain_le_embDomain_iff_le, lt_iff_le_not_ge
-/
lemma embDomain_lt_embDomain_iff_lt [Preorder α] (f : ι ↪ κ) (g₁ g₂ : ι ->₀ α) :
    g₁.embDomain f < g₂.embDomain f ↔ g₁ < g₂ := by
  simp [lt_iff_le_not_ge, embDomain_le_embDomain_iff_le]

end EmbDomain

end Zero

section MapDomain

variable [AddCommMonoid α]

/--
lemma `mapDomain_le_mapDomain_iff_le` / 引理 `mapDomain_le_mapDomain_iff_le`

English:
lemma mapDomain_le_mapDomain_iff_le
  statement: [LE α] [@Std.Refl α (· <= ·)] {f : ι -> κ} (h : f.Injective)
  proof: by
  simpa [Finsupp.embDomain_eq_mapDomain] using Finsupp.embDomain_le_embDomain_iff_le ⟨f, h⟩ g₁ g₂

中文:
引理 mapDomain_le_mapDomain_iff_le
  结论: [LE α] [@Std.Refl α (· <= ·)] {f : ι -> κ} (h : f.Injective)
  证明: by
  simpa [Finsupp.embDomain_eq_mapDomain] using Finsupp.embDomain_le_embDomain_iff_le ⟨f, h⟩ g₁ g₂

Depends on / 依赖: Finsupp, Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_le_embDomain_iff_le, embDomain_eq_mapDomain, embDomain_le_embDomain_iff_le
-/
lemma mapDomain_le_mapDomain_iff_le [LE α] [@Std.Refl α (· <= ·)] {f : ι -> κ} (h : f.Injective)
    (g₁ g₂ : ι ->₀ α) : g₁.mapDomain f <= g₂.mapDomain f ↔ g₁ <= g₂ := by
  simpa [Finsupp.embDomain_eq_mapDomain] using Finsupp.embDomain_le_embDomain_iff_le ⟨f, h⟩ g₁ g₂

/--
lemma `mapDomain_lt_mapDomain_iff_lt` / 引理 `mapDomain_lt_mapDomain_iff_lt`

English:
lemma mapDomain_lt_mapDomain_iff_lt
  statement: [Preorder α] {f : ι -> κ} (h : f.Injective)
  proof: by
  simpa [Finsupp.embDomain_eq_mapDomain] using Finsupp.embDomain_lt_embDomain_iff_lt ⟨f, h⟩ g₁ g₂

中文:
引理 mapDomain_lt_mapDomain_iff_lt
  结论: [Preorder α] {f : ι -> κ} (h : f.Injective)
  证明: by
  simpa [Finsupp.embDomain_eq_mapDomain] using Finsupp.embDomain_lt_embDomain_iff_lt ⟨f, h⟩ g₁ g₂

Depends on / 依赖: Finsupp, Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_lt_embDomain_iff_lt, embDomain_eq_mapDomain, embDomain_lt_embDomain_iff_lt
-/
lemma mapDomain_lt_mapDomain_iff_lt [Preorder α] {f : ι -> κ} (h : f.Injective)
    (g₁ g₂ : ι ->₀ α) : g₁.mapDomain f < g₂.mapDomain f ↔ g₁ < g₂ := by
  simpa [Finsupp.embDomain_eq_mapDomain] using Finsupp.embDomain_lt_embDomain_iff_lt ⟨f, h⟩ g₁ g₂

end MapDomain

/-! ### Algebraic order structures -/

section OrderedAddCommMonoid
variable [AddCommMonoid α] [Preorder α] [IsOrderedAddMonoid α]
  {i : ι} {f : ι -> κ} {g g₁ g₂ : ι ->₀ α}

/--
Instance `isOrderedAddMonoid` / 实例 `isOrderedAddMonoid`

English:
instance isOrderedAddMonoid
  signature: : IsOrderedAddMonoid (ι ->₀ α)
  body: { add_le_add_left := fun _a _b h c s => add_le_add_left (h s) (c s) }

@[gcongr]

中文:
实例 isOrderedAddMonoid
  签名: : IsOrderedAddMonoid (ι ->₀ α)
  定义体: { add_le_add_left := fun _a _b h c s => add_le_add_left (h s) (c s) }

@[gcongr]

Depends on / 依赖: add_le_add_left
-/
instance isOrderedAddMonoid : IsOrderedAddMonoid (ι ->₀ α) :=
  { add_le_add_left := fun _a _b h c s => add_le_add_left (h s) (c s) }

@[gcongr]
/--
lemma `mapDomain_mono` / 引理 `mapDomain_mono`

English:
lemma mapDomain_mono
  statement: Monotone (mapDomain f : (ι ->₀ α) -> (κ ->₀ α))
  proof: by
  classical exact fun g₁ g₂ h => sum_le_sum_index h (fun _ _ => single_mono) (by simp)

中文:
引理 mapDomain_mono
  结论: Monotone (mapDomain f : (ι ->₀ α) -> (κ ->₀ α))
  证明: by
  classical exact fun g₁ g₂ h => sum_le_sum_index h (fun _ _ => single_mono) (by simp)

Depends on / 依赖: classical, single_mono, sum_le_sum_index
-/
lemma mapDomain_mono : Monotone (mapDomain f : (ι ->₀ α) -> (κ ->₀ α)) := by
  classical exact fun g₁ g₂ h => sum_le_sum_index h (fun _ _ => single_mono) (by simp)

/--
lemma `mapDomain_nonneg` / 引理 `mapDomain_nonneg`

English:
lemma mapDomain_nonneg
  given: (hg : 0 <= g)
  statement: 0 <= g.mapDomain f
  proof: by simpa using mapDomain_mono hg

中文:
引理 mapDomain_nonneg
  条件: (hg : 0 <= g)
  结论: 0 <= g.mapDomain f
  证明: by simpa using mapDomain_mono hg

Depends on / 依赖: mapDomain_mono
-/
lemma mapDomain_nonneg (hg : 0 <= g) : 0 <= g.mapDomain f := by simpa using mapDomain_mono hg
/--
lemma `mapDomain_nonpos` / 引理 `mapDomain_nonpos`

English:
lemma mapDomain_nonpos
  given: (hg : g <= 0)
  statement: g.mapDomain f <= 0
  proof: by simpa using mapDomain_mono hg

中文:
引理 mapDomain_nonpos
  条件: (hg : g <= 0)
  结论: g.mapDomain f <= 0
  证明: by simpa using mapDomain_mono hg

Depends on / 依赖: mapDomain_mono
-/
lemma mapDomain_nonpos (hg : g <= 0) : g.mapDomain f <= 0 := by simpa using mapDomain_mono hg

/--
theorem `single_le_sum` / 定理 `single_le_sum`

English:
theorem single_le_sum
  statement: {α M N : Type*} [Zero M] [AddCommMonoid N]
  proof: by
  rcases eq_or_ne (f a) 0 with H | H
  · rw [H, single_zero, sum_zero_index]
    exact sum_nonneg' (fun i => h i (f i))
  · rw [sum, support_single _ H, sum_singleton, single_eq_same]
    apply Finset.single_le_sum (fun i hi => h i (f i))
    simpa [mem_support_iff, ne_eq] using H

中文:
定理 single_le_sum
  结论: {α M N : 类型} [Zero M] [AddCommMonoid N]
  证明: by
  rcases eq_or_ne (f a) 0 with H | H
  · rw [H, single_zero, sum_zero_index]
    exact sum_nonneg' (fun i => h i (f i))
  · rw [sum, support_single _ H, sum_singleton, single_eq_same]
    apply Finset.single_le_sum (fun i hi => h i (f i))
    simpa [mem_support_iff, ne_eq] using H

Depends on / 依赖: Finset, Finset.single_le_sum, eq_or_ne, mem_support_iff, ne_eq, single_eq_same, single_le_sum, single_zero, sum_nonneg, sum_singleton, sum_zero_index, support_single
-/
theorem single_le_sum {α M N : Type*} [Zero M] [AddCommMonoid N]
    [PartialOrder N] [IsOrderedAddMonoid N] (f : α ->₀ M) {g : α -> M -> N}
    (h : 0 <= (g · ·)) (a : α) :
    ((single a (f a)).sum g) <= f.sum g := by
  rcases eq_or_ne (f a) 0 with H | H
  · rw [H, single_zero, sum_zero_index]
    exact sum_nonneg' (fun i => h i (f i))
  · rw [sum, support_single _ H, sum_singleton, single_eq_same]
    apply Finset.single_le_sum (fun i hi => h i (f i))
    simpa [mem_support_iff, ne_eq] using H

/--
lemma `single_eval_le_sum` / 引理 `single_eval_le_sum`

English:
lemma single_eval_le_sum
  statement: {α M N : Type*} [Zero M] [AddCommMonoid N] [PartialOrder N]
  proof: by
  simp only [← sum_single_index (h := fun (_ : α) m => g m) (a := a) (b := f a) hg]
  apply single_le_sum _ (fun _ m => h m)

中文:
引理 single_eval_le_sum
  结论: {α M N : 类型} [Zero M] [AddCommMonoid N] [PartialOrder N]
  证明: by
  simp only [← sum_single_index (h := fun (_ : α) m => g m) (a := a) (b := f a) hg]
  apply single_le_sum _ (fun _ m => h m)

Depends on / 依赖: single_le_sum, sum_single_index
-/
lemma single_eval_le_sum {α M N : Type*} [Zero M] [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] (f : α ->₀ M) {g : M -> N} (hg : g 0 = 0) (h : 0 <= (g ·)) (a : α) :
    g (f a) <= f.sum fun _ m => g m := by
  simp only [← sum_single_index (h := fun (_ : α) m => g m) (a := a) (b := f a) hg]
  apply single_le_sum _ (fun _ m => h m)

end OrderedAddCommMonoid

/--
Instance `isOrderedCancelAddMonoid` / 实例 `isOrderedCancelAddMonoid`

English:
instance isOrderedCancelAddMonoid
  signature: [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α]
  body: { le_of_add_le_add_left := fun _f _g _i h s => le_of_add_le_add_left (h s) }

中文:
实例 isOrderedCancelAddMonoid
  签名: [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α]
  定义体: { le_of_add_le_add_left := fun _f _g _i h s => le_of_add_le_add_left (h s) }

Depends on / 依赖: le_of_add_le_add_left
-/
instance isOrderedCancelAddMonoid [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelAddMonoid (ι ->₀ α) :=
  { le_of_add_le_add_left := fun _f _g _i h s => le_of_add_le_add_left (h s) }

/--
Instance `addLeftReflectLE` / 实例 `addLeftReflectLE`

English:
instance addLeftReflectLE
  signature: [AddCommMonoid α] [Preorder α] [AddLeftReflectLE α]
  body: le_of_add_le_add_left H x

中文:
实例 addLeftReflectLE
  签名: [AddCommMonoid α] [Preorder α] [AddLeftReflectLE α]
  定义体: le_of_add_le_add_left H x

Depends on / 依赖: le_of_add_le_add_left
-/
instance addLeftReflectLE [AddCommMonoid α] [Preorder α] [AddLeftReflectLE α] :
    AddLeftReflectLE (ι ->₀ α) where
le_of_add_le_add_left H x := le_of_add_le_add_left H x

section SMulZeroClass
variable [Zero α] [Preorder α] [Zero β] [Preorder β] [SMulZeroClass α β]

/--
Instance `instPosSMulMono` / 实例 `instPosSMulMono`

English:
instance instPosSMulMono
  signature: [PosSMulMono α β]
  body: PosSMulMono.lift _ coe_le_coe coe_smul

中文:
实例 instPosSMulMono
  签名: [PosSMulMono α β]
  定义体: PosSMulMono.lift _ coe_le_coe coe_smul

Depends on / 依赖: PosSMulMono, PosSMulMono.lift, coe_le_coe, coe_smul
-/
instance instPosSMulMono [PosSMulMono α β] : PosSMulMono α (ι ->₀ β) :=
  PosSMulMono.lift _ coe_le_coe coe_smul

/--
Instance `instSMulPosMono` / 实例 `instSMulPosMono`

English:
instance instSMulPosMono
  signature: [SMulPosMono α β]
  body: SMulPosMono.lift _ coe_le_coe coe_smul coe_zero

中文:
实例 instSMulPosMono
  签名: [SMulPosMono α β]
  定义体: SMulPosMono.lift _ coe_le_coe coe_smul coe_zero

Depends on / 依赖: SMulPosMono, SMulPosMono.lift, coe_le_coe, coe_smul, coe_zero
-/
instance instSMulPosMono [SMulPosMono α β] : SMulPosMono α (ι ->₀ β) :=
  SMulPosMono.lift _ coe_le_coe coe_smul coe_zero

/--
Instance `instPosSMulReflectLE` / 实例 `instPosSMulReflectLE`

English:
instance instPosSMulReflectLE
  signature: [PosSMulReflectLE α β]
  body: PosSMulReflectLE.lift _ coe_le_coe coe_smul

中文:
实例 instPosSMulReflectLE
  签名: [PosSMulReflectLE α β]
  定义体: PosSMulReflectLE.lift _ coe_le_coe coe_smul

Depends on / 依赖: PosSMulReflectLE, PosSMulReflectLE.lift, coe_le_coe, coe_smul
-/
instance instPosSMulReflectLE [PosSMulReflectLE α β] : PosSMulReflectLE α (ι ->₀ β) :=
  PosSMulReflectLE.lift _ coe_le_coe coe_smul

/--
Instance `instSMulPosReflectLE` / 实例 `instSMulPosReflectLE`

English:
instance instSMulPosReflectLE
  signature: [SMulPosReflectLE α β]
  body: SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

中文:
实例 instSMulPosReflectLE
  签名: [SMulPosReflectLE α β]
  定义体: SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

Depends on / 依赖: SMulPosReflectLE, SMulPosReflectLE.lift, coe_le_coe, coe_smul, coe_zero
-/
instance instSMulPosReflectLE [SMulPosReflectLE α β] : SMulPosReflectLE α (ι ->₀ β) :=
  SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

end SMulZeroClass

section SMulWithZero
variable [Zero α] [PartialOrder α] [Zero β] [PartialOrder β] [SMulWithZero α β]

/--
Instance `instPosSMulStrictMono` / 实例 `instPosSMulStrictMono`

English:
instance instPosSMulStrictMono
  signature: [PosSMulStrictMono α β]
  body: PosSMulStrictMono.lift _ coe_le_coe coe_smul

中文:
实例 instPosSMulStrictMono
  签名: [PosSMulStrictMono α β]
  定义体: PosSMulStrictMono.lift _ coe_le_coe coe_smul

Depends on / 依赖: PosSMulStrictMono, PosSMulStrictMono.lift, coe_le_coe, coe_smul
-/
instance instPosSMulStrictMono [PosSMulStrictMono α β] : PosSMulStrictMono α (ι ->₀ β) :=
  PosSMulStrictMono.lift _ coe_le_coe coe_smul

/--
Instance `instSMulPosStrictMono` / 实例 `instSMulPosStrictMono`

English:
instance instSMulPosStrictMono
  signature: [SMulPosStrictMono α β]
  body: SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

中文:
实例 instSMulPosStrictMono
  签名: [SMulPosStrictMono α β]
  定义体: SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

Depends on / 依赖: SMulPosStrictMono, SMulPosStrictMono.lift, coe_le_coe, coe_smul, coe_zero
-/
instance instSMulPosStrictMono [SMulPosStrictMono α β] : SMulPosStrictMono α (ι ->₀ β) :=
  SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

-- `PosSMulReflectLT α (ι →₀ β)` already follows from the other instances

/--
Instance `instSMulPosReflectLT` / 实例 `instSMulPosReflectLT`

English:
instance instSMulPosReflectLT
  signature: [SMulPosReflectLT α β]
  body: SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

中文:
实例 instSMulPosReflectLT
  签名: [SMulPosReflectLT α β]
  定义体: SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

Depends on / 依赖: SMulPosReflectLT, SMulPosReflectLT.lift, coe_le_coe, coe_smul, coe_zero
-/
instance instSMulPosReflectLT [SMulPosReflectLT α β] : SMulPosReflectLT α (ι ->₀ β) :=
  SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

end SMulWithZero

section PartialOrder

variable [AddCommMonoid α] [PartialOrder α] {f g : ι ->₀ α}

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [IsBotZeroClass α]
  body: 0
  bot_le := by simp [le_def]

中文:
实例 orderBot
  签名: [IsBotZeroClass α]
  定义体: 0
  bot_le := by simp [le_def]
-/
instance orderBot [IsBotZeroClass α] : OrderBot (ι ->₀ α) where
  bot := 0
  bot_le := by simp [le_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsBotZeroClass
  signature: α] : IsBotZeroClass (ι ->₀ α) where
  body: isBot_bot

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]

中文:
实例 [IsBotZeroClass
  签名: α] : IsBotZeroClass (ι ->₀ α) where
  定义体: isBot_bot

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]

Depends on / 依赖: isBot_bot
-/
instance [IsBotZeroClass α] : IsBotZeroClass (ι ->₀ α) where
  isBot_zero := isBot_bot

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]
/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  given: [IsBotZeroClass α]
  statement: (⊥ : ι ->₀ α) = 0
  proof: rfl

中文:
定理 bot_eq_zero
  条件: [IsBotZeroClass α]
  结论: (⊥ : ι ->₀ α) = 0
  证明: rfl
-/
protected theorem bot_eq_zero [IsBotZeroClass α] : (⊥ : ι ->₀ α) = 0 :=
  rfl

variable [CanonicallyOrderedAdd α]

@[simp]
/--
theorem `add_eq_zero_iff` / 定理 `add_eq_zero_iff`

English:
theorem add_eq_zero_iff
  given: (f g : ι ->₀ α)
  statement: f + g = 0 ↔ f = 0 ∧ g = 0
  proof: by
  simp [DFunLike.ext_iff, forall_and]

中文:
定理 add_eq_zero_iff
  条件: (f g : ι ->₀ α)
  结论: f + g = 0 ↔ f = 0 ∧ g = 0
  证明: by
  simp [DFunLike.ext_iff, forall_and]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, forall_and
-/
theorem add_eq_zero_iff (f g : ι ->₀ α) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [DFunLike.ext_iff, forall_and]

/--
theorem `le_iff'` / 定理 `le_iff'`

English:
theorem le_iff'
  given: (f g : ι ->₀ α) {s : Finset ι} (hf : f.support subseteq s)
  proof: by
  refine ⟨fun h s _ => h s, fun h s => ?_⟩
  by_cases H : s in f.support
  · exact h s (hf H)
  · exact notMem_support_iff.1 H ▸ zero_le

中文:
定理 le_iff'
  条件: (f g : ι ->₀ α) {s : Finset ι} (hf : f.support subseteq s)
  证明: by
  refine ⟨fun h s _ => h s, fun h s => ?_⟩
  by_cases H : s in f.support
  · exact h s (hf H)
  · exact notMem_support_iff.1 H ▸ zero_le

Depends on / 依赖: f.support, notMem_support_iff, support, zero_le
-/
theorem le_iff' (f g : ι ->₀ α) {s : Finset ι} (hf : f.support subseteq s) :
    f <= g ↔ forall i in s, f i <= g i := by
  refine ⟨fun h s _ => h s, fun h s => ?_⟩
  by_cases H : s in f.support
  · exact h s (hf H)
  · exact notMem_support_iff.1 H ▸ zero_le

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  given: (f g : ι ->₀ α)
  statement: f <= g ↔ forall i in f.support, f i <= g i
  proof: le_iff' f g Subset.refl _

中文:
定理 le_iff
  条件: (f g : ι ->₀ α)
  结论: f <= g ↔ 对任意 i in f.support, f i <= g i
  证明: le_iff' f g Subset.refl _

Depends on / 依赖: Subset, Subset.refl, le_iff
-/
theorem le_iff (f g : ι ->₀ α) : f <= g ↔ forall i in f.support, f i <= g i :=
le_iff' f g Subset.refl _

/--
lemma `support_monotone` / 引理 `support_monotone`

English:
lemma support_monotone
  statement: Monotone (support (α := ι) (M := α))
  proof: fun f g h a ha => by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)

中文:
引理 support_monotone
  结论: Monotone (support (α := ι) (M := α))
  证明: fun f g h a ha => by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)
-/
lemma support_monotone : Monotone (support (α := ι) (M := α)) :=
  fun f g h a ha => by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)

/--
lemma `support_mono` / 引理 `support_mono`

English:
lemma support_mono
  given: (hfg : f <= g)
  statement: f.support subseteq g.support
  proof: support_monotone hfg

中文:
引理 support_mono
  条件: (hfg : f <= g)
  结论: f.support subseteq g.support
  证明: support_monotone hfg

Depends on / 依赖: support_monotone
-/
lemma support_mono (hfg : f <= g) : f.support subseteq g.support := support_monotone hfg

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: [DecidableLE α]
  body: fun f g =>
  decidable_of_iff _ (le_iff f g).symm

中文:
实例 decidableLE
  签名: [DecidableLE α]
  定义体: fun f g =>
  decidable_of_iff _ (le_iff f g).symm
-/
instance decidableLE [DecidableLE α] : DecidableLE (ι ->₀ α) := fun f g =>
  decidable_of_iff _ (le_iff f g).symm

/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: [DecidableLE α]
  body: decidableLTOfDecidableLE

@[simp]

中文:
实例 decidableLT
  签名: [DecidableLE α]
  定义体: decidableLTOfDecidableLE

@[simp]

Depends on / 依赖: decidableLTOfDecidableLE
-/
instance decidableLT [DecidableLE α] : DecidableLT (ι ->₀ α) :=
  decidableLTOfDecidableLE

@[simp]
/--
theorem `single_le_iff` / 定理 `single_le_iff`

English:
theorem single_le_iff
  given: {i : ι} {x : α} {f : ι ->₀ α}
  statement: single i x <= f ↔ x <= f i
  proof: (le_iff' _ _ support_single_subset).trans by simp

中文:
定理 single_le_iff
  条件: {i : ι} {x : α} {f : ι ->₀ α}
  结论: single i x <= f ↔ x <= f i
  证明: (le_iff' _ _ support_single_subset).trans by simp

Depends on / 依赖: Quot.lift, le_iff, recF_eq_of_Wequiv, support_single_subset
-/
theorem single_le_iff {i : ι} {x : α} {f : ι ->₀ α} : single i x <= f ↔ x <= f i :=
(le_iff' _ _ support_single_subset).trans by simp

variable [Sub α] [OrderedSub α] {f g : ι ->₀ α} {i : ι} {a b : α}

/--
Instance `tsub` / 实例 `tsub`

English:
instance tsub
  signature: : Sub (ι ->₀ α)
  body: ⟨zipWith (fun m n => m - n) (tsub_self 0)⟩

中文:
实例 tsub
  签名: : Sub (ι ->₀ α)
  定义体: ⟨zipWith (fun m n => m - n) (tsub_self 0)⟩

Depends on / 依赖: tsub_self, zipWith
-/
instance tsub : Sub (ι ->₀ α) :=
  ⟨zipWith (fun m n => m - n) (tsub_self 0)⟩

/--
Instance `orderedSub` / 实例 `orderedSub`

English:
instance orderedSub
  signature: : OrderedSub (ι ->₀ α)
  body: ⟨fun _n _m _k => forall_congr' fun _x => tsub_le_iff_right⟩

中文:
实例 orderedSub
  签名: : OrderedSub (ι ->₀ α)
  定义体: ⟨fun _n _m _k => forall_congr' fun _x => tsub_le_iff_right⟩

Depends on / 依赖: PFunctor, PFunctor.W.mk, Quot.mk, fixToW, forall_congr, q.P.map, tsub_le_iff_right
-/
instance orderedSub : OrderedSub (ι ->₀ α) :=
  ⟨fun _n _m _k => forall_congr' fun _x => tsub_le_iff_right⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddLeftMono
  signature: α] : CanonicallyOrderedAdd (ι ->₀ α) where
  body: fun {f g} h => ⟨g - f, ext fun x => (add_tsub_cancel_of_le <| h x).symm⟩
  le_add_self _ _ _ := le_add_self
  le_self_add := fun _f _g _x => le_self_add

中文:
实例 [AddLeftMono
  签名: α] : CanonicallyOrderedAdd (ι ->₀ α) where
  定义体: fun {f g} h => ⟨g - f, ext fun x => (add_tsub_cancel_of_le <| h x).symm⟩
  le_add_self _ _ _ := le_add_self
  le_self_add := fun _f _g _x => le_self_add

Depends on / 依赖: Fix.mk, Fix.rec, Functor, Functor.map, add_tsub_cancel_of_le
-/
instance [AddLeftMono α] : CanonicallyOrderedAdd (ι ->₀ α) where
  exists_add_of_le := fun {f g} h => ⟨g - f, ext fun x => (add_tsub_cancel_of_le <| h x).symm⟩
  le_add_self _ _ _ := le_add_self
  le_self_add := fun _f _g _x => le_self_add

/--
lemma `coe_tsub` / 引理 `coe_tsub`

English:
lemma coe_tsub
  given: (f g : ι ->₀ α)
  statement: ⇑(f - g) = f - g
  proof: rfl

中文:
引理 coe_tsub
  条件: (f g : ι ->₀ α)
  结论: ⇑(f - g) = f - g
  证明: rfl

Depends on / 依赖: Fix.mk, Fix.rec, PFunctor, PFunctor.W.dest_mk, PFunctor.map_eq, PFunctor.map_map, Wrepr_equiv, abs_map, abs_repr, dest_mk, fixToW, map_eq, map_map, recF_eq, recF_eq_of_Wequiv
-/
@[simp, norm_cast] lemma coe_tsub (f g : ι ->₀ α) : ⇑(f - g) = f - g := rfl

/--
theorem `tsub_apply` / 定理 `tsub_apply`

English:
theorem tsub_apply
  given: (f g : ι ->₀ α) (a : ι)
  statement: (f - g) a = f a - g a
  proof: rfl

@[simp]

中文:
定理 tsub_apply
  条件: (f g : ι ->₀ α) (a : ι)
  结论: (f - g) a = f a - g a
  证明: rfl

@[simp]

Depends on / 依赖: Fix.mk, Function, Function.comp, PFunctor, PFunctor.W.dest_mk, PFunctor.map_eq, Quot.sound, Wequiv, Wequiv.abs, Wrepr_equiv, abs_map, abs_repr, dest_mk, map_eq, recF_eq
-/
theorem tsub_apply (f g : ι ->₀ α) (a : ι) : (f - g) a = f a - g a :=
  rfl

@[simp]
/--
theorem `single_tsub` / 定理 `single_tsub`

English:
theorem single_tsub
  statement: single i (a - b) = single i a - single i b
  proof: by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

中文:
定理 single_tsub
  结论: single i (a - b) = single i a - single i b
  证明: by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

Depends on / 依赖: Fix.ind_aux, PFunctor, PFunctor.map_eq, abs_map, eq_or_ne, ind_aux, map_eq, single_eq_of_ne, single_eq_same, tsub_apply, tsub_self
-/
theorem single_tsub : single i (a - b) = single i a - single i b := by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

/--
theorem `support_tsub` / 定理 `support_tsub`

English:
theorem support_tsub
  given: {f1 f2 : ι ->₀ α}
  statement: (f1 - f2).support subseteq f1.support
  proof: by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]

中文:
定理 support_tsub
  条件: {f1 f2 : ι ->₀ α}
  结论: (f1 - f2).support subseteq f1.support
  证明: by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]

Depends on / 依赖: Fix.ind_rec, Fix.rec_eq, Pi.sub_apply, coe_tsub, contextual, imp_true_iff, ind_rec, mem_support_iff, not_imp_not, rec_eq, sub_apply, subset_iff, tsub_eq_zero_iff_le, zero_le
-/
theorem support_tsub {f1 f2 : ι ->₀ α} : (f1 - f2).support subseteq f1.support := by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]

/--
theorem `subset_support_tsub` / 定理 `subset_support_tsub`

English:
theorem subset_support_tsub
  given: [DecidableEq ι] {f1 f2 : ι ->₀ α}
  proof: by
  simp +contextual [subset_iff]

中文:
定理 subset_support_tsub
  条件: [DecidableEq ι] {f1 f2 : ι ->₀ α}
  证明: by
  simp +contextual [subset_iff]

Depends on / 依赖: Fix.dest, Fix.ind_rec, Fix.mk, Fix.rec_eq, Function, Function.comp_apply, comp_apply, comp_map, contextual, id_eq, id_map, ind_rec, rec_eq, subset_iff
-/
theorem subset_support_tsub [DecidableEq ι] {f1 f2 : ι ->₀ α} :
    f1.support \ f2.support subseteq (f1 - f2).support := by
  simp +contextual [subset_iff]

/--
lemma `mapDomain_tsub` / 引理 `mapDomain_tsub`

English:
lemma mapDomain_tsub
  given: {f : ι -> κ} (h : f.Injective) (f1 f2 : ι ->₀ α)
  proof: by
  ext y
  by_cases! hy : y ∉ Set.range f
  · simp [mapDomain_of_notMem_range _ _ hy]
  · obtain ⟨x, rfl⟩ := hy
    simp [mapDomain_apply h]

中文:
引理 mapDomain_tsub
  条件: {f : ι -> κ} (h : f.Injective) (f1 f2 : ι ->₀ α)
  证明: by
  ext y
  by_cases! hy : y ∉ Set.range f
  · simp [mapDomain_of_notMem_range _ _ hy]
  · obtain ⟨x, rfl⟩ := hy
    simp [mapDomain_apply h]

Depends on / 依赖: Fix.dest, Fix.mk_dest, Fix.rec_eq, Set.range, comp_map, id_map, mapDomain_apply, mapDomain_of_notMem_range, mk_dest, rec_eq
-/
lemma mapDomain_tsub {f : ι -> κ} (h : f.Injective) (f1 f2 : ι ->₀ α) :
    (f1 - f2).mapDomain f = f1.mapDomain f - f2.mapDomain f := by
  ext y
  by_cases! hy : y ∉ Set.range f
  · simp [mapDomain_of_notMem_range _ _ hy]
  · obtain ⟨x, rfl⟩ := hy
    simp [mapDomain_apply h]

/--
lemma `embDomain_tsub` / 引理 `embDomain_tsub`

English:
lemma embDomain_tsub
  given: (f : ι ↪ κ) (f1 f2 : ι ->₀ α)
  proof: by
  simp_rw [embDomain_eq_mapDomain, mapDomain_tsub f.injective]

中文:
引理 embDomain_tsub
  条件: (f : ι ↪ κ) (f1 f2 : ι ->₀ α)
  证明: by
  simp_rw [embDomain_eq_mapDomain, mapDomain_tsub f.injective]

Depends on / 依赖: Fix.ind_aux, convert, embDomain_eq_mapDomain, f.injective, ind_aux, injective, liftp_iff, mapDomain_tsub, simp_rw
-/
lemma embDomain_tsub (f : ι ↪ κ) (f1 f2 : ι ->₀ α) :
    (f1 - f2).embDomain f = f1.embDomain f - f2.embDomain f := by
  simp_rw [embDomain_eq_mapDomain, mapDomain_tsub f.injective]

/--
lemma `support_add_eq_union` / 引理 `support_add_eq_union`

English:
lemma support_add_eq_union
  given: {f1 f2 : ι ->₀ α} [DecidableEq ι]
  proof: le_antisymm support_add Finset.union_subset
    (support_mono le_self_add) (support_mono le_add_self)

中文:
引理 support_add_eq_union
  条件: {f1 f2 : ι ->₀ α} [DecidableEq ι]
  证明: le_antisymm support_add Finset.union_subset
    (support_mono le_self_add) (support_mono le_add_self)

Depends on / 依赖: Finset, Finset.union_subset, le_add_self, le_antisymm, le_self_add, support_add, support_mono, union_subset
-/
lemma support_add_eq_union {f1 f2 : ι ->₀ α} [DecidableEq ι] :
    (f1 + f2).support = f1.support union f2.support :=
le_antisymm support_add Finset.union_subset
    (support_mono le_self_add) (support_mono le_add_self)

end PartialOrder

section LinearOrder

variable [AddCommMonoid α] [LinearOrder α] [IsBotZeroClass α]

@[simp]
/--
theorem `support_inf` / 定理 `support_inf`

English:
theorem support_inf
  given: [DecidableEq ι] (f g : ι ->₀ α)
  statement: (f ⊓ g).support = f.support inter g.support
  proof: by
  ext
  simp

@[simp]

中文:
定理 support_inf
  条件: [DecidableEq ι] (f g : ι ->₀ α)
  结论: (f ⊓ g).support = f.support inter g.support
  证明: by
  ext
  simp

@[simp]
-/
theorem support_inf [DecidableEq ι] (f g : ι ->₀ α) : (f ⊓ g).support = f.support inter g.support := by
  ext
  simp

@[simp]
/--
theorem `support_sup` / 定理 `support_sup`

English:
theorem support_sup
  given: [DecidableEq ι] (f g : ι ->₀ α)
  statement: (f ⊔ g).support = f.support union g.support
  proof: by
  ext
  simp [imp_iff_not_or]

nonrec theorem disjoint_iff {f g : ι ->₀ α} : Disjoint f g ↔ Disjoint f.support g.support := by
  classical
  simp [disjoint_iff, bot_eq_zero, ← Finsupp.support_eq_empty]

中文:
定理 support_sup
  条件: [DecidableEq ι] (f g : ι ->₀ α)
  结论: (f ⊔ g).support = f.support union g.support
  证明: by
  ext
  simp [imp_iff_not_or]

nonrec theorem disjoint_iff {f g : ι ->₀ α} : Disjoint f g ↔ Disjoint f.support g.support := by
  classical
  simp [disjoint_iff, bot_eq_zero, ← Finsupp.support_eq_empty]

Depends on / 依赖: imp_iff_not_or
-/
theorem support_sup [DecidableEq ι] (f g : ι ->₀ α) : (f ⊔ g).support = f.support union g.support := by
  ext
  simp [imp_iff_not_or]

nonrec theorem disjoint_iff {f g : ι ->₀ α} : Disjoint f g ↔ Disjoint f.support g.support := by
  classical
  simp [disjoint_iff, bot_eq_zero, ← Finsupp.support_eq_empty]

end LinearOrder

/-! ### Some lemmas about `ℕ` -/

section Nat

/--
theorem `sub_single_one_add` / 定理 `sub_single_one_add`

English:
theorem sub_single_one_add
  given: {a : ι} {u u' : ι ->₀ Nat} (h : u a != 0)
  proof: tsub_add_eq_add_tsub single_le_iff.mpr Nat.one_le_iff_ne_zero.mpr h

中文:
定理 sub_single_one_add
  条件: {a : ι} {u u' : ι ->₀ 自然数} (h : u a != 0)
  证明: tsub_add_eq_add_tsub single_le_iff.mpr Nat.one_le_iff_ne_zero.mpr h

Depends on / 依赖: Nat.one_le_iff_ne_zero.mpr, one_le_iff_ne_zero, single_le_iff, single_le_iff.mpr, tsub_add_eq_add_tsub
-/
theorem sub_single_one_add {a : ι} {u u' : ι ->₀ Nat} (h : u a != 0) :
    u - single a 1 + u' = u + u' - single a 1 :=
tsub_add_eq_add_tsub single_le_iff.mpr Nat.one_le_iff_ne_zero.mpr h

/--
theorem `add_sub_single_one` / 定理 `add_sub_single_one`

English:
theorem add_sub_single_one
  given: {a : ι} {u u' : ι ->₀ Nat} (h : u' a != 0)
  proof: (add_tsub_assoc_of_le (single_le_iff.mpr <| Nat.one_le_iff_ne_zero.mpr h) _).symm

中文:
定理 add_sub_single_one
  条件: {a : ι} {u u' : ι ->₀ 自然数} (h : u' a != 0)
  证明: (add_tsub_assoc_of_le (single_le_iff.mpr <| Nat.one_le_iff_ne_zero.mpr h) _).symm

Depends on / 依赖: Nat.one_le_iff_ne_zero.mpr, add_tsub_assoc_of_le, one_le_iff_ne_zero, single_le_iff, single_le_iff.mpr
-/
theorem add_sub_single_one {a : ι} {u u' : ι ->₀ Nat} (h : u' a != 0) :
    u + (u' - single a 1) = u + u' - single a 1 :=
  (add_tsub_assoc_of_le (single_le_iff.mpr <| Nat.one_le_iff_ne_zero.mpr h) _).symm

/--
lemma `sub_add_single_one_cancel` / 引理 `sub_add_single_one_cancel`

English:
lemma sub_add_single_one_cancel
  given: {u : ι ->₀ Nat} {i : ι} (h : u i != 0)
  proof: by
  rw [sub_single_one_add h]; rw [add_tsub_cancel_right]

中文:
引理 sub_add_single_one_cancel
  条件: {u : ι ->₀ 自然数} {i : ι} (h : u i != 0)
  证明: by
  rw [sub_single_one_add h]; rw [add_tsub_cancel_right]

Depends on / 依赖: add_tsub_cancel_right, sub_single_one_add
-/
lemma sub_add_single_one_cancel {u : ι ->₀ Nat} {i : ι} (h : u i != 0) :
    u - single i 1 + single i 1 = u := by
  rw [sub_single_one_add h]; rw [add_tsub_cancel_right]

/--
theorem `isLowerSet_range_embDomain` / 定理 `isLowerSet_range_embDomain`

English:
theorem isLowerSet_range_embDomain
  given: (f : α ↪ β)
  proof: by
  rintro _ y h ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := exists_add_of_le h
  rw [mem_range_embDomain_iff]
  trans ↑(y + w).support
  · exact fun _ => by simp; grind
  · simp [← hw]

中文:
定理 isLowerSet_range_embDomain
  条件: (f : α ↪ β)
  证明: by
  rintro _ y h ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := exists_add_of_le h
  rw [mem_range_embDomain_iff]
  trans ↑(y + w).support
  · exact fun _ => by simp; grind
  · simp [← hw]

Depends on / 依赖: Quot.mk, corecF, exists_add_of_le, mem_range_embDomain_iff, support
-/
theorem isLowerSet_range_embDomain (f : α ↪ β) :
    IsLowerSet ((Set.range (embDomain f)) : Set (β ->₀ Nat)) := by
  rintro _ y h ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := exists_add_of_le h
  rw [mem_range_embDomain_iff]
  trans ↑(y + w).support
  · exact fun _ => by simp; grind
  · simp [← hw]

end Nat

end Finsupp
