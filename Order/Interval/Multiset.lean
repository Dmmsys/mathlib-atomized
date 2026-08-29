/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Finset.Basic

/-!
# Intervals as multisets

This file defines intervals as multisets.

## Main declarations

In a `LocallyFiniteOrder`,
* `Multiset.Icc`: Closed-closed interval as a multiset.
* `Multiset.Ico`: Closed-open interval as a multiset.
* `Multiset.Ioc`: Open-closed interval as a multiset.
* `Multiset.Ioo`: Open-open interval as a multiset.

In a `LocallyFiniteOrderTop`,
* `Multiset.Ici`: Closed-infinite interval as a multiset.
* `Multiset.Ioi`: Open-infinite interval as a multiset.

In a `LocallyFiniteOrderBot`,
* `Multiset.Iic`: Infinite-open interval as a multiset.
* `Multiset.Iio`: Infinite-closed interval as a multiset.

## TODO

Do we really need this file at all? (March 2024)
-/

@[expose] public section


variable {α : Type*}

namespace Multiset

section LocallyFiniteOrder
variable [Preorder α] [LocallyFiniteOrder α] {a b x : α}

/--
Definition of `Icc` / `Icc` 的定义

English:
definition Icc
  signature: (a b : α)
  body: (Finset.Icc a b).val

中文:
定义 Icc
  签名: (a b : α)
  定义体: (Finset.Icc a b).val

Depends on / 依赖: Finset, Finset.Icc
-/
def Icc (a b : α) : Multiset α := (Finset.Icc a b).val

/--
Definition of `Ico` / `Ico` 的定义

English:
definition Ico
  signature: (a b : α)
  body: (Finset.Ico a b).val

中文:
定义 Ico
  签名: (a b : α)
  定义体: (Finset.Ico a b).val

Depends on / 依赖: Finset, Finset.Ico
-/
def Ico (a b : α) : Multiset α := (Finset.Ico a b).val

/--
Definition of `Ioc` / `Ioc` 的定义

English:
definition Ioc
  signature: (a b : α)
  body: (Finset.Ioc a b).val

中文:
定义 Ioc
  签名: (a b : α)
  定义体: (Finset.Ioc a b).val

Depends on / 依赖: Finset, Finset.Ioc
-/
def Ioc (a b : α) : Multiset α := (Finset.Ioc a b).val

/--
Definition of `Ioo` / `Ioo` 的定义

English:
definition Ioo
  signature: (a b : α)
  body: (Finset.Ioo a b).val

中文:
定义 Ioo
  签名: (a b : α)
  定义体: (Finset.Ioo a b).val

Depends on / 依赖: Finset, Finset.Ioo
-/
def Ioo (a b : α) : Multiset α := (Finset.Ioo a b).val

/--
lemma `mem_Icc` / 引理 `mem_Icc`

English:
lemma mem_Icc
  statement: x in Icc a b ↔ a <= x ∧ x <= b
  proof: by rw [Icc, ← Finset.mem_def, Finset.mem_Icc]

中文:
引理 mem_Icc
  结论: x in Icc a b ↔ a <= x ∧ x <= b
  证明: by rw [Icc, ← Finset.mem_def, Finset.mem_Icc]
-/
@[simp] lemma mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b := by rw [Icc, ← Finset.mem_def, Finset.mem_Icc]

/--
lemma `mem_Ico` / 引理 `mem_Ico`

English:
lemma mem_Ico
  statement: x in Ico a b ↔ a <= x ∧ x < b
  proof: by rw [Ico, ← Finset.mem_def, Finset.mem_Ico]

中文:
引理 mem_Ico
  结论: x in Ico a b ↔ a <= x ∧ x < b
  证明: by rw [Ico, ← Finset.mem_def, Finset.mem_Ico]
-/
@[simp] lemma mem_Ico : x in Ico a b ↔ a <= x ∧ x < b := by rw [Ico, ← Finset.mem_def, Finset.mem_Ico]

/--
lemma `mem_Ioc` / 引理 `mem_Ioc`

English:
lemma mem_Ioc
  statement: x in Ioc a b ↔ a < x ∧ x <= b
  proof: by rw [Ioc, ← Finset.mem_def, Finset.mem_Ioc]

中文:
引理 mem_Ioc
  结论: x in Ioc a b ↔ a < x ∧ x <= b
  证明: by rw [Ioc, ← Finset.mem_def, Finset.mem_Ioc]
-/
@[simp] lemma mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b := by rw [Ioc, ← Finset.mem_def, Finset.mem_Ioc]

/--
lemma `mem_Ioo` / 引理 `mem_Ioo`

English:
lemma mem_Ioo
  statement: x in Ioo a b ↔ a < x ∧ x < b
  proof: by rw [Ioo, ← Finset.mem_def, Finset.mem_Ioo]

中文:
引理 mem_Ioo
  结论: x in Ioo a b ↔ a < x ∧ x < b
  证明: by rw [Ioo, ← Finset.mem_def, Finset.mem_Ioo]
-/
@[simp] lemma mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b := by rw [Ioo, ← Finset.mem_def, Finset.mem_Ioo]

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [Preorder α] [LocallyFiniteOrderTop α] {a x : α}

/--
Definition of `Ici` / `Ici` 的定义

English:
definition Ici
  signature: (a : α)
  body: (Finset.Ici a).val

中文:
定义 Ici
  签名: (a : α)
  定义体: (Finset.Ici a).val

Depends on / 依赖: Finset, Finset.Ici
-/
def Ici (a : α) : Multiset α := (Finset.Ici a).val

/--
Definition of `Ioi` / `Ioi` 的定义

English:
definition Ioi
  signature: (a : α)
  body: (Finset.Ioi a).val

中文:
定义 Ioi
  签名: (a : α)
  定义体: (Finset.Ioi a).val

Depends on / 依赖: Finset, Finset.Ioi
-/
def Ioi (a : α) : Multiset α := (Finset.Ioi a).val

/--
lemma `mem_Ici` / 引理 `mem_Ici`

English:
lemma mem_Ici
  statement: x in Ici a ↔ a <= x
  proof: by rw [Ici, ← Finset.mem_def, Finset.mem_Ici]

中文:
引理 mem_Ici
  结论: x in Ici a ↔ a <= x
  证明: by rw [Ici, ← Finset.mem_def, Finset.mem_Ici]
-/
@[simp] lemma mem_Ici : x in Ici a ↔ a <= x := by rw [Ici, ← Finset.mem_def, Finset.mem_Ici]

/--
lemma `mem_Ioi` / 引理 `mem_Ioi`

English:
lemma mem_Ioi
  statement: x in Ioi a ↔ a < x
  proof: by rw [Ioi, ← Finset.mem_def, Finset.mem_Ioi]

中文:
引理 mem_Ioi
  结论: x in Ioi a ↔ a < x
  证明: by rw [Ioi, ← Finset.mem_def, Finset.mem_Ioi]
-/
@[simp] lemma mem_Ioi : x in Ioi a ↔ a < x := by rw [Ioi, ← Finset.mem_def, Finset.mem_Ioi]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [Preorder α] [LocallyFiniteOrderBot α] {b x : α}

/--
Definition of `Iic` / `Iic` 的定义

English:
definition Iic
  signature: (b : α)
  body: (Finset.Iic b).val

中文:
定义 Iic
  签名: (b : α)
  定义体: (Finset.Iic b).val

Depends on / 依赖: Finset, Finset.Iic
-/
def Iic (b : α) : Multiset α := (Finset.Iic b).val

/--
Definition of `Iio` / `Iio` 的定义

English:
definition Iio
  signature: (b : α)
  body: (Finset.Iio b).val

中文:
定义 Iio
  签名: (b : α)
  定义体: (Finset.Iio b).val

Depends on / 依赖: Finset, Finset.Iio
-/
def Iio (b : α) : Multiset α := (Finset.Iio b).val

/--
lemma `mem_Iic` / 引理 `mem_Iic`

English:
lemma mem_Iic
  statement: x in Iic b ↔ x <= b
  proof: by rw [Iic, ← Finset.mem_def, Finset.mem_Iic]

中文:
引理 mem_Iic
  结论: x in Iic b ↔ x <= b
  证明: by rw [Iic, ← Finset.mem_def, Finset.mem_Iic]
-/
@[simp] lemma mem_Iic : x in Iic b ↔ x <= b := by rw [Iic, ← Finset.mem_def, Finset.mem_Iic]

/--
lemma `mem_Iio` / 引理 `mem_Iio`

English:
lemma mem_Iio
  statement: x in Iio b ↔ x < b
  proof: by rw [Iio, ← Finset.mem_def, Finset.mem_Iio]

中文:
引理 mem_Iio
  结论: x in Iio b ↔ x < b
  证明: by rw [Iio, ← Finset.mem_def, Finset.mem_Iio]
-/
@[simp] lemma mem_Iio : x in Iio b ↔ x < b := by rw [Iio, ← Finset.mem_def, Finset.mem_Iio]

end LocallyFiniteOrderBot

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] {a b c : α}

/--
theorem `nodup_Icc` / 定理 `nodup_Icc`

English:
theorem nodup_Icc
  statement: (Icc a b).Nodup
  proof: Finset.nodup _

中文:
定理 nodup_Icc
  结论: (Icc a b).Nodup
  证明: Finset.nodup _

Depends on / 依赖: Finset, Finset.nodup
-/
theorem nodup_Icc : (Icc a b).Nodup :=
  Finset.nodup _

/--
theorem `nodup_Ico` / 定理 `nodup_Ico`

English:
theorem nodup_Ico
  statement: (Ico a b).Nodup
  proof: Finset.nodup _

中文:
定理 nodup_Ico
  结论: (Ico a b).Nodup
  证明: Finset.nodup _

Depends on / 依赖: Finset, Finset.nodup
-/
theorem nodup_Ico : (Ico a b).Nodup :=
  Finset.nodup _

/--
theorem `nodup_Ioc` / 定理 `nodup_Ioc`

English:
theorem nodup_Ioc
  statement: (Ioc a b).Nodup
  proof: Finset.nodup _

中文:
定理 nodup_Ioc
  结论: (Ioc a b).Nodup
  证明: Finset.nodup _

Depends on / 依赖: Finset, Finset.nodup
-/
theorem nodup_Ioc : (Ioc a b).Nodup :=
  Finset.nodup _

/--
theorem `nodup_Ioo` / 定理 `nodup_Ioo`

English:
theorem nodup_Ioo
  statement: (Ioo a b).Nodup
  proof: Finset.nodup _

@[simp]

中文:
定理 nodup_Ioo
  结论: (Ioo a b).Nodup
  证明: Finset.nodup _

@[simp]

Depends on / 依赖: Finset, Finset.nodup
-/
theorem nodup_Ioo : (Ioo a b).Nodup :=
  Finset.nodup _

@[simp]
/--
theorem `Icc_eq_zero_iff` / 定理 `Icc_eq_zero_iff`

English:
theorem Icc_eq_zero_iff
  statement: Icc a b = 0 ↔ ¬a <= b
  proof: by
  rw [Icc]; rw [Finset.val_eq_zero]; rw [Finset.Icc_eq_empty_iff]

@[simp]

中文:
定理 Icc_eq_zero_iff
  结论: Icc a b = 0 ↔ ¬a <= b
  证明: by
  rw [Icc]; rw [Finset.val_eq_zero]; rw [Finset.Icc_eq_empty_iff]

@[simp]

Depends on / 依赖: Finset, Finset.Icc_eq_empty_iff, Finset.val_eq_zero, Icc_eq_empty_iff, val_eq_zero
-/
theorem Icc_eq_zero_iff : Icc a b = 0 ↔ ¬a <= b := by
  rw [Icc]; rw [Finset.val_eq_zero]; rw [Finset.Icc_eq_empty_iff]

@[simp]
/--
theorem `Ico_eq_zero_iff` / 定理 `Ico_eq_zero_iff`

English:
theorem Ico_eq_zero_iff
  statement: Ico a b = 0 ↔ ¬a < b
  proof: by
  rw [Ico]; rw [Finset.val_eq_zero]; rw [Finset.Ico_eq_empty_iff]

@[simp]

中文:
定理 Ico_eq_zero_iff
  结论: Ico a b = 0 ↔ ¬a < b
  证明: by
  rw [Ico]; rw [Finset.val_eq_zero]; rw [Finset.Ico_eq_empty_iff]

@[simp]

Depends on / 依赖: Finset, Finset.Ico_eq_empty_iff, Finset.val_eq_zero, Ico_eq_empty_iff, val_eq_zero
-/
theorem Ico_eq_zero_iff : Ico a b = 0 ↔ ¬a < b := by
  rw [Ico]; rw [Finset.val_eq_zero]; rw [Finset.Ico_eq_empty_iff]

@[simp]
/--
theorem `Ioc_eq_zero_iff` / 定理 `Ioc_eq_zero_iff`

English:
theorem Ioc_eq_zero_iff
  statement: Ioc a b = 0 ↔ ¬a < b
  proof: by
  rw [Ioc]; rw [Finset.val_eq_zero]; rw [Finset.Ioc_eq_empty_iff]

@[simp]

中文:
定理 Ioc_eq_zero_iff
  结论: Ioc a b = 0 ↔ ¬a < b
  证明: by
  rw [Ioc]; rw [Finset.val_eq_zero]; rw [Finset.Ioc_eq_empty_iff]

@[simp]

Depends on / 依赖: Finset, Finset.Ioc_eq_empty_iff, Finset.val_eq_zero, Ioc_eq_empty_iff, val_eq_zero
-/
theorem Ioc_eq_zero_iff : Ioc a b = 0 ↔ ¬a < b := by
  rw [Ioc]; rw [Finset.val_eq_zero]; rw [Finset.Ioc_eq_empty_iff]

@[simp]
/--
theorem `Ioo_eq_zero_iff` / 定理 `Ioo_eq_zero_iff`

English:
theorem Ioo_eq_zero_iff
  given: [DenselyOrdered α]
  statement: Ioo a b = 0 ↔ ¬a < b
  proof: by
  rw [Ioo]; rw [Finset.val_eq_zero]; rw [Finset.Ioo_eq_empty_iff]

alias ⟨_, Icc_eq_zero⟩ := Icc_eq_zero_iff

alias ⟨_, Ico_eq_zero⟩ := Ico_eq_zero_iff

alias ⟨_, Ioc_eq_zero⟩ := Ioc_eq_zero_iff

@[simp]

中文:
定理 Ioo_eq_zero_iff
  条件: [DenselyOrdered α]
  结论: Ioo a b = 0 ↔ ¬a < b
  证明: by
  rw [Ioo]; rw [Finset.val_eq_zero]; rw [Finset.Ioo_eq_empty_iff]

alias ⟨_, Icc_eq_zero⟩ := Icc_eq_zero_iff

alias ⟨_, Ico_eq_zero⟩ := Ico_eq_zero_iff

alias ⟨_, Ioc_eq_zero⟩ := Ioc_eq_zero_iff

@[simp]

Depends on / 依赖: Finset, Finset.Ioo_eq_empty_iff, Finset.val_eq_zero, Ioo_eq_empty_iff, val_eq_zero
-/
theorem Ioo_eq_zero_iff [DenselyOrdered α] : Ioo a b = 0 ↔ ¬a < b := by
  rw [Ioo]; rw [Finset.val_eq_zero]; rw [Finset.Ioo_eq_empty_iff]

alias ⟨_, Icc_eq_zero⟩ := Icc_eq_zero_iff

alias ⟨_, Ico_eq_zero⟩ := Ico_eq_zero_iff

alias ⟨_, Ioc_eq_zero⟩ := Ioc_eq_zero_iff

@[simp]
/--
theorem `Ioo_eq_zero` / 定理 `Ioo_eq_zero`

English:
theorem Ioo_eq_zero
  given: (h : ¬a < b)
  statement: Ioo a b = 0
  proof: eq_zero_iff_forall_notMem.2 fun _x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]

中文:
定理 Ioo_eq_zero
  条件: (h : ¬a < b)
  结论: Ioo a b = 0
  证明: eq_zero_iff_forall_notMem.2 fun _x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]

Depends on / 依赖: eq_zero_iff_forall_notMem, mem_Ioo
-/
theorem Ioo_eq_zero (h : ¬a < b) : Ioo a b = 0 :=
  eq_zero_iff_forall_notMem.2 fun _x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]
/--
theorem `Icc_eq_zero_of_lt` / 定理 `Icc_eq_zero_of_lt`

English:
theorem Icc_eq_zero_of_lt
  given: (h : b < a)
  statement: Icc a b = 0
  proof: Icc_eq_zero h.not_ge

@[simp]

中文:
定理 Icc_eq_zero_of_lt
  条件: (h : b < a)
  结论: Icc a b = 0
  证明: Icc_eq_zero h.not_ge

@[simp]

Depends on / 依赖: Icc_eq_zero, h.not_ge, not_ge
-/
theorem Icc_eq_zero_of_lt (h : b < a) : Icc a b = 0 :=
  Icc_eq_zero h.not_ge

@[simp]
/--
theorem `Ico_eq_zero_of_le` / 定理 `Ico_eq_zero_of_le`

English:
theorem Ico_eq_zero_of_le
  given: (h : b <= a)
  statement: Ico a b = 0
  proof: Ico_eq_zero h.not_gt

@[simp]

中文:
定理 Ico_eq_zero_of_le
  条件: (h : b <= a)
  结论: Ico a b = 0
  证明: Ico_eq_zero h.not_gt

@[simp]

Depends on / 依赖: Ico_eq_zero, h.not_gt, not_gt
-/
theorem Ico_eq_zero_of_le (h : b <= a) : Ico a b = 0 :=
  Ico_eq_zero h.not_gt

@[simp]
/--
theorem `Ioc_eq_zero_of_le` / 定理 `Ioc_eq_zero_of_le`

English:
theorem Ioc_eq_zero_of_le
  given: (h : b <= a)
  statement: Ioc a b = 0
  proof: Ioc_eq_zero h.not_gt

@[simp]

中文:
定理 Ioc_eq_zero_of_le
  条件: (h : b <= a)
  结论: Ioc a b = 0
  证明: Ioc_eq_zero h.not_gt

@[simp]

Depends on / 依赖: Ioc_eq_zero, h.not_gt, not_gt
-/
theorem Ioc_eq_zero_of_le (h : b <= a) : Ioc a b = 0 :=
  Ioc_eq_zero h.not_gt

@[simp]
/--
theorem `Ioo_eq_zero_of_le` / 定理 `Ioo_eq_zero_of_le`

English:
theorem Ioo_eq_zero_of_le
  given: (h : b <= a)
  statement: Ioo a b = 0
  proof: Ioo_eq_zero h.not_gt

中文:
定理 Ioo_eq_zero_of_le
  条件: (h : b <= a)
  结论: Ioo a b = 0
  证明: Ioo_eq_zero h.not_gt

Depends on / 依赖: Ioo_eq_zero, h.not_gt, not_gt
-/
theorem Ioo_eq_zero_of_le (h : b <= a) : Ioo a b = 0 :=
  Ioo_eq_zero h.not_gt

variable (a)

/--
theorem `Ico_self` / 定理 `Ico_self`

English:
theorem Ico_self
  statement: Ico a a = 0
  proof: by rw [Ico, Finset.Ico_self, Finset.empty_val]

中文:
定理 Ico_self
  结论: Ico a a = 0
  证明: by rw [Ico, Finset.Ico_self, Finset.empty_val]

Depends on / 依赖: Finset, Finset.Ico_self, Finset.empty_val, Ico_self, empty_val
-/
theorem Ico_self : Ico a a = 0 := by rw [Ico, Finset.Ico_self, Finset.empty_val]

/--
theorem `Ioc_self` / 定理 `Ioc_self`

English:
theorem Ioc_self
  statement: Ioc a a = 0
  proof: by rw [Ioc, Finset.Ioc_self, Finset.empty_val]

中文:
定理 Ioc_self
  结论: Ioc a a = 0
  证明: by rw [Ioc, Finset.Ioc_self, Finset.empty_val]

Depends on / 依赖: Finset, Finset.Ioc_self, Finset.empty_val, Ioc_self, empty_val
-/
theorem Ioc_self : Ioc a a = 0 := by rw [Ioc, Finset.Ioc_self, Finset.empty_val]

/--
theorem `Ioo_self` / 定理 `Ioo_self`

English:
theorem Ioo_self
  statement: Ioo a a = 0
  proof: by rw [Ioo, Finset.Ioo_self, Finset.empty_val]

中文:
定理 Ioo_self
  结论: Ioo a a = 0
  证明: by rw [Ioo, Finset.Ioo_self, Finset.empty_val]

Depends on / 依赖: Finset, Finset.Ioo_self, Finset.empty_val, Function, Function.RightInverse.surjective, GradedRing, GradedRing.projZeroRingHom, Ioo_self, RightInverse, _apply_coe, empty_val, projZeroRingHom, surjective
-/
theorem Ioo_self : Ioo a a = 0 := by rw [Ioo, Finset.Ioo_self, Finset.empty_val]

variable {a}

/--
theorem `left_mem_Icc` / 定理 `left_mem_Icc`

English:
theorem left_mem_Icc
  statement: a in Icc a b ↔ a <= b
  proof: Finset.left_mem_Icc

中文:
定理 left_mem_Icc
  结论: a in Icc a b ↔ a <= b
  证明: Finset.left_mem_Icc

Depends on / 依赖: Finset, Finset.left_mem_Icc, left_mem_Icc
-/
theorem left_mem_Icc : a in Icc a b ↔ a <= b :=
  Finset.left_mem_Icc

/--
theorem `left_mem_Ico` / 定理 `left_mem_Ico`

English:
theorem left_mem_Ico
  statement: a in Ico a b ↔ a < b
  proof: Finset.left_mem_Ico

中文:
定理 left_mem_Ico
  结论: a in Ico a b ↔ a < b
  证明: Finset.left_mem_Ico

Depends on / 依赖: Finset, Finset.left_mem_Ico, left_mem_Ico
-/
theorem left_mem_Ico : a in Ico a b ↔ a < b :=
  Finset.left_mem_Ico

/--
theorem `right_mem_Icc` / 定理 `right_mem_Icc`

English:
theorem right_mem_Icc
  statement: b in Icc a b ↔ a <= b
  proof: Finset.right_mem_Icc

中文:
定理 right_mem_Icc
  结论: b in Icc a b ↔ a <= b
  证明: Finset.right_mem_Icc

Depends on / 依赖: Finset, Finset.right_mem_Icc, right_mem_Icc
-/
theorem right_mem_Icc : b in Icc a b ↔ a <= b :=
  Finset.right_mem_Icc

/--
theorem `right_mem_Ioc` / 定理 `right_mem_Ioc`

English:
theorem right_mem_Ioc
  statement: b in Ioc a b ↔ a < b
  proof: Finset.right_mem_Ioc

中文:
定理 right_mem_Ioc
  结论: b in Ioc a b ↔ a < b
  证明: Finset.right_mem_Ioc

Depends on / 依赖: Finset, Finset.right_mem_Ioc, right_mem_Ioc
-/
theorem right_mem_Ioc : b in Ioc a b ↔ a < b :=
  Finset.right_mem_Ioc

/--
theorem `left_notMem_Ioc` / 定理 `left_notMem_Ioc`

English:
theorem left_notMem_Ioc
  statement: a ∉ Ioc a b
  proof: Finset.left_notMem_Ioc

中文:
定理 left_notMem_Ioc
  结论: a ∉ Ioc a b
  证明: Finset.left_notMem_Ioc

Depends on / 依赖: Finset, Finset.left_notMem_Ioc, left_notMem_Ioc
-/
theorem left_notMem_Ioc : a ∉ Ioc a b :=
  Finset.left_notMem_Ioc

/--
theorem `left_notMem_Ioo` / 定理 `left_notMem_Ioo`

English:
theorem left_notMem_Ioo
  statement: a ∉ Ioo a b
  proof: Finset.left_notMem_Ioo

中文:
定理 left_notMem_Ioo
  结论: a ∉ Ioo a b
  证明: Finset.left_notMem_Ioo

Depends on / 依赖: Finset, Finset.left_notMem_Ioo, left_notMem_Ioo
-/
theorem left_notMem_Ioo : a ∉ Ioo a b :=
  Finset.left_notMem_Ioo

/--
theorem `right_notMem_Ico` / 定理 `right_notMem_Ico`

English:
theorem right_notMem_Ico
  statement: b ∉ Ico a b
  proof: Finset.right_notMem_Ico

中文:
定理 right_notMem_Ico
  结论: b ∉ Ico a b
  证明: Finset.right_notMem_Ico

Depends on / 依赖: Finset, Finset.right_notMem_Ico, right_notMem_Ico
-/
theorem right_notMem_Ico : b ∉ Ico a b :=
  Finset.right_notMem_Ico

/--
theorem `right_notMem_Ioo` / 定理 `right_notMem_Ioo`

English:
theorem right_notMem_Ioo
  statement: b ∉ Ioo a b
  proof: Finset.right_notMem_Ioo

中文:
定理 right_notMem_Ioo
  结论: b ∉ Ioo a b
  证明: Finset.right_notMem_Ioo

Depends on / 依赖: Finset, Finset.right_notMem_Ioo, right_notMem_Ioo
-/
theorem right_notMem_Ioo : b ∉ Ioo a b :=
  Finset.right_notMem_Ioo

/--
theorem `Ico_filter_lt_of_le_left` / 定理 `Ico_filter_lt_of_le_left`

English:
theorem Ico_filter_lt_of_le_left
  given: [DecidablePred (· < c)] (hca : c <= a)
  proof: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt_of_le_left hca]
  rfl

中文:
定理 Ico_filter_lt_of_le_left
  条件: [DecidablePred (· < c)] (hca : c <= a)
  证明: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt_of_le_left hca]
  rfl

Depends on / 依赖: Finset, Finset.Ico_filter_lt_of_le_left, Finset.filter_val, Ico_filter_lt_of_le_left, filter_val
-/
theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c <= a) :
    ((Ico a b).filter fun x => x < c) = ∅ := by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt_of_le_left hca]
  rfl

/--
theorem `Ico_filter_lt_of_right_le` / 定理 `Ico_filter_lt_of_right_le`

English:
theorem Ico_filter_lt_of_right_le
  given: [DecidablePred (· < c)] (hbc : b <= c)
  proof: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt_of_right_le hbc]

中文:
定理 Ico_filter_lt_of_right_le
  条件: [DecidablePred (· < c)] (hbc : b <= c)
  证明: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt_of_right_le hbc]

Depends on / 依赖: Finset, Finset.Ico_filter_lt_of_right_le, Finset.filter_val, Ico_filter_lt_of_right_le, filter_val
-/
theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b <= c) :
    ((Ico a b).filter fun x => x < c) = Ico a b := by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt_of_right_le hbc]

/--
theorem `Ico_filter_lt_of_le_right` / 定理 `Ico_filter_lt_of_le_right`

English:
theorem Ico_filter_lt_of_le_right
  given: [DecidablePred (· < c)] (hcb : c <= b)
  proof: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt_of_le_right hcb]
  rfl

中文:
定理 Ico_filter_lt_of_le_right
  条件: [DecidablePred (· < c)] (hcb : c <= b)
  证明: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt_of_le_right hcb]
  rfl

Depends on / 依赖: Finset, Finset.Ico_filter_lt_of_le_right, Finset.filter_val, Ico_filter_lt_of_le_right, filter_val
-/
theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c <= b) :
    ((Ico a b).filter fun x => x < c) = Ico a c := by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt_of_le_right hcb]
  rfl

/--
theorem `Ico_filter_le_of_le_left` / 定理 `Ico_filter_le_of_le_left`

English:
theorem Ico_filter_le_of_le_left
  given: [DecidablePred (c <= ·)] (hca : c <= a)
  proof: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_of_le_left hca]

中文:
定理 Ico_filter_le_of_le_left
  条件: [DecidablePred (c <= ·)] (hca : c <= a)
  证明: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_of_le_left hca]

Depends on / 依赖: Finset, Finset.Ico_filter_le_of_le_left, Finset.filter_val, Ico_filter_le_of_le_left, filter_val
-/
theorem Ico_filter_le_of_le_left [DecidablePred (c <= ·)] (hca : c <= a) :
    ((Ico a b).filter fun x => c <= x) = Ico a b := by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_of_le_left hca]

/--
theorem `Ico_filter_le_of_right_le` / 定理 `Ico_filter_le_of_right_le`

English:
theorem Ico_filter_le_of_right_le
  given: [DecidablePred (b <= ·)]
  proof: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_of_right_le]
  rfl

中文:
定理 Ico_filter_le_of_right_le
  条件: [DecidablePred (b <= ·)]
  证明: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_of_right_le]
  rfl

Depends on / 依赖: Finset, Finset.Ico_filter_le_of_right_le, Finset.filter_val, Ico_filter_le_of_right_le, filter_val
-/
theorem Ico_filter_le_of_right_le [DecidablePred (b <= ·)] :
    ((Ico a b).filter fun x => b <= x) = ∅ := by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_of_right_le]
  rfl

/--
theorem `Ico_filter_le_of_left_le` / 定理 `Ico_filter_le_of_left_le`

English:
theorem Ico_filter_le_of_left_le
  given: [DecidablePred (c <= ·)] (hac : a <= c)
  proof: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_of_left_le hac]
  rfl

中文:
定理 Ico_filter_le_of_left_le
  条件: [DecidablePred (c <= ·)] (hac : a <= c)
  证明: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_of_left_le hac]
  rfl

Depends on / 依赖: Finset, Finset.Ico_filter_le_of_left_le, Finset.filter_val, Ico_filter_le_of_left_le, filter_val
-/
theorem Ico_filter_le_of_left_le [DecidablePred (c <= ·)] (hac : a <= c) :
    ((Ico a b).filter fun x => c <= x) = Ico c b := by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_of_left_le hac]
  rfl

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b : α}

@[simp]
/--
theorem `Icc_self` / 定理 `Icc_self`

English:
theorem Icc_self
  given: (a : α)
  statement: Icc a a = {a}
  proof: by rw [Icc, Finset.Icc_self, Finset.singleton_val]

中文:
定理 Icc_self
  条件: (a : α)
  结论: Icc a a = {a}
  证明: by rw [Icc, Finset.Icc_self, Finset.singleton_val]

Depends on / 依赖: Finset, Finset.Icc_self, Finset.singleton_val, Icc_self, singleton_val
-/
theorem Icc_self (a : α) : Icc a a = {a} := by rw [Icc, Finset.Icc_self, Finset.singleton_val]

/--
theorem `Ico_cons_right` / 定理 `Ico_cons_right`

English:
theorem Ico_cons_right
  given: (h : a <= b)
  statement: b ::ₘ Ico a b = Icc a b
  proof: by
  classical
    rw [Ico]; rw [← Finset.insert_val_of_notMem right_notMem_Ico]; rw [Finset.Ico_insert_right h]
    rfl

中文:
定理 Ico_cons_right
  条件: (h : a <= b)
  结论: b ::ₘ Ico a b = Icc a b
  证明: by
  classical
    rw [Ico]; rw [← Finset.insert_val_of_notMem right_notMem_Ico]; rw [Finset.Ico_insert_right h]
    rfl

Depends on / 依赖: Finset, Finset.Ico_insert_right, Finset.insert_val_of_notMem, Ico_insert_right, classical, insert_val_of_notMem, right_notMem_Ico
-/
theorem Ico_cons_right (h : a <= b) : b ::ₘ Ico a b = Icc a b := by
  classical
    rw [Ico]; rw [← Finset.insert_val_of_notMem right_notMem_Ico]; rw [Finset.Ico_insert_right h]
    rfl

/--
theorem `Ioo_cons_left` / 定理 `Ioo_cons_left`

English:
theorem Ioo_cons_left
  given: (h : a < b)
  statement: a ::ₘ Ioo a b = Ico a b
  proof: by
  classical
    rw [Ioo]; rw [← Finset.insert_val_of_notMem left_notMem_Ioo]; rw [Finset.Ioo_insert_left h]
    rfl

中文:
定理 Ioo_cons_left
  条件: (h : a < b)
  结论: a ::ₘ Ioo a b = Ico a b
  证明: by
  classical
    rw [Ioo]; rw [← Finset.insert_val_of_notMem left_notMem_Ioo]; rw [Finset.Ioo_insert_left h]
    rfl

Depends on / 依赖: Finset, Finset.Ioo_insert_left, Finset.insert_val_of_notMem, Ioo_insert_left, classical, insert_val_of_notMem, left_notMem_Ioo
-/
theorem Ioo_cons_left (h : a < b) : a ::ₘ Ioo a b = Ico a b := by
  classical
    rw [Ioo]; rw [← Finset.insert_val_of_notMem left_notMem_Ioo]; rw [Finset.Ioo_insert_left h]
    rfl

/--
theorem `Ico_disjoint_Ico` / 定理 `Ico_disjoint_Ico`

English:
theorem Ico_disjoint_Ico
  given: {a b c d : α} (h : b <= c)
  statement: Disjoint (Ico a b) (Ico c d)
  proof: disjoint_left.mpr fun hab hbc => by
    rw [mem_Ico] at hab hbc
    exact hab.2.not_ge (h.trans hbc.1)

@[simp]

中文:
定理 Ico_disjoint_Ico
  条件: {a b c d : α} (h : b <= c)
  结论: Disjoint (Ico a b) (Ico c d)
  证明: disjoint_left.mpr fun hab hbc => by
    rw [mem_Ico] at hab hbc
    exact hab.2.not_ge (h.trans hbc.1)

@[simp]

Depends on / 依赖: disjoint_left, disjoint_left.mpr, h.trans, mem_Ico, not_ge
-/
theorem Ico_disjoint_Ico {a b c d : α} (h : b <= c) : Disjoint (Ico a b) (Ico c d) :=
  disjoint_left.mpr fun hab hbc => by
    rw [mem_Ico] at hab hbc
    exact hab.2.not_ge (h.trans hbc.1)

@[simp]
/--
theorem `Ico_inter_Ico_of_le` / 定理 `Ico_inter_Ico_of_le`

English:
theorem Ico_inter_Ico_of_le
  given: [DecidableEq α] {a b c d : α} (h : b <= c)
  statement: Ico a b inter Ico c d = 0
  proof: Multiset.inter_eq_zero_iff_disjoint.2 Ico_disjoint_Ico h

中文:
定理 Ico_inter_Ico_of_le
  条件: [DecidableEq α] {a b c d : α} (h : b <= c)
  结论: Ico a b inter Ico c d = 0
  证明: Multiset.inter_eq_zero_iff_disjoint.2 Ico_disjoint_Ico h

Depends on / 依赖: Ico_disjoint_Ico, Multiset, Multiset.inter_eq_zero_iff_disjoint, inter_eq_zero_iff_disjoint
-/
theorem Ico_inter_Ico_of_le [DecidableEq α] {a b c d : α} (h : b <= c) : Ico a b inter Ico c d = 0 :=
Multiset.inter_eq_zero_iff_disjoint.2 Ico_disjoint_Ico h

/--
theorem `Ico_filter_le_left` / 定理 `Ico_filter_le_left`

English:
theorem Ico_filter_le_left
  given: {a b : α} [DecidablePred (· <= a)] (hab : a < b)
  proof: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_left hab]
  rfl

中文:
定理 Ico_filter_le_left
  条件: {a b : α} [DecidablePred (· <= a)] (hab : a < b)
  证明: by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_left hab]
  rfl

Depends on / 依赖: Finset, Finset.Ico_filter_le_left, Finset.filter_val, Ico_filter_le_left, filter_val
-/
theorem Ico_filter_le_left {a b : α} [DecidablePred (· <= a)] (hab : a < b) :
    ((Ico a b).filter fun x => x <= a) = {a} := by
  rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le_left hab]
  rfl

/--
theorem `card_Ico_eq_card_Icc_sub_one` / 定理 `card_Ico_eq_card_Icc_sub_one`

English:
theorem card_Ico_eq_card_Icc_sub_one
  given: (a b : α)
  statement: card (Ico a b) = card (Icc a b) - 1
  proof: Finset.card_Ico_eq_card_Icc_sub_one _ _

中文:
定理 card_Ico_eq_card_Icc_sub_one
  条件: (a b : α)
  结论: card (Ico a b) = card (Icc a b) - 1
  证明: Finset.card_Ico_eq_card_Icc_sub_one _ _

Depends on / 依赖: Finset, Finset.card_Ico_eq_card_Icc_sub_one, card_Ico_eq_card_Icc_sub_one
-/
theorem card_Ico_eq_card_Icc_sub_one (a b : α) : card (Ico a b) = card (Icc a b) - 1 :=
  Finset.card_Ico_eq_card_Icc_sub_one _ _

/--
theorem `card_Ioc_eq_card_Icc_sub_one` / 定理 `card_Ioc_eq_card_Icc_sub_one`

English:
theorem card_Ioc_eq_card_Icc_sub_one
  given: (a b : α)
  statement: card (Ioc a b) = card (Icc a b) - 1
  proof: Finset.card_Ioc_eq_card_Icc_sub_one _ _

中文:
定理 card_Ioc_eq_card_Icc_sub_one
  条件: (a b : α)
  结论: card (Ioc a b) = card (Icc a b) - 1
  证明: Finset.card_Ioc_eq_card_Icc_sub_one _ _

Depends on / 依赖: Finset, Finset.card_Ioc_eq_card_Icc_sub_one, card_Ioc_eq_card_Icc_sub_one
-/
theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : card (Ioc a b) = card (Icc a b) - 1 :=
  Finset.card_Ioc_eq_card_Icc_sub_one _ _

/--
theorem `card_Ioo_eq_card_Ico_sub_one` / 定理 `card_Ioo_eq_card_Ico_sub_one`

English:
theorem card_Ioo_eq_card_Ico_sub_one
  given: (a b : α)
  statement: card (Ioo a b) = card (Ico a b) - 1
  proof: Finset.card_Ioo_eq_card_Ico_sub_one _ _

中文:
定理 card_Ioo_eq_card_Ico_sub_one
  条件: (a b : α)
  结论: card (Ioo a b) = card (Ico a b) - 1
  证明: Finset.card_Ioo_eq_card_Ico_sub_one _ _

Depends on / 依赖: Finset, Finset.card_Ioo_eq_card_Ico_sub_one, card_Ioo_eq_card_Ico_sub_one
-/
theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : card (Ioo a b) = card (Ico a b) - 1 :=
  Finset.card_Ioo_eq_card_Ico_sub_one _ _

/--
theorem `card_Ioo_eq_card_Icc_sub_two` / 定理 `card_Ioo_eq_card_Icc_sub_two`

English:
theorem card_Ioo_eq_card_Icc_sub_two
  given: (a b : α)
  statement: card (Ioo a b) = card (Icc a b) - 2
  proof: Finset.card_Ioo_eq_card_Icc_sub_two _ _

中文:
定理 card_Ioo_eq_card_Icc_sub_two
  条件: (a b : α)
  结论: card (Ioo a b) = card (Icc a b) - 2
  证明: Finset.card_Ioo_eq_card_Icc_sub_two _ _

Depends on / 依赖: Finset, Finset.card_Ioo_eq_card_Icc_sub_two, card_Ioo_eq_card_Icc_sub_two
-/
theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : card (Ioo a b) = card (Icc a b) - 2 :=
  Finset.card_Ioo_eq_card_Icc_sub_two _ _

end PartialOrder

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a b c d : α}

/--
theorem `Ico_subset_Ico_iff` / 定理 `Ico_subset_Ico_iff`

English:
theorem Ico_subset_Ico_iff
  given: {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁)
  proof: Finset.Ico_subset_Ico_iff h

中文:
定理 Ico_subset_Ico_iff
  条件: {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁)
  证明: Finset.Ico_subset_Ico_iff h

Depends on / 依赖: Finset, Finset.Ico_subset_Ico_iff, Ico_subset_Ico_iff
-/
theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂ :=
  Finset.Ico_subset_Ico_iff h

/--
theorem `Ico_add_Ico_eq_Ico` / 定理 `Ico_add_Ico_eq_Ico`

English:
theorem Ico_add_Ico_eq_Ico
  given: {a b c : α} (hab : a <= b) (hbc : b <= c)
  proof: by
  rw [add_eq_union_iff_disjoint.2 (Ico_disjoint_Ico le_rfl)]; rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.union_val]; rw [Finset.Ico_union_Ico_eq_Ico hab hbc]

中文:
定理 Ico_add_Ico_eq_Ico
  条件: {a b c : α} (hab : a <= b) (hbc : b <= c)
  证明: by
  rw [add_eq_union_iff_disjoint.2 (Ico_disjoint_Ico le_rfl)]; rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.union_val]; rw [Finset.Ico_union_Ico_eq_Ico hab hbc]

Depends on / 依赖: Finset, Finset.Ico_union_Ico_eq_Ico, Finset.union_val, Ico_disjoint_Ico, Ico_union_Ico_eq_Ico, add_eq_union_iff_disjoint, le_rfl, union_val
-/
theorem Ico_add_Ico_eq_Ico {a b c : α} (hab : a <= b) (hbc : b <= c) :
    Ico a b + Ico b c = Ico a c := by
  rw [add_eq_union_iff_disjoint.2 (Ico_disjoint_Ico le_rfl)]; rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.union_val]; rw [Finset.Ico_union_Ico_eq_Ico hab hbc]

/--
theorem `Ico_inter_Ico` / 定理 `Ico_inter_Ico`

English:
theorem Ico_inter_Ico
  statement: Ico a b inter Ico c d = Ico (max a c) (min b d)
  proof: by
  rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.inter_val]; rw [Finset.Ico_inter_Ico]

@[simp]

中文:
定理 Ico_inter_Ico
  结论: Ico a b inter Ico c d = Ico (max a c) (min b d)
  证明: by
  rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.inter_val]; rw [Finset.Ico_inter_Ico]

@[simp]

Depends on / 依赖: Finset, Finset.Ico_inter_Ico, Finset.inter_val, Ico_inter_Ico, inter_val
-/
theorem Ico_inter_Ico : Ico a b inter Ico c d = Ico (max a c) (min b d) := by
  rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.inter_val]; rw [Finset.Ico_inter_Ico]

@[simp]
/--
theorem `Ico_filter_lt` / 定理 `Ico_filter_lt`

English:
theorem Ico_filter_lt
  given: (a b c : α)
  statement: ((Ico a b).filter fun x => x < c) = Ico a (min b c)
  proof: by
  rw [Ico]; rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt]

@[simp]

中文:
定理 Ico_filter_lt
  条件: (a b c : α)
  结论: ((Ico a b).filter fun x => x < c) = Ico a (min b c)
  证明: by
  rw [Ico]; rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt]

@[simp]

Depends on / 依赖: Finset, Finset.Ico_filter_lt, Finset.filter_val, Ico_filter_lt, filter_val
-/
theorem Ico_filter_lt (a b c : α) : ((Ico a b).filter fun x => x < c) = Ico a (min b c) := by
  rw [Ico]; rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_lt]

@[simp]
/--
theorem `Ico_filter_le` / 定理 `Ico_filter_le`

English:
theorem Ico_filter_le
  given: (a b c : α)
  statement: ((Ico a b).filter fun x => c <= x) = Ico (max a c) b
  proof: by
  rw [Ico]; rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le]

@[simp]

中文:
定理 Ico_filter_le
  条件: (a b c : α)
  结论: ((Ico a b).filter fun x => c <= x) = Ico (max a c) b
  证明: by
  rw [Ico]; rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le]

@[simp]

Depends on / 依赖: Finset, Finset.Ico_filter_le, Finset.filter_val, Ico_filter_le, filter_val
-/
theorem Ico_filter_le (a b c : α) : ((Ico a b).filter fun x => c <= x) = Ico (max a c) b := by
  rw [Ico]; rw [Ico]; rw [← Finset.filter_val]; rw [Finset.Ico_filter_le]

@[simp]
/--
theorem `Ico_sub_Ico_left` / 定理 `Ico_sub_Ico_left`

English:
theorem Ico_sub_Ico_left
  given: (a b c : α)
  statement: Ico a b - Ico a c = Ico (max a c) b
  proof: by
  rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.sdiff_val]; rw [Finset.Ico_sdiff_Ico_left]

@[simp]

中文:
定理 Ico_sub_Ico_left
  条件: (a b c : α)
  结论: Ico a b - Ico a c = Ico (max a c) b
  证明: by
  rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.sdiff_val]; rw [Finset.Ico_sdiff_Ico_left]

@[simp]

Depends on / 依赖: Finset, Finset.Ico_sdiff_Ico_left, Finset.sdiff_val, Ico_sdiff_Ico_left, sdiff_val
-/
theorem Ico_sub_Ico_left (a b c : α) : Ico a b - Ico a c = Ico (max a c) b := by
  rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.sdiff_val]; rw [Finset.Ico_sdiff_Ico_left]

@[simp]
/--
theorem `Ico_sub_Ico_right` / 定理 `Ico_sub_Ico_right`

English:
theorem Ico_sub_Ico_right
  given: (a b c : α)
  statement: Ico a b - Ico c b = Ico a (min b c)
  proof: by
  rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.sdiff_val]; rw [Finset.Ico_sdiff_Ico_right]

中文:
定理 Ico_sub_Ico_right
  条件: (a b c : α)
  结论: Ico a b - Ico c b = Ico a (min b c)
  证明: by
  rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.sdiff_val]; rw [Finset.Ico_sdiff_Ico_right]

Depends on / 依赖: Finset, Finset.Ico_sdiff_Ico_right, Finset.sdiff_val, Ico_sdiff_Ico_right, sdiff_val
-/
theorem Ico_sub_Ico_right (a b c : α) : Ico a b - Ico c b = Ico a (min b c) := by
  rw [Ico]; rw [Ico]; rw [Ico]; rw [← Finset.sdiff_val]; rw [Finset.Ico_sdiff_Ico_right]

end LinearOrder
end Multiset
