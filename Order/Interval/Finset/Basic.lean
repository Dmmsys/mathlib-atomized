/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Yaël Dillies
-/
module

public import Mathlib.Order.Cover
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Preorder.Finite

/-!
# Intervals as finsets

This file provides basic results about all the `Finset.Ixx`, which are defined in
`Order.Interval.Finset.Defs`.

In addition, it shows that in a locally finite order `≤` and `<` are the transitive closures of,
respectively, `⩿` and `⋖`, which then leads to a characterization of monotone and strictly
functions whose domain is a locally finite order. In particular, this file proves:

* `le_iff_transGen_wcovBy`: `≤` is the transitive closure of `⩿`
* `lt_iff_transGen_covBy`: `<` is the transitive closure of `⋖`
* `monotone_iff_forall_wcovBy`: Characterization of monotone functions
* `strictMono_iff_forall_covBy`: Characterization of strictly monotone functions

## TODO

This file was originally only about `Finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `Data.X.Intervals` and abstract away the concrete structure.

Complete the API. See
https://github.com/leanprover-community/mathlib/pull/14448#discussion_r906109235
for some ideas.
-/

@[expose] public section

assert_not_exists MonoidWithZero Finset.sum

open Function OrderDual

open FinsetInterval

variable {ι α : Type*} {a a₁ a₂ b b₁ b₂ c x : α}

namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

@[simp]
/--
theorem `nonempty_Icc` / 定理 `nonempty_Icc`

English:
theorem nonempty_Icc
  statement: (Icc a b).Nonempty ↔ a <= b
  proof: by
  rw [← coe_nonempty]; rw [coe_Icc]; rw [Set.nonempty_Icc]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Icc_of_le⟩ := nonempty_Icc

@[simp]

中文:
定理 nonempty_Icc
  结论: (闭区间 a b).非空 ↔ a <= b
  证明: by
  rw [← coe_nonempty]; rw [coe_Icc]; rw [Set.nonempty_Icc]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Icc_of_le⟩ := nonempty_Icc

@[simp]

Depends on / 依赖: Set.nonempty_Icc, coe_Icc, coe_nonempty, nonempty_Icc
-/
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a <= b := by
  rw [← coe_nonempty]; rw [coe_Icc]; rw [Set.nonempty_Icc]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Icc_of_le⟩ := nonempty_Icc

@[simp]
/--
theorem `nonempty_Ico` / 定理 `nonempty_Ico`

English:
theorem nonempty_Ico
  statement: (Ico a b).Nonempty ↔ a < b
  proof: by
  rw [← coe_nonempty]; rw [coe_Ico]; rw [Set.nonempty_Ico]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ico_of_lt⟩ := nonempty_Ico

@[simp]

中文:
定理 nonempty_Ico
  结论: (左闭右开区间 a b).非空 ↔ a < b
  证明: by
  rw [← coe_nonempty]; rw [coe_Ico]; rw [Set.nonempty_Ico]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ico_of_lt⟩ := nonempty_Ico

@[simp]

Depends on / 依赖: Set.nonempty_Ico, coe_Ico, coe_nonempty, nonempty_Ico
-/
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty]; rw [coe_Ico]; rw [Set.nonempty_Ico]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ico_of_lt⟩ := nonempty_Ico

@[simp]
/--
theorem `nonempty_Ioc` / 定理 `nonempty_Ioc`

English:
theorem nonempty_Ioc
  statement: (Ioc a b).Nonempty ↔ a < b
  proof: by
  rw [← coe_nonempty]; rw [coe_Ioc]; rw [Set.nonempty_Ioc]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ioc_of_lt⟩ := nonempty_Ioc

中文:
定理 nonempty_Ioc
  结论: (左开右闭区间 a b).非空 ↔ a < b
  证明: by
  rw [← coe_nonempty]; rw [coe_Ioc]; rw [Set.nonempty_Ioc]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ioc_of_lt⟩ := nonempty_Ioc

Depends on / 依赖: Finite, Module, Module.Finite, Set.nonempty_Ioc, coe_Ioc, coe_nonempty, h.toRingHom.toAlgebra, nonempty_Ioc, toAlgebra, toRingHom
-/
theorem nonempty_Ioc : (Ioc a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty]; rw [coe_Ioc]; rw [Set.nonempty_Ioc]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ioc_of_lt⟩ := nonempty_Ioc

-- TODO: This is nonsense. A locally finite order is never densely ordered;
-- See `not_lt_of_denselyOrdered_of_locallyFinite`
@[simp]
/--
theorem `nonempty_Ioo` / 定理 `nonempty_Ioo`

English:
theorem nonempty_Ioo
  given: [DenselyOrdered α]
  statement: (Ioo a b).Nonempty ↔ a < b
  proof: by
  rw [← coe_nonempty]; rw [coe_Ioo]; rw [Set.nonempty_Ioo]

@[simp]

中文:
定理 nonempty_Ioo
  条件: [稠密序 α]
  结论: (开区间 a b).非空 ↔ a < b
  证明: by
  rw [← coe_nonempty]; rw [coe_Ioo]; rw [Set.nonempty_Ioo]

@[simp]

Depends on / 依赖: Set.nonempty_Ioo, coe_Ioo, coe_nonempty, nonempty_Ioo
-/
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty]; rw [coe_Ioo]; rw [Set.nonempty_Ioo]

@[simp]
/--
theorem `Icc_eq_empty_iff` / 定理 `Icc_eq_empty_iff`

English:
theorem Icc_eq_empty_iff
  statement: Icc a b = ∅ ↔ ¬a <= b
  proof: by
  rw [← coe_eq_empty]; rw [coe_Icc]; rw [Set.Icc_eq_empty_iff]

@[simp]

中文:
定理 Icc_eq_empty_iff
  结论: 闭区间 a b = ∅ ↔ ¬a <= b
  证明: by
  rw [← coe_eq_empty]; rw [coe_Icc]; rw [Set.Icc_eq_empty_iff]

@[simp]

Depends on / 依赖: Icc_eq_empty_iff, Set.Icc_eq_empty_iff, coe_Icc, coe_eq_empty
-/
theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a <= b := by
  rw [← coe_eq_empty]; rw [coe_Icc]; rw [Set.Icc_eq_empty_iff]

@[simp]
/--
theorem `Ico_eq_empty_iff` / 定理 `Ico_eq_empty_iff`

English:
theorem Ico_eq_empty_iff
  statement: Ico a b = ∅ ↔ ¬a < b
  proof: by
  rw [← coe_eq_empty]; rw [coe_Ico]; rw [Set.Ico_eq_empty_iff]

@[simp]

中文:
定理 Ico_eq_empty_iff
  结论: 左闭右开区间 a b = ∅ ↔ ¬a < b
  证明: by
  rw [← coe_eq_empty]; rw [coe_Ico]; rw [Set.Ico_eq_empty_iff]

@[simp]

Depends on / 依赖: Ico_eq_empty_iff, Set.Ico_eq_empty_iff, coe_Ico, coe_eq_empty
-/
theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty]; rw [coe_Ico]; rw [Set.Ico_eq_empty_iff]

@[simp]
/--
theorem `Ioc_eq_empty_iff` / 定理 `Ioc_eq_empty_iff`

English:
theorem Ioc_eq_empty_iff
  statement: Ioc a b = ∅ ↔ ¬a < b
  proof: by
  rw [← coe_eq_empty]; rw [coe_Ioc]; rw [Set.Ioc_eq_empty_iff]

中文:
定理 Ioc_eq_empty_iff
  结论: 左开右闭区间 a b = ∅ ↔ ¬a < b
  证明: by
  rw [← coe_eq_empty]; rw [coe_Ioc]; rw [Set.Ioc_eq_empty_iff]

Depends on / 依赖: Ioc_eq_empty_iff, Set.Ioc_eq_empty_iff, coe_Ioc, coe_eq_empty
-/
theorem Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty]; rw [coe_Ioc]; rw [Set.Ioc_eq_empty_iff]

-- TODO: This is nonsense. A locally finite order is never densely ordered
-- See `not_lt_of_denselyOrdered_of_locallyFinite`
@[simp]
/--
theorem `Ioo_eq_empty_iff` / 定理 `Ioo_eq_empty_iff`

English:
theorem Ioo_eq_empty_iff
  given: [DenselyOrdered α]
  statement: Ioo a b = ∅ ↔ ¬a < b
  proof: by
  rw [← coe_eq_empty]; rw [coe_Ioo]; rw [Set.Ioo_eq_empty_iff]

alias ⟨_, Icc_eq_empty⟩ := Icc_eq_empty_iff

alias ⟨_, Ico_eq_empty⟩ := Ico_eq_empty_iff

alias ⟨_, Ioc_eq_empty⟩ := Ioc_eq_empty_iff

@[simp]

中文:
定理 Ioo_eq_empty_iff
  条件: [稠密序 α]
  结论: 开区间 a b = ∅ ↔ ¬a < b
  证明: by
  rw [← coe_eq_empty]; rw [coe_Ioo]; rw [Set.Ioo_eq_empty_iff]

alias ⟨_, Icc_eq_empty⟩ := Icc_eq_empty_iff

alias ⟨_, Ico_eq_empty⟩ := Ico_eq_empty_iff

alias ⟨_, Ioc_eq_empty⟩ := Ioc_eq_empty_iff

@[simp]

Depends on / 依赖: Ioo_eq_empty_iff, Set.Ioo_eq_empty_iff, coe_Ioo, coe_eq_empty
-/
theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty]; rw [coe_Ioo]; rw [Set.Ioo_eq_empty_iff]

alias ⟨_, Icc_eq_empty⟩ := Icc_eq_empty_iff

alias ⟨_, Ico_eq_empty⟩ := Ico_eq_empty_iff

alias ⟨_, Ioc_eq_empty⟩ := Ioc_eq_empty_iff

@[simp]
/--
theorem `Ioo_eq_empty` / 定理 `Ioo_eq_empty`

English:
theorem Ioo_eq_empty
  given: (h : ¬a < b)
  statement: Ioo a b = ∅
  proof: eq_empty_iff_forall_notMem.2 fun _ hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]

中文:
定理 Ioo_eq_empty
  条件: (h : ¬a < b)
  结论: 开区间 a b = ∅
  证明: eq_empty_iff_forall_notMem.2 fun _ hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]

Depends on / 依赖: eq_empty_iff_forall_notMem, mem_Ioo
-/
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]
/--
theorem `Icc_eq_empty_of_lt` / 定理 `Icc_eq_empty_of_lt`

English:
theorem Icc_eq_empty_of_lt
  given: (h : b < a)
  statement: Icc a b = ∅
  proof: Icc_eq_empty h.not_ge

@[simp]

中文:
定理 Icc_eq_empty_of_lt
  条件: (h : b < a)
  结论: 闭区间 a b = ∅
  证明: Icc_eq_empty h.not_ge

@[simp]

Depends on / 依赖: Icc_eq_empty, h.not_ge, not_ge
-/
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_ge

@[simp]
/--
theorem `Ico_eq_empty_of_le` / 定理 `Ico_eq_empty_of_le`

English:
theorem Ico_eq_empty_of_le
  given: (h : b <= a)
  statement: Ico a b = ∅
  proof: Ico_eq_empty h.not_gt

@[simp]

中文:
定理 Ico_eq_empty_of_le
  条件: (h : b <= a)
  结论: 左闭右开区间 a b = ∅
  证明: Ico_eq_empty h.not_gt

@[simp]

Depends on / 依赖: Ico_eq_empty, h.not_gt, not_gt
-/
theorem Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_gt

@[simp]
/--
theorem `Ioc_eq_empty_of_le` / 定理 `Ioc_eq_empty_of_le`

English:
theorem Ioc_eq_empty_of_le
  given: (h : b <= a)
  statement: Ioc a b = ∅
  proof: Ioc_eq_empty h.not_gt

@[simp]

中文:
定理 Ioc_eq_empty_of_le
  条件: (h : b <= a)
  结论: 左开右闭区间 a b = ∅
  证明: Ioc_eq_empty h.not_gt

@[simp]

Depends on / 依赖: Ioc_eq_empty, h.not_gt, not_gt
-/
theorem Ioc_eq_empty_of_le (h : b <= a) : Ioc a b = ∅ :=
  Ioc_eq_empty h.not_gt

@[simp]
/--
theorem `Ioo_eq_empty_of_le` / 定理 `Ioo_eq_empty_of_le`

English:
theorem Ioo_eq_empty_of_le
  given: (h : b <= a)
  statement: Ioo a b = ∅
  proof: Ioo_eq_empty h.not_gt

中文:
定理 Ioo_eq_empty_of_le
  条件: (h : b <= a)
  结论: 开区间 a b = ∅
  证明: Ioo_eq_empty h.not_gt

Depends on / 依赖: Ioo_eq_empty, h.not_gt, not_gt
-/
theorem Ioo_eq_empty_of_le (h : b <= a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_gt

/--
theorem `left_mem_Icc` / 定理 `left_mem_Icc`

English:
theorem left_mem_Icc
  statement: a in Icc a b ↔ a <= b
  proof: by simp only [mem_Icc, true_and, le_rfl]

中文:
定理 left_mem_Icc
  结论: a in 闭区间 a b ↔ a <= b
  证明: by simp only [mem_Icc, true_and, le_rfl]

Depends on / 依赖: le_rfl, mem_Icc, true_and
-/
theorem left_mem_Icc : a in Icc a b ↔ a <= b := by simp only [mem_Icc, true_and, le_rfl]

/--
theorem `left_mem_Ico` / 定理 `left_mem_Ico`

English:
theorem left_mem_Ico
  statement: a in Ico a b ↔ a < b
  proof: by simp only [mem_Ico, true_and, le_refl]

中文:
定理 left_mem_Ico
  结论: a in 左闭右开区间 a b ↔ a < b
  证明: by simp only [mem_Ico, true_and, le_refl]

Depends on / 依赖: le_refl, mem_Ico, true_and
-/
theorem left_mem_Ico : a in Ico a b ↔ a < b := by simp only [mem_Ico, true_and, le_refl]

/--
theorem `right_mem_Icc` / 定理 `right_mem_Icc`

English:
theorem right_mem_Icc
  statement: b in Icc a b ↔ a <= b
  proof: by simp only [mem_Icc, and_true, le_rfl]

中文:
定理 right_mem_Icc
  结论: b in 闭区间 a b ↔ a <= b
  证明: by simp only [mem_Icc, and_true, le_rfl]

Depends on / 依赖: and_true, le_rfl, mem_Icc
-/
theorem right_mem_Icc : b in Icc a b ↔ a <= b := by simp only [mem_Icc, and_true, le_rfl]

/--
theorem `right_mem_Ioc` / 定理 `right_mem_Ioc`

English:
theorem right_mem_Ioc
  statement: b in Ioc a b ↔ a < b
  proof: by simp only [mem_Ioc, and_true, le_rfl]

中文:
定理 right_mem_Ioc
  结论: b in 左开右闭区间 a b ↔ a < b
  证明: by simp only [mem_Ioc, and_true, le_rfl]

Depends on / 依赖: and_true, le_rfl, mem_Ioc
-/
theorem right_mem_Ioc : b in Ioc a b ↔ a < b := by simp only [mem_Ioc, and_true, le_rfl]

/--
theorem `left_notMem_Ioc` / 定理 `left_notMem_Ioc`

English:
theorem left_notMem_Ioc
  statement: a ∉ Ioc a b
  proof: fun h => lt_irrefl _ (mem_Ioc.1 h).1

中文:
定理 left_notMem_Ioc
  结论: a ∉ 左开右闭区间 a b
  证明: fun h => lt_irrefl _ (mem_Ioc.1 h).1

Depends on / 依赖: lt_irrefl, mem_Ioc
-/
theorem left_notMem_Ioc : a ∉ Ioc a b := fun h => lt_irrefl _ (mem_Ioc.1 h).1

/--
theorem `left_notMem_Ioo` / 定理 `left_notMem_Ioo`

English:
theorem left_notMem_Ioo
  statement: a ∉ Ioo a b
  proof: fun h => lt_irrefl _ (mem_Ioo.1 h).1

中文:
定理 left_notMem_Ioo
  结论: a ∉ 开区间 a b
  证明: fun h => lt_irrefl _ (mem_Ioo.1 h).1

Depends on / 依赖: lt_irrefl, mem_Ioo
-/
theorem left_notMem_Ioo : a ∉ Ioo a b := fun h => lt_irrefl _ (mem_Ioo.1 h).1

/--
theorem `right_notMem_Ico` / 定理 `right_notMem_Ico`

English:
theorem right_notMem_Ico
  statement: b ∉ Ico a b
  proof: fun h => lt_irrefl _ (mem_Ico.1 h).2

中文:
定理 right_notMem_Ico
  结论: b ∉ 左闭右开区间 a b
  证明: fun h => lt_irrefl _ (mem_Ico.1 h).2

Depends on / 依赖: lt_irrefl, mem_Ico
-/
theorem right_notMem_Ico : b ∉ Ico a b := fun h => lt_irrefl _ (mem_Ico.1 h).2

/--
theorem `right_notMem_Ioo` / 定理 `right_notMem_Ioo`

English:
theorem right_notMem_Ioo
  statement: b ∉ Ioo a b
  proof: fun h => lt_irrefl _ (mem_Ioo.1 h).2

@[gcongr]

中文:
定理 right_notMem_Ioo
  结论: b ∉ 开区间 a b
  证明: fun h => lt_irrefl _ (mem_Ioo.1 h).2

@[gcongr]

Depends on / 依赖: lt_irrefl, mem_Ioo
-/
theorem right_notMem_Ioo : b ∉ Ioo a b := fun h => lt_irrefl _ (mem_Ioo.1 h).2

@[gcongr]
/--
theorem `Icc_subset_Icc` / 定理 `Icc_subset_Icc`

English:
theorem Icc_subset_Icc
  given: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  statement: Icc a₁ b₁ subseteq Icc a₂ b₂
  proof: by
  simpa [← coe_subset] using Set.Icc_subset_Icc ha hb

@[gcongr]

中文:
定理 Icc_subset_Icc
  条件: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  结论: 闭区间 a₁ b₁ subseteq 闭区间 a₂ b₂
  证明: by
  simpa [← coe_subset] using Set.Icc_subset_Icc ha hb

@[gcongr]

Depends on / 依赖: Icc_subset_Icc, Set.Icc_subset_Icc, coe_subset
-/
theorem Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc a₁ b₁ subseteq Icc a₂ b₂ := by
  simpa [← coe_subset] using Set.Icc_subset_Icc ha hb

@[gcongr]
/--
theorem `Ico_subset_Ico` / 定理 `Ico_subset_Ico`

English:
theorem Ico_subset_Ico
  given: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  statement: Ico a₁ b₁ subseteq Ico a₂ b₂
  proof: by
  simpa [← coe_subset] using Set.Ico_subset_Ico ha hb

@[gcongr]

中文:
定理 Ico_subset_Ico
  条件: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  结论: 左闭右开区间 a₁ b₁ subseteq 左闭右开区间 a₂ b₂
  证明: by
  simpa [← coe_subset] using Set.Ico_subset_Ico ha hb

@[gcongr]

Depends on / 依赖: Ico_subset_Ico, Set.Ico_subset_Ico, coe_subset
-/
theorem Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ico a₁ b₁ subseteq Ico a₂ b₂ := by
  simpa [← coe_subset] using Set.Ico_subset_Ico ha hb

@[gcongr]
/--
theorem `Ioc_subset_Ioc` / 定理 `Ioc_subset_Ioc`

English:
theorem Ioc_subset_Ioc
  given: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  statement: Ioc a₁ b₁ subseteq Ioc a₂ b₂
  proof: by
  simpa [← coe_subset] using Set.Ioc_subset_Ioc ha hb

@[gcongr]

中文:
定理 Ioc_subset_Ioc
  条件: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  结论: 左开右闭区间 a₁ b₁ subseteq 左开右闭区间 a₂ b₂
  证明: by
  simpa [← coe_subset] using Set.Ioc_subset_Ioc ha hb

@[gcongr]

Depends on / 依赖: Ioc_subset_Ioc, Set.Ioc_subset_Ioc, coe_subset
-/
theorem Ioc_subset_Ioc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioc a₁ b₁ subseteq Ioc a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioc ha hb

@[gcongr]
/--
theorem `Ioo_subset_Ioo` / 定理 `Ioo_subset_Ioo`

English:
theorem Ioo_subset_Ioo
  given: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  statement: Ioo a₁ b₁ subseteq Ioo a₂ b₂
  proof: by
  simpa [← coe_subset] using Set.Ioo_subset_Ioo ha hb

中文:
定理 Ioo_subset_Ioo
  条件: (ha : a₂ <= a₁) (hb : b₁ <= b₂)
  结论: 开区间 a₁ b₁ subseteq 开区间 a₂ b₂
  证明: by
  simpa [← coe_subset] using Set.Ioo_subset_Ioo ha hb

Depends on / 依赖: Ioo_subset_Ioo, Set.Ioo_subset_Ioo, coe_subset
-/
theorem Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo a₁ b₁ subseteq Ioo a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioo ha hb

/--
theorem `Icc_subset_Icc_left` / 定理 `Icc_subset_Icc_left`

English:
theorem Icc_subset_Icc_left
  given: (h : a₁ <= a₂)
  statement: Icc a₂ b subseteq Icc a₁ b
  proof: Icc_subset_Icc h le_rfl

中文:
定理 Icc_subset_Icc_left
  条件: (h : a₁ <= a₂)
  结论: 闭区间 a₂ b subseteq 闭区间 a₁ b
  证明: Icc_subset_Icc h le_rfl

Depends on / 依赖: Icc_subset_Icc, le_rfl
-/
theorem Icc_subset_Icc_left (h : a₁ <= a₂) : Icc a₂ b subseteq Icc a₁ b :=
  Icc_subset_Icc h le_rfl

/--
theorem `Ico_subset_Ico_left` / 定理 `Ico_subset_Ico_left`

English:
theorem Ico_subset_Ico_left
  given: (h : a₁ <= a₂)
  statement: Ico a₂ b subseteq Ico a₁ b
  proof: Ico_subset_Ico h le_rfl

中文:
定理 Ico_subset_Ico_left
  条件: (h : a₁ <= a₂)
  结论: 左闭右开区间 a₂ b subseteq 左闭右开区间 a₁ b
  证明: Ico_subset_Ico h le_rfl

Depends on / 依赖: Ico_subset_Ico, le_rfl
-/
theorem Ico_subset_Ico_left (h : a₁ <= a₂) : Ico a₂ b subseteq Ico a₁ b :=
  Ico_subset_Ico h le_rfl

/--
theorem `Ioc_subset_Ioc_left` / 定理 `Ioc_subset_Ioc_left`

English:
theorem Ioc_subset_Ioc_left
  given: (h : a₁ <= a₂)
  statement: Ioc a₂ b subseteq Ioc a₁ b
  proof: Ioc_subset_Ioc h le_rfl

中文:
定理 Ioc_subset_Ioc_left
  条件: (h : a₁ <= a₂)
  结论: 左开右闭区间 a₂ b subseteq 左开右闭区间 a₁ b
  证明: Ioc_subset_Ioc h le_rfl

Depends on / 依赖: Ioc_subset_Ioc, le_rfl
-/
theorem Ioc_subset_Ioc_left (h : a₁ <= a₂) : Ioc a₂ b subseteq Ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl

/--
theorem `Ioo_subset_Ioo_left` / 定理 `Ioo_subset_Ioo_left`

English:
theorem Ioo_subset_Ioo_left
  given: (h : a₁ <= a₂)
  statement: Ioo a₂ b subseteq Ioo a₁ b
  proof: Ioo_subset_Ioo h le_rfl

中文:
定理 Ioo_subset_Ioo_left
  条件: (h : a₁ <= a₂)
  结论: 开区间 a₂ b subseteq 开区间 a₁ b
  证明: Ioo_subset_Ioo h le_rfl

Depends on / 依赖: Ioo_subset_Ioo, le_rfl
-/
theorem Ioo_subset_Ioo_left (h : a₁ <= a₂) : Ioo a₂ b subseteq Ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl

/--
theorem `Icc_subset_Icc_right` / 定理 `Icc_subset_Icc_right`

English:
theorem Icc_subset_Icc_right
  given: (h : b₁ <= b₂)
  statement: Icc a b₁ subseteq Icc a b₂
  proof: Icc_subset_Icc le_rfl h

中文:
定理 Icc_subset_Icc_right
  条件: (h : b₁ <= b₂)
  结论: 闭区间 a b₁ subseteq 闭区间 a b₂
  证明: Icc_subset_Icc le_rfl h

Depends on / 依赖: Icc_subset_Icc, le_rfl
-/
theorem Icc_subset_Icc_right (h : b₁ <= b₂) : Icc a b₁ subseteq Icc a b₂ :=
  Icc_subset_Icc le_rfl h

/--
theorem `Ico_subset_Ico_right` / 定理 `Ico_subset_Ico_right`

English:
theorem Ico_subset_Ico_right
  given: (h : b₁ <= b₂)
  statement: Ico a b₁ subseteq Ico a b₂
  proof: Ico_subset_Ico le_rfl h

中文:
定理 Ico_subset_Ico_right
  条件: (h : b₁ <= b₂)
  结论: 左闭右开区间 a b₁ subseteq 左闭右开区间 a b₂
  证明: Ico_subset_Ico le_rfl h

Depends on / 依赖: Ico_subset_Ico, le_rfl
-/
theorem Ico_subset_Ico_right (h : b₁ <= b₂) : Ico a b₁ subseteq Ico a b₂ :=
  Ico_subset_Ico le_rfl h

/--
theorem `Ioc_subset_Ioc_right` / 定理 `Ioc_subset_Ioc_right`

English:
theorem Ioc_subset_Ioc_right
  given: (h : b₁ <= b₂)
  statement: Ioc a b₁ subseteq Ioc a b₂
  proof: Ioc_subset_Ioc le_rfl h

中文:
定理 Ioc_subset_Ioc_right
  条件: (h : b₁ <= b₂)
  结论: 左开右闭区间 a b₁ subseteq 左开右闭区间 a b₂
  证明: Ioc_subset_Ioc le_rfl h

Depends on / 依赖: Ioc_subset_Ioc, le_rfl
-/
theorem Ioc_subset_Ioc_right (h : b₁ <= b₂) : Ioc a b₁ subseteq Ioc a b₂ :=
  Ioc_subset_Ioc le_rfl h

/--
theorem `Ioo_subset_Ioo_right` / 定理 `Ioo_subset_Ioo_right`

English:
theorem Ioo_subset_Ioo_right
  given: (h : b₁ <= b₂)
  statement: Ioo a b₁ subseteq Ioo a b₂
  proof: Ioo_subset_Ioo le_rfl h

中文:
定理 Ioo_subset_Ioo_right
  条件: (h : b₁ <= b₂)
  结论: 开区间 a b₁ subseteq 开区间 a b₂
  证明: Ioo_subset_Ioo le_rfl h

Depends on / 依赖: Ioo_subset_Ioo, le_rfl
-/
theorem Ioo_subset_Ioo_right (h : b₁ <= b₂) : Ioo a b₁ subseteq Ioo a b₂ :=
  Ioo_subset_Ioo le_rfl h

/--
theorem `Ico_subset_Ioo_left` / 定理 `Ico_subset_Ioo_left`

English:
theorem Ico_subset_Ioo_left
  given: (h : a₁ < a₂)
  statement: Ico a₂ b subseteq Ioo a₁ b
  proof: by
  rw [← coe_subset]; rw [coe_Ico]; rw [coe_Ioo]
  exact Set.Ico_subset_Ioo_left h

中文:
定理 Ico_subset_Ioo_left
  条件: (h : a₁ < a₂)
  结论: 左闭右开区间 a₂ b subseteq 开区间 a₁ b
  证明: by
  rw [← coe_subset]; rw [coe_Ico]; rw [coe_Ioo]
  exact Set.Ico_subset_Ioo_left h

Depends on / 依赖: Ico_subset_Ioo_left, Set.Ico_subset_Ioo_left, coe_Ico, coe_Ioo, coe_subset
-/
theorem Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b subseteq Ioo a₁ b := by
  rw [← coe_subset]; rw [coe_Ico]; rw [coe_Ioo]
  exact Set.Ico_subset_Ioo_left h

/--
theorem `Ioc_subset_Ioo_right` / 定理 `Ioc_subset_Ioo_right`

English:
theorem Ioc_subset_Ioo_right
  given: (h : b₁ < b₂)
  statement: Ioc a b₁ subseteq Ioo a b₂
  proof: by
  rw [← coe_subset]; rw [coe_Ioc]; rw [coe_Ioo]
  exact Set.Ioc_subset_Ioo_right h

中文:
定理 Ioc_subset_Ioo_right
  条件: (h : b₁ < b₂)
  结论: 左开右闭区间 a b₁ subseteq 开区间 a b₂
  证明: by
  rw [← coe_subset]; rw [coe_Ioc]; rw [coe_Ioo]
  exact Set.Ioc_subset_Ioo_right h

Depends on / 依赖: Ioc_subset_Ioo_right, Set.Ioc_subset_Ioo_right, coe_Ioc, coe_Ioo, coe_subset
-/
theorem Ioc_subset_Ioo_right (h : b₁ < b₂) : Ioc a b₁ subseteq Ioo a b₂ := by
  rw [← coe_subset]; rw [coe_Ioc]; rw [coe_Ioo]
  exact Set.Ioc_subset_Ioo_right h

/--
theorem `Icc_subset_Ico_right` / 定理 `Icc_subset_Ico_right`

English:
theorem Icc_subset_Ico_right
  given: (h : b₁ < b₂)
  statement: Icc a b₁ subseteq Ico a b₂
  proof: by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Ico]
  exact Set.Icc_subset_Ico_right h

中文:
定理 Icc_subset_Ico_right
  条件: (h : b₁ < b₂)
  结论: 闭区间 a b₁ subseteq 左闭右开区间 a b₂
  证明: by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Ico]
  exact Set.Icc_subset_Ico_right h

Depends on / 依赖: Icc_subset_Ico_right, Set.Icc_subset_Ico_right, coe_Icc, coe_Ico, coe_subset
-/
theorem Icc_subset_Ico_right (h : b₁ < b₂) : Icc a b₁ subseteq Ico a b₂ := by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Ico]
  exact Set.Icc_subset_Ico_right h

/--
theorem `Ioo_subset_Ico_self` / 定理 `Ioo_subset_Ico_self`

English:
theorem Ioo_subset_Ico_self
  statement: Ioo a b subseteq Ico a b
  proof: by
  rw [← coe_subset]; rw [coe_Ioo]; rw [coe_Ico]
  exact Set.Ioo_subset_Ico_self

中文:
定理 Ioo_subset_Ico_self
  结论: 开区间 a b subseteq 左闭右开区间 a b
  证明: by
  rw [← coe_subset]; rw [coe_Ioo]; rw [coe_Ico]
  exact Set.Ioo_subset_Ico_self

Depends on / 依赖: Ioo_subset_Ico_self, Set.Ioo_subset_Ico_self, coe_Ico, coe_Ioo, coe_subset
-/
theorem Ioo_subset_Ico_self : Ioo a b subseteq Ico a b := by
  rw [← coe_subset]; rw [coe_Ioo]; rw [coe_Ico]
  exact Set.Ioo_subset_Ico_self

/--
theorem `Ioo_subset_Ioc_self` / 定理 `Ioo_subset_Ioc_self`

English:
theorem Ioo_subset_Ioc_self
  statement: Ioo a b subseteq Ioc a b
  proof: by
  rw [← coe_subset]; rw [coe_Ioo]; rw [coe_Ioc]
  exact Set.Ioo_subset_Ioc_self

中文:
定理 Ioo_subset_Ioc_self
  结论: 开区间 a b subseteq 左开右闭区间 a b
  证明: by
  rw [← coe_subset]; rw [coe_Ioo]; rw [coe_Ioc]
  exact Set.Ioo_subset_Ioc_self

Depends on / 依赖: Ioo_subset_Ioc_self, Set.Ioo_subset_Ioc_self, coe_Ioc, coe_Ioo, coe_subset
-/
theorem Ioo_subset_Ioc_self : Ioo a b subseteq Ioc a b := by
  rw [← coe_subset]; rw [coe_Ioo]; rw [coe_Ioc]
  exact Set.Ioo_subset_Ioc_self

/--
theorem `Ico_subset_Icc_self` / 定理 `Ico_subset_Icc_self`

English:
theorem Ico_subset_Icc_self
  statement: Ico a b subseteq Icc a b
  proof: by
  rw [← coe_subset]; rw [coe_Ico]; rw [coe_Icc]
  exact Set.Ico_subset_Icc_self

中文:
定理 Ico_subset_Icc_self
  结论: 左闭右开区间 a b subseteq 闭区间 a b
  证明: by
  rw [← coe_subset]; rw [coe_Ico]; rw [coe_Icc]
  exact Set.Ico_subset_Icc_self

Depends on / 依赖: Ico_subset_Icc_self, Set.Ico_subset_Icc_self, coe_Icc, coe_Ico, coe_subset
-/
theorem Ico_subset_Icc_self : Ico a b subseteq Icc a b := by
  rw [← coe_subset]; rw [coe_Ico]; rw [coe_Icc]
  exact Set.Ico_subset_Icc_self

/--
theorem `Ioc_subset_Icc_self` / 定理 `Ioc_subset_Icc_self`

English:
theorem Ioc_subset_Icc_self
  statement: Ioc a b subseteq Icc a b
  proof: by
  rw [← coe_subset]; rw [coe_Ioc]; rw [coe_Icc]
  exact Set.Ioc_subset_Icc_self

中文:
定理 Ioc_subset_Icc_self
  结论: 左开右闭区间 a b subseteq 闭区间 a b
  证明: by
  rw [← coe_subset]; rw [coe_Ioc]; rw [coe_Icc]
  exact Set.Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, Set.Ioc_subset_Icc_self, coe_Icc, coe_Ioc, coe_subset
-/
theorem Ioc_subset_Icc_self : Ioc a b subseteq Icc a b := by
  rw [← coe_subset]; rw [coe_Ioc]; rw [coe_Icc]
  exact Set.Ioc_subset_Icc_self

/--
theorem `Ioo_subset_Icc_self` / 定理 `Ioo_subset_Icc_self`

English:
theorem Ioo_subset_Icc_self
  statement: Ioo a b subseteq Icc a b
  proof: Ioo_subset_Ico_self.trans Ico_subset_Icc_self

中文:
定理 Ioo_subset_Icc_self
  结论: 开区间 a b subseteq 闭区间 a b
  证明: Ioo_subset_Ico_self.trans Ico_subset_Icc_self

Depends on / 依赖: Ico_subset_Icc_self, Ioo_subset_Ico_self, Ioo_subset_Ico_self.trans
-/
theorem Ioo_subset_Icc_self : Ioo a b subseteq Icc a b :=
  Ioo_subset_Ico_self.trans Ico_subset_Icc_self

/--
theorem `Icc_subset_Icc_iff` / 定理 `Icc_subset_Icc_iff`

English:
theorem Icc_subset_Icc_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
  proof: by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Icc]; rw [Set.Icc_subset_Icc_iff h₁]

中文:
定理 Icc_subset_Icc_iff
  条件: (h₁ : a₁ <= b₁)
  结论: 闭区间 a₁ b₁ subseteq 闭区间 a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
  证明: by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Icc]; rw [Set.Icc_subset_Icc_iff h₁]

Depends on / 依赖: Icc_subset_Icc_iff, Set.Icc_subset_Icc_iff, coe_Icc, coe_subset
-/
theorem Icc_subset_Icc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂ := by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Icc]; rw [Set.Icc_subset_Icc_iff h₁]

/--
theorem `Icc_subset_Ioo_iff` / 定理 `Icc_subset_Ioo_iff`

English:
theorem Icc_subset_Ioo_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂
  proof: by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Ioo]; rw [Set.Icc_subset_Ioo_iff h₁]

中文:
定理 Icc_subset_Ioo_iff
  条件: (h₁ : a₁ <= b₁)
  结论: 闭区间 a₁ b₁ subseteq 开区间 a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂
  证明: by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Ioo]; rw [Set.Icc_subset_Ioo_iff h₁]

Depends on / 依赖: Icc_subset_Ioo_iff, Set.Icc_subset_Ioo_iff, coe_Icc, coe_Ioo, coe_subset
-/
theorem Icc_subset_Ioo_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Ioo]; rw [Set.Icc_subset_Ioo_iff h₁]

/--
theorem `Icc_subset_Ico_iff` / 定理 `Icc_subset_Ico_iff`

English:
theorem Icc_subset_Ico_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ < b₂
  proof: by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Ico]; rw [Set.Icc_subset_Ico_iff h₁]

中文:
定理 Icc_subset_Ico_iff
  条件: (h₁ : a₁ <= b₁)
  结论: 闭区间 a₁ b₁ subseteq 左闭右开区间 a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ < b₂
  证明: by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Ico]; rw [Set.Icc_subset_Ico_iff h₁]

Depends on / 依赖: Icc_subset_Ico_iff, Set.Icc_subset_Ico_iff, coe_Icc, coe_Ico, coe_subset
-/
theorem Icc_subset_Ico_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset]; rw [coe_Icc]; rw [coe_Ico]; rw [Set.Icc_subset_Ico_iff h₁]

/--
theorem `Icc_subset_Ioc_iff` / 定理 `Icc_subset_Ioc_iff`

English:
theorem Icc_subset_Ioc_iff
  given: (h₁ : a₁ <= b₁)
  statement: Icc a₁ b₁ subseteq Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ <= b₂
  proof: (Icc_subset_Ico_iff h₁.dual).trans and_comm

中文:
定理 Icc_subset_Ioc_iff
  条件: (h₁ : a₁ <= b₁)
  结论: 闭区间 a₁ b₁ subseteq 左开右闭区间 a₂ b₂ ↔ a₂ < a₁ ∧ b₁ <= b₂
  证明: (Icc_subset_Ico_iff h₁.dual).trans and_comm

Depends on / 依赖: Icc_subset_Ico_iff, and_comm
-/
theorem Icc_subset_Ioc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ <= b₂ :=
  (Icc_subset_Ico_iff h₁.dual).trans and_comm

--TODO: `Ico_subset_Ioo_iff`, `Ioc_subset_Ioo_iff`
/--
theorem `Icc_ssubset_Icc_left` / 定理 `Icc_ssubset_Icc_left`

English:
theorem Icc_ssubset_Icc_left
  given: (hI : a₂ <= b₂) (ha : a₂ < a₁) (hb : b₁ <= b₂)
  proof: by
  rw [← coe_ssubset]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.Icc_ssubset_Icc_left hI ha hb

中文:
定理 Icc_ssubset_Icc_left
  条件: (hI : a₂ <= b₂) (ha : a₂ < a₁) (hb : b₁ <= b₂)
  证明: by
  rw [← coe_ssubset]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.Icc_ssubset_Icc_left hI ha hb

Depends on / 依赖: Icc_ssubset_Icc_left, Set.Icc_ssubset_Icc_left, coe_Icc, coe_ssubset
-/
theorem Icc_ssubset_Icc_left (hI : a₂ <= b₂) (ha : a₂ < a₁) (hb : b₁ <= b₂) :
    Icc a₁ b₁ ⊂ Icc a₂ b₂ := by
  rw [← coe_ssubset]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.Icc_ssubset_Icc_left hI ha hb

/--
theorem `Icc_ssubset_Icc_right` / 定理 `Icc_ssubset_Icc_right`

English:
theorem Icc_ssubset_Icc_right
  given: (hI : a₂ <= b₂) (ha : a₂ <= a₁) (hb : b₁ < b₂)
  proof: by
  rw [← coe_ssubset]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.Icc_ssubset_Icc_right hI ha hb

@[simp]

中文:
定理 Icc_ssubset_Icc_right
  条件: (hI : a₂ <= b₂) (ha : a₂ <= a₁) (hb : b₁ < b₂)
  证明: by
  rw [← coe_ssubset]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.Icc_ssubset_Icc_right hI ha hb

@[simp]

Depends on / 依赖: Icc_ssubset_Icc_right, Set.Icc_ssubset_Icc_right, coe_Icc, coe_ssubset
-/
theorem Icc_ssubset_Icc_right (hI : a₂ <= b₂) (ha : a₂ <= a₁) (hb : b₁ < b₂) :
    Icc a₁ b₁ ⊂ Icc a₂ b₂ := by
  rw [← coe_ssubset]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.Icc_ssubset_Icc_right hI ha hb

@[simp]
/--
theorem `Ioc_disjoint_Ioc_of_le` / 定理 `Ioc_disjoint_Ioc_of_le`

English:
theorem Ioc_disjoint_Ioc_of_le
  given: {d : α} (hbc : b <= c)
  statement: Disjoint (Ioc a b) (Ioc c d)
  proof: disjoint_left.2 fun _ h1 h2 => not_and_of_not_left _
    ((mem_Ioc.1 h1).2.trans hbc).not_gt (mem_Ioc.1 h2)

中文:
定理 Ioc_disjoint_Ioc_of_le
  条件: {d : α} (hbc : b <= c)
  结论: Disjoint (左开右闭区间 a b) (左开右闭区间 c d)
  证明: disjoint_left.2 fun _ h1 h2 => not_and_of_not_left _
    ((mem_Ioc.1 h1).2.trans hbc).not_gt (mem_Ioc.1 h2)

Depends on / 依赖: disjoint_left, mem_Ioc, not_and_of_not_left, not_gt
-/
theorem Ioc_disjoint_Ioc_of_le {d : α} (hbc : b <= c) : Disjoint (Ioc a b) (Ioc c d) :=
  disjoint_left.2 fun _ h1 h2 => not_and_of_not_left _
    ((mem_Ioc.1 h1).2.trans hbc).not_gt (mem_Ioc.1 h2)

/--
lemma `_root_.not_lt_of_denselyOrdered_of_locallyFinite` / 引理 `_root_.not_lt_of_denselyOrdered_of_locallyFinite`

English:
lemma _root_.not_lt_of_denselyOrdered_of_locallyFinite
  given: [DenselyOrdered α] (a b : α)
  proof: by
  intro h
  induction hs : Finset.Icc a b using Finset.strongInduction generalizing b with | H i ih
  subst hs
  obtain ⟨c, hac, hcb⟩ := exists_between h
  refine ih _ ?_ c hac rfl
  exact Finset.Icc_ssubset_Icc_right (hac.trans hcb).le le_rfl hcb

中文:
引理 _root_.not_lt_of_denselyOrdered_of_locallyFinite
  条件: [稠密序 α] (a b : α)
  证明: by
  intro h
  induction hs : Finset.Icc a b using Finset.strongInduction generalizing b with | H i ih
  subst hs
  obtain ⟨c, hac, hcb⟩ := exists_between h
  refine ih _ ?_ c hac rfl
  exact Finset.Icc_ssubset_Icc_right (hac.trans hcb).le le_rfl hcb

Depends on / 依赖: Finset, Finset.Icc, Finset.Icc_ssubset_Icc_right, Finset.strongInduction, Icc_ssubset_Icc_right, exists_between, generalizing, hac.trans, le_rfl, strongInduction
-/
lemma _root_.not_lt_of_denselyOrdered_of_locallyFinite [DenselyOrdered α] (a b : α) :
    ¬ a < b := by
  intro h
  induction hs : Finset.Icc a b using Finset.strongInduction generalizing b with | H i ih
  subst hs
  obtain ⟨c, hac, hcb⟩ := exists_between h
  refine ih _ ?_ c hac rfl
  exact Finset.Icc_ssubset_Icc_right (hac.trans hcb).le le_rfl hcb

variable (a)

/--
theorem `Ico_self` / 定理 `Ico_self`

English:
theorem Ico_self
  statement: Ico a a = ∅
  proof: Ico_eq_empty lt_irrefl _

中文:
定理 Ico_self
  结论: 左闭右开区间 a a = ∅
  证明: Ico_eq_empty lt_irrefl _

Depends on / 依赖: Ico_eq_empty, lt_irrefl
-/
theorem Ico_self : Ico a a = ∅ :=
Ico_eq_empty lt_irrefl _

/--
theorem `Ioc_self` / 定理 `Ioc_self`

English:
theorem Ioc_self
  statement: Ioc a a = ∅
  proof: Ioc_eq_empty lt_irrefl _

中文:
定理 Ioc_self
  结论: 左开右闭区间 a a = ∅
  证明: Ioc_eq_empty lt_irrefl _

Depends on / 依赖: Ioc_eq_empty, lt_irrefl
-/
theorem Ioc_self : Ioc a a = ∅ :=
Ioc_eq_empty lt_irrefl _

/--
theorem `Ioo_self` / 定理 `Ioo_self`

English:
theorem Ioo_self
  statement: Ioo a a = ∅
  proof: Ioo_eq_empty lt_irrefl _

中文:
定理 Ioo_self
  结论: 开区间 a a = ∅
  证明: Ioo_eq_empty lt_irrefl _

Depends on / 依赖: Ioo_eq_empty, lt_irrefl
-/
theorem Ioo_self : Ioo a a = ∅ :=
Ioo_eq_empty lt_irrefl _

variable {a}

/-- A set with upper and lower bounds in a locally finite order is a fintype -/
@[instance_reducible]
/--
Definition of `_root_.Set.fintypeOfMemBounds` / `_root_.Set.fintypeOfMemBounds` 的定义

English:
definition _root_.Set.fintypeOfMemBounds
  signature: {s : Set α} [DecidablePred (· in s)] (ha : a in lowerBounds s)
  body: Set.fintypeSubset (Set.Icc a b) fun _ hx => ⟨ha hx, hb hx⟩

中文:
定义 _root_.集合.fintypeOfMemBounds
  签名: {s : 集合 α} [DecidablePred (· in s)] (ha : a in lowerBounds s)
  定义体: Set.fintypeSubset (Set.Icc a b) fun _ hx => ⟨ha hx, hb hx⟩

Depends on / 依赖: Set.Icc, Set.fintypeSubset, fintypeSubset
-/
def _root_.Set.fintypeOfMemBounds {s : Set α} [DecidablePred (· in s)] (ha : a in lowerBounds s)
    (hb : b in upperBounds s) : Fintype s :=
  Set.fintypeSubset (Set.Icc a b) fun _ hx => ⟨ha hx, hb hx⟩

section Filter

/--
theorem `Ico_filter_lt_of_le_left` / 定理 `Ico_filter_lt_of_le_left`

English:
theorem Ico_filter_lt_of_le_left
  given: [DecidablePred (· < c)] (hca : c <= a)
  proof: filter_false_of_mem fun _ hx => (hca.trans (mem_Ico.1 hx).1).not_gt

中文:
定理 Ico_filter_lt_of_le_left
  条件: [DecidablePred (· < c)] (hca : c <= a)
  证明: filter_false_of_mem fun _ hx => (hca.trans (mem_Ico.1 hx).1).not_gt

Depends on / 依赖: filter_false_of_mem, hca.trans, mem_Ico, not_gt
-/
theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c <= a) :
    {x in Ico a b | x < c} = ∅ :=
  filter_false_of_mem fun _ hx => (hca.trans (mem_Ico.1 hx).1).not_gt

/--
theorem `Ico_filter_lt_of_right_le` / 定理 `Ico_filter_lt_of_right_le`

English:
theorem Ico_filter_lt_of_right_le
  given: [DecidablePred (· < c)] (hbc : b <= c)
  proof: filter_true_of_mem fun _ hx => (mem_Ico.1 hx).2.trans_le hbc

中文:
定理 Ico_filter_lt_of_right_le
  条件: [DecidablePred (· < c)] (hbc : b <= c)
  证明: filter_true_of_mem fun _ hx => (mem_Ico.1 hx).2.trans_le hbc

Depends on / 依赖: filter_true_of_mem, mem_Ico, trans_le
-/
theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b <= c) :
    {x in Ico a b | x < c} = Ico a b :=
  filter_true_of_mem fun _ hx => (mem_Ico.1 hx).2.trans_le hbc

/--
theorem `Ico_filter_lt_of_le_right` / 定理 `Ico_filter_lt_of_le_right`

English:
theorem Ico_filter_lt_of_le_right
  given: [DecidablePred (· < c)] (hcb : c <= b)
  proof: by
  grind

中文:
定理 Ico_filter_lt_of_le_right
  条件: [DecidablePred (· < c)] (hcb : c <= b)
  证明: by
  grind
-/
theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c <= b) :
    {x in Ico a b | x < c} = Ico a c := by
  grind

/--
theorem `Ico_filter_le_of_le_left` / 定理 `Ico_filter_le_of_le_left`

English:
theorem Ico_filter_le_of_le_left
  given: {a b c : α} [DecidablePred (c <= ·)] (hca : c <= a)
  proof: filter_true_of_mem fun _ hx => hca.trans (mem_Ico.1 hx).1

中文:
定理 Ico_filter_le_of_le_left
  条件: {a b c : α} [DecidablePred (c <= ·)] (hca : c <= a)
  证明: filter_true_of_mem fun _ hx => hca.trans (mem_Ico.1 hx).1

Depends on / 依赖: filter_true_of_mem, hca.trans, mem_Ico
-/
theorem Ico_filter_le_of_le_left {a b c : α} [DecidablePred (c <= ·)] (hca : c <= a) :
    {x in Ico a b | c <= x} = Ico a b :=
  filter_true_of_mem fun _ hx => hca.trans (mem_Ico.1 hx).1

/--
theorem `Ico_filter_le_of_right_le` / 定理 `Ico_filter_le_of_right_le`

English:
theorem Ico_filter_le_of_right_le
  given: {a b : α} [DecidablePred (b <= ·)]
  proof: filter_false_of_mem fun _ hx => (mem_Ico.1 hx).2.not_ge

中文:
定理 Ico_filter_le_of_right_le
  条件: {a b : α} [DecidablePred (b <= ·)]
  证明: filter_false_of_mem fun _ hx => (mem_Ico.1 hx).2.not_ge

Depends on / 依赖: filter_false_of_mem, mem_Ico, not_ge
-/
theorem Ico_filter_le_of_right_le {a b : α} [DecidablePred (b <= ·)] :
    {x in Ico a b | b <= x} = ∅ :=
  filter_false_of_mem fun _ hx => (mem_Ico.1 hx).2.not_ge

/--
theorem `Ico_filter_le_of_left_le` / 定理 `Ico_filter_le_of_left_le`

English:
theorem Ico_filter_le_of_left_le
  given: {a b c : α} [DecidablePred (c <= ·)] (hac : a <= c)
  proof: by
  grind

中文:
定理 Ico_filter_le_of_left_le
  条件: {a b c : α} [DecidablePred (c <= ·)] (hac : a <= c)
  证明: by
  grind
-/
theorem Ico_filter_le_of_left_le {a b c : α} [DecidablePred (c <= ·)] (hac : a <= c) :
    {x in Ico a b | c <= x} = Ico c b := by
  grind

/--
theorem `Icc_filter_lt_of_lt_right` / 定理 `Icc_filter_lt_of_lt_right`

English:
theorem Icc_filter_lt_of_lt_right
  given: {a b c : α} [DecidablePred (· < c)] (h : b < c)
  proof: filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Icc.1 hx).2 h

中文:
定理 Icc_filter_lt_of_lt_right
  条件: {a b c : α} [DecidablePred (· < c)] (h : b < c)
  证明: filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Icc.1 hx).2 h

Depends on / 依赖: filter_true_of_mem, lt_of_le_of_lt, mem_Icc
-/
theorem Icc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    {x in Icc a b | x < c} = Icc a b :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Icc.1 hx).2 h

/--
theorem `Ioc_filter_lt_of_lt_right` / 定理 `Ioc_filter_lt_of_lt_right`

English:
theorem Ioc_filter_lt_of_lt_right
  given: {a b c : α} [DecidablePred (· < c)] (h : b < c)
  proof: filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Ioc.1 hx).2 h

中文:
定理 Ioc_filter_lt_of_lt_right
  条件: {a b c : α} [DecidablePred (· < c)] (h : b < c)
  证明: filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Ioc.1 hx).2 h

Depends on / 依赖: filter_true_of_mem, lt_of_le_of_lt, mem_Ioc
-/
theorem Ioc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    {x in Ioc a b | x < c} = Ioc a b :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Ioc.1 hx).2 h

/--
theorem `Iic_filter_lt_of_lt_right` / 定理 `Iic_filter_lt_of_lt_right`

English:
theorem Iic_filter_lt_of_lt_right
  statement: {α} [Preorder α] [LocallyFiniteOrderBot α] {a c : α}
  proof: filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Iic.1 hx) h

中文:
定理 Iic_filter_lt_of_lt_right
  结论: {α} [预序 α] [LocallyFiniteOrderBot α] {a c : α}
  证明: filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Iic.1 hx) h

Depends on / 依赖: filter_true_of_mem, lt_of_le_of_lt, mem_Iic
-/
theorem Iic_filter_lt_of_lt_right {α} [Preorder α] [LocallyFiniteOrderBot α] {a c : α}
    [DecidablePred (· < c)] (h : a < c) : {x in Iic a | x < c} = Iic a :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Iic.1 hx) h

variable (a b) [Fintype α]

/--
theorem `filter_lt_lt_eq_Ioo` / 定理 `filter_lt_lt_eq_Ioo`

English:
theorem filter_lt_lt_eq_Ioo
  given: [DecidablePred fun j => a < j ∧ j < b]
  proof: by ext; simp

中文:
定理 filter_lt_lt_eq_Ioo
  条件: [DecidablePred fun j => a < j ∧ j < b]
  证明: by ext; simp
-/
theorem filter_lt_lt_eq_Ioo [DecidablePred fun j => a < j ∧ j < b] :
    ({j | a < j ∧ j < b} : Finset _) = Ioo a b := by ext; simp

/--
theorem `filter_lt_le_eq_Ioc` / 定理 `filter_lt_le_eq_Ioc`

English:
theorem filter_lt_le_eq_Ioc
  given: [DecidablePred fun j => a < j ∧ j <= b]
  proof: by ext; simp

中文:
定理 filter_lt_le_eq_Ioc
  条件: [DecidablePred fun j => a < j ∧ j <= b]
  证明: by ext; simp
-/
theorem filter_lt_le_eq_Ioc [DecidablePred fun j => a < j ∧ j <= b] :
    ({j | a < j ∧ j <= b} : Finset _) = Ioc a b := by ext; simp

/--
theorem `filter_le_lt_eq_Ico` / 定理 `filter_le_lt_eq_Ico`

English:
theorem filter_le_lt_eq_Ico
  given: [DecidablePred fun j => a <= j ∧ j < b]
  proof: by ext; simp

中文:
定理 filter_le_lt_eq_Ico
  条件: [DecidablePred fun j => a <= j ∧ j < b]
  证明: by ext; simp
-/
theorem filter_le_lt_eq_Ico [DecidablePred fun j => a <= j ∧ j < b] :
    ({j | a <= j ∧ j < b} : Finset _) = Ico a b := by ext; simp

/--
theorem `filter_le_le_eq_Icc` / 定理 `filter_le_le_eq_Icc`

English:
theorem filter_le_le_eq_Icc
  given: [DecidablePred fun j => a <= j ∧ j <= b]
  proof: by ext; simp

中文:
定理 filter_le_le_eq_Icc
  条件: [DecidablePred fun j => a <= j ∧ j <= b]
  证明: by ext; simp
-/
theorem filter_le_le_eq_Icc [DecidablePred fun j => a <= j ∧ j <= b] :
    ({j | a <= j ∧ j <= b} : Finset _) = Icc a b := by ext; simp

end Filter

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

@[simp]
/--
theorem `Ioi_eq_empty` / 定理 `Ioi_eq_empty`

English:
theorem Ioi_eq_empty
  statement: Ioi a = ∅ ↔ IsMax a
  proof: by
  rw [← coe_eq_empty]; rw [coe_Ioi]; rw [Set.Ioi_eq_empty_iff]

@[simp] alias ⟨_, _root_.IsMax.finsetIoi_eq⟩ := Ioi_eq_empty

中文:
定理 Ioi_eq_empty
  结论: 左开右无界区间 a = ∅ ↔ IsMax a
  证明: by
  rw [← coe_eq_empty]; rw [coe_Ioi]; rw [Set.Ioi_eq_empty_iff]

@[simp] alias ⟨_, _root_.IsMax.finsetIoi_eq⟩ := Ioi_eq_empty

Depends on / 依赖: Ioi_eq_empty_iff, Set.Ioi_eq_empty_iff, coe_Ioi, coe_eq_empty
-/
theorem Ioi_eq_empty : Ioi a = ∅ ↔ IsMax a := by
  rw [← coe_eq_empty]; rw [coe_Ioi]; rw [Set.Ioi_eq_empty_iff]

@[simp] alias ⟨_, _root_.IsMax.finsetIoi_eq⟩ := Ioi_eq_empty

/--
lemma `Ioi_nonempty` / 引理 `Ioi_nonempty`

English:
lemma Ioi_nonempty
  statement: (Ioi a).Nonempty ↔ ¬ IsMax a
  proof: by
  contrapose!; exact Ioi_eq_empty

中文:
引理 Ioi_nonempty
  结论: (左开右无界区间 a).非空 ↔ ¬ IsMax a
  证明: by
  contrapose!; exact Ioi_eq_empty
-/
@[simp] lemma Ioi_nonempty : (Ioi a).Nonempty ↔ ¬ IsMax a := by
  contrapose!; exact Ioi_eq_empty

/--
theorem `Ioi_top` / 定理 `Ioi_top`

English:
theorem Ioi_top
  given: [OrderTop α]
  statement: Ioi (⊤ : α) = ∅
  proof: Ioi_eq_empty.mpr isMax_top

@[simp]

中文:
定理 Ioi_top
  条件: [有顶序 α]
  结论: 左开右无界区间 (⊤ : α) = ∅
  证明: Ioi_eq_empty.mpr isMax_top

@[simp]

Depends on / 依赖: Ioi_eq_empty, Ioi_eq_empty.mpr, isMax_top
-/
theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ∅ := Ioi_eq_empty.mpr isMax_top

@[simp]
/--
theorem `Ici_bot` / 定理 `Ici_bot`

English:
theorem Ici_bot
  given: [OrderBot α] [Fintype α]
  statement: Ici (⊥ : α) = univ
  proof: by
  ext a; simp only [mem_Ici, bot_le, mem_univ]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 Ici_bot
  条件: [有底序 α] [有限类型 α]
  结论: 左闭右无界区间 (⊥ : α) = univ
  证明: by
  ext a; simp only [mem_Ici, bot_le, mem_univ]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: bot_le, mem_Ici, mem_univ
-/
theorem Ici_bot [OrderBot α] [Fintype α] : Ici (⊥ : α) = univ := by
  ext a; simp only [mem_Ici, bot_le, mem_univ]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/--
lemma `nonempty_Ici` / 引理 `nonempty_Ici`

English:
lemma nonempty_Ici
  statement: (Ici a).Nonempty
  proof: ⟨a, mem_Ici.2 le_rfl⟩

中文:
引理 nonempty_Ici
  结论: (左闭右无界区间 a).非空
  证明: ⟨a, mem_Ici.2 le_rfl⟩

Depends on / 依赖: le_rfl, mem_Ici
-/
lemma nonempty_Ici : (Ici a).Nonempty := ⟨a, mem_Ici.2 le_rfl⟩
/--
lemma `nonempty_Ioi` / 引理 `nonempty_Ioi`

English:
lemma nonempty_Ioi
  statement: (Ioi a).Nonempty ↔ ¬ IsMax a
  proof: by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ioi_of_not_isMax⟩ := nonempty_Ioi

@[simp, gcongr]

中文:
引理 nonempty_Ioi
  结论: (左开右无界区间 a).非空 ↔ ¬ IsMax a
  证明: by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ioi_of_not_isMax⟩ := nonempty_Ioi

@[simp, gcongr]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty
-/
lemma nonempty_Ioi : (Ioi a).Nonempty ↔ ¬ IsMax a := by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ioi_of_not_isMax⟩ := nonempty_Ioi

@[simp, gcongr]
/--
theorem `Ici_subset_Ici` / 定理 `Ici_subset_Ici`

English:
theorem Ici_subset_Ici
  statement: Ici a subseteq Ici b ↔ b <= a
  proof: by
  simp [← coe_subset]

@[simp, gcongr]

中文:
定理 Ici_subset_Ici
  结论: 左闭右无界区间 a subseteq 左闭右无界区间 b ↔ b <= a
  证明: by
  simp [← coe_subset]

@[simp, gcongr]

Depends on / 依赖: coe_subset
-/
theorem Ici_subset_Ici : Ici a subseteq Ici b ↔ b <= a := by
  simp [← coe_subset]

@[simp, gcongr]
/--
theorem `Ici_ssubset_Ici` / 定理 `Ici_ssubset_Ici`

English:
theorem Ici_ssubset_Ici
  statement: Ici a ⊂ Ici b ↔ b < a
  proof: by
  simp [← coe_ssubset]

@[gcongr]

中文:
定理 Ici_ssubset_Ici
  结论: 左闭右无界区间 a ⊂ 左闭右无界区间 b ↔ b < a
  证明: by
  simp [← coe_ssubset]

@[gcongr]

Depends on / 依赖: coe_ssubset
-/
theorem Ici_ssubset_Ici : Ici a ⊂ Ici b ↔ b < a := by
  simp [← coe_ssubset]

@[gcongr]
/--
theorem `Ioi_subset_Ioi` / 定理 `Ioi_subset_Ioi`

English:
theorem Ioi_subset_Ioi
  given: (h : a <= b)
  statement: Ioi b subseteq Ioi a
  proof: by
  simpa [← coe_subset] using Set.Ioi_subset_Ioi h

@[gcongr]

中文:
定理 Ioi_subset_Ioi
  条件: (h : a <= b)
  结论: 左开右无界区间 b subseteq 左开右无界区间 a
  证明: by
  simpa [← coe_subset] using Set.Ioi_subset_Ioi h

@[gcongr]

Depends on / 依赖: Ioi_subset_Ioi, Set.Ioi_subset_Ioi, coe_subset
-/
theorem Ioi_subset_Ioi (h : a <= b) : Ioi b subseteq Ioi a := by
  simpa [← coe_subset] using Set.Ioi_subset_Ioi h

@[gcongr]
/--
theorem `Ioi_ssubset_Ioi` / 定理 `Ioi_ssubset_Ioi`

English:
theorem Ioi_ssubset_Ioi
  given: (h : a < b)
  statement: Ioi b ⊂ Ioi a
  proof: by
  simpa [← coe_ssubset] using Set.Ioi_ssubset_Ioi h

中文:
定理 Ioi_ssubset_Ioi
  条件: (h : a < b)
  结论: 左开右无界区间 b ⊂ 左开右无界区间 a
  证明: by
  simpa [← coe_ssubset] using Set.Ioi_ssubset_Ioi h

Depends on / 依赖: Ioi_ssubset_Ioi, Set.Ioi_ssubset_Ioi, coe_ssubset
-/
theorem Ioi_ssubset_Ioi (h : a < b) : Ioi b ⊂ Ioi a := by
  simpa [← coe_ssubset] using Set.Ioi_ssubset_Ioi h

variable [LocallyFiniteOrder α]

/--
theorem `Icc_subset_Ici_self` / 定理 `Icc_subset_Ici_self`

English:
theorem Icc_subset_Ici_self
  statement: Icc a b subseteq Ici a
  proof: by
  simpa [← coe_subset] using Set.Icc_subset_Ici_self

中文:
定理 Icc_subset_Ici_self
  结论: 闭区间 a b subseteq 左闭右无界区间 a
  证明: by
  simpa [← coe_subset] using Set.Icc_subset_Ici_self

Depends on / 依赖: Icc_subset_Ici_self, Set.Icc_subset_Ici_self, coe_subset
-/
theorem Icc_subset_Ici_self : Icc a b subseteq Ici a := by
  simpa [← coe_subset] using Set.Icc_subset_Ici_self

/--
theorem `Ico_subset_Ici_self` / 定理 `Ico_subset_Ici_self`

English:
theorem Ico_subset_Ici_self
  statement: Ico a b subseteq Ici a
  proof: by
  simpa [← coe_subset] using Set.Ico_subset_Ici_self

中文:
定理 Ico_subset_Ici_self
  结论: 左闭右开区间 a b subseteq 左闭右无界区间 a
  证明: by
  simpa [← coe_subset] using Set.Ico_subset_Ici_self

Depends on / 依赖: Ico_subset_Ici_self, Set.Ico_subset_Ici_self, coe_subset
-/
theorem Ico_subset_Ici_self : Ico a b subseteq Ici a := by
  simpa [← coe_subset] using Set.Ico_subset_Ici_self

/--
theorem `Ioc_subset_Ioi_self` / 定理 `Ioc_subset_Ioi_self`

English:
theorem Ioc_subset_Ioi_self
  statement: Ioc a b subseteq Ioi a
  proof: by
  simpa [← coe_subset] using Set.Ioc_subset_Ioi_self

中文:
定理 Ioc_subset_Ioi_self
  结论: 左开右闭区间 a b subseteq 左开右无界区间 a
  证明: by
  simpa [← coe_subset] using Set.Ioc_subset_Ioi_self

Depends on / 依赖: Ioc_subset_Ioi_self, Set.Ioc_subset_Ioi_self, coe_subset
-/
theorem Ioc_subset_Ioi_self : Ioc a b subseteq Ioi a := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioi_self

/--
theorem `Ioo_subset_Ioi_self` / 定理 `Ioo_subset_Ioi_self`

English:
theorem Ioo_subset_Ioi_self
  statement: Ioo a b subseteq Ioi a
  proof: by
  simpa [← coe_subset] using Set.Ioo_subset_Ioi_self

中文:
定理 Ioo_subset_Ioi_self
  结论: 开区间 a b subseteq 左开右无界区间 a
  证明: by
  simpa [← coe_subset] using Set.Ioo_subset_Ioi_self

Depends on / 依赖: Finset, Finset.coe_image, Ioo_subset_Ioi_self, Set.Ioo_subset_Ioi_self, classical, coe_image, coe_subset, map_span, s.image
-/
theorem Ioo_subset_Ioi_self : Ioo a b subseteq Ioi a := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioi_self

/--
theorem `Ioc_subset_Ici_self` / 定理 `Ioc_subset_Ici_self`

English:
theorem Ioc_subset_Ici_self
  statement: Ioc a b subseteq Ici a
  proof: Ioc_subset_Icc_self.trans Icc_subset_Ici_self

中文:
定理 Ioc_subset_Ici_self
  结论: 左开右闭区间 a b subseteq 左闭右无界区间 a
  证明: Ioc_subset_Icc_self.trans Icc_subset_Ici_self

Depends on / 依赖: Icc_subset_Ici_self, Ioc_subset_Icc_self, Ioc_subset_Icc_self.trans
-/
theorem Ioc_subset_Ici_self : Ioc a b subseteq Ici a :=
  Ioc_subset_Icc_self.trans Icc_subset_Ici_self

/--
theorem `Ioo_subset_Ici_self` / 定理 `Ioo_subset_Ici_self`

English:
theorem Ioo_subset_Ici_self
  statement: Ioo a b subseteq Ici a
  proof: Ioo_subset_Ico_self.trans Ico_subset_Ici_self

中文:
定理 Ioo_subset_Ici_self
  结论: 开区间 a b subseteq 左闭右无界区间 a
  证明: Ioo_subset_Ico_self.trans Ico_subset_Ici_self

Depends on / 依赖: Ico_subset_Ici_self, Ioo_subset_Ico_self, Ioo_subset_Ico_self.trans
-/
theorem Ioo_subset_Ici_self : Ioo a b subseteq Ici a :=
  Ioo_subset_Ico_self.trans Ico_subset_Ici_self

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

@[simp]
/--
theorem `Iio_eq_empty` / 定理 `Iio_eq_empty`

English:
theorem Iio_eq_empty
  statement: Iio a = ∅ ↔ IsMin a
  proof: Ioi_eq_empty (α := αᵒᵈ)

@[simp] alias ⟨_, _root_.IsMin.finsetIio_eq⟩ := Iio_eq_empty

中文:
定理 Iio_eq_empty
  结论: 左无界右开区间 a = ∅ ↔ IsMin a
  证明: Ioi_eq_empty (α := αᵒᵈ)

@[simp] alias ⟨_, _root_.IsMin.finsetIio_eq⟩ := Iio_eq_empty

Depends on / 依赖: Ioi_eq_empty
-/
theorem Iio_eq_empty : Iio a = ∅ ↔ IsMin a := Ioi_eq_empty (α := αᵒᵈ)

@[simp] alias ⟨_, _root_.IsMin.finsetIio_eq⟩ := Iio_eq_empty

/--
lemma `Iio_nonempty` / 引理 `Iio_nonempty`

English:
lemma Iio_nonempty
  statement: (Iio a).Nonempty ↔ ¬ IsMin a
  proof: by
  contrapose!; exact Iio_eq_empty

中文:
引理 Iio_nonempty
  结论: (左无界右开区间 a).非空 ↔ ¬ IsMin a
  证明: by
  contrapose!; exact Iio_eq_empty
-/
@[simp] lemma Iio_nonempty : (Iio a).Nonempty ↔ ¬ IsMin a := by
  contrapose!; exact Iio_eq_empty

/--
theorem `Iio_bot` / 定理 `Iio_bot`

English:
theorem Iio_bot
  given: [OrderBot α]
  statement: Iio (⊥ : α) = ∅
  proof: Iio_eq_empty.mpr isMin_bot

@[simp]

中文:
定理 Iio_bot
  条件: [有底序 α]
  结论: 左无界右开区间 (⊥ : α) = ∅
  证明: Iio_eq_empty.mpr isMin_bot

@[simp]

Depends on / 依赖: Iio_eq_empty, Iio_eq_empty.mpr, isMin_bot
-/
theorem Iio_bot [OrderBot α] : Iio (⊥ : α) = ∅ := Iio_eq_empty.mpr isMin_bot

@[simp]
/--
theorem `Iic_top` / 定理 `Iic_top`

English:
theorem Iic_top
  given: [OrderTop α] [Fintype α]
  statement: Iic (⊤ : α) = univ
  proof: by
  ext a; simp only [mem_Iic, le_top, mem_univ]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 Iic_top
  条件: [有顶序 α] [有限类型 α]
  结论: 左无界右闭区间 (⊤ : α) = univ
  证明: by
  ext a; simp only [mem_Iic, le_top, mem_univ]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: le_top, mem_Iic, mem_univ
-/
theorem Iic_top [OrderTop α] [Fintype α] : Iic (⊤ : α) = univ := by
  ext a; simp only [mem_Iic, le_top, mem_univ]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/--
lemma `nonempty_Iic` / 引理 `nonempty_Iic`

English:
lemma nonempty_Iic
  statement: (Iic a).Nonempty
  proof: ⟨a, mem_Iic.2 le_rfl⟩

中文:
引理 nonempty_Iic
  结论: (左无界右闭区间 a).非空
  证明: ⟨a, mem_Iic.2 le_rfl⟩

Depends on / 依赖: le_rfl, mem_Iic
-/
lemma nonempty_Iic : (Iic a).Nonempty := ⟨a, mem_Iic.2 le_rfl⟩
/--
lemma `nonempty_Iio` / 引理 `nonempty_Iio`

English:
lemma nonempty_Iio
  statement: (Iio a).Nonempty ↔ ¬ IsMin a
  proof: by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Iio_of_not_isMin⟩ := nonempty_Iio

@[simp, gcongr]

中文:
引理 nonempty_Iio
  结论: (左无界右开区间 a).非空 ↔ ¬ IsMin a
  证明: by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Iio_of_not_isMin⟩ := nonempty_Iio

@[simp, gcongr]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty
-/
lemma nonempty_Iio : (Iio a).Nonempty ↔ ¬ IsMin a := by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Iio_of_not_isMin⟩ := nonempty_Iio

@[simp, gcongr]
/--
theorem `Iic_subset_Iic` / 定理 `Iic_subset_Iic`

English:
theorem Iic_subset_Iic
  statement: Iic a subseteq Iic b ↔ a <= b
  proof: by
  simp [← coe_subset]

@[simp, gcongr]

中文:
定理 Iic_subset_Iic
  结论: 左无界右闭区间 a subseteq 左无界右闭区间 b ↔ a <= b
  证明: by
  simp [← coe_subset]

@[simp, gcongr]

Depends on / 依赖: coe_subset
-/
theorem Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b := by
  simp [← coe_subset]

@[simp, gcongr]
/--
theorem `Iic_ssubset_Iic` / 定理 `Iic_ssubset_Iic`

English:
theorem Iic_ssubset_Iic
  statement: Iic a ⊂ Iic b ↔ a < b
  proof: by
  simp [← coe_ssubset]

@[gcongr]

中文:
定理 Iic_ssubset_Iic
  结论: 左无界右闭区间 a ⊂ 左无界右闭区间 b ↔ a < b
  证明: by
  simp [← coe_ssubset]

@[gcongr]

Depends on / 依赖: coe_ssubset
-/
theorem Iic_ssubset_Iic : Iic a ⊂ Iic b ↔ a < b := by
  simp [← coe_ssubset]

@[gcongr]
/--
theorem `Iio_subset_Iio` / 定理 `Iio_subset_Iio`

English:
theorem Iio_subset_Iio
  given: (h : a <= b)
  statement: Iio a subseteq Iio b
  proof: by
  simpa [← coe_subset] using Set.Iio_subset_Iio h

@[gcongr]

中文:
定理 Iio_subset_Iio
  条件: (h : a <= b)
  结论: 左无界右开区间 a subseteq 左无界右开区间 b
  证明: by
  simpa [← coe_subset] using Set.Iio_subset_Iio h

@[gcongr]

Depends on / 依赖: Iio_subset_Iio, Set.Iio_subset_Iio, coe_subset
-/
theorem Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b := by
  simpa [← coe_subset] using Set.Iio_subset_Iio h

@[gcongr]
/--
theorem `Iio_ssubset_Iio` / 定理 `Iio_ssubset_Iio`

English:
theorem Iio_ssubset_Iio
  given: (h : a < b)
  statement: Iio a ⊂ Iio b
  proof: by
  simpa [← coe_ssubset] using Set.Iio_ssubset_Iio h

中文:
定理 Iio_ssubset_Iio
  条件: (h : a < b)
  结论: 左无界右开区间 a ⊂ 左无界右开区间 b
  证明: by
  simpa [← coe_ssubset] using Set.Iio_ssubset_Iio h

Depends on / 依赖: Iio_ssubset_Iio, Set.Iio_ssubset_Iio, coe_ssubset
-/
theorem Iio_ssubset_Iio (h : a < b) : Iio a ⊂ Iio b := by
  simpa [← coe_ssubset] using Set.Iio_ssubset_Iio h

/--
theorem `sup_Iic_of_monotone` / 定理 `sup_Iic_of_monotone`

English:
theorem sup_Iic_of_monotone
  statement: {β : Type*} [SemilatticeSup β] [OrderBot β] {f : α -> β}
  proof: le_antisymm (Finset.sup_le_iff.mpr fun _ h => hf (by simpa using h)) (le_sup (by simp))

中文:
定理 sup_Iic_of_monotone
  结论: {β : 类型} [SemilatticeSup β] [有底序 β] {f : α -> β}
  证明: le_antisymm (Finset.sup_le_iff.mpr fun _ h => hf (by simpa using h)) (le_sup (by simp))

Depends on / 依赖: Finset, Finset.sup_le_iff.mpr, le_antisymm, le_sup, sup_le_iff
-/
theorem sup_Iic_of_monotone {β : Type*} [SemilatticeSup β] [OrderBot β] {f : α -> β}
    (hf : Monotone f) : (Iic a).sup f = f a :=
  le_antisymm (Finset.sup_le_iff.mpr fun _ h => hf (by simpa using h)) (le_sup (by simp))

variable [LocallyFiniteOrder α]

/--
theorem `Icc_subset_Iic_self` / 定理 `Icc_subset_Iic_self`

English:
theorem Icc_subset_Iic_self
  statement: Icc a b subseteq Iic b
  proof: by
  simpa [← coe_subset] using Set.Icc_subset_Iic_self

中文:
定理 Icc_subset_Iic_self
  结论: 闭区间 a b subseteq 左无界右闭区间 b
  证明: by
  simpa [← coe_subset] using Set.Icc_subset_Iic_self

Depends on / 依赖: Icc_subset_Iic_self, Set.Icc_subset_Iic_self, coe_subset
-/
theorem Icc_subset_Iic_self : Icc a b subseteq Iic b := by
  simpa [← coe_subset] using Set.Icc_subset_Iic_self

/--
theorem `Ioc_subset_Iic_self` / 定理 `Ioc_subset_Iic_self`

English:
theorem Ioc_subset_Iic_self
  statement: Ioc a b subseteq Iic b
  proof: by
  simpa [← coe_subset] using Set.Ioc_subset_Iic_self

中文:
定理 Ioc_subset_Iic_self
  结论: 左开右闭区间 a b subseteq 左无界右闭区间 b
  证明: by
  simpa [← coe_subset] using Set.Ioc_subset_Iic_self

Depends on / 依赖: Ioc_subset_Iic_self, Set.Ioc_subset_Iic_self, coe_subset
-/
theorem Ioc_subset_Iic_self : Ioc a b subseteq Iic b := by
  simpa [← coe_subset] using Set.Ioc_subset_Iic_self

/--
theorem `Ico_subset_Iio_self` / 定理 `Ico_subset_Iio_self`

English:
theorem Ico_subset_Iio_self
  statement: Ico a b subseteq Iio b
  proof: by
  simpa [← coe_subset] using Set.Ico_subset_Iio_self

中文:
定理 Ico_subset_Iio_self
  结论: 左闭右开区间 a b subseteq 左无界右开区间 b
  证明: by
  simpa [← coe_subset] using Set.Ico_subset_Iio_self

Depends on / 依赖: Ico_subset_Iio_self, Set.Ico_subset_Iio_self, coe_subset
-/
theorem Ico_subset_Iio_self : Ico a b subseteq Iio b := by
  simpa [← coe_subset] using Set.Ico_subset_Iio_self

/--
theorem `Ioo_subset_Iio_self` / 定理 `Ioo_subset_Iio_self`

English:
theorem Ioo_subset_Iio_self
  statement: Ioo a b subseteq Iio b
  proof: by
  simpa [← coe_subset] using Set.Ioo_subset_Iio_self

中文:
定理 Ioo_subset_Iio_self
  结论: 开区间 a b subseteq 左无界右开区间 b
  证明: by
  simpa [← coe_subset] using Set.Ioo_subset_Iio_self

Depends on / 依赖: Ioo_subset_Iio_self, Set.Ioo_subset_Iio_self, coe_subset
-/
theorem Ioo_subset_Iio_self : Ioo a b subseteq Iio b := by
  simpa [← coe_subset] using Set.Ioo_subset_Iio_self

/--
theorem `Ico_subset_Iic_self` / 定理 `Ico_subset_Iic_self`

English:
theorem Ico_subset_Iic_self
  statement: Ico a b subseteq Iic b
  proof: Ico_subset_Icc_self.trans Icc_subset_Iic_self

中文:
定理 Ico_subset_Iic_self
  结论: 左闭右开区间 a b subseteq 左无界右闭区间 b
  证明: Ico_subset_Icc_self.trans Icc_subset_Iic_self

Depends on / 依赖: Icc_subset_Iic_self, Ico_subset_Icc_self, Ico_subset_Icc_self.trans
-/
theorem Ico_subset_Iic_self : Ico a b subseteq Iic b :=
  Ico_subset_Icc_self.trans Icc_subset_Iic_self

/--
theorem `Ioo_subset_Iic_self` / 定理 `Ioo_subset_Iic_self`

English:
theorem Ioo_subset_Iic_self
  statement: Ioo a b subseteq Iic b
  proof: Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self

中文:
定理 Ioo_subset_Iic_self
  结论: 开区间 a b subseteq 左无界右闭区间 b
  证明: Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self

Depends on / 依赖: Ioc_subset_Iic_self, Ioo_subset_Ioc_self, Ioo_subset_Ioc_self.trans
-/
theorem Ioo_subset_Iic_self : Ioo a b subseteq Iic b :=
  Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self

/--
theorem `Iic_disjoint_Ioc` / 定理 `Iic_disjoint_Ioc`

English:
theorem Iic_disjoint_Ioc
  given: (h : a <= b)
  statement: Disjoint (Iic a) (Ioc b c)
  proof: disjoint_left.2 fun _ hax hbcx => (mem_Iic.1 hax).not_gt lt_of_le_of_lt h (mem_Ioc.1 hbcx).1

中文:
定理 Iic_disjoint_Ioc
  条件: (h : a <= b)
  结论: Disjoint (左无界右闭区间 a) (左开右闭区间 b c)
  证明: disjoint_left.2 fun _ hax hbcx => (mem_Iic.1 hax).not_gt lt_of_le_of_lt h (mem_Ioc.1 hbcx).1

Depends on / 依赖: disjoint_left, lt_of_le_of_lt, mem_Iic, mem_Ioc, not_gt
-/
theorem Iic_disjoint_Ioc (h : a <= b) : Disjoint (Iic a) (Ioc b c) :=
disjoint_left.2 fun _ hax hbcx => (mem_Iic.1 hax).not_gt lt_of_le_of_lt h (mem_Ioc.1 hbcx).1

/--
Definition of `_root_.Equiv.IicFinsetSet` / `_root_.Equiv.IicFinsetSet` 的定义

English:
definition _root_.Equiv.IicFinsetSet
  signature: (a : α)
  body: ⟨b.1, coe_Iic a ▸ mem_coe.2 b.2⟩
  invFun b := ⟨b.1, by rw [← mem_coe, coe_Iic a]; exact b.2⟩

中文:
定义 _root_.等价.IicFinsetSet
  签名: (a : α)
  定义体: ⟨b.1, coe_Iic a ▸ mem_coe.2 b.2⟩
  invFun b := ⟨b.1, by rw [← mem_coe, coe_Iic a]; exact b.2⟩

Depends on / 依赖: coe_Iic, mem_coe
-/
def _root_.Equiv.IicFinsetSet (a : α) : Iic a ≃ Set.Iic a where
  toFun b := ⟨b.1, coe_Iic a ▸ mem_coe.2 b.2⟩
  invFun b := ⟨b.1, by rw [← mem_coe, coe_Iic a]; exact b.2⟩

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a : α}

/--
theorem `Ioi_subset_Ici_self` / 定理 `Ioi_subset_Ici_self`

English:
theorem Ioi_subset_Ici_self
  statement: Ioi a subseteq Ici a
  proof: by
  simpa [← coe_subset] using Set.Ioi_subset_Ici_self

中文:
定理 Ioi_subset_Ici_self
  结论: 左开右无界区间 a subseteq 左闭右无界区间 a
  证明: by
  simpa [← coe_subset] using Set.Ioi_subset_Ici_self

Depends on / 依赖: Ioi_subset_Ici_self, LinearMap, LinearMap.inl, LinearMap.inr, LinearMap.span_inl_union_inr, Set.Ioi_subset_Ici_self, coe_subset, fg_def, span_inl_union_inr
-/
theorem Ioi_subset_Ici_self : Ioi a subseteq Ici a := by
  simpa [← coe_subset] using Set.Ioi_subset_Ici_self

/--
theorem `_root_.BddBelow.finite` / 定理 `_root_.BddBelow.finite`

English:
theorem _root_.BddBelow.finite
  given: {s : Set α} (hs : BddBelow s)
  statement: s.Finite
  proof: let ⟨a, ha⟩ := hs
(Ici a).finite_toSet.subset fun _ hx => mem_Ici.2 ha hx

中文:
定理 _root_.BddBelow.finite
  条件: {s : 集合 α} (hs : BddBelow s)
  结论: s.有限
  证明: let ⟨a, ha⟩ := hs
(Ici a).finite_toSet.subset fun _ hx => mem_Ici.2 ha hx

Depends on / 依赖: finite_toSet, finite_toSet.subset, mem_Ici, subset
-/
theorem _root_.BddBelow.finite {s : Set α} (hs : BddBelow s) : s.Finite :=
  let ⟨a, ha⟩ := hs
(Ici a).finite_toSet.subset fun _ hx => mem_Ici.2 ha hx

/--
theorem `_root_.Set.Infinite.not_bddBelow` / 定理 `_root_.Set.Infinite.not_bddBelow`

English:
theorem _root_.Set.Infinite.not_bddBelow
  given: {s : Set α}
  statement: s.Infinite -> ¬BddBelow s
  proof: mt BddBelow.finite

中文:
定理 _root_.集合.无限.not_bddBelow
  条件: {s : 集合 α}
  结论: s.无限 -> ¬BddBelow s
  证明: mt BddBelow.finite

Depends on / 依赖: BddBelow, BddBelow.finite, finite
-/
theorem _root_.Set.Infinite.not_bddBelow {s : Set α} : s.Infinite -> ¬BddBelow s :=
  mt BddBelow.finite

variable [Fintype α]

/--
theorem `filter_lt_eq_Ioi` / 定理 `filter_lt_eq_Ioi`

English:
theorem filter_lt_eq_Ioi
  given: [DecidablePred (a < ·)]
  statement: ({x | a < x} : Finset _) = Ioi a
  proof: by ext; simp

中文:
定理 filter_lt_eq_Ioi
  条件: [DecidablePred (a < ·)]
  结论: ({x | a < x} : 有限集 _) = 左开右无界区间 a
  证明: by ext; simp
-/
theorem filter_lt_eq_Ioi [DecidablePred (a < ·)] : ({x | a < x} : Finset _) = Ioi a := by ext; simp
/--
theorem `filter_le_eq_Ici` / 定理 `filter_le_eq_Ici`

English:
theorem filter_le_eq_Ici
  given: [DecidablePred (a <= ·)]
  statement: ({x | a <= x} : Finset _) = Ici a
  proof: by ext; simp

中文:
定理 filter_le_eq_Ici
  条件: [DecidablePred (a <= ·)]
  结论: ({x | a <= x} : 有限集 _) = 左闭右无界区间 a
  证明: by ext; simp
-/
theorem filter_le_eq_Ici [DecidablePred (a <= ·)] : ({x | a <= x} : Finset _) = Ici a := by ext; simp

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a : α}

/--
theorem `Iio_subset_Iic_self` / 定理 `Iio_subset_Iic_self`

English:
theorem Iio_subset_Iic_self
  statement: Iio a subseteq Iic a
  proof: by
  simpa [← coe_subset] using Set.Iio_subset_Iic_self

中文:
定理 Iio_subset_Iic_self
  结论: 左无界右开区间 a subseteq 左无界右闭区间 a
  证明: by
  simpa [← coe_subset] using Set.Iio_subset_Iic_self

Depends on / 依赖: Iio_subset_Iic_self, Set.Iio_subset_Iic_self, coe_subset
-/
theorem Iio_subset_Iic_self : Iio a subseteq Iic a := by
  simpa [← coe_subset] using Set.Iio_subset_Iic_self

/--
theorem `_root_.BddAbove.finite` / 定理 `_root_.BddAbove.finite`

English:
theorem _root_.BddAbove.finite
  given: {s : Set α} (hs : BddAbove s)
  statement: s.Finite
  proof: hs.dual.finite

中文:
定理 _root_.BddAbove.finite
  条件: {s : 集合 α} (hs : BddAbove s)
  结论: s.有限
  证明: hs.dual.finite

Depends on / 依赖: finite, hs.dual.finite
-/
theorem _root_.BddAbove.finite {s : Set α} (hs : BddAbove s) : s.Finite :=
  hs.dual.finite

/--
theorem `_root_.Set.Infinite.not_bddAbove` / 定理 `_root_.Set.Infinite.not_bddAbove`

English:
theorem _root_.Set.Infinite.not_bddAbove
  given: {s : Set α}
  statement: s.Infinite -> ¬BddAbove s
  proof: mt BddAbove.finite

中文:
定理 _root_.集合.无限.not_bddAbove
  条件: {s : 集合 α}
  结论: s.无限 -> ¬BddAbove s
  证明: mt BddAbove.finite

Depends on / 依赖: BddAbove, BddAbove.finite, finite
-/
theorem _root_.Set.Infinite.not_bddAbove {s : Set α} : s.Infinite -> ¬BddAbove s :=
  mt BddAbove.finite

variable [Fintype α]

/--
theorem `filter_gt_eq_Iio` / 定理 `filter_gt_eq_Iio`

English:
theorem filter_gt_eq_Iio
  given: [DecidablePred (· < a)]
  statement: ({x | x < a} : Finset _) = Iio a
  proof: by ext; simp

中文:
定理 filter_gt_eq_Iio
  条件: [DecidablePred (· < a)]
  结论: ({x | x < a} : 有限集 _) = 左无界右开区间 a
  证明: by ext; simp
-/
theorem filter_gt_eq_Iio [DecidablePred (· < a)] : ({x | x < a} : Finset _) = Iio a := by ext; simp
/--
theorem `filter_ge_eq_Iic` / 定理 `filter_ge_eq_Iic`

English:
theorem filter_ge_eq_Iic
  given: [DecidablePred (· <= a)]
  statement: ({x | x <= a} : Finset _) = Iic a
  proof: by ext; simp

中文:
定理 filter_ge_eq_Iic
  条件: [DecidablePred (· <= a)]
  结论: ({x | x <= a} : 有限集 _) = 左无界右闭区间 a
  证明: by ext; simp
-/
theorem filter_ge_eq_Iic [DecidablePred (· <= a)] : ({x | x <= a} : Finset _) = Iic a := by ext; simp

end LocallyFiniteOrderBot

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

@[simp]
/--
theorem `Icc_bot` / 定理 `Icc_bot`

English:
theorem Icc_bot
  given: [OrderBot α]
  statement: Icc (⊥ : α) a = Iic a
  proof: rfl

@[simp]

中文:
定理 Icc_bot
  条件: [有底序 α]
  结论: 闭区间 (⊥ : α) a = 左无界右闭区间 a
  证明: rfl

@[simp]
-/
theorem Icc_bot [OrderBot α] : Icc (⊥ : α) a = Iic a := rfl

@[simp]
/--
theorem `Icc_top` / 定理 `Icc_top`

English:
theorem Icc_top
  given: [OrderTop α]
  statement: Icc a (⊤ : α) = Ici a
  proof: rfl

@[simp]

中文:
定理 Icc_top
  条件: [有顶序 α]
  结论: 闭区间 a (⊤ : α) = 左闭右无界区间 a
  证明: rfl

@[simp]
-/
theorem Icc_top [OrderTop α] : Icc a (⊤ : α) = Ici a := rfl

@[simp]
/--
theorem `Ico_bot` / 定理 `Ico_bot`

English:
theorem Ico_bot
  given: [OrderBot α]
  statement: Ico (⊥ : α) a = Iio a
  proof: rfl

@[simp]

中文:
定理 Ico_bot
  条件: [有底序 α]
  结论: 左闭右开区间 (⊥ : α) a = 左无界右开区间 a
  证明: rfl

@[simp]
-/
theorem Ico_bot [OrderBot α] : Ico (⊥ : α) a = Iio a := rfl

@[simp]
/--
theorem `Ioc_top` / 定理 `Ioc_top`

English:
theorem Ioc_top
  given: [OrderTop α]
  statement: Ioc a (⊤ : α) = Ioi a
  proof: rfl

中文:
定理 Ioc_top
  条件: [有顶序 α]
  结论: 左开右闭区间 a (⊤ : α) = 左开右无界区间 a
  证明: rfl
-/
theorem Ioc_top [OrderTop α] : Ioc a (⊤ : α) = Ioi a := rfl

/--
theorem `Icc_bot_top` / 定理 `Icc_bot_top`

English:
theorem Icc_bot_top
  given: [BoundedOrder α] [Fintype α]
  statement: Icc (⊥ : α) (⊤ : α) = univ
  proof: by
  rw [Icc_bot]; rw [Iic_top]

中文:
定理 Icc_bot_top
  条件: [有界序 α] [有限类型 α]
  结论: 闭区间 (⊥ : α) (⊤ : α) = univ
  证明: by
  rw [Icc_bot]; rw [Iic_top]

Depends on / 依赖: Icc_bot, Iic_top
-/
theorem Icc_bot_top [BoundedOrder α] [Fintype α] : Icc (⊥ : α) (⊤ : α) = univ := by
  rw [Icc_bot]; rw [Iic_top]

end LocallyFiniteOrder

variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

/--
theorem `disjoint_Ioi_Iio` / 定理 `disjoint_Ioi_Iio`

English:
theorem disjoint_Ioi_Iio
  given: (a : α)
  statement: Disjoint (Ioi a) (Iio a)
  proof: disjoint_left.2 fun _ hab hba => (mem_Ioi.1 hab).not_gt mem_Iio.1 hba

中文:
定理 disjoint_Ioi_Iio
  条件: (a : α)
  结论: Disjoint (左开右无界区间 a) (左无界右开区间 a)
  证明: disjoint_left.2 fun _ hab hba => (mem_Ioi.1 hab).not_gt mem_Iio.1 hba

Depends on / 依赖: disjoint_left, mem_Iio, mem_Ioi, not_gt
-/
theorem disjoint_Ioi_Iio (a : α) : Disjoint (Ioi a) (Iio a) :=
disjoint_left.2 fun _ hab hba => (mem_Ioi.1 hab).not_gt mem_Iio.1 hba

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b c : α}

@[simp]
/--
theorem `Icc_self` / 定理 `Icc_self`

English:
theorem Icc_self
  given: (a : α)
  statement: Icc a a = {a}
  proof: by rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]

@[simp]

中文:
定理 Icc_self
  条件: (a : α)
  结论: 闭区间 a a = {a}
  证明: by rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]

@[simp]

Depends on / 依赖: Icc_self, Set.Icc_self, coe_Icc, coe_eq_singleton
-/
theorem Icc_self (a : α) : Icc a a = {a} := by rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]

@[simp]
/--
theorem `Icc_eq_singleton_iff` / 定理 `Icc_eq_singleton_iff`

English:
theorem Icc_eq_singleton_iff
  statement: Icc a b = {c} ↔ a = c ∧ b = c
  proof: by
  rw [← coe_eq_singleton]; rw [coe_Icc]; rw [Set.Icc_eq_singleton_iff]

中文:
定理 Icc_eq_singleton_iff
  结论: 闭区间 a b = {c} ↔ a = c ∧ b = c
  证明: by
  rw [← coe_eq_singleton]; rw [coe_Icc]; rw [Set.Icc_eq_singleton_iff]

Depends on / 依赖: Icc_eq_singleton_iff, Set.Icc_eq_singleton_iff, coe_Icc, coe_eq_singleton
-/
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  rw [← coe_eq_singleton]; rw [coe_Icc]; rw [Set.Icc_eq_singleton_iff]

/--
theorem `Ico_disjoint_Ico_consecutive` / 定理 `Ico_disjoint_Ico_consecutive`

English:
theorem Ico_disjoint_Ico_consecutive
  given: (a b c : α)
  statement: Disjoint (Ico a b) (Ico b c)
  proof: disjoint_left.2 fun _ hab hbc => (mem_Ico.mp hab).2.not_ge (mem_Ico.mp hbc).1

@[simp]

中文:
定理 Ico_disjoint_Ico_consecutive
  条件: (a b c : α)
  结论: Disjoint (左闭右开区间 a b) (左闭右开区间 b c)
  证明: disjoint_left.2 fun _ hab hbc => (mem_Ico.mp hab).2.not_ge (mem_Ico.mp hbc).1

@[simp]

Depends on / 依赖: disjoint_left, mem_Ico, mem_Ico.mp, not_ge
-/
theorem Ico_disjoint_Ico_consecutive (a b c : α) : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.2 fun _ hab hbc => (mem_Ico.mp hab).2.not_ge (mem_Ico.mp hbc).1

@[simp]
/--
theorem `Ici_top` / 定理 `Ici_top`

English:
theorem Ici_top
  given: [OrderTop α]
  statement: Ici (⊤ : α) = {⊤}
  proof: Icc_eq_singleton_iff.2 ⟨rfl, rfl⟩

@[simp]

中文:
定理 Ici_top
  条件: [有顶序 α]
  结论: 左闭右无界区间 (⊤ : α) = {⊤}
  证明: Icc_eq_singleton_iff.2 ⟨rfl, rfl⟩

@[simp]

Depends on / 依赖: Icc_eq_singleton_iff
-/
theorem Ici_top [OrderTop α] : Ici (⊤ : α) = {⊤} := Icc_eq_singleton_iff.2 ⟨rfl, rfl⟩

@[simp]
/--
theorem `Iic_bot` / 定理 `Iic_bot`

English:
theorem Iic_bot
  given: [OrderBot α]
  statement: Iic (⊥ : α) = {⊥}
  proof: Icc_eq_singleton_iff.2 ⟨rfl, rfl⟩

中文:
定理 Iic_bot
  条件: [有底序 α]
  结论: 左无界右闭区间 (⊥ : α) = {⊥}
  证明: Icc_eq_singleton_iff.2 ⟨rfl, rfl⟩

Depends on / 依赖: Icc_eq_singleton_iff
-/
theorem Iic_bot [OrderBot α] : Iic (⊥ : α) = {⊥} := Icc_eq_singleton_iff.2 ⟨rfl, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OrderBot
  signature: α] : Unique (Iic (⊥ : α))
  body: by
  rw [Iic_bot]
  infer_instance

中文:
实例 [有底序
  签名: α] : 唯一 (左无界右闭区间 (⊥ : α))
  定义体: by
  rw [Iic_bot]
  infer_instance

Depends on / 依赖: Iic_bot, infer_instance
-/
instance [OrderBot α] : Unique (Iic (⊥ : α)) := by
  rw [Iic_bot]
  infer_instance

section DecidableEq

variable [DecidableEq α]

@[simp]
/--
theorem `Icc_erase_left` / 定理 `Icc_erase_left`

English:
theorem Icc_erase_left
  given: (a b : α)
  statement: (Icc a b).erase a = Ioc a b
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 Icc_erase_left
  条件: (a b : α)
  结论: (闭区间 a b).erase a = 左开右闭区间 a b
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj, hm.map
-/
theorem Icc_erase_left (a b : α) : (Icc a b).erase a = Ioc a b := by simp [← coe_inj]

@[simp]
/--
theorem `Icc_erase_right` / 定理 `Icc_erase_right`

English:
theorem Icc_erase_right
  given: (a b : α)
  statement: (Icc a b).erase b = Ico a b
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 Icc_erase_right
  条件: (a b : α)
  结论: (闭区间 a b).erase b = 左闭右开区间 a b
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: Nat.recOn, coe_inj, ih.mul, one_eq_span, pow_succ
-/
theorem Icc_erase_right (a b : α) : (Icc a b).erase b = Ico a b := by simp [← coe_inj]

@[simp]
/--
theorem `Ico_erase_left` / 定理 `Ico_erase_left`

English:
theorem Ico_erase_left
  given: (a b : α)
  statement: (Ico a b).erase a = Ioo a b
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 Ico_erase_left
  条件: (a b : α)
  结论: (左闭右开区间 a b).erase a = 开区间 a b
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem Ico_erase_left (a b : α) : (Ico a b).erase a = Ioo a b := by simp [← coe_inj]

@[simp]
/--
theorem `Ioc_erase_right` / 定理 `Ioc_erase_right`

English:
theorem Ioc_erase_right
  given: (a b : α)
  statement: (Ioc a b).erase b = Ioo a b
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 Ioc_erase_right
  条件: (a b : α)
  结论: (左开右闭区间 a b).erase b = 开区间 a b
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem Ioc_erase_right (a b : α) : (Ioc a b).erase b = Ioo a b := by simp [← coe_inj]

@[simp]
/--
theorem `Icc_sdiff_both` / 定理 `Icc_sdiff_both`

English:
theorem Icc_sdiff_both
  given: (a b : α)
  statement: Icc a b \ {a, b} = Ioo a b
  proof: by simp [← coe_inj]

@[deprecated (since := "2026-06-03")] alias Icc_diff_both := Icc_sdiff_both

@[simp]

中文:
定理 Icc_sdiff_both
  条件: (a b : α)
  结论: 闭区间 a b \ {a, b} = 开区间 a b
  证明: by simp [← coe_inj]

@[deprecated (since := "2026-06-03")] alias Icc_diff_both := Icc_sdiff_both

@[simp]

Depends on / 依赖: coe_inj
-/
theorem Icc_sdiff_both (a b : α) : Icc a b \ {a, b} = Ioo a b := by simp [← coe_inj]

@[deprecated (since := "2026-06-03")] alias Icc_diff_both := Icc_sdiff_both

@[simp]
/--
theorem `Ico_insert_right` / 定理 `Ico_insert_right`

English:
theorem Ico_insert_right
  given: (h : a <= b)
  statement: insert b (Ico a b) = Icc a b
  proof: by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Icc]; rw [coe_Ico]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ico_union_right h]

@[simp]

中文:
定理 Ico_insert_right
  条件: (h : a <= b)
  结论: insert b (左闭右开区间 a b) = 闭区间 a b
  证明: by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Icc]; rw [coe_Ico]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ico_union_right h]

@[simp]

Depends on / 依赖: Ico_union_right, Set.Ico_union_right, Set.insert_eq, Set.union_comm, coe_Icc, coe_Ico, coe_inj, coe_insert, insert_eq, union_comm
-/
theorem Ico_insert_right (h : a <= b) : insert b (Ico a b) = Icc a b := by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Icc]; rw [coe_Ico]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ico_union_right h]

@[simp]
/--
theorem `Ioc_insert_left` / 定理 `Ioc_insert_left`

English:
theorem Ioc_insert_left
  given: (h : a <= b)
  statement: insert a (Ioc a b) = Icc a b
  proof: by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Ioc]; rw [coe_Icc]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ioc_union_left h]

@[simp]

中文:
定理 Ioc_insert_left
  条件: (h : a <= b)
  结论: insert a (左开右闭区间 a b) = 闭区间 a b
  证明: by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Ioc]; rw [coe_Icc]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ioc_union_left h]

@[simp]

Depends on / 依赖: Ioc_union_left, Set.Ioc_union_left, Set.insert_eq, Set.union_comm, coe_Icc, coe_Ioc, coe_inj, coe_insert, insert_eq, union_comm
-/
theorem Ioc_insert_left (h : a <= b) : insert a (Ioc a b) = Icc a b := by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Ioc]; rw [coe_Icc]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ioc_union_left h]

@[simp]
/--
theorem `Ioo_insert_left` / 定理 `Ioo_insert_left`

English:
theorem Ioo_insert_left
  given: (h : a < b)
  statement: insert a (Ioo a b) = Ico a b
  proof: by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Ioo]; rw [coe_Ico]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ioo_union_left h]

@[simp]

中文:
定理 Ioo_insert_left
  条件: (h : a < b)
  结论: insert a (开区间 a b) = 左闭右开区间 a b
  证明: by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Ioo]; rw [coe_Ico]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ioo_union_left h]

@[simp]

Depends on / 依赖: Ioo_union_left, Set.Ioo_union_left, Set.insert_eq, Set.union_comm, coe_Ico, coe_Ioo, coe_inj, coe_insert, insert_eq, union_comm
-/
theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Ioo]; rw [coe_Ico]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ioo_union_left h]

@[simp]
/--
theorem `Ioo_insert_right` / 定理 `Ioo_insert_right`

English:
theorem Ioo_insert_right
  given: (h : a < b)
  statement: insert b (Ioo a b) = Ioc a b
  proof: by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Ioo]; rw [coe_Ioc]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ioo_union_right h]

@[simp]

中文:
定理 Ioo_insert_right
  条件: (h : a < b)
  结论: insert b (开区间 a b) = 左开右闭区间 a b
  证明: by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Ioo]; rw [coe_Ioc]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ioo_union_right h]

@[simp]

Depends on / 依赖: Ioo_union_right, Set.Ioo_union_right, Set.insert_eq, Set.union_comm, coe_Ioc, coe_Ioo, coe_inj, coe_insert, insert_eq, union_comm
-/
theorem Ioo_insert_right (h : a < b) : insert b (Ioo a b) = Ioc a b := by
  rw [← coe_inj]; rw [coe_insert]; rw [coe_Ioo]; rw [coe_Ioc]; rw [Set.insert_eq]; rw [Set.union_comm]; rw [Set.Ioo_union_right h]

@[simp]
/--
theorem `Icc_sdiff_Ico_self` / 定理 `Icc_sdiff_Ico_self`

English:
theorem Icc_sdiff_Ico_self
  given: (h : a <= b)
  statement: Icc a b \ Ico a b = {b}
  proof: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ico_self := Icc_sdiff_Ico_self

@[simp]

中文:
定理 Icc_sdiff_Ico_self
  条件: (h : a <= b)
  结论: 闭区间 a b \ 左闭右开区间 a b = {b}
  证明: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ico_self := Icc_sdiff_Ico_self

@[simp]

Depends on / 依赖: coe_inj
-/
theorem Icc_sdiff_Ico_self (h : a <= b) : Icc a b \ Ico a b = {b} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ico_self := Icc_sdiff_Ico_self

@[simp]
/--
theorem `Icc_sdiff_Ioc_self` / 定理 `Icc_sdiff_Ioc_self`

English:
theorem Icc_sdiff_Ioc_self
  given: (h : a <= b)
  statement: Icc a b \ Ioc a b = {a}
  proof: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioc_self := Icc_sdiff_Ioc_self

@[simp]

中文:
定理 Icc_sdiff_Ioc_self
  条件: (h : a <= b)
  结论: 闭区间 a b \ 左开右闭区间 a b = {a}
  证明: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioc_self := Icc_sdiff_Ioc_self

@[simp]

Depends on / 依赖: coe_inj
-/
theorem Icc_sdiff_Ioc_self (h : a <= b) : Icc a b \ Ioc a b = {a} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioc_self := Icc_sdiff_Ioc_self

@[simp]
/--
theorem `Icc_sdiff_Ioo_self` / 定理 `Icc_sdiff_Ioo_self`

English:
theorem Icc_sdiff_Ioo_self
  given: (h : a <= b)
  statement: Icc a b \ Ioo a b = {a, b}
  proof: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioo_self := Icc_sdiff_Ioo_self

@[simp]

中文:
定理 Icc_sdiff_Ioo_self
  条件: (h : a <= b)
  结论: 闭区间 a b \ 开区间 a b = {a, b}
  证明: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioo_self := Icc_sdiff_Ioo_self

@[simp]

Depends on / 依赖: coe_inj
-/
theorem Icc_sdiff_Ioo_self (h : a <= b) : Icc a b \ Ioo a b = {a, b} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioo_self := Icc_sdiff_Ioo_self

@[simp]
/--
theorem `Ico_sdiff_Ioo_self` / 定理 `Ico_sdiff_Ioo_self`

English:
theorem Ico_sdiff_Ioo_self
  given: (h : a < b)
  statement: Ico a b \ Ioo a b = {a}
  proof: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ioo_self := Ico_sdiff_Ioo_self

@[simp]

中文:
定理 Ico_sdiff_Ioo_self
  条件: (h : a < b)
  结论: 左闭右开区间 a b \ 开区间 a b = {a}
  证明: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ioo_self := Ico_sdiff_Ioo_self

@[simp]

Depends on / 依赖: coe_inj
-/
theorem Ico_sdiff_Ioo_self (h : a < b) : Ico a b \ Ioo a b = {a} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ioo_self := Ico_sdiff_Ioo_self

@[simp]
/--
theorem `Ioc_sdiff_Ioo_self` / 定理 `Ioc_sdiff_Ioo_self`

English:
theorem Ioc_sdiff_Ioo_self
  given: (h : a < b)
  statement: Ioc a b \ Ioo a b = {b}
  proof: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Ioo_self := Ioc_sdiff_Ioo_self

@[simp]

中文:
定理 Ioc_sdiff_Ioo_self
  条件: (h : a < b)
  结论: 左开右闭区间 a b \ 开区间 a b = {b}
  证明: by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Ioo_self := Ioc_sdiff_Ioo_self

@[simp]

Depends on / 依赖: coe_inj
-/
theorem Ioc_sdiff_Ioo_self (h : a < b) : Ioc a b \ Ioo a b = {b} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Ioo_self := Ioc_sdiff_Ioo_self

@[simp]
/--
theorem `Ico_inter_Ico_consecutive` / 定理 `Ico_inter_Ico_consecutive`

English:
theorem Ico_inter_Ico_consecutive
  given: (a b c : α)
  statement: Ico a b inter Ico b c = ∅
  proof: (Ico_disjoint_Ico_consecutive a b c).eq_bot

中文:
定理 Ico_inter_Ico_consecutive
  条件: (a b c : α)
  结论: 左闭右开区间 a b inter 左闭右开区间 b c = ∅
  证明: (Ico_disjoint_Ico_consecutive a b c).eq_bot

Depends on / 依赖: Ico_disjoint_Ico_consecutive, eq_bot
-/
theorem Ico_inter_Ico_consecutive (a b c : α) : Ico a b inter Ico b c = ∅ :=
  (Ico_disjoint_Ico_consecutive a b c).eq_bot

end DecidableEq

-- Those lemmas are purposefully the other way around

/--
theorem `Icc_eq_cons_Ico` / 定理 `Icc_eq_cons_Ico`

English:
theorem Icc_eq_cons_Ico
  given: (h : a <= b)
  statement: Icc a b = (Ico a b).cons b right_notMem_Ico
  proof: by
  classical rw [cons_eq_insert, Ico_insert_right h]

中文:
定理 Icc_eq_cons_Ico
  条件: (h : a <= b)
  结论: 闭区间 a b = (左闭右开区间 a b).cons b right_notMem_Ico
  证明: by
  classical rw [cons_eq_insert, Ico_insert_right h]

Depends on / 依赖: Ico_insert_right, classical, cons_eq_insert
-/
theorem Icc_eq_cons_Ico (h : a <= b) : Icc a b = (Ico a b).cons b right_notMem_Ico := by
  classical rw [cons_eq_insert, Ico_insert_right h]

/--
theorem `Icc_eq_cons_Ioc` / 定理 `Icc_eq_cons_Ioc`

English:
theorem Icc_eq_cons_Ioc
  given: (h : a <= b)
  statement: Icc a b = (Ioc a b).cons a left_notMem_Ioc
  proof: by
  classical rw [cons_eq_insert, Ioc_insert_left h]

中文:
定理 Icc_eq_cons_Ioc
  条件: (h : a <= b)
  结论: 闭区间 a b = (左开右闭区间 a b).cons a left_notMem_Ioc
  证明: by
  classical rw [cons_eq_insert, Ioc_insert_left h]

Depends on / 依赖: Ioc_insert_left, classical, cons_eq_insert
-/
theorem Icc_eq_cons_Ioc (h : a <= b) : Icc a b = (Ioc a b).cons a left_notMem_Ioc := by
  classical rw [cons_eq_insert, Ioc_insert_left h]

/--
theorem `Ioc_eq_cons_Ioo` / 定理 `Ioc_eq_cons_Ioo`

English:
theorem Ioc_eq_cons_Ioo
  given: (h : a < b)
  statement: Ioc a b = (Ioo a b).cons b right_notMem_Ioo
  proof: by
  classical rw [cons_eq_insert, Ioo_insert_right h]

中文:
定理 Ioc_eq_cons_Ioo
  条件: (h : a < b)
  结论: 左开右闭区间 a b = (开区间 a b).cons b right_notMem_Ioo
  证明: by
  classical rw [cons_eq_insert, Ioo_insert_right h]

Depends on / 依赖: Ioo_insert_right, classical, cons_eq_insert
-/
theorem Ioc_eq_cons_Ioo (h : a < b) : Ioc a b = (Ioo a b).cons b right_notMem_Ioo := by
  classical rw [cons_eq_insert, Ioo_insert_right h]

/--
theorem `Ico_eq_cons_Ioo` / 定理 `Ico_eq_cons_Ioo`

English:
theorem Ico_eq_cons_Ioo
  given: (h : a < b)
  statement: Ico a b = (Ioo a b).cons a left_notMem_Ioo
  proof: by
  classical rw [cons_eq_insert, Ioo_insert_left h]

中文:
定理 Ico_eq_cons_Ioo
  条件: (h : a < b)
  结论: 左闭右开区间 a b = (开区间 a b).cons a left_notMem_Ioo
  证明: by
  classical rw [cons_eq_insert, Ioo_insert_left h]

Depends on / 依赖: Ioo_insert_left, classical, cons_eq_insert
-/
theorem Ico_eq_cons_Ioo (h : a < b) : Ico a b = (Ioo a b).cons a left_notMem_Ioo := by
  classical rw [cons_eq_insert, Ioo_insert_left h]

/--
theorem `Ico_filter_le_left` / 定理 `Ico_filter_le_left`

English:
theorem Ico_filter_le_left
  given: {a b : α} [DecidablePred (· <= a)] (hab : a < b)
  proof: by
  grind

中文:
定理 Ico_filter_le_left
  条件: {a b : α} [DecidablePred (· <= a)] (hab : a < b)
  证明: by
  grind
-/
theorem Ico_filter_le_left {a b : α} [DecidablePred (· <= a)] (hab : a < b) :
    {x in Ico a b | x <= a} = {a} := by
  grind

/--
theorem `card_Ico_eq_card_Icc_sub_one` / 定理 `card_Ico_eq_card_Icc_sub_one`

English:
theorem card_Ico_eq_card_Icc_sub_one
  given: (a b : α)
  statement: #(Ico a b) = #(Icc a b) - 1
  proof: by
  by_cases h : a <= b
  · rw [Icc_eq_cons_Ico h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, Nat.zero_sub]

中文:
定理 card_Ico_eq_card_Icc_sub_one
  条件: (a b : α)
  结论: #(左闭右开区间 a b) = #(闭区间 a b) - 1
  证明: by
  by_cases h : a <= b
  · rw [Icc_eq_cons_Ico h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, Nat.zero_sub]

Depends on / 依赖: Icc_eq_cons_Ico, Icc_eq_empty, Ico_eq_empty, Nat.add_sub_cancel, Nat.zero_sub, add_sub_cancel, card_cons, card_empty, zero_sub
-/
theorem card_Ico_eq_card_Icc_sub_one (a b : α) : #(Ico a b) = #(Icc a b) - 1 := by
  by_cases h : a <= b
  · rw [Icc_eq_cons_Ico h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, Nat.zero_sub]

/--
theorem `card_Ioc_eq_card_Icc_sub_one` / 定理 `card_Ioc_eq_card_Icc_sub_one`

English:
theorem card_Ioc_eq_card_Icc_sub_one
  given: (a b : α)
  statement: #(Ioc a b) = #(Icc a b) - 1
  proof: @card_Ico_eq_card_Icc_sub_one αᵒᵈ _ _ _ _

中文:
定理 card_Ioc_eq_card_Icc_sub_one
  条件: (a b : α)
  结论: #(左开右闭区间 a b) = #(闭区间 a b) - 1
  证明: @card_Ico_eq_card_Icc_sub_one αᵒᵈ _ _ _ _

Depends on / 依赖: card_Ico_eq_card_Icc_sub_one
-/
theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : #(Ioc a b) = #(Icc a b) - 1 :=
  @card_Ico_eq_card_Icc_sub_one αᵒᵈ _ _ _ _

/--
theorem `card_Ioo_eq_card_Ico_sub_one` / 定理 `card_Ioo_eq_card_Ico_sub_one`

English:
theorem card_Ioo_eq_card_Ico_sub_one
  given: (a b : α)
  statement: #(Ioo a b) = #(Ico a b) - 1
  proof: by
  by_cases h : a < b
  · rw [Ico_eq_cons_Ioo h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ioo_eq_empty h, Ico_eq_empty h, card_empty, Nat.zero_sub]

中文:
定理 card_Ioo_eq_card_Ico_sub_one
  条件: (a b : α)
  结论: #(开区间 a b) = #(左闭右开区间 a b) - 1
  证明: by
  by_cases h : a < b
  · rw [Ico_eq_cons_Ioo h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ioo_eq_empty h, Ico_eq_empty h, card_empty, Nat.zero_sub]

Depends on / 依赖: Ico_eq_cons_Ioo, Ico_eq_empty, Ioo_eq_empty, Nat.add_sub_cancel, Nat.zero_sub, add_sub_cancel, card_cons, card_empty, zero_sub
-/
theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : #(Ioo a b) = #(Ico a b) - 1 := by
  by_cases h : a < b
  · rw [Ico_eq_cons_Ioo h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ioo_eq_empty h, Ico_eq_empty h, card_empty, Nat.zero_sub]

/--
theorem `card_Ioo_eq_card_Ioc_sub_one` / 定理 `card_Ioo_eq_card_Ioc_sub_one`

English:
theorem card_Ioo_eq_card_Ioc_sub_one
  given: (a b : α)
  statement: #(Ioo a b) = #(Ioc a b) - 1
  proof: @card_Ioo_eq_card_Ico_sub_one αᵒᵈ _ _ _ _

中文:
定理 card_Ioo_eq_card_Ioc_sub_one
  条件: (a b : α)
  结论: #(开区间 a b) = #(左开右闭区间 a b) - 1
  证明: @card_Ioo_eq_card_Ico_sub_one αᵒᵈ _ _ _ _

Depends on / 依赖: card_Ioo_eq_card_Ico_sub_one
-/
theorem card_Ioo_eq_card_Ioc_sub_one (a b : α) : #(Ioo a b) = #(Ioc a b) - 1 :=
  @card_Ioo_eq_card_Ico_sub_one αᵒᵈ _ _ _ _

/--
theorem `card_Ioo_eq_card_Icc_sub_two` / 定理 `card_Ioo_eq_card_Icc_sub_two`

English:
theorem card_Ioo_eq_card_Icc_sub_two
  given: (a b : α)
  statement: #(Ioo a b) = #(Icc a b) - 2
  proof: by
  rw [card_Ioo_eq_card_Ico_sub_one]; rw [card_Ico_eq_card_Icc_sub_one]
  rfl

中文:
定理 card_Ioo_eq_card_Icc_sub_two
  条件: (a b : α)
  结论: #(开区间 a b) = #(闭区间 a b) - 2
  证明: by
  rw [card_Ioo_eq_card_Ico_sub_one]; rw [card_Ico_eq_card_Icc_sub_one]
  rfl

Depends on / 依赖: card_Ico_eq_card_Icc_sub_one, card_Ioo_eq_card_Ico_sub_one
-/
theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : #(Ioo a b) = #(Icc a b) - 2 := by
  rw [card_Ioo_eq_card_Ico_sub_one]; rw [card_Ico_eq_card_Icc_sub_one]
  rfl

end PartialOrder

section Prod

variable {β : Type*}

section sectL

/--
lemma `uIcc_map_sectL` / 引理 `uIcc_map_sectL`

English:
lemma uIcc_map_sectL
  statement: [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  proof: by
  aesop (add safe forward [le_antisymm])

中文:
引理 uIcc_map_sectL
  结论: [格 α] [格 β] [局部有限序 α] [局部有限序 β]
  证明: by
  aesop (add safe forward [le_antisymm])

Depends on / 依赖: forward, le_antisymm
-/
lemma uIcc_map_sectL [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableLE (α × β)] (a b : α) (c : β) :
    (uIcc a b).map (.sectL _ c) = uIcc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm])

variable [Preorder α] [PartialOrder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableLE (α × β)] (a b : α) (c : β)

/--
lemma `Icc_map_sectL` / 引理 `Icc_map_sectL`

English:
lemma Icc_map_sectL
  statement: (Icc a b).map (.sectL _ c) = Icc (a, c) (b, c)
  proof: by
  aesop (add safe forward [le_antisymm])

中文:
引理 Icc_map_sectL
  结论: (闭区间 a b).map (.sectL _ c) = 闭区间 (a, c) (b, c)
  证明: by
  aesop (add safe forward [le_antisymm])

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.rTensor_tensor, Function, Function.Injective, I.injective_subtype, I.subtype, I.subtype.rTensor, Injective, RestrictScalars, RestrictScalars.moduleOrig, Submodule, forward, injective_subtype, le_antisymm, moduleOrig, rTensor, rTensor_preserves_injective_linearMap, rTensor_tensor, restrictScalars, subtype
-/
lemma Icc_map_sectL : (Icc a b).map (.sectL _ c) = Icc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm])

/--
lemma `Ioc_map_sectL` / 引理 `Ioc_map_sectL`

English:
lemma Ioc_map_sectL
  statement: (Ioc a b).map (.sectL _ c) = Ioc (a, c) (b, c)
  proof: by
  aesop (add safe forward [le_antisymm, le_of_lt])

中文:
引理 Ioc_map_sectL
  结论: (左开右闭区间 a b).map (.sectL _ c) = 左开右闭区间 (a, c) (b, c)
  证明: by
  aesop (add safe forward [le_antisymm, le_of_lt])

Depends on / 依赖: forward, le_antisymm, le_of_lt
-/
lemma Ioc_map_sectL : (Ioc a b).map (.sectL _ c) = Ioc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

/--
lemma `Ico_map_sectL` / 引理 `Ico_map_sectL`

English:
lemma Ico_map_sectL
  statement: (Ico a b).map (.sectL _ c) = Ico (a, c) (b, c)
  proof: by
  aesop (add safe forward [le_antisymm, le_of_lt])

中文:
引理 Ico_map_sectL
  结论: (左闭右开区间 a b).map (.sectL _ c) = 左闭右开区间 (a, c) (b, c)
  证明: by
  aesop (add safe forward [le_antisymm, le_of_lt])

Depends on / 依赖: forward, le_antisymm, le_of_lt
-/
lemma Ico_map_sectL : (Ico a b).map (.sectL _ c) = Ico (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

/--
lemma `Ioo_map_sectL` / 引理 `Ioo_map_sectL`

English:
lemma Ioo_map_sectL
  statement: (Ioo a b).map (.sectL _ c) = Ioo (a, c) (b, c)
  proof: by
  aesop (add safe forward [le_antisymm, le_of_lt])

中文:
引理 Ioo_map_sectL
  结论: (开区间 a b).map (.sectL _ c) = 开区间 (a, c) (b, c)
  证明: by
  aesop (add safe forward [le_antisymm, le_of_lt])

Depends on / 依赖: forward, le_antisymm, le_of_lt
-/
lemma Ioo_map_sectL : (Ioo a b).map (.sectL _ c) = Ioo (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

end sectL

section sectR

/--
lemma `uIcc_map_sectR` / 引理 `uIcc_map_sectR`

English:
lemma uIcc_map_sectR
  statement: [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  proof: by
  aesop (add safe forward [le_antisymm])

中文:
引理 uIcc_map_sectR
  结论: [格 α] [格 β] [局部有限序 α] [局部有限序 β]
  证明: by
  aesop (add safe forward [le_antisymm])

Depends on / 依赖: forward, le_antisymm
-/
lemma uIcc_map_sectR [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableLE (α × β)] (c : α) (a b : β) :
    (uIcc a b).map (.sectR c _) = uIcc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm])

variable [PartialOrder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableLE (α × β)] (c : α) (a b : β)

/--
lemma `Icc_map_sectR` / 引理 `Icc_map_sectR`

English:
lemma Icc_map_sectR
  statement: (Icc a b).map (.sectR c _) = Icc (c, a) (c, b)
  proof: by
  aesop (add safe forward [le_antisymm])

中文:
引理 Icc_map_sectR
  结论: (闭区间 a b).map (.sectR c _) = 闭区间 (c, a) (c, b)
  证明: by
  aesop (add safe forward [le_antisymm])

Depends on / 依赖: forward, le_antisymm
-/
lemma Icc_map_sectR : (Icc a b).map (.sectR c _) = Icc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm])

/--
lemma `Ioc_map_sectR` / 引理 `Ioc_map_sectR`

English:
lemma Ioc_map_sectR
  statement: (Ioc a b).map (.sectR c _) = Ioc (c, a) (c, b)
  proof: by
  aesop (add safe forward [le_antisymm, le_of_lt])

中文:
引理 Ioc_map_sectR
  结论: (左开右闭区间 a b).map (.sectR c _) = 左开右闭区间 (c, a) (c, b)
  证明: by
  aesop (add safe forward [le_antisymm, le_of_lt])

Depends on / 依赖: forward, le_antisymm, le_of_lt
-/
lemma Ioc_map_sectR : (Ioc a b).map (.sectR c _) = Ioc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

/--
lemma `Ico_map_sectR` / 引理 `Ico_map_sectR`

English:
lemma Ico_map_sectR
  statement: (Ico a b).map (.sectR c _) = Ico (c, a) (c, b)
  proof: by
  aesop (add safe forward [le_antisymm, le_of_lt])

中文:
引理 Ico_map_sectR
  结论: (左闭右开区间 a b).map (.sectR c _) = 左闭右开区间 (c, a) (c, b)
  证明: by
  aesop (add safe forward [le_antisymm, le_of_lt])

Depends on / 依赖: forward, le_antisymm, le_of_lt
-/
lemma Ico_map_sectR : (Ico a b).map (.sectR c _) = Ico (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

/--
lemma `Ioo_map_sectR` / 引理 `Ioo_map_sectR`

English:
lemma Ioo_map_sectR
  statement: (Ioo a b).map (.sectR c _) = Ioo (c, a) (c, b)
  proof: by
  aesop (add safe forward [le_antisymm, le_of_lt])

中文:
引理 Ioo_map_sectR
  结论: (开区间 a b).map (.sectR c _) = 开区间 (c, a) (c, b)
  证明: by
  aesop (add safe forward [le_antisymm, le_of_lt])

Depends on / 依赖: forward, le_antisymm, le_of_lt
-/
lemma Ioo_map_sectR : (Ioo a b).map (.sectR c _) = Ioo (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

end sectR

end Prod

section BoundedPartialOrder

variable [PartialOrder α]

section OrderTop

variable [LocallyFiniteOrderTop α]

@[simp]
/--
theorem `Ici_erase` / 定理 `Ici_erase`

English:
theorem Ici_erase
  given: [DecidableEq α] (a : α)
  statement: (Ici a).erase a = Ioi a
  proof: by
  ext
  simp_rw [Finset.mem_erase, mem_Ici, mem_Ioi, lt_iff_le_and_ne, and_comm, ne_comm]

@[simp]

中文:
定理 Ici_erase
  条件: [DecidableEq α] (a : α)
  结论: (左闭右无界区间 a).erase a = 左开右无界区间 a
  证明: by
  ext
  simp_rw [Finset.mem_erase, mem_Ici, mem_Ioi, lt_iff_le_and_ne, and_comm, ne_comm]

@[simp]

Depends on / 依赖: Finset, Finset.mem_erase, and_comm, lt_iff_le_and_ne, mem_Ici, mem_Ioi, mem_erase, ne_comm, simp_rw
-/
theorem Ici_erase [DecidableEq α] (a : α) : (Ici a).erase a = Ioi a := by
  ext
  simp_rw [Finset.mem_erase, mem_Ici, mem_Ioi, lt_iff_le_and_ne, and_comm, ne_comm]

@[simp]
/--
theorem `Ioi_insert` / 定理 `Ioi_insert`

English:
theorem Ioi_insert
  given: [DecidableEq α] (a : α)
  statement: insert a (Ioi a) = Ici a
  proof: by
  ext
  simp_rw [Finset.mem_insert, mem_Ici, mem_Ioi, le_iff_lt_or_eq, or_comm, eq_comm]

中文:
定理 Ioi_insert
  条件: [DecidableEq α] (a : α)
  结论: insert a (左开右无界区间 a) = 左闭右无界区间 a
  证明: by
  ext
  simp_rw [Finset.mem_insert, mem_Ici, mem_Ioi, le_iff_lt_or_eq, or_comm, eq_comm]

Depends on / 依赖: Finset, Finset.mem_insert, eq_comm, le_iff_lt_or_eq, mem_Ici, mem_Ioi, mem_insert, or_comm, simp_rw
-/
theorem Ioi_insert [DecidableEq α] (a : α) : insert a (Ioi a) = Ici a := by
  ext
  simp_rw [Finset.mem_insert, mem_Ici, mem_Ioi, le_iff_lt_or_eq, or_comm, eq_comm]

/--
theorem `notMem_Ioi_self` / 定理 `notMem_Ioi_self`

English:
theorem notMem_Ioi_self
  given: {b : α}
  statement: b ∉ Ioi b
  proof: fun h => lt_irrefl _ (mem_Ioi.1 h)

中文:
定理 notMem_Ioi_self
  条件: {b : α}
  结论: b ∉ 左开右无界区间 b
  证明: fun h => lt_irrefl _ (mem_Ioi.1 h)

Depends on / 依赖: lt_irrefl, mem_Ioi
-/
theorem notMem_Ioi_self {b : α} : b ∉ Ioi b := fun h => lt_irrefl _ (mem_Ioi.1 h)

-- Purposefully written the other way around
/--
theorem `Ici_eq_cons_Ioi` / 定理 `Ici_eq_cons_Ioi`

English:
theorem Ici_eq_cons_Ioi
  given: (a : α)
  statement: Ici a = (Ioi a).cons a notMem_Ioi_self
  proof: by
  classical rw [cons_eq_insert, Ioi_insert]

中文:
定理 Ici_eq_cons_Ioi
  条件: (a : α)
  结论: 左闭右无界区间 a = (左开右无界区间 a).cons a notMem_Ioi_self
  证明: by
  classical rw [cons_eq_insert, Ioi_insert]

Depends on / 依赖: Ioi_insert, classical, cons_eq_insert
-/
theorem Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a notMem_Ioi_self := by
  classical rw [cons_eq_insert, Ioi_insert]

/--
theorem `card_Ioi_eq_card_Ici_sub_one` / 定理 `card_Ioi_eq_card_Ici_sub_one`

English:
theorem card_Ioi_eq_card_Ici_sub_one
  given: (a : α)
  statement: #(Ioi a) = #(Ici a) - 1
  proof: by
  rw [Ici_eq_cons_Ioi]; rw [card_cons]; rw [Nat.add_sub_cancel_right]

中文:
定理 card_Ioi_eq_card_Ici_sub_one
  条件: (a : α)
  结论: #(左开右无界区间 a) = #(左闭右无界区间 a) - 1
  证明: by
  rw [Ici_eq_cons_Ioi]; rw [card_cons]; rw [Nat.add_sub_cancel_right]

Depends on / 依赖: Ici_eq_cons_Ioi, Nat.add_sub_cancel_right, add_sub_cancel_right, card_cons
-/
theorem card_Ioi_eq_card_Ici_sub_one (a : α) : #(Ioi a) = #(Ici a) - 1 := by
  rw [Ici_eq_cons_Ioi]; rw [card_cons]; rw [Nat.add_sub_cancel_right]

end OrderTop

section OrderBot

variable [LocallyFiniteOrderBot α]

@[simp]
/--
theorem `Iic_erase` / 定理 `Iic_erase`

English:
theorem Iic_erase
  given: [DecidableEq α] (b : α)
  statement: (Iic b).erase b = Iio b
  proof: by
  ext
  simp_rw [Finset.mem_erase, mem_Iic, mem_Iio, lt_iff_le_and_ne, and_comm]

@[simp]

中文:
定理 Iic_erase
  条件: [DecidableEq α] (b : α)
  结论: (左无界右闭区间 b).erase b = 左无界右开区间 b
  证明: by
  ext
  simp_rw [Finset.mem_erase, mem_Iic, mem_Iio, lt_iff_le_and_ne, and_comm]

@[simp]

Depends on / 依赖: Finset, Finset.mem_erase, and_comm, lt_iff_le_and_ne, mem_Iic, mem_Iio, mem_erase, simp_rw
-/
theorem Iic_erase [DecidableEq α] (b : α) : (Iic b).erase b = Iio b := by
  ext
  simp_rw [Finset.mem_erase, mem_Iic, mem_Iio, lt_iff_le_and_ne, and_comm]

@[simp]
/--
theorem `Iio_insert` / 定理 `Iio_insert`

English:
theorem Iio_insert
  given: [DecidableEq α] (b : α)
  statement: insert b (Iio b) = Iic b
  proof: by
  ext
  simp_rw [Finset.mem_insert, mem_Iic, mem_Iio, le_iff_lt_or_eq, or_comm]

中文:
定理 Iio_insert
  条件: [DecidableEq α] (b : α)
  结论: insert b (左无界右开区间 b) = 左无界右闭区间 b
  证明: by
  ext
  simp_rw [Finset.mem_insert, mem_Iic, mem_Iio, le_iff_lt_or_eq, or_comm]

Depends on / 依赖: Finset, Finset.mem_insert, le_iff_lt_or_eq, mem_Iic, mem_Iio, mem_insert, or_comm, simp_rw
-/
theorem Iio_insert [DecidableEq α] (b : α) : insert b (Iio b) = Iic b := by
  ext
  simp_rw [Finset.mem_insert, mem_Iic, mem_Iio, le_iff_lt_or_eq, or_comm]

/--
theorem `notMem_Iio_self` / 定理 `notMem_Iio_self`

English:
theorem notMem_Iio_self
  given: {b : α}
  statement: b ∉ Iio b
  proof: fun h => lt_irrefl _ (mem_Iio.1 h)

中文:
定理 notMem_Iio_self
  条件: {b : α}
  结论: b ∉ 左无界右开区间 b
  证明: fun h => lt_irrefl _ (mem_Iio.1 h)

Depends on / 依赖: lt_irrefl, mem_Iio
-/
theorem notMem_Iio_self {b : α} : b ∉ Iio b := fun h => lt_irrefl _ (mem_Iio.1 h)

-- Purposefully written the other way around
/--
theorem `Iic_eq_cons_Iio` / 定理 `Iic_eq_cons_Iio`

English:
theorem Iic_eq_cons_Iio
  given: (b : α)
  statement: Iic b = (Iio b).cons b notMem_Iio_self
  proof: by
  classical rw [cons_eq_insert, Iio_insert]

中文:
定理 Iic_eq_cons_Iio
  条件: (b : α)
  结论: 左无界右闭区间 b = (左无界右开区间 b).cons b notMem_Iio_self
  证明: by
  classical rw [cons_eq_insert, Iio_insert]

Depends on / 依赖: Iio_insert, classical, cons_eq_insert
-/
theorem Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b notMem_Iio_self := by
  classical rw [cons_eq_insert, Iio_insert]

/--
theorem `card_Iio_eq_card_Iic_sub_one` / 定理 `card_Iio_eq_card_Iic_sub_one`

English:
theorem card_Iio_eq_card_Iic_sub_one
  given: (a : α)
  statement: #(Iio a) = #(Iic a) - 1
  proof: by
  rw [Iic_eq_cons_Iio]; rw [card_cons]; rw [Nat.add_sub_cancel_right]

中文:
定理 card_Iio_eq_card_Iic_sub_one
  条件: (a : α)
  结论: #(左无界右开区间 a) = #(左无界右闭区间 a) - 1
  证明: by
  rw [Iic_eq_cons_Iio]; rw [card_cons]; rw [Nat.add_sub_cancel_right]

Depends on / 依赖: Iic_eq_cons_Iio, Nat.add_sub_cancel_right, add_sub_cancel_right, card_cons
-/
theorem card_Iio_eq_card_Iic_sub_one (a : α) : #(Iio a) = #(Iic a) - 1 := by
  rw [Iic_eq_cons_Iio]; rw [card_cons]; rw [Nat.add_sub_cancel_right]

end OrderBot

end BoundedPartialOrder

section SemilatticeSup
variable [SemilatticeSup α] [LocallyFiniteOrderBot α]

-- TODO: Why does `id_eq` simplify the LHS here but not the LHS of `Finset.sup_Iic`?
/--
lemma `sup'_Iic` / 引理 `sup'_Iic`

English:
lemma sup'_Iic
  given: (a : α)
  statement: (Iic a).sup' nonempty_Iic id = a
  proof: le_antisymm (sup'_le _ _ fun _ => mem_Iic.1) le_sup' (f := id) mem_Iic.2 le_refl a

中文:
引理 上确界'_Iic
  条件: (a : α)
  结论: (左无界右闭区间 a).上确界' nonempty_Iic id = a
  证明: le_antisymm (sup'_le _ _ fun _ => mem_Iic.1) le_sup' (f := id) mem_Iic.2 le_refl a
-/
lemma sup'_Iic (a : α) : (Iic a).sup' nonempty_Iic id = a :=
le_antisymm (sup'_le _ _ fun _ => mem_Iic.1) le_sup' (f := id) mem_Iic.2 le_refl a

/--
lemma `sup_Iic` / 引理 `sup_Iic`

English:
lemma sup_Iic
  given: [OrderBot α] (a : α)
  statement: (Iic a).sup id = a
  proof: le_antisymm (Finset.sup_le fun _ => mem_Iic.1) le_sup (f := id) mem_Iic.2 le_refl a

中文:
引理 sup_Iic
  条件: [有底序 α] (a : α)
  结论: (左无界右闭区间 a).上确界 id = a
  证明: le_antisymm (Finset.sup_le fun _ => mem_Iic.1) le_sup (f := id) mem_Iic.2 le_refl a
-/
@[simp] lemma sup_Iic [OrderBot α] (a : α) : (Iic a).sup id = a :=
le_antisymm (Finset.sup_le fun _ => mem_Iic.1) le_sup (f := id) mem_Iic.2 le_refl a

/--
lemma `image_subset_Iic_sup` / 引理 `image_subset_Iic_sup`

English:
lemma image_subset_Iic_sup
  given: [OrderBot α] [DecidableEq α] (f : ι -> α) (s : Finset ι)
  proof: by
  refine fun i hi => mem_Iic.2 ?_
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hi
  exact le_sup hj

中文:
引理 image_subset_Iic_sup
  条件: [有底序 α] [DecidableEq α] (f : ι -> α) (s : 有限集 ι)
  证明: by
  refine fun i hi => mem_Iic.2 ?_
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hi
  exact le_sup hj

Depends on / 依赖: le_sup, mem_Iic, mem_image
-/
lemma image_subset_Iic_sup [OrderBot α] [DecidableEq α] (f : ι -> α) (s : Finset ι) :
    s.image f subseteq Iic (s.sup f) := by
  refine fun i hi => mem_Iic.2 ?_
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hi
  exact le_sup hj

/--
lemma `subset_Iic_sup_id` / 引理 `subset_Iic_sup_id`

English:
lemma subset_Iic_sup_id
  given: [OrderBot α] (s : Finset α)
  statement: s subseteq Iic (s.sup id)
  proof: fun _ h => mem_Iic.2 le_sup (f := id) h

中文:
引理 subset_Iic_sup_id
  条件: [有底序 α] (s : 有限集 α)
  结论: s subseteq 左无界右闭区间 (s.上确界 id)
  证明: fun _ h => mem_Iic.2 le_sup (f := id) h

Depends on / 依赖: le_sup, mem_Iic
-/
lemma subset_Iic_sup_id [OrderBot α] (s : Finset α) : s subseteq Iic (s.sup id) :=
fun _ h => mem_Iic.2 le_sup (f := id) h

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [LocallyFiniteOrderTop α]

/--
lemma `inf'_Ici` / 引理 `inf'_Ici`

English:
lemma inf'_Ici
  given: (a : α)
  statement: (Ici a).inf' nonempty_Ici id = a
  proof: ge_antisymm (le_inf' _ _ fun _ => mem_Ici.1) inf'_le (f := id) mem_Ici.2 le_refl a

中文:
引理 下确界'_Ici
  条件: (a : α)
  结论: (左闭右无界区间 a).下确界' nonempty_Ici id = a
  证明: ge_antisymm (le_inf' _ _ fun _ => mem_Ici.1) inf'_le (f := id) mem_Ici.2 le_refl a
-/
lemma inf'_Ici (a : α) : (Ici a).inf' nonempty_Ici id = a :=
ge_antisymm (le_inf' _ _ fun _ => mem_Ici.1) inf'_le (f := id) mem_Ici.2 le_refl a

/--
lemma `inf_Ici` / 引理 `inf_Ici`

English:
lemma inf_Ici
  given: [OrderTop α] (a : α)
  statement: (Ici a).inf id = a
  proof: le_antisymm (inf_le (f := id) <| mem_Ici.2 <| le_refl a) Finset.le_inf fun _ => mem_Ici.1

中文:
引理 inf_Ici
  条件: [有顶序 α] (a : α)
  结论: (左闭右无界区间 a).下确界 id = a
  证明: le_antisymm (inf_le (f := id) <| mem_Ici.2 <| le_refl a) Finset.le_inf fun _ => mem_Ici.1
-/
@[simp] lemma inf_Ici [OrderTop α] (a : α) : (Ici a).inf id = a :=
le_antisymm (inf_le (f := id) <| mem_Ici.2 <| le_refl a) Finset.le_inf fun _ => mem_Ici.1

end SemilatticeInf

section LinearOrder

variable [LinearOrder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

/--
theorem `Ico_subset_Ico_iff` / 定理 `Ico_subset_Ico_iff`

English:
theorem Ico_subset_Ico_iff
  given: {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁)
  proof: by
  rw [← coe_subset]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_subset_Ico_iff h]

中文:
定理 Ico_subset_Ico_iff
  条件: {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁)
  证明: by
  rw [← coe_subset]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_subset_Ico_iff h]

Depends on / 依赖: Ico_subset_Ico_iff, Set.Ico_subset_Ico_iff, coe_Ico, coe_subset
-/
theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂ := by
  rw [← coe_subset]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_subset_Ico_iff h]

/--
theorem `Ico_union_Ico_eq_Ico` / 定理 `Ico_union_Ico_eq_Ico`

English:
theorem Ico_union_Ico_eq_Ico
  given: {a b c : α} (hab : a <= b) (hbc : b <= c)
  proof: by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_union_Ico_eq_Ico hab hbc]

@[simp]

中文:
定理 Ico_union_Ico_eq_Ico
  条件: {a b c : α} (hab : a <= b) (hbc : b <= c)
  证明: by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_union_Ico_eq_Ico hab hbc]

@[simp]

Depends on / 依赖: Ico_union_Ico_eq_Ico, Set.Ico_union_Ico_eq_Ico, coe_Ico, coe_inj, coe_union
-/
theorem Ico_union_Ico_eq_Ico {a b c : α} (hab : a <= b) (hbc : b <= c) :
    Ico a b union Ico b c = Ico a c := by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_union_Ico_eq_Ico hab hbc]

@[simp]
/--
theorem `Ioc_union_Ioc_eq_Ioc` / 定理 `Ioc_union_Ioc_eq_Ioc`

English:
theorem Ioc_union_Ioc_eq_Ioc
  given: {a b c : α} (h₁ : a <= b) (h₂ : b <= c)
  proof: by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ioc]; rw [coe_Ioc]; rw [coe_Ioc]; rw [Set.Ioc_union_Ioc_eq_Ioc h₁ h₂]

中文:
定理 Ioc_union_Ioc_eq_Ioc
  条件: {a b c : α} (h₁ : a <= b) (h₂ : b <= c)
  证明: by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ioc]; rw [coe_Ioc]; rw [coe_Ioc]; rw [Set.Ioc_union_Ioc_eq_Ioc h₁ h₂]

Depends on / 依赖: Ioc_union_Ioc_eq_Ioc, Set.Ioc_union_Ioc_eq_Ioc, coe_Ioc, coe_inj, coe_union
-/
theorem Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a <= b) (h₂ : b <= c) :
    Ioc a b union Ioc b c = Ioc a c := by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ioc]; rw [coe_Ioc]; rw [coe_Ioc]; rw [Set.Ioc_union_Ioc_eq_Ioc h₁ h₂]

/--
theorem `Ico_subset_Ico_union_Ico` / 定理 `Ico_subset_Ico_union_Ico`

English:
theorem Ico_subset_Ico_union_Ico
  given: {a b c : α}
  statement: Ico a c subseteq Ico a b union Ico b c
  proof: by
  rw [← coe_subset]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]
  exact Set.Ico_subset_Ico_union_Ico

中文:
定理 Ico_subset_Ico_union_Ico
  条件: {a b c : α}
  结论: 左闭右开区间 a c subseteq 左闭右开区间 a b union 左闭右开区间 b c
  证明: by
  rw [← coe_subset]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]
  exact Set.Ico_subset_Ico_union_Ico

Depends on / 依赖: Ico_subset_Ico_union_Ico, Set.Ico_subset_Ico_union_Ico, coe_Ico, coe_subset, coe_union
-/
theorem Ico_subset_Ico_union_Ico {a b c : α} : Ico a c subseteq Ico a b union Ico b c := by
  rw [← coe_subset]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]
  exact Set.Ico_subset_Ico_union_Ico

/--
theorem `Ico_union_Ico` / 定理 `Ico_union_Ico`

English:
theorem Ico_union_Ico
  given: {a b c d : α} (h₁ : min a b <= max c d) (h₂ : min c d <= max a b)
  proof: by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_union_Ico h₁ h₂]

中文:
定理 Ico_union_Ico
  条件: {a b c d : α} (h₁ : 最小值 a b <= 最大值 c d) (h₂ : 最小值 c d <= 最大值 a b)
  证明: by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_union_Ico h₁ h₂]

Depends on / 依赖: Ico_union_Ico, Set.Ico_union_Ico, coe_Ico, coe_inj, coe_union
-/
theorem Ico_union_Ico {a b c d : α} (h₁ : min a b <= max c d) (h₂ : min c d <= max a b) :
    Ico a b union Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_union_Ico h₁ h₂]

/--
theorem `Ico_union_Ico'` / 定理 `Ico_union_Ico'`

English:
theorem Ico_union_Ico'
  given: {a b c d : α} (hcb : c <= b) (had : a <= d)
  proof: by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_union_Ico' hcb had]

中文:
定理 Ico_union_Ico'
  条件: {a b c d : α} (hcb : c <= b) (had : a <= d)
  证明: by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_union_Ico' hcb had]

Depends on / 依赖: Ico_union_Ico, Set.Ico_union_Ico, coe_Ico, coe_inj, coe_union
-/
theorem Ico_union_Ico' {a b c d : α} (hcb : c <= b) (had : a <= d) :
    Ico a b union Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj]; rw [coe_union]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_union_Ico' hcb had]

/--
theorem `Ico_inter_Ico` / 定理 `Ico_inter_Ico`

English:
theorem Ico_inter_Ico
  given: {a b c d : α}
  statement: Ico a b inter Ico c d = Ico (max a c) (min b d)
  proof: by
  rw [← coe_inj]; rw [coe_inter]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_inter_Ico]

中文:
定理 Ico_inter_Ico
  条件: {a b c d : α}
  结论: 左闭右开区间 a b inter 左闭右开区间 c d = 左闭右开区间 (最大值 a c) (最小值 b d)
  证明: by
  rw [← coe_inj]; rw [coe_inter]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_inter_Ico]

Depends on / 依赖: Ico_inter_Ico, Set.Ico_inter_Ico, coe_Ico, coe_inj, coe_inter
-/
theorem Ico_inter_Ico {a b c d : α} : Ico a b inter Ico c d = Ico (max a c) (min b d) := by
  rw [← coe_inj]; rw [coe_inter]; rw [coe_Ico]; rw [coe_Ico]; rw [coe_Ico]; rw [Set.Ico_inter_Ico]

/--
theorem `Ioc_inter_Ioc` / 定理 `Ioc_inter_Ioc`

English:
theorem Ioc_inter_Ioc
  given: {a b c d : α}
  statement: Ioc a b inter Ioc c d = Ioc (max a c) (min b d)
  proof: by grind

@[simp]

中文:
定理 Ioc_inter_Ioc
  条件: {a b c d : α}
  结论: 左开右闭区间 a b inter 左开右闭区间 c d = 左开右闭区间 (最大值 a c) (最小值 b d)
  证明: by grind

@[simp]
-/
theorem Ioc_inter_Ioc {a b c d : α} : Ioc a b inter Ioc c d = Ioc (max a c) (min b d) := by grind

@[simp]
/--
theorem `Ico_filter_lt` / 定理 `Ico_filter_lt`

English:
theorem Ico_filter_lt
  given: (a b c : α)
  statement: {x in Ico a b | x < c} = Ico a (min b c)
  proof: by grind

@[simp]

中文:
定理 Ico_filter_lt
  条件: (a b c : α)
  结论: {x in 左闭右开区间 a b | x < c} = 左闭右开区间 a (最小值 b c)
  证明: by grind

@[simp]
-/
theorem Ico_filter_lt (a b c : α) : {x in Ico a b | x < c} = Ico a (min b c) := by grind

@[simp]
/--
theorem `Ico_filter_le` / 定理 `Ico_filter_le`

English:
theorem Ico_filter_le
  given: (a b c : α)
  statement: {x in Ico a b | c <= x} = Ico (max a c) b
  proof: by grind

@[simp]

中文:
定理 Ico_filter_le
  条件: (a b c : α)
  结论: {x in 左闭右开区间 a b | c <= x} = 左闭右开区间 (最大值 a c) b
  证明: by grind

@[simp]
-/
theorem Ico_filter_le (a b c : α) : {x in Ico a b | c <= x} = Ico (max a c) b := by grind

@[simp]
/--
theorem `Ioo_filter_lt` / 定理 `Ioo_filter_lt`

English:
theorem Ioo_filter_lt
  given: (a b c : α)
  statement: {x in Ioo a b | x < c} = Ioo a (min b c)
  proof: by grind

@[simp]

中文:
定理 Ioo_filter_lt
  条件: (a b c : α)
  结论: {x in 开区间 a b | x < c} = 开区间 a (最小值 b c)
  证明: by grind

@[simp]
-/
theorem Ioo_filter_lt (a b c : α) : {x in Ioo a b | x < c} = Ioo a (min b c) := by grind

@[simp]
/--
theorem `Iio_filter_lt` / 定理 `Iio_filter_lt`

English:
theorem Iio_filter_lt
  given: {α} [LinearOrder α] [LocallyFiniteOrderBot α] (a b : α)
  proof: by grind

@[simp]

中文:
定理 Iio_filter_lt
  条件: {α} [线性序 α] [LocallyFiniteOrderBot α] (a b : α)
  证明: by grind

@[simp]
-/
theorem Iio_filter_lt {α} [LinearOrder α] [LocallyFiniteOrderBot α] (a b : α) :
    {x in Iio a | x < b} = Iio (min a b) := by grind

@[simp]
/--
theorem `Ico_sdiff_Ico_left` / 定理 `Ico_sdiff_Ico_left`

English:
theorem Ico_sdiff_Ico_left
  given: (a b c : α)
  statement: Ico a b \ Ico a c = Ico (max a c) b
  proof: by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_left := Ico_sdiff_Ico_left

@[simp]

中文:
定理 Ico_sdiff_Ico_left
  条件: (a b c : α)
  结论: 左闭右开区间 a b \ 左闭右开区间 a c = 左闭右开区间 (最大值 a c) b
  证明: by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_left := Ico_sdiff_Ico_left

@[simp]
-/
theorem Ico_sdiff_Ico_left (a b c : α) : Ico a b \ Ico a c = Ico (max a c) b := by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_left := Ico_sdiff_Ico_left

@[simp]
/--
theorem `Ico_sdiff_Ico_right` / 定理 `Ico_sdiff_Ico_right`

English:
theorem Ico_sdiff_Ico_right
  given: (a b c : α)
  statement: Ico a b \ Ico c b = Ico a (min b c)
  proof: by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_right := Ico_sdiff_Ico_right

@[simp]

中文:
定理 Ico_sdiff_Ico_right
  条件: (a b c : α)
  结论: 左闭右开区间 a b \ 左闭右开区间 c b = 左闭右开区间 a (最小值 b c)
  证明: by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_right := Ico_sdiff_Ico_right

@[simp]
-/
theorem Ico_sdiff_Ico_right (a b c : α) : Ico a b \ Ico c b = Ico a (min b c) := by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_right := Ico_sdiff_Ico_right

@[simp]
/--
theorem `Ioc_disjoint_Ioc` / 定理 `Ioc_disjoint_Ioc`

English:
theorem Ioc_disjoint_Ioc
  statement: Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ <= max a₁ b₁
  proof: by
  simp_rw [disjoint_iff_inter_eq_empty, Ioc_inter_Ioc, Ioc_eq_empty_iff, not_lt]

中文:
定理 Ioc_disjoint_Ioc
  结论: Disjoint (左开右闭区间 a₁ a₂) (左开右闭区间 b₁ b₂) ↔ 最小值 a₂ b₂ <= 最大值 a₁ b₁
  证明: by
  simp_rw [disjoint_iff_inter_eq_empty, Ioc_inter_Ioc, Ioc_eq_empty_iff, not_lt]

Depends on / 依赖: Ioc_eq_empty_iff, Ioc_inter_Ioc, disjoint_iff_inter_eq_empty, not_lt, simp_rw
-/
theorem Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ <= max a₁ b₁ := by
  simp_rw [disjoint_iff_inter_eq_empty, Ioc_inter_Ioc, Ioc_eq_empty_iff, not_lt]

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

/--
theorem `Iic_sdiff_Ioc` / 定理 `Iic_sdiff_Ioc`

English:
theorem Iic_sdiff_Ioc
  statement: Iic b \ Ioc a b = Iic (a ⊓ b)
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc := Iic_sdiff_Ioc

中文:
定理 Iic_sdiff_Ioc
  结论: 左无界右闭区间 b \ 左开右闭区间 a b = 左无界右闭区间 (a ⊓ b)
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc := Iic_sdiff_Ioc
-/
theorem Iic_sdiff_Ioc : Iic b \ Ioc a b = Iic (a ⊓ b) := by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc := Iic_sdiff_Ioc

/--
theorem `Iic_sdiff_Ioc_self_of_le` / 定理 `Iic_sdiff_Ioc_self_of_le`

English:
theorem Iic_sdiff_Ioc_self_of_le
  given: (hab : a <= b)
  statement: Iic b \ Ioc a b = Iic a
  proof: by
  rw [Iic_sdiff_Ioc]; rw [min_eq_left hab]

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc_self_of_le := Iic_sdiff_Ioc_self_of_le

中文:
定理 Iic_sdiff_Ioc_self_of_le
  条件: (hab : a <= b)
  结论: 左无界右闭区间 b \ 左开右闭区间 a b = 左无界右闭区间 a
  证明: by
  rw [Iic_sdiff_Ioc]; rw [min_eq_left hab]

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc_self_of_le := Iic_sdiff_Ioc_self_of_le

Depends on / 依赖: Iic_sdiff_Ioc, min_eq_left
-/
theorem Iic_sdiff_Ioc_self_of_le (hab : a <= b) : Iic b \ Ioc a b = Iic a := by
  rw [Iic_sdiff_Ioc]; rw [min_eq_left hab]

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc_self_of_le := Iic_sdiff_Ioc_self_of_le

/--
theorem `Iic_union_Ioc_eq_Iic` / 定理 `Iic_union_Ioc_eq_Iic`

English:
theorem Iic_union_Ioc_eq_Iic
  given: (h : a <= b)
  statement: Iic a union Ioc a b = Iic b
  proof: by
  grind

中文:
定理 Iic_union_Ioc_eq_Iic
  条件: (h : a <= b)
  结论: 左无界右闭区间 a union 左开右闭区间 a b = 左无界右闭区间 b
  证明: by
  grind
-/
theorem Iic_union_Ioc_eq_Iic (h : a <= b) : Iic a union Ioc a b = Iic b := by
  grind

end LocallyFiniteOrderBot

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α] {s : Set α}

/--
theorem `_root_.Set.Infinite.exists_gt` / 定理 `_root_.Set.Infinite.exists_gt`

English:
theorem _root_.Set.Infinite.exists_gt
  given: (hs : s.Infinite)
  statement: forall a, exists b in s, a < b
  proof: not_bddAbove_iff.1 hs.not_bddAbove

中文:
定理 _root_.集合.无限.存在_gt
  条件: (hs : s.无限)
  结论: 对任意 a, 存在 b in s, a < b
  证明: not_bddAbove_iff.1 hs.not_bddAbove

Depends on / 依赖: hs.not_bddAbove, not_bddAbove, not_bddAbove_iff
-/
theorem _root_.Set.Infinite.exists_gt (hs : s.Infinite) : forall a, exists b in s, a < b :=
  not_bddAbove_iff.1 hs.not_bddAbove

/--
theorem `_root_.Set.infinite_iff_exists_gt` / 定理 `_root_.Set.infinite_iff_exists_gt`

English:
theorem _root_.Set.infinite_iff_exists_gt
  given: [Nonempty α]
  statement: s.Infinite ↔ forall a, exists b in s, a < b
  proof: ⟨Set.Infinite.exists_gt, Set.infinite_of_forall_exists_gt⟩

中文:
定理 _root_.集合.infinite_iff_存在_gt
  条件: [非空 α]
  结论: s.无限 ↔ 对任意 a, 存在 b in s, a < b
  证明: ⟨Set.Infinite.exists_gt, Set.infinite_of_forall_exists_gt⟩

Depends on / 依赖: Infinite, Set.Infinite.exists_gt, Set.infinite_of_forall_exists_gt, exists_gt, infinite_of_forall_exists_gt
-/
theorem _root_.Set.infinite_iff_exists_gt [Nonempty α] : s.Infinite ↔ forall a, exists b in s, a < b :=
  ⟨Set.Infinite.exists_gt, Set.infinite_of_forall_exists_gt⟩

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α] {s : Set α}

/--
theorem `_root_.Set.Infinite.exists_lt` / 定理 `_root_.Set.Infinite.exists_lt`

English:
theorem _root_.Set.Infinite.exists_lt
  given: (hs : s.Infinite)
  statement: forall a, exists b in s, b < a
  proof: not_bddBelow_iff.1 hs.not_bddBelow

中文:
定理 _root_.集合.无限.存在_lt
  条件: (hs : s.无限)
  结论: 对任意 a, 存在 b in s, b < a
  证明: not_bddBelow_iff.1 hs.not_bddBelow

Depends on / 依赖: hs.not_bddBelow, not_bddBelow, not_bddBelow_iff
-/
theorem _root_.Set.Infinite.exists_lt (hs : s.Infinite) : forall a, exists b in s, b < a :=
  not_bddBelow_iff.1 hs.not_bddBelow

/--
theorem `_root_.Set.infinite_iff_exists_lt` / 定理 `_root_.Set.infinite_iff_exists_lt`

English:
theorem _root_.Set.infinite_iff_exists_lt
  given: [Nonempty α]
  statement: s.Infinite ↔ forall a, exists b in s, b < a
  proof: ⟨Set.Infinite.exists_lt, Set.infinite_of_forall_exists_lt⟩

中文:
定理 _root_.集合.infinite_iff_存在_lt
  条件: [非空 α]
  结论: s.无限 ↔ 对任意 a, 存在 b in s, b < a
  证明: ⟨Set.Infinite.exists_lt, Set.infinite_of_forall_exists_lt⟩

Depends on / 依赖: Infinite, Set.Infinite.exists_lt, Set.infinite_of_forall_exists_lt, exists_lt, infinite_of_forall_exists_lt
-/
theorem _root_.Set.infinite_iff_exists_lt [Nonempty α] : s.Infinite ↔ forall a, exists b in s, b < a :=
  ⟨Set.Infinite.exists_lt, Set.infinite_of_forall_exists_lt⟩

end LocallyFiniteOrderTop

variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

/--
theorem `Ioi_disjUnion_Iio` / 定理 `Ioi_disjUnion_Iio`

English:
theorem Ioi_disjUnion_Iio
  given: (a : α)
  proof: by
  ext
  simp [eq_comm]

中文:
定理 Ioi_disjUnion_Iio
  条件: (a : α)
  证明: by
  ext
  simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem Ioi_disjUnion_Iio (a : α) :
    (Ioi a).disjUnion (Iio a) (disjoint_Ioi_Iio a) = ({a} : Finset α)ᶜ := by
  ext
  simp [eq_comm]

end LinearOrder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ x : α}

/--
theorem `uIcc_toDual` / 定理 `uIcc_toDual`

English:
theorem uIcc_toDual
  given: (a b : α)
  statement: [[toDual a, toDual b]] = [[a, b]].map toDual.toEmbedding
  proof: Icc_toDual (a ⊔ b) (a ⊓ b)

@[simp]

中文:
定理 uIcc_toDual
  条件: (a b : α)
  结论: [[toDual a, toDual b]] = [[a, b]].map toDual.toEmbedding
  证明: Icc_toDual (a ⊔ b) (a ⊓ b)

@[simp]

Depends on / 依赖: Icc_toDual
-/
theorem uIcc_toDual (a b : α) : [[toDual a, toDual b]] = [[a, b]].map toDual.toEmbedding :=
  Icc_toDual (a ⊔ b) (a ⊓ b)

@[simp]
/--
theorem `uIcc_of_le` / 定理 `uIcc_of_le`

English:
theorem uIcc_of_le
  given: (h : a <= b)
  statement: [[a, b]] = Icc a b
  proof: by
  rw [uIcc]; rw [inf_eq_left.2 h]; rw [sup_eq_right.2 h]

@[simp]

中文:
定理 uIcc_of_le
  条件: (h : a <= b)
  结论: [[a, b]] = 闭区间 a b
  证明: by
  rw [uIcc]; rw [inf_eq_left.2 h]; rw [sup_eq_right.2 h]

@[simp]

Depends on / 依赖: inf_eq_left, sup_eq_right
-/
theorem uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b := by
  rw [uIcc]; rw [inf_eq_left.2 h]; rw [sup_eq_right.2 h]

@[simp]
/--
theorem `uIcc_of_ge` / 定理 `uIcc_of_ge`

English:
theorem uIcc_of_ge
  given: (h : b <= a)
  statement: [[a, b]] = Icc b a
  proof: by
  rw [uIcc]; rw [inf_eq_right.2 h]; rw [sup_eq_left.2 h]

中文:
定理 uIcc_of_ge
  条件: (h : b <= a)
  结论: [[a, b]] = 闭区间 b a
  证明: by
  rw [uIcc]; rw [inf_eq_right.2 h]; rw [sup_eq_left.2 h]

Depends on / 依赖: inf_eq_right, sup_eq_left
-/
theorem uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a := by
  rw [uIcc]; rw [inf_eq_right.2 h]; rw [sup_eq_left.2 h]

/--
theorem `uIcc_comm` / 定理 `uIcc_comm`

English:
theorem uIcc_comm
  given: (a b : α)
  statement: [[a, b]] = [[b, a]]
  proof: by
  rw [uIcc]; rw [uIcc]; rw [inf_comm]; rw [sup_comm]

中文:
定理 uIcc_comm
  条件: (a b : α)
  结论: [[a, b]] = [[b, a]]
  证明: by
  rw [uIcc]; rw [uIcc]; rw [inf_comm]; rw [sup_comm]

Depends on / 依赖: inf_comm, sup_comm
-/
theorem uIcc_comm (a b : α) : [[a, b]] = [[b, a]] := by
  rw [uIcc]; rw [uIcc]; rw [inf_comm]; rw [sup_comm]

/--
theorem `uIcc_self` / 定理 `uIcc_self`

English:
theorem uIcc_self
  statement: [[a, a]] = {a}
  proof: by simp [uIcc]

@[simp]

中文:
定理 uIcc_self
  结论: [[a, a]] = {a}
  证明: by simp [uIcc]

@[simp]
-/
theorem uIcc_self : [[a, a]] = {a} := by simp [uIcc]

@[simp]
/--
theorem `nonempty_uIcc` / 定理 `nonempty_uIcc`

English:
theorem nonempty_uIcc
  statement: Finset.Nonempty [[a, b]]
  proof: nonempty_Icc.2 inf_le_sup

中文:
定理 nonempty_uIcc
  结论: 有限集.非空 [[a, b]]
  证明: nonempty_Icc.2 inf_le_sup

Depends on / 依赖: inf_le_sup, nonempty_Icc
-/
theorem nonempty_uIcc : Finset.Nonempty [[a, b]] :=
  nonempty_Icc.2 inf_le_sup

/--
theorem `Icc_subset_uIcc` / 定理 `Icc_subset_uIcc`

English:
theorem Icc_subset_uIcc
  statement: Icc a b subseteq [[a, b]]
  proof: Icc_subset_Icc inf_le_left le_sup_right

中文:
定理 Icc_subset_uIcc
  结论: 闭区间 a b subseteq [[a, b]]
  证明: Icc_subset_Icc inf_le_left le_sup_right

Depends on / 依赖: Icc_subset_Icc, inf_le_left, le_sup_right
-/
theorem Icc_subset_uIcc : Icc a b subseteq [[a, b]] :=
  Icc_subset_Icc inf_le_left le_sup_right

/--
theorem `Icc_subset_uIcc'` / 定理 `Icc_subset_uIcc'`

English:
theorem Icc_subset_uIcc'
  statement: Icc b a subseteq [[a, b]]
  proof: Icc_subset_Icc inf_le_right le_sup_left

中文:
定理 Icc_subset_uIcc'
  结论: 闭区间 b a subseteq [[a, b]]
  证明: Icc_subset_Icc inf_le_right le_sup_left

Depends on / 依赖: Icc_subset_Icc, inf_le_right, le_sup_left
-/
theorem Icc_subset_uIcc' : Icc b a subseteq [[a, b]] :=
  Icc_subset_Icc inf_le_right le_sup_left

/--
theorem `left_mem_uIcc` / 定理 `left_mem_uIcc`

English:
theorem left_mem_uIcc
  statement: a in [[a, b]]
  proof: mem_Icc.2 ⟨inf_le_left, le_sup_left⟩

中文:
定理 left_mem_uIcc
  结论: a in [[a, b]]
  证明: mem_Icc.2 ⟨inf_le_left, le_sup_left⟩

Depends on / 依赖: inf_le_left, le_sup_left, mem_Icc
-/
theorem left_mem_uIcc : a in [[a, b]] :=
  mem_Icc.2 ⟨inf_le_left, le_sup_left⟩

/--
theorem `right_mem_uIcc` / 定理 `right_mem_uIcc`

English:
theorem right_mem_uIcc
  statement: b in [[a, b]]
  proof: mem_Icc.2 ⟨inf_le_right, le_sup_right⟩

中文:
定理 right_mem_uIcc
  结论: b in [[a, b]]
  证明: mem_Icc.2 ⟨inf_le_right, le_sup_right⟩

Depends on / 依赖: inf_le_right, le_sup_right, mem_Icc
-/
theorem right_mem_uIcc : b in [[a, b]] :=
  mem_Icc.2 ⟨inf_le_right, le_sup_right⟩

/--
theorem `mem_uIcc_of_le` / 定理 `mem_uIcc_of_le`

English:
theorem mem_uIcc_of_le
  given: (ha : a <= x) (hb : x <= b)
  statement: x in [[a, b]]
  proof: Icc_subset_uIcc mem_Icc.2 ⟨ha, hb⟩

中文:
定理 mem_uIcc_of_le
  条件: (ha : a <= x) (hb : x <= b)
  结论: x in [[a, b]]
  证明: Icc_subset_uIcc mem_Icc.2 ⟨ha, hb⟩

Depends on / 依赖: Icc_subset_uIcc, mem_Icc
-/
theorem mem_uIcc_of_le (ha : a <= x) (hb : x <= b) : x in [[a, b]] :=
Icc_subset_uIcc mem_Icc.2 ⟨ha, hb⟩

/--
theorem `mem_uIcc_of_ge` / 定理 `mem_uIcc_of_ge`

English:
theorem mem_uIcc_of_ge
  given: (hb : b <= x) (ha : x <= a)
  statement: x in [[a, b]]
  proof: Icc_subset_uIcc' mem_Icc.2 ⟨hb, ha⟩

中文:
定理 mem_uIcc_of_ge
  条件: (hb : b <= x) (ha : x <= a)
  结论: x in [[a, b]]
  证明: Icc_subset_uIcc' mem_Icc.2 ⟨hb, ha⟩

Depends on / 依赖: Icc_subset_uIcc, mem_Icc
-/
theorem mem_uIcc_of_ge (hb : b <= x) (ha : x <= a) : x in [[a, b]] :=
Icc_subset_uIcc' mem_Icc.2 ⟨hb, ha⟩

/--
theorem `uIcc_subset_uIcc` / 定理 `uIcc_subset_uIcc`

English:
theorem uIcc_subset_uIcc
  given: (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ in [[a₂, b₂]])
  proof: by
  rw [mem_uIcc] at h₁ h₂
  exact Icc_subset_Icc (_root_.le_inf h₁.1 h₂.1) (_root_.sup_le h₁.2 h₂.2)

中文:
定理 uIcc_subset_uIcc
  条件: (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ in [[a₂, b₂]])
  证明: by
  rw [mem_uIcc] at h₁ h₂
  exact Icc_subset_Icc (_root_.le_inf h₁.1 h₂.1) (_root_.sup_le h₁.2 h₂.2)

Depends on / 依赖: Icc_subset_Icc, _root_, _root_.le_inf, _root_.sup_le, le_inf, mem_uIcc, sup_le
-/
theorem uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ in [[a₂, b₂]]) :
    [[a₁, b₁]] subseteq [[a₂, b₂]] := by
  rw [mem_uIcc] at h₁ h₂
  exact Icc_subset_Icc (_root_.le_inf h₁.1 h₂.1) (_root_.sup_le h₁.2 h₂.2)

/--
theorem `uIcc_subset_Icc` / 定理 `uIcc_subset_Icc`

English:
theorem uIcc_subset_Icc
  given: (ha : a₁ in Icc a₂ b₂) (hb : b₁ in Icc a₂ b₂)
  statement: [[a₁, b₁]] subseteq Icc a₂ b₂
  proof: by
  rw [mem_Icc] at ha hb
  exact Icc_subset_Icc (_root_.le_inf ha.1 hb.1) (_root_.sup_le ha.2 hb.2)

中文:
定理 uIcc_subset_Icc
  条件: (ha : a₁ in 闭区间 a₂ b₂) (hb : b₁ in 闭区间 a₂ b₂)
  结论: [[a₁, b₁]] subseteq 闭区间 a₂ b₂
  证明: by
  rw [mem_Icc] at ha hb
  exact Icc_subset_Icc (_root_.le_inf ha.1 hb.1) (_root_.sup_le ha.2 hb.2)

Depends on / 依赖: Icc_subset_Icc, _root_, _root_.le_inf, _root_.sup_le, le_inf, mem_Icc, sup_le
-/
theorem uIcc_subset_Icc (ha : a₁ in Icc a₂ b₂) (hb : b₁ in Icc a₂ b₂) : [[a₁, b₁]] subseteq Icc a₂ b₂ := by
  rw [mem_Icc] at ha hb
  exact Icc_subset_Icc (_root_.le_inf ha.1 hb.1) (_root_.sup_le ha.2 hb.2)

/--
theorem `uIcc_subset_uIcc_iff_mem` / 定理 `uIcc_subset_uIcc_iff_mem`

English:
theorem uIcc_subset_uIcc_iff_mem
  statement: [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₁ in [[a₂, b₂]] ∧ b₁ in [[a₂, b₂]]
  proof: ⟨fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩, fun h => uIcc_subset_uIcc h.1 h.2⟩

中文:
定理 uIcc_subset_uIcc_iff_mem
  结论: [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₁ in [[a₂, b₂]] ∧ b₁ in [[a₂, b₂]]
  证明: ⟨fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩, fun h => uIcc_subset_uIcc h.1 h.2⟩

Depends on / 依赖: left_mem_uIcc, right_mem_uIcc, uIcc_subset_uIcc
-/
theorem uIcc_subset_uIcc_iff_mem : [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₁ in [[a₂, b₂]] ∧ b₁ in [[a₂, b₂]] :=
  ⟨fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩, fun h => uIcc_subset_uIcc h.1 h.2⟩

/--
theorem `uIcc_subset_uIcc_iff_le'` / 定理 `uIcc_subset_uIcc_iff_le'`

English:
theorem uIcc_subset_uIcc_iff_le'
  proof: Icc_subset_Icc_iff inf_le_sup

中文:
定理 uIcc_subset_uIcc_iff_le'
  证明: Icc_subset_Icc_iff inf_le_sup

Depends on / 依赖: Icc_subset_Icc_iff, inf_le_sup
-/
theorem uIcc_subset_uIcc_iff_le' :
    [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₂ ⊓ b₂ <= a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ <= a₂ ⊔ b₂ :=
  Icc_subset_Icc_iff inf_le_sup

/--
theorem `uIcc_subset_uIcc_right` / 定理 `uIcc_subset_uIcc_right`

English:
theorem uIcc_subset_uIcc_right
  given: (h : x in [[a, b]])
  statement: [[x, b]] subseteq [[a, b]]
  proof: uIcc_subset_uIcc h right_mem_uIcc

中文:
定理 uIcc_subset_uIcc_right
  条件: (h : x in [[a, b]])
  结论: [[x, b]] subseteq [[a, b]]
  证明: uIcc_subset_uIcc h right_mem_uIcc

Depends on / 依赖: right_mem_uIcc, uIcc_subset_uIcc
-/
theorem uIcc_subset_uIcc_right (h : x in [[a, b]]) : [[x, b]] subseteq [[a, b]] :=
  uIcc_subset_uIcc h right_mem_uIcc

/--
theorem `uIcc_subset_uIcc_left` / 定理 `uIcc_subset_uIcc_left`

English:
theorem uIcc_subset_uIcc_left
  given: (h : x in [[a, b]])
  statement: [[a, x]] subseteq [[a, b]]
  proof: uIcc_subset_uIcc left_mem_uIcc h

中文:
定理 uIcc_subset_uIcc_left
  条件: (h : x in [[a, b]])
  结论: [[a, x]] subseteq [[a, b]]
  证明: uIcc_subset_uIcc left_mem_uIcc h

Depends on / 依赖: left_mem_uIcc, uIcc_subset_uIcc
-/
theorem uIcc_subset_uIcc_left (h : x in [[a, b]]) : [[a, x]] subseteq [[a, b]] :=
  uIcc_subset_uIcc left_mem_uIcc h

end Lattice

section DistribLattice

variable [DistribLattice α] [LocallyFiniteOrder α] {a b c : α}

/--
theorem `eq_of_mem_uIcc_of_mem_uIcc` / 定理 `eq_of_mem_uIcc_of_mem_uIcc`

English:
theorem eq_of_mem_uIcc_of_mem_uIcc
  statement: a in [[b, c]] -> b in [[a, c]] -> a = b
  proof: by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc

中文:
定理 eq_of_mem_uIcc_of_mem_uIcc
  结论: a in [[b, c]] -> b in [[a, c]] -> a = b
  证明: by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc

Depends on / 依赖: Set.eq_of_mem_uIcc_of_mem_uIcc, eq_of_mem_uIcc_of_mem_uIcc, mem_uIcc, simp_rw
-/
theorem eq_of_mem_uIcc_of_mem_uIcc : a in [[b, c]] -> b in [[a, c]] -> a = b := by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc

/--
theorem `eq_of_mem_uIcc_of_mem_uIcc'` / 定理 `eq_of_mem_uIcc_of_mem_uIcc'`

English:
theorem eq_of_mem_uIcc_of_mem_uIcc'
  statement: b in [[a, c]] -> c in [[a, b]] -> b = c
  proof: by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc'

中文:
定理 eq_of_mem_uIcc_of_mem_uIcc'
  结论: b in [[a, c]] -> c in [[a, b]] -> b = c
  证明: by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc'

Depends on / 依赖: Set.eq_of_mem_uIcc_of_mem_uIcc, eq_of_mem_uIcc_of_mem_uIcc, mem_uIcc, simp_rw
-/
theorem eq_of_mem_uIcc_of_mem_uIcc' : b in [[a, c]] -> c in [[a, b]] -> b = c := by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc'

/--
theorem `uIcc_injective_right` / 定理 `uIcc_injective_right`

English:
theorem uIcc_injective_right
  given: (a : α)
  statement: Injective fun b => [[b, a]]
  proof: fun b c h => by
  rw [Finset.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)

中文:
定理 uIcc_injective_right
  条件: (a : α)
  结论: 单射 fun b => [[b, a]]
  证明: fun b c h => by
  rw [Finset.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)

Depends on / 依赖: Finset, Finset.ext_iff, eq_of_mem_uIcc_of_mem_uIcc, ext_iff, left_mem_uIcc
-/
theorem uIcc_injective_right (a : α) : Injective fun b => [[b, a]] := fun b c h => by
  rw [Finset.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)

/--
theorem `uIcc_injective_left` / 定理 `uIcc_injective_left`

English:
theorem uIcc_injective_left
  given: (a : α)
  statement: Injective (uIcc a)
  proof: by
  simpa only [uIcc_comm] using uIcc_injective_right a

中文:
定理 uIcc_injective_left
  条件: (a : α)
  结论: 单射 (uIcc a)
  证明: by
  simpa only [uIcc_comm] using uIcc_injective_right a

Depends on / 依赖: uIcc_comm, uIcc_injective_right
-/
theorem uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a

end DistribLattice

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c : α}

/--
theorem `Icc_min_max` / 定理 `Icc_min_max`

English:
theorem Icc_min_max
  statement: Icc (min a b) (max a b) = [[a, b]]
  proof: rfl

中文:
定理 Icc_min_max
  结论: 闭区间 (最小值 a b) (最大值 a b) = [[a, b]]
  证明: rfl
-/
theorem Icc_min_max : Icc (min a b) (max a b) = [[a, b]] :=
  rfl

/--
theorem `uIcc_of_not_le` / 定理 `uIcc_of_not_le`

English:
theorem uIcc_of_not_le
  given: (h : ¬a <= b)
  statement: [[a, b]] = Icc b a
  proof: uIcc_of_ge le_of_not_ge h

中文:
定理 uIcc_of_not_le
  条件: (h : ¬a <= b)
  结论: [[a, b]] = 闭区间 b a
  证明: uIcc_of_ge le_of_not_ge h

Depends on / 依赖: le_of_not_ge, uIcc_of_ge
-/
theorem uIcc_of_not_le (h : ¬a <= b) : [[a, b]] = Icc b a :=
uIcc_of_ge le_of_not_ge h

/--
theorem `uIcc_of_not_ge` / 定理 `uIcc_of_not_ge`

English:
theorem uIcc_of_not_ge
  given: (h : ¬b <= a)
  statement: [[a, b]] = Icc a b
  proof: uIcc_of_le le_of_not_ge h

中文:
定理 uIcc_of_not_ge
  条件: (h : ¬b <= a)
  结论: [[a, b]] = 闭区间 a b
  证明: uIcc_of_le le_of_not_ge h

Depends on / 依赖: le_of_not_ge, uIcc_of_le
-/
theorem uIcc_of_not_ge (h : ¬b <= a) : [[a, b]] = Icc a b :=
uIcc_of_le le_of_not_ge h

/--
theorem `uIcc_eq_union` / 定理 `uIcc_eq_union`

English:
theorem uIcc_eq_union
  statement: [[a, b]] = Icc a b union Icc b a
  proof: coe_injective by
    push_cast
    exact Set.uIcc_eq_union

中文:
定理 uIcc_eq_union
  结论: [[a, b]] = 闭区间 a b union 闭区间 b a
  证明: coe_injective by
    push_cast
    exact Set.uIcc_eq_union

Depends on / 依赖: Set.uIcc_eq_union, coe_injective, uIcc_eq_union
-/
theorem uIcc_eq_union : [[a, b]] = Icc a b union Icc b a :=
coe_injective by
    push_cast
    exact Set.uIcc_eq_union

/--
theorem `mem_uIcc'` / 定理 `mem_uIcc'`

English:
theorem mem_uIcc'
  statement: a in [[b, c]] ↔ b <= a ∧ a <= c ∨ c <= a ∧ a <= b
  proof: by simp [uIcc_eq_union]

中文:
定理 mem_uIcc'
  结论: a in [[b, c]] ↔ b <= a ∧ a <= c ∨ c <= a ∧ a <= b
  证明: by simp [uIcc_eq_union]

Depends on / 依赖: uIcc_eq_union
-/
theorem mem_uIcc' : a in [[b, c]] ↔ b <= a ∧ a <= c ∨ c <= a ∧ a <= b := by simp [uIcc_eq_union]

/--
theorem `notMem_uIcc_of_lt` / 定理 `notMem_uIcc_of_lt`

English:
theorem notMem_uIcc_of_lt
  statement: c < a -> c < b -> c ∉ [[a, b]]
  proof: by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_lt

中文:
定理 notMem_uIcc_of_lt
  结论: c < a -> c < b -> c ∉ [[a, b]]
  证明: by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_lt

Depends on / 依赖: Set.notMem_uIcc_of_lt, mem_uIcc, notMem_uIcc_of_lt
-/
theorem notMem_uIcc_of_lt : c < a -> c < b -> c ∉ [[a, b]] := by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_lt

/--
theorem `notMem_uIcc_of_gt` / 定理 `notMem_uIcc_of_gt`

English:
theorem notMem_uIcc_of_gt
  statement: a < c -> b < c -> c ∉ [[a, b]]
  proof: by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_gt

中文:
定理 notMem_uIcc_of_gt
  结论: a < c -> b < c -> c ∉ [[a, b]]
  证明: by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_gt

Depends on / 依赖: Set.notMem_uIcc_of_gt, mem_uIcc, notMem_uIcc_of_gt
-/
theorem notMem_uIcc_of_gt : a < c -> b < c -> c ∉ [[a, b]] := by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_gt

/--
theorem `uIcc_subset_uIcc_iff_le` / 定理 `uIcc_subset_uIcc_iff_le`

English:
theorem uIcc_subset_uIcc_iff_le
  proof: uIcc_subset_uIcc_iff_le'

中文:
定理 uIcc_subset_uIcc_iff_le
  证明: uIcc_subset_uIcc_iff_le'

Depends on / 依赖: uIcc_subset_uIcc_iff_le
-/
theorem uIcc_subset_uIcc_iff_le :
    [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ min a₂ b₂ <= min a₁ b₁ ∧ max a₁ b₁ <= max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'

/--
theorem `uIcc_subset_uIcc_union_uIcc` / 定理 `uIcc_subset_uIcc_union_uIcc`

English:
theorem uIcc_subset_uIcc_union_uIcc
  statement: [[a, c]] subseteq [[a, b]] union [[b, c]]
  proof: coe_subset.1 by
    push_cast
    exact Set.uIcc_subset_uIcc_union_uIcc

中文:
定理 uIcc_subset_uIcc_union_uIcc
  结论: [[a, c]] subseteq [[a, b]] union [[b, c]]
  证明: coe_subset.1 by
    push_cast
    exact Set.uIcc_subset_uIcc_union_uIcc

Depends on / 依赖: Set.uIcc_subset_uIcc_union_uIcc, coe_subset, uIcc_subset_uIcc_union_uIcc
-/
theorem uIcc_subset_uIcc_union_uIcc : [[a, c]] subseteq [[a, b]] union [[b, c]] :=
coe_subset.1 by
    push_cast
    exact Set.uIcc_subset_uIcc_union_uIcc

end LinearOrder
end Finset

/-! ### `⩿`, `⋖` and monotonicity -/

section Cover

open Finset Relation

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `transGen_wcovBy_of_le` / 引理 `transGen_wcovBy_of_le`

English:
lemma transGen_wcovBy_of_le
  given: [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x <= y)
  proof: by
  -- We proceed by well-founded induction on the cardinality of `Icc x y`.
  -- It's impossible for the cardinality to be zero since `x ≤ y`
have : #(Ico x y) < #(Icc x y) := card_lt_card
    ⟨Ico_subset_Icc_self, not_subset.mpr ⟨y, ⟨right_mem_Icc.mpr hxy, right_notMem_Ico⟩⟩⟩
  by_cases hxy' : y <= x
  -- If `y ≤ x`, then `x ⩿ y`
· exact .single wcovBy_of_le_of_le hxy hxy'
  /- and if `¬ y ≤ x`, then `x < y`, not because it is a linear order, but because `x ≤ y`
  already. In that case, since `z` is maximal in `Ico x y`, then `z ⩿ y` and we can use the
  induction hypothesis to show that `Relation.TransGen (· ⩿ ·) x z`. -/
  · obtain ⟨z, hxz, hz⟩ :=
(Set.finite_Ico x y).exists_le_maximal Set.left_mem_Ico.2 hxy.lt_of_not_ge hxy'
    have z_card := calc
#(Icc x z) <= #(Ico x y) := card_le_card Icc_subset_Ico_right hz.1.2
      _ < #(Icc x y) := this
    have h₁ := transGen_wcovBy_of_le hz.1.1
    have h₂ : z ⩿ y :=
⟨hz.1.2.le, fun c hzc hcy => hzc.not_ge hz.2 ⟨hz.1.1.trans hzc.le, hcy⟩ hzc.le⟩
    exact .tail h₁ h₂
termination_by #(Icc x y)

中文:
引理 transGen_wcovBy_of_le
  条件: [预序 α] [局部有限序 α] {x y : α} (hxy : x <= y)
  证明: by
  -- We proceed by well-founded induction on the cardinality of `Icc x y`.
  -- It's impossible for the cardinality to be zero since `x ≤ y`
have : #(Ico x y) < #(Icc x y) := card_lt_card
    ⟨Ico_subset_Icc_self, not_subset.mpr ⟨y, ⟨right_mem_Icc.mpr hxy, right_notMem_Ico⟩⟩⟩
  by_cases hxy' : y <= x
  -- If `y ≤ x`, then `x ⩿ y`
· exact .single wcovBy_of_le_of_le hxy hxy'
  /- and if `¬ y ≤ x`, then `x < y`, not because it is a linear order, but because `x ≤ y`
  already. In that case, since `z` is maximal in `Ico x y`, then `z ⩿ y` and we can use the
  induction hypothesis to show that `Relation.TransGen (· ⩿ ·) x z`. -/
  · obtain ⟨z, hxz, hz⟩ :=
(Set.finite_Ico x y).exists_le_maximal Set.left_mem_Ico.2 hxy.lt_of_not_ge hxy'
    have z_card := calc
#(Icc x z) <= #(Ico x y) := card_le_card Icc_subset_Ico_right hz.1.2
      _ < #(Icc x y) := this
    have h₁ := transGen_wcovBy_of_le hz.1.1
    have h₂ : z ⩿ y :=
⟨hz.1.2.le, fun c hzc hcy => hzc.not_ge hz.2 ⟨hz.1.1.trans hzc.le, hcy⟩ hzc.le⟩
    exact .tail h₁ h₂
termination_by #(Icc x y)
-/
lemma transGen_wcovBy_of_le [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x <= y) :
    TransGen (· ⩿ ·) x y := by
  -- We proceed by well-founded induction on the cardinality of `Icc x y`.
  -- It's impossible for the cardinality to be zero since `x ≤ y`
have : #(Ico x y) < #(Icc x y) := card_lt_card
    ⟨Ico_subset_Icc_self, not_subset.mpr ⟨y, ⟨right_mem_Icc.mpr hxy, right_notMem_Ico⟩⟩⟩
  by_cases hxy' : y <= x
  -- If `y ≤ x`, then `x ⩿ y`
· exact .single wcovBy_of_le_of_le hxy hxy'
  /- and if `¬ y ≤ x`, then `x < y`, not because it is a linear order, but because `x ≤ y`
  already. In that case, since `z` is maximal in `Ico x y`, then `z ⩿ y` and we can use the
  induction hypothesis to show that `Relation.TransGen (· ⩿ ·) x z`. -/
  · obtain ⟨z, hxz, hz⟩ :=
(Set.finite_Ico x y).exists_le_maximal Set.left_mem_Ico.2 hxy.lt_of_not_ge hxy'
    have z_card := calc
#(Icc x z) <= #(Ico x y) := card_le_card Icc_subset_Ico_right hz.1.2
      _ < #(Icc x y) := this
    have h₁ := transGen_wcovBy_of_le hz.1.1
    have h₂ : z ⩿ y :=
⟨hz.1.2.le, fun c hzc hcy => hzc.not_ge hz.2 ⟨hz.1.1.trans hzc.le, hcy⟩ hzc.le⟩
    exact .tail h₁ h₂
termination_by #(Icc x y)

/--
lemma `le_iff_transGen_wcovBy` / 引理 `le_iff_transGen_wcovBy`

English:
lemma le_iff_transGen_wcovBy
  given: [Preorder α] [LocallyFiniteOrder α] {x y : α}
  proof: by
  refine ⟨transGen_wcovBy_of_le, fun h => ?_⟩
  induction h with
  | single h => exact h.le
  | tail _ h₁ h₂ => exact h₂.trans h₁.le

中文:
引理 le_iff_transGen_wcovBy
  条件: [预序 α] [局部有限序 α] {x y : α}
  证明: by
  refine ⟨transGen_wcovBy_of_le, fun h => ?_⟩
  induction h with
  | single h => exact h.le
  | tail _ h₁ h₂ => exact h₂.trans h₁.le

Depends on / 依赖: h.le, single, transGen_wcovBy_of_le
-/
lemma le_iff_transGen_wcovBy [Preorder α] [LocallyFiniteOrder α] {x y : α} :
    x <= y ↔ TransGen (· ⩿ ·) x y := by
  refine ⟨transGen_wcovBy_of_le, fun h => ?_⟩
  induction h with
  | single h => exact h.le
  | tail _ h₁ h₂ => exact h₂.trans h₁.le

/--
lemma `le_iff_reflTransGen_covBy` / 引理 `le_iff_reflTransGen_covBy`

English:
lemma le_iff_reflTransGen_covBy
  given: [PartialOrder α] [LocallyFiniteOrder α] {x y : α}
  proof: by
  rw [le_iff_transGen_wcovBy]; rw [wcovBy_eq_reflGen_covBy]; rw [transGen_reflGen]

中文:
引理 le_iff_reflTransGen_covBy
  条件: [偏序 α] [局部有限序 α] {x y : α}
  证明: by
  rw [le_iff_transGen_wcovBy]; rw [wcovBy_eq_reflGen_covBy]; rw [transGen_reflGen]

Depends on / 依赖: le_iff_transGen_wcovBy, transGen_reflGen, wcovBy_eq_reflGen_covBy
-/
lemma le_iff_reflTransGen_covBy [PartialOrder α] [LocallyFiniteOrder α] {x y : α} :
    x <= y ↔ ReflTransGen (· ⋖ ·) x y := by
  rw [le_iff_transGen_wcovBy]; rw [wcovBy_eq_reflGen_covBy]; rw [transGen_reflGen]

/--
lemma `transGen_covBy_of_lt` / 引理 `transGen_covBy_of_lt`

English:
lemma transGen_covBy_of_lt
  given: [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x < y)
  proof: by
  -- We proceed by well-founded induction on the cardinality of `Ico x y`.
  -- It's impossible for the cardinality to be zero since `x < y`
  -- `Ico x y` is a nonempty finset and so contains a maximal element `z` and
  -- `Ico x z` has cardinality strictly less than the cardinality of `Ico x y`
obtain ⟨z, hxz, hz⟩ := (Set.finite_Ico x y).exists_le_maximal Set.left_mem_Ico.2 hxy
have z_card : #(Ico x z) < #(Ico x y) := card_lt_card ssubset_iff_of_subset
.mpr ⟨z, mem_Ico.2 hz.1, right_notMem_Ico⟩ (Ico_subset_Ico_right hz.1.2.le)
  /- Since `z` is maximal in `Ico x y`, `z ⋖ y`. -/
  have hzy : z ⋖ y :=
⟨hz.1.2, fun c hc hcy => hc.not_ge hz.2 (⟨(hz.1.1.trans_lt hc).le, hcy⟩) hc.le⟩
  by_cases hxz : x < z
  /- when `x < z`, then we may use the induction hypothesis to get a chain
  `Relation.TransGen (· ⋖ ·) x z`, which we can extend with `Relation.TransGen.tail`. -/
  · exact .tail (transGen_covBy_of_lt hxz) hzy
  /- when `¬ x < z`, then actually `z ≤ x` (not because it's a linear order, but because
  `x ≤ z`), and since `z ⋖ y` we conclude that `x ⋖ y`, then `Relation.TransGen.single`. -/
  · simp only [lt_iff_le_not_ge, not_and, not_not] at hxz
    exact .single (hzy.of_le_of_lt (hxz hz.1.1) hxy)
termination_by #(Ico x y)

中文:
引理 transGen_covBy_of_lt
  条件: [预序 α] [局部有限序 α] {x y : α} (hxy : x < y)
  证明: by
  -- We proceed by well-founded induction on the cardinality of `Ico x y`.
  -- It's impossible for the cardinality to be zero since `x < y`
  -- `Ico x y` is a nonempty finset and so contains a maximal element `z` and
  -- `Ico x z` has cardinality strictly less than the cardinality of `Ico x y`
obtain ⟨z, hxz, hz⟩ := (Set.finite_Ico x y).exists_le_maximal Set.left_mem_Ico.2 hxy
have z_card : #(Ico x z) < #(Ico x y) := card_lt_card ssubset_iff_of_subset
.mpr ⟨z, mem_Ico.2 hz.1, right_notMem_Ico⟩ (Ico_subset_Ico_right hz.1.2.le)
  /- Since `z` is maximal in `Ico x y`, `z ⋖ y`. -/
  have hzy : z ⋖ y :=
⟨hz.1.2, fun c hc hcy => hc.not_ge hz.2 (⟨(hz.1.1.trans_lt hc).le, hcy⟩) hc.le⟩
  by_cases hxz : x < z
  /- when `x < z`, then we may use the induction hypothesis to get a chain
  `Relation.TransGen (· ⋖ ·) x z`, which we can extend with `Relation.TransGen.tail`. -/
  · exact .tail (transGen_covBy_of_lt hxz) hzy
  /- when `¬ x < z`, then actually `z ≤ x` (not because it's a linear order, but because
  `x ≤ z`), and since `z ⋖ y` we conclude that `x ⋖ y`, then `Relation.TransGen.single`. -/
  · simp only [lt_iff_le_not_ge, not_and, not_not] at hxz
    exact .single (hzy.of_le_of_lt (hxz hz.1.1) hxy)
termination_by #(Ico x y)
-/
lemma transGen_covBy_of_lt [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x < y) :
    TransGen (· ⋖ ·) x y := by
  -- We proceed by well-founded induction on the cardinality of `Ico x y`.
  -- It's impossible for the cardinality to be zero since `x < y`
  -- `Ico x y` is a nonempty finset and so contains a maximal element `z` and
  -- `Ico x z` has cardinality strictly less than the cardinality of `Ico x y`
obtain ⟨z, hxz, hz⟩ := (Set.finite_Ico x y).exists_le_maximal Set.left_mem_Ico.2 hxy
have z_card : #(Ico x z) < #(Ico x y) := card_lt_card ssubset_iff_of_subset
.mpr ⟨z, mem_Ico.2 hz.1, right_notMem_Ico⟩ (Ico_subset_Ico_right hz.1.2.le)
  /- Since `z` is maximal in `Ico x y`, `z ⋖ y`. -/
  have hzy : z ⋖ y :=
⟨hz.1.2, fun c hc hcy => hc.not_ge hz.2 (⟨(hz.1.1.trans_lt hc).le, hcy⟩) hc.le⟩
  by_cases hxz : x < z
  /- when `x < z`, then we may use the induction hypothesis to get a chain
  `Relation.TransGen (· ⋖ ·) x z`, which we can extend with `Relation.TransGen.tail`. -/
  · exact .tail (transGen_covBy_of_lt hxz) hzy
  /- when `¬ x < z`, then actually `z ≤ x` (not because it's a linear order, but because
  `x ≤ z`), and since `z ⋖ y` we conclude that `x ⋖ y`, then `Relation.TransGen.single`. -/
  · simp only [lt_iff_le_not_ge, not_and, not_not] at hxz
    exact .single (hzy.of_le_of_lt (hxz hz.1.1) hxy)
termination_by #(Ico x y)

/--
lemma `lt_iff_transGen_covBy` / 引理 `lt_iff_transGen_covBy`

English:
lemma lt_iff_transGen_covBy
  given: [Preorder α] [LocallyFiniteOrder α] {x y : α}
  proof: by
  refine ⟨transGen_covBy_of_lt, fun h => ?_⟩
  induction h with
  | single hx => exact hx.1
  | tail _ hb ih => exact ih.trans hb.1

中文:
引理 lt_iff_transGen_covBy
  条件: [预序 α] [局部有限序 α] {x y : α}
  证明: by
  refine ⟨transGen_covBy_of_lt, fun h => ?_⟩
  induction h with
  | single hx => exact hx.1
  | tail _ hb ih => exact ih.trans hb.1

Depends on / 依赖: ih.trans, single, transGen_covBy_of_lt
-/
lemma lt_iff_transGen_covBy [Preorder α] [LocallyFiniteOrder α] {x y : α} :
    x < y ↔ TransGen (· ⋖ ·) x y := by
  refine ⟨transGen_covBy_of_lt, fun h => ?_⟩
  induction h with
  | single hx => exact hx.1
  | tail _ hb ih => exact ih.trans hb.1

variable {β : Type*}

/--
lemma `monotone_iff_forall_wcovBy` / 引理 `monotone_iff_forall_wcovBy`

English:
lemma monotone_iff_forall_wcovBy
  statement: [Preorder α] [LocallyFiniteOrder α] [Preorder β]
  proof: by
  refine ⟨fun hf _ _ h => hf h.le, fun h a b hab => ?_⟩
simpa [transGen_eq_self] using TransGen.lift f h a b le_iff_transGen_wcovBy.mp hab

中文:
引理 monotone_iff_对任意_wcovBy
  结论: [预序 α] [局部有限序 α] [预序 β]
  证明: by
  refine ⟨fun hf _ _ h => hf h.le, fun h a b hab => ?_⟩
simpa [transGen_eq_self] using TransGen.lift f h a b le_iff_transGen_wcovBy.mp hab

Depends on / 依赖: TransGen, TransGen.lift, h.le, le_iff_transGen_wcovBy, le_iff_transGen_wcovBy.mp, transGen_eq_self
-/
lemma monotone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α -> β) : Monotone f ↔ forall a b : α, a ⩿ b -> f a <= f b := by
  refine ⟨fun hf _ _ h => hf h.le, fun h a b hab => ?_⟩
simpa [transGen_eq_self] using TransGen.lift f h a b le_iff_transGen_wcovBy.mp hab

/--
lemma `monotone_iff_forall_covBy` / 引理 `monotone_iff_forall_covBy`

English:
lemma monotone_iff_forall_covBy
  statement: [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
  proof: by
  refine ⟨fun hf _ _ h => hf h.le, fun h a b hab => ?_⟩
simpa [reflTransGen_eq_self] using ReflTransGen.lift f h a b le_iff_reflTransGen_covBy.mp hab

中文:
引理 monotone_iff_对任意_covBy
  结论: [偏序 α] [局部有限序 α] [预序 β]
  证明: by
  refine ⟨fun hf _ _ h => hf h.le, fun h a b hab => ?_⟩
simpa [reflTransGen_eq_self] using ReflTransGen.lift f h a b le_iff_reflTransGen_covBy.mp hab

Depends on / 依赖: ReflTransGen, ReflTransGen.lift, h.le, le_iff_reflTransGen_covBy, le_iff_reflTransGen_covBy.mp, reflTransGen_eq_self
-/
lemma monotone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α -> β) : Monotone f ↔ forall a b : α, a ⋖ b -> f a <= f b := by
  refine ⟨fun hf _ _ h => hf h.le, fun h a b hab => ?_⟩
simpa [reflTransGen_eq_self] using ReflTransGen.lift f h a b le_iff_reflTransGen_covBy.mp hab

/--
lemma `strictMono_iff_forall_covBy` / 引理 `strictMono_iff_forall_covBy`

English:
lemma strictMono_iff_forall_covBy
  statement: [Preorder α] [LocallyFiniteOrder α] [Preorder β]
  proof: by
  refine ⟨fun hf _ _ h => hf h.lt, fun h a b hab => ?_⟩
  have := Relation.TransGen.lift f h a b
  rw [← lt_iff_transGen_covBy]; rw [transGen_eq_self] at this
  exact this hab

中文:
引理 strictMono_iff_对任意_covBy
  结论: [预序 α] [局部有限序 α] [预序 β]
  证明: by
  refine ⟨fun hf _ _ h => hf h.lt, fun h a b hab => ?_⟩
  have := Relation.TransGen.lift f h a b
  rw [← lt_iff_transGen_covBy]; rw [transGen_eq_self] at this
  exact this hab

Depends on / 依赖: Relation, Relation.TransGen.lift, TransGen, h.lt, lt_iff_transGen_covBy, transGen_eq_self
-/
lemma strictMono_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α -> β) : StrictMono f ↔ forall a b : α, a ⋖ b -> f a < f b := by
  refine ⟨fun hf _ _ h => hf h.lt, fun h a b hab => ?_⟩
  have := Relation.TransGen.lift f h a b
  rw [← lt_iff_transGen_covBy]; rw [transGen_eq_self] at this
  exact this hab

/--
lemma `antitone_iff_forall_wcovBy` / 引理 `antitone_iff_forall_wcovBy`

English:
lemma antitone_iff_forall_wcovBy
  statement: [Preorder α] [LocallyFiniteOrder α] [Preorder β]
  proof: monotone_iff_forall_wcovBy (β := βᵒᵈ) f

中文:
引理 antitone_iff_对任意_wcovBy
  结论: [预序 α] [局部有限序 α] [预序 β]
  证明: monotone_iff_forall_wcovBy (β := βᵒᵈ) f

Depends on / 依赖: monotone_iff_forall_wcovBy
-/
lemma antitone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α -> β) : Antitone f ↔ forall a b : α, a ⩿ b -> f b <= f a :=
  monotone_iff_forall_wcovBy (β := βᵒᵈ) f

/--
lemma `antitone_iff_forall_covBy` / 引理 `antitone_iff_forall_covBy`

English:
lemma antitone_iff_forall_covBy
  statement: [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
  proof: monotone_iff_forall_covBy (β := βᵒᵈ) f

中文:
引理 antitone_iff_对任意_covBy
  结论: [偏序 α] [局部有限序 α] [预序 β]
  证明: monotone_iff_forall_covBy (β := βᵒᵈ) f

Depends on / 依赖: monotone_iff_forall_covBy
-/
lemma antitone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α -> β) : Antitone f ↔ forall a b : α, a ⋖ b -> f b <= f a :=
  monotone_iff_forall_covBy (β := βᵒᵈ) f

/--
lemma `strictAnti_iff_forall_covBy` / 引理 `strictAnti_iff_forall_covBy`

English:
lemma strictAnti_iff_forall_covBy
  statement: [Preorder α] [LocallyFiniteOrder α] [Preorder β]
  proof: strictMono_iff_forall_covBy (β := βᵒᵈ) f

中文:
引理 strictAnti_iff_对任意_covBy
  结论: [预序 α] [局部有限序 α] [预序 β]
  证明: strictMono_iff_forall_covBy (β := βᵒᵈ) f

Depends on / 依赖: strictMono_iff_forall_covBy
-/
lemma strictAnti_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α -> β) : StrictAnti f ↔ forall a b : α, a ⋖ b -> f b < f a :=
  strictMono_iff_forall_covBy (β := βᵒᵈ) f

end Cover
