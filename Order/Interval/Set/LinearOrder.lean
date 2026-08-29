/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.Order.Interval.Set.Basic

/-!
# Interval properties in linear orders

Since every pair of elements are comparable in a linear order, intervals over them are
better behaved. This file collects their properties under this assumption.
-/

public section

assert_not_exists RelIso

open Function

namespace Set

variable {α : Type*} [LinearOrder α] {a a₁ a₂ b b₁ b₂ c d : α}

@[to_dual]
/--
theorem `notMem_Ici` / 定理 `notMem_Ici`

English:
theorem notMem_Ici
  statement: c ∉ Ici a ↔ c < a
  proof: not_le

@[to_dual]

中文:
定理 notMem_Ici
  结论: c ∉ 左闭右无界区间 a ↔ c < a
  证明: not_le

@[to_dual]

Depends on / 依赖: not_le
-/
theorem notMem_Ici : c ∉ Ici a ↔ c < a :=
  not_le

@[to_dual]
/--
theorem `notMem_Ioi` / 定理 `notMem_Ioi`

English:
theorem notMem_Ioi
  statement: c ∉ Ioi a ↔ c <= a
  proof: not_lt

@[to_dual (attr := simp)]

中文:
定理 notMem_Ioi
  结论: c ∉ 左开右无界区间 a ↔ c <= a
  证明: not_lt

@[to_dual (attr := simp)]

Depends on / 依赖: not_lt
-/
theorem notMem_Ioi : c ∉ Ioi a ↔ c <= a :=
  not_lt

@[to_dual (attr := simp)]
/--
theorem `compl_Iic` / 定理 `compl_Iic`

English:
theorem compl_Iic
  statement: (Iic a)ᶜ = Ioi a
  proof: ext fun _ => not_le

@[to_dual (attr := simp)]

中文:
定理 compl_Iic
  结论: (左无界右闭区间 a)ᶜ = 左开右无界区间 a
  证明: ext fun _ => not_le

@[to_dual (attr := simp)]

Depends on / 依赖: not_le
-/
theorem compl_Iic : (Iic a)ᶜ = Ioi a :=
  ext fun _ => not_le

@[to_dual (attr := simp)]
/--
theorem `compl_Iio` / 定理 `compl_Iio`

English:
theorem compl_Iio
  statement: (Iio a)ᶜ = Ici a
  proof: ext fun _ => not_lt

@[to_dual (attr := simp)]

中文:
定理 compl_Iio
  结论: (左无界右开区间 a)ᶜ = 左闭右无界区间 a
  证明: ext fun _ => not_lt

@[to_dual (attr := simp)]

Depends on / 依赖: not_lt
-/
theorem compl_Iio : (Iio a)ᶜ = Ici a :=
  ext fun _ => not_lt

@[to_dual (attr := simp)]
/--
theorem `Ici_sdiff_Ici` / 定理 `Ici_sdiff_Ici`

English:
theorem Ici_sdiff_Ici
  statement: Ici a \ Ici b = Ico a b
  proof: by rw [sdiff_eq, compl_Ici, Ici_inter_Iio]

@[deprecated (since := "2026-06-03")] alias Ici_diff_Ici := Ici_sdiff_Ici

@[to_dual (attr := simp)]

中文:
定理 Ici_sdiff_Ici
  结论: 左闭右无界区间 a \ 左闭右无界区间 b = 左闭右开区间 a b
  证明: by rw [sdiff_eq, compl_Ici, Ici_inter_Iio]

@[deprecated (since := "2026-06-03")] alias Ici_diff_Ici := Ici_sdiff_Ici

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_inter_Iio, compl_Ici, sdiff_eq
-/
theorem Ici_sdiff_Ici : Ici a \ Ici b = Ico a b := by rw [sdiff_eq, compl_Ici, Ici_inter_Iio]

@[deprecated (since := "2026-06-03")] alias Ici_diff_Ici := Ici_sdiff_Ici

@[to_dual (attr := simp)]
/--
theorem `Ici_sdiff_Ioi` / 定理 `Ici_sdiff_Ioi`

English:
theorem Ici_sdiff_Ioi
  statement: Ici a \ Ioi b = Icc a b
  proof: by rw [sdiff_eq, compl_Ioi, Ici_inter_Iic]

@[deprecated (since := "2026-06-03")] alias Ici_diff_Ioi := Ici_sdiff_Ioi

@[to_dual (attr := simp)]

中文:
定理 Ici_sdiff_Ioi
  结论: 左闭右无界区间 a \ 左开右无界区间 b = 闭区间 a b
  证明: by rw [sdiff_eq, compl_Ioi, Ici_inter_Iic]

@[deprecated (since := "2026-06-03")] alias Ici_diff_Ioi := Ici_sdiff_Ioi

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_inter_Iic, compl_Ioi, sdiff_eq
-/
theorem Ici_sdiff_Ioi : Ici a \ Ioi b = Icc a b := by rw [sdiff_eq, compl_Ioi, Ici_inter_Iic]

@[deprecated (since := "2026-06-03")] alias Ici_diff_Ioi := Ici_sdiff_Ioi

@[to_dual (attr := simp)]
/--
theorem `Ioi_sdiff_Ioi` / 定理 `Ioi_sdiff_Ioi`

English:
theorem Ioi_sdiff_Ioi
  statement: Ioi a \ Ioi b = Ioc a b
  proof: by rw [sdiff_eq, compl_Ioi, Ioi_inter_Iic]

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ioi := Ioi_sdiff_Ioi

@[to_dual (attr := simp)]

中文:
定理 Ioi_sdiff_Ioi
  结论: 左开右无界区间 a \ 左开右无界区间 b = 左开右闭区间 a b
  证明: by rw [sdiff_eq, compl_Ioi, Ioi_inter_Iic]

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ioi := Ioi_sdiff_Ioi

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_inter_Iic, compl_Ioi, sdiff_eq
-/
theorem Ioi_sdiff_Ioi : Ioi a \ Ioi b = Ioc a b := by rw [sdiff_eq, compl_Ioi, Ioi_inter_Iic]

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ioi := Ioi_sdiff_Ioi

@[to_dual (attr := simp)]
/--
theorem `Ioi_sdiff_Ici` / 定理 `Ioi_sdiff_Ici`

English:
theorem Ioi_sdiff_Ici
  statement: Ioi a \ Ici b = Ioo a b
  proof: by rw [sdiff_eq, compl_Ici, Ioi_inter_Iio]

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ici := Ioi_sdiff_Ici

@[to_dual]

中文:
定理 Ioi_sdiff_Ici
  结论: 左开右无界区间 a \ 左闭右无界区间 b = 开区间 a b
  证明: by rw [sdiff_eq, compl_Ici, Ioi_inter_Iio]

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ici := Ioi_sdiff_Ici

@[to_dual]

Depends on / 依赖: Ioi_inter_Iio, compl_Ici, sdiff_eq
-/
theorem Ioi_sdiff_Ici : Ioi a \ Ici b = Ioo a b := by rw [sdiff_eq, compl_Ici, Ioi_inter_Iio]

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ici := Ioi_sdiff_Ici

@[to_dual]
/--
theorem `Ioi_injective` / 定理 `Ioi_injective`

English:
theorem Ioi_injective
  statement: Injective (Ioi : α -> Set α)
  proof: fun _ _ =>
  eq_of_forall_gt_iff ∘ Set.ext_iff.1

@[to_dual]

中文:
定理 Ioi_injective
  结论: 单射 (左开右无界区间 : α -> 集合 α)
  证明: fun _ _ =>
  eq_of_forall_gt_iff ∘ Set.ext_iff.1

@[to_dual]
-/
theorem Ioi_injective : Injective (Ioi : α -> Set α) := fun _ _ =>
  eq_of_forall_gt_iff ∘ Set.ext_iff.1

@[to_dual]
/--
theorem `Ioi_inj` / 定理 `Ioi_inj`

English:
theorem Ioi_inj
  statement: Ioi a = Ioi b ↔ a = b
  proof: Ioi_injective.eq_iff

中文:
定理 Ioi_inj
  结论: 左开右无界区间 a = 左开右无界区间 b ↔ a = b
  证明: Ioi_injective.eq_iff

Depends on / 依赖: Ioi_injective, Ioi_injective.eq_iff, eq_iff
-/
theorem Ioi_inj : Ioi a = Ioi b ↔ a = b :=
  Ioi_injective.eq_iff

/--
theorem `Ico_subset_Ico_iff` / 定理 `Ico_subset_Ico_iff`

English:
theorem Ico_subset_Ico_iff
  given: (h₁ : a₁ < b₁)
  statement: Ico a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
  proof: ⟨fun h =>
    have : a₂ <= a₁ ∧ a₁ < b₂ := h ⟨le_rfl, h₁⟩
    ⟨this.1, le_of_not_gt fun h' => lt_irrefl b₂ (h ⟨this.2.le, h'⟩).2⟩,
    fun ⟨h₁, h₂⟩ => Ico_subset_Ico h₁ h₂⟩

中文:
定理 Ico_subset_Ico_iff
  条件: (h₁ : a₁ < b₁)
  结论: 左闭右开区间 a₁ b₁ subseteq 左闭右开区间 a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
  证明: ⟨fun h =>
    have : a₂ <= a₁ ∧ a₁ < b₂ := h ⟨le_rfl, h₁⟩
    ⟨this.1, le_of_not_gt fun h' => lt_irrefl b₂ (h ⟨this.2.le, h'⟩).2⟩,
    fun ⟨h₁, h₂⟩ => Ico_subset_Ico h₁ h₂⟩

Depends on / 依赖: Ico_subset_Ico, le_of_not_gt, le_rfl, lt_irrefl
-/
theorem Ico_subset_Ico_iff (h₁ : a₁ < b₁) : Ico a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂ :=
  ⟨fun h =>
    have : a₂ <= a₁ ∧ a₁ < b₂ := h ⟨le_rfl, h₁⟩
    ⟨this.1, le_of_not_gt fun h' => lt_irrefl b₂ (h ⟨this.2.le, h'⟩).2⟩,
    fun ⟨h₁, h₂⟩ => Ico_subset_Ico h₁ h₂⟩

/--
theorem `Ioc_subset_Ioc_iff` / 定理 `Ioc_subset_Ioc_iff`

English:
theorem Ioc_subset_Ioc_iff
  given: (h₁ : a₁ < b₁)
  statement: Ioc a₁ b₁ subseteq Ioc a₂ b₂ ↔ b₁ <= b₂ ∧ a₂ <= a₁
  proof: by
  convert! @Ico_subset_Ico_iff αᵒᵈ _ b₁ b₂ a₁ a₂ h₁ using 2 <;> exact (@Ico_toDual α _ _ _).symm

中文:
定理 Ioc_subset_Ioc_iff
  条件: (h₁ : a₁ < b₁)
  结论: 左开右闭区间 a₁ b₁ subseteq 左开右闭区间 a₂ b₂ ↔ b₁ <= b₂ ∧ a₂ <= a₁
  证明: by
  convert! @Ico_subset_Ico_iff αᵒᵈ _ b₁ b₂ a₁ a₂ h₁ using 2 <;> exact (@Ico_toDual α _ _ _).symm

Depends on / 依赖: Ico_subset_Ico_iff, Ico_toDual, convert
-/
theorem Ioc_subset_Ioc_iff (h₁ : a₁ < b₁) : Ioc a₁ b₁ subseteq Ioc a₂ b₂ ↔ b₁ <= b₂ ∧ a₂ <= a₁ := by
  convert! @Ico_subset_Ico_iff αᵒᵈ _ b₁ b₂ a₁ a₂ h₁ using 2 <;> exact (@Ico_toDual α _ _ _).symm

/--
theorem `Ico_eq_Ico_iff` / 定理 `Ico_eq_Ico_iff`

English:
theorem Ico_eq_Ico_iff
  given: (h : a < b ∨ c < d)
  statement: Ico a b = Ico c d ↔ a = c ∧ b = d
  proof: by
  refine ⟨fun h => ?_, by grind⟩
  have : c <= a ∧ b <= d := (Ico_subset_Ico_iff (show a < b by grind [Set.nonempty_Ico])).1 h.subset
  have : a <= c ∧ d <= b := (Ico_subset_Ico_iff (show c < d by grind)).1 h.superset
  grind

中文:
定理 Ico_eq_Ico_iff
  条件: (h : a < b ∨ c < d)
  结论: 左闭右开区间 a b = 左闭右开区间 c d ↔ a = c ∧ b = d
  证明: by
  refine ⟨fun h => ?_, by grind⟩
  have : c <= a ∧ b <= d := (Ico_subset_Ico_iff (show a < b by grind [Set.nonempty_Ico])).1 h.subset
  have : a <= c ∧ d <= b := (Ico_subset_Ico_iff (show c < d by grind)).1 h.superset
  grind

Depends on / 依赖: Ico_subset_Ico_iff, Set.nonempty_Ico, h.subset, h.superset, nonempty_Ico, subset, superset
-/
theorem Ico_eq_Ico_iff (h : a < b ∨ c < d) : Ico a b = Ico c d ↔ a = c ∧ b = d := by
  refine ⟨fun h => ?_, by grind⟩
  have : c <= a ∧ b <= d := (Ico_subset_Ico_iff (show a < b by grind [Set.nonempty_Ico])).1 h.subset
  have : a <= c ∧ d <= b := (Ico_subset_Ico_iff (show c < d by grind)).1 h.superset
  grind

/--
theorem `Ioc_eq_Ioc_iff` / 定理 `Ioc_eq_Ioc_iff`

English:
theorem Ioc_eq_Ioc_iff
  given: (hab : a < b ∨ c < d)
  statement: Ioc a b = Ioc c d ↔ a = c ∧ b = d
  proof: by
  refine ⟨fun h => ?_, by grind⟩
  have : b <= d ∧ c <= a := (Ioc_subset_Ioc_iff (show a < b by grind [Set.nonempty_Ioc])).1 h.subset
  have : d <= b ∧ a <= c := (Ioc_subset_Ioc_iff (show c < d by grind)).1 h.superset
  grind

中文:
定理 Ioc_eq_Ioc_iff
  条件: (hab : a < b ∨ c < d)
  结论: 左开右闭区间 a b = 左开右闭区间 c d ↔ a = c ∧ b = d
  证明: by
  refine ⟨fun h => ?_, by grind⟩
  have : b <= d ∧ c <= a := (Ioc_subset_Ioc_iff (show a < b by grind [Set.nonempty_Ioc])).1 h.subset
  have : d <= b ∧ a <= c := (Ioc_subset_Ioc_iff (show c < d by grind)).1 h.superset
  grind

Depends on / 依赖: Ioc_subset_Ioc_iff, Set.nonempty_Ioc, h.subset, h.superset, nonempty_Ioc, subset, superset
-/
theorem Ioc_eq_Ioc_iff (hab : a < b ∨ c < d) : Ioc a b = Ioc c d ↔ a = c ∧ b = d := by
  refine ⟨fun h => ?_, by grind⟩
  have : b <= d ∧ c <= a := (Ioc_subset_Ioc_iff (show a < b by grind [Set.nonempty_Ioc])).1 h.subset
  have : d <= b ∧ a <= c := (Ioc_subset_Ioc_iff (show c < d by grind)).1 h.superset
  grind

/--
theorem `Ioo_subset_Ioo_iff` / 定理 `Ioo_subset_Ioo_iff`

English:
theorem Ioo_subset_Ioo_iff
  given: [DenselyOrdered α] (h₁ : a₁ < b₁)
  proof: ⟨fun h => by
    rcases exists_between h₁ with ⟨x, xa, xb⟩
    constructor <;> refine le_of_not_gt fun h' => ?_
    · have ab := (h ⟨xa, xb⟩).1.trans xb
      exact lt_irrefl _ (h ⟨h', ab⟩).1
    · have ab := xa.trans (h ⟨xa, xb⟩).2
      exact lt_irrefl _ (h ⟨ab, h'⟩).2,
    fun ⟨h₁, h₂⟩ => Ioo_subset_Ioo h₁ h₂⟩

@[to_dual]

中文:
定理 Ioo_subset_Ioo_iff
  条件: [稠密序 α] (h₁ : a₁ < b₁)
  证明: ⟨fun h => by
    rcases exists_between h₁ with ⟨x, xa, xb⟩
    constructor <;> refine le_of_not_gt fun h' => ?_
    · have ab := (h ⟨xa, xb⟩).1.trans xb
      exact lt_irrefl _ (h ⟨h', ab⟩).1
    · have ab := xa.trans (h ⟨xa, xb⟩).2
      exact lt_irrefl _ (h ⟨ab, h'⟩).2,
    fun ⟨h₁, h₂⟩ => Ioo_subset_Ioo h₁ h₂⟩

@[to_dual]

Depends on / 依赖: Ioo_subset_Ioo, exists_between, le_of_not_gt, lt_irrefl, xa.trans
-/
theorem Ioo_subset_Ioo_iff [DenselyOrdered α] (h₁ : a₁ < b₁) :
    Ioo a₁ b₁ subseteq Ioo a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂ :=
  ⟨fun h => by
    rcases exists_between h₁ with ⟨x, xa, xb⟩
    constructor <;> refine le_of_not_gt fun h' => ?_
    · have ab := (h ⟨xa, xb⟩).1.trans xb
      exact lt_irrefl _ (h ⟨h', ab⟩).1
    · have ab := xa.trans (h ⟨xa, xb⟩).2
      exact lt_irrefl _ (h ⟨ab, h'⟩).2,
    fun ⟨h₁, h₂⟩ => Ioo_subset_Ioo h₁ h₂⟩

@[to_dual]
/--
lemma `Ici_eq_singleton_iff_isTop` / 引理 `Ici_eq_singleton_iff_isTop`

English:
lemma Ici_eq_singleton_iff_isTop
  given: {x : α}
  statement: (Ici x = {x}) ↔ IsTop x
  proof: by
  refine ⟨fun h y => ?_, fun h => by ext y; simp [(h y).ge_iff_eq]⟩
  by_contra! H
  have : y in Ici x := H.le
  rw [h]; rw [mem_singleton_iff] at this
  exact lt_irrefl y (this.le.trans_lt H)

@[to_dual (attr := simp)]

中文:
引理 Ici_eq_singleton_iff_isTop
  条件: {x : α}
  结论: (左闭右无界区间 x = {x}) ↔ IsTop x
  证明: by
  refine ⟨fun h y => ?_, fun h => by ext y; simp [(h y).ge_iff_eq]⟩
  by_contra! H
  have : y in Ici x := H.le
  rw [h]; rw [mem_singleton_iff] at this
  exact lt_irrefl y (this.le.trans_lt H)

@[to_dual (attr := simp)]

Depends on / 依赖: H.le, ge_iff_eq, lt_irrefl, mem_singleton_iff, this.le.trans_lt, trans_lt
-/
lemma Ici_eq_singleton_iff_isTop {x : α} : (Ici x = {x}) ↔ IsTop x := by
  refine ⟨fun h y => ?_, fun h => by ext y; simp [(h y).ge_iff_eq]⟩
  by_contra! H
  have : y in Ici x := H.le
  rw [h]; rw [mem_singleton_iff] at this
  exact lt_irrefl y (this.le.trans_lt H)

@[to_dual (attr := simp)]
/--
theorem `Ioi_subset_Ioi_iff` / 定理 `Ioi_subset_Ioi_iff`

English:
theorem Ioi_subset_Ioi_iff
  statement: Ioi b subseteq Ioi a ↔ a <= b
  proof: by
  refine ⟨fun h => ?_, Ioi_subset_Ioi⟩
  by_contra ba
  exact lt_irrefl _ (h (not_le.mp ba))

@[to_dual (attr := simp)]

中文:
定理 Ioi_subset_Ioi_iff
  结论: 左开右无界区间 b subseteq 左开右无界区间 a ↔ a <= b
  证明: by
  refine ⟨fun h => ?_, Ioi_subset_Ioi⟩
  by_contra ba
  exact lt_irrefl _ (h (not_le.mp ba))

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_subset_Ioi, lt_irrefl, not_le, not_le.mp
-/
theorem Ioi_subset_Ioi_iff : Ioi b subseteq Ioi a ↔ a <= b := by
  refine ⟨fun h => ?_, Ioi_subset_Ioi⟩
  by_contra ba
  exact lt_irrefl _ (h (not_le.mp ba))

@[to_dual (attr := simp)]
/--
theorem `Ioi_ssubset_Ioi_iff` / 定理 `Ioi_ssubset_Ioi_iff`

English:
theorem Ioi_ssubset_Ioi_iff
  statement: Ioi b ⊂ Ioi a ↔ a < b
  proof: by
  refine ⟨fun h => ?_, Ioi_ssubset_Ioi⟩
  obtain ⟨_, c, ac, cb⟩ := ssubset_iff_exists.mp h
  exact ac.trans_le (le_of_not_gt cb)

@[to_dual (attr := simp)]

中文:
定理 Ioi_ssubset_Ioi_iff
  结论: 左开右无界区间 b ⊂ 左开右无界区间 a ↔ a < b
  证明: by
  refine ⟨fun h => ?_, Ioi_ssubset_Ioi⟩
  obtain ⟨_, c, ac, cb⟩ := ssubset_iff_exists.mp h
  exact ac.trans_le (le_of_not_gt cb)

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_ssubset_Ioi, ac.trans_le, le_of_not_gt, ssubset_iff_exists, ssubset_iff_exists.mp, trans_le
-/
theorem Ioi_ssubset_Ioi_iff : Ioi b ⊂ Ioi a ↔ a < b := by
  refine ⟨fun h => ?_, Ioi_ssubset_Ioi⟩
  obtain ⟨_, c, ac, cb⟩ := ssubset_iff_exists.mp h
  exact ac.trans_le (le_of_not_gt cb)

@[to_dual (attr := simp)]
/--
theorem `Ioi_subset_Ici_iff` / 定理 `Ioi_subset_Ici_iff`

English:
theorem Ioi_subset_Ici_iff
  given: [DenselyOrdered α]
  statement: Ioi b subseteq Ici a ↔ a <= b
  proof: by
  refine ⟨fun h => ?_, Ioi_subset_Ici⟩
  by_contra ba
  obtain ⟨c, bc, ca⟩ : exists c, b < c ∧ c < a := exists_between (not_le.mp ba)
  exact lt_irrefl _ (ca.trans_le (h bc))

中文:
定理 Ioi_subset_Ici_iff
  条件: [稠密序 α]
  结论: 左开右无界区间 b subseteq 左闭右无界区间 a ↔ a <= b
  证明: by
  refine ⟨fun h => ?_, Ioi_subset_Ici⟩
  by_contra ba
  obtain ⟨c, bc, ca⟩ : exists c, b < c ∧ c < a := exists_between (not_le.mp ba)
  exact lt_irrefl _ (ca.trans_le (h bc))

Depends on / 依赖: Ioi_subset_Ici, ca.trans_le, exists_between, lt_irrefl, not_le, not_le.mp, trans_le
-/
theorem Ioi_subset_Ici_iff [DenselyOrdered α] : Ioi b subseteq Ici a ↔ a <= b := by
  refine ⟨fun h => ?_, Ioi_subset_Ici⟩
  by_contra ba
  obtain ⟨c, bc, ca⟩ : exists c, b < c ∧ c < a := exists_between (not_le.mp ba)
  exact lt_irrefl _ (ca.trans_le (h bc))

/-! ### Two infinite intervals -/

@[to_dual]
/--
theorem `Iic_union_Ioi_of_le` / 定理 `Iic_union_Ioi_of_le`

English:
theorem Iic_union_Ioi_of_le
  given: (h : a <= b)
  statement: Iic b union Ioi a = univ
  proof: eq_univ_of_forall fun x => (h.gt_or_le x).symm

@[to_dual]

中文:
定理 Iic_union_Ioi_of_le
  条件: (h : a <= b)
  结论: 左无界右闭区间 b union 左开右无界区间 a = univ
  证明: eq_univ_of_forall fun x => (h.gt_or_le x).symm

@[to_dual]

Depends on / 依赖: eq_univ_of_forall, gt_or_le, h.gt_or_le
-/
theorem Iic_union_Ioi_of_le (h : a <= b) : Iic b union Ioi a = univ :=
  eq_univ_of_forall fun x => (h.gt_or_le x).symm

@[to_dual]
/--
theorem `Iio_union_Ici_of_le` / 定理 `Iio_union_Ici_of_le`

English:
theorem Iio_union_Ici_of_le
  given: (h : a <= b)
  statement: Iio b union Ici a = univ
  proof: eq_univ_of_forall fun x => (h.ge_or_lt x).symm

@[to_dual]

中文:
定理 Iio_union_Ici_of_le
  条件: (h : a <= b)
  结论: 左无界右开区间 b union 左闭右无界区间 a = univ
  证明: eq_univ_of_forall fun x => (h.ge_or_lt x).symm

@[to_dual]

Depends on / 依赖: eq_univ_of_forall, ge_or_lt, h.ge_or_lt
-/
theorem Iio_union_Ici_of_le (h : a <= b) : Iio b union Ici a = univ :=
  eq_univ_of_forall fun x => (h.ge_or_lt x).symm

@[to_dual]
/--
theorem `Iic_union_Ici_of_le` / 定理 `Iic_union_Ici_of_le`

English:
theorem Iic_union_Ici_of_le
  given: (h : a <= b)
  statement: Iic b union Ici a = univ
  proof: eq_univ_of_forall fun x => (h.ge_or_le x).symm

@[to_dual]

中文:
定理 Iic_union_Ici_of_le
  条件: (h : a <= b)
  结论: 左无界右闭区间 b union 左闭右无界区间 a = univ
  证明: eq_univ_of_forall fun x => (h.ge_or_le x).symm

@[to_dual]

Depends on / 依赖: eq_univ_of_forall, ge_or_le, h.ge_or_le
-/
theorem Iic_union_Ici_of_le (h : a <= b) : Iic b union Ici a = univ :=
  eq_univ_of_forall fun x => (h.ge_or_le x).symm

@[to_dual]
/--
theorem `Iio_union_Ioi_of_lt` / 定理 `Iio_union_Ioi_of_lt`

English:
theorem Iio_union_Ioi_of_lt
  given: (h : a < b)
  statement: Iio b union Ioi a = univ
  proof: eq_univ_of_forall fun x => (h.gt_or_lt x).symm

@[to_dual (attr := simp)]

中文:
定理 Iio_union_Ioi_of_lt
  条件: (h : a < b)
  结论: 左无界右开区间 b union 左开右无界区间 a = univ
  证明: eq_univ_of_forall fun x => (h.gt_or_lt x).symm

@[to_dual (attr := simp)]

Depends on / 依赖: eq_univ_of_forall, gt_or_lt, h.gt_or_lt
-/
theorem Iio_union_Ioi_of_lt (h : a < b) : Iio b union Ioi a = univ :=
  eq_univ_of_forall fun x => (h.gt_or_lt x).symm

@[to_dual (attr := simp)]
/--
theorem `Iic_union_Ici` / 定理 `Iic_union_Ici`

English:
theorem Iic_union_Ici
  statement: Iic a union Ici a = univ
  proof: Iic_union_Ici_of_le le_rfl

@[to_dual (attr := simp)]

中文:
定理 Iic_union_Ici
  结论: 左无界右闭区间 a union 左闭右无界区间 a = univ
  证明: Iic_union_Ici_of_le le_rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iic_union_Ici_of_le, le_rfl
-/
theorem Iic_union_Ici : Iic a union Ici a = univ :=
  Iic_union_Ici_of_le le_rfl

@[to_dual (attr := simp)]
/--
theorem `Iio_union_Ici` / 定理 `Iio_union_Ici`

English:
theorem Iio_union_Ici
  statement: Iio a union Ici a = univ
  proof: Iio_union_Ici_of_le le_rfl

@[to_dual (attr := simp)]

中文:
定理 Iio_union_Ici
  结论: 左无界右开区间 a union 左闭右无界区间 a = univ
  证明: Iio_union_Ici_of_le le_rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iio_union_Ici_of_le, le_rfl
-/
theorem Iio_union_Ici : Iio a union Ici a = univ :=
  Iio_union_Ici_of_le le_rfl

@[to_dual (attr := simp)]
/--
theorem `Iic_union_Ioi` / 定理 `Iic_union_Ioi`

English:
theorem Iic_union_Ioi
  statement: Iic a union Ioi a = univ
  proof: Iic_union_Ioi_of_le le_rfl

@[to_dual (attr := simp)]

中文:
定理 Iic_union_Ioi
  结论: 左无界右闭区间 a union 左开右无界区间 a = univ
  证明: Iic_union_Ioi_of_le le_rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iic_union_Ioi_of_le, le_rfl
-/
theorem Iic_union_Ioi : Iic a union Ioi a = univ :=
  Iic_union_Ioi_of_le le_rfl

@[to_dual (attr := simp)]
/--
theorem `Iio_union_Ioi` / 定理 `Iio_union_Ioi`

English:
theorem Iio_union_Ioi
  statement: Iio a union Ioi a = {a}ᶜ
  proof: ext fun _ => lt_or_lt_iff_ne

中文:
定理 Iio_union_Ioi
  结论: 左无界右开区间 a union 左开右无界区间 a = {a}ᶜ
  证明: ext fun _ => lt_or_lt_iff_ne

Depends on / 依赖: lt_or_lt_iff_ne
-/
theorem Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ :=
  ext fun _ => lt_or_lt_iff_ne


/--
theorem `Ioo_union_Ioi` / 定理 `Ioo_union_Ioi`

English:
theorem Ioo_union_Ioi
  given: (h : c < max a b)
  statement: Ioo a b union Ioi c = Ioi (min a c)
  proof: by
  grind

@[deprecated Ioo_union_Ioi (since := "2026-02-22")]

中文:
定理 Ioo_union_Ioi
  条件: (h : c < 最大值 a b)
  结论: 开区间 a b union 左开右无界区间 c = 左开右无界区间 (最小值 a c)
  证明: by
  grind

@[deprecated Ioo_union_Ioi (since := "2026-02-22")]
-/
theorem Ioo_union_Ioi (h : c < max a b) : Ioo a b union Ioi c = Ioi (min a c) := by
  grind

@[deprecated Ioo_union_Ioi (since := "2026-02-22")]
/--
theorem `Ioo_union_Ioi'` / 定理 `Ioo_union_Ioi'`

English:
theorem Ioo_union_Ioi'
  given: (h₁ : c < b)
  statement: Ioo a b union Ioi c = Ioi (min a c)
  proof: Ioo_union_Ioi (h₁.trans_le (le_max_right ..))

中文:
定理 Ioo_union_Ioi'
  条件: (h₁ : c < b)
  结论: 开区间 a b union 左开右无界区间 c = 左开右无界区间 (最小值 a c)
  证明: Ioo_union_Ioi (h₁.trans_le (le_max_right ..))

Depends on / 依赖: Ioo_union_Ioi, le_max_right, trans_le
-/
theorem Ioo_union_Ioi' (h₁ : c < b) : Ioo a b union Ioi c = Ioi (min a c) :=
  Ioo_union_Ioi (h₁.trans_le (le_max_right ..))

/--
theorem `Ioi_subset_Ioo_union_Ici` / 定理 `Ioi_subset_Ioo_union_Ici`

English:
theorem Ioi_subset_Ioo_union_Ici
  statement: Ioi a subseteq Ioo a b union Ici b
  proof: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]

中文:
定理 Ioi_subset_Ioo_union_Ici
  结论: 左开右无界区间 a subseteq 开区间 a b union 左闭右无界区间 b
  证明: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
-/
theorem Ioi_subset_Ioo_union_Ici : Ioi a subseteq Ioo a b union Ici b := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
/--
theorem `Ioo_union_Ici_eq_Ioi` / 定理 `Ioo_union_Ici_eq_Ioi`

English:
theorem Ioo_union_Ici_eq_Ioi
  given: (h : a < b)
  statement: Ioo a b union Ici b = Ioi a
  proof: Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioo_union_Ici

中文:
定理 Ioo_union_Ici_eq_Ioi
  条件: (h : a < b)
  结论: 开区间 a b union 左闭右无界区间 b = 左开右无界区间 a
  证明: Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioo_union_Ici

Depends on / 依赖: And.left, Ioi_subset_Ioo_union_Ici, Subset, Subset.antisymm, antisymm, h.trans_le, hx.elim, trans_le
-/
theorem Ioo_union_Ici_eq_Ioi (h : a < b) : Ioo a b union Ici b = Ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioo_union_Ici

/--
theorem `Ici_subset_Ico_union_Ici` / 定理 `Ici_subset_Ico_union_Ici`

English:
theorem Ici_subset_Ico_union_Ici
  statement: Ici a subseteq Ico a b union Ici b
  proof: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]

中文:
定理 Ici_subset_Ico_union_Ici
  结论: 左闭右无界区间 a subseteq 左闭右开区间 a b union 左闭右无界区间 b
  证明: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
-/
theorem Ici_subset_Ico_union_Ici : Ici a subseteq Ico a b union Ici b := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
/--
theorem `Ico_union_Ici_eq_Ici` / 定理 `Ico_union_Ici_eq_Ici`

English:
theorem Ico_union_Ici_eq_Ici
  given: (h : a <= b)
  statement: Ico a b union Ici b = Ici a
  proof: Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Ico_union_Ici

中文:
定理 Ico_union_Ici_eq_Ici
  条件: (h : a <= b)
  结论: 左闭右开区间 a b union 左闭右无界区间 b = 左闭右无界区间 a
  证明: Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Ico_union_Ici

Depends on / 依赖: And.left, Ici_subset_Ico_union_Ici, Subset, Subset.antisymm, antisymm, h.trans, hx.elim
-/
theorem Ico_union_Ici_eq_Ici (h : a <= b) : Ico a b union Ici b = Ici a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Ico_union_Ici

/--
theorem `Ico_union_Ici` / 定理 `Ico_union_Ici`

English:
theorem Ico_union_Ici
  given: (h : c <= max a b)
  statement: Ico a b union Ici c = Ici (min a c)
  proof: by
  grind

@[deprecated Ico_union_Ici (since := "2026-02-22")]

中文:
定理 Ico_union_Ici
  条件: (h : c <= 最大值 a b)
  结论: 左闭右开区间 a b union 左闭右无界区间 c = 左闭右无界区间 (最小值 a c)
  证明: by
  grind

@[deprecated Ico_union_Ici (since := "2026-02-22")]
-/
theorem Ico_union_Ici (h : c <= max a b) : Ico a b union Ici c = Ici (min a c) := by
  grind

@[deprecated Ico_union_Ici (since := "2026-02-22")]
/--
theorem `Ico_union_Ici'` / 定理 `Ico_union_Ici'`

English:
theorem Ico_union_Ici'
  given: (h₁ : c <= b)
  statement: Ico a b union Ici c = Ici (min a c)
  proof: Ico_union_Ici (h₁.trans (le_max_right ..))

中文:
定理 Ico_union_Ici'
  条件: (h₁ : c <= b)
  结论: 左闭右开区间 a b union 左闭右无界区间 c = 左闭右无界区间 (最小值 a c)
  证明: Ico_union_Ici (h₁.trans (le_max_right ..))

Depends on / 依赖: Ico_union_Ici, le_max_right
-/
theorem Ico_union_Ici' (h₁ : c <= b) : Ico a b union Ici c = Ici (min a c) :=
  Ico_union_Ici (h₁.trans (le_max_right ..))

/--
theorem `Ioi_subset_Ioc_union_Ioi` / 定理 `Ioi_subset_Ioc_union_Ioi`

English:
theorem Ioi_subset_Ioc_union_Ioi
  statement: Ioi a subseteq Ioc a b union Ioi b
  proof: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]

中文:
定理 Ioi_subset_Ioc_union_Ioi
  结论: 左开右无界区间 a subseteq 左开右闭区间 a b union 左开右无界区间 b
  证明: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
-/
theorem Ioi_subset_Ioc_union_Ioi : Ioi a subseteq Ioc a b union Ioi b := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
/--
theorem `Ioc_union_Ioi_eq_Ioi` / 定理 `Ioc_union_Ioi_eq_Ioi`

English:
theorem Ioc_union_Ioi_eq_Ioi
  given: (h : a <= b)
  statement: Ioc a b union Ioi b = Ioi a
  proof: Subset.antisymm (fun _ hx => hx.elim And.left h.trans_lt) Ioi_subset_Ioc_union_Ioi

中文:
定理 Ioc_union_Ioi_eq_Ioi
  条件: (h : a <= b)
  结论: 左开右闭区间 a b union 左开右无界区间 b = 左开右无界区间 a
  证明: Subset.antisymm (fun _ hx => hx.elim And.left h.trans_lt) Ioi_subset_Ioc_union_Ioi

Depends on / 依赖: And.left, Ioi_subset_Ioc_union_Ioi, Subset, Subset.antisymm, antisymm, h.trans_lt, hx.elim, trans_lt
-/
theorem Ioc_union_Ioi_eq_Ioi (h : a <= b) : Ioc a b union Ioi b = Ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_lt) Ioi_subset_Ioc_union_Ioi

/--
theorem `Ioc_union_Ioi` / 定理 `Ioc_union_Ioi`

English:
theorem Ioc_union_Ioi
  given: (h : c <= max a b)
  statement: Ioc a b union Ioi c = Ioi (min a c)
  proof: by
  grind

@[deprecated Ioc_union_Ioi (since := "2026-02-22")]

中文:
定理 Ioc_union_Ioi
  条件: (h : c <= 最大值 a b)
  结论: 左开右闭区间 a b union 左开右无界区间 c = 左开右无界区间 (最小值 a c)
  证明: by
  grind

@[deprecated Ioc_union_Ioi (since := "2026-02-22")]
-/
theorem Ioc_union_Ioi (h : c <= max a b) : Ioc a b union Ioi c = Ioi (min a c) := by
  grind

@[deprecated Ioc_union_Ioi (since := "2026-02-22")]
/--
theorem `Ioc_union_Ioi'` / 定理 `Ioc_union_Ioi'`

English:
theorem Ioc_union_Ioi'
  given: (h₁ : c <= b)
  statement: Ioc a b union Ioi c = Ioi (min a c)
  proof: Ioc_union_Ioi (h₁.trans (le_max_right ..))

中文:
定理 Ioc_union_Ioi'
  条件: (h₁ : c <= b)
  结论: 左开右闭区间 a b union 左开右无界区间 c = 左开右无界区间 (最小值 a c)
  证明: Ioc_union_Ioi (h₁.trans (le_max_right ..))

Depends on / 依赖: Ioc_union_Ioi, le_max_right
-/
theorem Ioc_union_Ioi' (h₁ : c <= b) : Ioc a b union Ioi c = Ioi (min a c) :=
  Ioc_union_Ioi (h₁.trans (le_max_right ..))

/--
theorem `Ici_subset_Icc_union_Ioi` / 定理 `Ici_subset_Icc_union_Ioi`

English:
theorem Ici_subset_Icc_union_Ioi
  statement: Ici a subseteq Icc a b union Ioi b
  proof: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]

中文:
定理 Ici_subset_Icc_union_Ioi
  结论: 左闭右无界区间 a subseteq 闭区间 a b union 左开右无界区间 b
  证明: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
-/
theorem Ici_subset_Icc_union_Ioi : Ici a subseteq Icc a b union Ioi b := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
/--
theorem `Icc_union_Ioi_eq_Ici` / 定理 `Icc_union_Ioi_eq_Ici`

English:
theorem Icc_union_Ioi_eq_Ici
  given: (h : a <= b)
  statement: Icc a b union Ioi b = Ici a
  proof: Subset.antisymm (fun _ hx => (hx.elim And.left) fun hx' => h.trans <| le_of_lt hx')
    Ici_subset_Icc_union_Ioi

中文:
定理 Icc_union_Ioi_eq_Ici
  条件: (h : a <= b)
  结论: 闭区间 a b union 左开右无界区间 b = 左闭右无界区间 a
  证明: Subset.antisymm (fun _ hx => (hx.elim And.left) fun hx' => h.trans <| le_of_lt hx')
    Ici_subset_Icc_union_Ioi

Depends on / 依赖: And.left, Ici_subset_Icc_union_Ioi, Subset, Subset.antisymm, antisymm, h.trans, hx.elim, le_of_lt
-/
theorem Icc_union_Ioi_eq_Ici (h : a <= b) : Icc a b union Ioi b = Ici a :=
  Subset.antisymm (fun _ hx => (hx.elim And.left) fun hx' => h.trans <| le_of_lt hx')
    Ici_subset_Icc_union_Ioi

/--
theorem `Ioi_subset_Ioc_union_Ici` / 定理 `Ioi_subset_Ioc_union_Ici`

English:
theorem Ioi_subset_Ioc_union_Ici
  statement: Ioi a subseteq Ioc a b union Ici b
  proof: Subset.trans Ioi_subset_Ioo_union_Ici (union_subset_union_left _ Ioo_subset_Ioc_self)

@[simp]

中文:
定理 Ioi_subset_Ioc_union_Ici
  结论: 左开右无界区间 a subseteq 左开右闭区间 a b union 左闭右无界区间 b
  证明: Subset.trans Ioi_subset_Ioo_union_Ici (union_subset_union_left _ Ioo_subset_Ioc_self)

@[simp]

Depends on / 依赖: Ioi_subset_Ioo_union_Ici, Ioo_subset_Ioc_self, Subset, Subset.trans, union_subset_union_left
-/
theorem Ioi_subset_Ioc_union_Ici : Ioi a subseteq Ioc a b union Ici b :=
  Subset.trans Ioi_subset_Ioo_union_Ici (union_subset_union_left _ Ioo_subset_Ioc_self)

@[simp]
/--
theorem `Ioc_union_Ici_eq_Ioi` / 定理 `Ioc_union_Ici_eq_Ioi`

English:
theorem Ioc_union_Ici_eq_Ioi
  given: (h : a < b)
  statement: Ioc a b union Ici b = Ioi a
  proof: Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioc_union_Ici

中文:
定理 Ioc_union_Ici_eq_Ioi
  条件: (h : a < b)
  结论: 左开右闭区间 a b union 左闭右无界区间 b = 左开右无界区间 a
  证明: Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioc_union_Ici

Depends on / 依赖: And.left, Ioi_subset_Ioc_union_Ici, Subset, Subset.antisymm, antisymm, h.trans_le, hx.elim, trans_le
-/
theorem Ioc_union_Ici_eq_Ioi (h : a < b) : Ioc a b union Ici b = Ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioc_union_Ici

/--
theorem `Ici_subset_Icc_union_Ici` / 定理 `Ici_subset_Icc_union_Ici`

English:
theorem Ici_subset_Icc_union_Ici
  statement: Ici a subseteq Icc a b union Ici b
  proof: Subset.trans Ici_subset_Ico_union_Ici (union_subset_union_left _ Ico_subset_Icc_self)

@[simp]

中文:
定理 Ici_subset_Icc_union_Ici
  结论: 左闭右无界区间 a subseteq 闭区间 a b union 左闭右无界区间 b
  证明: Subset.trans Ici_subset_Ico_union_Ici (union_subset_union_left _ Ico_subset_Icc_self)

@[simp]

Depends on / 依赖: Ici_subset_Ico_union_Ici, Ico_subset_Icc_self, Subset, Subset.trans, union_subset_union_left
-/
theorem Ici_subset_Icc_union_Ici : Ici a subseteq Icc a b union Ici b :=
  Subset.trans Ici_subset_Ico_union_Ici (union_subset_union_left _ Ico_subset_Icc_self)

@[simp]
/--
theorem `Icc_union_Ici_eq_Ici` / 定理 `Icc_union_Ici_eq_Ici`

English:
theorem Icc_union_Ici_eq_Ici
  given: (h : a <= b)
  statement: Icc a b union Ici b = Ici a
  proof: Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Icc_union_Ici

中文:
定理 Icc_union_Ici_eq_Ici
  条件: (h : a <= b)
  结论: 闭区间 a b union 左闭右无界区间 b = 左闭右无界区间 a
  证明: Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Icc_union_Ici

Depends on / 依赖: And.left, Ici_subset_Icc_union_Ici, Subset, Subset.antisymm, antisymm, h.trans, hx.elim
-/
theorem Icc_union_Ici_eq_Ici (h : a <= b) : Icc a b union Ici b = Ici a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Icc_union_Ici

/--
theorem `Icc_union_Ici` / 定理 `Icc_union_Ici`

English:
theorem Icc_union_Ici
  given: (h : c <= max a b)
  statement: Icc a b union Ici c = Ici (min a c)
  proof: by
  grind

@[deprecated Icc_union_Ici (since := "2026-02-22")]

中文:
定理 Icc_union_Ici
  条件: (h : c <= 最大值 a b)
  结论: 闭区间 a b union 左闭右无界区间 c = 左闭右无界区间 (最小值 a c)
  证明: by
  grind

@[deprecated Icc_union_Ici (since := "2026-02-22")]
-/
theorem Icc_union_Ici (h : c <= max a b) : Icc a b union Ici c = Ici (min a c) := by
  grind

@[deprecated Icc_union_Ici (since := "2026-02-22")]
/--
theorem `Icc_union_Ici'` / 定理 `Icc_union_Ici'`

English:
theorem Icc_union_Ici'
  given: (h₁ : c <= b)
  statement: Icc a b union Ici c = Ici (min a c)
  proof: Icc_union_Ici (h₁.trans (le_max_right ..))

中文:
定理 Icc_union_Ici'
  条件: (h₁ : c <= b)
  结论: 闭区间 a b union 左闭右无界区间 c = 左闭右无界区间 (最小值 a c)
  证明: Icc_union_Ici (h₁.trans (le_max_right ..))

Depends on / 依赖: Icc_union_Ici, le_max_right
-/
theorem Icc_union_Ici' (h₁ : c <= b) : Icc a b union Ici c = Ici (min a c) :=
  Icc_union_Ici (h₁.trans (le_max_right ..))


/--
theorem `Iic_subset_Iio_union_Icc` / 定理 `Iic_subset_Iio_union_Icc`

English:
theorem Iic_subset_Iio_union_Icc
  statement: Iic b subseteq Iio a union Icc a b
  proof: fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]

中文:
定理 Iic_subset_Iio_union_Icc
  结论: 左无界右闭区间 b subseteq 左无界右开区间 a union 闭区间 a b
  证明: fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
-/
theorem Iic_subset_Iio_union_Icc : Iic b subseteq Iio a union Icc a b := fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
/--
theorem `Iio_union_Icc_eq_Iic` / 定理 `Iio_union_Icc_eq_Iic`

English:
theorem Iio_union_Icc_eq_Iic
  given: (h : a <= b)
  statement: Iio a union Icc a b = Iic b
  proof: Subset.antisymm (fun _ hx => hx.elim (fun hx => (le_of_lt hx).trans h) And.right)
    Iic_subset_Iio_union_Icc

中文:
定理 Iio_union_Icc_eq_Iic
  条件: (h : a <= b)
  结论: 左无界右开区间 a union 闭区间 a b = 左无界右闭区间 b
  证明: Subset.antisymm (fun _ hx => hx.elim (fun hx => (le_of_lt hx).trans h) And.right)
    Iic_subset_Iio_union_Icc

Depends on / 依赖: And.right, Iic_subset_Iio_union_Icc, Subset, Subset.antisymm, antisymm, hx.elim, le_of_lt
-/
theorem Iio_union_Icc_eq_Iic (h : a <= b) : Iio a union Icc a b = Iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx => (le_of_lt hx).trans h) And.right)
    Iic_subset_Iio_union_Icc

/--
theorem `Iio_subset_Iio_union_Ico` / 定理 `Iio_subset_Iio_union_Ico`

English:
theorem Iio_subset_Iio_union_Ico
  statement: Iio b subseteq Iio a union Ico a b
  proof: fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]

中文:
定理 Iio_subset_Iio_union_Ico
  结论: 左无界右开区间 b subseteq 左无界右开区间 a union 左闭右开区间 a b
  证明: fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
-/
theorem Iio_subset_Iio_union_Ico : Iio b subseteq Iio a union Ico a b := fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
/--
theorem `Iio_union_Ico_eq_Iio` / 定理 `Iio_union_Ico_eq_Iio`

English:
theorem Iio_union_Ico_eq_Iio
  given: (h : a <= b)
  statement: Iio a union Ico a b = Iio b
  proof: Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_lt_of_le hx' h) And.right)
    Iio_subset_Iio_union_Ico

中文:
定理 Iio_union_Ico_eq_Iio
  条件: (h : a <= b)
  结论: 左无界右开区间 a union 左闭右开区间 a b = 左无界右开区间 b
  证明: Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_lt_of_le hx' h) And.right)
    Iio_subset_Iio_union_Ico

Depends on / 依赖: And.right, Iio_subset_Iio_union_Ico, Subset, Subset.antisymm, antisymm, hx.elim, lt_of_lt_of_le
-/
theorem Iio_union_Ico_eq_Iio (h : a <= b) : Iio a union Ico a b = Iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_lt_of_le hx' h) And.right)
    Iio_subset_Iio_union_Ico

/--
theorem `Iio_union_Ico` / 定理 `Iio_union_Ico`

English:
theorem Iio_union_Ico
  given: (h : min c d <= b)
  statement: Iio b union Ico c d = Iio (max b d)
  proof: by
  grind

@[deprecated Iio_union_Ico (since := "2026-02-22")]

中文:
定理 Iio_union_Ico
  条件: (h : 最小值 c d <= b)
  结论: 左无界右开区间 b union 左闭右开区间 c d = 左无界右开区间 (最大值 b d)
  证明: by
  grind

@[deprecated Iio_union_Ico (since := "2026-02-22")]
-/
theorem Iio_union_Ico (h : min c d <= b) : Iio b union Ico c d = Iio (max b d) := by
  grind

@[deprecated Iio_union_Ico (since := "2026-02-22")]
/--
theorem `Iio_union_Ico'` / 定理 `Iio_union_Ico'`

English:
theorem Iio_union_Ico'
  given: (h₁ : c <= b)
  statement: Iio b union Ico c d = Iio (max b d)
  proof: Iio_union_Ico ((min_le_left ..).trans h₁)

中文:
定理 Iio_union_Ico'
  条件: (h₁ : c <= b)
  结论: 左无界右开区间 b union 左闭右开区间 c d = 左无界右开区间 (最大值 b d)
  证明: Iio_union_Ico ((min_le_left ..).trans h₁)

Depends on / 依赖: Iio_union_Ico, min_le_left
-/
theorem Iio_union_Ico' (h₁ : c <= b) : Iio b union Ico c d = Iio (max b d) :=
  Iio_union_Ico ((min_le_left ..).trans h₁)

/--
theorem `Iic_subset_Iic_union_Ioc` / 定理 `Iic_subset_Iic_union_Ioc`

English:
theorem Iic_subset_Iic_union_Ioc
  statement: Iic b subseteq Iic a union Ioc a b
  proof: fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]

中文:
定理 Iic_subset_Iic_union_Ioc
  结论: 左无界右闭区间 b subseteq 左无界右闭区间 a union 左开右闭区间 a b
  证明: fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
-/
theorem Iic_subset_Iic_union_Ioc : Iic b subseteq Iic a union Ioc a b := fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
/--
theorem `Iic_union_Ioc_eq_Iic` / 定理 `Iic_union_Ioc_eq_Iic`

English:
theorem Iic_union_Ioc_eq_Iic
  given: (h : a <= b)
  statement: Iic a union Ioc a b = Iic b
  proof: Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Ioc

中文:
定理 Iic_union_Ioc_eq_Iic
  条件: (h : a <= b)
  结论: 左无界右闭区间 a union 左开右闭区间 a b = 左无界右闭区间 b
  证明: Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Ioc

Depends on / 依赖: And.right, Iic_subset_Iic_union_Ioc, Subset, Subset.antisymm, antisymm, hx.elim, le_trans
-/
theorem Iic_union_Ioc_eq_Iic (h : a <= b) : Iic a union Ioc a b = Iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Ioc

/--
theorem `Iic_union_Ioc` / 定理 `Iic_union_Ioc`

English:
theorem Iic_union_Ioc
  given: (h : min c d < b)
  statement: Iic b union Ioc c d = Iic (max b d)
  proof: by
  grind

@[deprecated Iic_union_Ioc (since := "2026-02-22")]

中文:
定理 Iic_union_Ioc
  条件: (h : 最小值 c d < b)
  结论: 左无界右闭区间 b union 左开右闭区间 c d = 左无界右闭区间 (最大值 b d)
  证明: by
  grind

@[deprecated Iic_union_Ioc (since := "2026-02-22")]
-/
theorem Iic_union_Ioc (h : min c d < b) : Iic b union Ioc c d = Iic (max b d) := by
  grind

@[deprecated Iic_union_Ioc (since := "2026-02-22")]
/--
theorem `Iic_union_Ioc'` / 定理 `Iic_union_Ioc'`

English:
theorem Iic_union_Ioc'
  given: (h₁ : c < b)
  statement: Iic b union Ioc c d = Iic (max b d)
  proof: Iic_union_Ioc ((min_le_left ..).trans_lt h₁)

中文:
定理 Iic_union_Ioc'
  条件: (h₁ : c < b)
  结论: 左无界右闭区间 b union 左开右闭区间 c d = 左无界右闭区间 (最大值 b d)
  证明: Iic_union_Ioc ((min_le_left ..).trans_lt h₁)

Depends on / 依赖: Iic_union_Ioc, min_le_left, trans_lt
-/
theorem Iic_union_Ioc' (h₁ : c < b) : Iic b union Ioc c d = Iic (max b d) :=
  Iic_union_Ioc ((min_le_left ..).trans_lt h₁)

/--
theorem `Iio_subset_Iic_union_Ioo` / 定理 `Iio_subset_Iic_union_Ioo`

English:
theorem Iio_subset_Iic_union_Ioo
  statement: Iio b subseteq Iic a union Ioo a b
  proof: fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]

中文:
定理 Iio_subset_Iic_union_Ioo
  结论: 左无界右开区间 b subseteq 左无界右闭区间 a union 开区间 a b
  证明: fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
-/
theorem Iio_subset_Iic_union_Ioo : Iio b subseteq Iic a union Ioo a b := fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
/--
theorem `Iic_union_Ioo_eq_Iio` / 定理 `Iic_union_Ioo_eq_Iio`

English:
theorem Iic_union_Ioo_eq_Iio
  given: (h : a < b)
  statement: Iic a union Ioo a b = Iio b
  proof: Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ioo

中文:
定理 Iic_union_Ioo_eq_Iio
  条件: (h : a < b)
  结论: 左无界右闭区间 a union 开区间 a b = 左无界右开区间 b
  证明: Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ioo

Depends on / 依赖: And.right, Iio_subset_Iic_union_Ioo, Subset, Subset.antisymm, antisymm, hx.elim, lt_of_le_of_lt
-/
theorem Iic_union_Ioo_eq_Iio (h : a < b) : Iic a union Ioo a b = Iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ioo

/--
theorem `Iio_union_Ioo` / 定理 `Iio_union_Ioo`

English:
theorem Iio_union_Ioo
  given: (h : min c d < b)
  statement: Iio b union Ioo c d = Iio (max b d)
  proof: by
  grind

@[deprecated Iio_union_Ioo (since := "2026-02-22")]

中文:
定理 Iio_union_Ioo
  条件: (h : 最小值 c d < b)
  结论: 左无界右开区间 b union 开区间 c d = 左无界右开区间 (最大值 b d)
  证明: by
  grind

@[deprecated Iio_union_Ioo (since := "2026-02-22")]
-/
theorem Iio_union_Ioo (h : min c d < b) : Iio b union Ioo c d = Iio (max b d) := by
  grind

@[deprecated Iio_union_Ioo (since := "2026-02-22")]
/--
theorem `Iio_union_Ioo'` / 定理 `Iio_union_Ioo'`

English:
theorem Iio_union_Ioo'
  given: (h₁ : c < b)
  statement: Iio b union Ioo c d = Iio (max b d)
  proof: Iio_union_Ioo ((min_le_left ..).trans_lt h₁)

中文:
定理 Iio_union_Ioo'
  条件: (h₁ : c < b)
  结论: 左无界右开区间 b union 开区间 c d = 左无界右开区间 (最大值 b d)
  证明: Iio_union_Ioo ((min_le_left ..).trans_lt h₁)

Depends on / 依赖: Iio_union_Ioo, min_le_left, trans_lt
-/
theorem Iio_union_Ioo' (h₁ : c < b) : Iio b union Ioo c d = Iio (max b d) :=
  Iio_union_Ioo ((min_le_left ..).trans_lt h₁)

/--
theorem `Iic_subset_Iic_union_Icc` / 定理 `Iic_subset_Iic_union_Icc`

English:
theorem Iic_subset_Iic_union_Icc
  statement: Iic b subseteq Iic a union Icc a b
  proof: Subset.trans Iic_subset_Iic_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]

中文:
定理 Iic_subset_Iic_union_Icc
  结论: 左无界右闭区间 b subseteq 左无界右闭区间 a union 闭区间 a b
  证明: Subset.trans Iic_subset_Iic_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]

Depends on / 依赖: Iic_subset_Iic_union_Ioc, Ioc_subset_Icc_self, Subset, Subset.trans, union_subset_union_right
-/
theorem Iic_subset_Iic_union_Icc : Iic b subseteq Iic a union Icc a b :=
  Subset.trans Iic_subset_Iic_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
/--
theorem `Iic_union_Icc_eq_Iic` / 定理 `Iic_union_Icc_eq_Iic`

English:
theorem Iic_union_Icc_eq_Iic
  given: (h : a <= b)
  statement: Iic a union Icc a b = Iic b
  proof: Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Icc

中文:
定理 Iic_union_Icc_eq_Iic
  条件: (h : a <= b)
  结论: 左无界右闭区间 a union 闭区间 a b = 左无界右闭区间 b
  证明: Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Icc

Depends on / 依赖: And.right, Iic_subset_Iic_union_Icc, Subset, Subset.antisymm, antisymm, hx.elim, le_trans
-/
theorem Iic_union_Icc_eq_Iic (h : a <= b) : Iic a union Icc a b = Iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Icc

/--
theorem `Iic_union_Icc` / 定理 `Iic_union_Icc`

English:
theorem Iic_union_Icc
  given: (h : min c d <= b)
  statement: Iic b union Icc c d = Iic (max b d)
  proof: by
  grind

@[deprecated Iic_union_Icc (since := "2026-02-22")]

中文:
定理 Iic_union_Icc
  条件: (h : 最小值 c d <= b)
  结论: 左无界右闭区间 b union 闭区间 c d = 左无界右闭区间 (最大值 b d)
  证明: by
  grind

@[deprecated Iic_union_Icc (since := "2026-02-22")]
-/
theorem Iic_union_Icc (h : min c d <= b) : Iic b union Icc c d = Iic (max b d) := by
  grind

@[deprecated Iic_union_Icc (since := "2026-02-22")]
/--
theorem `Iic_union_Icc'` / 定理 `Iic_union_Icc'`

English:
theorem Iic_union_Icc'
  given: (h₁ : c <= b)
  statement: Iic b union Icc c d = Iic (max b d)
  proof: Iic_union_Icc ((min_le_left ..).trans h₁)

中文:
定理 Iic_union_Icc'
  条件: (h₁ : c <= b)
  结论: 左无界右闭区间 b union 闭区间 c d = 左无界右闭区间 (最大值 b d)
  证明: Iic_union_Icc ((min_le_left ..).trans h₁)

Depends on / 依赖: Iic_union_Icc, min_le_left
-/
theorem Iic_union_Icc' (h₁ : c <= b) : Iic b union Icc c d = Iic (max b d) :=
  Iic_union_Icc ((min_le_left ..).trans h₁)

/--
theorem `Iio_subset_Iic_union_Ico` / 定理 `Iio_subset_Iic_union_Ico`

English:
theorem Iio_subset_Iic_union_Ico
  statement: Iio b subseteq Iic a union Ico a b
  proof: Subset.trans Iio_subset_Iic_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]

中文:
定理 Iio_subset_Iic_union_Ico
  结论: 左无界右开区间 b subseteq 左无界右闭区间 a union 左闭右开区间 a b
  证明: Subset.trans Iio_subset_Iic_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]

Depends on / 依赖: Iio_subset_Iic_union_Ioo, Ioo_subset_Ico_self, Subset, Subset.trans, union_subset_union_right
-/
theorem Iio_subset_Iic_union_Ico : Iio b subseteq Iic a union Ico a b :=
  Subset.trans Iio_subset_Iic_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
/--
theorem `Iic_union_Ico_eq_Iio` / 定理 `Iic_union_Ico_eq_Iio`

English:
theorem Iic_union_Ico_eq_Iio
  given: (h : a < b)
  statement: Iic a union Ico a b = Iio b
  proof: Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ico

中文:
定理 Iic_union_Ico_eq_Iio
  条件: (h : a < b)
  结论: 左无界右闭区间 a union 左闭右开区间 a b = 左无界右开区间 b
  证明: Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ico

Depends on / 依赖: And.right, Iio_subset_Iic_union_Ico, Subset, Subset.antisymm, antisymm, hx.elim, lt_of_le_of_lt
-/
theorem Iic_union_Ico_eq_Iio (h : a < b) : Iic a union Ico a b = Iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ico


/--
theorem `Ioo_subset_Ioo_union_Ico` / 定理 `Ioo_subset_Ioo_union_Ico`

English:
theorem Ioo_subset_Ioo_union_Ico
  statement: Ioo a c subseteq Ioo a b union Ico b c
  proof: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]

中文:
定理 Ioo_subset_Ioo_union_Ico
  结论: 开区间 a c subseteq 开区间 a b union 左闭右开区间 b c
  证明: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
-/
theorem Ioo_subset_Ioo_union_Ico : Ioo a c subseteq Ioo a b union Ico b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/--
theorem `Ioo_union_Ico_eq_Ioo` / 定理 `Ioo_union_Ico_eq_Ioo`

English:
theorem Ioo_union_Ico_eq_Ioo
  given: (h₁ : a < b) (h₂ : b <= c)
  statement: Ioo a b union Ico b c = Ioo a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioo_subset_Ioo_union_Ico

中文:
定理 Ioo_union_Ico_eq_Ioo
  条件: (h₁ : a < b) (h₂ : b <= c)
  结论: 开区间 a b union 左闭右开区间 b c = 开区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioo_subset_Ioo_union_Ico

Depends on / 依赖: Ioo_subset_Ioo_union_Ico, Subset, Subset.antisymm, antisymm, hx.elim, trans_le
-/
theorem Ioo_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b <= c) : Ioo a b union Ico b c = Ioo a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioo_subset_Ioo_union_Ico

/--
theorem `Ico_subset_Ico_union_Ico` / 定理 `Ico_subset_Ico_union_Ico`

English:
theorem Ico_subset_Ico_union_Ico
  statement: Ico a c subseteq Ico a b union Ico b c
  proof: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]

中文:
定理 Ico_subset_Ico_union_Ico
  结论: 左闭右开区间 a c subseteq 左闭右开区间 a b union 左闭右开区间 b c
  证明: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
-/
theorem Ico_subset_Ico_union_Ico : Ico a c subseteq Ico a b union Ico b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/--
theorem `Ico_union_Ico_eq_Ico` / 定理 `Ico_union_Ico_eq_Ico`

English:
theorem Ico_union_Ico_eq_Ico
  given: (h₁ : a <= b) (h₂ : b <= c)
  statement: Ico a b union Ico b c = Ico a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Ico_union_Ico

中文:
定理 Ico_union_Ico_eq_Ico
  条件: (h₁ : a <= b) (h₂ : b <= c)
  结论: 左闭右开区间 a b union 左闭右开区间 b c = 左闭右开区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Ico_union_Ico

Depends on / 依赖: Ico_subset_Ico_union_Ico, Subset, Subset.antisymm, antisymm, hx.elim, trans_le
-/
theorem Ico_union_Ico_eq_Ico (h₁ : a <= b) (h₂ : b <= c) : Ico a b union Ico b c = Ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Ico_union_Ico

/--
theorem `Ico_union_Ico` / 定理 `Ico_union_Ico`

English:
theorem Ico_union_Ico
  given: (h₁ : min a b <= max c d) (h₂ : min c d <= max a b)
  proof: by
  grind

中文:
定理 Ico_union_Ico
  条件: (h₁ : 最小值 a b <= 最大值 c d) (h₂ : 最小值 c d <= 最大值 a b)
  证明: by
  grind
-/
theorem Ico_union_Ico (h₁ : min a b <= max c d) (h₂ : min c d <= max a b) :
    Ico a b union Ico c d = Ico (min a c) (max b d) := by
  grind

/--
theorem `Ico_union_Ico'` / 定理 `Ico_union_Ico'`

English:
theorem Ico_union_Ico'
  given: (h₁ : c <= b) (h₂ : a <= d)
  statement: Ico a b union Ico c d = Ico (min a c) (max b d)
  proof: Ico_union_Ico
    ((min_le_left ..).trans (h₂.trans (le_max_right ..)))
    ((min_le_left ..).trans (h₁.trans (le_max_right ..)))

中文:
定理 Ico_union_Ico'
  条件: (h₁ : c <= b) (h₂ : a <= d)
  结论: 左闭右开区间 a b union 左闭右开区间 c d = 左闭右开区间 (最小值 a c) (最大值 b d)
  证明: Ico_union_Ico
    ((min_le_left ..).trans (h₂.trans (le_max_right ..)))
    ((min_le_left ..).trans (h₁.trans (le_max_right ..)))

Depends on / 依赖: Ico_union_Ico, le_max_right, min_le_left
-/
theorem Ico_union_Ico' (h₁ : c <= b) (h₂ : a <= d) : Ico a b union Ico c d = Ico (min a c) (max b d) :=
  Ico_union_Ico
    ((min_le_left ..).trans (h₂.trans (le_max_right ..)))
    ((min_le_left ..).trans (h₁.trans (le_max_right ..)))

/--
theorem `Icc_subset_Ico_union_Icc` / 定理 `Icc_subset_Ico_union_Icc`

English:
theorem Icc_subset_Ico_union_Icc
  statement: Icc a c subseteq Ico a b union Icc b c
  proof: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]

中文:
定理 Icc_subset_Ico_union_Icc
  结论: 闭区间 a c subseteq 左闭右开区间 a b union 闭区间 b c
  证明: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
-/
theorem Icc_subset_Ico_union_Icc : Icc a c subseteq Ico a b union Icc b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/--
theorem `Ico_union_Icc_eq_Icc` / 定理 `Ico_union_Icc_eq_Icc`

English:
theorem Ico_union_Icc_eq_Icc
  given: (h₁ : a <= b) (h₂ : b <= c)
  statement: Ico a b union Icc b c = Icc a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Ico_union_Icc

中文:
定理 Ico_union_Icc_eq_Icc
  条件: (h₁ : a <= b) (h₂ : b <= c)
  结论: 左闭右开区间 a b union 闭区间 b c = 闭区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Ico_union_Icc

Depends on / 依赖: Icc_subset_Ico_union_Icc, Subset, Subset.antisymm, antisymm, hx.elim, le.trans
-/
theorem Ico_union_Icc_eq_Icc (h₁ : a <= b) (h₂ : b <= c) : Ico a b union Icc b c = Icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Ico_union_Icc

/--
theorem `Ioc_subset_Ioo_union_Icc` / 定理 `Ioc_subset_Ioo_union_Icc`

English:
theorem Ioc_subset_Ioo_union_Icc
  statement: Ioc a c subseteq Ioo a b union Icc b c
  proof: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]

中文:
定理 Ioc_subset_Ioo_union_Icc
  结论: 左开右闭区间 a c subseteq 开区间 a b union 闭区间 b c
  证明: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
-/
theorem Ioc_subset_Ioo_union_Icc : Ioc a c subseteq Ioo a b union Icc b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/--
theorem `Ioo_union_Icc_eq_Ioc` / 定理 `Ioo_union_Icc_eq_Ioc`

English:
theorem Ioo_union_Icc_eq_Ioc
  given: (h₁ : a < b) (h₂ : b <= c)
  statement: Ioo a b union Icc b c = Ioc a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioo_union_Icc

中文:
定理 Ioo_union_Icc_eq_Ioc
  条件: (h₁ : a < b) (h₂ : b <= c)
  结论: 开区间 a b union 闭区间 b c = 左开右闭区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioo_union_Icc

Depends on / 依赖: Ioc_subset_Ioo_union_Icc, Subset, Subset.antisymm, antisymm, hx.elim, le.trans, trans_le
-/
theorem Ioo_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b <= c) : Ioo a b union Icc b c = Ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioo_union_Icc

/-! ### Two finite intervals, `I?c` and `Io?` -/

@[to_dual none]
/--
theorem `Ioo_subset_Ioc_union_Ioo` / 定理 `Ioo_subset_Ioc_union_Ioo`

English:
theorem Ioo_subset_Ioc_union_Ioo
  statement: Ioo a c subseteq Ioc a b union Ioo b c
  proof: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]

中文:
定理 Ioo_subset_Ioc_union_Ioo
  结论: 开区间 a c subseteq 左开右闭区间 a b union 开区间 b c
  证明: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
-/
theorem Ioo_subset_Ioc_union_Ioo : Ioo a c subseteq Ioc a b union Ioo b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/--
theorem `Ioc_union_Ioo_eq_Ioo` / 定理 `Ioc_union_Ioo_eq_Ioo`

English:
theorem Ioc_union_Ioo_eq_Ioo
  given: (h₁ : a <= b) (h₂ : b < c)
  statement: Ioc a b union Ioo b c = Ioo a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioo_subset_Ioc_union_Ioo

@[to_dual none]

中文:
定理 Ioc_union_Ioo_eq_Ioo
  条件: (h₁ : a <= b) (h₂ : b < c)
  结论: 左开右闭区间 a b union 开区间 b c = 开区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioo_subset_Ioc_union_Ioo

@[to_dual none]

Depends on / 依赖: Ioo_subset_Ioc_union_Ioo, Subset, Subset.antisymm, antisymm, hx.elim, trans_lt
-/
theorem Ioc_union_Ioo_eq_Ioo (h₁ : a <= b) (h₂ : b < c) : Ioc a b union Ioo b c = Ioo a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioo_subset_Ioc_union_Ioo

@[to_dual none]
/--
theorem `Ico_subset_Icc_union_Ioo` / 定理 `Ico_subset_Icc_union_Ioo`

English:
theorem Ico_subset_Icc_union_Ioo
  statement: Ico a c subseteq Icc a b union Ioo b c
  proof: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp, to_dual none]

中文:
定理 Ico_subset_Icc_union_Ioo
  结论: 左闭右开区间 a c subseteq 闭区间 a b union 开区间 b c
  证明: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp, to_dual none]
-/
theorem Ico_subset_Icc_union_Ioo : Ico a c subseteq Icc a b union Ioo b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp, to_dual none]
/--
theorem `Icc_union_Ioo_eq_Ico` / 定理 `Icc_union_Ioo_eq_Ico`

English:
theorem Icc_union_Ioo_eq_Ico
  given: (h₁ : a <= b) (h₂ : b < c)
  statement: Icc a b union Ioo b c = Ico a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Ico_subset_Icc_union_Ioo

中文:
定理 Icc_union_Ioo_eq_Ico
  条件: (h₁ : a <= b) (h₂ : b < c)
  结论: 闭区间 a b union 开区间 b c = 左闭右开区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Ico_subset_Icc_union_Ioo

Depends on / 依赖: Ico_subset_Icc_union_Ioo, Subset, Subset.antisymm, antisymm, hx.elim, trans_lt
-/
theorem Icc_union_Ioo_eq_Ico (h₁ : a <= b) (h₂ : b < c) : Icc a b union Ioo b c = Ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Ico_subset_Icc_union_Ioo

/--
theorem `Icc_subset_Icc_union_Ioc` / 定理 `Icc_subset_Icc_union_Ioc`

English:
theorem Icc_subset_Icc_union_Ioc
  statement: Icc a c subseteq Icc a b union Ioc b c
  proof: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]

中文:
定理 Icc_subset_Icc_union_Ioc
  结论: 闭区间 a c subseteq 闭区间 a b union 左开右闭区间 b c
  证明: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
-/
theorem Icc_subset_Icc_union_Ioc : Icc a c subseteq Icc a b union Ioc b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/--
theorem `Icc_union_Ioc_eq_Icc` / 定理 `Icc_union_Ioc_eq_Icc`

English:
theorem Icc_union_Ioc_eq_Icc
  given: (h₁ : a <= b) (h₂ : b <= c)
  statement: Icc a b union Ioc b c = Icc a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Icc_subset_Icc_union_Ioc

中文:
定理 Icc_union_Ioc_eq_Icc
  条件: (h₁ : a <= b) (h₂ : b <= c)
  结论: 闭区间 a b union 左开右闭区间 b c = 闭区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Icc_subset_Icc_union_Ioc

Depends on / 依赖: Icc_subset_Icc_union_Ioc, Subset, Subset.antisymm, antisymm, hx.elim
-/
theorem Icc_union_Ioc_eq_Icc (h₁ : a <= b) (h₂ : b <= c) : Icc a b union Ioc b c = Icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Icc_subset_Icc_union_Ioc

/--
theorem `Ioc_subset_Ioc_union_Ioc` / 定理 `Ioc_subset_Ioc_union_Ioc`

English:
theorem Ioc_subset_Ioc_union_Ioc
  statement: Ioc a c subseteq Ioc a b union Ioc b c
  proof: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]

中文:
定理 Ioc_subset_Ioc_union_Ioc
  结论: 左开右闭区间 a c subseteq 左开右闭区间 a b union 左开右闭区间 b c
  证明: fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
-/
theorem Ioc_subset_Ioc_union_Ioc : Ioc a c subseteq Ioc a b union Ioc b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/--
theorem `Ioc_union_Ioc_eq_Ioc` / 定理 `Ioc_union_Ioc_eq_Ioc`

English:
theorem Ioc_union_Ioc_eq_Ioc
  given: (h₁ : a <= b) (h₂ : b <= c)
  statement: Ioc a b union Ioc b c = Ioc a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Ioc

中文:
定理 Ioc_union_Ioc_eq_Ioc
  条件: (h₁ : a <= b) (h₂ : b <= c)
  结论: 左开右闭区间 a b union 左开右闭区间 b c = 左开右闭区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Ioc

Depends on / 依赖: Ioc_subset_Ioc_union_Ioc, Subset, Subset.antisymm, antisymm, hx.elim, trans_lt
-/
theorem Ioc_union_Ioc_eq_Ioc (h₁ : a <= b) (h₂ : b <= c) : Ioc a b union Ioc b c = Ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Ioc

/--
theorem `Ioc_union_Ioc` / 定理 `Ioc_union_Ioc`

English:
theorem Ioc_union_Ioc
  given: (h₁ : min a b <= max c d) (h₂ : min c d <= max a b)
  proof: by
  grind

中文:
定理 Ioc_union_Ioc
  条件: (h₁ : 最小值 a b <= 最大值 c d) (h₂ : 最小值 c d <= 最大值 a b)
  证明: by
  grind
-/
theorem Ioc_union_Ioc (h₁ : min a b <= max c d) (h₂ : min c d <= max a b) :
    Ioc a b union Ioc c d = Ioc (min a c) (max b d) := by
  grind

/--
theorem `Ioc_union_Ioc'` / 定理 `Ioc_union_Ioc'`

English:
theorem Ioc_union_Ioc'
  given: (h₁ : c <= b) (h₂ : a <= d)
  statement: Ioc a b union Ioc c d = Ioc (min a c) (max b d)
  proof: Ioc_union_Ioc
    ((min_le_left ..).trans (h₂.trans (le_max_right ..)))
    ((min_le_left ..).trans (h₁.trans (le_max_right ..)))

中文:
定理 Ioc_union_Ioc'
  条件: (h₁ : c <= b) (h₂ : a <= d)
  结论: 左开右闭区间 a b union 左开右闭区间 c d = 左开右闭区间 (最小值 a c) (最大值 b d)
  证明: Ioc_union_Ioc
    ((min_le_left ..).trans (h₂.trans (le_max_right ..)))
    ((min_le_left ..).trans (h₁.trans (le_max_right ..)))

Depends on / 依赖: Ioc_union_Ioc, le_max_right, min_le_left
-/
theorem Ioc_union_Ioc' (h₁ : c <= b) (h₂ : a <= d) : Ioc a b union Ioc c d = Ioc (min a c) (max b d) :=
  Ioc_union_Ioc
    ((min_le_left ..).trans (h₂.trans (le_max_right ..)))
    ((min_le_left ..).trans (h₁.trans (le_max_right ..)))

/-! ### Two finite intervals with a common point -/

@[to_dual none]
/--
theorem `Ioo_subset_Ioc_union_Ico` / 定理 `Ioo_subset_Ioc_union_Ico`

English:
theorem Ioo_subset_Ioc_union_Ico
  statement: Ioo a c subseteq Ioc a b union Ico b c
  proof: Subset.trans Ioo_subset_Ioc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[to_dual (attr := simp)]

中文:
定理 Ioo_subset_Ioc_union_Ico
  结论: 开区间 a c subseteq 左开右闭区间 a b union 左闭右开区间 b c
  证明: Subset.trans Ioo_subset_Ioc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[to_dual (attr := simp)]

Depends on / 依赖: Ioo_subset_Ico_self, Ioo_subset_Ioc_union_Ioo, Subset, Subset.trans, union_subset_union_right
-/
theorem Ioo_subset_Ioc_union_Ico : Ioo a c subseteq Ioc a b union Ico b c :=
  Subset.trans Ioo_subset_Ioc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[to_dual (attr := simp)]
/--
theorem `Ioc_union_Ico_eq_Ioo` / 定理 `Ioc_union_Ico_eq_Ioo`

English:
theorem Ioc_union_Ico_eq_Ioo
  given: (h₁ : a < b) (h₂ : b < c)
  statement: Ioc a b union Ico b c = Ioo a c
  proof: Subset.antisymm
    (fun _ hx =>
      hx.elim (fun hx' => ⟨hx'.1, hx'.2.trans_lt h₂⟩) fun hx' => ⟨h₁.trans_le hx'.1, hx'.2⟩)
    Ioo_subset_Ioc_union_Ico

中文:
定理 Ioc_union_Ico_eq_Ioo
  条件: (h₁ : a < b) (h₂ : b < c)
  结论: 左开右闭区间 a b union 左闭右开区间 b c = 开区间 a c
  证明: Subset.antisymm
    (fun _ hx =>
      hx.elim (fun hx' => ⟨hx'.1, hx'.2.trans_lt h₂⟩) fun hx' => ⟨h₁.trans_le hx'.1, hx'.2⟩)
    Ioo_subset_Ioc_union_Ico

Depends on / 依赖: Ioo_subset_Ioc_union_Ico, Subset, Subset.antisymm, antisymm, hx.elim, trans_le, trans_lt
-/
theorem Ioc_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b < c) : Ioc a b union Ico b c = Ioo a c :=
  Subset.antisymm
    (fun _ hx =>
      hx.elim (fun hx' => ⟨hx'.1, hx'.2.trans_lt h₂⟩) fun hx' => ⟨h₁.trans_le hx'.1, hx'.2⟩)
    Ioo_subset_Ioc_union_Ico

/--
theorem `Ico_subset_Icc_union_Ico` / 定理 `Ico_subset_Icc_union_Ico`

English:
theorem Ico_subset_Icc_union_Ico
  statement: Ico a c subseteq Icc a b union Ico b c
  proof: Subset.trans Ico_subset_Icc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]

中文:
定理 Ico_subset_Icc_union_Ico
  结论: 左闭右开区间 a c subseteq 闭区间 a b union 左闭右开区间 b c
  证明: Subset.trans Ico_subset_Icc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]

Depends on / 依赖: Ico_subset_Icc_union_Ioo, Ioo_subset_Ico_self, Subset, Subset.trans, union_subset_union_right
-/
theorem Ico_subset_Icc_union_Ico : Ico a c subseteq Icc a b union Ico b c :=
  Subset.trans Ico_subset_Icc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
/--
theorem `Icc_union_Ico_eq_Ico` / 定理 `Icc_union_Ico_eq_Ico`

English:
theorem Icc_union_Ico_eq_Ico
  given: (h₁ : a <= b) (h₂ : b < c)
  statement: Icc a b union Ico b c = Ico a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Icc_union_Ico

中文:
定理 Icc_union_Ico_eq_Ico
  条件: (h₁ : a <= b) (h₂ : b < c)
  结论: 闭区间 a b union 左闭右开区间 b c = 左闭右开区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Icc_union_Ico

Depends on / 依赖: Ico_subset_Icc_union_Ico, Subset, Subset.antisymm, antisymm, hx.elim, trans_lt
-/
theorem Icc_union_Ico_eq_Ico (h₁ : a <= b) (h₂ : b < c) : Icc a b union Ico b c = Ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Icc_union_Ico

/--
theorem `Icc_subset_Icc_union_Icc` / 定理 `Icc_subset_Icc_union_Icc`

English:
theorem Icc_subset_Icc_union_Icc
  statement: Icc a c subseteq Icc a b union Icc b c
  proof: Subset.trans Icc_subset_Icc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]

中文:
定理 Icc_subset_Icc_union_Icc
  结论: 闭区间 a c subseteq 闭区间 a b union 闭区间 b c
  证明: Subset.trans Icc_subset_Icc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]

Depends on / 依赖: Icc_subset_Icc_union_Ioc, Ioc_subset_Icc_self, Subset, Subset.trans, union_subset_union_right
-/
theorem Icc_subset_Icc_union_Icc : Icc a c subseteq Icc a b union Icc b c :=
  Subset.trans Icc_subset_Icc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
/--
theorem `Icc_union_Icc_eq_Icc` / 定理 `Icc_union_Icc_eq_Icc`

English:
theorem Icc_union_Icc_eq_Icc
  given: (h₁ : a <= b) (h₂ : b <= c)
  statement: Icc a b union Icc b c = Icc a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Icc_union_Icc

中文:
定理 Icc_union_Icc_eq_Icc
  条件: (h₁ : a <= b) (h₂ : b <= c)
  结论: 闭区间 a b union 闭区间 b c = 闭区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Icc_union_Icc

Depends on / 依赖: Icc_subset_Icc_union_Icc, Subset, Subset.antisymm, antisymm, hx.elim
-/
theorem Icc_union_Icc_eq_Icc (h₁ : a <= b) (h₂ : b <= c) : Icc a b union Icc b c = Icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Icc_union_Icc

/--
theorem `Icc_union_Icc'` / 定理 `Icc_union_Icc'`

English:
theorem Icc_union_Icc'
  given: (h₁ : c <= b) (h₂ : a <= d)
  statement: Icc a b union Icc c d = Icc (min a c) (max b d)
  proof: by
  grind

中文:
定理 Icc_union_Icc'
  条件: (h₁ : c <= b) (h₂ : a <= d)
  结论: 闭区间 a b union 闭区间 c d = 闭区间 (最小值 a c) (最大值 b d)
  证明: by
  grind
-/
theorem Icc_union_Icc' (h₁ : c <= b) (h₂ : a <= d) : Icc a b union Icc c d = Icc (min a c) (max b d) := by
  grind

/--
theorem `Icc_union_Icc` / 定理 `Icc_union_Icc`

English:
theorem Icc_union_Icc
  given: (h₁ : min a b < max c d) (h₂ : min c d < max a b)
  proof: by
  grind

中文:
定理 Icc_union_Icc
  条件: (h₁ : 最小值 a b < 最大值 c d) (h₂ : 最小值 c d < 最大值 a b)
  证明: by
  grind
-/
theorem Icc_union_Icc (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    Icc a b union Icc c d = Icc (min a c) (max b d) := by
  grind

/--
theorem `Ioc_subset_Ioc_union_Icc` / 定理 `Ioc_subset_Ioc_union_Icc`

English:
theorem Ioc_subset_Ioc_union_Icc
  statement: Ioc a c subseteq Ioc a b union Icc b c
  proof: Subset.trans Ioc_subset_Ioc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]

中文:
定理 Ioc_subset_Ioc_union_Icc
  结论: 左开右闭区间 a c subseteq 左开右闭区间 a b union 闭区间 b c
  证明: Subset.trans Ioc_subset_Ioc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]

Depends on / 依赖: Ioc_subset_Icc_self, Ioc_subset_Ioc_union_Ioc, Subset, Subset.trans, union_subset_union_right
-/
theorem Ioc_subset_Ioc_union_Icc : Ioc a c subseteq Ioc a b union Icc b c :=
  Subset.trans Ioc_subset_Ioc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
/--
theorem `Ioc_union_Icc_eq_Ioc` / 定理 `Ioc_union_Icc_eq_Ioc`

English:
theorem Ioc_union_Icc_eq_Ioc
  given: (h₁ : a < b) (h₂ : b <= c)
  statement: Ioc a b union Icc b c = Ioc a c
  proof: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Icc

中文:
定理 Ioc_union_Icc_eq_Ioc
  条件: (h₁ : a < b) (h₂ : b <= c)
  结论: 左开右闭区间 a b union 闭区间 b c = 左开右闭区间 a c
  证明: Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Icc

Depends on / 依赖: Ioc_subset_Ioc_union_Icc, Subset, Subset.antisymm, antisymm, hx.elim, trans_le
-/
theorem Ioc_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b <= c) : Ioc a b union Icc b c = Ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Icc

/--
theorem `Ioo_union_Ioo'` / 定理 `Ioo_union_Ioo'`

English:
theorem Ioo_union_Ioo'
  given: (h₁ : c < b) (h₂ : a < d)
  statement: Ioo a b union Ioo c d = Ioo (min a c) (max b d)
  proof: by
  grind

中文:
定理 Ioo_union_Ioo'
  条件: (h₁ : c < b) (h₂ : a < d)
  结论: 开区间 a b union 开区间 c d = 开区间 (最小值 a c) (最大值 b d)
  证明: by
  grind
-/
theorem Ioo_union_Ioo' (h₁ : c < b) (h₂ : a < d) : Ioo a b union Ioo c d = Ioo (min a c) (max b d) := by
  grind

/--
theorem `Ioo_union_Ioo` / 定理 `Ioo_union_Ioo`

English:
theorem Ioo_union_Ioo
  given: (h₁ : min a b < max c d) (h₂ : min c d < max a b)
  proof: by
  grind

中文:
定理 Ioo_union_Ioo
  条件: (h₁ : 最小值 a b < 最大值 c d) (h₂ : 最小值 c d < 最大值 a b)
  证明: by
  grind
-/
theorem Ioo_union_Ioo (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    Ioo a b union Ioo c d = Ioo (min a c) (max b d) := by
  grind

/--
theorem `Ioo_subset_Ioo_union_Ioo` / 定理 `Ioo_subset_Ioo_union_Ioo`

English:
theorem Ioo_subset_Ioo_union_Ioo
  given: (h₁ : a <= a₁) (h₂ : c < b) (h₃ : b₁ <= d)
  proof: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨lt_of_le_of_lt h₁ hx.1, hxb⟩)
    fun hxb => Or.inr ⟨lt_of_lt_of_le h₂ hxb, lt_of_lt_of_le hx.2 h₃⟩

中文:
定理 Ioo_subset_Ioo_union_Ioo
  条件: (h₁ : a <= a₁) (h₂ : c < b) (h₃ : b₁ <= d)
  证明: fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨lt_of_le_of_lt h₁ hx.1, hxb⟩)
    fun hxb => Or.inr ⟨lt_of_lt_of_le h₂ hxb, lt_of_lt_of_le hx.2 h₃⟩
-/
theorem Ioo_subset_Ioo_union_Ioo (h₁ : a <= a₁) (h₂ : c < b) (h₃ : b₁ <= d) :
    Ioo a₁ b₁ subseteq Ioo a b union Ioo c d := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨lt_of_le_of_lt h₁ hx.1, hxb⟩)
    fun hxb => Or.inr ⟨lt_of_lt_of_le h₂ hxb, lt_of_lt_of_le hx.2 h₃⟩

/-! ### Intersection, difference, complement -/

@[to_dual (attr := simp)]
/--
theorem `Ioi_inter_Ioi` / 定理 `Ioi_inter_Ioi`

English:
theorem Ioi_inter_Ioi
  statement: Ioi a inter Ioi b = Ioi (a ⊔ b)
  proof: ext fun _ => sup_lt_iff.symm

@[to_dual]

中文:
定理 Ioi_inter_Ioi
  结论: 左开右无界区间 a inter 左开右无界区间 b = 左开右无界区间 (a ⊔ b)
  证明: ext fun _ => sup_lt_iff.symm

@[to_dual]

Depends on / 依赖: sup_lt_iff, sup_lt_iff.symm
-/
theorem Ioi_inter_Ioi : Ioi a inter Ioi b = Ioi (a ⊔ b) :=
  ext fun _ => sup_lt_iff.symm

@[to_dual]
/--
theorem `Ico_inter_Ico` / 定理 `Ico_inter_Ico`

English:
theorem Ico_inter_Ico
  statement: Ico a₁ b₁ inter Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂)
  proof: by
  grind

@[to_dual self]

中文:
定理 Ico_inter_Ico
  结论: 左闭右开区间 a₁ b₁ inter 左闭右开区间 a₂ b₂ = 左闭右开区间 (a₁ ⊔ a₂) (b₁ ⊓ b₂)
  证明: by
  grind

@[to_dual self]
-/
theorem Ico_inter_Ico : Ico a₁ b₁ inter Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  grind

@[to_dual self]
/--
theorem `Ioo_inter_Ioo` / 定理 `Ioo_inter_Ioo`

English:
theorem Ioo_inter_Ioo
  statement: Ioo a₁ b₁ inter Ioo a₂ b₂ = Ioo (a₁ ⊔ a₂) (b₁ ⊓ b₂)
  proof: by
  grind

@[to_dual]

中文:
定理 Ioo_inter_Ioo
  结论: 开区间 a₁ b₁ inter 开区间 a₂ b₂ = 开区间 (a₁ ⊔ a₂) (b₁ ⊓ b₂)
  证明: by
  grind

@[to_dual]
-/
theorem Ioo_inter_Ioo : Ioo a₁ b₁ inter Ioo a₂ b₂ = Ioo (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  grind

@[to_dual]
/--
theorem `Ioo_inter_Iio` / 定理 `Ioo_inter_Iio`

English:
theorem Ioo_inter_Iio
  statement: Ioo a b inter Iio c = Ioo a (min b c)
  proof: by
  grind

@[to_dual]

中文:
定理 Ioo_inter_Iio
  结论: 开区间 a b inter 左无界右开区间 c = 开区间 a (最小值 b c)
  证明: by
  grind

@[to_dual]
-/
theorem Ioo_inter_Iio : Ioo a b inter Iio c = Ioo a (min b c) := by
  grind

@[to_dual]
/--
theorem `Iio_inter_Ioo` / 定理 `Iio_inter_Ioo`

English:
theorem Iio_inter_Ioo
  statement: Iio a inter Ioo b c = Ioo b (min a c)
  proof: by
  grind

中文:
定理 Iio_inter_Ioo
  结论: 左无界右开区间 a inter 开区间 b c = 开区间 b (最小值 a c)
  证明: by
  grind
-/
theorem Iio_inter_Ioo : Iio a inter Ioo b c = Ioo b (min a c) := by
  grind

/--
theorem `Ioc_inter_Ioo_of_left_lt` / 定理 `Ioc_inter_Ioo_of_left_lt`

English:
theorem Ioc_inter_Ioo_of_left_lt
  given: (h : b₁ < b₂)
  statement: Ioc a₁ b₁ inter Ioo a₂ b₂ = Ioc (max a₁ a₂) b₁
  proof: by
  grind

中文:
定理 Ioc_inter_Ioo_of_left_lt
  条件: (h : b₁ < b₂)
  结论: 左开右闭区间 a₁ b₁ inter 开区间 a₂ b₂ = 左开右闭区间 (最大值 a₁ a₂) b₁
  证明: by
  grind
-/
theorem Ioc_inter_Ioo_of_left_lt (h : b₁ < b₂) : Ioc a₁ b₁ inter Ioo a₂ b₂ = Ioc (max a₁ a₂) b₁ := by
  grind

/--
theorem `Ioc_inter_Ioo_of_right_le` / 定理 `Ioc_inter_Ioo_of_right_le`

English:
theorem Ioc_inter_Ioo_of_right_le
  given: (h : b₂ <= b₁)
  statement: Ioc a₁ b₁ inter Ioo a₂ b₂ = Ioo (max a₁ a₂) b₂
  proof: by
  grind

中文:
定理 Ioc_inter_Ioo_of_right_le
  条件: (h : b₂ <= b₁)
  结论: 左开右闭区间 a₁ b₁ inter 开区间 a₂ b₂ = 开区间 (最大值 a₁ a₂) b₂
  证明: by
  grind
-/
theorem Ioc_inter_Ioo_of_right_le (h : b₂ <= b₁) : Ioc a₁ b₁ inter Ioo a₂ b₂ = Ioo (max a₁ a₂) b₂ := by
  grind

/--
theorem `Ioo_inter_Ioc_of_left_le` / 定理 `Ioo_inter_Ioc_of_left_le`

English:
theorem Ioo_inter_Ioc_of_left_le
  given: (h : b₁ <= b₂)
  statement: Ioo a₁ b₁ inter Ioc a₂ b₂ = Ioo (max a₁ a₂) b₁
  proof: by
  grind

中文:
定理 Ioo_inter_Ioc_of_left_le
  条件: (h : b₁ <= b₂)
  结论: 开区间 a₁ b₁ inter 左开右闭区间 a₂ b₂ = 开区间 (最大值 a₁ a₂) b₁
  证明: by
  grind
-/
theorem Ioo_inter_Ioc_of_left_le (h : b₁ <= b₂) : Ioo a₁ b₁ inter Ioc a₂ b₂ = Ioo (max a₁ a₂) b₁ := by
  grind

/--
theorem `Ioo_inter_Ioc_of_right_lt` / 定理 `Ioo_inter_Ioc_of_right_lt`

English:
theorem Ioo_inter_Ioc_of_right_lt
  given: (h : b₂ < b₁)
  statement: Ioo a₁ b₁ inter Ioc a₂ b₂ = Ioc (max a₁ a₂) b₂
  proof: by
  grind

@[simp]

中文:
定理 Ioo_inter_Ioc_of_right_lt
  条件: (h : b₂ < b₁)
  结论: 开区间 a₁ b₁ inter 左开右闭区间 a₂ b₂ = 左开右闭区间 (最大值 a₁ a₂) b₂
  证明: by
  grind

@[simp]
-/
theorem Ioo_inter_Ioc_of_right_lt (h : b₂ < b₁) : Ioo a₁ b₁ inter Ioc a₂ b₂ = Ioc (max a₁ a₂) b₂ := by
  grind

@[simp]
/--
theorem `Ico_sdiff_Iio` / 定理 `Ico_sdiff_Iio`

English:
theorem Ico_sdiff_Iio
  statement: Ico a b \ Iio c = Ico (max a c) b
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Iio := Ico_sdiff_Iio

@[simp]

中文:
定理 Ico_sdiff_Iio
  结论: 左闭右开区间 a b \ 左无界右开区间 c = 左闭右开区间 (最大值 a c) b
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Iio := Ico_sdiff_Iio

@[simp]
-/
theorem Ico_sdiff_Iio : Ico a b \ Iio c = Ico (max a c) b := by
  grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Iio := Ico_sdiff_Iio

@[simp]
/--
theorem `Ioc_sdiff_Ioi` / 定理 `Ioc_sdiff_Ioi`

English:
theorem Ioc_sdiff_Ioi
  statement: Ioc a b \ Ioi c = Ioc a (min b c)
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Ioi := Ioc_sdiff_Ioi

@[simp]

中文:
定理 Ioc_sdiff_Ioi
  结论: 左开右闭区间 a b \ 左开右无界区间 c = 左开右闭区间 a (最小值 b c)
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Ioi := Ioc_sdiff_Ioi

@[simp]
-/
theorem Ioc_sdiff_Ioi : Ioc a b \ Ioi c = Ioc a (min b c) := by
  grind

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Ioi := Ioc_sdiff_Ioi

@[simp]
/--
theorem `Ioc_inter_Ioi` / 定理 `Ioc_inter_Ioi`

English:
theorem Ioc_inter_Ioi
  statement: Ioc a b inter Ioi c = Ioc (a ⊔ c) b
  proof: by
  grind

@[simp]

中文:
定理 Ioc_inter_Ioi
  结论: 左开右闭区间 a b inter 左开右无界区间 c = 左开右闭区间 (a ⊔ c) b
  证明: by
  grind

@[simp]
-/
theorem Ioc_inter_Ioi : Ioc a b inter Ioi c = Ioc (a ⊔ c) b := by
  grind

@[simp]
/--
theorem `Ico_inter_Iio` / 定理 `Ico_inter_Iio`

English:
theorem Ico_inter_Iio
  statement: Ico a b inter Iio c = Ico a (min b c)
  proof: by
  grind

@[simp]

中文:
定理 Ico_inter_Iio
  结论: 左闭右开区间 a b inter 左无界右开区间 c = 左闭右开区间 a (最小值 b c)
  证明: by
  grind

@[simp]
-/
theorem Ico_inter_Iio : Ico a b inter Iio c = Ico a (min b c) := by
  grind

@[simp]
/--
theorem `Ioc_sdiff_Iic` / 定理 `Ioc_sdiff_Iic`

English:
theorem Ioc_sdiff_Iic
  statement: Ioc a b \ Iic c = Ioc (max a c) b
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Iic := Ioc_sdiff_Iic

中文:
定理 Ioc_sdiff_Iic
  结论: 左开右闭区间 a b \ 左无界右闭区间 c = 左开右闭区间 (最大值 a c) b
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Iic := Ioc_sdiff_Iic
-/
theorem Ioc_sdiff_Iic : Ioc a b \ Iic c = Ioc (max a c) b := by
  grind

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Iic := Ioc_sdiff_Iic

/--
theorem `compl_Ioc` / 定理 `compl_Ioc`

English:
theorem compl_Ioc
  statement: (Ioc a b)ᶜ = Iic a union Ioi b
  proof: by
  grind

中文:
定理 compl_Ioc
  结论: (左开右闭区间 a b)ᶜ = 左无界右闭区间 a union 左开右无界区间 b
  证明: by
  grind
-/
theorem compl_Ioc : (Ioc a b)ᶜ = Iic a union Ioi b := by
  grind

/--
theorem `Iic_sdiff_Ioc` / 定理 `Iic_sdiff_Ioc`

English:
theorem Iic_sdiff_Ioc
  statement: Iic b \ Ioc a b = Iic (a ⊓ b)
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc := Iic_sdiff_Ioc

@[simp]

中文:
定理 Iic_sdiff_Ioc
  结论: 左无界右闭区间 b \ 左开右闭区间 a b = 左无界右闭区间 (a ⊓ b)
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc := Iic_sdiff_Ioc

@[simp]
-/
theorem Iic_sdiff_Ioc : Iic b \ Ioc a b = Iic (a ⊓ b) := by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc := Iic_sdiff_Ioc

@[simp]
/--
theorem `Ioi_sdiff_Ioc` / 定理 `Ioi_sdiff_Ioc`

English:
theorem Ioi_sdiff_Ioc
  statement: Ioi a \ Ioc a b = Ioi (max a b)
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ioc := Ioi_sdiff_Ioc

中文:
定理 Ioi_sdiff_Ioc
  结论: 左开右无界区间 a \ 左开右闭区间 a b = 左开右无界区间 (最大值 a b)
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ioc := Ioi_sdiff_Ioc
-/
theorem Ioi_sdiff_Ioc : Ioi a \ Ioc a b = Ioi (max a b) := by
  grind

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ioc := Ioi_sdiff_Ioc

/--
theorem `Iic_sdiff_Ioc_self_of_le` / 定理 `Iic_sdiff_Ioc_self_of_le`

English:
theorem Iic_sdiff_Ioc_self_of_le
  given: (hab : a <= b)
  statement: Iic b \ Ioc a b = Iic a
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc_self_of_le := Iic_sdiff_Ioc_self_of_le

@[simp]

中文:
定理 Iic_sdiff_Ioc_self_of_le
  条件: (hab : a <= b)
  结论: 左无界右闭区间 b \ 左开右闭区间 a b = 左无界右闭区间 a
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc_self_of_le := Iic_sdiff_Ioc_self_of_le

@[simp]
-/
theorem Iic_sdiff_Ioc_self_of_le (hab : a <= b) : Iic b \ Ioc a b = Iic a := by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc_self_of_le := Iic_sdiff_Ioc_self_of_le

@[simp]
/--
theorem `Ioc_union_Ioc_right` / 定理 `Ioc_union_Ioc_right`

English:
theorem Ioc_union_Ioc_right
  statement: Ioc a b union Ioc a c = Ioc a (max b c)
  proof: by
  grind

@[simp]

中文:
定理 Ioc_union_Ioc_right
  结论: 左开右闭区间 a b union 左开右闭区间 a c = 左开右闭区间 a (最大值 b c)
  证明: by
  grind

@[simp]
-/
theorem Ioc_union_Ioc_right : Ioc a b union Ioc a c = Ioc a (max b c) := by
  grind

@[simp]
/--
theorem `Ioc_union_Ioc_left` / 定理 `Ioc_union_Ioc_left`

English:
theorem Ioc_union_Ioc_left
  statement: Ioc a c union Ioc b c = Ioc (min a b) c
  proof: by
  grind

@[simp]

中文:
定理 Ioc_union_Ioc_left
  结论: 左开右闭区间 a c union 左开右闭区间 b c = 左开右闭区间 (最小值 a b) c
  证明: by
  grind

@[simp]
-/
theorem Ioc_union_Ioc_left : Ioc a c union Ioc b c = Ioc (min a b) c := by
  grind

@[simp]
/--
theorem `Ioc_union_Ioc_symm` / 定理 `Ioc_union_Ioc_symm`

English:
theorem Ioc_union_Ioc_symm
  statement: Ioc a b union Ioc b a = Ioc (min a b) (max a b)
  proof: by
  grind

@[simp]

中文:
定理 Ioc_union_Ioc_symm
  结论: 左开右闭区间 a b union 左开右闭区间 b a = 左开右闭区间 (最小值 a b) (最大值 a b)
  证明: by
  grind

@[simp]
-/
theorem Ioc_union_Ioc_symm : Ioc a b union Ioc b a = Ioc (min a b) (max a b) := by
  grind

@[simp]
/--
theorem `Ioc_union_Ioc_union_Ioc_cycle` / 定理 `Ioc_union_Ioc_union_Ioc_cycle`

English:
theorem Ioc_union_Ioc_union_Ioc_cycle
  proof: by
  grind

中文:
定理 Ioc_union_Ioc_union_Ioc_cycle
  证明: by
  grind
-/
theorem Ioc_union_Ioc_union_Ioc_cycle :
    Ioc a b union Ioc b c union Ioc c a = Ioc (min a (min b c)) (max a (max b c)) := by
  grind

end Set
