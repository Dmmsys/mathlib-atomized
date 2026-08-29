/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Intervals of finsets as finsets

This file provides the `LocallyFiniteOrder` instance for `Finset α` and calculates the cardinality
of finite intervals of finsets.

If `s t : Finset α`, then `Finset.Icc s t` is the finset of finsets which include `s` and are
included in `t`. For example,
`Finset.Icc {0, 1} {0, 1, 2, 3} = {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}}`
and
`Finset.Icc {0, 1, 2} {0, 1, 3} = {}`.

In addition, this file gives characterizations of monotone and strictly monotone functions
out of `Finset α` in terms of `Finset.insert`
-/

public section


variable {α β : Type*}

namespace Finset

section Decidable

/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: [DecidableEq α]
  body: .ofIcc _ (fun s t =>
    if s subseteq t then
(t \ s).powerset.attach.map ⟨fun u => u.1.disjUnion s
disjoint_sdiff_self_left.mono_left mem_powerset.mp u.2, fun u₁ u₂ h => by
          simpa only [disjUnion_inj_left, Subtype.ext_iff] using h⟩
    else ∅) fun s t u => by
      by_cases hst : s subsete

中文:
实例 instLocallyFiniteOrder
  签名: [DecidableEq α]
  定义体: .ofIcc _ (fun s t =>
    if s subseteq t then
(t \ s).powerset.attach.map ⟨fun u => u.1.disjUnion s
disjoint_sdiff_self_left.mono_left mem_powerset.mp u.2, fun u₁ u₂ h => by
          simpa only [disjUnion_inj_left, Subtype.ext_iff] using h⟩
    else ∅) fun s t u => by
      by_cases hst : s subsete

Depends on / 依赖: Disjoint, Subtype, Subtype.ext_iff, and_assoc, attach, disjUnion, disjUnion_inj_left, disjoint_sdiff_self_left, disjoint_sdiff_self_left.mono_left, ext_iff, mem_powerset, mem_powerset.mp, mono_left, powerset, powerset.attach.map, subset_sdiff, subset_union_right, subseteq, union_subset
-/
instance instLocallyFiniteOrder [DecidableEq α] : LocallyFiniteOrder (Finset α) :=
  .ofIcc _ (fun s t =>
    if s subseteq t then
(t \ s).powerset.attach.map ⟨fun u => u.1.disjUnion s
disjoint_sdiff_self_left.mono_left mem_powerset.mp u.2, fun u₁ u₂ h => by
          simpa only [disjUnion_inj_left, Subtype.ext_iff] using h⟩
    else ∅) fun s t u => by
      by_cases hst : s subseteq t
      · suffices (exists a subseteq t, Disjoint a s ∧ a union s = u) ↔ s subseteq u ∧ u subseteq t by
          simpa [hst, subset_sdiff, and_assoc]
        constructor
        · rintro ⟨u, hut, -, rfl⟩
          exact ⟨subset_union_right, union_subset hut hst⟩
        · rintro ⟨hsu, hut⟩
          exact ⟨u \ s, sdiff_subset.trans hut, disjoint_sdiff_self_left, sdiff_union_of_subset hsu⟩
      · suffices s subseteq u -> ¬u subseteq t by simpa [hst]
        exact fun hsu hut => hst (hsu.trans hut)

variable [DecidableEq α] (s t : Finset α)

/--
theorem `Icc_eq_filter_powerset` / 定理 `Icc_eq_filter_powerset`

English:
theorem Icc_eq_filter_powerset
  statement: Icc s t = {u in t.powerset | s subseteq u}
  proof: by ext; simp [and_comm]

中文:
定理 Icc_eq_filter_powerset
  结论: 闭区间 s t = {u in t.powerset | s subseteq u}
  证明: by ext; simp [and_comm]

Depends on / 依赖: and_comm
-/
theorem Icc_eq_filter_powerset : Icc s t = {u in t.powerset | s subseteq u} := by ext; simp [and_comm]
/--
theorem `Ico_eq_filter_ssubsets` / 定理 `Ico_eq_filter_ssubsets`

English:
theorem Ico_eq_filter_ssubsets
  statement: Ico s t = {u in t.ssubsets | s subseteq u}
  proof: by ext; simp [and_comm]

中文:
定理 Ico_eq_filter_ssubsets
  结论: 左闭右开区间 s t = {u in t.ssubsets | s subseteq u}
  证明: by ext; simp [and_comm]

Depends on / 依赖: and_comm
-/
theorem Ico_eq_filter_ssubsets : Ico s t = {u in t.ssubsets | s subseteq u} := by ext; simp [and_comm]
/--
theorem `Ioc_eq_filter_powerset` / 定理 `Ioc_eq_filter_powerset`

English:
theorem Ioc_eq_filter_powerset
  statement: Ioc s t = {u in t.powerset | s ⊂ u}
  proof: by ext; simp [and_comm]

中文:
定理 Ioc_eq_filter_powerset
  结论: 左开右闭区间 s t = {u in t.powerset | s ⊂ u}
  证明: by ext; simp [and_comm]

Depends on / 依赖: and_comm
-/
theorem Ioc_eq_filter_powerset : Ioc s t = {u in t.powerset | s ⊂ u} := by ext; simp [and_comm]
/--
theorem `Ioo_eq_filter_ssubsets` / 定理 `Ioo_eq_filter_ssubsets`

English:
theorem Ioo_eq_filter_ssubsets
  statement: Ioo s t = {u in t.ssubsets | s ⊂ u}
  proof: by ext; simp [and_comm]

中文:
定理 Ioo_eq_filter_ssubsets
  结论: 开区间 s t = {u in t.ssubsets | s ⊂ u}
  证明: by ext; simp [and_comm]

Depends on / 依赖: and_comm
-/
theorem Ioo_eq_filter_ssubsets : Ioo s t = {u in t.ssubsets | s ⊂ u} := by ext; simp [and_comm]
/--
theorem `Iic_eq_powerset` / 定理 `Iic_eq_powerset`

English:
theorem Iic_eq_powerset
  statement: Iic s = s.powerset
  proof: by ext; simp

中文:
定理 Iic_eq_powerset
  结论: 左无界右闭区间 s = s.powerset
  证明: by ext; simp
-/
theorem Iic_eq_powerset : Iic s = s.powerset := by ext; simp
/--
theorem `Iio_eq_ssubsets` / 定理 `Iio_eq_ssubsets`

English:
theorem Iio_eq_ssubsets
  statement: Iio s = s.ssubsets
  proof: by ext; simp

中文:
定理 Iio_eq_ssubsets
  结论: 左无界右开区间 s = s.ssubsets
  证明: by ext; simp
-/
theorem Iio_eq_ssubsets : Iio s = s.ssubsets := by ext; simp

variable {s t}

/--
theorem `Icc_eq_image_powerset` / 定理 `Icc_eq_image_powerset`

English:
theorem Icc_eq_image_powerset
  given: (h : s subseteq t)
  statement: Icc s t = (t \ s).powerset.image (s union ·)
  proof: by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  ext
  simp [h, union_comm]

中文:
定理 Icc_eq_image_powerset
  条件: (h : s subseteq t)
  结论: 闭区间 s t = (t \ s).powerset.像 (s union ·)
  证明: by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  ext
  simp [h, union_comm]

Depends on / 依赖: Finset, Finset.Icc, LocallyFiniteOrder, LocallyFiniteOrder.ofIcc, instLocallyFiniteOrder, union_comm
-/
theorem Icc_eq_image_powerset (h : s subseteq t) : Icc s t = (t \ s).powerset.image (s union ·) := by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  ext
  simp [h, union_comm]

/--
theorem `Ico_eq_image_ssubsets` / 定理 `Ico_eq_image_ssubsets`

English:
theorem Ico_eq_image_ssubsets
  given: (h : s subseteq t)
  statement: Ico s t = (t \ s).ssubsets.image (s union ·)
  proof: by
  ext u
  simp_rw [mem_Ico, mem_image, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩

中文:
定理 Ico_eq_image_ssubsets
  条件: (h : s subseteq t)
  结论: 左闭右开区间 s t = (t \ s).ssubsets.像 (s union ·)
  证明: by
  ext u
  simp_rw [mem_Ico, mem_image, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩

Depends on / 依赖: le_sup_left, mem_Ico, mem_image, mem_ssubsets, sdiff_lt_sdiff_right, simp_rw, sup_lt_of_lt_sdiff_left, sup_sdiff_cancel_right
-/
theorem Ico_eq_image_ssubsets (h : s subseteq t) : Ico s t = (t \ s).ssubsets.image (s union ·) := by
  ext u
  simp_rw [mem_Ico, mem_image, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩

/--
theorem `card_Icc_finset` / 定理 `card_Icc_finset`

English:
theorem card_Icc_finset
  given: (h : s subseteq t)
  statement: (Icc s t).card = 2 ^ (t.card - s.card)
  proof: by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  simp [h, card_sdiff_of_subset]

中文:
定理 card_Icc_finset
  条件: (h : s subseteq t)
  结论: (闭区间 s t).card = 2 ^ (t.card - s.card)
  证明: by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  simp [h, card_sdiff_of_subset]

Depends on / 依赖: Finset, Finset.Icc, LocallyFiniteOrder, LocallyFiniteOrder.ofIcc, card_sdiff_of_subset, instLocallyFiniteOrder
-/
theorem card_Icc_finset (h : s subseteq t) : (Icc s t).card = 2 ^ (t.card - s.card) := by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  simp [h, card_sdiff_of_subset]

/--
theorem `card_Ico_finset` / 定理 `card_Ico_finset`

English:
theorem card_Ico_finset
  given: (h : s subseteq t)
  statement: (Ico s t).card = 2 ^ (t.card - s.card) - 1
  proof: by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc_finset h]

中文:
定理 card_Ico_finset
  条件: (h : s subseteq t)
  结论: (左闭右开区间 s t).card = 2 ^ (t.card - s.card) - 1
  证明: by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc_finset h]

Depends on / 依赖: card_Icc_finset, card_Ico_eq_card_Icc_sub_one
-/
theorem card_Ico_finset (h : s subseteq t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc_finset h]

/--
theorem `card_Ioc_finset` / 定理 `card_Ioc_finset`

English:
theorem card_Ioc_finset
  given: (h : s subseteq t)
  statement: (Ioc s t).card = 2 ^ (t.card - s.card) - 1
  proof: by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc_finset h]

中文:
定理 card_Ioc_finset
  条件: (h : s subseteq t)
  结论: (左开右闭区间 s t).card = 2 ^ (t.card - s.card) - 1
  证明: by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc_finset h]

Depends on / 依赖: card_Icc_finset, card_Ioc_eq_card_Icc_sub_one
-/
theorem card_Ioc_finset (h : s subseteq t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc_finset h]

/--
theorem `card_Ioo_finset` / 定理 `card_Ioo_finset`

English:
theorem card_Ioo_finset
  given: (h : s subseteq t)
  statement: (Ioo s t).card = 2 ^ (t.card - s.card) - 2
  proof: by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc_finset h]

中文:
定理 card_Ioo_finset
  条件: (h : s subseteq t)
  结论: (开区间 s t).card = 2 ^ (t.card - s.card) - 2
  证明: by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc_finset h]

Depends on / 依赖: card_Icc_finset, card_Ioo_eq_card_Icc_sub_two
-/
theorem card_Ioo_finset (h : s subseteq t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc_finset h]

/--
theorem `card_Iic_finset` / 定理 `card_Iic_finset`

English:
theorem card_Iic_finset
  statement: (Iic s).card = 2 ^ s.card
  proof: by rw [Iic_eq_powerset, card_powerset]

中文:
定理 card_Iic_finset
  结论: (左无界右闭区间 s).card = 2 ^ s.card
  证明: by rw [Iic_eq_powerset, card_powerset]

Depends on / 依赖: Iic_eq_powerset, card_powerset
-/
theorem card_Iic_finset : (Iic s).card = 2 ^ s.card := by rw [Iic_eq_powerset, card_powerset]

/--
theorem `card_Iio_finset` / 定理 `card_Iio_finset`

English:
theorem card_Iio_finset
  statement: (Iio s).card = 2 ^ s.card - 1
  proof: by
  rw [Iio_eq_ssubsets]; rw [ssubsets]; rw [card_erase_of_mem (mem_powerset_self _)]; rw [card_powerset]

中文:
定理 card_Iio_finset
  结论: (左无界右开区间 s).card = 2 ^ s.card - 1
  证明: by
  rw [Iio_eq_ssubsets]; rw [ssubsets]; rw [card_erase_of_mem (mem_powerset_self _)]; rw [card_powerset]

Depends on / 依赖: Iio_eq_ssubsets, card_erase_of_mem, card_powerset, mem_powerset_self, ssubsets
-/
theorem card_Iio_finset : (Iio s).card = 2 ^ s.card - 1 := by
  rw [Iio_eq_ssubsets]; rw [ssubsets]; rw [card_erase_of_mem (mem_powerset_self _)]; rw [card_powerset]

end Decidable

variable [Preorder β] {s t : Finset α} {f : Finset α -> β}

section Cons

/--
lemma `monotone_iff_forall_le_cons` / 引理 `monotone_iff_forall_le_cons`

English:
lemma monotone_iff_forall_le_cons
  statement: Monotone f ↔ forall s, forall ⦃a⦄ (ha), f s <= f (cons a s ha)
  proof: by
  classical simp [monotone_iff_forall_covBy, covBy_iff_exists_cons]

中文:
引理 monotone_iff_对任意_le_cons
  结论: 递增 f ↔ 对任意 s, 对任意 ⦃a⦄ (ha), f s <= f (cons a s ha)
  证明: by
  classical simp [monotone_iff_forall_covBy, covBy_iff_exists_cons]

Depends on / 依赖: classical, covBy_iff_exists_cons, monotone_iff_forall_covBy
-/
lemma monotone_iff_forall_le_cons : Monotone f ↔ forall s, forall ⦃a⦄ (ha), f s <= f (cons a s ha) := by
  classical simp [monotone_iff_forall_covBy, covBy_iff_exists_cons]

/--
lemma `antitone_iff_forall_cons_le` / 引理 `antitone_iff_forall_cons_le`

English:
lemma antitone_iff_forall_cons_le
  statement: Antitone f ↔ forall s ⦃a⦄ ha, f (cons a s ha) <= f s
  proof: monotone_iff_forall_le_cons (β := βᵒᵈ)

中文:
引理 antitone_iff_对任意_cons_le
  结论: 递减 f ↔ 对任意 s ⦃a⦄ ha, f (cons a s ha) <= f s
  证明: monotone_iff_forall_le_cons (β := βᵒᵈ)

Depends on / 依赖: monotone_iff_forall_le_cons
-/
lemma antitone_iff_forall_cons_le : Antitone f ↔ forall s ⦃a⦄ ha, f (cons a s ha) <= f s :=
  monotone_iff_forall_le_cons (β := βᵒᵈ)

/--
lemma `strictMono_iff_forall_lt_cons` / 引理 `strictMono_iff_forall_lt_cons`

English:
lemma strictMono_iff_forall_lt_cons
  statement: StrictMono f ↔ forall s ⦃a⦄ ha, f s < f (cons a s ha)
  proof: by
  classical simp [strictMono_iff_forall_covBy, covBy_iff_exists_cons]

中文:
引理 strictMono_iff_对任意_lt_cons
  结论: 严格递增 f ↔ 对任意 s ⦃a⦄ ha, f s < f (cons a s ha)
  证明: by
  classical simp [strictMono_iff_forall_covBy, covBy_iff_exists_cons]

Depends on / 依赖: classical, covBy_iff_exists_cons, strictMono_iff_forall_covBy
-/
lemma strictMono_iff_forall_lt_cons : StrictMono f ↔ forall s ⦃a⦄ ha, f s < f (cons a s ha) := by
  classical simp [strictMono_iff_forall_covBy, covBy_iff_exists_cons]

/--
lemma `strictAnti_iff_forall_cons_lt` / 引理 `strictAnti_iff_forall_cons_lt`

English:
lemma strictAnti_iff_forall_cons_lt
  statement: StrictAnti f ↔ forall s ⦃a⦄ ha, f (cons a s ha) < f s
  proof: strictMono_iff_forall_lt_cons (β := βᵒᵈ)

中文:
引理 strictAnti_iff_对任意_cons_lt
  结论: 严格递减 f ↔ 对任意 s ⦃a⦄ ha, f (cons a s ha) < f s
  证明: strictMono_iff_forall_lt_cons (β := βᵒᵈ)

Depends on / 依赖: strictMono_iff_forall_lt_cons
-/
lemma strictAnti_iff_forall_cons_lt : StrictAnti f ↔ forall s ⦃a⦄ ha, f (cons a s ha) < f s :=
  strictMono_iff_forall_lt_cons (β := βᵒᵈ)

end Cons

section Insert

variable [DecidableEq α]

/--
lemma `monotone_iff_forall_le_insert` / 引理 `monotone_iff_forall_le_insert`

English:
lemma monotone_iff_forall_le_insert
  statement: Monotone f ↔ forall s ⦃a⦄, a ∉ s -> f s <= f (insert a s)
  proof: by
  simp [monotone_iff_forall_le_cons]

中文:
引理 monotone_iff_对任意_le_insert
  结论: 递增 f ↔ 对任意 s ⦃a⦄, a ∉ s -> f s <= f (insert a s)
  证明: by
  simp [monotone_iff_forall_le_cons]

Depends on / 依赖: monotone_iff_forall_le_cons
-/
lemma monotone_iff_forall_le_insert : Monotone f ↔ forall s ⦃a⦄, a ∉ s -> f s <= f (insert a s) := by
  simp [monotone_iff_forall_le_cons]

/--
lemma `antitone_iff_forall_insert_le` / 引理 `antitone_iff_forall_insert_le`

English:
lemma antitone_iff_forall_insert_le
  statement: Antitone f ↔ forall s ⦃a⦄, a ∉ s -> f (insert a s) <= f s
  proof: monotone_iff_forall_le_insert (β := βᵒᵈ)

中文:
引理 antitone_iff_对任意_insert_le
  结论: 递减 f ↔ 对任意 s ⦃a⦄, a ∉ s -> f (insert a s) <= f s
  证明: monotone_iff_forall_le_insert (β := βᵒᵈ)

Depends on / 依赖: monotone_iff_forall_le_insert
-/
lemma antitone_iff_forall_insert_le : Antitone f ↔ forall s ⦃a⦄, a ∉ s -> f (insert a s) <= f s :=
  monotone_iff_forall_le_insert (β := βᵒᵈ)

/--
lemma `strictMono_iff_forall_lt_insert` / 引理 `strictMono_iff_forall_lt_insert`

English:
lemma strictMono_iff_forall_lt_insert
  statement: StrictMono f ↔ forall s ⦃a⦄, a ∉ s -> f s < f (insert a s)
  proof: by
  simp [strictMono_iff_forall_lt_cons]

中文:
引理 strictMono_iff_对任意_lt_insert
  结论: 严格递增 f ↔ 对任意 s ⦃a⦄, a ∉ s -> f s < f (insert a s)
  证明: by
  simp [strictMono_iff_forall_lt_cons]

Depends on / 依赖: strictMono_iff_forall_lt_cons
-/
lemma strictMono_iff_forall_lt_insert : StrictMono f ↔ forall s ⦃a⦄, a ∉ s -> f s < f (insert a s) := by
  simp [strictMono_iff_forall_lt_cons]

/--
lemma `strictAnti_iff_forall_lt_insert` / 引理 `strictAnti_iff_forall_lt_insert`

English:
lemma strictAnti_iff_forall_lt_insert
  statement: StrictAnti f ↔ forall s ⦃a⦄, a ∉ s -> f (insert a s) < f s
  proof: strictMono_iff_forall_lt_insert (β := βᵒᵈ)

中文:
引理 strictAnti_iff_对任意_lt_insert
  结论: 严格递减 f ↔ 对任意 s ⦃a⦄, a ∉ s -> f (insert a s) < f s
  证明: strictMono_iff_forall_lt_insert (β := βᵒᵈ)

Depends on / 依赖: strictMono_iff_forall_lt_insert
-/
lemma strictAnti_iff_forall_lt_insert : StrictAnti f ↔ forall s ⦃a⦄, a ∉ s -> f (insert a s) < f s :=
  strictMono_iff_forall_lt_insert (β := βᵒᵈ)

end Insert

end Finset
