/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.CountableSeparatingOn

/-!
# Countably many infinite intervals separate points

In this file we prove that in a linear order with second countable order topology,
the points can be separated by countably many infinite intervals.
We prove 4 versions of this statement (one for each of the infinite intervals),
as well as provide convenience corollaries about `Filter.EventuallyEq`.
-/

public section

open Set

variable {X : Type*} [TopologicalSpace X] [LinearOrder X]
  [OrderTopology X] [SecondCountableTopology X]

namespace HasCountableSeparatingOn

variable {s : Set X}

/--
Instance `range_Iio` / 实例 `range_Iio`

English:
instance range_Iio
  signature: : HasCountableSeparatingOn X (· in range Iio) s
  body: by
  constructor
  rcases TopologicalSpace.exists_countable_dense X with ⟨s, hsc, hsd⟩
  set t := s union {x | exists y, y ⋖ x}
  refine ⟨Iio '' t, .image ?_ _, ?_, ?_⟩
  · exact hsc.union countable_setOfPred_covBy_left
  · exact image_subset_range _ _
  · rintro x - y - h
    by_contra! hne
    wlo

中文:
实例 range_Iio
  签名: : HasCountableSeparatingOn X (· in range Iio) s
  定义体: by
  constructor
  rcases TopologicalSpace.exists_countable_dense X with ⟨s, hsc, hsd⟩
  set t := s union {x | exists y, y ⋖ x}
  refine ⟨Iio '' t, .image ?_ _, ?_, ?_⟩
  · exact hsc.union countable_setOfPred_covBy_left
  · exact image_subset_range _ _
  · rintro x - y - h
    by_contra! hne
    wlo

Depends on / 依赖: TopologicalSpace, TopologicalSpace.exists_countable_dense, countable_setOfPred_covBy_left, eq_empty_or_nonempty, exists_countable_dense, generalizing, hne.lt_or_gt.resolve_left, hne.symm, hsc.union, iff_comm, image_subset_range, lt_or_gt, mem_image_of_mem, resolve_left, specialize
-/
instance range_Iio : HasCountableSeparatingOn X (· in range Iio) s := by
  constructor
  rcases TopologicalSpace.exists_countable_dense X with ⟨s, hsc, hsd⟩
  set t := s union {x | exists y, y ⋖ x}
  refine ⟨Iio '' t, .image ?_ _, ?_, ?_⟩
  · exact hsc.union countable_setOfPred_covBy_left
  · exact image_subset_range _ _
  · rintro x - y - h
    by_contra! hne
    wlog hlt : x < y generalizing x y
    · refine this y x ?_ hne.symm (hne.lt_or_gt.resolve_left hlt)
      simpa only [iff_comm] using h
    cases (Ioo x y).eq_empty_or_nonempty with
    | inl he =>
      specialize h (Iio y) (mem_image_of_mem _ (.inr ⟨x, hlt, by simpa using Set.ext_iff.mp he⟩))
      simp [hlt.not_ge] at h
    | inr hne =>
      rcases hsd.inter_open_nonempty _ isOpen_Ioo hne with ⟨z, ⟨hxz, hzy⟩, hzs⟩
      simpa [hxz, hzy.not_gt] using h (Iio z) (mem_image_of_mem _ (.inl hzs))

/--
Instance `range_Ioi` / 实例 `range_Ioi`

English:
instance range_Ioi
  signature: : HasCountableSeparatingOn X (· in range Ioi) s
  body: .range_Iio (X := Xᵒᵈ)

中文:
实例 range_Ioi
  签名: : HasCountableSeparatingOn X (· in range Ioi) s
  定义体: .range_Iio (X := Xᵒᵈ)

Depends on / 依赖: range_Iio
-/
instance range_Ioi : HasCountableSeparatingOn X (· in range Ioi) s :=
  .range_Iio (X := Xᵒᵈ)

/--
Instance `range_Iic` / 实例 `range_Iic`

English:
instance range_Iic
  signature: : HasCountableSeparatingOn X (· in range Iic) s
  body: let ⟨t, htc, ht_sub, ht⟩ := (range_Ioi (X := X) (s := s)).1
  ⟨compl '' t, htc.image _, by simpa [← compl_inj_iff (x := Ioi _)] using ht_sub,
    by simpa [not_iff_not]⟩

中文:
实例 range_Iic
  签名: : HasCountableSeparatingOn X (· in range Iic) s
  定义体: let ⟨t, htc, ht_sub, ht⟩ := (range_Ioi (X := X) (s := s)).1
  ⟨compl '' t, htc.image _, by simpa [← compl_inj_iff (x := Ioi _)] using ht_sub,
    by simpa [not_iff_not]⟩

Depends on / 依赖: compl_inj_iff, ht_sub, htc.image, not_iff_not, range_Ioi
-/
instance range_Iic : HasCountableSeparatingOn X (· in range Iic) s :=
  let ⟨t, htc, ht_sub, ht⟩ := (range_Ioi (X := X) (s := s)).1
  ⟨compl '' t, htc.image _, by simpa [← compl_inj_iff (x := Ioi _)] using ht_sub,
    by simpa [not_iff_not]⟩

/--
Instance `range_Ici` / 实例 `range_Ici`

English:
instance range_Ici
  signature: : HasCountableSeparatingOn X (· in range Ici) s
  body: range_Iic (X := Xᵒᵈ)

中文:
实例 range_Ici
  签名: : HasCountableSeparatingOn X (· in range Ici) s
  定义体: range_Iic (X := Xᵒᵈ)

Depends on / 依赖: range_Iic
-/
instance range_Ici : HasCountableSeparatingOn X (· in range Ici) s :=
  range_Iic (X := Xᵒᵈ)

end HasCountableSeparatingOn

namespace Filter.EventuallyEq

variable {α : Type*} {l : Filter α} [CountableInterFilter l] {f g : α -> X}

/--
lemma `of_forall_eventually_lt_iff` / 引理 `of_forall_eventually_lt_iff`

English:
lemma of_forall_eventually_lt_iff
  given: (h : forall x, forallᶠ a in l, f a < x ↔ g a < x)
  statement: f =ᶠ[l] g
  proof: of_forall_separating_preimage (· in range Iio) forall_mem_range.2 fun x => .set_eq (h x)

中文:
引理 of_forall_eventually_lt_iff
  条件: (h : 对任意 x, 对任意ᶠ a in l, f a < x ↔ g a < x)
  结论: f =ᶠ[l] g
  证明: of_forall_separating_preimage (· in range Iio) forall_mem_range.2 fun x => .set_eq (h x)

Depends on / 依赖: forall_mem_range, of_forall_separating_preimage, set_eq
-/
lemma of_forall_eventually_lt_iff (h : forall x, forallᶠ a in l, f a < x ↔ g a < x) : f =ᶠ[l] g :=
of_forall_separating_preimage (· in range Iio) forall_mem_range.2 fun x => .set_eq (h x)

/--
lemma `of_forall_eventually_le_iff` / 引理 `of_forall_eventually_le_iff`

English:
lemma of_forall_eventually_le_iff
  given: (h : forall x, forallᶠ a in l, f a <= x ↔ g a <= x)
  statement: f =ᶠ[l] g
  proof: of_forall_separating_preimage (· in range Iic) forall_mem_range.2 fun x => .set_eq (h x)

中文:
引理 of_forall_eventually_le_iff
  条件: (h : 对任意 x, 对任意ᶠ a in l, f a <= x ↔ g a <= x)
  结论: f =ᶠ[l] g
  证明: of_forall_separating_preimage (· in range Iic) forall_mem_range.2 fun x => .set_eq (h x)

Depends on / 依赖: forall_mem_range, of_forall_separating_preimage, set_eq
-/
lemma of_forall_eventually_le_iff (h : forall x, forallᶠ a in l, f a <= x ↔ g a <= x) : f =ᶠ[l] g :=
of_forall_separating_preimage (· in range Iic) forall_mem_range.2 fun x => .set_eq (h x)

/--
lemma `of_forall_eventually_gt_iff` / 引理 `of_forall_eventually_gt_iff`

English:
lemma of_forall_eventually_gt_iff
  given: (h : forall x, forallᶠ a in l, x < f a ↔ x < g a)
  statement: f =ᶠ[l] g
  proof: of_forall_eventually_lt_iff (X := Xᵒᵈ) h

中文:
引理 of_forall_eventually_gt_iff
  条件: (h : 对任意 x, 对任意ᶠ a in l, x < f a ↔ x < g a)
  结论: f =ᶠ[l] g
  证明: of_forall_eventually_lt_iff (X := Xᵒᵈ) h

Depends on / 依赖: of_forall_eventually_lt_iff
-/
lemma of_forall_eventually_gt_iff (h : forall x, forallᶠ a in l, x < f a ↔ x < g a) : f =ᶠ[l] g :=
  of_forall_eventually_lt_iff (X := Xᵒᵈ) h

/--
lemma `of_forall_eventually_ge_iff` / 引理 `of_forall_eventually_ge_iff`

English:
lemma of_forall_eventually_ge_iff
  given: (h : forall x, forallᶠ a in l, x <= f a ↔ x <= g a)
  statement: f =ᶠ[l] g
  proof: of_forall_eventually_le_iff (X := Xᵒᵈ) h

中文:
引理 of_forall_eventually_ge_iff
  条件: (h : 对任意 x, 对任意ᶠ a in l, x <= f a ↔ x <= g a)
  结论: f =ᶠ[l] g
  证明: of_forall_eventually_le_iff (X := Xᵒᵈ) h

Depends on / 依赖: of_forall_eventually_le_iff
-/
lemma of_forall_eventually_ge_iff (h : forall x, forallᶠ a in l, x <= f a ↔ x <= g a) : f =ᶠ[l] g :=
  of_forall_eventually_le_iff (X := Xᵒᵈ) h

end Filter.EventuallyEq
