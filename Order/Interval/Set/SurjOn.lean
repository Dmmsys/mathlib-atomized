/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Monotone surjective functions are surjective on intervals

A monotone surjective function sends any interval in the domain onto the interval with corresponding
endpoints in the range. This is expressed in this file using `Set.surjOn`, and provided for all
permutations of interval endpoints.
-/

public section


variable {α : Type*} {β : Type*} [LinearOrder α] [PartialOrder β] {f : α -> β}

open Set Function

open OrderDual (toDual)

/--
theorem `surjOn_Ioo_of_monotone_surjective` / 定理 `surjOn_Ioo_of_monotone_surjective`

English:
theorem surjOn_Ioo_of_monotone_surjective
  statement: (h_mono : Monotone f) (h_surj : Function.Surjective f)
  proof: by
  intro p hp
  rcases h_surj p with ⟨x, rfl⟩
  refine ⟨x, mem_Ioo.2 ?_, rfl⟩
  contrapose! hp
  exact fun h => h.2.not_ge (h_mono <| hp <| h_mono.reflect_lt h.1)

中文:
定理 surjOn_Ioo_of_monotone_surjective
  结论: (h_mono : 递增 f) (h_surj : 函数.满射 f)
  证明: by
  intro p hp
  rcases h_surj p with ⟨x, rfl⟩
  refine ⟨x, mem_Ioo.2 ?_, rfl⟩
  contrapose! hp
  exact fun h => h.2.not_ge (h_mono <| hp <| h_mono.reflect_lt h.1)

Depends on / 依赖: Ideal.finiteHeight_of_finiteRingKrullDim, contrapose, finiteHeight_of_finiteRingKrullDim, h_mono, h_mono.reflect_lt, h_surj, mem_Ioo, not_ge, reflect_lt
-/
theorem surjOn_Ioo_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ioo a b) (Ioo (f a) (f b)) := by
  intro p hp
  rcases h_surj p with ⟨x, rfl⟩
  refine ⟨x, mem_Ioo.2 ?_, rfl⟩
  contrapose! hp
  exact fun h => h.2.not_ge (h_mono <| hp <| h_mono.reflect_lt h.1)

/--
theorem `surjOn_Ico_of_monotone_surjective` / 定理 `surjOn_Ico_of_monotone_surjective`

English:
theorem surjOn_Ico_of_monotone_surjective
  statement: (h_mono : Monotone f) (h_surj : Function.Surjective f)
  proof: by
  obtain hab | hab := lt_or_ge a b
  · intro p hp
    rcases eq_left_or_mem_Ioo_of_mem_Ico hp with (rfl | hp')
    · exact mem_image_of_mem f (left_mem_Ico.mpr hab)
· exact image_mono Ioo_subset_Ico_self
        surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'
  · rw [Ico_eq_empty (h_mono hab).not_gt]
    exact surjOn_empty f _

中文:
定理 surjOn_Ico_of_monotone_surjective
  结论: (h_mono : 递增 f) (h_surj : 函数.满射 f)
  证明: by
  obtain hab | hab := lt_or_ge a b
  · intro p hp
    rcases eq_left_or_mem_Ioo_of_mem_Ico hp with (rfl | hp')
    · exact mem_image_of_mem f (left_mem_Ico.mpr hab)
· exact image_mono Ioo_subset_Ico_self
        surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'
  · rw [Ico_eq_empty (h_mono hab).not_gt]
    exact surjOn_empty f _

Depends on / 依赖: Ico_eq_empty, Ioo_subset_Ico_self, eq_left_or_mem_Ioo_of_mem_Ico, h_mono, h_surj, image_mono, left_mem_Ico, left_mem_Ico.mpr, lt_or_ge, mem_image_of_mem, not_gt, surjOn_Ioo_of_monotone_surjective, surjOn_empty
-/
theorem surjOn_Ico_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ico a b) (Ico (f a) (f b)) := by
  obtain hab | hab := lt_or_ge a b
  · intro p hp
    rcases eq_left_or_mem_Ioo_of_mem_Ico hp with (rfl | hp')
    · exact mem_image_of_mem f (left_mem_Ico.mpr hab)
· exact image_mono Ioo_subset_Ico_self
        surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'
  · rw [Ico_eq_empty (h_mono hab).not_gt]
    exact surjOn_empty f _

/--
theorem `surjOn_Ioc_of_monotone_surjective` / 定理 `surjOn_Ioc_of_monotone_surjective`

English:
theorem surjOn_Ioc_of_monotone_surjective
  statement: (h_mono : Monotone f) (h_surj : Function.Surjective f)
  proof: by
  simpa using! surjOn_Ico_of_monotone_surjective h_mono.dual h_surj (toDual b) (toDual a)

中文:
定理 surjOn_Ioc_of_monotone_surjective
  结论: (h_mono : 递增 f) (h_surj : 函数.满射 f)
  证明: by
  simpa using! surjOn_Ico_of_monotone_surjective h_mono.dual h_surj (toDual b) (toDual a)

Depends on / 依赖: h_mono, h_mono.dual, h_surj, surjOn_Ico_of_monotone_surjective, toDual
-/
theorem surjOn_Ioc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ioc a b) (Ioc (f a) (f b)) := by
  simpa using! surjOn_Ico_of_monotone_surjective h_mono.dual h_surj (toDual b) (toDual a)

-- to see that the hypothesis `a ≤ b` is necessary, consider a constant function
/--
theorem `surjOn_Icc_of_monotone_surjective` / 定理 `surjOn_Icc_of_monotone_surjective`

English:
theorem surjOn_Icc_of_monotone_surjective
  statement: (h_mono : Monotone f) (h_surj : Function.Surjective f)
  proof: by
  intro p hp
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with (rfl | rfl | hp')
  · exact ⟨a, left_mem_Icc.mpr hab, rfl⟩
  · exact ⟨b, right_mem_Icc.mpr hab, rfl⟩
· exact image_mono Ioo_subset_Icc_self
      surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'

中文:
定理 surjOn_Icc_of_monotone_surjective
  结论: (h_mono : 递增 f) (h_surj : 函数.满射 f)
  证明: by
  intro p hp
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with (rfl | rfl | hp')
  · exact ⟨a, left_mem_Icc.mpr hab, rfl⟩
  · exact ⟨b, right_mem_Icc.mpr hab, rfl⟩
· exact image_mono Ioo_subset_Icc_self
      surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'

Depends on / 依赖: Ioo_subset_Icc_self, eq_endpoints_or_mem_Ioo_of_mem_Icc, h_mono, h_surj, image_mono, left_mem_Icc, left_mem_Icc.mpr, right_mem_Icc, right_mem_Icc.mpr, surjOn_Ioo_of_monotone_surjective
-/
theorem surjOn_Icc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    {a b : α} (hab : a <= b) : SurjOn f (Icc a b) (Icc (f a) (f b)) := by
  intro p hp
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with (rfl | rfl | hp')
  · exact ⟨a, left_mem_Icc.mpr hab, rfl⟩
  · exact ⟨b, right_mem_Icc.mpr hab, rfl⟩
· exact image_mono Ioo_subset_Icc_self
      surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'

/--
theorem `surjOn_Ioi_of_monotone_surjective` / 定理 `surjOn_Ioi_of_monotone_surjective`

English:
theorem surjOn_Ioi_of_monotone_surjective
  statement: (h_mono : Monotone f) (h_surj : Function.Surjective f)
  proof: by
  rw [← compl_Iic]; rw [← compl_compl (Ioi (f a))]
  refine MapsTo.surjOn_compl ?_ h_surj
  exact fun x hx => (h_mono hx).not_gt

中文:
定理 surjOn_Ioi_of_monotone_surjective
  结论: (h_mono : 递增 f) (h_surj : 函数.满射 f)
  证明: by
  rw [← compl_Iic]; rw [← compl_compl (Ioi (f a))]
  refine MapsTo.surjOn_compl ?_ h_surj
  exact fun x hx => (h_mono hx).not_gt

Depends on / 依赖: MapsTo, MapsTo.surjOn_compl, compl_Iic, compl_compl, h_mono, h_surj, not_gt, surjOn_compl
-/
theorem surjOn_Ioi_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Ioi a) (Ioi (f a)) := by
  rw [← compl_Iic]; rw [← compl_compl (Ioi (f a))]
  refine MapsTo.surjOn_compl ?_ h_surj
  exact fun x hx => (h_mono hx).not_gt

/--
theorem `surjOn_Iio_of_monotone_surjective` / 定理 `surjOn_Iio_of_monotone_surjective`

English:
theorem surjOn_Iio_of_monotone_surjective
  statement: (h_mono : Monotone f) (h_surj : Function.Surjective f)
  proof: @surjOn_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

中文:
定理 surjOn_Iio_of_monotone_surjective
  结论: (h_mono : 递增 f) (h_surj : 函数.满射 f)
  证明: @surjOn_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

Depends on / 依赖: h_mono, h_mono.dual, h_surj, surjOn_Ioi_of_monotone_surjective
-/
theorem surjOn_Iio_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Iio a) (Iio (f a)) :=
  @surjOn_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

/--
theorem `surjOn_Ici_of_monotone_surjective` / 定理 `surjOn_Ici_of_monotone_surjective`

English:
theorem surjOn_Ici_of_monotone_surjective
  statement: (h_mono : Monotone f) (h_surj : Function.Surjective f)
  proof: by
  rw [← Ioi_union_left]; rw [← Ioi_union_left]
  exact
    (surjOn_Ioi_of_monotone_surjective h_mono h_surj a).union_union
      (@image_singleton _ _ f a ▸ surjOn_image _ _)

中文:
定理 surjOn_Ici_of_monotone_surjective
  结论: (h_mono : 递增 f) (h_surj : 函数.满射 f)
  证明: by
  rw [← Ioi_union_left]; rw [← Ioi_union_left]
  exact
    (surjOn_Ioi_of_monotone_surjective h_mono h_surj a).union_union
      (@image_singleton _ _ f a ▸ surjOn_image _ _)

Depends on / 依赖: Ioi_union_left, h_mono, h_surj, image_singleton, surjOn_Ioi_of_monotone_surjective, surjOn_image, union_union
-/
theorem surjOn_Ici_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Ici a) (Ici (f a)) := by
  rw [← Ioi_union_left]; rw [← Ioi_union_left]
  exact
    (surjOn_Ioi_of_monotone_surjective h_mono h_surj a).union_union
      (@image_singleton _ _ f a ▸ surjOn_image _ _)

/--
theorem `surjOn_Iic_of_monotone_surjective` / 定理 `surjOn_Iic_of_monotone_surjective`

English:
theorem surjOn_Iic_of_monotone_surjective
  statement: (h_mono : Monotone f) (h_surj : Function.Surjective f)
  proof: @surjOn_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

中文:
定理 surjOn_Iic_of_monotone_surjective
  结论: (h_mono : 递增 f) (h_surj : 函数.满射 f)
  证明: @surjOn_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

Depends on / 依赖: h_mono, h_mono.dual, h_surj, surjOn_Ici_of_monotone_surjective
-/
theorem surjOn_Iic_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Iic a) (Iic (f a)) :=
  @surjOn_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a
