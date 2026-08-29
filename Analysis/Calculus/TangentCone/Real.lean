/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Unique differentiability property in real normed spaces

In this file we prove that

- `uniqueDiffOn_convex`: a convex set with nonempty interior in a real normed space
  has the unique differentiability property;
- `uniqueDiffOn_Ioc` etc: intervals on the real line have the unique differentiability property.
-/

public section

open Filter Set
open scoped Topology NNReal

section RealTVS

variable {E : Type*} [AddCommGroup E] [Module Real E] [TopologicalSpace E] [ContinuousSMul Real E]
  {s : Set E} {x y : E}

/--
theorem `sub_mem_posTangentConeAt_of_openSegment_subset` / 定理 `sub_mem_posTangentConeAt_of_openSegment_subset`

English:
theorem sub_mem_posTangentConeAt_of_openSegment_subset
  given: (h : openSegment Real x y subseteq s)
  proof: by
  refine mem_tangentConeAt_of_add_smul_mem (tendsto_id'.mpr <| nhdsGT_le_nhdsNE 0) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with a ha
  apply h
  rw [openSegment_eq_image_lineMap]
  use a, mod_cast ha
  simp [AffineMap.lineMap_apply_module', add_comm, NNReal.smul_def]

中文:
定理 sub_mem_posTangentConeAt_of_openSegment_subset
  条件: (h : openSegment 实数 x y subseteq s)
  证明: by
  refine mem_tangentConeAt_of_add_smul_mem (tendsto_id'.mpr <| nhdsGT_le_nhdsNE 0) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with a ha
  apply h
  rw [openSegment_eq_image_lineMap]
  use a, mod_cast ha
  simp [AffineMap.lineMap_apply_module', add_comm, NNReal.smul_def]

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_module, Ioo_mem_nhdsGT, NNReal, NNReal.smul_def, add_comm, filter_upwards, lineMap_apply_module, mem_tangentConeAt_of_add_smul_mem, mod_cast, nhdsGT_le_nhdsNE, one_pos, openSegment_eq_image_lineMap, smul_def, tendsto_id
-/
theorem sub_mem_posTangentConeAt_of_openSegment_subset (h : openSegment Real x y subseteq s) :
    y - x in tangentConeAt Real>=0 s x := by
  refine mem_tangentConeAt_of_add_smul_mem (tendsto_id'.mpr <| nhdsGT_le_nhdsNE 0) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with a ha
  apply h
  rw [openSegment_eq_image_lineMap]
  use a, mod_cast ha
  simp [AffineMap.lineMap_apply_module', add_comm, NNReal.smul_def]

/--
theorem `mem_tangentConeAt_of_openSegment_subset` / 定理 `mem_tangentConeAt_of_openSegment_subset`

English:
theorem mem_tangentConeAt_of_openSegment_subset
  given: (h : openSegment Real x y subseteq s)
  proof: tangentConeAt_mono_field (sub_mem_posTangentConeAt_of_openSegment_subset h)

中文:
定理 mem_tangentConeAt_of_openSegment_subset
  条件: (h : openSegment 实数 x y subseteq s)
  证明: tangentConeAt_mono_field (sub_mem_posTangentConeAt_of_openSegment_subset h)

Depends on / 依赖: sub_mem_posTangentConeAt_of_openSegment_subset, tangentConeAt_mono_field
-/
theorem mem_tangentConeAt_of_openSegment_subset (h : openSegment Real x y subseteq s) :
    y - x in tangentConeAt Real s x :=
  tangentConeAt_mono_field (sub_mem_posTangentConeAt_of_openSegment_subset h)

/--
theorem `mem_tangentConeAt_of_segment_subset` / 定理 `mem_tangentConeAt_of_segment_subset`

English:
theorem mem_tangentConeAt_of_segment_subset
  given: (h : segment Real x y subseteq s)
  proof: mem_tangentConeAt_of_openSegment_subset ((openSegment_subset_segment Real x y).trans h)

中文:
定理 mem_tangentConeAt_of_segment_subset
  条件: (h : segment 实数 x y subseteq s)
  证明: mem_tangentConeAt_of_openSegment_subset ((openSegment_subset_segment Real x y).trans h)

Depends on / 依赖: mem_tangentConeAt_of_openSegment_subset, openSegment_subset_segment
-/
theorem mem_tangentConeAt_of_segment_subset (h : segment Real x y subseteq s) :
    y - x in tangentConeAt Real s x :=
  mem_tangentConeAt_of_openSegment_subset ((openSegment_subset_segment Real x y).trans h)

variable [IsTopologicalAddGroup E]

/--
theorem `Convex.span_tangentConeAt` / 定理 `Convex.span_tangentConeAt`

English:
theorem Convex.span_tangentConeAt
  statement: (conv : Convex Real s) (hs : (interior s).Nonempty)
  proof: by
  rcases hs with ⟨y, hy⟩
  suffices y - x in interior (tangentConeAt Real s x) by
    apply (Submodule.span Real (tangentConeAt Real s x)).eq_top_of_nonempty_interior'
    exact ⟨y - x, interior_mono Submodule.subset_span this⟩
  rw [mem_interior_iff_mem_nhds]
  replace hy : interior s in 𝓝 y := IsOpen.mem_nhds isOpen_interior hy
  apply mem_of_superset ((isOpenMap_sub_right x).image_mem_nhds hy)
  rintro _ ⟨z, zs, rfl⟩
  refine mem_tangentConeAt_of_openSegment_subset (Subset.trans ?_ interior_subset)
  exact conv.openSegment_closure_interior_subset_interior hx zs

中文:
定理 凸.span_tangentConeAt
  结论: (conv : 凸 实数 s) (hs : (interior s).非空)
  证明: by
  rcases hs with ⟨y, hy⟩
  suffices y - x in interior (tangentConeAt Real s x) by
    apply (Submodule.span Real (tangentConeAt Real s x)).eq_top_of_nonempty_interior'
    exact ⟨y - x, interior_mono Submodule.subset_span this⟩
  rw [mem_interior_iff_mem_nhds]
  replace hy : interior s in 𝓝 y := IsOpen.mem_nhds isOpen_interior hy
  apply mem_of_superset ((isOpenMap_sub_right x).image_mem_nhds hy)
  rintro _ ⟨z, zs, rfl⟩
  refine mem_tangentConeAt_of_openSegment_subset (Subset.trans ?_ interior_subset)
  exact conv.openSegment_closure_interior_subset_interior hx zs

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, Submodule, Submodule.span, Submodule.subset_span, Subset, Subset.trans, conv.o, eq_top_of_nonempty_interior, image_mem_nhds, interior, interior_mono, interior_subset, isOpenMap_sub_right, isOpen_interior, mem_interior_iff_mem_nhds, mem_nhds, mem_of_superset, mem_tangentConeAt_of_openSegment_subset, replace
-/
theorem Convex.span_tangentConeAt (conv : Convex Real s) (hs : (interior s).Nonempty)
    (hx : x in closure s) :
    Submodule.span Real (tangentConeAt Real s x) = ⊤ := by
  rcases hs with ⟨y, hy⟩
  suffices y - x in interior (tangentConeAt Real s x) by
    apply (Submodule.span Real (tangentConeAt Real s x)).eq_top_of_nonempty_interior'
    exact ⟨y - x, interior_mono Submodule.subset_span this⟩
  rw [mem_interior_iff_mem_nhds]
  replace hy : interior s in 𝓝 y := IsOpen.mem_nhds isOpen_interior hy
  apply mem_of_superset ((isOpenMap_sub_right x).image_mem_nhds hy)
  rintro _ ⟨z, zs, rfl⟩
  refine mem_tangentConeAt_of_openSegment_subset (Subset.trans ?_ interior_subset)
  exact conv.openSegment_closure_interior_subset_interior hx zs

/--
theorem `uniqueDiffWithinAt_convex` / 定理 `uniqueDiffWithinAt_convex`

English:
theorem uniqueDiffWithinAt_convex
  statement: (conv : Convex Real s) (hs : (interior s).Nonempty)
  proof: by
  simp [uniqueDiffWithinAt_iff, conv.span_tangentConeAt hs hx, hx]

中文:
定理 uniqueDiffWithinAt_convex
  结论: (conv : 凸 实数 s) (hs : (interior s).非空)
  证明: by
  simp [uniqueDiffWithinAt_iff, conv.span_tangentConeAt hs hx, hx]

Depends on / 依赖: conv.span_tangentConeAt, span_tangentConeAt, uniqueDiffWithinAt_iff
-/
theorem uniqueDiffWithinAt_convex (conv : Convex Real s) (hs : (interior s).Nonempty)
    {x : E} (hx : x in closure s) : UniqueDiffWithinAt Real s x := by
  simp [uniqueDiffWithinAt_iff, conv.span_tangentConeAt hs hx, hx]

/--
theorem `uniqueDiffOn_convex` / 定理 `uniqueDiffOn_convex`

English:
theorem uniqueDiffOn_convex
  given: (conv : Convex Real s) (hs : (interior s).Nonempty)
  proof: fun _ xs => uniqueDiffWithinAt_convex conv hs (subset_closure xs)

中文:
定理 uniqueDiffOn_convex
  条件: (conv : 凸 实数 s) (hs : (interior s).非空)
  证明: fun _ xs => uniqueDiffWithinAt_convex conv hs (subset_closure xs)

Depends on / 依赖: subset_closure, uniqueDiffWithinAt_convex
-/
theorem uniqueDiffOn_convex (conv : Convex Real s) (hs : (interior s).Nonempty) :
    UniqueDiffOn Real s :=
  fun _ xs => uniqueDiffWithinAt_convex conv hs (subset_closure xs)

end RealTVS

section Real

/--
theorem `uniqueDiffOn_Ici` / 定理 `uniqueDiffOn_Ici`

English:
theorem uniqueDiffOn_Ici
  given: (a : Real)
  statement: UniqueDiffOn Real (Ici a)
  proof: uniqueDiffOn_convex (convex_Ici a) by simp only [interior_Ici, nonempty_Ioi]

中文:
定理 uniqueDiffOn_Ici
  条件: (a : 实数)
  结论: UniqueDiffOn 实数 (左闭右无界区间 a)
  证明: uniqueDiffOn_convex (convex_Ici a) by simp only [interior_Ici, nonempty_Ioi]

Depends on / 依赖: Complex.instStarHomClass, StarHomClass, convex_Ici, instStarHomClass, interior_Ici, nonempty_Ioi, uniqueDiffOn_convex
-/
theorem uniqueDiffOn_Ici (a : Real) : UniqueDiffOn Real (Ici a) :=
uniqueDiffOn_convex (convex_Ici a) by simp only [interior_Ici, nonempty_Ioi]

/--
theorem `uniqueDiffOn_Iic` / 定理 `uniqueDiffOn_Iic`

English:
theorem uniqueDiffOn_Iic
  given: (a : Real)
  statement: UniqueDiffOn Real (Iic a)
  proof: uniqueDiffOn_convex (convex_Iic a) by simp only [interior_Iic, nonempty_Iio]

中文:
定理 uniqueDiffOn_Iic
  条件: (a : 实数)
  结论: UniqueDiffOn 实数 (左无界右闭区间 a)
  证明: uniqueDiffOn_convex (convex_Iic a) by simp only [interior_Iic, nonempty_Iio]

Depends on / 依赖: convex_Iic, interior_Iic, nonempty_Iio, uniqueDiffOn_convex
-/
theorem uniqueDiffOn_Iic (a : Real) : UniqueDiffOn Real (Iic a) :=
uniqueDiffOn_convex (convex_Iic a) by simp only [interior_Iic, nonempty_Iio]

/--
theorem `uniqueDiffOn_Ioi` / 定理 `uniqueDiffOn_Ioi`

English:
theorem uniqueDiffOn_Ioi
  given: (a : Real)
  statement: UniqueDiffOn Real (Ioi a)
  proof: isOpen_Ioi.uniqueDiffOn

中文:
定理 uniqueDiffOn_Ioi
  条件: (a : 实数)
  结论: UniqueDiffOn 实数 (左开右无界区间 a)
  证明: isOpen_Ioi.uniqueDiffOn

Depends on / 依赖: isOpen_Ioi, isOpen_Ioi.uniqueDiffOn, uniqueDiffOn
-/
theorem uniqueDiffOn_Ioi (a : Real) : UniqueDiffOn Real (Ioi a) :=
  isOpen_Ioi.uniqueDiffOn

/--
theorem `uniqueDiffOn_Iio` / 定理 `uniqueDiffOn_Iio`

English:
theorem uniqueDiffOn_Iio
  given: (a : Real)
  statement: UniqueDiffOn Real (Iio a)
  proof: isOpen_Iio.uniqueDiffOn

中文:
定理 uniqueDiffOn_Iio
  条件: (a : 实数)
  结论: UniqueDiffOn 实数 (左无界右开区间 a)
  证明: isOpen_Iio.uniqueDiffOn

Depends on / 依赖: isOpen_Iio, isOpen_Iio.uniqueDiffOn, uniqueDiffOn
-/
theorem uniqueDiffOn_Iio (a : Real) : UniqueDiffOn Real (Iio a) :=
  isOpen_Iio.uniqueDiffOn

/--
theorem `uniqueDiffOn_Icc` / 定理 `uniqueDiffOn_Icc`

English:
theorem uniqueDiffOn_Icc
  given: {a b : Real} (hab : a < b)
  statement: UniqueDiffOn Real (Icc a b)
  proof: uniqueDiffOn_convex (convex_Icc a b) by simp only [interior_Icc, nonempty_Ioo, hab]

中文:
定理 uniqueDiffOn_Icc
  条件: {a b : 实数} (hab : a < b)
  结论: UniqueDiffOn 实数 (闭区间 a b)
  证明: uniqueDiffOn_convex (convex_Icc a b) by simp only [interior_Icc, nonempty_Ioo, hab]

Depends on / 依赖: convex_Icc, interior_Icc, nonempty_Ioo, uniqueDiffOn_convex
-/
theorem uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDiffOn Real (Icc a b) :=
uniqueDiffOn_convex (convex_Icc a b) by simp only [interior_Icc, nonempty_Ioo, hab]

/--
theorem `uniqueDiffOn_uIcc` / 定理 `uniqueDiffOn_uIcc`

English:
theorem uniqueDiffOn_uIcc
  given: {a b : Real} (hab : a != b)
  statement: UniqueDiffOn Real (uIcc a b)
  proof: uniqueDiffOn_Icc min_lt_max.mpr hab

中文:
定理 uniqueDiffOn_uIcc
  条件: {a b : 实数} (hab : a != b)
  结论: UniqueDiffOn 实数 (uIcc a b)
  证明: uniqueDiffOn_Icc min_lt_max.mpr hab

Depends on / 依赖: min_lt_max, min_lt_max.mpr, uniqueDiffOn_Icc
-/
theorem uniqueDiffOn_uIcc {a b : Real} (hab : a != b) : UniqueDiffOn Real (uIcc a b) :=
uniqueDiffOn_Icc min_lt_max.mpr hab

/--
theorem `uniqueDiffOn_Ico` / 定理 `uniqueDiffOn_Ico`

English:
theorem uniqueDiffOn_Ico
  given: (a b : Real)
  statement: UniqueDiffOn Real (Ico a b)
  proof: if hab : a < b then
uniqueDiffOn_convex (convex_Ico a b) by simp only [interior_Ico, nonempty_Ioo, hab]
  else by simp only [Ico_eq_empty hab, uniqueDiffOn_empty]

中文:
定理 uniqueDiffOn_Ico
  条件: (a b : 实数)
  结论: UniqueDiffOn 实数 (左闭右开区间 a b)
  证明: if hab : a < b then
uniqueDiffOn_convex (convex_Ico a b) by simp only [interior_Ico, nonempty_Ioo, hab]
  else by simp only [Ico_eq_empty hab, uniqueDiffOn_empty]

Depends on / 依赖: Ico_eq_empty, convex_Ico, interior_Ico, nonempty_Ioo, uniqueDiffOn_convex, uniqueDiffOn_empty
-/
theorem uniqueDiffOn_Ico (a b : Real) : UniqueDiffOn Real (Ico a b) :=
  if hab : a < b then
uniqueDiffOn_convex (convex_Ico a b) by simp only [interior_Ico, nonempty_Ioo, hab]
  else by simp only [Ico_eq_empty hab, uniqueDiffOn_empty]

/--
theorem `uniqueDiffOn_Ioc` / 定理 `uniqueDiffOn_Ioc`

English:
theorem uniqueDiffOn_Ioc
  given: (a b : Real)
  statement: UniqueDiffOn Real (Ioc a b)
  proof: if hab : a < b then
uniqueDiffOn_convex (convex_Ioc a b) by simp only [interior_Ioc, nonempty_Ioo, hab]
  else by simp only [Ioc_eq_empty hab, uniqueDiffOn_empty]

中文:
定理 uniqueDiffOn_Ioc
  条件: (a b : 实数)
  结论: UniqueDiffOn 实数 (左开右闭区间 a b)
  证明: if hab : a < b then
uniqueDiffOn_convex (convex_Ioc a b) by simp only [interior_Ioc, nonempty_Ioo, hab]
  else by simp only [Ioc_eq_empty hab, uniqueDiffOn_empty]

Depends on / 依赖: Ioc_eq_empty, convex_Ioc, interior_Ioc, nonempty_Ioo, uniqueDiffOn_convex, uniqueDiffOn_empty
-/
theorem uniqueDiffOn_Ioc (a b : Real) : UniqueDiffOn Real (Ioc a b) :=
  if hab : a < b then
uniqueDiffOn_convex (convex_Ioc a b) by simp only [interior_Ioc, nonempty_Ioo, hab]
  else by simp only [Ioc_eq_empty hab, uniqueDiffOn_empty]

/--
theorem `uniqueDiffOn_Ioo` / 定理 `uniqueDiffOn_Ioo`

English:
theorem uniqueDiffOn_Ioo
  given: (a b : Real)
  statement: UniqueDiffOn Real (Ioo a b)
  proof: isOpen_Ioo.uniqueDiffOn

中文:
定理 uniqueDiffOn_Ioo
  条件: (a b : 实数)
  结论: UniqueDiffOn 实数 (开区间 a b)
  证明: isOpen_Ioo.uniqueDiffOn

Depends on / 依赖: isOpen_Ioo, isOpen_Ioo.uniqueDiffOn, uniqueDiffOn
-/
theorem uniqueDiffOn_Ioo (a b : Real) : UniqueDiffOn Real (Ioo a b) :=
  isOpen_Ioo.uniqueDiffOn

/--
theorem `uniqueDiffOn_Icc_zero_one` / 定理 `uniqueDiffOn_Icc_zero_one`

English:
theorem uniqueDiffOn_Icc_zero_one
  statement: UniqueDiffOn Real (Icc (0 : Real) 1)
  proof: uniqueDiffOn_Icc zero_lt_one

中文:
定理 uniqueDiffOn_Icc_zero_one
  结论: UniqueDiffOn 实数 (闭区间 (0 : 实数) 1)
  证明: uniqueDiffOn_Icc zero_lt_one

Depends on / 依赖: uniqueDiffOn_Icc, zero_lt_one
-/
theorem uniqueDiffOn_Icc_zero_one : UniqueDiffOn Real (Icc (0 : Real) 1) :=
  uniqueDiffOn_Icc zero_lt_one

/--
theorem `uniqueDiffWithinAt_Ioo` / 定理 `uniqueDiffWithinAt_Ioo`

English:
theorem uniqueDiffWithinAt_Ioo
  given: {a b t : Real} (ht : t in Set.Ioo a b)
  proof: IsOpen.uniqueDiffWithinAt isOpen_Ioo ht

中文:
定理 uniqueDiffWithinAt_Ioo
  条件: {a b t : 实数} (ht : t in 集合.开区间 a b)
  证明: IsOpen.uniqueDiffWithinAt isOpen_Ioo ht

Depends on / 依赖: IsOpen, IsOpen.uniqueDiffWithinAt, SubringClass, SubringClass.toNormedRing, elemental, isOpen_Ioo, mul_comm, toNormedRing, uniqueDiffWithinAt
-/
theorem uniqueDiffWithinAt_Ioo {a b t : Real} (ht : t in Set.Ioo a b) :
    UniqueDiffWithinAt Real (Set.Ioo a b) t :=
  IsOpen.uniqueDiffWithinAt isOpen_Ioo ht

/--
theorem `uniqueDiffWithinAt_Ioi` / 定理 `uniqueDiffWithinAt_Ioi`

English:
theorem uniqueDiffWithinAt_Ioi
  given: (a : Real)
  statement: UniqueDiffWithinAt Real (Ioi a) a
  proof: uniqueDiffWithinAt_convex (convex_Ioi a) (by simp) (by simp)

中文:
定理 uniqueDiffWithinAt_Ioi
  条件: (a : 实数)
  结论: UniqueDiffWithinAt 实数 (左开右无界区间 a) a
  证明: uniqueDiffWithinAt_convex (convex_Ioi a) (by simp) (by simp)

Depends on / 依赖: convex_Ioi, uniqueDiffWithinAt_convex
-/
theorem uniqueDiffWithinAt_Ioi (a : Real) : UniqueDiffWithinAt Real (Ioi a) a :=
  uniqueDiffWithinAt_convex (convex_Ioi a) (by simp) (by simp)

/--
theorem `uniqueDiffWithinAt_Iio` / 定理 `uniqueDiffWithinAt_Iio`

English:
theorem uniqueDiffWithinAt_Iio
  given: (a : Real)
  statement: UniqueDiffWithinAt Real (Iio a) a
  proof: uniqueDiffWithinAt_convex (convex_Iio a) (by simp) (by simp)

中文:
定理 uniqueDiffWithinAt_Iio
  条件: (a : 实数)
  结论: UniqueDiffWithinAt 实数 (左无界右开区间 a) a
  证明: uniqueDiffWithinAt_convex (convex_Iio a) (by simp) (by simp)

Depends on / 依赖: convex_Iio, uniqueDiffWithinAt_convex
-/
theorem uniqueDiffWithinAt_Iio (a : Real) : UniqueDiffWithinAt Real (Iio a) a :=
  uniqueDiffWithinAt_convex (convex_Iio a) (by simp) (by simp)

/--
theorem `uniqueDiffWithinAt_Ici` / 定理 `uniqueDiffWithinAt_Ici`

English:
theorem uniqueDiffWithinAt_Ici
  given: (x : Real)
  statement: UniqueDiffWithinAt Real (Ici x) x
  proof: (uniqueDiffWithinAt_Ioi x).mono Set.Ioi_subset_Ici_self

中文:
定理 uniqueDiffWithinAt_Ici
  条件: (x : 实数)
  结论: UniqueDiffWithinAt 实数 (左闭右无界区间 x) x
  证明: (uniqueDiffWithinAt_Ioi x).mono Set.Ioi_subset_Ici_self

Depends on / 依赖: Ioi_subset_Ici_self, Set.Ioi_subset_Ici_self, uniqueDiffWithinAt_Ioi
-/
theorem uniqueDiffWithinAt_Ici (x : Real) : UniqueDiffWithinAt Real (Ici x) x :=
  (uniqueDiffWithinAt_Ioi x).mono Set.Ioi_subset_Ici_self

/--
theorem `uniqueDiffWithinAt_Iic` / 定理 `uniqueDiffWithinAt_Iic`

English:
theorem uniqueDiffWithinAt_Iic
  given: (x : Real)
  statement: UniqueDiffWithinAt Real (Iic x) x
  proof: (uniqueDiffWithinAt_Iio x).mono Set.Iio_subset_Iic_self

中文:
定理 uniqueDiffWithinAt_Iic
  条件: (x : 实数)
  结论: UniqueDiffWithinAt 实数 (左无界右闭区间 x) x
  证明: (uniqueDiffWithinAt_Iio x).mono Set.Iio_subset_Iic_self

Depends on / 依赖: Iio_subset_Iic_self, Set.Iio_subset_Iic_self, uniqueDiffWithinAt_Iio
-/
theorem uniqueDiffWithinAt_Iic (x : Real) : UniqueDiffWithinAt Real (Iic x) x :=
  (uniqueDiffWithinAt_Iio x).mono Set.Iio_subset_Iic_self

end Real
