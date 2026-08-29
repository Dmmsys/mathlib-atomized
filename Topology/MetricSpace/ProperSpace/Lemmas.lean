/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Proper spaces

This file contains some more involved results about `ProperSpace`s.

## Main definitions and results

* `exists_pos_lt_subset_ball`
* `exists_lt_subset_ball`
* `Metric.exists_isLocalMin_mem_ball`
-/

public section

open Set Metric

variable {α : Type*} {β : Type*} [PseudoMetricSpace α] [ProperSpace α] {x : α} {r : Real} {s : Set α}

/--
theorem `exists_pos_lt_subset_ball` / 定理 `exists_pos_lt_subset_ball`

English:
theorem exists_pos_lt_subset_ball
  given: (hr : 0 < r) (hs : IsClosed s) (h : s subseteq ball x r)
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨r / 2, ⟨half_pos hr, half_lt_self hr⟩, empty_subset _⟩
  have : IsCompact s :=
    (isCompact_closedBall x r).of_isClosed_subset hs (h.trans ball_subset_closedBall)
  obtain ⟨y, hys, hy⟩ : exists y in s, s subseteq closedBall x (dist y x

中文:
定理 存在_pos_lt_subset_ball
  条件: (hr : 0 < r) (hs : 是闭集 s) (h : s subseteq ball x r)
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨r / 2, ⟨half_pos hr, half_lt_self hr⟩, empty_subset _⟩
  have : IsCompact s :=
    (isCompact_closedBall x r).of_isClosed_subset hs (h.trans ball_subset_closedBall)
  obtain ⟨y, hys, hy⟩ : exists y in s, s subseteq closedBall x (dist y x

Depends on / 依赖: IsCompact, ball_subset_closedBall, closedBall, closedBall_s, dist_nonneg, dist_nonneg.trans_lt, empty_subset, eq_empty_or_nonempty, exists_between, exists_isMaxOn, fun_prop, h.trans, half_lt_self, half_pos, hy.trans, isCompact_closedBall, of_isClosed_subset, subseteq, this.exists_isMaxOn, trans_lt
-/
theorem exists_pos_lt_subset_ball (hr : 0 < r) (hs : IsClosed s) (h : s subseteq ball x r) :
    exists r' in Ioo 0 r, s subseteq ball x r' := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨r / 2, ⟨half_pos hr, half_lt_self hr⟩, empty_subset _⟩
  have : IsCompact s :=
    (isCompact_closedBall x r).of_isClosed_subset hs (h.trans ball_subset_closedBall)
  obtain ⟨y, hys, hy⟩ : exists y in s, s subseteq closedBall x (dist y x) :=
    this.exists_isMaxOn (β := α) (α := Real) hne (by fun_prop)
  have hyr : dist y x < r := h hys
  rcases exists_between hyr with ⟨r', hyr', hrr'⟩
exact ⟨r', ⟨dist_nonneg.trans_lt hyr', hrr'⟩, hy.trans closedBall_subset_ball hyr'⟩

/--
theorem `exists_lt_subset_ball` / 定理 `exists_lt_subset_ball`

English:
theorem exists_lt_subset_ball
  given: (hs : IsClosed s) (h : s subseteq ball x r)
  statement: exists r' < r, s subseteq ball x r'
  proof: by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, subset_empty_iff] at h
    subst s
    exact (exists_lt r).imp fun r' hr' => ⟨hr', empty_subset _⟩
  · exact (exists_pos_lt_subset_ball hr hs h).imp fun r' hr' => ⟨hr'.1.2, hr'.2⟩

中文:
定理 存在_lt_subset_ball
  条件: (hs : 是闭集 s) (h : s subseteq ball x r)
  结论: 存在 r' < r, s subseteq ball x r'
  证明: by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, subset_empty_iff] at h
    subst s
    exact (exists_lt r).imp fun r' hr' => ⟨hr', empty_subset _⟩
  · exact (exists_pos_lt_subset_ball hr hs h).imp fun r' hr' => ⟨hr'.1.2, hr'.2⟩

Depends on / 依赖: ball_eq_empty, empty_subset, exists_lt, exists_pos_lt_subset_ball, le_or_gt, subset_empty_iff
-/
theorem exists_lt_subset_ball (hs : IsClosed s) (h : s subseteq ball x r) : exists r' < r, s subseteq ball x r' := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, subset_empty_iff] at h
    subst s
    exact (exists_lt r).imp fun r' hr' => ⟨hr', empty_subset _⟩
  · exact (exists_pos_lt_subset_ball hr hs h).imp fun r' hr' => ⟨hr'.1.2, hr'.2⟩

/--
theorem `Metric.exists_isLocalMin_mem_ball` / 定理 `Metric.exists_isLocalMin_mem_ball`

English:
theorem Metric.exists_isLocalMin_mem_ball
  statement: [TopologicalSpace β]
  proof: by
  simp_rw [← closedBall_sdiff_ball] at hf1
  exact (isCompact_closedBall a r).exists_isLocalMin_mem_open ball_subset_closedBall hf hz hf1
    isOpen_ball

@[fun_prop]

中文:
定理 Metric.存在_isLocalMin_mem_ball
  结论: [拓扑空间 β]
  证明: by
  simp_rw [← closedBall_sdiff_ball] at hf1
  exact (isCompact_closedBall a r).exists_isLocalMin_mem_open ball_subset_closedBall hf hz hf1
    isOpen_ball

@[fun_prop]

Depends on / 依赖: ball_subset_closedBall, closedBall_sdiff_ball, exists_isLocalMin_mem_open, isCompact_closedBall, isOpen_ball, simp_rw
-/
theorem Metric.exists_isLocalMin_mem_ball [TopologicalSpace β]
    [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α -> β} {a z : α} {r : Real}
    (hf : ContinuousOn f (closedBall a r)) (hz : z in closedBall a r)
    (hf1 : forall z' in sphere a r, f z < f z') : exists z in ball a r, IsLocalMin f z := by
  simp_rw [← closedBall_sdiff_ball] at hf1
  exact (isCompact_closedBall a r).exists_isLocalMin_mem_open ball_subset_closedBall hf hz hf1
    isOpen_ball

@[fun_prop]
/--
lemma `isProperMap_dist` / 引理 `isProperMap_dist`

English:
lemma isProperMap_dist
  given: (x : α)
  statement: IsProperMap (dist x)
  proof: isProperMap_iff_tendsto_cocompact.mpr
    ⟨by fun_prop, (tendsto_dist_left_cocompact_atTop x).trans atTop_le_cocompact⟩

omit [ProperSpace α] in

中文:
引理 isProperMap_dist
  条件: (x : α)
  结论: 是真映射 (dist x)
  证明: isProperMap_iff_tendsto_cocompact.mpr
    ⟨by fun_prop, (tendsto_dist_left_cocompact_atTop x).trans atTop_le_cocompact⟩

omit [ProperSpace α] in

Depends on / 依赖: atTop_le_cocompact, fun_prop, isProperMap_iff_tendsto_cocompact, isProperMap_iff_tendsto_cocompact.mpr, tendsto_dist_left_cocompact_atTop
-/
lemma isProperMap_dist (x : α) : IsProperMap (dist x) :=
  isProperMap_iff_tendsto_cocompact.mpr
    ⟨by fun_prop, (tendsto_dist_left_cocompact_atTop x).trans atTop_le_cocompact⟩

omit [ProperSpace α] in
/--
lemma `properSpace_iff_isProperMap_dist` / 引理 `properSpace_iff_isProperMap_dist`

English:
lemma properSpace_iff_isProperMap_dist
  statement: ProperSpace α ↔ forall x : α, IsProperMap (dist x)
  proof: by
  refine ⟨fun _ => isProperMap_dist, fun H => ⟨fun x r => ?_⟩⟩
  convert! (H x).isCompact_preimage (isCompact_closedBall 0 r)
  ext
  simp [dist_comm, Real.dist_eq]

中文:
引理 properSpace_iff_isProperMap_dist
  结论: 真空间 α ↔ 对任意 x : α, 是真映射 (dist x)
  证明: by
  refine ⟨fun _ => isProperMap_dist, fun H => ⟨fun x r => ?_⟩⟩
  convert! (H x).isCompact_preimage (isCompact_closedBall 0 r)
  ext
  simp [dist_comm, Real.dist_eq]

Depends on / 依赖: Real.dist_eq, convert, dist_comm, dist_eq, isCompact_closedBall, isCompact_preimage, isProperMap_dist
-/
lemma properSpace_iff_isProperMap_dist : ProperSpace α ↔ forall x : α, IsProperMap (dist x) := by
  refine ⟨fun _ => isProperMap_dist, fun H => ⟨fun x r => ?_⟩⟩
  convert! (H x).isCompact_preimage (isCompact_closedBall 0 r)
  ext
  simp [dist_comm, Real.dist_eq]

/--
lemma `isClosedMap_dist` / 引理 `isClosedMap_dist`

English:
lemma isClosedMap_dist
  given: (x : α)
  statement: IsClosedMap (dist x)
  proof: (isProperMap_dist x).isClosedMap

中文:
引理 isClosedMap_dist
  条件: (x : α)
  结论: 是闭映射 (dist x)
  证明: (isProperMap_dist x).isClosedMap

Depends on / 依赖: isClosedMap, isProperMap_dist
-/
lemma isClosedMap_dist (x : α) : IsClosedMap (dist x) := (isProperMap_dist x).isClosedMap

/--
lemma `isProperMap_nndist` / 引理 `isProperMap_nndist`

English:
lemma isProperMap_nndist
  given: (x : α)
  statement: IsProperMap (nndist x)
  proof: isProperMap_of_comp_of_inj (Z := Real) (g := (↑)) (by fun_prop) (by fun_prop)
    (isProperMap_dist x) NNReal.coe_injective

中文:
引理 isProperMap_nndist
  条件: (x : α)
  结论: 是真映射 (nndist x)
  证明: isProperMap_of_comp_of_inj (Z := Real) (g := (↑)) (by fun_prop) (by fun_prop)
    (isProperMap_dist x) NNReal.coe_injective

Depends on / 依赖: NNReal, NNReal.coe_injective, coe_injective, fun_prop, isProperMap_dist, isProperMap_of_comp_of_inj
-/
lemma isProperMap_nndist (x : α) : IsProperMap (nndist x) :=
  isProperMap_of_comp_of_inj (Z := Real) (g := (↑)) (by fun_prop) (by fun_prop)
    (isProperMap_dist x) NNReal.coe_injective

/--
lemma `isClosedMap_nndist` / 引理 `isClosedMap_nndist`

English:
lemma isClosedMap_nndist
  given: (x : α)
  statement: IsClosedMap (nndist x)
  proof: (isProperMap_nndist _).isClosedMap

中文:
引理 isClosedMap_nndist
  条件: (x : α)
  结论: 是闭映射 (nndist x)
  证明: (isProperMap_nndist _).isClosedMap

Depends on / 依赖: isClosedMap, isProperMap_nndist
-/
lemma isClosedMap_nndist (x : α) : IsClosedMap (nndist x) := (isProperMap_nndist _).isClosedMap
