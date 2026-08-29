/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.Equicontinuity
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Topology induced by a family of seminorms

## Main definitions

* `SeminormFamily.basisSets`: The set of open seminorm balls for a family of seminorms.
* `SeminormFamily.moduleFilterBasis`: A module filter basis formed by the open balls.
* `Seminorm.IsBounded`: A linear map `f : E →ₗ[𝕜] F` is bounded iff every seminorm in `F` can be
  bounded by a finite number of seminorms in `E`.
* `WithSeminorms p`, when `p` is a family of seminorms on `E`, is a proposition expressing that the
  (existing) topology on `E` is induced by the seminorms `p`.
* `PolynormableSpace 𝕜 E` is a class asserting that the (existing) topology on `E` is induced
  by *some* family of `𝕜`-seminorms. If `𝕜` is `RCLike`, this is equivalent to
  `LocallyConvexSpace 𝕜 E`.
  The terminology is inspired by N. Bourbaki, *Variétés différentielles et analytiques*. However,
  unlike Bourbaki, we do not ask seminorms to be ultrametric when `𝕜` is ultrametric.

## Main statements

* `WithSeminorms.toLocallyConvexSpace`: A space equipped with a family of seminorms is locally
  convex.
* `WithSeminorms.firstCountable`: A space is first countable if its topology is induced by a
  countable family of seminorms.

## Continuity of semilinear maps

If `E` and `F` are topological vector space with the topology induced by a family of seminorms, then
we have a direct method to prove that a linear map is continuous:
* `Seminorm.continuous_from_bounded`: A bounded linear map `f : E →ₗ[𝕜] F` is continuous.

If the topology of a space `E` is induced by a family of seminorms, then we can characterize von
Neumann boundedness in terms of that seminorm family. Together with
`LinearMap.continuous_of_locally_bounded` this gives general criterion for continuity.

* `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.isVonNBounded_iff_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_seminorm_bounded`

## Tags

seminorm, locally convex
-/

@[expose] public section


open NormedField Set Seminorm TopologicalSpace Filter List Bornology

open NNReal Pointwise Topology Uniformity

variable {R 𝕜 𝕜₂ 𝕝 𝕝₂ E F G ι ι' : Type*}

section FilterBasis

variable [SeminormedRing R] [AddCommGroup E] [Module R E]
variable (R E ι)

/--
Definition of `SeminormFamily` / `SeminormFamily` 的定义

English:
abbreviation SeminormFamily
  body: ι -> Seminorm R E

中文:
缩写 SeminormFamily
  定义体: ι -> Seminorm R E

Depends on / 依赖: Seminorm
-/
abbrev SeminormFamily :=
  ι -> Seminorm R E

variable {R E ι}

namespace SeminormFamily

/--
Definition of `basisSets` / `basisSets` 的定义

English:
definition basisSets
  signature: (p : SeminormFamily R E ι)
  body: ⋃ (s : Finset ι) (r) (_ : 0 < r), singleton (ball (s.sup p) (0 : E) r)

中文:
定义 basisSets
  签名: (p : SeminormFamily R E ι)
  定义体: ⋃ (s : Finset ι) (r) (_ : 0 < r), singleton (ball (s.sup p) (0 : E) r)

Depends on / 依赖: Finset, s.sup, singleton
-/
def basisSets (p : SeminormFamily R E ι) : Set (Set E) :=
  ⋃ (s : Finset ι) (r) (_ : 0 < r), singleton (ball (s.sup p) (0 : E) r)

variable (p : SeminormFamily R E ι)

/--
theorem `basisSets_iff` / 定理 `basisSets_iff`

English:
theorem basisSets_iff
  given: {U : Set E}
  proof: by
  simp only [basisSets, mem_iUnion, exists_prop, mem_singleton_iff]

中文:
定理 basisSets_iff
  条件: {U : 集合 E}
  证明: by
  simp only [basisSets, mem_iUnion, exists_prop, mem_singleton_iff]

Depends on / 依赖: basisSets, exists_prop, mem_iUnion, mem_singleton_iff
-/
theorem basisSets_iff {U : Set E} :
    U in p.basisSets ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r := by
  simp only [basisSets, mem_iUnion, exists_prop, mem_singleton_iff]

/--
theorem `basisSets_mem` / 定理 `basisSets_mem`

English:
theorem basisSets_mem
  given: (i : Finset ι) {r : Real} (hr : 0 < r)
  statement: (i.sup p).ball 0 r in p.basisSets
  proof: (basisSets_iff _).mpr ⟨i, _, hr, rfl⟩

中文:
定理 basisSets_mem
  条件: (i : 有限集 ι) {r : 实数} (hr : 0 < r)
  结论: (i.上确界 p).ball 0 r in p.basisSets
  证明: (basisSets_iff _).mpr ⟨i, _, hr, rfl⟩

Depends on / 依赖: basisSets_iff
-/
theorem basisSets_mem (i : Finset ι) {r : Real} (hr : 0 < r) : (i.sup p).ball 0 r in p.basisSets :=
  (basisSets_iff _).mpr ⟨i, _, hr, rfl⟩

/--
theorem `basisSets_singleton_mem` / 定理 `basisSets_singleton_mem`

English:
theorem basisSets_singleton_mem
  given: (i : ι) {r : Real} (hr : 0 < r)
  statement: (p i).ball 0 r in p.basisSets
  proof: (basisSets_iff _).mpr ⟨{i}, _, hr, by rw [Finset.sup_singleton]⟩

中文:
定理 basisSets_singleton_mem
  条件: (i : ι) {r : 实数} (hr : 0 < r)
  结论: (p i).ball 0 r in p.basisSets
  证明: (basisSets_iff _).mpr ⟨{i}, _, hr, by rw [Finset.sup_singleton]⟩

Depends on / 依赖: Finset, Finset.sup_singleton, basisSets_iff, sup_singleton
-/
theorem basisSets_singleton_mem (i : ι) {r : Real} (hr : 0 < r) : (p i).ball 0 r in p.basisSets :=
  (basisSets_iff _).mpr ⟨{i}, _, hr, by rw [Finset.sup_singleton]⟩

/--
theorem `basisSets_univ_mem` / 定理 `basisSets_univ_mem`

English:
theorem basisSets_univ_mem
  statement: univ in p.basisSets
  proof: (basisSets_iff _).mpr ⟨∅, _, one_pos, by
    rw [Finset.sup_empty]; rw [Seminorm.bot_eq_zero]; rw [ball_zero' _ one_pos]⟩

中文:
定理 basisSets_univ_mem
  结论: univ in p.basisSets
  证明: (basisSets_iff _).mpr ⟨∅, _, one_pos, by
    rw [Finset.sup_empty]; rw [Seminorm.bot_eq_zero]; rw [ball_zero' _ one_pos]⟩

Depends on / 依赖: Finset, Finset.sup_empty, Seminorm, Seminorm.bot_eq_zero, ball_zero, basisSets_iff, bot_eq_zero, one_pos, sup_empty
-/
theorem basisSets_univ_mem : univ in p.basisSets :=
  (basisSets_iff _).mpr ⟨∅, _, one_pos, by
    rw [Finset.sup_empty]; rw [Seminorm.bot_eq_zero]; rw [ball_zero' _ one_pos]⟩

/--
theorem `basisSets_nonempty` / 定理 `basisSets_nonempty`

English:
theorem basisSets_nonempty
  statement: p.basisSets.Nonempty
  proof: by
  refine nonempty_def.mpr ⟨univ, basisSets_univ_mem _⟩

中文:
定理 basisSets_nonempty
  结论: p.basisSets.非空
  证明: by
  refine nonempty_def.mpr ⟨univ, basisSets_univ_mem _⟩

Depends on / 依赖: basisSets_univ_mem, nonempty_def, nonempty_def.mpr
-/
theorem basisSets_nonempty : p.basisSets.Nonempty := by
  refine nonempty_def.mpr ⟨univ, basisSets_univ_mem _⟩

/--
theorem `basisSets_intersect` / 定理 `basisSets_intersect`

English:
theorem basisSets_intersect
  given: (U V : Set E) (hU : U in p.basisSets) (hV : V in p.basisSets)
  proof: by
  classical
    rcases p.basisSets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩
    rcases p.basisSets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩
    use ((s union t).sup p).ball 0 (min r₁ r₂)
    refine ⟨p.basisSets_mem (s union t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), ?_⟩
    rw [hU]; rw [hV]; rw [ball_finset_sup_eq_iInter _ _ _ (lt_min_iff.mpr ⟨hr₁]; rw [hr₂⟩)]; rw [ball_finset_sup_eq_iInter _ _ _ hr₁]; rw [ball_finset_sup_eq_iInter _ _ _ hr₂]
    exact
      Set.subset_inter
        (Set.iInter₂_mono' fun i hi =>
⟨i, Finset.subset_union_left hi, ball_mono min_le_left _ _⟩)
        (Set.iInter₂_mono' fun i hi =>
⟨i, Finset.subset_union_right hi, ball_mono min_le_right _ _⟩)

中文:
定理 basisSets_intersect
  条件: (U V : 集合 E) (hU : U in p.basisSets) (hV : V in p.basisSets)
  证明: by
  classical
    rcases p.basisSets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩
    rcases p.basisSets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩
    use ((s union t).sup p).ball 0 (min r₁ r₂)
    refine ⟨p.basisSets_mem (s union t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), ?_⟩
    rw [hU]; rw [hV]; rw [ball_finset_sup_eq_iInter _ _ _ (lt_min_iff.mpr ⟨hr₁]; rw [hr₂⟩)]; rw [ball_finset_sup_eq_iInter _ _ _ hr₁]; rw [ball_finset_sup_eq_iInter _ _ _ hr₂]
    exact
      Set.subset_inter
        (Set.iInter₂_mono' fun i hi =>
⟨i, Finset.subset_union_left hi, ball_mono min_le_left _ _⟩)
        (Set.iInter₂_mono' fun i hi =>
⟨i, Finset.subset_union_right hi, ball_mono min_le_right _ _⟩)

Depends on / 依赖: Finset, Finset.subset_union_left, Set.iInter, Set.subset_inter, ball_finset_sup_eq_iInter, ball_mono, basisSets_iff, basisSets_mem, classical, lt_min_iff, lt_min_iff.mpr, min_, p.basisSets_iff.mp, p.basisSets_mem, subset_inter, subset_union_left
-/
theorem basisSets_intersect (U V : Set E) (hU : U in p.basisSets) (hV : V in p.basisSets) :
    exists z in p.basisSets, z subseteq U inter V := by
  classical
    rcases p.basisSets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩
    rcases p.basisSets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩
    use ((s union t).sup p).ball 0 (min r₁ r₂)
    refine ⟨p.basisSets_mem (s union t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), ?_⟩
    rw [hU]; rw [hV]; rw [ball_finset_sup_eq_iInter _ _ _ (lt_min_iff.mpr ⟨hr₁]; rw [hr₂⟩)]; rw [ball_finset_sup_eq_iInter _ _ _ hr₁]; rw [ball_finset_sup_eq_iInter _ _ _ hr₂]
    exact
      Set.subset_inter
        (Set.iInter₂_mono' fun i hi =>
⟨i, Finset.subset_union_left hi, ball_mono min_le_left _ _⟩)
        (Set.iInter₂_mono' fun i hi =>
⟨i, Finset.subset_union_right hi, ball_mono min_le_right _ _⟩)

/--
theorem `basisSets_zero` / 定理 `basisSets_zero`

English:
theorem basisSets_zero
  given: (U) (hU : U in p.basisSets)
  statement: (0 : E) in U
  proof: by
  rcases p.basisSets_iff.mp hU with ⟨ι', r, hr, hU⟩
  rw [hU]; rw [mem_ball_zero]; rw [map_zero]
  exact hr

中文:
定理 basisSets_zero
  条件: (U) (hU : U in p.basisSets)
  结论: (0 : E) in U
  证明: by
  rcases p.basisSets_iff.mp hU with ⟨ι', r, hr, hU⟩
  rw [hU]; rw [mem_ball_zero]; rw [map_zero]
  exact hr

Depends on / 依赖: basisSets_iff, map_zero, mem_ball_zero, p.basisSets_iff.mp
-/
theorem basisSets_zero (U) (hU : U in p.basisSets) : (0 : E) in U := by
  rcases p.basisSets_iff.mp hU with ⟨ι', r, hr, hU⟩
  rw [hU]; rw [mem_ball_zero]; rw [map_zero]
  exact hr

/--
theorem `basisSets_add` / 定理 `basisSets_add`

English:
theorem basisSets_add
  given: (U) (hU : U in p.basisSets)
  proof: by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  use (s.sup p).ball 0 (r / 2)
  refine ⟨p.basisSets_mem s (div_pos hr zero_lt_two), ?_⟩
  refine Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) ?_
  rw [hU]; rw [add_zero]; rw [add_halves]

中文:
定理 basisSets_add
  条件: (U) (hU : U in p.basisSets)
  证明: by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  use (s.sup p).ball 0 (r / 2)
  refine ⟨p.basisSets_mem s (div_pos hr zero_lt_two), ?_⟩
  refine Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) ?_
  rw [hU]; rw [add_zero]; rw [add_halves]

Depends on / 依赖: Set.Subset.trans, Subset, add_halves, add_zero, ball_add_ball_subset, basisSets_iff, basisSets_mem, div_pos, p.basisSets_iff.mp, p.basisSets_mem, s.sup, zero_lt_two
-/
theorem basisSets_add (U) (hU : U in p.basisSets) :
    exists V in p.basisSets, V + V subseteq U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  use (s.sup p).ball 0 (r / 2)
  refine ⟨p.basisSets_mem s (div_pos hr zero_lt_two), ?_⟩
  refine Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) ?_
  rw [hU]; rw [add_zero]; rw [add_halves]

/--
theorem `basisSets_neg` / 定理 `basisSets_neg`

English:
theorem basisSets_neg
  given: (U) (hU' : U in p.basisSets)
  proof: by
  rcases p.basisSets_iff.mp hU' with ⟨s, r, _, hU⟩
  rw [hU]; rw [neg_preimage]; rw [neg_ball (s.sup p)]; rw [neg_zero]
  exact ⟨U, hU', Eq.subset hU⟩

中文:
定理 basisSets_neg
  条件: (U) (hU' : U in p.basisSets)
  证明: by
  rcases p.basisSets_iff.mp hU' with ⟨s, r, _, hU⟩
  rw [hU]; rw [neg_preimage]; rw [neg_ball (s.sup p)]; rw [neg_zero]
  exact ⟨U, hU', Eq.subset hU⟩

Depends on / 依赖: Eq.subset, basisSets_iff, neg_ball, neg_preimage, neg_zero, p.basisSets_iff.mp, s.sup, subset
-/
theorem basisSets_neg (U) (hU' : U in p.basisSets) :
    exists V in p.basisSets, V subseteq (fun x : E => -x) ⁻¹' U := by
  rcases p.basisSets_iff.mp hU' with ⟨s, r, _, hU⟩
  rw [hU]; rw [neg_preimage]; rw [neg_ball (s.sup p)]; rw [neg_zero]
  exact ⟨U, hU', Eq.subset hU⟩

/-- The `addGroupFilterBasis` induced by the filter basis `Seminorm.basisSets`. -/
@[instance_reducible]
/--
Definition of `addGroupFilterBasis` / `addGroupFilterBasis` 的定义

English:
definition addGroupFilterBasis
  signature: : AddGroupFilterBasis E
  body: addGroupFilterBasisOfComm p.basisSets p.basisSets_nonempty p.basisSets_intersect p.basisSets_zero
    p.basisSets_add p.basisSets_neg

中文:
定义 addGroupFilterBasis
  签名: : 加法群滤子基 E
  定义体: addGroupFilterBasisOfComm p.basisSets p.basisSets_nonempty p.basisSets_intersect p.basisSets_zero
    p.basisSets_add p.basisSets_neg
-/
protected def addGroupFilterBasis : AddGroupFilterBasis E :=
  addGroupFilterBasisOfComm p.basisSets p.basisSets_nonempty p.basisSets_intersect p.basisSets_zero
    p.basisSets_add p.basisSets_neg

/--
theorem `basisSets_smul_right` / 定理 `basisSets_smul_right`

English:
theorem basisSets_smul_right
  given: (v : E) (U : Set E) (hU : U in p.basisSets)
  proof: by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]; rw [Filter.eventually_iff]
  simp_rw [(s.sup p).mem_ball_zero, map_smul_eq_mul]
  by_cases! h : 0 < (s.sup p) v
  · simp_rw [(lt_div_iff₀ h).symm]
    rw [← _root_.ball_zero_eq]
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
  simp_rw [le_antisymm h (apply_nonneg _ v), mul_zero, hr]
  exact IsOpen.mem_nhds isOpen_univ (mem_univ 0)

中文:
定理 basisSets_smul_right
  条件: (v : E) (U : 集合 E) (hU : U in p.basisSets)
  证明: by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]; rw [Filter.eventually_iff]
  simp_rw [(s.sup p).mem_ball_zero, map_smul_eq_mul]
  by_cases! h : 0 < (s.sup p) v
  · simp_rw [(lt_div_iff₀ h).symm]
    rw [← _root_.ball_zero_eq]
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
  simp_rw [le_antisymm h (apply_nonneg _ v), mul_zero, hr]
  exact IsOpen.mem_nhds isOpen_univ (mem_univ 0)

Depends on / 依赖: Filter, Filter.eventually_iff, IsOpen, IsOpen.mem_nhds, Metric, Metric.ball_mem_nhds, _root_, _root_.ball_zero_eq, apply_nonneg, ball_mem_nhds, ball_zero_eq, basisSets_iff, div_pos, eventually_iff, isOpen_univ, le_antisymm, map_smul_eq_mul, mem_ball_zero, mem_nhds, mem_univ
-/
theorem basisSets_smul_right (v : E) (U : Set E) (hU : U in p.basisSets) :
    forallᶠ x : R in 𝓝 0, x • v in U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]; rw [Filter.eventually_iff]
  simp_rw [(s.sup p).mem_ball_zero, map_smul_eq_mul]
  by_cases! h : 0 < (s.sup p) v
  · simp_rw [(lt_div_iff₀ h).symm]
    rw [← _root_.ball_zero_eq]
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
  simp_rw [le_antisymm h (apply_nonneg _ v), mul_zero, hr]
  exact IsOpen.mem_nhds isOpen_univ (mem_univ 0)

/--
theorem `basisSets_smul` / 定理 `basisSets_smul`

English:
theorem basisSets_smul
  given: (U) (hU : U in p.basisSets)
  proof: by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  refine ⟨Metric.ball 0 √r, Metric.ball_mem_nhds 0 (Real.sqrt_pos.mpr hr), ?_⟩
  refine ⟨(s.sup p).ball 0 √r, p.basisSets_mem s (Real.sqrt_pos.mpr hr), ?_⟩
  refine Set.Subset.trans (ball_smul_ball (s.sup p) √r √r) ?_
  rw [hU]; rw [Real.mul_self_sqrt (le_of_lt hr)]

中文:
定理 basisSets_smul
  条件: (U) (hU : U in p.basisSets)
  证明: by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  refine ⟨Metric.ball 0 √r, Metric.ball_mem_nhds 0 (Real.sqrt_pos.mpr hr), ?_⟩
  refine ⟨(s.sup p).ball 0 √r, p.basisSets_mem s (Real.sqrt_pos.mpr hr), ?_⟩
  refine Set.Subset.trans (ball_smul_ball (s.sup p) √r √r) ?_
  rw [hU]; rw [Real.mul_self_sqrt (le_of_lt hr)]

Depends on / 依赖: Metric, Metric.ball, Metric.ball_mem_nhds, Real.mul_self_sqrt, Real.sqrt_pos.mpr, Set.Subset.trans, Subset, ball_mem_nhds, ball_smul_ball, basisSets_iff, basisSets_mem, le_of_lt, mul_self_sqrt, p.basisSets_iff.mp, p.basisSets_mem, s.sup, sqrt_pos
-/
theorem basisSets_smul (U) (hU : U in p.basisSets) :
    exists V in 𝓝 (0 : R), exists W in p.addGroupFilterBasis.sets, V • W subseteq U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  refine ⟨Metric.ball 0 √r, Metric.ball_mem_nhds 0 (Real.sqrt_pos.mpr hr), ?_⟩
  refine ⟨(s.sup p).ball 0 √r, p.basisSets_mem s (Real.sqrt_pos.mpr hr), ?_⟩
  refine Set.Subset.trans (ball_smul_ball (s.sup p) √r √r) ?_
  rw [hU]; rw [Real.mul_self_sqrt (le_of_lt hr)]

variable [NormedDivisionRing 𝕜] [AddCommGroup F] [Module 𝕜 F] (p : SeminormFamily 𝕜 F ι)

/--
theorem `basisSets_smul_left` / 定理 `basisSets_smul_left`

English:
theorem basisSets_smul_left
  given: (x : 𝕜) (U : Set F) (hU : U in p.basisSets)
  proof: by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]
  by_cases h : x != 0
  · rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    use (s.sup p).ball 0 (r / ‖x‖)
    exact ⟨p.basisSets_mem s (div_pos hr (norm_pos_iff.mpr h)), Subset.rfl⟩
  refine ⟨(s.sup p).ball 0 r, p.basisSets_mem s hr, ?_⟩
  simp only [not_ne_iff.mp h, Set.subset_def, mem_ball_zero, hr, mem_univ, map_zero, imp_true_iff,
    preimage_const_of_mem, zero_smul]

中文:
定理 basisSets_smul_left
  条件: (x : 𝕜) (U : 集合 F) (hU : U in p.basisSets)
  证明: by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]
  by_cases h : x != 0
  · rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    use (s.sup p).ball 0 (r / ‖x‖)
    exact ⟨p.basisSets_mem s (div_pos hr (norm_pos_iff.mpr h)), Subset.rfl⟩
  refine ⟨(s.sup p).ball 0 r, p.basisSets_mem s hr, ?_⟩
  simp only [not_ne_iff.mp h, Set.subset_def, mem_ball_zero, hr, mem_univ, map_zero, imp_true_iff,
    preimage_const_of_mem, zero_smul]

Depends on / 依赖: Set.subset_def, Subset, Subset.rfl, basisSets_iff, basisSets_mem, div_pos, imp_true_iff, map_zero, mem_ball_zero, mem_univ, norm_pos_iff, norm_pos_iff.mpr, not_ne_iff, not_ne_iff.mp, p.basisSets_iff.mp, p.basisSets_mem, preimage_const_of_mem, s.sup, smul_ball_preimage, smul_zero
-/
theorem basisSets_smul_left (x : 𝕜) (U : Set F) (hU : U in p.basisSets) :
    exists V in p.addGroupFilterBasis.sets, V subseteq (fun y : F => x • y) ⁻¹' U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]
  by_cases h : x != 0
  · rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    use (s.sup p).ball 0 (r / ‖x‖)
    exact ⟨p.basisSets_mem s (div_pos hr (norm_pos_iff.mpr h)), Subset.rfl⟩
  refine ⟨(s.sup p).ball 0 r, p.basisSets_mem s hr, ?_⟩
  simp only [not_ne_iff.mp h, Set.subset_def, mem_ball_zero, hr, mem_univ, map_zero, imp_true_iff,
    preimage_const_of_mem, zero_smul]

/--
Definition of `moduleFilterBasis` / `moduleFilterBasis` 的定义

English:
definition moduleFilterBasis
  signature: : ModuleFilterBasis 𝕜 F where
  body: p.addGroupFilterBasis
  smul' := p.basisSets_smul _
  smul_left' := p.basisSets_smul_left
  smul_right' := p.basisSets_smul_right

中文:
定义 moduleFilterBasis
  签名: : ModuleFilterBasis 𝕜 F where
  定义体: p.addGroupFilterBasis
  smul' := p.basisSets_smul _
  smul_left' := p.basisSets_smul_left
  smul_right' := p.basisSets_smul_right
-/
protected def moduleFilterBasis : ModuleFilterBasis 𝕜 F where
  toAddGroupFilterBasis := p.addGroupFilterBasis
  smul' := p.basisSets_smul _
  smul_left' := p.basisSets_smul_left
  smul_right' := p.basisSets_smul_right

/--
theorem `filter_eq_iInf` / 定理 `filter_eq_iInf`

English:
theorem filter_eq_iInf
  given: (p : SeminormFamily 𝕜 F ι)
  proof: by
  refine le_antisymm (le_iInf fun i => ?_) ?_
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.le_basis_iff
        (Metric.nhds_basis_ball.comap _)]
    intro ε hε
    refine ⟨(p i).ball 0 ε, ?_, ?_⟩
    · rw [← (Finset.sup_singleton : _ = p i)]
      exact p.basisSets_mem {i} hε
    · rw [id, (p i).ball_zero_eq_preimage_ball]
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.ge_iff]
    rintro U (hU : U in p.basisSets)
    rcases p.basisSets_iff.mp hU with ⟨s, r, hr, rfl⟩
    rw [id]; rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]; rw [s.iInter_mem_sets]
    exact fun i _ =>
      Filter.mem_iInf_of_mem i
        ⟨Metric.ball 0 r, Metric.ball_mem_nhds 0 hr,
          Eq.subset (p i).ball_zero_eq_preimage_ball.symm⟩

中文:
定理 filter_eq_iInf
  条件: (p : SeminormFamily 𝕜 F ι)
  证明: by
  refine le_antisymm (le_iInf fun i => ?_) ?_
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.le_basis_iff
        (Metric.nhds_basis_ball.comap _)]
    intro ε hε
    refine ⟨(p i).ball 0 ε, ?_, ?_⟩
    · rw [← (Finset.sup_singleton : _ = p i)]
      exact p.basisSets_mem {i} hε
    · rw [id, (p i).ball_zero_eq_preimage_ball]
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.ge_iff]
    rintro U (hU : U in p.basisSets)
    rcases p.basisSets_iff.mp hU with ⟨s, r, hr, rfl⟩
    rw [id]; rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]; rw [s.iInter_mem_sets]
    exact fun i _ =>
      Filter.mem_iInf_of_mem i
        ⟨Metric.ball 0 r, Metric.ball_mem_nhds 0 hr,
          Eq.subset (p i).ball_zero_eq_preimage_ball.symm⟩

Depends on / 依赖: Finset, Finset.sup_singleton, Metric, Metric.nhds_basis_ball.comap, Seminorm, Seminorm.ball_finset_sup_eq_iInter, ball_finset_sup_eq_iInter, ball_zero_eq_preimage_ball, basisSets, basisSets_iff, basisSets_mem, ge_iff, hasBasis, le_antisymm, le_basis_iff, le_iInf, moduleFilterBasis, nhds_basis_ball, p.basisSets, p.basisSets_iff.mp
-/
theorem filter_eq_iInf (p : SeminormFamily 𝕜 F ι) :
    p.moduleFilterBasis.toFilterBasis.filter = ⨅ i, (𝓝 0).comap (p i) := by
  refine le_antisymm (le_iInf fun i => ?_) ?_
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.le_basis_iff
        (Metric.nhds_basis_ball.comap _)]
    intro ε hε
    refine ⟨(p i).ball 0 ε, ?_, ?_⟩
    · rw [← (Finset.sup_singleton : _ = p i)]
      exact p.basisSets_mem {i} hε
    · rw [id, (p i).ball_zero_eq_preimage_ball]
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.ge_iff]
    rintro U (hU : U in p.basisSets)
    rcases p.basisSets_iff.mp hU with ⟨s, r, hr, rfl⟩
    rw [id]; rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]; rw [s.iInter_mem_sets]
    exact fun i _ =>
      Filter.mem_iInf_of_mem i
        ⟨Metric.ball 0 r, Metric.ball_mem_nhds 0 hr,
          Eq.subset (p i).ball_zero_eq_preimage_ball.symm⟩

/--
lemma `basisSets_mem_nhds` / 引理 `basisSets_mem_nhds`

English:
lemma basisSets_mem_nhds
  statement: {𝕜 E ι : Type*} [NormedField 𝕜]
  proof: by
  obtain ⟨s, r, hr, rfl⟩ := p.basisSets_iff.mp hU
  clear hU
  refine Seminorm.ball_mem_nhds ?_ hr
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_zero
  | insert a s _ hs =>
    simp only [Finset.sup_insert, coe_sup]
    exact Continuous.max (hp a) hs

中文:
引理 basisSets_mem_nhds
  结论: {𝕜 E ι : 类型} [赋范域 𝕜]
  证明: by
  obtain ⟨s, r, hr, rfl⟩ := p.basisSets_iff.mp hU
  clear hU
  refine Seminorm.ball_mem_nhds ?_ hr
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_zero
  | insert a s _ hs =>
    simp only [Finset.sup_insert, coe_sup]
    exact Continuous.max (hp a) hs

Depends on / 依赖: Continuous, Continuous.max, Finset, Finset.induction_on, Finset.sup_insert, Seminorm, Seminorm.ball_mem_nhds, ball_mem_nhds, basisSets_iff, classical, coe_sup, continuous_zero, induction_on, insert, p.basisSets_iff.mp, sup_insert
-/
lemma basisSets_mem_nhds {𝕜 E ι : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] (p : SeminormFamily 𝕜 E ι)
    (hp : forall i, Continuous (p i)) (U : Set E) (hU : U in p.basisSets) : U in 𝓝 (0 : E) := by
  obtain ⟨s, r, hr, rfl⟩ := p.basisSets_iff.mp hU
  clear hU
  refine Seminorm.ball_mem_nhds ?_ hr
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_zero
  | insert a s _ hs =>
    simp only [Finset.sup_insert, coe_sup]
    exact Continuous.max (hp a) hs

end SeminormFamily

end FilterBasis

section Bounded

namespace Seminorm

variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [SeminormedRing 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]

/--
Definition of `IsBounded` / `IsBounded` 的定义

English:
definition IsBounded
  signature: (p : ι -> Seminorm 𝕜 E) (q : ι' -> Seminorm 𝕜₂ F) (f : E ->ₛₗ[σ₁₂] F)
  body: forall i, exists s : Finset ι, exists C : Real>=0, (q i).comp f <= C • s.sup p

中文:
定义 IsBounded
  签名: (p : ι -> 半范数 𝕜 E) (q : ι' -> 半范数 𝕜₂ F) (f : E ->ₛₗ[σ₁₂] F)
  定义体: forall i, exists s : Finset ι, exists C : Real>=0, (q i).comp f <= C • s.sup p

Depends on / 依赖: Finset, s.sup
-/
def IsBounded (p : ι -> Seminorm 𝕜 E) (q : ι' -> Seminorm 𝕜₂ F) (f : E ->ₛₗ[σ₁₂] F) : Prop :=
  forall i, exists s : Finset ι, exists C : Real>=0, (q i).comp f <= C • s.sup p

/--
theorem `IsBounded.of_real` / 定理 `IsBounded.of_real`

English:
theorem IsBounded.of_real
  statement: {p : ι -> Seminorm 𝕜 E} {q : ι' -> Seminorm 𝕜₂ F} {f : E ->ₛₗ[σ₁₂] F}
  proof: by
  rw [IsBounded]
  peel H with i s H
  obtain ⟨C, hC⟩ := H
  refine ⟨C.toNNReal, fun x => show q i (f x) <= C.toNNReal • ((s.sup p) x) from ?_⟩
exact (hC x).trans mul_le_mul_of_nonneg_right C.le_coe_toNNReal (apply_nonneg _ _)

中文:
定理 IsBounded.of_real
  结论: {p : ι -> 半范数 𝕜 E} {q : ι' -> 半范数 𝕜₂ F} {f : E ->ₛₗ[σ₁₂] F}
  证明: by
  rw [IsBounded]
  peel H with i s H
  obtain ⟨C, hC⟩ := H
  refine ⟨C.toNNReal, fun x => show q i (f x) <= C.toNNReal • ((s.sup p) x) from ?_⟩
exact (hC x).trans mul_le_mul_of_nonneg_right C.le_coe_toNNReal (apply_nonneg _ _)

Depends on / 依赖: C.le_coe_toNNReal, C.toNNReal, IsBounded, apply_nonneg, le_coe_toNNReal, mul_le_mul_of_nonneg_right, s.sup, toNNReal
-/
theorem IsBounded.of_real {p : ι -> Seminorm 𝕜 E} {q : ι' -> Seminorm 𝕜₂ F} {f : E ->ₛₗ[σ₁₂] F}
    (H : forall i, exists s : Finset ι, exists C : Real, forall x, q i (f x) <= C * (s.sup p) x) :
    IsBounded p q f := by
  rw [IsBounded]
  peel H with i s H
  obtain ⟨C, hC⟩ := H
  refine ⟨C.toNNReal, fun x => show q i (f x) <= C.toNNReal • ((s.sup p) x) from ?_⟩
exact (hC x).trans mul_le_mul_of_nonneg_right C.le_coe_toNNReal (apply_nonneg _ _)

/--
theorem `isBounded_const` / 定理 `isBounded_const`

English:
theorem isBounded_const
  statement: (ι' : Type*) [Nonempty ι'] {p : ι -> Seminorm 𝕜 E} {q : Seminorm 𝕜₂ F}
  proof: by
  simp only [IsBounded, forall_const]

中文:
定理 isBounded_const
  结论: (ι' : 类型) [非空 ι'] {p : ι -> 半范数 𝕜 E} {q : 半范数 𝕜₂ F}
  证明: by
  simp only [IsBounded, forall_const]

Depends on / 依赖: IsBounded, forall_const
-/
theorem isBounded_const (ι' : Type*) [Nonempty ι'] {p : ι -> Seminorm 𝕜 E} {q : Seminorm 𝕜₂ F}
    (f : E ->ₛₗ[σ₁₂] F) :
    IsBounded p (fun _ : ι' => q) f ↔ exists (s : Finset ι) (C : Real>=0), q.comp f <= C • s.sup p := by
  simp only [IsBounded, forall_const]

/--
theorem `const_isBounded` / 定理 `const_isBounded`

English:
theorem const_isBounded
  statement: (ι : Type*) [Nonempty ι] {p : Seminorm 𝕜 E} {q : ι' -> Seminorm 𝕜₂ F}
  proof: by
  constructor <;> intro h i
  · rcases h i with ⟨s, C, h⟩
    exact ⟨C, h.trans (IsOrderedSMul.smul_le_smul_left _ p (Finset.sup_le fun _ _ => le_rfl) C)⟩
  · use {Classical.arbitrary ι}
    simp only [h, Finset.sup_singleton]

中文:
定理 const_isBounded
  结论: (ι : 类型) [非空 ι] {p : 半范数 𝕜 E} {q : ι' -> 半范数 𝕜₂ F}
  证明: by
  constructor <;> intro h i
  · rcases h i with ⟨s, C, h⟩
    exact ⟨C, h.trans (IsOrderedSMul.smul_le_smul_left _ p (Finset.sup_le fun _ _ => le_rfl) C)⟩
  · use {Classical.arbitrary ι}
    simp only [h, Finset.sup_singleton]

Depends on / 依赖: Classical, Classical.arbitrary, Finset, Finset.sup_le, Finset.sup_singleton, IsOrderedSMul, IsOrderedSMul.smul_le_smul_left, arbitrary, h.trans, le_rfl, smul_le_smul_left, sup_le, sup_singleton
-/
theorem const_isBounded (ι : Type*) [Nonempty ι] {p : Seminorm 𝕜 E} {q : ι' -> Seminorm 𝕜₂ F}
    (f : E ->ₛₗ[σ₁₂] F) : IsBounded (fun _ : ι => p) q f ↔ forall i, exists C : Real>=0, (q i).comp f <= C • p := by
  constructor <;> intro h i
  · rcases h i with ⟨s, C, h⟩
    exact ⟨C, h.trans (IsOrderedSMul.smul_le_smul_left _ p (Finset.sup_le fun _ _ => le_rfl) C)⟩
  · use {Classical.arbitrary ι}
    simp only [h, Finset.sup_singleton]

/--
theorem `isBounded_sup` / 定理 `isBounded_sup`

English:
theorem isBounded_sup
  statement: {p : ι -> Seminorm 𝕜 E} {q : ι' -> Seminorm 𝕜₂ F} {f : E ->ₛₗ[σ₁₂] F}
  proof: by
  classical
  obtain rfl | _ := s'.eq_empty_or_nonempty
  · exact ⟨1, ∅, by simp [Seminorm.bot_eq_zero]⟩
  choose fₛ fC hf using hf
  use s'.card • s'.sup fC, Finset.biUnion s' fₛ
  have hs : forall i : ι', i in s' -> (q i).comp f <= s'.sup fC • (Finset.biUnion s' fₛ).sup p := by
    intro i hi
    refine (hf i).trans (IsOrderedSMul.smul_le_smul (Finset.le_sup hi) ?_)
    exact Finset.sup_mono (Finset.subset_biUnion_of_mem fₛ hi)
  refine (comp_mono f (finset_sup_le_sum q s')).trans ?_
  simp_rw [← pullback_apply, map_sum, pullback_apply]
  refine (Finset.sum_le_sum hs).trans ?_
  rw [Finset.sum_const]; rw [smul_assoc]

中文:
定理 isBounded_sup
  结论: {p : ι -> 半范数 𝕜 E} {q : ι' -> 半范数 𝕜₂ F} {f : E ->ₛₗ[σ₁₂] F}
  证明: by
  classical
  obtain rfl | _ := s'.eq_empty_or_nonempty
  · exact ⟨1, ∅, by simp [Seminorm.bot_eq_zero]⟩
  choose fₛ fC hf using hf
  use s'.card • s'.sup fC, Finset.biUnion s' fₛ
  have hs : forall i : ι', i in s' -> (q i).comp f <= s'.sup fC • (Finset.biUnion s' fₛ).sup p := by
    intro i hi
    refine (hf i).trans (IsOrderedSMul.smul_le_smul (Finset.le_sup hi) ?_)
    exact Finset.sup_mono (Finset.subset_biUnion_of_mem fₛ hi)
  refine (comp_mono f (finset_sup_le_sum q s')).trans ?_
  simp_rw [← pullback_apply, map_sum, pullback_apply]
  refine (Finset.sum_le_sum hs).trans ?_
  rw [Finset.sum_const]; rw [smul_assoc]

Depends on / 依赖: Finset, Finset.biUnion, Finset.le_sup, Finset.subset_biUnion_of_mem, Finset.sup_mono, IsOrderedSMul, IsOrderedSMul.smul_le_smul, Seminorm, Seminorm.bot_eq_zero, biUnion, bot_eq_zero, classical, comp_mono, eq_empty_or_nonempty, finset_sup_le_sum, le_sup, map_s, pullback_apply, simp_rw, smul_le_smul
-/
theorem isBounded_sup {p : ι -> Seminorm 𝕜 E} {q : ι' -> Seminorm 𝕜₂ F} {f : E ->ₛₗ[σ₁₂] F}
    (hf : IsBounded p q f) (s' : Finset ι') :
    exists (C : Real>=0) (s : Finset ι), (s'.sup q).comp f <= C • s.sup p := by
  classical
  obtain rfl | _ := s'.eq_empty_or_nonempty
  · exact ⟨1, ∅, by simp [Seminorm.bot_eq_zero]⟩
  choose fₛ fC hf using hf
  use s'.card • s'.sup fC, Finset.biUnion s' fₛ
  have hs : forall i : ι', i in s' -> (q i).comp f <= s'.sup fC • (Finset.biUnion s' fₛ).sup p := by
    intro i hi
    refine (hf i).trans (IsOrderedSMul.smul_le_smul (Finset.le_sup hi) ?_)
    exact Finset.sup_mono (Finset.subset_biUnion_of_mem fₛ hi)
  refine (comp_mono f (finset_sup_le_sum q s')).trans ?_
  simp_rw [← pullback_apply, map_sum, pullback_apply]
  refine (Finset.sum_le_sum hs).trans ?_
  rw [Finset.sum_const]; rw [smul_assoc]

end Seminorm

end Bounded

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/--
Definition of `WithSeminorms` / `WithSeminorms` 的定义

English:
structure WithSeminorms
  parameters: (p : SeminormFamily 𝕜 E ι) [topology : TopologicalSpace E]
  axioms and operations (1):
    - topology_eq_withSeminorms : topology = p.moduleFilterBasis.topology

中文:
结构 WithSeminorms
  参数: (p : SeminormFamily 𝕜 E ι) [topology : 拓扑空间 E]
  公理与运算 (1 个):
    - topology_eq_withSeminorms : topology = p.moduleFilterBasis.topology
-/
structure WithSeminorms (p : SeminormFamily 𝕜 E ι) [topology : TopologicalSpace E] : Prop where
  topology_eq_withSeminorms : topology = p.moduleFilterBasis.topology

variable (𝕜 E) in
/--
Definition of `PolynormableSpace` / `PolynormableSpace` 的定义

English:
class PolynormableSpace
  parameters: [topology : TopologicalSpace E]
  axioms and operations (1):
    - withSeminorms' : WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} => p.1)

中文:
类 Polynormable空间
  参数: [topology : 拓扑空间 E]
  公理与运算 (1 个):
    - withSeminorms' : WithSeminorms (fun p : {p : 半范数 𝕜 E // 连续 p} => p.1)
-/
class PolynormableSpace [topology : TopologicalSpace E] where
  withSeminorms' : WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} => p.1)

/--
theorem `WithSeminorms.withSeminorms_eq` / 定理 `WithSeminorms.withSeminorms_eq`

English:
theorem WithSeminorms.withSeminorms_eq
  statement: {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
  proof: hp.1

中文:
定理 WithSeminorms.withSeminorms_eq
  结论: {p : SeminormFamily 𝕜 E ι} [t : 拓扑空间 E]
  证明: hp.1
-/
theorem WithSeminorms.withSeminorms_eq {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) : t = p.moduleFilterBasis.topology :=
  hp.1

variable [TopologicalSpace E]
variable {p : SeminormFamily 𝕜 E ι}

variable (𝕜 E) in
/--
theorem `PolynormableSpace.withSeminorms` / 定理 `PolynormableSpace.withSeminorms`

English:
theorem PolynormableSpace.withSeminorms
  given: [PolynormableSpace 𝕜 E]
  proof: PolynormableSpace.withSeminorms'

中文:
定理 Polynormable空间.withSeminorms
  条件: [Polynormable空间 𝕜 E]
  证明: PolynormableSpace.withSeminorms'

Depends on / 依赖: PolynormableSpace, PolynormableSpace.withSeminorms, withSeminorms
-/
theorem PolynormableSpace.withSeminorms [PolynormableSpace 𝕜 E] :
    WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} => p.1) :=
  PolynormableSpace.withSeminorms'

/--
theorem `WithSeminorms.topologicalAddGroup` / 定理 `WithSeminorms.topologicalAddGroup`

English:
theorem WithSeminorms.topologicalAddGroup
  given: (hp : WithSeminorms p)
  statement: IsTopologicalAddGroup E
  proof: by
  rw [hp.withSeminorms_eq]
  exact AddGroupFilterBasis.isTopologicalAddGroup _

中文:
定理 WithSeminorms.topologicalAddGroup
  条件: (hp : WithSeminorms p)
  结论: 是拓扑加群 E
  证明: by
  rw [hp.withSeminorms_eq]
  exact AddGroupFilterBasis.isTopologicalAddGroup _

Depends on / 依赖: AddGroupFilterBasis, AddGroupFilterBasis.isTopologicalAddGroup, hp.withSeminorms_eq, isTopologicalAddGroup, withSeminorms_eq
-/
theorem WithSeminorms.topologicalAddGroup (hp : WithSeminorms p) : IsTopologicalAddGroup E := by
  rw [hp.withSeminorms_eq]
  exact AddGroupFilterBasis.isTopologicalAddGroup _

/--
theorem `WithSeminorms.continuousSMul` / 定理 `WithSeminorms.continuousSMul`

English:
theorem WithSeminorms.continuousSMul
  given: (hp : WithSeminorms p)
  statement: ContinuousSMul 𝕜 E
  proof: by
  rw [hp.withSeminorms_eq]
  exact ModuleFilterBasis.continuousSMul _

中文:
定理 WithSeminorms.continuousSMul
  条件: (hp : WithSeminorms p)
  结论: 连续标量乘法 𝕜 E
  证明: by
  rw [hp.withSeminorms_eq]
  exact ModuleFilterBasis.continuousSMul _

Depends on / 依赖: ModuleFilterBasis, ModuleFilterBasis.continuousSMul, continuousSMul, hp.withSeminorms_eq, withSeminorms_eq
-/
theorem WithSeminorms.continuousSMul (hp : WithSeminorms p) : ContinuousSMul 𝕜 E := by
  rw [hp.withSeminorms_eq]
  exact ModuleFilterBasis.continuousSMul _

/--
theorem `WithSeminorms.hasBasis` / 定理 `WithSeminorms.hasBasis`

English:
theorem WithSeminorms.hasBasis
  given: (hp : WithSeminorms p)
  proof: by
  rw [congr_fun (congr_arg (@nhds E) hp.1) 0]
  exact AddGroupFilterBasis.nhds_zero_hasBasis _

中文:
定理 WithSeminorms.hasBasis
  条件: (hp : WithSeminorms p)
  证明: by
  rw [congr_fun (congr_arg (@nhds E) hp.1) 0]
  exact AddGroupFilterBasis.nhds_zero_hasBasis _

Depends on / 依赖: AddGroupFilterBasis, AddGroupFilterBasis.nhds_zero_hasBasis, congr_arg, congr_fun, nhds_zero_hasBasis
-/
theorem WithSeminorms.hasBasis (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s in p.basisSets) id := by
  rw [congr_fun (congr_arg (@nhds E) hp.1) 0]
  exact AddGroupFilterBasis.nhds_zero_hasBasis _

/--
theorem `WithSeminorms.hasBasis_zero_ball` / 定理 `WithSeminorms.hasBasis_zero_ball`

English:
theorem WithSeminorms.hasBasis_zero_ball
  given: (hp : WithSeminorms p)
  proof: by
  refine ⟨fun V => ?_⟩
  simp only [hp.hasBasis.mem_iff, SeminormFamily.basisSets_iff, Prod.exists, id_eq]
  grind

中文:
定理 WithSeminorms.hasBasis_zero_ball
  条件: (hp : WithSeminorms p)
  证明: by
  refine ⟨fun V => ?_⟩
  simp only [hp.hasBasis.mem_iff, SeminormFamily.basisSets_iff, Prod.exists, id_eq]
  grind

Depends on / 依赖: Prod.exists, SeminormFamily, SeminormFamily.basisSets_iff, basisSets_iff, hasBasis, hp.hasBasis.mem_iff, id_eq, mem_iff
-/
theorem WithSeminorms.hasBasis_zero_ball (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis
    (fun sr : Finset ι × Real => 0 < sr.2) fun sr => (sr.1.sup p).ball 0 sr.2 := by
  refine ⟨fun V => ?_⟩
  simp only [hp.hasBasis.mem_iff, SeminormFamily.basisSets_iff, Prod.exists, id_eq]
  grind

/--
theorem `WithSeminorms.hasBasis_ball` / 定理 `WithSeminorms.hasBasis_ball`

English:
theorem WithSeminorms.hasBasis_ball
  given: (hp : WithSeminorms p) {x : E}
  proof: by
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  rw [← map_add_left_nhds_zero]
  convert! hp.hasBasis_zero_ball.map (x + ·) using 1
  ext sr : 1
  -- Porting note: extra type ascriptions needed on `0`
  have : (sr.fst.sup p).ball (x +ᵥ (0 : E)) sr.snd = x +ᵥ (sr.fst.sup p).ball 0 sr.snd :=
    Eq.symm (Seminorm.vadd_ball (sr.fst.sup p))
  rwa [vadd_eq_add, add_zero] at this

中文:
定理 WithSeminorms.hasBasis_ball
  条件: (hp : WithSeminorms p) {x : E}
  证明: by
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  rw [← map_add_left_nhds_zero]
  convert! hp.hasBasis_zero_ball.map (x + ·) using 1
  ext sr : 1
  -- Porting note: extra type ascriptions needed on `0`
  have : (sr.fst.sup p).ball (x +ᵥ (0 : E)) sr.snd = x +ᵥ (sr.fst.sup p).ball 0 sr.snd :=
    Eq.symm (Seminorm.vadd_ball (sr.fst.sup p))
  rwa [vadd_eq_add, add_zero] at this

Depends on / 依赖: IsTopologicalAddGroup, convert, hasBasis_zero_ball, hp.hasBasis_zero_ball.map, hp.topologicalAddGroup, map_add_left_nhds_zero, topologicalAddGroup
-/
theorem WithSeminorms.hasBasis_ball (hp : WithSeminorms p) {x : E} :
    (𝓝 (x : E)).HasBasis
    (fun sr : Finset ι × Real => 0 < sr.2) fun sr => (sr.1.sup p).ball x sr.2 := by
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  rw [← map_add_left_nhds_zero]
  convert! hp.hasBasis_zero_ball.map (x + ·) using 1
  ext sr : 1
  -- Porting note: extra type ascriptions needed on `0`
  have : (sr.fst.sup p).ball (x +ᵥ (0 : E)) sr.snd = x +ᵥ (sr.fst.sup p).ball 0 sr.snd :=
    Eq.symm (Seminorm.vadd_ball (sr.fst.sup p))
  rwa [vadd_eq_add, add_zero] at this

/--
theorem `WithSeminorms.mem_nhds_iff` / 定理 `WithSeminorms.mem_nhds_iff`

English:
theorem WithSeminorms.mem_nhds_iff
  given: (hp : WithSeminorms p) (x : E) (U : Set E)
  proof: by
  rw [hp.hasBasis_ball.mem_iff]; rw [Prod.exists]

中文:
定理 WithSeminorms.mem_nhds_iff
  条件: (hp : WithSeminorms p) (x : E) (U : 集合 E)
  证明: by
  rw [hp.hasBasis_ball.mem_iff]; rw [Prod.exists]

Depends on / 依赖: Prod.exists, hasBasis_ball, hp.hasBasis_ball.mem_iff, mem_iff
-/
theorem WithSeminorms.mem_nhds_iff (hp : WithSeminorms p) (x : E) (U : Set E) :
    U in 𝓝 x ↔ exists s : Finset ι, exists r > 0, (s.sup p).ball x r subseteq U := by
  rw [hp.hasBasis_ball.mem_iff]; rw [Prod.exists]

/--
theorem `WithSeminorms.isOpen_iff_mem_balls` / 定理 `WithSeminorms.isOpen_iff_mem_balls`

English:
theorem WithSeminorms.isOpen_iff_mem_balls
  given: (hp : WithSeminorms p) (U : Set E)
  proof: by
  simp_rw [← WithSeminorms.mem_nhds_iff hp _ U, isOpen_iff_mem_nhds]

中文:
定理 WithSeminorms.isOpen_iff_mem_balls
  条件: (hp : WithSeminorms p) (U : 集合 E)
  证明: by
  simp_rw [← WithSeminorms.mem_nhds_iff hp _ U, isOpen_iff_mem_nhds]

Depends on / 依赖: WithSeminorms, WithSeminorms.mem_nhds_iff, isOpen_iff_mem_nhds, mem_nhds_iff, simp_rw
-/
theorem WithSeminorms.isOpen_iff_mem_balls (hp : WithSeminorms p) (U : Set E) :
    IsOpen U ↔ forall x in U, exists s : Finset ι, exists r > 0, (s.sup p).ball x r subseteq U := by
  simp_rw [← WithSeminorms.mem_nhds_iff hp _ U, isOpen_iff_mem_nhds]

/- Note that through the following lemmas, one also immediately has that separating families
of seminorms induce T₂ and T₃ topologies by `IsTopologicalAddGroup.t2Space`
and `IsTopologicalAddGroup.t3Space` -/
/--
theorem `WithSeminorms.T1_of_separating` / 定理 `WithSeminorms.T1_of_separating`

English:
theorem WithSeminorms.T1_of_separating
  statement: (hp : WithSeminorms p)
  proof: by
  have := hp.topologicalAddGroup
  refine IsTopologicalAddGroup.t1Space _ ?_
  rw [← isOpen_compl_iff]; rw [hp.isOpen_iff_mem_balls]
  rintro x (hx : x != 0)
  obtain ⟨i, pi_nonzero⟩ := h x hx
  refine ⟨{i}, p i x, by positivity, subset_compl_singleton_iff.mpr ?_⟩
  rw [Finset.sup_singleton]; rw [mem_ball]; rw [zero_sub]; rw [map_neg_eq_map]; rw [not_lt]

中文:
定理 WithSeminorms.T1_of_separating
  结论: (hp : WithSeminorms p)
  证明: by
  have := hp.topologicalAddGroup
  refine IsTopologicalAddGroup.t1Space _ ?_
  rw [← isOpen_compl_iff]; rw [hp.isOpen_iff_mem_balls]
  rintro x (hx : x != 0)
  obtain ⟨i, pi_nonzero⟩ := h x hx
  refine ⟨{i}, p i x, by positivity, subset_compl_singleton_iff.mpr ?_⟩
  rw [Finset.sup_singleton]; rw [mem_ball]; rw [zero_sub]; rw [map_neg_eq_map]; rw [not_lt]

Depends on / 依赖: Finset, Finset.sup_singleton, IsTopologicalAddGroup, IsTopologicalAddGroup.t1Space, hp.isOpen_iff_mem_balls, hp.topologicalAddGroup, isOpen_compl_iff, isOpen_iff_mem_balls, map_neg_eq_map, mem_ball, not_lt, pi_nonzero, subset_compl_singleton_iff, subset_compl_singleton_iff.mpr, sup_singleton, t1Space, topologicalAddGroup, zero_sub
-/
theorem WithSeminorms.T1_of_separating (hp : WithSeminorms p)
    (h : forall x, x != 0 -> exists i, p i x != 0) : T1Space E := by
  have := hp.topologicalAddGroup
  refine IsTopologicalAddGroup.t1Space _ ?_
  rw [← isOpen_compl_iff]; rw [hp.isOpen_iff_mem_balls]
  rintro x (hx : x != 0)
  obtain ⟨i, pi_nonzero⟩ := h x hx
  refine ⟨{i}, p i x, by positivity, subset_compl_singleton_iff.mpr ?_⟩
  rw [Finset.sup_singleton]; rw [mem_ball]; rw [zero_sub]; rw [map_neg_eq_map]; rw [not_lt]

/--
theorem `WithSeminorms.separating_of_T1` / 定理 `WithSeminorms.separating_of_T1`

English:
theorem WithSeminorms.separating_of_T1
  given: [T1Space E] (hp : WithSeminorms p) (x : E) (hx : x != 0)
  proof: by
  have := ((t1Space_TFAE E).out 0 9).mp (inferInstance : T1Space E)
  by_contra! h
  refine hx (this ?_)
  rw [hp.hasBasis_zero_ball.specializes_iff]
  rintro ⟨s, r⟩ (hr : 0 < r)
  simp only [ball_finset_sup_eq_iInter _ _ _ hr, mem_iInter₂, mem_ball_zero, h, hr, forall_true_iff]

中文:
定理 WithSeminorms.separating_of_T1
  条件: [T1空间 E] (hp : WithSeminorms p) (x : E) (hx : x != 0)
  证明: by
  have := ((t1Space_TFAE E).out 0 9).mp (inferInstance : T1Space E)
  by_contra! h
  refine hx (this ?_)
  rw [hp.hasBasis_zero_ball.specializes_iff]
  rintro ⟨s, r⟩ (hr : 0 < r)
  simp only [ball_finset_sup_eq_iInter _ _ _ hr, mem_iInter₂, mem_ball_zero, h, hr, forall_true_iff]

Depends on / 依赖: T1Space, ball_finset_sup_eq_iInter, forall_true_iff, hasBasis_zero_ball, hp.hasBasis_zero_ball.specializes_iff, mem_ball_zero, specializes_iff, t1Space_TFAE
-/
theorem WithSeminorms.separating_of_T1 [T1Space E] (hp : WithSeminorms p) (x : E) (hx : x != 0) :
    exists i, p i x != 0 := by
  have := ((t1Space_TFAE E).out 0 9).mp (inferInstance : T1Space E)
  by_contra! h
  refine hx (this ?_)
  rw [hp.hasBasis_zero_ball.specializes_iff]
  rintro ⟨s, r⟩ (hr : 0 < r)
  simp only [ball_finset_sup_eq_iInter _ _ _ hr, mem_iInter₂, mem_ball_zero, h, hr, forall_true_iff]

/--
theorem `WithSeminorms.separating_iff_T1` / 定理 `WithSeminorms.separating_iff_T1`

English:
theorem WithSeminorms.separating_iff_T1
  given: (hp : WithSeminorms p)
  proof: by
  refine ⟨WithSeminorms.T1_of_separating hp, ?_⟩
  intro
  exact WithSeminorms.separating_of_T1 hp

中文:
定理 WithSeminorms.separating_iff_T1
  条件: (hp : WithSeminorms p)
  证明: by
  refine ⟨WithSeminorms.T1_of_separating hp, ?_⟩
  intro
  exact WithSeminorms.separating_of_T1 hp

Depends on / 依赖: T1_of_separating, WithSeminorms, WithSeminorms.T1_of_separating, WithSeminorms.separating_of_T1, separating_of_T1
-/
theorem WithSeminorms.separating_iff_T1 (hp : WithSeminorms p) :
    (forall x, x != 0 -> exists i, p i x != 0) ↔ T1Space E := by
  refine ⟨WithSeminorms.T1_of_separating hp, ?_⟩
  intro
  exact WithSeminorms.separating_of_T1 hp

end Topology

section Tendsto

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {p : SeminormFamily 𝕜 E ι}

/--
theorem `WithSeminorms.tendsto_nhds'` / 定理 `WithSeminorms.tendsto_nhds'`

English:
theorem WithSeminorms.tendsto_nhds'
  given: (hp : WithSeminorms p) (u : F -> E) {f : Filter F} (y₀ : E)
  proof: by
  simp [hp.hasBasis_ball.tendsto_right_iff]

中文:
定理 WithSeminorms.tendsto_nhds'
  条件: (hp : WithSeminorms p) (u : F -> E) {f : 滤子 F} (y₀ : E)
  证明: by
  simp [hp.hasBasis_ball.tendsto_right_iff]

Depends on / 依赖: hasBasis_ball, hp.hasBasis_ball.tendsto_right_iff, tendsto_right_iff
-/
theorem WithSeminorms.tendsto_nhds' (hp : WithSeminorms p) (u : F -> E) {f : Filter F} (y₀ : E) :
    Filter.Tendsto u f (𝓝 y₀) ↔
    forall (s : Finset ι) (ε), 0 < ε -> forallᶠ x in f, s.sup p (u x - y₀) < ε := by
  simp [hp.hasBasis_ball.tendsto_right_iff]

/--
theorem `WithSeminorms.tendsto_nhds` / 定理 `WithSeminorms.tendsto_nhds`

English:
theorem WithSeminorms.tendsto_nhds
  given: (hp : WithSeminorms p) (u : F -> E) {f : Filter F} (y₀ : E)
  proof: by
  rw [hp.tendsto_nhds' u y₀]
  exact
    ⟨fun h i => by simpa only [Finset.sup_singleton] using h {i}, fun h s ε hε =>
      (s.eventually_all.2 fun i _ => h i ε hε).mono fun _ => finset_sup_apply_lt hε⟩

中文:
定理 WithSeminorms.tendsto_nhds
  条件: (hp : WithSeminorms p) (u : F -> E) {f : 滤子 F} (y₀ : E)
  证明: by
  rw [hp.tendsto_nhds' u y₀]
  exact
    ⟨fun h i => by simpa only [Finset.sup_singleton] using h {i}, fun h s ε hε =>
      (s.eventually_all.2 fun i _ => h i ε hε).mono fun _ => finset_sup_apply_lt hε⟩

Depends on / 依赖: Finset, Finset.sup_singleton, eventually_all, finset_sup_apply_lt, hp.tendsto_nhds, s.eventually_all, sup_singleton, tendsto_nhds
-/
theorem WithSeminorms.tendsto_nhds (hp : WithSeminorms p) (u : F -> E) {f : Filter F} (y₀ : E) :
    Filter.Tendsto u f (𝓝 y₀) ↔ forall i ε, 0 < ε -> forallᶠ x in f, p i (u x - y₀) < ε := by
  rw [hp.tendsto_nhds' u y₀]
  exact
    ⟨fun h i => by simpa only [Finset.sup_singleton] using h {i}, fun h s ε hε =>
      (s.eventually_all.2 fun i _ => h i ε hε).mono fun _ => finset_sup_apply_lt hε⟩

variable [SemilatticeSup F] [Nonempty F]

/--
theorem `WithSeminorms.tendsto_nhds_atTop` / 定理 `WithSeminorms.tendsto_nhds_atTop`

English:
theorem WithSeminorms.tendsto_nhds_atTop
  given: (hp : WithSeminorms p) (u : F -> E) (y₀ : E)
  proof: by
  rw [hp.tendsto_nhds u y₀]
  exact forall₃_congr fun _ _ _ => Filter.eventually_atTop

中文:
定理 WithSeminorms.tendsto_nhds_atTop
  条件: (hp : WithSeminorms p) (u : F -> E) (y₀ : E)
  证明: by
  rw [hp.tendsto_nhds u y₀]
  exact forall₃_congr fun _ _ _ => Filter.eventually_atTop

Depends on / 依赖: Filter, Filter.eventually_atTop, eventually_atTop, hp.tendsto_nhds, tendsto_nhds
-/
theorem WithSeminorms.tendsto_nhds_atTop (hp : WithSeminorms p) (u : F -> E) (y₀ : E) :
    Filter.Tendsto u Filter.atTop (𝓝 y₀) ↔
    forall i ε, 0 < ε -> exists x₀, forall x, x₀ <= x -> p i (u x - y₀) < ε := by
  rw [hp.tendsto_nhds u y₀]
  exact forall₃_congr fun _ _ _ => Filter.eventually_atTop

end Tendsto

section IsTopologicalAddGroup

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

section TopologicalSpace

variable [t : TopologicalSpace E]

/--
theorem `SeminormFamily.withSeminorms_of_nhds` / 定理 `SeminormFamily.withSeminorms_of_nhds`

English:
theorem SeminormFamily.withSeminorms_of_nhds
  statement: [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι)
  proof: by
  refine
    ⟨IsTopologicalAddGroup.ext inferInstance p.addGroupFilterBasis.isTopologicalAddGroup ?_⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  exact h

中文:
定理 SeminormFamily.withSeminorms_of_nhds
  结论: [是拓扑加群 E] (p : SeminormFamily 𝕜 E ι)
  证明: by
  refine
    ⟨IsTopologicalAddGroup.ext inferInstance p.addGroupFilterBasis.isTopologicalAddGroup ?_⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  exact h

Depends on / 依赖: AddGroupFilterBasis, AddGroupFilterBasis.nhds_zero_eq, IsTopologicalAddGroup, IsTopologicalAddGroup.ext, addGroupFilterBasis, isTopologicalAddGroup, nhds_zero_eq, p.addGroupFilterBasis.isTopologicalAddGroup
-/
theorem SeminormFamily.withSeminorms_of_nhds [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι)
    (h : 𝓝 (0 : E) = p.moduleFilterBasis.toFilterBasis.filter) : WithSeminorms p := by
  refine
    ⟨IsTopologicalAddGroup.ext inferInstance p.addGroupFilterBasis.isTopologicalAddGroup ?_⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  exact h

/--
theorem `SeminormFamily.withSeminorms_of_hasBasis` / 定理 `SeminormFamily.withSeminorms_of_hasBasis`

English:
theorem SeminormFamily.withSeminorms_of_hasBasis
  statement: [IsTopologicalAddGroup E]
  proof: p.withSeminorms_of_nhds
    Filter.HasBasis.eq_of_same_basis h p.addGroupFilterBasis.toFilterBasis.hasBasis

中文:
定理 SeminormFamily.withSeminorms_of_hasBasis
  结论: [是拓扑加群 E]
  证明: p.withSeminorms_of_nhds
    Filter.HasBasis.eq_of_same_basis h p.addGroupFilterBasis.toFilterBasis.hasBasis

Depends on / 依赖: Filter, Filter.HasBasis.eq_of_same_basis, HasBasis, addGroupFilterBasis, eq_of_same_basis, hasBasis, p.addGroupFilterBasis.toFilterBasis.hasBasis, p.withSeminorms_of_nhds, toFilterBasis, withSeminorms_of_nhds
-/
theorem SeminormFamily.withSeminorms_of_hasBasis [IsTopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) (h : (𝓝 (0 : E)).HasBasis (fun s : Set E => s in p.basisSets) id) :
    WithSeminorms p :=
p.withSeminorms_of_nhds
    Filter.HasBasis.eq_of_same_basis h p.addGroupFilterBasis.toFilterBasis.hasBasis

/--
theorem `SeminormFamily.withSeminorms_iff_nhds_eq_iInf` / 定理 `SeminormFamily.withSeminorms_iff_nhds_eq_iInf`

English:
theorem SeminormFamily.withSeminorms_iff_nhds_eq_iInf
  statement: [IsTopologicalAddGroup E]
  proof: by
  rw [← p.filter_eq_iInf]
  refine ⟨fun h => ?_, p.withSeminorms_of_nhds⟩
  rw [h.topology_eq_withSeminorms]
  exact AddGroupFilterBasis.nhds_zero_eq _

中文:
定理 SeminormFamily.withSeminorms_iff_nhds_eq_iInf
  结论: [是拓扑加群 E]
  证明: by
  rw [← p.filter_eq_iInf]
  refine ⟨fun h => ?_, p.withSeminorms_of_nhds⟩
  rw [h.topology_eq_withSeminorms]
  exact AddGroupFilterBasis.nhds_zero_eq _

Depends on / 依赖: AddGroupFilterBasis, AddGroupFilterBasis.nhds_zero_eq, filter_eq_iInf, h.topology_eq_withSeminorms, nhds_zero_eq, p.filter_eq_iInf, p.withSeminorms_of_nhds, topology_eq_withSeminorms, withSeminorms_of_nhds
-/
theorem SeminormFamily.withSeminorms_iff_nhds_eq_iInf [IsTopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) : WithSeminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝 0).comap (p i) := by
  rw [← p.filter_eq_iInf]
  refine ⟨fun h => ?_, p.withSeminorms_of_nhds⟩
  rw [h.topology_eq_withSeminorms]
  exact AddGroupFilterBasis.nhds_zero_eq _

/--
theorem `SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf` / 定理 `SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf`

English:
theorem SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf
  statement: [IsTopologicalAddGroup E]
  proof: by
  rw [p.withSeminorms_iff_nhds_eq_iInf]; rw [IsTopologicalAddGroup.ext_iff inferInstance (topologicalAddGroup_iInf fun i => inferInstance)]; rw [nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toSeminormedAddGroup

中文:
定理 SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf
  结论: [是拓扑加群 E]
  证明: by
  rw [p.withSeminorms_iff_nhds_eq_iInf]; rw [IsTopologicalAddGroup.ext_iff inferInstance (topologicalAddGroup_iInf fun i => inferInstance)]; rw [nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toSeminormedAddGroup

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.ext_iff, comap_norm_nhds_zero, congrm, ext_iff, nhds_iInf, p.withSeminorms_iff_nhds_eq_iInf, toSeminormedAddGroup, topologicalAddGroup_iInf, withSeminorms_iff_nhds_eq_iInf
-/
theorem SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf [IsTopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔
      t = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  rw [p.withSeminorms_iff_nhds_eq_iInf]; rw [IsTopologicalAddGroup.ext_iff inferInstance (topologicalAddGroup_iInf fun i => inferInstance)]; rw [nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toSeminormedAddGroup

/--
theorem `WithSeminorms.continuous_seminorm` / 定理 `WithSeminorms.continuous_seminorm`

English:
theorem WithSeminorms.continuous_seminorm
  statement: {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
  proof: by
  have := hp.topologicalAddGroup
  rw [p.withSeminorms_iff_topologicalSpace_eq_iInf.mp hp]
  exact continuous_iInf_dom (@continuous_norm _ (p i).toSeminormedAddGroup)

中文:
定理 WithSeminorms.continuous_seminorm
  结论: {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
  证明: by
  have := hp.topologicalAddGroup
  rw [p.withSeminorms_iff_topologicalSpace_eq_iInf.mp hp]
  exact continuous_iInf_dom (@continuous_norm _ (p i).toSeminormedAddGroup)

Depends on / 依赖: continuous_iInf_dom, continuous_norm, hp.topologicalAddGroup, p.withSeminorms_iff_topologicalSpace_eq_iInf.mp, toSeminormedAddGroup, topologicalAddGroup, withSeminorms_iff_topologicalSpace_eq_iInf
-/
theorem WithSeminorms.continuous_seminorm {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
    (i : ι) : Continuous (p i) := by
  have := hp.topologicalAddGroup
  rw [p.withSeminorms_iff_topologicalSpace_eq_iInf.mp hp]
  exact continuous_iInf_dom (@continuous_norm _ (p i).toSeminormedAddGroup)

/--
theorem `WithSeminorms.toPolynormableSpace` / 定理 `WithSeminorms.toPolynormableSpace`

English:
theorem WithSeminorms.toPolynormableSpace
  given: {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
  proof: by
    have := hp.topologicalAddGroup
    have hp' (i : ι) : Continuous (p i) := hp.continuous_seminorm i
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at ⊢ hp
    refine le_antisymm ?_ ?_
    · simp_rw [le_iInf_iff, ← tendsto_iff_comap]
      intro ⟨p, hp⟩
      exact hp.tendsto' 0 0 (map_zero _)
    · simp_rw [hp, le_iInf_iff]
      intro i
      exact iInf_le (ι := {p : Seminorm 𝕜 E // Continuous p}) _ ⟨p i, hp' i⟩

中文:
定理 WithSeminorms.toPolynormableSpace
  条件: {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
  证明: by
    have := hp.topologicalAddGroup
    have hp' (i : ι) : Continuous (p i) := hp.continuous_seminorm i
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at ⊢ hp
    refine le_antisymm ?_ ?_
    · simp_rw [le_iInf_iff, ← tendsto_iff_comap]
      intro ⟨p, hp⟩
      exact hp.tendsto' 0 0 (map_zero _)
    · simp_rw [hp, le_iInf_iff]
      intro i
      exact iInf_le (ι := {p : Seminorm 𝕜 E // Continuous p}) _ ⟨p i, hp' i⟩

Depends on / 依赖: Continuous, Seminorm, SeminormFamily, SeminormFamily.withSeminorms_iff_nhds_eq_iInf, continuous_seminorm, hp.continuous_seminorm, hp.tendsto, hp.topologicalAddGroup, iInf_le, le_antisymm, le_iInf_iff, map_zero, simp_rw, tendsto, tendsto_iff_comap, topologicalAddGroup, withSeminorms_iff_nhds_eq_iInf
-/
theorem WithSeminorms.toPolynormableSpace {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    PolynormableSpace 𝕜 E where
  withSeminorms' := by
    have := hp.topologicalAddGroup
    have hp' (i : ι) : Continuous (p i) := hp.continuous_seminorm i
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at ⊢ hp
    refine le_antisymm ?_ ?_
    · simp_rw [le_iInf_iff, ← tendsto_iff_comap]
      intro ⟨p, hp⟩
      exact hp.tendsto' 0 0 (map_zero _)
    · simp_rw [hp, le_iInf_iff]
      intro i
      exact iInf_le (ι := {p : Seminorm 𝕜 E // Continuous p}) _ ⟨p i, hp' i⟩

end TopologicalSpace

/--
theorem `SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf` / 定理 `SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf`

English:
theorem SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf
  statement: [u : UniformSpace E]
  proof: by
  rw [p.withSeminorms_iff_nhds_eq_iInf]; rw [IsUniformAddGroup.ext_iff inferInstance (isUniformAddGroup_iInf fun i => inferInstance)]; rw [UniformSpace.toTopologicalSpace_iInf]; rw [nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toAddGroupSeminorm.toSeminormedAddGroup

中文:
定理 SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf
  结论: [u : 一致空间 E]
  证明: by
  rw [p.withSeminorms_iff_nhds_eq_iInf]; rw [IsUniformAddGroup.ext_iff inferInstance (isUniformAddGroup_iInf fun i => inferInstance)]; rw [UniformSpace.toTopologicalSpace_iInf]; rw [nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toAddGroupSeminorm.toSeminormedAddGroup

Depends on / 依赖: IsUniformAddGroup, IsUniformAddGroup.ext_iff, UniformSpace, UniformSpace.toTopologicalSpace_iInf, comap_norm_nhds_zero, congrm, ext_iff, isUniformAddGroup_iInf, nhds_iInf, p.withSeminorms_iff_nhds_eq_iInf, toAddGroupSeminorm, toAddGroupSeminorm.toSeminormedAddGroup, toSeminormedAddGroup, toTopologicalSpace_iInf, withSeminorms_iff_nhds_eq_iInf
-/
theorem SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf [u : UniformSpace E]
    [IsUniformAddGroup E] (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔ u = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace := by
  rw [p.withSeminorms_iff_nhds_eq_iInf]; rw [IsUniformAddGroup.ext_iff inferInstance (isUniformAddGroup_iInf fun i => inferInstance)]; rw [UniformSpace.toTopologicalSpace_iInf]; rw [nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toAddGroupSeminorm.toSeminormedAddGroup

end IsTopologicalAddGroup

section NormedSpace

/--
theorem `norm_withSeminorms` / 定理 `norm_withSeminorms`

English:
theorem norm_withSeminorms
  given: (𝕜 E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]; rw [iInf_const]; rw [coe_normSeminorm]; rw [comap_norm_nhds_zero]

中文:
定理 norm_withSeminorms
  条件: (𝕜 E) [赋范域 𝕜] [SeminormedAddComm群 E] [赋范空间 𝕜 E]
  证明: by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]; rw [iInf_const]; rw [coe_normSeminorm]; rw [comap_norm_nhds_zero]

Depends on / 依赖: SeminormFamily, SeminormFamily.withSeminorms_iff_nhds_eq_iInf, coe_normSeminorm, comap_norm_nhds_zero, iInf_const, withSeminorms_iff_nhds_eq_iInf
-/
theorem norm_withSeminorms (𝕜 E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    WithSeminorms fun _ : Fin 1 => normSeminorm 𝕜 E := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]; rw [iInf_const]; rw [coe_normSeminorm]; rw [comap_norm_nhds_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedField
  signature: 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
  body: .toPolynormableSpace norm_withSeminorms 𝕜 E

中文:
实例 [赋范域
  签名: 𝕜] [SeminormedAddComm群 E] [赋范空间 𝕜 E] :
  定义体: .toPolynormableSpace norm_withSeminorms 𝕜 E

Depends on / 依赖: norm_withSeminorms, toPolynormableSpace
-/
instance [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    PolynormableSpace 𝕜 E :=
.toPolynormableSpace norm_withSeminorms 𝕜 E

end NormedSpace

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {p : SeminormFamily 𝕜 E ι}
variable [TopologicalSpace E]

/--
theorem `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded` / 定理 `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded`

English:
theorem WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded
  given: {s : Set E} (hp : WithSeminorms p)
  proof: by
  rw [hp.hasBasis.isVonNBounded_iff]
  constructor
  · intro h I
    simp only [id] at h
    specialize h ((I.sup p).ball 0 1) (p.basisSets_mem I zero_lt_one)
    rcases h.exists_pos with ⟨r, hr, h⟩
    obtain ⟨a, ha⟩ := NormedField.exists_lt_norm 𝕜 r
    specialize h a (le_of_lt ha)
    rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hr.trans ha)]; rw [mul_one] at h
    refine ⟨‖a‖, lt_trans hr ha, ?_⟩
    intro x hx
    specialize h hx
    exact (Finset.sup I p).mem_ball_zero.mp h
  intro h s' hs'
  rcases p.basisSets_iff.mp hs' with ⟨I, r, hr, hs'⟩
  rw [id]; rw [hs']
  rcases h I with ⟨r', _, h'⟩
  simp_rw [← (I.sup p).mem_ball_zero] at h'
  refine Absorbs.mono_right ?_ h'
  exact (Finset.sup I p).ball_zero_absorbs_ball_zero hr

中文:
定理 WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded
  条件: {s : 集合 E} (hp : WithSeminorms p)
  证明: by
  rw [hp.hasBasis.isVonNBounded_iff]
  constructor
  · intro h I
    simp only [id] at h
    specialize h ((I.sup p).ball 0 1) (p.basisSets_mem I zero_lt_one)
    rcases h.exists_pos with ⟨r, hr, h⟩
    obtain ⟨a, ha⟩ := NormedField.exists_lt_norm 𝕜 r
    specialize h a (le_of_lt ha)
    rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hr.trans ha)]; rw [mul_one] at h
    refine ⟨‖a‖, lt_trans hr ha, ?_⟩
    intro x hx
    specialize h hx
    exact (Finset.sup I p).mem_ball_zero.mp h
  intro h s' hs'
  rcases p.basisSets_iff.mp hs' with ⟨I, r, hr, hs'⟩
  rw [id]; rw [hs']
  rcases h I with ⟨r', _, h'⟩
  simp_rw [← (I.sup p).mem_ball_zero] at h'
  refine Absorbs.mono_right ?_ h'
  exact (Finset.sup I p).ball_zero_absorbs_ball_zero hr

Depends on / 依赖: Finset, Finset.sup, I.sup, NormedField, NormedField.exists_lt_norm, Seminorm, Seminorm.smul_ball_zero, basisSets_iff, basisSets_mem, exists_lt_norm, exists_pos, h.exists_pos, hasBasis, hp.hasBasis.isVonNBounded_iff, hr.trans, isVonNBounded_iff, le_of_lt, lt_trans, mem_ball_zero, mem_ball_zero.mp
-/
theorem WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded {s : Set E} (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 s ↔ forall I : Finset ι, exists r > 0, forall x in s, I.sup p x < r := by
  rw [hp.hasBasis.isVonNBounded_iff]
  constructor
  · intro h I
    simp only [id] at h
    specialize h ((I.sup p).ball 0 1) (p.basisSets_mem I zero_lt_one)
    rcases h.exists_pos with ⟨r, hr, h⟩
    obtain ⟨a, ha⟩ := NormedField.exists_lt_norm 𝕜 r
    specialize h a (le_of_lt ha)
    rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hr.trans ha)]; rw [mul_one] at h
    refine ⟨‖a‖, lt_trans hr ha, ?_⟩
    intro x hx
    specialize h hx
    exact (Finset.sup I p).mem_ball_zero.mp h
  intro h s' hs'
  rcases p.basisSets_iff.mp hs' with ⟨I, r, hr, hs'⟩
  rw [id]; rw [hs']
  rcases h I with ⟨r', _, h'⟩
  simp_rw [← (I.sup p).mem_ball_zero] at h'
  refine Absorbs.mono_right ?_ h'
  exact (Finset.sup I p).ball_zero_absorbs_ball_zero hr

/--
theorem `WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded` / 定理 `WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded`

English:
theorem WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded
  statement: (f : G -> E) {s : Set G}
  proof: by
  simp_rw [hp.isVonNBounded_iff_finset_seminorm_bounded, Set.forall_mem_image]

中文:
定理 WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded
  结论: (f : G -> E) {s : 集合 G}
  证明: by
  simp_rw [hp.isVonNBounded_iff_finset_seminorm_bounded, Set.forall_mem_image]

Depends on / 依赖: Set.forall_mem_image, forall_mem_image, hp.isVonNBounded_iff_finset_seminorm_bounded, isVonNBounded_iff_finset_seminorm_bounded, simp_rw
-/
theorem WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded (f : G -> E) {s : Set G}
    (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 (f '' s) ↔
      forall I : Finset ι, exists r > 0, forall x in s, I.sup p (f x) < r := by
  simp_rw [hp.isVonNBounded_iff_finset_seminorm_bounded, Set.forall_mem_image]

/--
theorem `WithSeminorms.isVonNBounded_iff_seminorm_bounded` / 定理 `WithSeminorms.isVonNBounded_iff_seminorm_bounded`

English:
theorem WithSeminorms.isVonNBounded_iff_seminorm_bounded
  given: {s : Set E} (hp : WithSeminorms p)
  proof: by
  rw [hp.isVonNBounded_iff_finset_seminorm_bounded]
  constructor
  · intro hI i
    convert! hI { i }
    rw [Finset.sup_singleton]
  intro hi I
  by_cases! hI : I.Nonempty
  · choose r hr h using hi
    have h' : 0 < I.sup' hI r := by
      rcases hI with ⟨i, hi⟩
      exact lt_of_lt_of_le (hr i) (Finset.le_sup' r hi)
    refine ⟨I.sup' hI r, h', fun x hx => finset_sup_apply_lt h' fun i hi => ?_⟩
    refine lt_of_lt_of_le (h i x hx) ?_
    simp only [Finset.le_sup'_iff]
    exact ⟨i, hi, (Eq.refl _).le⟩
  simp only [hI, Finset.sup_empty, coe_bot, Pi.zero_apply]
  exact ⟨1, zero_lt_one, fun _ _ => zero_lt_one⟩

中文:
定理 WithSeminorms.isVonNBounded_iff_seminorm_bounded
  条件: {s : 集合 E} (hp : WithSeminorms p)
  证明: by
  rw [hp.isVonNBounded_iff_finset_seminorm_bounded]
  constructor
  · intro hI i
    convert! hI { i }
    rw [Finset.sup_singleton]
  intro hi I
  by_cases! hI : I.Nonempty
  · choose r hr h using hi
    have h' : 0 < I.sup' hI r := by
      rcases hI with ⟨i, hi⟩
      exact lt_of_lt_of_le (hr i) (Finset.le_sup' r hi)
    refine ⟨I.sup' hI r, h', fun x hx => finset_sup_apply_lt h' fun i hi => ?_⟩
    refine lt_of_lt_of_le (h i x hx) ?_
    simp only [Finset.le_sup'_iff]
    exact ⟨i, hi, (Eq.refl _).le⟩
  simp only [hI, Finset.sup_empty, coe_bot, Pi.zero_apply]
  exact ⟨1, zero_lt_one, fun _ _ => zero_lt_one⟩

Depends on / 依赖: Eq.refl, Finset, Finset.le_sup, Finset.sup_empty, Finset.sup_singleton, I.Nonempty, I.sup, Nonempty, _iff, coe_b, convert, finset_sup_apply_lt, hp.isVonNBounded_iff_finset_seminorm_bounded, isVonNBounded_iff_finset_seminorm_bounded, le_sup, lt_of_lt_of_le, sup_empty, sup_singleton
-/
theorem WithSeminorms.isVonNBounded_iff_seminorm_bounded {s : Set E} (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 s ↔ forall i : ι, exists r > 0, forall x in s, p i x < r := by
  rw [hp.isVonNBounded_iff_finset_seminorm_bounded]
  constructor
  · intro hI i
    convert! hI { i }
    rw [Finset.sup_singleton]
  intro hi I
  by_cases! hI : I.Nonempty
  · choose r hr h using hi
    have h' : 0 < I.sup' hI r := by
      rcases hI with ⟨i, hi⟩
      exact lt_of_lt_of_le (hr i) (Finset.le_sup' r hi)
    refine ⟨I.sup' hI r, h', fun x hx => finset_sup_apply_lt h' fun i hi => ?_⟩
    refine lt_of_lt_of_le (h i x hx) ?_
    simp only [Finset.le_sup'_iff]
    exact ⟨i, hi, (Eq.refl _).le⟩
  simp only [hI, Finset.sup_empty, coe_bot, Pi.zero_apply]
  exact ⟨1, zero_lt_one, fun _ _ => zero_lt_one⟩

/--
theorem `WithSeminorms.image_isVonNBounded_iff_seminorm_bounded` / 定理 `WithSeminorms.image_isVonNBounded_iff_seminorm_bounded`

English:
theorem WithSeminorms.image_isVonNBounded_iff_seminorm_bounded
  statement: (f : G -> E) {s : Set G}
  proof: by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, Set.forall_mem_image]

中文:
定理 WithSeminorms.image_isVonNBounded_iff_seminorm_bounded
  结论: (f : G -> E) {s : 集合 G}
  证明: by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, Set.forall_mem_image]

Depends on / 依赖: Set.forall_mem_image, forall_mem_image, hp.isVonNBounded_iff_seminorm_bounded, isVonNBounded_iff_seminorm_bounded, simp_rw
-/
theorem WithSeminorms.image_isVonNBounded_iff_seminorm_bounded (f : G -> E) {s : Set G}
    (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 (f '' s) ↔ forall i : ι, exists r > 0, forall x in s, p i (f x) < r := by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, Set.forall_mem_image]

/--
theorem `WithSeminorms.isVonNBounded_iff_seminorm_bddAbove` / 定理 `WithSeminorms.isVonNBounded_iff_seminorm_bddAbove`

English:
theorem WithSeminorms.isVonNBounded_iff_seminorm_bddAbove
  given: {s : Set E} (hp : WithSeminorms p)
  proof: by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, bddAbove_def, forall_mem_image]
  congrm forall i, ?_
  constructor
  · rintro ⟨r, _⟩
    use r
    grind
  · rintro ⟨r, _⟩
    use 1 + max r 0
    grind

中文:
定理 WithSeminorms.isVonNBounded_iff_seminorm_bddAbove
  条件: {s : 集合 E} (hp : WithSeminorms p)
  证明: by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, bddAbove_def, forall_mem_image]
  congrm forall i, ?_
  constructor
  · rintro ⟨r, _⟩
    use r
    grind
  · rintro ⟨r, _⟩
    use 1 + max r 0
    grind

Depends on / 依赖: bddAbove_def, congrm, forall_mem_image, hp.isVonNBounded_iff_seminorm_bounded, isVonNBounded_iff_seminorm_bounded, simp_rw
-/
theorem WithSeminorms.isVonNBounded_iff_seminorm_bddAbove {s : Set E} (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 s ↔ forall i : ι, BddAbove (p i '' s) := by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, bddAbove_def, forall_mem_image]
  congrm forall i, ?_
  constructor
  · rintro ⟨r, _⟩
    use r
    grind
  · rintro ⟨r, _⟩
    use 1 + max r 0
    grind

/--
theorem `withSeminorms_iff_mem_nhds_isVonNBounded` / 定理 `withSeminorms_iff_mem_nhds_isVonNBounded`

English:
theorem withSeminorms_iff_mem_nhds_isVonNBounded
  statement: [IsTopologicalAddGroup E]
  proof: by
  /- The nontrivial direction is from right to left. With `SeminormFamily.withSeminorms_of_nhds`,
  we need to see that the neighborhoods of zero for the initial topology and for `p` coincide. -/
  refine ⟨fun h => ⟨?_, ?_⟩, ?_⟩
  · apply (h.mem_nhds_iff _ _).2
    exact ⟨Finset.univ, 1, zero_lt_one, by simp⟩
  · apply h.isVonNBounded_iff_seminorm_bounded.2 (fun i => ?_)
    exact ⟨1, zero_lt_one, by simp⟩
  rintro ⟨h, h'⟩
  apply SeminormFamily.withSeminorms_of_nhds
  ext s
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · /- Show that a neighborhood `s` of zero for the topology is a neighborhood for `p`, by using the
    boundedness of `p.ball 0 1`: this ensures that, for some nonzero `c`, we have
    `p.ball 0 1 ⊆ c • s`, and therefore `p.ball 0 (‖c‖⁻¹) ⊆ s`. -/
    obtain ⟨c, hc, c_ne⟩ : exists (c : 𝕜), p.ball 0 1 subseteq c • s ∧ c != 0 :=
      ((h' hs).and (eventually_ne_cobounded 0)).exists
    have : p.ball 0 (‖c⁻¹‖) subseteq s := by
      have : c • p.ball 0 (‖c⁻¹‖) subseteq c • s := by
        simpa [smul_ball_zero c_ne, ← norm_mul, c_ne] using hc
      rwa [smul_set_subset_smul_set_iff₀ c_ne] at this
    grw [← this]
    apply FilterBasis.mem_filter_of_mem
    change p.ball 0 (‖c⁻¹‖) in SeminormFamily.basisSets (fun (i : Fin 1) => p)
    apply SeminormFamily.basisSets_singleton_mem _ 0
    simpa using c_ne
  · /- Show that a neighborhood `s` for `p` is a neighborhood for the topology, by using the
    fact that `p.ball 0 1` is a neighborhood of `0`. Indeed, `s` contains a ball `p.ball 0 r`,
    which contains `c • p.ball 0 1` for some nonzero `c`. The latter set is a neighborhood of zero
    for the topology thanks to the topological vector space assumption. -/
    rcases (FilterBasis.mem_filter_iff _).1 hs with ⟨t, ht, ts⟩
    grw [← ts]
    rcases (SeminormFamily.basisSets_iff _).1 ht with ⟨w, r, r_pos, hw⟩
    rcases eq_or_ne w ∅ with rfl | w_ne
    · simp only [ball, Finset.sup_empty, sub_zero, coe_bot, Pi.zero_apply, r_pos, ofPred_true] at hw
      simp [hw]
    have : t = p.ball 0 r := by
      have : w = Finset.univ := by
        rcases Finset.nonempty_of_ne_empty w_ne with ⟨i, hi⟩
        ext j
        simp only [Subsingleton.elim j i, hi, Finset.mem_univ]
      simpa only [this, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.sup_singleton] using hw
    rw [this]
    obtain ⟨c, c_pos, hc⟩ : exists (c : 𝕜), 0 < ‖c‖ ∧ ‖c‖ < r := exists_norm_lt 𝕜 r_pos
    have c_ne : c != 0 := (by simpa using c_pos)
    have : c • p.ball 0 1 subseteq p.ball 0 r := by
      rw [smul_ball_zero c_ne]
      exact ball_mono (by simpa using hc.le)
    grw [← this]
    simpa using smul_mem_nhds_smul₀ c_ne h

中文:
定理 withSeminorms_iff_mem_nhds_isVonNBounded
  结论: [是拓扑加群 E]
  证明: by
  /- The nontrivial direction is from right to left. With `SeminormFamily.withSeminorms_of_nhds`,
  we need to see that the neighborhoods of zero for the initial topology and for `p` coincide. -/
  refine ⟨fun h => ⟨?_, ?_⟩, ?_⟩
  · apply (h.mem_nhds_iff _ _).2
    exact ⟨Finset.univ, 1, zero_lt_one, by simp⟩
  · apply h.isVonNBounded_iff_seminorm_bounded.2 (fun i => ?_)
    exact ⟨1, zero_lt_one, by simp⟩
  rintro ⟨h, h'⟩
  apply SeminormFamily.withSeminorms_of_nhds
  ext s
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · /- Show that a neighborhood `s` of zero for the topology is a neighborhood for `p`, by using the
    boundedness of `p.ball 0 1`: this ensures that, for some nonzero `c`, we have
    `p.ball 0 1 ⊆ c • s`, and therefore `p.ball 0 (‖c‖⁻¹) ⊆ s`. -/
    obtain ⟨c, hc, c_ne⟩ : exists (c : 𝕜), p.ball 0 1 subseteq c • s ∧ c != 0 :=
      ((h' hs).and (eventually_ne_cobounded 0)).exists
    have : p.ball 0 (‖c⁻¹‖) subseteq s := by
      have : c • p.ball 0 (‖c⁻¹‖) subseteq c • s := by
        simpa [smul_ball_zero c_ne, ← norm_mul, c_ne] using hc
      rwa [smul_set_subset_smul_set_iff₀ c_ne] at this
    grw [← this]
    apply FilterBasis.mem_filter_of_mem
    change p.ball 0 (‖c⁻¹‖) in SeminormFamily.basisSets (fun (i : Fin 1) => p)
    apply SeminormFamily.basisSets_singleton_mem _ 0
    simpa using c_ne
  · /- Show that a neighborhood `s` for `p` is a neighborhood for the topology, by using the
    fact that `p.ball 0 1` is a neighborhood of `0`. Indeed, `s` contains a ball `p.ball 0 r`,
    which contains `c • p.ball 0 1` for some nonzero `c`. The latter set is a neighborhood of zero
    for the topology thanks to the topological vector space assumption. -/
    rcases (FilterBasis.mem_filter_iff _).1 hs with ⟨t, ht, ts⟩
    grw [← ts]
    rcases (SeminormFamily.basisSets_iff _).1 ht with ⟨w, r, r_pos, hw⟩
    rcases eq_or_ne w ∅ with rfl | w_ne
    · simp only [ball, Finset.sup_empty, sub_zero, coe_bot, Pi.zero_apply, r_pos, ofPred_true] at hw
      simp [hw]
    have : t = p.ball 0 r := by
      have : w = Finset.univ := by
        rcases Finset.nonempty_of_ne_empty w_ne with ⟨i, hi⟩
        ext j
        simp only [Subsingleton.elim j i, hi, Finset.mem_univ]
      simpa only [this, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.sup_singleton] using hw
    rw [this]
    obtain ⟨c, c_pos, hc⟩ : exists (c : 𝕜), 0 < ‖c‖ ∧ ‖c‖ < r := exists_norm_lt 𝕜 r_pos
    have c_ne : c != 0 := (by simpa using c_pos)
    have : c • p.ball 0 1 subseteq p.ball 0 r := by
      rw [smul_ball_zero c_ne]
      exact ball_mono (by simpa using hc.le)
    grw [← this]
    simpa using smul_mem_nhds_smul₀ c_ne h
-/
theorem withSeminorms_iff_mem_nhds_isVonNBounded [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} :
    WithSeminorms (fun (_ : Fin 1) => p) ↔ p.ball 0 1 in 𝓝 0 ∧ IsVonNBounded 𝕜 (p.ball 0 1) := by
  /- The nontrivial direction is from right to left. With `SeminormFamily.withSeminorms_of_nhds`,
  we need to see that the neighborhoods of zero for the initial topology and for `p` coincide. -/
  refine ⟨fun h => ⟨?_, ?_⟩, ?_⟩
  · apply (h.mem_nhds_iff _ _).2
    exact ⟨Finset.univ, 1, zero_lt_one, by simp⟩
  · apply h.isVonNBounded_iff_seminorm_bounded.2 (fun i => ?_)
    exact ⟨1, zero_lt_one, by simp⟩
  rintro ⟨h, h'⟩
  apply SeminormFamily.withSeminorms_of_nhds
  ext s
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · /- Show that a neighborhood `s` of zero for the topology is a neighborhood for `p`, by using the
    boundedness of `p.ball 0 1`: this ensures that, for some nonzero `c`, we have
    `p.ball 0 1 ⊆ c • s`, and therefore `p.ball 0 (‖c‖⁻¹) ⊆ s`. -/
    obtain ⟨c, hc, c_ne⟩ : exists (c : 𝕜), p.ball 0 1 subseteq c • s ∧ c != 0 :=
      ((h' hs).and (eventually_ne_cobounded 0)).exists
    have : p.ball 0 (‖c⁻¹‖) subseteq s := by
      have : c • p.ball 0 (‖c⁻¹‖) subseteq c • s := by
        simpa [smul_ball_zero c_ne, ← norm_mul, c_ne] using hc
      rwa [smul_set_subset_smul_set_iff₀ c_ne] at this
    grw [← this]
    apply FilterBasis.mem_filter_of_mem
    change p.ball 0 (‖c⁻¹‖) in SeminormFamily.basisSets (fun (i : Fin 1) => p)
    apply SeminormFamily.basisSets_singleton_mem _ 0
    simpa using c_ne
  · /- Show that a neighborhood `s` for `p` is a neighborhood for the topology, by using the
    fact that `p.ball 0 1` is a neighborhood of `0`. Indeed, `s` contains a ball `p.ball 0 r`,
    which contains `c • p.ball 0 1` for some nonzero `c`. The latter set is a neighborhood of zero
    for the topology thanks to the topological vector space assumption. -/
    rcases (FilterBasis.mem_filter_iff _).1 hs with ⟨t, ht, ts⟩
    grw [← ts]
    rcases (SeminormFamily.basisSets_iff _).1 ht with ⟨w, r, r_pos, hw⟩
    rcases eq_or_ne w ∅ with rfl | w_ne
    · simp only [ball, Finset.sup_empty, sub_zero, coe_bot, Pi.zero_apply, r_pos, ofPred_true] at hw
      simp [hw]
    have : t = p.ball 0 r := by
      have : w = Finset.univ := by
        rcases Finset.nonempty_of_ne_empty w_ne with ⟨i, hi⟩
        ext j
        simp only [Subsingleton.elim j i, hi, Finset.mem_univ]
      simpa only [this, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.sup_singleton] using hw
    rw [this]
    obtain ⟨c, c_pos, hc⟩ : exists (c : 𝕜), 0 < ‖c‖ ∧ ‖c‖ < r := exists_norm_lt 𝕜 r_pos
    have c_ne : c != 0 := (by simpa using c_pos)
    have : c • p.ball 0 1 subseteq p.ball 0 r := by
      rw [smul_ball_zero c_ne]
      exact ball_mono (by simpa using hc.le)
    grw [← this]
    simpa using smul_mem_nhds_smul₀ c_ne h

end NontriviallyNormedField

section continuous_of_bounded

namespace WithSeminorms

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [NormedField 𝕝] [Module 𝕝 E]
variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable [NormedField 𝕝₂] [Module 𝕝₂ F]
variable {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]
variable {τ₁₂ : 𝕝 ->+* 𝕝₂} [RingHomIsometric τ₁₂]

/--
theorem `continuous_of_continuous_comp` / 定理 `continuous_of_continuous_comp`

English:
theorem continuous_of_continuous_comp
  statement: {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E]
  proof: by
  have : IsTopologicalAddGroup F := hq.topologicalAddGroup
  refine continuous_of_continuousAt_zero f ?_
  simp_rw [ContinuousAt, f.map_zero, q.withSeminorms_iff_nhds_eq_iInf.mp hq, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff]
  intro i
  convert! (hf i).continuousAt.tendsto
  exact (map_zero _).symm

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_of_continuous_comp := continuous_of_continuous_comp

中文:
定理 continuous_of_continuous_comp
  结论: {q : SeminormFamily 𝕝₂ F ι'} [拓扑空间 E]
  证明: by
  have : IsTopologicalAddGroup F := hq.topologicalAddGroup
  refine continuous_of_continuousAt_zero f ?_
  simp_rw [ContinuousAt, f.map_zero, q.withSeminorms_iff_nhds_eq_iInf.mp hq, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff]
  intro i
  convert! (hf i).continuousAt.tendsto
  exact (map_zero _).symm

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_of_continuous_comp := continuous_of_continuous_comp

Depends on / 依赖: ContinuousAt, Filter, Filter.tendsto_comap_iff, Filter.tendsto_iInf, IsTopologicalAddGroup, continuousAt, continuousAt.tendsto, continuous_of_continuousAt_zero, convert, f.map_zero, hq.topologicalAddGroup, map_zero, q.withSeminorms_iff_nhds_eq_iInf.mp, simp_rw, tendsto, tendsto_comap_iff, tendsto_iInf, topologicalAddGroup, withSeminorms_iff_nhds_eq_iInf
-/
theorem continuous_of_continuous_comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E]
    [IsTopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q)
    (f : E ->ₛₗ[τ₁₂] F) (hf : forall i, Continuous ((q i).comp f)) : Continuous f := by
  have : IsTopologicalAddGroup F := hq.topologicalAddGroup
  refine continuous_of_continuousAt_zero f ?_
  simp_rw [ContinuousAt, f.map_zero, q.withSeminorms_iff_nhds_eq_iInf.mp hq, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff]
  intro i
  convert! (hf i).continuousAt.tendsto
  exact (map_zero _).symm

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_of_continuous_comp := continuous_of_continuous_comp

/--
theorem `continuous_iff_continuous_comp` / 定理 `continuous_iff_continuous_comp`

English:
theorem continuous_iff_continuous_comp
  statement: {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E]
  proof: ⟨fun h i => (hq.continuous_seminorm i).comp h, continuous_of_continuous_comp hq f⟩

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_iff_continuous_comp := continuous_iff_continuous_comp

中文:
定理 continuous_iff_continuous_comp
  结论: {q : SeminormFamily 𝕝₂ F ι'} [拓扑空间 E]
  证明: ⟨fun h i => (hq.continuous_seminorm i).comp h, continuous_of_continuous_comp hq f⟩

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_iff_continuous_comp := continuous_iff_continuous_comp

Depends on / 依赖: continuous_of_continuous_comp, continuous_seminorm, hq.continuous_seminorm
-/
theorem continuous_iff_continuous_comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E]
    [IsTopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q) (f : E ->ₛₗ[τ₁₂] F) :
    Continuous f ↔ forall i, Continuous ((q i).comp f) :=
  ⟨fun h i => (hq.continuous_seminorm i).comp h, continuous_of_continuous_comp hq f⟩

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_iff_continuous_comp := continuous_iff_continuous_comp

/--
theorem `continuous_of_isBounded` / 定理 `continuous_of_isBounded`

English:
theorem continuous_of_isBounded
  statement: {p : SeminormFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ F ι'}
  proof: by
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  refine continuous_of_continuous_comp hq _ fun i => ?_
  rcases hf i with ⟨s, C, hC⟩
  rw [← finset_sup_smul] at hC
  exact continuous_of_le
    (continuous_finsetSup fun i _ => (hp.continuous_seminorm i).const_smul C) hC

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_from_bounded := continuous_of_isBounded

中文:
定理 continuous_of_isBounded
  结论: {p : SeminormFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ F ι'}
  证明: by
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  refine continuous_of_continuous_comp hq _ fun i => ?_
  rcases hf i with ⟨s, C, hC⟩
  rw [← finset_sup_smul] at hC
  exact continuous_of_le
    (continuous_finsetSup fun i _ => (hp.continuous_seminorm i).const_smul C) hC

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_from_bounded := continuous_of_isBounded

Depends on / 依赖: IsTopologicalAddGroup, const_smul, continuous_finsetSup, continuous_of_continuous_comp, continuous_of_le, continuous_seminorm, finset_sup_smul, hp.continuous_seminorm, hp.topologicalAddGroup, topologicalAddGroup
-/
theorem continuous_of_isBounded {p : SeminormFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ F ι'}
    {_ : TopologicalSpace E} (hp : WithSeminorms p) {_ : TopologicalSpace F} (hq : WithSeminorms q)
    (f : E ->ₛₗ[τ₁₂] F) (hf : Seminorm.IsBounded p q f) : Continuous f := by
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  refine continuous_of_continuous_comp hq _ fun i => ?_
  rcases hf i with ⟨s, C, hC⟩
  rw [← finset_sup_smul] at hC
  exact continuous_of_le
    (continuous_finsetSup fun i _ => (hp.continuous_seminorm i).const_smul C) hC

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_from_bounded := continuous_of_isBounded

/--
theorem `continuous_normedSpace_rng` / 定理 `continuous_normedSpace_rng`

English:
theorem continuous_normedSpace_rng
  statement: (F) [SeminormedAddCommGroup F] [NormedSpace 𝕝₂ F]
  proof: by
  rw [← Seminorm.isBounded_const (Fin 1)] at hf
  exact continuous_of_isBounded hp (norm_withSeminorms 𝕝₂ F) f hf

中文:
定理 continuous_normedSpace_rng
  结论: (F) [SeminormedAddComm群 F] [赋范空间 𝕝₂ F]
  证明: by
  rw [← Seminorm.isBounded_const (Fin 1)] at hf
  exact continuous_of_isBounded hp (norm_withSeminorms 𝕝₂ F) f hf

Depends on / 依赖: Seminorm, Seminorm.isBounded_const, continuous_of_isBounded, isBounded_const, norm_withSeminorms
-/
theorem continuous_normedSpace_rng (F) [SeminormedAddCommGroup F] [NormedSpace 𝕝₂ F]
    [TopologicalSpace E] {p : ι -> Seminorm 𝕝 E} (hp : WithSeminorms p)
    (f : E ->ₛₗ[τ₁₂] F) (hf : exists (s : Finset ι) (C : Real>=0), (normSeminorm 𝕝₂ F).comp f <= C • s.sup p) :
    Continuous f := by
  rw [← Seminorm.isBounded_const (Fin 1)] at hf
  exact continuous_of_isBounded hp (norm_withSeminorms 𝕝₂ F) f hf

/--
lemma `_root_.Seminorm.abs_le_of_le` / 引理 `_root_.Seminorm.abs_le_of_le`

English:
lemma _root_.Seminorm.abs_le_of_le
  statement: [Module Real E] {p : Seminorm Real E}
  proof: abs_le.2 ⟨neg_le.1 (by simpa using hfp (-x)), hfp x⟩

中文:
引理 _root_.半范数.abs_le_of_le
  结论: [模 实数 E] {p : 半范数 实数 E}
  证明: abs_le.2 ⟨neg_le.1 (by simpa using hfp (-x)), hfp x⟩

Depends on / 依赖: abs_le, neg_le
-/
lemma _root_.Seminorm.abs_le_of_le [Module Real E] {p : Seminorm Real E}
    {f : E ->ₗ[Real] Real} (hfp : forall x, f x <= p x) (x : E) :
    |f x| <= p x :=
  abs_le.2 ⟨neg_le.1 (by simpa using hfp (-x)), hfp x⟩

/--
theorem `continuous_real_rng` / 定理 `continuous_real_rng`

English:
theorem continuous_real_rng
  statement: [Module Real E] [TopologicalSpace E] {p : ι -> Seminorm Real E}
  proof: by
  obtain ⟨s, C, hC⟩ := hf
  exact continuous_normedSpace_rng Real hp f ⟨s, C, abs_le_of_le hC⟩

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.cont_withSeminorms_normedSpace := continuous_normedSpace_rng

中文:
定理 continuous_real_rng
  结论: [模 实数 E] [拓扑空间 E] {p : ι -> 半范数 实数 E}
  证明: by
  obtain ⟨s, C, hC⟩ := hf
  exact continuous_normedSpace_rng Real hp f ⟨s, C, abs_le_of_le hC⟩

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.cont_withSeminorms_normedSpace := continuous_normedSpace_rng

Depends on / 依赖: abs_le_of_le, continuous_normedSpace_rng
-/
theorem continuous_real_rng [Module Real E] [TopologicalSpace E] {p : ι -> Seminorm Real E}
    (hp : WithSeminorms p) (f : E ->ₗ[Real] Real)
    (hf : exists (s : Finset ι) (C : Real>=0), forall x, f x <= (C • s.sup p) x) :
    Continuous f := by
  obtain ⟨s, C, hC⟩ := hf
  exact continuous_normedSpace_rng Real hp f ⟨s, C, abs_le_of_le hC⟩

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.cont_withSeminorms_normedSpace := continuous_normedSpace_rng

/--
theorem `continuous_normedSpace_dom` / 定理 `continuous_normedSpace_dom`

English:
theorem continuous_normedSpace_dom
  statement: (E) [SeminormedAddCommGroup E] [NormedSpace 𝕝 E]
  proof: by
  rw [← Seminorm.const_isBounded (Fin 1)] at hf
  exact continuous_of_isBounded (norm_withSeminorms 𝕝 E) hq f hf

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.cont_normedSpace_to_withSeminorms := continuous_normedSpace_dom

中文:
定理 continuous_normedSpace_dom
  结论: (E) [SeminormedAddComm群 E] [赋范空间 𝕝 E]
  证明: by
  rw [← Seminorm.const_isBounded (Fin 1)] at hf
  exact continuous_of_isBounded (norm_withSeminorms 𝕝 E) hq f hf

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.cont_normedSpace_to_withSeminorms := continuous_normedSpace_dom

Depends on / 依赖: Seminorm, Seminorm.const_isBounded, const_isBounded, continuous_of_isBounded, norm_withSeminorms
-/
theorem continuous_normedSpace_dom (E) [SeminormedAddCommGroup E] [NormedSpace 𝕝 E]
    [TopologicalSpace F] {q : ι -> Seminorm 𝕝₂ F} (hq : WithSeminorms q)
    (f : E ->ₛₗ[τ₁₂] F) (hf : forall i : ι, exists C : Real>=0, (q i).comp f <= C • normSeminorm 𝕝 E) :
    Continuous f := by
  rw [← Seminorm.const_isBounded (Fin 1)] at hf
  exact continuous_of_isBounded (norm_withSeminorms 𝕝 E) hq f hf

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.cont_normedSpace_to_withSeminorms := continuous_normedSpace_dom

/--
theorem `equicontinuous_TFAE` / 定理 `equicontinuous_TFAE`

English:
theorem equicontinuous_TFAE
  statement: {κ : Type*}
  proof: by
  -- We start by reducing to the case where the target is a seminormed space
  rw [q.withSeminorms_iff_uniformSpace_eq_iInf.mp hq]; rw [uniformEquicontinuous_iInf_rng]; rw [equicontinuous_iInf_rng]; rw [equicontinuousAt_iInf_rng]
  refine forall_tfae [_, _, _, _, _] fun i => ?_
  let _ : SeminormedAddCommGroup F := (q i).toSeminormedAddCommGroup
  clear u hu hq
  -- Now we can prove the equivalence in this setting
  simp only [List.map]
  tfae_have 1 -> 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 -> 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 -> 1 := fun H => H 0
  tfae_have 3 -> 5
  | H => by
    have : forallᶠ x in 𝓝 0, forall k, q i (f k x) <= 1 := by
      filter_upwards [Metric.equicontinuousAt_iff_right.mp (H.equicontinuous 0) 1 one_pos]
        with x hx k
      simpa using! (hx k).le
    have bdd : BddAbove (range fun k => (q i).comp (f k)) :=
      Seminorm.bddAbove_of_absorbent (absorbent_nhds_zero this)
        (fun x hx => ⟨1, forall_mem_range.mpr hx⟩)
    rw [← Seminorm.coe_iSup_eq bdd]
    refine ⟨bdd, Seminorm.continuous' (r := 1) ?_⟩
    filter_upwards [this] with x hx
    simpa only [closedBall_iSup bdd _ one_pos, mem_iInter, mem_closedBall_zero] using! hx
  tfae_have 5 -> 4 := fun H => ⟨⨆ k, (q i).comp (f k), Seminorm.coe_iSup_eq H.1 ▸ H.2, le_ciSup H.1⟩
  tfae_have 4 -> 1 -- This would work over any `NormedField`
  | ⟨p, hp, hfp⟩ =>
Metric.equicontinuousAt_of_continuity_modulus p (map_zero p ▸ hp.tendsto 0) _
      Eventually.of_forall fun x k => by simpa using! hfp k x
  tfae_finish

中文:
定理 equicontinuous_TFAE
  结论: {κ : 类型}
  证明: by
  -- We start by reducing to the case where the target is a seminormed space
  rw [q.withSeminorms_iff_uniformSpace_eq_iInf.mp hq]; rw [uniformEquicontinuous_iInf_rng]; rw [equicontinuous_iInf_rng]; rw [equicontinuousAt_iInf_rng]
  refine forall_tfae [_, _, _, _, _] fun i => ?_
  let _ : SeminormedAddCommGroup F := (q i).toSeminormedAddCommGroup
  clear u hu hq
  -- Now we can prove the equivalence in this setting
  simp only [List.map]
  tfae_have 1 -> 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 -> 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 -> 1 := fun H => H 0
  tfae_have 3 -> 5
  | H => by
    have : forallᶠ x in 𝓝 0, forall k, q i (f k x) <= 1 := by
      filter_upwards [Metric.equicontinuousAt_iff_right.mp (H.equicontinuous 0) 1 one_pos]
        with x hx k
      simpa using! (hx k).le
    have bdd : BddAbove (range fun k => (q i).comp (f k)) :=
      Seminorm.bddAbove_of_absorbent (absorbent_nhds_zero this)
        (fun x hx => ⟨1, forall_mem_range.mpr hx⟩)
    rw [← Seminorm.coe_iSup_eq bdd]
    refine ⟨bdd, Seminorm.continuous' (r := 1) ?_⟩
    filter_upwards [this] with x hx
    simpa only [closedBall_iSup bdd _ one_pos, mem_iInter, mem_closedBall_zero] using! hx
  tfae_have 5 -> 4 := fun H => ⟨⨆ k, (q i).comp (f k), Seminorm.coe_iSup_eq H.1 ▸ H.2, le_ciSup H.1⟩
  tfae_have 4 -> 1 -- This would work over any `NormedField`
  | ⟨p, hp, hfp⟩ =>
Metric.equicontinuousAt_of_continuity_modulus p (map_zero p ▸ hp.tendsto 0) _
      Eventually.of_forall fun x k => by simpa using! hfp k x
  tfae_finish
-/
protected theorem equicontinuous_TFAE {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [IsUniformAddGroup E] [u : UniformSpace F]
    [hu : IsUniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ -> E ->ₛₗ[σ₁₂] F) : TFAE
    [ EquicontinuousAt ((↑) ∘ f) 0,
      Equicontinuous ((↑) ∘ f),
      UniformEquicontinuous ((↑) ∘ f),
      forall i, exists p : Seminorm 𝕜 E, Continuous p ∧ forall k, (q i).comp (f k) <= p,
      forall i, BddAbove (range fun k => (q i).comp (f k)) ∧ Continuous (⨆ k, (q i).comp (f k)) ] := by
  -- We start by reducing to the case where the target is a seminormed space
  rw [q.withSeminorms_iff_uniformSpace_eq_iInf.mp hq]; rw [uniformEquicontinuous_iInf_rng]; rw [equicontinuous_iInf_rng]; rw [equicontinuousAt_iInf_rng]
  refine forall_tfae [_, _, _, _, _] fun i => ?_
  let _ : SeminormedAddCommGroup F := (q i).toSeminormedAddCommGroup
  clear u hu hq
  -- Now we can prove the equivalence in this setting
  simp only [List.map]
  tfae_have 1 -> 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 -> 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 -> 1 := fun H => H 0
  tfae_have 3 -> 5
  | H => by
    have : forallᶠ x in 𝓝 0, forall k, q i (f k x) <= 1 := by
      filter_upwards [Metric.equicontinuousAt_iff_right.mp (H.equicontinuous 0) 1 one_pos]
        with x hx k
      simpa using! (hx k).le
    have bdd : BddAbove (range fun k => (q i).comp (f k)) :=
      Seminorm.bddAbove_of_absorbent (absorbent_nhds_zero this)
        (fun x hx => ⟨1, forall_mem_range.mpr hx⟩)
    rw [← Seminorm.coe_iSup_eq bdd]
    refine ⟨bdd, Seminorm.continuous' (r := 1) ?_⟩
    filter_upwards [this] with x hx
    simpa only [closedBall_iSup bdd _ one_pos, mem_iInter, mem_closedBall_zero] using! hx
  tfae_have 5 -> 4 := fun H => ⟨⨆ k, (q i).comp (f k), Seminorm.coe_iSup_eq H.1 ▸ H.2, le_ciSup H.1⟩
  tfae_have 4 -> 1 -- This would work over any `NormedField`
  | ⟨p, hp, hfp⟩ =>
Metric.equicontinuousAt_of_continuity_modulus p (map_zero p ▸ hp.tendsto 0) _
      Eventually.of_forall fun x k => by simpa using! hfp k x
  tfae_finish

/--
theorem `uniformEquicontinuous_iff_exists_continuous_seminorm` / 定理 `uniformEquicontinuous_iff_exists_continuous_seminorm`

English:
theorem uniformEquicontinuous_iff_exists_continuous_seminorm
  statement: {κ : Type*}
  proof: (hq.equicontinuous_TFAE f).out 2 3

中文:
定理 uniformEquicontinuous_iff_存在_continuous_seminorm
  结论: {κ : 类型}
  证明: (hq.equicontinuous_TFAE f).out 2 3

Depends on / 依赖: equicontinuous_TFAE, hq.equicontinuous_TFAE
-/
theorem uniformEquicontinuous_iff_exists_continuous_seminorm {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [IsUniformAddGroup E] [u : UniformSpace F]
    [IsUniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ -> E ->ₛₗ[σ₁₂] F) :
    UniformEquicontinuous ((↑) ∘ f) ↔
    forall i, exists p : Seminorm 𝕜 E, Continuous p ∧ forall k, (q i).comp (f k) <= p :=
  (hq.equicontinuous_TFAE f).out 2 3

/--
theorem `uniformEquicontinuous_iff_bddAbove_and_continuous_iSup` / 定理 `uniformEquicontinuous_iff_bddAbove_and_continuous_iSup`

English:
theorem uniformEquicontinuous_iff_bddAbove_and_continuous_iSup
  statement: {κ : Type*}
  proof: (hq.equicontinuous_TFAE f).out 2 4

中文:
定理 uniformEquicontinuous_iff_bddAbove_and_continuous_iSup
  结论: {κ : 类型}
  证明: (hq.equicontinuous_TFAE f).out 2 4

Depends on / 依赖: equicontinuous_TFAE, hq.equicontinuous_TFAE
-/
theorem uniformEquicontinuous_iff_bddAbove_and_continuous_iSup {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [IsUniformAddGroup E] [u : UniformSpace F]
    [IsUniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ -> E ->ₛₗ[σ₁₂] F) :
    UniformEquicontinuous ((↑) ∘ f) ↔ forall i,
    BddAbove (range fun k => (q i).comp (f k)) ∧
      Continuous (⨆ k, (q i).comp (f k)) :=
  (hq.equicontinuous_TFAE f).out 2 4

end WithSeminorms

section Congr

namespace WithSeminorms

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [SeminormedRing 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'}
  proof: by
  constructor
  rw [hp.topology_eq_withSeminorms]
  clear hp t
  refine le_antisymm ?_ ?_ <;>
  rw [← continuous_id_iff_le] <;>
  refine continuous_of_isBounded (.mk (topology := _) rfl) (.mk (topology := _) rfl)
    LinearMap.id (by assumption)

中文:
定理 congr
  结论: {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'}
  证明: by
  constructor
  rw [hp.topology_eq_withSeminorms]
  clear hp t
  refine le_antisymm ?_ ?_ <;>
  rw [← continuous_id_iff_le] <;>
  refine continuous_of_isBounded (.mk (topology := _) rfl) (.mk (topology := _) rfl)
    LinearMap.id (by assumption)
-/
protected theorem congr {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'}
    [t : TopologicalSpace E] (hp : WithSeminorms p) (hpq : Seminorm.IsBounded p q LinearMap.id)
    (hqp : Seminorm.IsBounded q p LinearMap.id) : WithSeminorms q := by
  constructor
  rw [hp.topology_eq_withSeminorms]
  clear hp t
  refine le_antisymm ?_ ?_ <;>
  rw [← continuous_id_iff_le] <;>
  refine continuous_of_isBounded (.mk (topology := _) rfl) (.mk (topology := _) rfl)
    LinearMap.id (by assumption)

/--
theorem `finset_sups` / 定理 `finset_sups`

English:
theorem finset_sups
  statement: {p : SeminormFamily 𝕜 E ι} [TopologicalSpace E]
  proof: by
  refine hp.congr ?_ ?_
  · intro s
    refine ⟨s, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{{i}}, 1, ?_⟩
    rw [Finset.sup_singleton]; rw [Finset.sup_singleton]; rw [one_smul]
    rfl

中文:
定理 finset_sups
  结论: {p : SeminormFamily 𝕜 E ι} [拓扑空间 E]
  证明: by
  refine hp.congr ?_ ?_
  · intro s
    refine ⟨s, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{{i}}, 1, ?_⟩
    rw [Finset.sup_singleton]; rw [Finset.sup_singleton]; rw [one_smul]
    rfl
-/
protected theorem finset_sups {p : SeminormFamily 𝕜 E ι} [TopologicalSpace E]
    (hp : WithSeminorms p) : WithSeminorms (fun s : Finset ι => s.sup p) := by
  refine hp.congr ?_ ?_
  · intro s
    refine ⟨s, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{{i}}, 1, ?_⟩
    rw [Finset.sup_singleton]; rw [Finset.sup_singleton]; rw [one_smul]
    rfl

/--
theorem `partial_sups` / 定理 `partial_sups`

English:
theorem partial_sups
  statement: [Preorder ι] [LocallyFiniteOrderBot ι] {p : SeminormFamily 𝕜 E ι}
  proof: by
  refine hp.congr ?_ ?_
  · intro i
    refine ⟨Finset.Iic i, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{i}, 1, ?_⟩
    rw [Finset.sup_singleton]; rw [one_smul]
    exact (Finset.le_sup (Finset.mem_Iic.mpr le_rfl) : p i <= (Finset.Iic i).sup p)

中文:
定理 partial_sups
  结论: [预序 ι] [LocallyFiniteOrderBot ι] {p : SeminormFamily 𝕜 E ι}
  证明: by
  refine hp.congr ?_ ?_
  · intro i
    refine ⟨Finset.Iic i, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{i}, 1, ?_⟩
    rw [Finset.sup_singleton]; rw [one_smul]
    exact (Finset.le_sup (Finset.mem_Iic.mpr le_rfl) : p i <= (Finset.Iic i).sup p)
-/
protected theorem partial_sups [Preorder ι] [LocallyFiniteOrderBot ι] {p : SeminormFamily 𝕜 E ι}
    [TopologicalSpace E] (hp : WithSeminorms p) : WithSeminorms (fun i => (Finset.Iic i).sup p) := by
  refine hp.congr ?_ ?_
  · intro i
    refine ⟨Finset.Iic i, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{i}, 1, ?_⟩
    rw [Finset.sup_singleton]; rw [one_smul]
    exact (Finset.le_sup (Finset.mem_Iic.mpr le_rfl) : p i <= (Finset.Iic i).sup p)

/--
theorem `congr_equiv` / 定理 `congr_equiv`

English:
theorem congr_equiv
  statement: {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
  proof: by
  refine hp.congr ?_ ?_ <;>
  intro i <;>
  [use {e i}, 1; use {e.symm i}, 1] <;>
  simp

中文:
定理 congr_equiv
  结论: {p : SeminormFamily 𝕜 E ι} [t : 拓扑空间 E]
  证明: by
  refine hp.congr ?_ ?_ <;>
  intro i <;>
  [use {e i}, 1; use {e.symm i}, 1] <;>
  simp
-/
protected theorem congr_equiv {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) (e : ι' ≃ ι) : WithSeminorms (p ∘ e) := by
  refine hp.congr ?_ ?_ <;>
  intro i <;>
  [use {e i}, 1; use {e.symm i}, 1] <;>
  simp

end WithSeminorms

end Congr

end continuous_of_bounded

section bounded_of_continuous

namespace Seminorm

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : SeminormFamily 𝕜 E ι}

/--
lemma `map_eq_zero_of_norm_eq_zero` / 引理 `map_eq_zero_of_norm_eq_zero`

English:
lemma map_eq_zero_of_norm_eq_zero
  statement: (q : Seminorm 𝕜 F)
  proof: (map_zero q) ▸
    ((specializes_iff_mem_closure.mpr <| mem_closure_zero_iff_norm.mpr hx).map hq).eq.symm

中文:
引理 map_eq_zero_of_norm_eq_zero
  结论: (q : 半范数 𝕜 F)
  证明: (map_zero q) ▸
    ((specializes_iff_mem_closure.mpr <| mem_closure_zero_iff_norm.mpr hx).map hq).eq.symm

Depends on / 依赖: eq.symm, map_zero, mem_closure_zero_iff_norm, mem_closure_zero_iff_norm.mpr, specializes_iff_mem_closure, specializes_iff_mem_closure.mpr
-/
lemma map_eq_zero_of_norm_eq_zero (q : Seminorm 𝕜 F)
    (hq : Continuous q) {x : F} (hx : ‖x‖ = 0) : q x = 0 :=
  (map_zero q) ▸
    ((specializes_iff_mem_closure.mpr <| mem_closure_zero_iff_norm.mpr hx).map hq).eq.symm

/--
lemma `bound_of_continuous_normedSpace` / 引理 `bound_of_continuous_normedSpace`

English:
lemma bound_of_continuous_normedSpace
  statement: (q : Seminorm 𝕜 F)
  proof: by
  have hq' : Tendsto q (𝓝 0) (𝓝 0) := map_zero q ▸ hq.tendsto 0
  rcases NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hq' <| Iio_mem_nhds one_pos)
    with ⟨ε, ε_pos, hε⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < ‖c‖ / ε := by positivity
  refine ⟨‖c‖ / ε, this, fun x => ?_⟩
  by_cases hx : ‖x‖ = 0
  · rw [hx, mul_zero]
    exact le_of_eq (map_eq_zero_of_norm_eq_zero q hq hx)
  · refine (normSeminorm 𝕜 F).bound_of_shell q ε_pos hc (fun x hle hlt => ?_) hx
    refine (le_of_lt <| show q x < _ from hε hlt).trans ?_
    rwa [← div_le_iff₀' this, one_div_div]

中文:
引理 bound_of_continuous_normedSpace
  结论: (q : 半范数 𝕜 F)
  证明: by
  have hq' : Tendsto q (𝓝 0) (𝓝 0) := map_zero q ▸ hq.tendsto 0
  rcases NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hq' <| Iio_mem_nhds one_pos)
    with ⟨ε, ε_pos, hε⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < ‖c‖ / ε := by positivity
  refine ⟨‖c‖ / ε, this, fun x => ?_⟩
  by_cases hx : ‖x‖ = 0
  · rw [hx, mul_zero]
    exact le_of_eq (map_eq_zero_of_norm_eq_zero q hq hx)
  · refine (normSeminorm 𝕜 F).bound_of_shell q ε_pos hc (fun x hle hlt => ?_) hx
    refine (le_of_lt <| show q x < _ from hε hlt).trans ?_
    rwa [← div_le_iff₀' this, one_div_div]

Depends on / 依赖: Iio_mem_nhds, NormedAddGroup, NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp, NormedField, NormedField.exists_one_lt_norm, Tendsto, bound_of_shell, exists_one_lt_norm, hq.tendsto, le_of_eq, le_of_lt, map_eq_zero_of_norm_eq_zero, map_zero, mem_iff, mul_zero, nhds_zero_basis_norm_lt, normSeminorm, one_pos, tendsto
-/
lemma bound_of_continuous_normedSpace (q : Seminorm 𝕜 F)
    (hq : Continuous q) : exists C, 0 < C ∧ (forall x : F, q x <= C * ‖x‖) := by
  have hq' : Tendsto q (𝓝 0) (𝓝 0) := map_zero q ▸ hq.tendsto 0
  rcases NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hq' <| Iio_mem_nhds one_pos)
    with ⟨ε, ε_pos, hε⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < ‖c‖ / ε := by positivity
  refine ⟨‖c‖ / ε, this, fun x => ?_⟩
  by_cases hx : ‖x‖ = 0
  · rw [hx, mul_zero]
    exact le_of_eq (map_eq_zero_of_norm_eq_zero q hq hx)
  · refine (normSeminorm 𝕜 F).bound_of_shell q ε_pos hc (fun x hle hlt => ?_) hx
    refine (le_of_lt <| show q x < _ from hε hlt).trans ?_
    rwa [← div_le_iff₀' this, one_div_div]

/--
lemma `bound_of_continuous` / 引理 `bound_of_continuous`

English:
lemma bound_of_continuous
  statement: [t : TopologicalSpace E] (hp : WithSeminorms p)
  proof: by
  -- The continuity of `q` gives us a finset `s` and a real `ε > 0`
  -- such that `hε : (s.sup p).ball 0 ε ⊆ q.ball 0 1`.
  rcases hp.hasBasis.mem_iff.mp (ball_mem_nhds hq one_pos) with ⟨V, hV, hε⟩
  rcases p.basisSets_iff.mp hV with ⟨s, ε, ε_pos, rfl⟩
  -- Now forget that `E` already had a topology and view it as the (semi)normed space
  -- `(E, s.sup p)`.
  clear hp hq t
  let _ : SeminormedAddCommGroup E := (s.sup p).toSeminormedAddCommGroup
  let _ : NormedSpace 𝕜 E := { norm_smul_le := fun a b => le_of_eq (map_smul_eq_mul (s.sup p) a b) }
  -- The inclusion `hε` tells us exactly that `q` is *still* continuous for this new topology
  have : Continuous q := by
    apply Seminorm.continuous (r := 1) (mem_of_superset (Metric.ball_mem_nhds _ ε_pos) ?_)
    rw [← ball_eq_metric]
    exact hε
  -- Hence we can conclude by applying `bound_of_continuous_normedSpace`.
  rcases bound_of_continuous_normedSpace q this with ⟨C, C_pos, hC⟩
  exact ⟨s, ⟨C, C_pos.le⟩, fun H => C_pos.ne.symm (congr_arg NNReal.toReal H), hC⟩
  -- Note that the key ingredient for this proof is that, by scaling arguments hidden in
  -- `Seminorm.continuous`, we only have to look at the `q`-ball of radius one, and the `s` we get
  -- from that will automatically work for all other radii.

中文:
引理 bound_of_continuous
  结论: [t : 拓扑空间 E] (hp : WithSeminorms p)
  证明: by
  -- The continuity of `q` gives us a finset `s` and a real `ε > 0`
  -- such that `hε : (s.sup p).ball 0 ε ⊆ q.ball 0 1`.
  rcases hp.hasBasis.mem_iff.mp (ball_mem_nhds hq one_pos) with ⟨V, hV, hε⟩
  rcases p.basisSets_iff.mp hV with ⟨s, ε, ε_pos, rfl⟩
  -- Now forget that `E` already had a topology and view it as the (semi)normed space
  -- `(E, s.sup p)`.
  clear hp hq t
  let _ : SeminormedAddCommGroup E := (s.sup p).toSeminormedAddCommGroup
  let _ : NormedSpace 𝕜 E := { norm_smul_le := fun a b => le_of_eq (map_smul_eq_mul (s.sup p) a b) }
  -- The inclusion `hε` tells us exactly that `q` is *still* continuous for this new topology
  have : Continuous q := by
    apply Seminorm.continuous (r := 1) (mem_of_superset (Metric.ball_mem_nhds _ ε_pos) ?_)
    rw [← ball_eq_metric]
    exact hε
  -- Hence we can conclude by applying `bound_of_continuous_normedSpace`.
  rcases bound_of_continuous_normedSpace q this with ⟨C, C_pos, hC⟩
  exact ⟨s, ⟨C, C_pos.le⟩, fun H => C_pos.ne.symm (congr_arg NNReal.toReal H), hC⟩
  -- Note that the key ingredient for this proof is that, by scaling arguments hidden in
  -- `Seminorm.continuous`, we only have to look at the `q`-ball of radius one, and the `s` we get
  -- from that will automatically work for all other radii.
-/
lemma bound_of_continuous [t : TopologicalSpace E] (hp : WithSeminorms p)
    (q : Seminorm 𝕜 E) (hq : Continuous q) :
    exists s : Finset ι, exists C : Real>=0, C != 0 ∧ q <= C • s.sup p := by
  -- The continuity of `q` gives us a finset `s` and a real `ε > 0`
  -- such that `hε : (s.sup p).ball 0 ε ⊆ q.ball 0 1`.
  rcases hp.hasBasis.mem_iff.mp (ball_mem_nhds hq one_pos) with ⟨V, hV, hε⟩
  rcases p.basisSets_iff.mp hV with ⟨s, ε, ε_pos, rfl⟩
  -- Now forget that `E` already had a topology and view it as the (semi)normed space
  -- `(E, s.sup p)`.
  clear hp hq t
  let _ : SeminormedAddCommGroup E := (s.sup p).toSeminormedAddCommGroup
  let _ : NormedSpace 𝕜 E := { norm_smul_le := fun a b => le_of_eq (map_smul_eq_mul (s.sup p) a b) }
  -- The inclusion `hε` tells us exactly that `q` is *still* continuous for this new topology
  have : Continuous q := by
    apply Seminorm.continuous (r := 1) (mem_of_superset (Metric.ball_mem_nhds _ ε_pos) ?_)
    rw [← ball_eq_metric]
    exact hε
  -- Hence we can conclude by applying `bound_of_continuous_normedSpace`.
  rcases bound_of_continuous_normedSpace q this with ⟨C, C_pos, hC⟩
  exact ⟨s, ⟨C, C_pos.le⟩, fun H => C_pos.ne.symm (congr_arg NNReal.toReal H), hC⟩
  -- Note that the key ingredient for this proof is that, by scaling arguments hidden in
  -- `Seminorm.continuous`, we only have to look at the `q`-ball of radius one, and the `s` we get
  -- from that will automatically work for all other radii.

end Seminorm

end bounded_of_continuous

section LocallyConvexSpace

open LocallyConvexSpace

variable [NormedField 𝕜] [NormedSpace Real 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module Real E]
  [IsScalarTower Real 𝕜 E] [TopologicalSpace E]

/--
theorem `WithSeminorms.toLocallyConvexSpace` / 定理 `WithSeminorms.toLocallyConvexSpace`

English:
theorem WithSeminorms.toLocallyConvexSpace
  given: {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
  proof: by
  have := hp.topologicalAddGroup
  apply ofBasisZero Real E id fun s => s in p.basisSets
  · rw [hp.1, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    exact FilterBasis.hasBasis _
  · intro s hs
    change s in Set.iUnion _ at hs
    simp_rw [Set.mem_iUnion, Set.mem_singleton_iff] at hs
    rcases hs with ⟨I, r, _, rfl⟩
    exact convex_ball _ _ _

中文:
定理 WithSeminorms.toLocallyConvexSpace
  条件: {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
  证明: by
  have := hp.topologicalAddGroup
  apply ofBasisZero Real E id fun s => s in p.basisSets
  · rw [hp.1, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    exact FilterBasis.hasBasis _
  · intro s hs
    change s in Set.iUnion _ at hs
    simp_rw [Set.mem_iUnion, Set.mem_singleton_iff] at hs
    rcases hs with ⟨I, r, _, rfl⟩
    exact convex_ball _ _ _

Depends on / 依赖: AddGroupFilterBasis, AddGroupFilterBasis.N_zero, AddGroupFilterBasis.nhds_eq, FilterBasis, FilterBasis.hasBasis, N_zero, Set.iUnion, Set.mem_iUnion, Set.mem_singleton_iff, basisSets, convex_ball, hasBasis, hp.topologicalAddGroup, iUnion, mem_iUnion, mem_singleton_iff, nhds_eq, ofBasisZero, p.basisSets, simp_rw
-/
theorem WithSeminorms.toLocallyConvexSpace {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    LocallyConvexSpace Real E := by
  have := hp.topologicalAddGroup
  apply ofBasisZero Real E id fun s => s in p.basisSets
  · rw [hp.1, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    exact FilterBasis.hasBasis _
  · intro s hs
    change s in Set.iUnion _ at hs
    simp_rw [Set.mem_iUnion, Set.mem_singleton_iff] at hs
    rcases hs with ⟨I, r, _, rfl⟩
    exact convex_ball _ _ _

/-- A `PolynormableSpace` over `ℝ` is locally convex.

TODO: generalize to `RCLike`. -/
instance (priority := low) [PolynormableSpace Real E] : LocallyConvexSpace Real E :=
.toLocallyConvexSpace PolynormableSpace.withSeminorms Real E

end LocallyConvexSpace

section NormedSpace

variable (𝕜) [NormedField 𝕜] [NormedSpace Real 𝕜] [SeminormedAddCommGroup E]

/--
theorem `NormedSpace.toLocallyConvexSpace'` / 定理 `NormedSpace.toLocallyConvexSpace'`

English:
theorem NormedSpace.toLocallyConvexSpace'
  given: [NormedSpace 𝕜 E] [Module Real E] [IsScalarTower Real 𝕜 E]
  proof: (norm_withSeminorms 𝕜 E).toLocallyConvexSpace

中文:
定理 赋范空间.toLocallyConvexSpace'
  条件: [赋范空间 𝕜 E] [模 实数 E] [标量塔 实数 𝕜 E]
  证明: (norm_withSeminorms 𝕜 E).toLocallyConvexSpace

Depends on / 依赖: norm_withSeminorms, toLocallyConvexSpace
-/
theorem NormedSpace.toLocallyConvexSpace' [NormedSpace 𝕜 E] [Module Real E] [IsScalarTower Real 𝕜 E] :
    LocallyConvexSpace Real E :=
  (norm_withSeminorms 𝕜 E).toLocallyConvexSpace

/--
Instance `NormedSpace.toLocallyConvexSpace` / 实例 `NormedSpace.toLocallyConvexSpace`

English:
instance NormedSpace.toLocallyConvexSpace
  signature: [NormedSpace Real E]
  body: NormedSpace.toLocallyConvexSpace' Real

中文:
实例 赋范空间.toLocallyConvexSpace
  签名: [赋范空间 实数 E]
  定义体: NormedSpace.toLocallyConvexSpace' Real

Depends on / 依赖: NormedSpace, NormedSpace.toLocallyConvexSpace, toLocallyConvexSpace
-/
instance NormedSpace.toLocallyConvexSpace [NormedSpace Real E] : LocallyConvexSpace Real E :=
  NormedSpace.toLocallyConvexSpace' Real

end NormedSpace

section TopologicalConstructions

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]

/--
Definition of `SeminormFamily.comp` / `SeminormFamily.comp` 的定义

English:
definition SeminormFamily.comp
  signature: (q : SeminormFamily 𝕜₂ F ι) (f : E ->ₛₗ[σ₁₂] F)
  body: fun i => (q i).comp f

中文:
定义 SeminormFamily.comp
  签名: (q : SeminormFamily 𝕜₂ F ι) (f : E ->ₛₗ[σ₁₂] F)
  定义体: fun i => (q i).comp f
-/
def SeminormFamily.comp (q : SeminormFamily 𝕜₂ F ι) (f : E ->ₛₗ[σ₁₂] F) : SeminormFamily 𝕜 E ι :=
  fun i => (q i).comp f

/--
theorem `SeminormFamily.comp_apply` / 定理 `SeminormFamily.comp_apply`

English:
theorem SeminormFamily.comp_apply
  given: (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E ->ₛₗ[σ₁₂] F)
  proof: rfl

中文:
定理 SeminormFamily.comp_apply
  条件: (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E ->ₛₗ[σ₁₂] F)
  证明: rfl
-/
theorem SeminormFamily.comp_apply (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E ->ₛₗ[σ₁₂] F) :
    q.comp f i = (q i).comp f :=
  rfl

/--
theorem `SeminormFamily.comp_smul_nnreal` / 定理 `SeminormFamily.comp_smul_nnreal`

English:
theorem SeminormFamily.comp_smul_nnreal
  statement: (q : SeminormFamily 𝕜₂ F ι) (c : NNReal)
  proof: by
  ext
  simp [SeminormFamily.comp_apply, Seminorm.comp_apply]

中文:
定理 SeminormFamily.comp_smul_nnreal
  结论: (q : SeminormFamily 𝕜₂ F ι) (c : 非负实数)
  证明: by
  ext
  simp [SeminormFamily.comp_apply, Seminorm.comp_apply]

Depends on / 依赖: Seminorm, Seminorm.comp_apply, SeminormFamily, SeminormFamily.comp_apply, comp_apply
-/
theorem SeminormFamily.comp_smul_nnreal (q : SeminormFamily 𝕜₂ F ι) (c : NNReal)
    (f : E ->ₛₗ[σ₁₂] F) :
    c • q.comp f = (c • q).comp f := by
  ext
  simp [SeminormFamily.comp_apply, Seminorm.comp_apply]

/--
theorem `SeminormFamily.finset_sup_comp` / 定理 `SeminormFamily.finset_sup_comp`

English:
theorem SeminormFamily.finset_sup_comp
  statement: (q : SeminormFamily 𝕜₂ F ι) (s : Finset ι)
  proof: by
  ext x
  rw [Seminorm.comp_apply]; rw [Seminorm.finset_sup_apply]; rw [Seminorm.finset_sup_apply]
  rfl

中文:
定理 SeminormFamily.finset_sup_comp
  结论: (q : SeminormFamily 𝕜₂ F ι) (s : 有限集 ι)
  证明: by
  ext x
  rw [Seminorm.comp_apply]; rw [Seminorm.finset_sup_apply]; rw [Seminorm.finset_sup_apply]
  rfl

Depends on / 依赖: Seminorm, Seminorm.comp_apply, Seminorm.finset_sup_apply, comp_apply, finset_sup_apply
-/
theorem SeminormFamily.finset_sup_comp (q : SeminormFamily 𝕜₂ F ι) (s : Finset ι)
    (f : E ->ₛₗ[σ₁₂] F) : (s.sup q).comp f = s.sup (q.comp f) := by
  ext x
  rw [Seminorm.comp_apply]; rw [Seminorm.finset_sup_apply]; rw [Seminorm.finset_sup_apply]
  rfl

variable [TopologicalSpace F]

/--
theorem `LinearMap.withSeminorms_induced` / 定理 `LinearMap.withSeminorms_induced`

English:
theorem LinearMap.withSeminorms_induced
  statement: {q : SeminormFamily 𝕜₂ F ι}
  proof: by
  have := hq.topologicalAddGroup
  let _ : TopologicalSpace E := induced f inferInstance
  have : IsTopologicalAddGroup E := topologicalAddGroup_induced f
  rw [(q.comp f).withSeminorms_iff_nhds_eq_iInf]; rw [nhds_induced]; rw [map_zero]; rw [q.withSeminorms_iff_nhds_eq_iInf.mp hq]; rw [Filter.comap_iInf]
  refine iInf_congr fun i => ?_
  exact Filter.comap_comap

中文:
定理 线性映射.withSeminorms_induced
  结论: {q : SeminormFamily 𝕜₂ F ι}
  证明: by
  have := hq.topologicalAddGroup
  let _ : TopologicalSpace E := induced f inferInstance
  have : IsTopologicalAddGroup E := topologicalAddGroup_induced f
  rw [(q.comp f).withSeminorms_iff_nhds_eq_iInf]; rw [nhds_induced]; rw [map_zero]; rw [q.withSeminorms_iff_nhds_eq_iInf.mp hq]; rw [Filter.comap_iInf]
  refine iInf_congr fun i => ?_
  exact Filter.comap_comap

Depends on / 依赖: Filter, Filter.comap_comap, Filter.comap_iInf, IsTopologicalAddGroup, TopologicalSpace, comap_comap, comap_iInf, hq.topologicalAddGroup, iInf_congr, induced, map_zero, nhds_induced, q.comp, q.withSeminorms_iff_nhds_eq_iInf.mp, topologicalAddGroup, topologicalAddGroup_induced, withSeminorms_iff_nhds_eq_iInf
-/
theorem LinearMap.withSeminorms_induced {q : SeminormFamily 𝕜₂ F ι}
    (hq : WithSeminorms q) (f : E ->ₛₗ[σ₁₂] F) :
    WithSeminorms (topology := induced f inferInstance) (q.comp f) := by
  have := hq.topologicalAddGroup
  let _ : TopologicalSpace E := induced f inferInstance
  have : IsTopologicalAddGroup E := topologicalAddGroup_induced f
  rw [(q.comp f).withSeminorms_iff_nhds_eq_iInf]; rw [nhds_induced]; rw [map_zero]; rw [q.withSeminorms_iff_nhds_eq_iInf.mp hq]; rw [Filter.comap_iInf]
  refine iInf_congr fun i => ?_
  exact Filter.comap_comap

/--
theorem `PolynormableSpace.induced` / 定理 `PolynormableSpace.induced`

English:
theorem PolynormableSpace.induced
  given: [PolynormableSpace 𝕜₂ F] (f : E ->ₛₗ[σ₁₂] F)
  proof: by
  let _ : TopologicalSpace E := induced f inferInstance
.toPolynormableSpace exact f.withSeminorms_induced (PolynormableSpace.withSeminorms 𝕜₂ F)

中文:
定理 Polynormable空间.induced
  条件: [Polynormable空间 𝕜₂ F] (f : E ->ₛₗ[σ₁₂] F)
  证明: by
  let _ : TopologicalSpace E := induced f inferInstance
.toPolynormableSpace exact f.withSeminorms_induced (PolynormableSpace.withSeminorms 𝕜₂ F)
-/
protected theorem PolynormableSpace.induced [PolynormableSpace 𝕜₂ F] (f : E ->ₛₗ[σ₁₂] F) :
    PolynormableSpace 𝕜 E (topology := induced f inferInstance) := by
  let _ : TopologicalSpace E := induced f inferInstance
.toPolynormableSpace exact f.withSeminorms_induced (PolynormableSpace.withSeminorms 𝕜₂ F)

/--
lemma `Topology.IsInducing.withSeminorms` / 引理 `Topology.IsInducing.withSeminorms`

English:
lemma Topology.IsInducing.withSeminorms
  statement: {q : SeminormFamily 𝕜₂ F ι}
  proof: by
  rw [hf.eq_induced]
  exact f.withSeminorms_induced hq

中文:
引理 拓扑.是Inducing.withSeminorms
  结论: {q : SeminormFamily 𝕜₂ F ι}
  证明: by
  rw [hf.eq_induced]
  exact f.withSeminorms_induced hq

Depends on / 依赖: eq_induced, f.withSeminorms_induced, hf.eq_induced, withSeminorms_induced
-/
lemma Topology.IsInducing.withSeminorms {q : SeminormFamily 𝕜₂ F ι}
    (hq : WithSeminorms q) [TopologicalSpace E] {f : E ->ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    WithSeminorms (q.comp f) := by
  rw [hf.eq_induced]
  exact f.withSeminorms_induced hq

/--
theorem `Topology.IsInducing.polynormableSpace` / 定理 `Topology.IsInducing.polynormableSpace`

English:
theorem Topology.IsInducing.polynormableSpace
  statement: [PolynormableSpace 𝕜₂ F]
  proof: .toPolynormableSpace hf.withSeminorms (PolynormableSpace.withSeminorms 𝕜₂ F)

中文:
定理 拓扑.是Inducing.polynormableSpace
  结论: [Polynormable空间 𝕜₂ F]
  证明: .toPolynormableSpace hf.withSeminorms (PolynormableSpace.withSeminorms 𝕜₂ F)

Depends on / 依赖: PolynormableSpace, PolynormableSpace.withSeminorms, hf.withSeminorms, toPolynormableSpace, withSeminorms
-/
theorem Topology.IsInducing.polynormableSpace [PolynormableSpace 𝕜₂ F]
    [TopologicalSpace E] {f : E ->ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    PolynormableSpace 𝕜 E :=
.toPolynormableSpace hf.withSeminorms (PolynormableSpace.withSeminorms 𝕜₂ F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PolynormableSpace
  signature: 𝕜₂ F] {S
  body: IsInducing.polynormableSpace (f := S.subtype) .subtypeVal

中文:
实例 [Polynormable空间
  签名: 𝕜₂ F] {S
  定义体: IsInducing.polynormableSpace (f := S.subtype) .subtypeVal

Depends on / 依赖: IsInducing, IsInducing.polynormableSpace, S.subtype, polynormableSpace, subtype, subtypeVal
-/
instance [PolynormableSpace 𝕜₂ F] {S : Submodule 𝕜₂ F} :
    PolynormableSpace 𝕜₂ S :=
  IsInducing.polynormableSpace (f := S.subtype) .subtypeVal

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Module 𝕜 E] [TopologicalSpace E]
variable {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]

/--
theorem `Seminorm.bound_comp_of_isInducing` / 定理 `Seminorm.bound_comp_of_isInducing`

English:
theorem Seminorm.bound_comp_of_isInducing
  statement: {p : Seminorm 𝕜 E} (hp : Continuous p)
  proof: by
  obtain ⟨s, C, hC, hqC⟩ := Seminorm.bound_of_continuous (hf.withSeminorms hq) p hp
  rw [← SeminormFamily.finset_sup_comp]; rw [← Seminorm.smul_comp] at hqC
  exact ⟨s, C, hC, hqC⟩

中文:
定理 半范数.bound_comp_of_isInducing
  结论: {p : 半范数 𝕜 E} (hp : 连续 p)
  证明: by
  obtain ⟨s, C, hC, hqC⟩ := Seminorm.bound_of_continuous (hf.withSeminorms hq) p hp
  rw [← SeminormFamily.finset_sup_comp]; rw [← Seminorm.smul_comp] at hqC
  exact ⟨s, C, hC, hqC⟩

Depends on / 依赖: Seminorm, Seminorm.bound_of_continuous, Seminorm.smul_comp, SeminormFamily, SeminormFamily.finset_sup_comp, bound_of_continuous, finset_sup_comp, hf.withSeminorms, smul_comp, withSeminorms
-/
theorem Seminorm.bound_comp_of_isInducing {p : Seminorm 𝕜 E} (hp : Continuous p)
    {q : SeminormFamily 𝕜₂ F ι} (hq : WithSeminorms q) {f : E ->ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    exists (s : Finset ι) (C : Real>=0), C != 0 ∧ p <= (C • s.sup q).comp f := by
  obtain ⟨s, C, hC, hqC⟩ := Seminorm.bound_of_continuous (hf.withSeminorms hq) p hp
  rw [← SeminormFamily.finset_sup_comp]; rw [← Seminorm.smul_comp] at hqC
  exact ⟨s, C, hC, hqC⟩

/--
theorem `Seminorm.exists_le_comp_of_isInducing` / 定理 `Seminorm.exists_le_comp_of_isInducing`

English:
theorem Seminorm.exists_le_comp_of_isInducing
  statement: {p : Seminorm 𝕜 E} (hp : Continuous p)
  proof: by
  obtain ⟨s, C, -, hqC⟩ := Seminorm.bound_comp_of_isInducing hp
    (PolynormableSpace.withSeminorms 𝕜₂ F) hf
  have := (PolynormableSpace.withSeminorms 𝕜₂ F).topologicalAddGroup
  exact ⟨_, Continuous.const_smul (continuous_finsetSup fun i _ => i.2) C, hqC⟩

中文:
定理 半范数.存在_le_comp_of_isInducing
  结论: {p : 半范数 𝕜 E} (hp : 连续 p)
  证明: by
  obtain ⟨s, C, -, hqC⟩ := Seminorm.bound_comp_of_isInducing hp
    (PolynormableSpace.withSeminorms 𝕜₂ F) hf
  have := (PolynormableSpace.withSeminorms 𝕜₂ F).topologicalAddGroup
  exact ⟨_, Continuous.const_smul (continuous_finsetSup fun i _ => i.2) C, hqC⟩

Depends on / 依赖: Continuous, Continuous.const_smul, PolynormableSpace, PolynormableSpace.withSeminorms, Seminorm, Seminorm.bound_comp_of_isInducing, bound_comp_of_isInducing, const_smul, continuous_finsetSup, topologicalAddGroup, withSeminorms
-/
theorem Seminorm.exists_le_comp_of_isInducing {p : Seminorm 𝕜 E} (hp : Continuous p)
    [PolynormableSpace 𝕜₂ F] {f : E ->ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    exists p₂ : Seminorm 𝕜₂ F, Continuous p₂ ∧ p <= p₂.comp f := by
  obtain ⟨s, C, -, hqC⟩ := Seminorm.bound_comp_of_isInducing hp
    (PolynormableSpace.withSeminorms 𝕜₂ F) hf
  have := (PolynormableSpace.withSeminorms 𝕜₂ F).topologicalAddGroup
  exact ⟨_, Continuous.const_smul (continuous_finsetSup fun i _ => i.2) C, hqC⟩

end NontriviallyNormedField

/--
Definition of `SeminormFamily.sigma` / `SeminormFamily.sigma` 的定义

English:
definition SeminormFamily.sigma
  signature: {κ : ι -> Type*} (p : (i : ι) -> SeminormFamily 𝕜 E (κ i))
  body: fun ⟨i, k⟩ => p i k

中文:
定义 SeminormFamily.sigma
  签名: {κ : ι -> 类型} (p : (i : ι) -> SeminormFamily 𝕜 E (κ i))
  定义体: fun ⟨i, k⟩ => p i k
-/
protected def SeminormFamily.sigma {κ : ι -> Type*} (p : (i : ι) -> SeminormFamily 𝕜 E (κ i)) :
    SeminormFamily 𝕜 E ((i : ι) × κ i) :=
  fun ⟨i, k⟩ => p i k

/--
theorem `withSeminorms_iInf` / 定理 `withSeminorms_iInf`

English:
theorem withSeminorms_iInf
  statement: {κ : ι -> Type*}
  proof: by
  have : forall i, @IsTopologicalAddGroup E (t i) _ :=
    fun i => @WithSeminorms.topologicalAddGroup _ _ _ _ _ _ (t i) _ (hp i)
  have : @IsTopologicalAddGroup E (⨅ i, t i) _ := topologicalAddGroup_iInf inferInstance
  simp_rw [@SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _ _ _ _ _ _ _ (_)] at hp ⊢
  rw [iInf_sigma]
  exact iInf_congr hp

中文:
定理 withSeminorms_iInf
  结论: {κ : ι -> 类型}
  证明: by
  have : forall i, @IsTopologicalAddGroup E (t i) _ :=
    fun i => @WithSeminorms.topologicalAddGroup _ _ _ _ _ _ (t i) _ (hp i)
  have : @IsTopologicalAddGroup E (⨅ i, t i) _ := topologicalAddGroup_iInf inferInstance
  simp_rw [@SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _ _ _ _ _ _ _ (_)] at hp ⊢
  rw [iInf_sigma]
  exact iInf_congr hp
-/
theorem withSeminorms_iInf {κ : ι -> Type*}
    {p : (i : ι) -> SeminormFamily 𝕜 E (κ i)} {t : ι -> TopologicalSpace E}
    (hp : forall i, WithSeminorms (topology := t i) (p i)) :
    WithSeminorms (topology := ⨅ i, t i) (SeminormFamily.sigma p) := by
  have : forall i, @IsTopologicalAddGroup E (t i) _ :=
    fun i => @WithSeminorms.topologicalAddGroup _ _ _ _ _ _ (t i) _ (hp i)
  have : @IsTopologicalAddGroup E (⨅ i, t i) _ := topologicalAddGroup_iInf inferInstance
  simp_rw [@SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _ _ _ _ _ _ _ (_)] at hp ⊢
  rw [iInf_sigma]
  exact iInf_congr hp

/--
theorem `PolynormableSpace.iInf` / 定理 `PolynormableSpace.iInf`

English:
theorem PolynormableSpace.iInf
  statement: {t : ι -> TopologicalSpace E}
  proof: by
  let _ : TopologicalSpace E := ⨅ i, t i
.toPolynormableSpace exact withSeminorms_iInf (fun i => (ht i).withSeminorms')

中文:
定理 Polynormable空间.iInf
  结论: {t : ι -> 拓扑空间 E}
  证明: by
  let _ : TopologicalSpace E := ⨅ i, t i
.toPolynormableSpace exact withSeminorms_iInf (fun i => (ht i).withSeminorms')
-/
theorem PolynormableSpace.iInf {t : ι -> TopologicalSpace E}
    (ht : forall i, PolynormableSpace 𝕜 E (topology := t i)) :
    PolynormableSpace 𝕜 E (topology := ⨅ i, t i) := by
  let _ : TopologicalSpace E := ⨅ i, t i
.toPolynormableSpace exact withSeminorms_iInf (fun i => (ht i).withSeminorms')

/--
theorem `PolynormableSpace.sInf` / 定理 `PolynormableSpace.sInf`

English:
theorem PolynormableSpace.sInf
  statement: {ts : Set (TopologicalSpace E)}
  proof: by
  rw [sInf_eq_iInf']
  exact .iInf fun t => hts t.1 t.2

中文:
定理 Polynormable空间.sInf
  结论: {ts : 集合 (拓扑空间 E)}
  证明: by
  rw [sInf_eq_iInf']
  exact .iInf fun t => hts t.1 t.2
-/
theorem PolynormableSpace.sInf {ts : Set (TopologicalSpace E)}
    (hts : forall t in ts, PolynormableSpace 𝕜 E (topology := t)) :
    PolynormableSpace 𝕜 E (topology := sInf ts) := by
  rw [sInf_eq_iInf']
  exact .iInf fun t => hts t.1 t.2

/--
theorem `PolynormableSpace.inf` / 定理 `PolynormableSpace.inf`

English:
theorem PolynormableSpace.inf
  statement: {t₁ t₂ : TopologicalSpace E}
  proof: by
  rw [← sInf_pair]
  exact .sInf (by simp [ht₁, ht₂])

中文:
定理 Polynormable空间.下确界
  结论: {t₁ t₂ : 拓扑空间 E}
  证明: by
  rw [← sInf_pair]
  exact .sInf (by simp [ht₁, ht₂])
-/
theorem PolynormableSpace.inf {t₁ t₂ : TopologicalSpace E}
    (ht₁ : PolynormableSpace 𝕜 E (topology := t₁))
    (ht₂ : PolynormableSpace 𝕜 E (topology := t₂)) :
    PolynormableSpace 𝕜 E (topology := t₁ ⊓ t₂) := by
  rw [← sInf_pair]
  exact .sInf (by simp [ht₁, ht₂])

/--
theorem `withSeminorms_pi` / 定理 `withSeminorms_pi`

English:
theorem withSeminorms_pi
  statement: {κ : ι -> Type*} {E : ι -> Type*}
  proof: withSeminorms_iInf fun i => (LinearMap.proj i).withSeminorms_induced (hp i)

中文:
定理 withSeminorms_pi
  结论: {κ : ι -> 类型} {E : ι -> 类型}
  证明: withSeminorms_iInf fun i => (LinearMap.proj i).withSeminorms_induced (hp i)

Depends on / 依赖: LinearMap, LinearMap.proj, withSeminorms_iInf, withSeminorms_induced
-/
theorem withSeminorms_pi {κ : ι -> Type*} {E : ι -> Type*}
    [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)]
    {p : (i : ι) -> SeminormFamily 𝕜 (E i) (κ i)}
    (hp : forall i, WithSeminorms (p i)) :
    WithSeminorms (SeminormFamily.sigma (fun i => (p i).comp (LinearMap.proj i))) :=
  withSeminorms_iInf fun i => (LinearMap.proj i).withSeminorms_induced (hp i)

instance {E : ι -> Type*} [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)]
    [forall i, TopologicalSpace (E i)] [forall i, PolynormableSpace 𝕜 (E i)] :
    PolynormableSpace 𝕜 (Π i, E i) :=
  .iInf fun i => .induced (LinearMap.proj (R := 𝕜) (φ := E) i)

instance {E₁ E₂ : Type*} [AddCommGroup E₁] [AddCommGroup E₂] [Module 𝕜 E₁] [Module 𝕜 E₂]
    [TopologicalSpace E₁] [TopologicalSpace E₂] [PolynormableSpace 𝕜 E₁] [PolynormableSpace 𝕜 E₂] :
    PolynormableSpace 𝕜 (E₁ × E₂) :=
  .inf (.induced <| LinearMap.fst 𝕜 E₁ E₂) (.induced <| LinearMap.snd 𝕜 E₁ E₂)

end TopologicalConstructions

section TopologicalProperties

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Countable ι]
variable {p : SeminormFamily 𝕜 E ι}
variable [TopologicalSpace E]

/--
theorem `WithSeminorms.firstCountableTopology` / 定理 `WithSeminorms.firstCountableTopology`

English:
theorem WithSeminorms.firstCountableTopology
  given: (hp : WithSeminorms p)
  proof: by
  have := hp.topologicalAddGroup
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : (𝓝 (0 : E)).IsCountablyGenerated := by
    rw [p.withSeminorms_iff_nhds_eq_iInf.mp hp]
    exact Filter.iInf.isCountablyGenerated _
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.firstCountableTopology E

中文:
定理 WithSeminorms.firstCountableTopology
  条件: (hp : WithSeminorms p)
  证明: by
  have := hp.topologicalAddGroup
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : (𝓝 (0 : E)).IsCountablyGenerated := by
    rw [p.withSeminorms_iff_nhds_eq_iInf.mp hp]
    exact Filter.iInf.isCountablyGenerated _
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.firstCountableTopology E

Depends on / 依赖: Filter, Filter.iInf.isCountablyGenerated, IsCountablyGenerated, IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, IsUniformAddGroup, IsUniformAddGroup.uniformity_countably_generated, UniformSpace, UniformSpace.firstCountableTopology, firstCountableTopology, hp.topologicalAddGroup, isCountablyGenerated, isUniformAddGroup_of_addCommGroup, p.withSeminorms_iff_nhds_eq_iInf.mp, rightUniformSpace, topologicalAddGroup, uniformity, uniformity_countably_generated, withSeminorms_iff_nhds_eq_iInf
-/
theorem WithSeminorms.firstCountableTopology (hp : WithSeminorms p) :
    FirstCountableTopology E := by
  have := hp.topologicalAddGroup
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : (𝓝 (0 : E)).IsCountablyGenerated := by
    rw [p.withSeminorms_iff_nhds_eq_iInf.mp hp]
    exact Filter.iInf.isCountablyGenerated _
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.firstCountableTopology E

end TopologicalProperties
