/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.UniformSpace.Compact

/-!
# Extra lemmas about pseudo-metric spaces
-/

public section

open Bornology Filter Metric Set
open scoped NNReal Topology

variable {ι α : Type*} [PseudoMetricSpace α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology Real
  body: orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]

中文:
实例 :
  签名: OrderTopology 实数
  定义体: orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]

Depends on / 依赖: Real.dist_eq, abs_sub_comm, dist_eq, eq_biInf, nhds_basis_ball, nhds_basis_ball.eq_biInf, orderTopology_of_nhds_abs
-/
instance : OrderTopology Real :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]

/--
lemma `Real.singleton_eq_inter_Icc` / 引理 `Real.singleton_eq_inter_Icc`

English:
lemma Real.singleton_eq_inter_Icc
  given: (b : Real)
  statement: {b} = ⋂ (r > 0), Icc (b - r) (b + r)
  proof: by
  simp [Icc_eq_closedBall, biInter_basis_nhds Metric.nhds_basis_closedBall]

中文:
引理 Real.singleton_eq_inter_Icc
  条件: (b : 实数)
  结论: {b} = ⋂ (r > 0), Icc (b - r) (b + r)
  证明: by
  simp [Icc_eq_closedBall, biInter_basis_nhds Metric.nhds_basis_closedBall]

Depends on / 依赖: Icc_eq_closedBall, Metric, Metric.nhds_basis_closedBall, biInter_basis_nhds, nhds_basis_closedBall
-/
lemma Real.singleton_eq_inter_Icc (b : Real) : {b} = ⋂ (r > 0), Icc (b - r) (b + r) := by
  simp [Icc_eq_closedBall, biInter_basis_nhds Metric.nhds_basis_closedBall]

/--
lemma `squeeze_zero'` / 引理 `squeeze_zero'`

English:
lemma squeeze_zero'
  statement: {α} {f g : α -> Real} {t₀ : Filter α} (hf : forallᶠ t in t₀, 0 <= f t)
  proof: tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft

中文:
引理 squeeze_zero'
  结论: {α} {f g : α -> 实数} {t₀ : Filter α} (hf : 对任意ᶠ t in t₀, 0 <= f t)
  证明: tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft

Depends on / 依赖: tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le
-/
lemma squeeze_zero' {α} {f g : α -> Real} {t₀ : Filter α} (hf : forallᶠ t in t₀, 0 <= f t)
    (hft : forallᶠ t in t₀, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft

/--
lemma `squeeze_zero` / 引理 `squeeze_zero`

English:
lemma squeeze_zero
  statement: {α} {f g : α -> Real} {t₀ : Filter α} (hf : forall t, 0 <= f t) (hft : forall t, f t <= g t)
  proof: squeeze_zero' (Eventually.of_forall hf) (Eventually.of_forall hft) g0

中文:
引理 squeeze_zero
  结论: {α} {f g : α -> 实数} {t₀ : Filter α} (hf : 对任意 t, 0 <= f t) (hft : 对任意 t, f t <= g t)
  证明: squeeze_zero' (Eventually.of_forall hf) (Eventually.of_forall hft) g0

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, squeeze_zero
-/
lemma squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : forall t, 0 <= f t) (hft : forall t, f t <= g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall hf) (Eventually.of_forall hft) g0

/--
lemma `eventually_closedBall_subset` / 引理 `eventually_closedBall_subset`

English:
lemma eventually_closedBall_subset
  given: {x : α} {u : Set α} (hu : u in 𝓝 x)
  proof: by
  obtain ⟨ε, εpos, hε⟩ : exists ε, 0 < ε ∧ closedBall x ε subseteq u := nhds_basis_closedBall.mem_iff.1 hu
  have : Iic ε in 𝓝 (0 : Real) := Iic_mem_nhds εpos
  filter_upwards [this] with _ hr using Subset.trans (closedBall_subset_closedBall hr) hε

中文:
引理 eventually_closedBall_subset
  条件: {x : α} {u : Set α} (hu : u in 𝓝 x)
  证明: by
  obtain ⟨ε, εpos, hε⟩ : exists ε, 0 < ε ∧ closedBall x ε subseteq u := nhds_basis_closedBall.mem_iff.1 hu
  have : Iic ε in 𝓝 (0 : Real) := Iic_mem_nhds εpos
  filter_upwards [this] with _ hr using Subset.trans (closedBall_subset_closedBall hr) hε

Depends on / 依赖: Iic_mem_nhds, Subset, Subset.trans, closedBall, closedBall_subset_closedBall, filter_upwards, mem_iff, nhds_basis_closedBall, nhds_basis_closedBall.mem_iff, subseteq
-/
lemma eventually_closedBall_subset {x : α} {u : Set α} (hu : u in 𝓝 x) :
    forallᶠ r in 𝓝 (0 : Real), closedBall x r subseteq u := by
  obtain ⟨ε, εpos, hε⟩ : exists ε, 0 < ε ∧ closedBall x ε subseteq u := nhds_basis_closedBall.mem_iff.1 hu
  have : Iic ε in 𝓝 (0 : Real) := Iic_mem_nhds εpos
  filter_upwards [this] with _ hr using Subset.trans (closedBall_subset_closedBall hr) hε

/--
lemma `tendsto_closedBall_smallSets` / 引理 `tendsto_closedBall_smallSets`

English:
lemma tendsto_closedBall_smallSets
  given: (x : α)
  statement: Tendsto (closedBall x) (𝓝 0) (𝓝 x).smallSets
  proof: tendsto_smallSets_iff.2 fun _ => eventually_closedBall_subset

中文:
引理 tendsto_closedBall_smallSets
  条件: (x : α)
  结论: Tendsto (closedBall x) (𝓝 0) (𝓝 x).smallSets
  证明: tendsto_smallSets_iff.2 fun _ => eventually_closedBall_subset

Depends on / 依赖: eventually_closedBall_subset, tendsto_smallSets_iff
-/
lemma tendsto_closedBall_smallSets (x : α) : Tendsto (closedBall x) (𝓝 0) (𝓝 x).smallSets :=
  tendsto_smallSets_iff.2 fun _ => eventually_closedBall_subset

/--
lemma `eventually_ball_subset` / 引理 `eventually_ball_subset`

English:
lemma eventually_ball_subset
  given: {x : α} {u : Set α} (hu : u in 𝓝 x)
  statement: forallᶠ r in 𝓝 (0 : Real), ball x r subseteq u
  proof: (eventually_closedBall_subset hu).mono fun _r hr => ball_subset_closedBall.trans hr

中文:
引理 eventually_ball_subset
  条件: {x : α} {u : Set α} (hu : u in 𝓝 x)
  结论: 对任意ᶠ r in 𝓝 (0 : 实数), ball x r subseteq u
  证明: (eventually_closedBall_subset hu).mono fun _r hr => ball_subset_closedBall.trans hr

Depends on / 依赖: ball_subset_closedBall, ball_subset_closedBall.trans, eventually_closedBall_subset
-/
lemma eventually_ball_subset {x : α} {u : Set α} (hu : u in 𝓝 x) : forallᶠ r in 𝓝 (0 : Real), ball x r subseteq u :=
  (eventually_closedBall_subset hu).mono fun _r hr => ball_subset_closedBall.trans hr

namespace Metric
variable {x y z : α} {ε ε₁ ε₂ : Real} {s : Set α}

/--
lemma `isClosed_closedBall` / 引理 `isClosed_closedBall`

English:
lemma isClosed_closedBall
  statement: IsClosed (closedBall x ε)
  proof: isClosed_le (by fun_prop) continuous_const

中文:
引理 isClosed_closedBall
  结论: IsClosed (closedBall x ε)
  证明: isClosed_le (by fun_prop) continuous_const

Depends on / 依赖: continuous_const, fun_prop, isClosed_le
-/
lemma isClosed_closedBall : IsClosed (closedBall x ε) := isClosed_le (by fun_prop) continuous_const

/--
lemma `isClosed_sphere` / 引理 `isClosed_sphere`

English:
lemma isClosed_sphere
  statement: IsClosed (sphere x ε)
  proof: isClosed_eq (by fun_prop) continuous_const

@[simp]

中文:
引理 isClosed_sphere
  结论: IsClosed (sphere x ε)
  证明: isClosed_eq (by fun_prop) continuous_const

@[simp]

Depends on / 依赖: continuous_const, fun_prop, isClosed_eq
-/
lemma isClosed_sphere : IsClosed (sphere x ε) := isClosed_eq (by fun_prop) continuous_const

@[simp]
/--
lemma `closure_closedBall` / 引理 `closure_closedBall`

English:
lemma closure_closedBall
  statement: closure (closedBall x ε) = closedBall x ε
  proof: isClosed_closedBall.closure_eq

@[simp]

中文:
引理 closure_closedBall
  结论: closure (closedBall x ε) = closedBall x ε
  证明: isClosed_closedBall.closure_eq

@[simp]

Depends on / 依赖: closure_eq, isClosed_closedBall, isClosed_closedBall.closure_eq
-/
lemma closure_closedBall : closure (closedBall x ε) = closedBall x ε :=
  isClosed_closedBall.closure_eq

@[simp]
/--
lemma `closure_sphere` / 引理 `closure_sphere`

English:
lemma closure_sphere
  statement: closure (sphere x ε) = sphere x ε
  proof: isClosed_sphere.closure_eq

中文:
引理 closure_sphere
  结论: closure (sphere x ε) = sphere x ε
  证明: isClosed_sphere.closure_eq

Depends on / 依赖: closure_eq, isClosed_sphere, isClosed_sphere.closure_eq
-/
lemma closure_sphere : closure (sphere x ε) = sphere x ε :=
  isClosed_sphere.closure_eq

/--
lemma `closure_ball_subset_closedBall` / 引理 `closure_ball_subset_closedBall`

English:
lemma closure_ball_subset_closedBall
  statement: closure (ball x ε) subseteq closedBall x ε
  proof: closure_minimal ball_subset_closedBall isClosed_closedBall

中文:
引理 closure_ball_subset_closedBall
  结论: closure (ball x ε) subseteq closedBall x ε
  证明: closure_minimal ball_subset_closedBall isClosed_closedBall

Depends on / 依赖: ball_subset_closedBall, closure_minimal, isClosed_closedBall
-/
lemma closure_ball_subset_closedBall : closure (ball x ε) subseteq closedBall x ε :=
  closure_minimal ball_subset_closedBall isClosed_closedBall

/--
lemma `frontier_ball_subset_sphere` / 引理 `frontier_ball_subset_sphere`

English:
lemma frontier_ball_subset_sphere
  statement: frontier (ball x ε) subseteq sphere x ε
  proof: frontier_lt_subset_eq (by fun_prop) continuous_const

中文:
引理 frontier_ball_subset_sphere
  结论: frontier (ball x ε) subseteq sphere x ε
  证明: frontier_lt_subset_eq (by fun_prop) continuous_const

Depends on / 依赖: continuous_const, frontier_lt_subset_eq, fun_prop
-/
lemma frontier_ball_subset_sphere : frontier (ball x ε) subseteq sphere x ε :=
  frontier_lt_subset_eq (by fun_prop) continuous_const

/--
lemma `frontier_closedBall_subset_sphere` / 引理 `frontier_closedBall_subset_sphere`

English:
lemma frontier_closedBall_subset_sphere
  statement: frontier (closedBall x ε) subseteq sphere x ε
  proof: frontier_le_subset_eq (by fun_prop) continuous_const

中文:
引理 frontier_closedBall_subset_sphere
  结论: frontier (closedBall x ε) subseteq sphere x ε
  证明: frontier_le_subset_eq (by fun_prop) continuous_const

Depends on / 依赖: continuous_const, frontier_le_subset_eq, fun_prop
-/
lemma frontier_closedBall_subset_sphere : frontier (closedBall x ε) subseteq sphere x ε :=
  frontier_le_subset_eq (by fun_prop) continuous_const

/--
lemma `closedBall_zero'` / 引理 `closedBall_zero'`

English:
lemma closedBall_zero'
  given: (x : α)
  statement: closedBall x 0 = closure {x}
  proof: Subset.antisymm
    (fun _y hy =>
      mem_closure_iff.2 fun _ε ε0 => ⟨x, mem_singleton x, (mem_closedBall.1 hy).trans_lt ε0⟩)
    (closure_minimal (singleton_subset_iff.2 (dist_self x).le) isClosed_closedBall)

中文:
引理 closedBall_zero'
  条件: (x : α)
  结论: closedBall x 0 = closure {x}
  证明: Subset.antisymm
    (fun _y hy =>
      mem_closure_iff.2 fun _ε ε0 => ⟨x, mem_singleton x, (mem_closedBall.1 hy).trans_lt ε0⟩)
    (closure_minimal (singleton_subset_iff.2 (dist_self x).le) isClosed_closedBall)

Depends on / 依赖: Subset, Subset.antisymm, antisymm, closure_minimal, dist_self, isClosed_closedBall, mem_closedBall, mem_closure_iff, mem_singleton, singleton_subset_iff, trans_lt
-/
lemma closedBall_zero' (x : α) : closedBall x 0 = closure {x} :=
  Subset.antisymm
    (fun _y hy =>
      mem_closure_iff.2 fun _ε ε0 => ⟨x, mem_singleton x, (mem_closedBall.1 hy).trans_lt ε0⟩)
    (closure_minimal (singleton_subset_iff.2 (dist_self x).le) isClosed_closedBall)

/--
lemma `eventually_isCompact_closedBall` / 引理 `eventually_isCompact_closedBall`

English:
lemma eventually_isCompact_closedBall
  given: [WeaklyLocallyCompactSpace α] (x : α)
  proof: by
  rcases exists_compact_mem_nhds x with ⟨s, s_compact, hs⟩
  filter_upwards [eventually_closedBall_subset hs] with r hr
  exact IsCompact.of_isClosed_subset s_compact isClosed_closedBall hr

中文:
引理 eventually_isCompact_closedBall
  条件: [WeaklyLocallyCompactSpace α] (x : α)
  证明: by
  rcases exists_compact_mem_nhds x with ⟨s, s_compact, hs⟩
  filter_upwards [eventually_closedBall_subset hs] with r hr
  exact IsCompact.of_isClosed_subset s_compact isClosed_closedBall hr

Depends on / 依赖: IsCompact, IsCompact.of_isClosed_subset, eventually_closedBall_subset, exists_compact_mem_nhds, filter_upwards, isClosed_closedBall, of_isClosed_subset, s_compact
-/
lemma eventually_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    forallᶠ r in 𝓝 (0 : Real), IsCompact (closedBall x r) := by
  rcases exists_compact_mem_nhds x with ⟨s, s_compact, hs⟩
  filter_upwards [eventually_closedBall_subset hs] with r hr
  exact IsCompact.of_isClosed_subset s_compact isClosed_closedBall hr

/--
lemma `exists_isCompact_closedBall` / 引理 `exists_isCompact_closedBall`

English:
lemma exists_isCompact_closedBall
  given: [WeaklyLocallyCompactSpace α] (x : α)
  proof: by
  have : forallᶠ r in 𝓝[>] 0, IsCompact (closedBall x r) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_isCompact_closedBall x)
  simpa only [and_comm] using (this.and self_mem_nhdsWithin).exists

中文:
引理 exists_isCompact_closedBall
  条件: [WeaklyLocallyCompactSpace α] (x : α)
  证明: by
  have : forallᶠ r in 𝓝[>] 0, IsCompact (closedBall x r) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_isCompact_closedBall x)
  simpa only [and_comm] using (this.and self_mem_nhdsWithin).exists

Depends on / 依赖: IsCompact, and_comm, closedBall, eventually_isCompact_closedBall, eventually_nhdsWithin_of_eventually_nhds, self_mem_nhdsWithin, this.and
-/
lemma exists_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    exists r, 0 < r ∧ IsCompact (closedBall x r) := by
  have : forallᶠ r in 𝓝[>] 0, IsCompact (closedBall x r) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_isCompact_closedBall x)
  simpa only [and_comm] using (this.and self_mem_nhdsWithin).exists

/--
theorem `biInter_gt_closedBall` / 定理 `biInter_gt_closedBall`

English:
theorem biInter_gt_closedBall
  given: (x : α) (r : Real)
  statement: ⋂ r' > r, closedBall x r' = closedBall x r
  proof: by
  ext
  simp [forall_gt_imp_ge_iff_le_of_dense]

中文:
定理 biInter_gt_closedBall
  条件: (x : α) (r : 实数)
  结论: ⋂ r' > r, closedBall x r' = closedBall x r
  证明: by
  ext
  simp [forall_gt_imp_ge_iff_le_of_dense]

Depends on / 依赖: forall_gt_imp_ge_iff_le_of_dense
-/
theorem biInter_gt_closedBall (x : α) (r : Real) : ⋂ r' > r, closedBall x r' = closedBall x r := by
  ext
  simp [forall_gt_imp_ge_iff_le_of_dense]

/--
theorem `biInter_gt_ball` / 定理 `biInter_gt_ball`

English:
theorem biInter_gt_ball
  given: (x : α) (r : Real)
  statement: ⋂ r' > r, ball x r' = closedBall x r
  proof: by
  ext
  simp [forall_gt_iff_le]

中文:
定理 biInter_gt_ball
  条件: (x : α) (r : 实数)
  结论: ⋂ r' > r, ball x r' = closedBall x r
  证明: by
  ext
  simp [forall_gt_iff_le]

Depends on / 依赖: forall_gt_iff_le
-/
theorem biInter_gt_ball (x : α) (r : Real) : ⋂ r' > r, ball x r' = closedBall x r := by
  ext
  simp [forall_gt_iff_le]

/--
theorem `biUnion_lt_ball` / 定理 `biUnion_lt_ball`

English:
theorem biUnion_lt_ball
  given: (x : α) (r : Real)
  statement: ⋃ r' < r, ball x r' = ball x r
  proof: by
  ext
  rw [← not_iff_not]
  simp [forall_lt_imp_le_iff_le_of_dense]

中文:
定理 biUnion_lt_ball
  条件: (x : α) (r : 实数)
  结论: ⋃ r' < r, ball x r' = ball x r
  证明: by
  ext
  rw [← not_iff_not]
  simp [forall_lt_imp_le_iff_le_of_dense]

Depends on / 依赖: forall_lt_imp_le_iff_le_of_dense, not_iff_not
-/
theorem biUnion_lt_ball (x : α) (r : Real) : ⋃ r' < r, ball x r' = ball x r := by
  ext
  rw [← not_iff_not]
  simp [forall_lt_imp_le_iff_le_of_dense]

/--
theorem `biUnion_lt_closedBall` / 定理 `biUnion_lt_closedBall`

English:
theorem biUnion_lt_closedBall
  given: (x : α) (r : Real)
  statement: ⋃ r' < r, closedBall x r' = ball x r
  proof: by
  ext
  rw [← not_iff_not]
  simp [forall_lt_iff_le]

中文:
定理 biUnion_lt_closedBall
  条件: (x : α) (r : 实数)
  结论: ⋃ r' < r, closedBall x r' = ball x r
  证明: by
  ext
  rw [← not_iff_not]
  simp [forall_lt_iff_le]

Depends on / 依赖: forall_lt_iff_le, not_iff_not
-/
theorem biUnion_lt_closedBall (x : α) (r : Real) : ⋃ r' < r, closedBall x r' = ball x r := by
  ext
  rw [← not_iff_not]
  simp [forall_lt_iff_le]

end Metric

/--
theorem `lebesgue_number_lemma_of_metric` / 定理 `lebesgue_number_lemma_of_metric`

English:
theorem lebesgue_number_lemma_of_metric
  statement: {s : Set α} {ι : Sort*} {c : ι -> Set α} (hs : IsCompact s)
  proof: by
  simpa only [ball, UniformSpace.ball, preimage_ofPred_eq, dist_comm]
    using uniformity_basis_dist.lebesgue_number_lemma hs hc₁ hc₂

中文:
定理 lebesgue_number_lemma_of_metric
  结论: {s : Set α} {ι : Sort*} {c : ι -> Set α} (hs : IsCompact s)
  证明: by
  simpa only [ball, UniformSpace.ball, preimage_ofPred_eq, dist_comm]
    using uniformity_basis_dist.lebesgue_number_lemma hs hc₁ hc₂

Depends on / 依赖: UniformSpace, UniformSpace.ball, dist_comm, lebesgue_number_lemma, preimage_ofPred_eq, uniformity_basis_dist, uniformity_basis_dist.lebesgue_number_lemma
-/
theorem lebesgue_number_lemma_of_metric {s : Set α} {ι : Sort*} {c : ι -> Set α} (hs : IsCompact s)
    (hc₁ : forall i, IsOpen (c i)) (hc₂ : s subseteq ⋃ i, c i) : exists δ > 0, forall x in s, exists i, ball x δ subseteq c i := by
  simpa only [ball, UniformSpace.ball, preimage_ofPred_eq, dist_comm]
    using uniformity_basis_dist.lebesgue_number_lemma hs hc₁ hc₂

/--
theorem `lebesgue_number_lemma_of_metric_sUnion` / 定理 `lebesgue_number_lemma_of_metric_sUnion`

English:
theorem lebesgue_number_lemma_of_metric_sUnion
  statement: {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
  proof: by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂

中文:
定理 lebesgue_number_lemma_of_metric_sUnion
  结论: {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
  证明: by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂

Depends on / 依赖: lebesgue_number_lemma_of_metric, sUnion_eq_iUnion
-/
theorem lebesgue_number_lemma_of_metric_sUnion {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : forall t in c, IsOpen t) (hc₂ : s subseteq ⋃₀ c) : exists δ > 0, forall x in s, exists t in c, ball x δ subseteq t := by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂
