/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.AsymptoticCone

/-!
# Asymptotic cones in normed spaces

In this file, we prove that the asymptotic cone of a set is non-trivial if and only if the set is
unbounded.
-/

public section

open AffineSpace Bornology Filter Topology

variable
  {V P : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [MetricSpace P] [NormedAddTorsor V P]

/--
theorem `AffineSpace.asymptoticNhds_le_cobounded` / 定理 `AffineSpace.asymptoticNhds_le_cobounded`

English:
theorem AffineSpace.asymptoticNhds_le_cobounded
  given: {v : V} (hv : v != 0)
  proof: by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← tendsto_id']; rw [← Metric.tendsto_dist_right_atTop_iff p]; rw [asymptoticNhds_eq_smul_vadd v p]; rw [vadd_pure]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [map_map]; rw [tendsto_map'_iff]
  change Tendsto (fun x : Real × V => dist (x.1 • x.2 +

中文:
定理 仿射空间.asymptoticNhds_le_cobounded
  条件: {v : V} (hv : v != 0)
  证明: by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← tendsto_id']; rw [← Metric.tendsto_dist_right_atTop_iff p]; rw [asymptoticNhds_eq_smul_vadd v p]; rw [vadd_pure]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [map_map]; rw [tendsto_map'_iff]
  change Tendsto (fun x : Real × V => dist (x.1 • x.2 +

Depends on / 依赖: Metric, Metric.tendsto_dist_right_atTop_iff, Nonempty, Tendsto, Tendsto.atTop_mul_pos, _iff, asymptoticNhds_eq_smul_vadd, atTop_mul_pos, dist_vadd_left, map_map, norm_pos_iff, norm_pos_iff.mpr, norm_smul, simp_rw, tendsto_dist_right_atTop_iff, tendsto_id, tendsto_id.fst, tendsto_map, tendsto_norm_atTop_atTop, tendsto_norm_atTop_atTop.comp
-/
theorem AffineSpace.asymptoticNhds_le_cobounded {v : V} (hv : v != 0) :
    asymptoticNhds Real P v <= cobounded P := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← tendsto_id']; rw [← Metric.tendsto_dist_right_atTop_iff p]; rw [asymptoticNhds_eq_smul_vadd v p]; rw [vadd_pure]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [map_map]; rw [tendsto_map'_iff]
  change Tendsto (fun x : Real × V => dist (x.1 • x.2 +ᵥ p) p) (atTop ×ˢ 𝓝 v) atTop
  simp_rw [dist_vadd_left, norm_smul]
  exact Tendsto.atTop_mul_pos (norm_pos_iff.mpr hv)
    (tendsto_norm_atTop_atTop.comp tendsto_id.fst)
    tendsto_snd.norm

/--
theorem `asymptoticCone_subset_singleton_of_bounded` / 定理 `asymptoticCone_subset_singleton_of_bounded`

English:
theorem asymptoticCone_subset_singleton_of_bounded
  given: {s : Set P} (hs : IsBounded s)
  proof: by
  intro v h
  by_contra! hv
  exact h (asymptoticNhds_le_cobounded hv hs)

中文:
定理 asymptoticCone_subset_singleton_of_bounded
  条件: {s : 集合 P} (hs : IsBounded s)
  证明: by
  intro v h
  by_contra! hv
  exact h (asymptoticNhds_le_cobounded hv hs)

Depends on / 依赖: asymptoticNhds_le_cobounded
-/
theorem asymptoticCone_subset_singleton_of_bounded {s : Set P} (hs : IsBounded s) :
    asymptoticCone Real s subseteq {0} := by
  intro v h
  by_contra! hv
  exact h (asymptoticNhds_le_cobounded hv hs)

variable [FiniteDimensional Real V]

/--
theorem `AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds` / 定理 `AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds`

English:
theorem AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds
  proof: by
refine le_antisymm ?_ iSup₂_le fun _ h => asymptoticNhds_le_cobounded
    Metric.ne_of_mem_sphere h one_ne_zero
  intro s hs
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [mem_iSup, asymptoticNhds_eq_smul_vadd _ p, vadd_pure] at hs
  choose! t ht u hu smul_subset_s using hs
  have ⟨cover, h₁

中文:
定理 仿射空间.cobounded_eq_iSup_sphere_asymptoticNhds
  证明: by
refine le_antisymm ?_ iSup₂_le fun _ h => asymptoticNhds_le_cobounded
    Metric.ne_of_mem_sphere h one_ne_zero
  intro s hs
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [mem_iSup, asymptoticNhds_eq_smul_vadd _ p, vadd_pure] at hs
  choose! t ht u hu smul_subset_s using hs
  have ⟨cover, h₁

Depends on / 依赖: Ioi_mem_atTop, Metric, Metric.comap_dist_left_atTop, Metric.ne_of_mem_sphere, Nonempty, Set.Ioi, asymptoticNhds_eq_smul_vadd, asymptoticNhds_le_cobounded, comap_dist_left_atTop, cover.iInter_mem_sets.mpr, elim_nhds_subcover, iInter_mem_sets, inter_mem, isCompact_sphere, le_antisymm, mem_iSup, ne_of_mem_sphere, one_ne_zero, simp_rw, smul_subset_s
-/
theorem AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds :
    cobounded P = ⨆ v in Metric.sphere 0 1, asymptoticNhds Real P v := by
refine le_antisymm ?_ iSup₂_le fun _ h => asymptoticNhds_le_cobounded
    Metric.ne_of_mem_sphere h one_ne_zero
  intro s hs
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [mem_iSup, asymptoticNhds_eq_smul_vadd _ p, vadd_pure] at hs
  choose! t ht u hu smul_subset_s using hs
  have ⟨cover, h₁, h₂⟩ := (isCompact_sphere 0 1).elim_nhds_subcover u hu
  rw [← Metric.comap_dist_left_atTop p]
  refine ⟨Set.Ioi 0 inter ⋂ x in cover, t x, inter_mem (Ioi_mem_atTop 0)
    (cover.iInter_mem_sets.mpr fun x hx => ht x (h₁ x hx)), fun x hx => ?_⟩
  rw [Set.mem_preimage]; rw [dist_eq_norm_vsub'] at hx
  let x' := ‖x -ᵥ p‖⁻¹ • (x -ᵥ p)
  have x'_mem : x' in Metric.sphere 0 1 := by
    rw [mem_sphere_zero_iff_norm]; rw [norm_smul]; rw [norm_inv]; rw [norm_norm]; rw [inv_mul_cancel₀ hx.1.ne']
  have ⟨y, y_mem, hy⟩ := Set.mem_iUnion₂.mp (h₂ x'_mem)
  rw [← vsub_vadd x p]; rw [← show ‖x -ᵥ p‖ • x' = x -ᵥ p from smul_inv_smul₀ hx.1.ne' (x -ᵥ p)]
exact smul_subset_s y (h₁ y y_mem) Set.smul_mem_smul (Set.biInter_subset_of_mem y_mem hx.2) hy

/--
theorem `isBounded_iff_asymptoticCone_subset_singleton` / 定理 `isBounded_iff_asymptoticCone_subset_singleton`

English:
theorem isBounded_iff_asymptoticCone_subset_singleton
  given: {s : Set P}
  proof: by
  refine ⟨asymptoticCone_subset_singleton_of_bounded, fun h => ?_⟩
  simp_rw [isBounded_def, cobounded_eq_iSup_sphere_asymptoticNhds, mem_iSup]
  intro v hv
  by_contra h'
  exact Metric.ne_of_mem_sphere hv one_ne_zero (h h')

中文:
定理 isBounded_iff_asymptoticCone_subset_singleton
  条件: {s : 集合 P}
  证明: by
  refine ⟨asymptoticCone_subset_singleton_of_bounded, fun h => ?_⟩
  simp_rw [isBounded_def, cobounded_eq_iSup_sphere_asymptoticNhds, mem_iSup]
  intro v hv
  by_contra h'
  exact Metric.ne_of_mem_sphere hv one_ne_zero (h h')

Depends on / 依赖: Metric, Metric.ne_of_mem_sphere, asymptoticCone_subset_singleton_of_bounded, cobounded_eq_iSup_sphere_asymptoticNhds, isBounded_def, mem_iSup, ne_of_mem_sphere, one_ne_zero, simp_rw
-/
theorem isBounded_iff_asymptoticCone_subset_singleton {s : Set P} :
    IsBounded s ↔ asymptoticCone Real s subseteq {0} := by
  refine ⟨asymptoticCone_subset_singleton_of_bounded, fun h => ?_⟩
  simp_rw [isBounded_def, cobounded_eq_iSup_sphere_asymptoticNhds, mem_iSup]
  intro v hv
  by_contra h'
  exact Metric.ne_of_mem_sphere hv one_ne_zero (h h')

/--
theorem `not_bounded_iff_exists_ne_zero_mem_asymptoticCone` / 定理 `not_bounded_iff_exists_ne_zero_mem_asymptoticCone`

English:
theorem not_bounded_iff_exists_ne_zero_mem_asymptoticCone
  given: {s : Set P}
  proof: by
  rw [isBounded_iff_asymptoticCone_subset_singleton]; rw [Set.subset_singleton_iff]; rw [not_forall]
  tauto

中文:
定理 not_bounded_iff_存在_ne_zero_mem_asymptoticCone
  条件: {s : 集合 P}
  证明: by
  rw [isBounded_iff_asymptoticCone_subset_singleton]; rw [Set.subset_singleton_iff]; rw [not_forall]
  tauto

Depends on / 依赖: Set.subset_singleton_iff, isBounded_iff_asymptoticCone_subset_singleton, not_forall, subset_singleton_iff
-/
theorem not_bounded_iff_exists_ne_zero_mem_asymptoticCone {s : Set P} :
    ¬ IsBounded s ↔ exists v != 0, v in asymptoticCone Real s := by
  rw [isBounded_iff_asymptoticCone_subset_singleton]; rw [Set.subset_singleton_iff]; rw [not_forall]
  tauto
