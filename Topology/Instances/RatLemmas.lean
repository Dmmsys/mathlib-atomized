/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Instances.Irrational
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Additional lemmas about the topology on rational numbers

The structure of a metric space on `ℚ` (`Rat.MetricSpace`) is introduced elsewhere, induced from
`ℝ`. In this file we prove some properties of this topological space and its one-point
compactification.

## Main statements

- `Rat.TotallyDisconnectedSpace`: `ℚ` is a totally disconnected space;

- `Rat.not_countably_generated_nhds_infty_opc`: the filter of neighbourhoods of infinity in
  `OnePoint ℚ` is not countably generated.

## Notation

- `ℚ∞` is used as a local notation for `OnePoint ℚ`
-/

public section


open Set Metric Filter TopologicalSpace

open Topology OnePoint

local notation "Rat∞" => OnePoint Rat

namespace Rat

variable {p : Rat} {s : Set Rat}

/--
theorem `interior_compact_eq_empty` / 定理 `interior_compact_eq_empty`

English:
theorem interior_compact_eq_empty
  given: (hs : IsCompact s)
  statement: interior s = ∅
  proof: isDenseEmbedding_coe_real.isDenseInducing.interior_compact_eq_empty dense_irrational hs

中文:
定理 interior_compact_eq_empty
  条件: (hs : 是紧集 s)
  结论: interior s = ∅
  证明: isDenseEmbedding_coe_real.isDenseInducing.interior_compact_eq_empty dense_irrational hs

Depends on / 依赖: dense_irrational, interior_compact_eq_empty, isDenseEmbedding_coe_real, isDenseEmbedding_coe_real.isDenseInducing.interior_compact_eq_empty, isDenseInducing
-/
theorem interior_compact_eq_empty (hs : IsCompact s) : interior s = ∅ :=
  isDenseEmbedding_coe_real.isDenseInducing.interior_compact_eq_empty dense_irrational hs

/--
theorem `dense_compl_compact` / 定理 `dense_compl_compact`

English:
theorem dense_compl_compact
  given: (hs : IsCompact s)
  statement: Dense sᶜ
  proof: interior_eq_empty_iff_dense_compl.1 (interior_compact_eq_empty hs)

中文:
定理 dense_compl_compact
  条件: (hs : 是紧集 s)
  结论: 稠密 sᶜ
  证明: interior_eq_empty_iff_dense_compl.1 (interior_compact_eq_empty hs)

Depends on / 依赖: interior_compact_eq_empty, interior_eq_empty_iff_dense_compl
-/
theorem dense_compl_compact (hs : IsCompact s) : Dense sᶜ :=
  interior_eq_empty_iff_dense_compl.1 (interior_compact_eq_empty hs)

/--
Instance `cocompact_inf_nhds_neBot` / 实例 `cocompact_inf_nhds_neBot`

English:
instance cocompact_inf_nhds_neBot
  signature: : NeBot (cocompact Rat ⊓ 𝓝 p)
  body: by
  refine (hasBasis_cocompact.inf (nhds_basis_opens _)).neBot_iff.2 ?_
  rintro ⟨s, o⟩ ⟨hs, hpo, ho⟩; rw [inter_comm]
  exact (dense_compl_compact hs).inter_open_nonempty _ ho ⟨p, hpo⟩

中文:
实例 cocompact_inf_nhds_neBot
  签名: : NeBot (cocompact 有理数 ⊓ 𝓝 p)
  定义体: by
  refine (hasBasis_cocompact.inf (nhds_basis_opens _)).neBot_iff.2 ?_
  rintro ⟨s, o⟩ ⟨hs, hpo, ho⟩; rw [inter_comm]
  exact (dense_compl_compact hs).inter_open_nonempty _ ho ⟨p, hpo⟩

Depends on / 依赖: dense_compl_compact, hasBasis_cocompact, hasBasis_cocompact.inf, inter_comm, inter_open_nonempty, neBot_iff, nhds_basis_opens
-/
instance cocompact_inf_nhds_neBot : NeBot (cocompact Rat ⊓ 𝓝 p) := by
  refine (hasBasis_cocompact.inf (nhds_basis_opens _)).neBot_iff.2 ?_
  rintro ⟨s, o⟩ ⟨hs, hpo, ho⟩; rw [inter_comm]
  exact (dense_compl_compact hs).inter_open_nonempty _ ho ⟨p, hpo⟩

/--
theorem `not_countably_generated_cocompact` / 定理 `not_countably_generated_cocompact`

English:
theorem not_countably_generated_cocompact
  statement: ¬IsCountablyGenerated (cocompact Rat)
  proof: by
  intro H
  rcases exists_seq_tendsto (cocompact Rat ⊓ 𝓝 0) with ⟨x, hx⟩
  rw [tendsto_inf] at hx; rcases hx with ⟨hxc, hx0⟩
  obtain ⟨n, hn⟩ : exists n : Nat, x n ∉ insert (0 : Rat) (range x) :=
    (hxc.eventually hx0.isCompact_insert_range.compl_mem_cocompact).exists
  exact hn (Or.inr ⟨n, rfl

中文:
定理 not_countably_generated_cocompact
  结论: ¬是余untablyGenerated (cocompact 有理数)
  证明: by
  intro H
  rcases exists_seq_tendsto (cocompact Rat ⊓ 𝓝 0) with ⟨x, hx⟩
  rw [tendsto_inf] at hx; rcases hx with ⟨hxc, hx0⟩
  obtain ⟨n, hn⟩ : exists n : Nat, x n ∉ insert (0 : Rat) (range x) :=
    (hxc.eventually hx0.isCompact_insert_range.compl_mem_cocompact).exists
  exact hn (Or.inr ⟨n, rfl

Depends on / 依赖: Or.inr, cocompact, compl_mem_cocompact, eventually, exists_seq_tendsto, hx0.isCompact_insert_range.compl_mem_cocompact, hxc.eventually, insert, isCompact_insert_range, tendsto_inf
-/
theorem not_countably_generated_cocompact : ¬IsCountablyGenerated (cocompact Rat) := by
  intro H
  rcases exists_seq_tendsto (cocompact Rat ⊓ 𝓝 0) with ⟨x, hx⟩
  rw [tendsto_inf] at hx; rcases hx with ⟨hxc, hx0⟩
  obtain ⟨n, hn⟩ : exists n : Nat, x n ∉ insert (0 : Rat) (range x) :=
    (hxc.eventually hx0.isCompact_insert_range.compl_mem_cocompact).exists
  exact hn (Or.inr ⟨n, rfl⟩)

/--
theorem `not_countably_generated_nhds_infty_opc` / 定理 `not_countably_generated_nhds_infty_opc`

English:
theorem not_countably_generated_nhds_infty_opc
  statement: ¬IsCountablyGenerated (𝓝 (∞ : Rat∞))
  proof: by
  intro
  have : IsCountablyGenerated (comap (OnePoint.some : Rat -> Rat∞) (𝓝 ∞)) := by infer_instance
  rw [OnePoint.comap_coe_nhds_infty]; rw [coclosedCompact_eq_cocompact] at this
  exact not_countably_generated_cocompact this

中文:
定理 not_countably_generated_nhds_infty_opc
  结论: ¬是余untablyGenerated (𝓝 (∞ : 有理数∞))
  证明: by
  intro
  have : IsCountablyGenerated (comap (OnePoint.some : Rat -> Rat∞) (𝓝 ∞)) := by infer_instance
  rw [OnePoint.comap_coe_nhds_infty]; rw [coclosedCompact_eq_cocompact] at this
  exact not_countably_generated_cocompact this

Depends on / 依赖: IsCountablyGenerated, OnePoint, OnePoint.comap_coe_nhds_infty, OnePoint.some, coclosedCompact_eq_cocompact, comap_coe_nhds_infty, infer_instance, not_countably_generated_cocompact
-/
theorem not_countably_generated_nhds_infty_opc : ¬IsCountablyGenerated (𝓝 (∞ : Rat∞)) := by
  intro
  have : IsCountablyGenerated (comap (OnePoint.some : Rat -> Rat∞) (𝓝 ∞)) := by infer_instance
  rw [OnePoint.comap_coe_nhds_infty]; rw [coclosedCompact_eq_cocompact] at this
  exact not_countably_generated_cocompact this

/--
theorem `not_firstCountableTopology_opc` / 定理 `not_firstCountableTopology_opc`

English:
theorem not_firstCountableTopology_opc
  statement: ¬FirstCountableTopology Rat∞
  proof: by
  intro
  exact not_countably_generated_nhds_infty_opc inferInstance

中文:
定理 not_firstCountableTopology_opc
  结论: ¬第一可数拓扑 有理数∞
  证明: by
  intro
  exact not_countably_generated_nhds_infty_opc inferInstance

Depends on / 依赖: not_countably_generated_nhds_infty_opc
-/
theorem not_firstCountableTopology_opc : ¬FirstCountableTopology Rat∞ := by
  intro
  exact not_countably_generated_nhds_infty_opc inferInstance

/--
theorem `not_secondCountableTopology_opc` / 定理 `not_secondCountableTopology_opc`

English:
theorem not_secondCountableTopology_opc
  statement: ¬SecondCountableTopology Rat∞
  proof: by
  intro
  exact not_firstCountableTopology_opc inferInstance

中文:
定理 not_secondCountableTopology_opc
  结论: ¬第二可数拓扑 有理数∞
  证明: by
  intro
  exact not_firstCountableTopology_opc inferInstance

Depends on / 依赖: not_firstCountableTopology_opc
-/
theorem not_secondCountableTopology_opc : ¬SecondCountableTopology Rat∞ := by
  intro
  exact not_firstCountableTopology_opc inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TotallyDisconnectedSpace Rat
  body: by
  clear p s
  refine ⟨fun s hsu hs x hx y hy => ?_⟩; clear hsu
  by_contra H : x != y
  wlog hlt : x < y
· apply this s hs y hy x hx H.symm H.lt_or_gt.resolve_left hlt
  rcases exists_irrational_btwn (Rat.cast_lt.2 hlt) with ⟨z, hz, hxz, hzy⟩
  have := hs.image _ continuous_coe_real.continuousOn


中文:
实例 :
  签名: 全不连通空间 有理数
  定义体: by
  clear p s
  refine ⟨fun s hsu hs x hx y hy => ?_⟩; clear hsu
  by_contra H : x != y
  wlog hlt : x < y
· apply this s hs y hy x hx H.symm H.lt_or_gt.resolve_left hlt
  rcases exists_irrational_btwn (Rat.cast_lt.2 hlt) with ⟨z, hz, hxz, hzy⟩
  have := hs.image _ continuous_coe_real.continuousOn


Depends on / 依赖: H.lt_or_gt.resolve_left, H.symm, Rat.cast, Rat.cast_lt, cast_lt, continuousOn, continuous_coe_real, continuous_coe_real.continuousOn, exists_irrational_btwn, hs.image, hxz.le, hzy.le, image_subset_range, isPreconnected_iff_ordConnected, lt_or_gt, mem_image_of_mem, resolve_left, this.out
-/
instance : TotallyDisconnectedSpace Rat := by
  clear p s
  refine ⟨fun s hsu hs x hx y hy => ?_⟩; clear hsu
  by_contra H : x != y
  wlog hlt : x < y
· apply this s hs y hy x hx H.symm H.lt_or_gt.resolve_left hlt
  rcases exists_irrational_btwn (Rat.cast_lt.2 hlt) with ⟨z, hz, hxz, hzy⟩
  have := hs.image _ continuous_coe_real.continuousOn
  rw [isPreconnected_iff_ordConnected] at this
  have : z in Rat.cast '' s :=
    this.out (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) ⟨hxz.le, hzy.le⟩
  exact hz (image_subset_range _ _ this)

end Rat
