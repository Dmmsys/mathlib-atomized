/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Topology.Continuous

/-! # Characterization of basic topological properties in terms of ultrafilters -/

public section

open Set Filter Topology

universe u v w x

variable {X : Type u} {Y : Type v} {ι : Sort w} {α β : Type*} {x : X} {s s₁ s₂ t : Set X}
    {p p₁ p₂ : X -> Prop} [TopologicalSpace X] [TopologicalSpace Y] {F : Filter α} {u : α -> X}

/--
theorem `Ultrafilter.clusterPt_iff` / 定理 `Ultrafilter.clusterPt_iff`

English:
theorem Ultrafilter.clusterPt_iff
  given: {f : Ultrafilter X}
  statement: ClusterPt x f ↔ ↑f <= 𝓝 x
  proof: ⟨f.le_of_inf_neBot', fun h => ClusterPt.of_le_nhds h⟩

中文:
定理 Ultrafilter.clusterPt_iff
  条件: {f : Ultrafilter X}
  结论: ClusterPt x f ↔ ↑f <= 𝓝 x
  证明: ⟨f.le_of_inf_neBot', fun h => ClusterPt.of_le_nhds h⟩

Depends on / 依赖: ClusterPt, ClusterPt.of_le_nhds, f.le_of_inf_neBot, le_of_inf_neBot, of_le_nhds
-/
theorem Ultrafilter.clusterPt_iff {f : Ultrafilter X} : ClusterPt x f ↔ ↑f <= 𝓝 x :=
  ⟨f.le_of_inf_neBot', fun h => ClusterPt.of_le_nhds h⟩

/--
theorem `clusterPt_iff_ultrafilter` / 定理 `clusterPt_iff_ultrafilter`

English:
theorem clusterPt_iff_ultrafilter
  given: {f : Filter X}
  statement: ClusterPt x f ↔
  proof: by
  simp_rw [ClusterPt, ← le_inf_iff, exists_ultrafilter_iff, inf_comm]

中文:
定理 clusterPt_iff_ultrafilter
  条件: {f : Filter X}
  结论: ClusterPt x f ↔
  证明: by
  simp_rw [ClusterPt, ← le_inf_iff, exists_ultrafilter_iff, inf_comm]

Depends on / 依赖: ClusterPt, exists_ultrafilter_iff, inf_comm, le_inf_iff, simp_rw
-/
theorem clusterPt_iff_ultrafilter {f : Filter X} : ClusterPt x f ↔
    exists u : Ultrafilter X, u <= f ∧ u <= 𝓝 x := by
  simp_rw [ClusterPt, ← le_inf_iff, exists_ultrafilter_iff, inf_comm]

/--
theorem `mapClusterPt_iff_ultrafilter` / 定理 `mapClusterPt_iff_ultrafilter`

English:
theorem mapClusterPt_iff_ultrafilter
  proof: by
  simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, tendsto_iff_comap,
    ← le_inf_iff, exists_ultrafilter_iff, inf_comm]

中文:
定理 mapClusterPt_iff_ultrafilter
  证明: by
  simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, tendsto_iff_comap,
    ← le_inf_iff, exists_ultrafilter_iff, inf_comm]

Depends on / 依赖: ClusterPt, Filter, Filter.push_pull, MapClusterPt, exists_ultrafilter_iff, inf_comm, le_inf_iff, map_neBot_iff, push_pull, simp_rw, tendsto_iff_comap
-/
theorem mapClusterPt_iff_ultrafilter :
    MapClusterPt x F u ↔ exists U : Ultrafilter α, U <= F ∧ Tendsto u U (𝓝 x) := by
  simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, tendsto_iff_comap,
    ← le_inf_iff, exists_ultrafilter_iff, inf_comm]

/--
theorem `isOpen_iff_ultrafilter` / 定理 `isOpen_iff_ultrafilter`

English:
theorem isOpen_iff_ultrafilter
  proof: by
  simp_rw [isOpen_iff_mem_nhds, ← mem_iff_ultrafilter]

中文:
定理 isOpen_iff_ultrafilter
  证明: by
  simp_rw [isOpen_iff_mem_nhds, ← mem_iff_ultrafilter]

Depends on / 依赖: isOpen_iff_mem_nhds, mem_iff_ultrafilter, simp_rw
-/
theorem isOpen_iff_ultrafilter :
    IsOpen s ↔ forall x in s, forall (l : Ultrafilter X), ↑l <= 𝓝 x -> s in l := by
  simp_rw [isOpen_iff_mem_nhds, ← mem_iff_ultrafilter]

/--
theorem `mem_closure_iff_ultrafilter` / 定理 `mem_closure_iff_ultrafilter`

English:
theorem mem_closure_iff_ultrafilter
  proof: by
  simp [closure_eq_cluster_pts, ClusterPt, ← exists_ultrafilter_iff, and_comm]

中文:
定理 mem_closure_iff_ultrafilter
  证明: by
  simp [closure_eq_cluster_pts, ClusterPt, ← exists_ultrafilter_iff, and_comm]

Depends on / 依赖: ClusterPt, and_comm, closure_eq_cluster_pts, exists_ultrafilter_iff
-/
theorem mem_closure_iff_ultrafilter :
    x in closure s ↔ exists u : Ultrafilter X, s in u ∧ ↑u <= 𝓝 x := by
  simp [closure_eq_cluster_pts, ClusterPt, ← exists_ultrafilter_iff, and_comm]

/--
theorem `isClosed_iff_ultrafilter` / 定理 `isClosed_iff_ultrafilter`

English:
theorem isClosed_iff_ultrafilter
  statement: IsClosed s ↔
  proof: by
  simp [isClosed_iff_clusterPt, ClusterPt, ← exists_ultrafilter_iff]

中文:
定理 isClosed_iff_ultrafilter
  结论: IsClosed s ↔
  证明: by
  simp [isClosed_iff_clusterPt, ClusterPt, ← exists_ultrafilter_iff]

Depends on / 依赖: ClusterPt, exists_ultrafilter_iff, isClosed_iff_clusterPt
-/
theorem isClosed_iff_ultrafilter : IsClosed s ↔
    forall x, forall u : Ultrafilter X, ↑u <= 𝓝 x -> s in u -> x in s := by
  simp [isClosed_iff_clusterPt, ClusterPt, ← exists_ultrafilter_iff]

variable {f : X -> Y}

/--
theorem `continuousAt_iff_ultrafilter` / 定理 `continuousAt_iff_ultrafilter`

English:
theorem continuousAt_iff_ultrafilter
  proof: tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))

中文:
定理 continuousAt_iff_ultrafilter
  证明: tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))

Depends on / 依赖: tendsto_iff_ultrafilter
-/
theorem continuousAt_iff_ultrafilter :
    ContinuousAt f x ↔ forall g : Ultrafilter X, ↑g <= 𝓝 x -> Tendsto f g (𝓝 (f x)) :=
  tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))

/--
theorem `continuous_iff_ultrafilter` / 定理 `continuous_iff_ultrafilter`

English:
theorem continuous_iff_ultrafilter
  proof: by
  simp only [continuous_iff_continuousAt, continuousAt_iff_ultrafilter]

中文:
定理 continuous_iff_ultrafilter
  证明: by
  simp only [continuous_iff_continuousAt, continuousAt_iff_ultrafilter]

Depends on / 依赖: continuousAt_iff_ultrafilter, continuous_iff_continuousAt
-/
theorem continuous_iff_ultrafilter :
    Continuous f ↔ forall (x) (g : Ultrafilter X), ↑g <= 𝓝 x -> Tendsto f g (𝓝 (f x)) := by
  simp only [continuous_iff_continuousAt, continuousAt_iff_ultrafilter]
