/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Topology.Neighborhoods

/-!
# Lemmas on cluster and accumulation points

In this file we prove various lemmas on [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.

A filter `F` on `X` has `x` as a cluster point if `ClusterPt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : α → X`
clusters at `x` along `F : Filter α` if `MapClusterPt x F f : ClusterPt x (map f F)`.
In particular the notion of cluster point of a sequence `u` is `MapClusterPt x atTop u`.
-/

public section

open Set Filter Topology

universe u v w

variable {X : Type u} [TopologicalSpace X] {Y : Type v} {ι : Sort w} {α β : Type*}
  {x : X} {s s₁ s₂ t : Set X}

@[simp]
/--
lemma `ClusterPt.top` / 引理 `ClusterPt.top`

English:
lemma ClusterPt.top
  statement: ClusterPt x ⊤
  proof: by simp [ClusterPt]

中文:
引理 ClusterPt.top
  结论: ClusterPt x ⊤
  证明: by simp [ClusterPt]
-/
protected lemma ClusterPt.top : ClusterPt x ⊤ := by simp [ClusterPt]

/--
theorem `clusterPt_sup` / 定理 `clusterPt_sup`

English:
theorem clusterPt_sup
  given: {F G : Filter X}
  statement: ClusterPt x (F ⊔ G) ↔ ClusterPt x F ∨ ClusterPt x G
  proof: by
  simp only [ClusterPt, inf_sup_left, sup_neBot]

中文:
定理 clusterPt_sup
  条件: {F G : 滤子 X}
  结论: ClusterPt x (F ⊔ G) ↔ ClusterPt x F ∨ ClusterPt x G
  证明: by
  simp only [ClusterPt, inf_sup_left, sup_neBot]

Depends on / 依赖: ClusterPt, inf_sup_left, sup_neBot
-/
theorem clusterPt_sup {F G : Filter X} : ClusterPt x (F ⊔ G) ↔ ClusterPt x F ∨ ClusterPt x G := by
  simp only [ClusterPt, inf_sup_left, sup_neBot]

/--
theorem `ClusterPt.neBot` / 定理 `ClusterPt.neBot`

English:
theorem ClusterPt.neBot
  given: {F : Filter X} (h : ClusterPt x F)
  statement: NeBot (𝓝 x ⊓ F)
  proof: h

中文:
定理 ClusterPt.neBot
  条件: {F : 滤子 X} (h : ClusterPt x F)
  结论: NeBot (𝓝 x ⊓ F)
  证明: h
-/
theorem ClusterPt.neBot {F : Filter X} (h : ClusterPt x F) : NeBot (𝓝 x ⊓ F) :=
  h

/--
theorem `Filter.HasBasis.clusterPt_iff` / 定理 `Filter.HasBasis.clusterPt_iff`

English:
theorem Filter.HasBasis.clusterPt_iff
  statement: {ιX ιF} {pX : ιX -> Prop} {sX : ιX -> Set X} {pF : ιF -> Prop}
  proof: hX.inf_basis_neBot_iff hF

中文:
定理 滤子.有基.clusterPt_iff
  结论: {ιX ιF} {pX : ιX -> 命题} {sX : ιX -> 集合 X} {pF : ιF -> 命题}
  证明: hX.inf_basis_neBot_iff hF

Depends on / 依赖: hX.inf_basis_neBot_iff, inf_basis_neBot_iff
-/
theorem Filter.HasBasis.clusterPt_iff {ιX ιF} {pX : ιX -> Prop} {sX : ιX -> Set X} {pF : ιF -> Prop}
    {sF : ιF -> Set X} {F : Filter X} (hX : (𝓝 x).HasBasis pX sX) (hF : F.HasBasis pF sF) :
    ClusterPt x F ↔ forall ⦃i⦄, pX i -> forall ⦃j⦄, pF j -> (sX i inter sF j).Nonempty :=
  hX.inf_basis_neBot_iff hF

/--
theorem `Filter.HasBasis.clusterPt_iff_frequently` / 定理 `Filter.HasBasis.clusterPt_iff_frequently`

English:
theorem Filter.HasBasis.clusterPt_iff_frequently
  statement: {ι} {p : ι -> Prop} {s : ι -> Set X} {F : Filter X}
  proof: by
  simp only [hx.clusterPt_iff F.basis_sets, Filter.frequently_iff, inter_comm (s _),
    Set.Nonempty, id, mem_inter_iff]

中文:
定理 滤子.有基.clusterPt_iff_frequently
  结论: {ι} {p : ι -> 命题} {s : ι -> 集合 X} {F : 滤子 X}
  证明: by
  simp only [hx.clusterPt_iff F.basis_sets, Filter.frequently_iff, inter_comm (s _),
    Set.Nonempty, id, mem_inter_iff]

Depends on / 依赖: F.basis_sets, Filter, Filter.frequently_iff, Nonempty, Set.Nonempty, basis_sets, clusterPt_iff, frequently_iff, hx.clusterPt_iff, inter_comm, mem_inter_iff
-/
theorem Filter.HasBasis.clusterPt_iff_frequently {ι} {p : ι -> Prop} {s : ι -> Set X} {F : Filter X}
    (hx : (𝓝 x).HasBasis p s) : ClusterPt x F ↔ forall i, p i -> existsᶠ x in F, x in s i := by
  simp only [hx.clusterPt_iff F.basis_sets, Filter.frequently_iff, inter_comm (s _),
    Set.Nonempty, id, mem_inter_iff]

/--
theorem `clusterPt_iff_frequently` / 定理 `clusterPt_iff_frequently`

English:
theorem clusterPt_iff_frequently
  given: {F : Filter X}
  statement: ClusterPt x F ↔ forall s in 𝓝 x, existsᶠ y in F, y in s
  proof: (𝓝 x).basis_sets.clusterPt_iff_frequently

中文:
定理 clusterPt_iff_frequently
  条件: {F : 滤子 X}
  结论: ClusterPt x F ↔ 对任意 s in 𝓝 x, 存在ᶠ y in F, y in s
  证明: (𝓝 x).basis_sets.clusterPt_iff_frequently

Depends on / 依赖: basis_sets, basis_sets.clusterPt_iff_frequently, clusterPt_iff_frequently
-/
theorem clusterPt_iff_frequently {F : Filter X} : ClusterPt x F ↔ forall s in 𝓝 x, existsᶠ y in F, y in s :=
  (𝓝 x).basis_sets.clusterPt_iff_frequently

/--
theorem `ClusterPt.frequently` / 定理 `ClusterPt.frequently`

English:
theorem ClusterPt.frequently
  statement: {F : Filter X} {p : X -> Prop} (hx : ClusterPt x F)
  proof: clusterPt_iff_frequently.mp hx {y | p y} hp

中文:
定理 ClusterPt.frequently
  结论: {F : 滤子 X} {p : X -> 命题} (hx : ClusterPt x F)
  证明: clusterPt_iff_frequently.mp hx {y | p y} hp

Depends on / 依赖: clusterPt_iff_frequently, clusterPt_iff_frequently.mp
-/
theorem ClusterPt.frequently {F : Filter X} {p : X -> Prop} (hx : ClusterPt x F)
    (hp : forallᶠ y in 𝓝 x, p y) : existsᶠ y in F, p y :=
  clusterPt_iff_frequently.mp hx {y | p y} hp

/--
theorem `Filter.HasBasis.clusterPt_iff_frequently'` / 定理 `Filter.HasBasis.clusterPt_iff_frequently'`

English:
theorem Filter.HasBasis.clusterPt_iff_frequently'
  statement: {ι} {p : ι -> Prop} {s : ι -> Set X} {F : Filter X}
  proof: by
  simp only [(𝓝 x).basis_sets.clusterPt_iff hx, Filter.frequently_iff]
  exact ⟨fun h a b c d => h d b, fun h a b c d => h c d b⟩

中文:
定理 滤子.有基.clusterPt_iff_frequently'
  结论: {ι} {p : ι -> 命题} {s : ι -> 集合 X} {F : 滤子 X}
  证明: by
  simp only [(𝓝 x).basis_sets.clusterPt_iff hx, Filter.frequently_iff]
  exact ⟨fun h a b c d => h d b, fun h a b c d => h c d b⟩

Depends on / 依赖: Filter, Filter.frequently_iff, basis_sets, basis_sets.clusterPt_iff, clusterPt_iff, frequently_iff
-/
theorem Filter.HasBasis.clusterPt_iff_frequently' {ι} {p : ι -> Prop} {s : ι -> Set X} {F : Filter X}
    (hx : F.HasBasis p s) : ClusterPt x F ↔ forall i, p i -> existsᶠ x in 𝓝 x, x in s i := by
  simp only [(𝓝 x).basis_sets.clusterPt_iff hx, Filter.frequently_iff]
  exact ⟨fun h a b c d => h d b, fun h a b c d => h c d b⟩

/--
theorem `clusterPt_iff_frequently'` / 定理 `clusterPt_iff_frequently'`

English:
theorem clusterPt_iff_frequently'
  given: {F : Filter X}
  statement: ClusterPt x F ↔ forall s in F, existsᶠ y in 𝓝 x, y in s
  proof: F.basis_sets.clusterPt_iff_frequently'

中文:
定理 clusterPt_iff_frequently'
  条件: {F : 滤子 X}
  结论: ClusterPt x F ↔ 对任意 s in F, 存在ᶠ y in 𝓝 x, y in s
  证明: F.basis_sets.clusterPt_iff_frequently'

Depends on / 依赖: F.basis_sets.clusterPt_iff_frequently, basis_sets, clusterPt_iff_frequently
-/
theorem clusterPt_iff_frequently' {F : Filter X} : ClusterPt x F ↔ forall s in F, existsᶠ y in 𝓝 x, y in s :=
  F.basis_sets.clusterPt_iff_frequently'

/--
theorem `ClusterPt.frequently'` / 定理 `ClusterPt.frequently'`

English:
theorem ClusterPt.frequently'
  statement: {F : Filter X} {p : X -> Prop} (hx : ClusterPt x F)
  proof: clusterPt_iff_frequently'.mp hx {y | p y} hp

中文:
定理 ClusterPt.frequently'
  结论: {F : 滤子 X} {p : X -> 命题} (hx : ClusterPt x F)
  证明: clusterPt_iff_frequently'.mp hx {y | p y} hp

Depends on / 依赖: clusterPt_iff_frequently
-/
theorem ClusterPt.frequently' {F : Filter X} {p : X -> Prop} (hx : ClusterPt x F)
    (hp : forallᶠ y in F, p y) : existsᶠ y in 𝓝 x, p y :=
  clusterPt_iff_frequently'.mp hx {y | p y} hp

/--
theorem `clusterPt_iff_nonempty` / 定理 `clusterPt_iff_nonempty`

English:
theorem clusterPt_iff_nonempty
  given: {F : Filter X}
  proof: inf_neBot_iff

中文:
定理 clusterPt_iff_nonempty
  条件: {F : 滤子 X}
  证明: inf_neBot_iff

Depends on / 依赖: inf_neBot_iff
-/
theorem clusterPt_iff_nonempty {F : Filter X} :
    ClusterPt x F ↔ forall ⦃U : Set X⦄, U in 𝓝 x -> forall ⦃V⦄, V in F -> (U inter V).Nonempty :=
  inf_neBot_iff

/--
theorem `clusterPt_iff_not_disjoint` / 定理 `clusterPt_iff_not_disjoint`

English:
theorem clusterPt_iff_not_disjoint
  given: {F : Filter X}
  proof: by
  rw [disjoint_iff]; rw [ClusterPt]; rw [neBot_iff]

中文:
定理 clusterPt_iff_not_disjoint
  条件: {F : 滤子 X}
  证明: by
  rw [disjoint_iff]; rw [ClusterPt]; rw [neBot_iff]

Depends on / 依赖: ClusterPt, disjoint_iff, neBot_iff
-/
theorem clusterPt_iff_not_disjoint {F : Filter X} :
    ClusterPt x F ↔ ¬Disjoint (𝓝 x) F := by
  rw [disjoint_iff]; rw [ClusterPt]; rw [neBot_iff]

/--
theorem `Filter.HasBasis.clusterPt_iff_forall_mem_closure` / 定理 `Filter.HasBasis.clusterPt_iff_forall_mem_closure`

English:
theorem Filter.HasBasis.clusterPt_iff_forall_mem_closure
  statement: {ι} {p : ι -> Prop}
  proof: by
  simp only [(nhds_basis_opens _).clusterPt_iff hF, mem_closure_iff]
  tauto

中文:
定理 滤子.有基.clusterPt_iff_对任意_mem_closure
  结论: {ι} {p : ι -> 命题}
  证明: by
  simp only [(nhds_basis_opens _).clusterPt_iff hF, mem_closure_iff]
  tauto
-/
protected theorem Filter.HasBasis.clusterPt_iff_forall_mem_closure {ι} {p : ι -> Prop}
    {s : ι -> Set X} {F : Filter X} (hF : F.HasBasis p s) :
    ClusterPt x F ↔ forall i, p i -> x in closure (s i) := by
  simp only [(nhds_basis_opens _).clusterPt_iff hF, mem_closure_iff]
  tauto

/--
theorem `clusterPt_iff_forall_mem_closure` / 定理 `clusterPt_iff_forall_mem_closure`

English:
theorem clusterPt_iff_forall_mem_closure
  given: {F : Filter X}
  proof: F.basis_sets.clusterPt_iff_forall_mem_closure

alias ⟨ClusterPt.mem_closure_of_mem, _⟩ := clusterPt_iff_forall_mem_closure

中文:
定理 clusterPt_iff_对任意_mem_closure
  条件: {F : 滤子 X}
  证明: F.basis_sets.clusterPt_iff_forall_mem_closure

alias ⟨ClusterPt.mem_closure_of_mem, _⟩ := clusterPt_iff_forall_mem_closure

Depends on / 依赖: F.basis_sets.clusterPt_iff_forall_mem_closure, basis_sets, clusterPt_iff_forall_mem_closure
-/
theorem clusterPt_iff_forall_mem_closure {F : Filter X} :
    ClusterPt x F ↔ forall s in F, x in closure s :=
  F.basis_sets.clusterPt_iff_forall_mem_closure

alias ⟨ClusterPt.mem_closure_of_mem, _⟩ := clusterPt_iff_forall_mem_closure

/--
theorem `clusterPt_principal_iff` / 定理 `clusterPt_principal_iff`

English:
theorem clusterPt_principal_iff
  proof: inf_principal_neBot_iff

中文:
定理 clusterPt_principal_iff
  证明: inf_principal_neBot_iff

Depends on / 依赖: inf_principal_neBot_iff
-/
theorem clusterPt_principal_iff :
    ClusterPt x (𝓟 s) ↔ forall U in 𝓝 x, (U inter s).Nonempty :=
  inf_principal_neBot_iff

/--
theorem `clusterPt_principal_iff_frequently` / 定理 `clusterPt_principal_iff_frequently`

English:
theorem clusterPt_principal_iff_frequently
  proof: by
  simp only [clusterPt_principal_iff, frequently_iff, Set.Nonempty, mem_inter_iff]

中文:
定理 clusterPt_principal_iff_frequently
  证明: by
  simp only [clusterPt_principal_iff, frequently_iff, Set.Nonempty, mem_inter_iff]

Depends on / 依赖: Nonempty, Set.Nonempty, clusterPt_principal_iff, frequently_iff, mem_inter_iff
-/
theorem clusterPt_principal_iff_frequently :
    ClusterPt x (𝓟 s) ↔ existsᶠ y in 𝓝 x, y in s := by
  simp only [clusterPt_principal_iff, frequently_iff, Set.Nonempty, mem_inter_iff]

/--
theorem `ClusterPt.of_le_nhds` / 定理 `ClusterPt.of_le_nhds`

English:
theorem ClusterPt.of_le_nhds
  given: {f : Filter X} (H : f <= 𝓝 x) [NeBot f]
  statement: ClusterPt x f
  proof: by
  rwa [ClusterPt, inf_eq_right.mpr H]

中文:
定理 ClusterPt.of_le_nhds
  条件: {f : 滤子 X} (H : f <= 𝓝 x) [NeBot f]
  结论: ClusterPt x f
  证明: by
  rwa [ClusterPt, inf_eq_right.mpr H]

Depends on / 依赖: ClusterPt, inf_eq_right, inf_eq_right.mpr
-/
theorem ClusterPt.of_le_nhds {f : Filter X} (H : f <= 𝓝 x) [NeBot f] : ClusterPt x f := by
  rwa [ClusterPt, inf_eq_right.mpr H]

/--
theorem `ClusterPt.of_le_nhds'` / 定理 `ClusterPt.of_le_nhds'`

English:
theorem ClusterPt.of_le_nhds'
  given: {f : Filter X} (H : f <= 𝓝 x) (_hf : NeBot f)
  proof: ClusterPt.of_le_nhds H

中文:
定理 ClusterPt.of_le_nhds'
  条件: {f : 滤子 X} (H : f <= 𝓝 x) (_hf : NeBot f)
  证明: ClusterPt.of_le_nhds H

Depends on / 依赖: ClusterPt, ClusterPt.of_le_nhds, of_le_nhds
-/
theorem ClusterPt.of_le_nhds' {f : Filter X} (H : f <= 𝓝 x) (_hf : NeBot f) :
    ClusterPt x f :=
  ClusterPt.of_le_nhds H

/--
theorem `ClusterPt.of_nhds_le` / 定理 `ClusterPt.of_nhds_le`

English:
theorem ClusterPt.of_nhds_le
  given: {f : Filter X} (H : 𝓝 x <= f)
  statement: ClusterPt x f
  proof: by
  simp only [ClusterPt, inf_eq_left.mpr H, nhds_neBot]

中文:
定理 ClusterPt.of_nhds_le
  条件: {f : 滤子 X} (H : 𝓝 x <= f)
  结论: ClusterPt x f
  证明: by
  simp only [ClusterPt, inf_eq_left.mpr H, nhds_neBot]

Depends on / 依赖: ClusterPt, inf_eq_left, inf_eq_left.mpr, nhds_neBot
-/
theorem ClusterPt.of_nhds_le {f : Filter X} (H : 𝓝 x <= f) : ClusterPt x f := by
  simp only [ClusterPt, inf_eq_left.mpr H, nhds_neBot]

/--
theorem `ClusterPt.mono` / 定理 `ClusterPt.mono`

English:
theorem ClusterPt.mono
  given: {f g : Filter X} (H : ClusterPt x f) (h : f <= g)
  statement: ClusterPt x g
  proof: NeBot.mono H inf_le_inf_left _ h

中文:
定理 ClusterPt.mono
  条件: {f g : 滤子 X} (H : ClusterPt x f) (h : f <= g)
  结论: ClusterPt x g
  证明: NeBot.mono H inf_le_inf_left _ h

Depends on / 依赖: NeBot.mono, inf_le_inf_left
-/
theorem ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h : f <= g) : ClusterPt x g :=
NeBot.mono H inf_le_inf_left _ h

/--
theorem `ClusterPt.of_inf_left` / 定理 `ClusterPt.of_inf_left`

English:
theorem ClusterPt.of_inf_left
  given: {f g : Filter X} (H : ClusterPt x <| f ⊓ g)
  statement: ClusterPt x f
  proof: H.mono inf_le_left

中文:
定理 ClusterPt.of_inf_left
  条件: {f g : 滤子 X} (H : ClusterPt x <| f ⊓ g)
  结论: ClusterPt x f
  证明: H.mono inf_le_left

Depends on / 依赖: H.mono, inf_le_left
-/
theorem ClusterPt.of_inf_left {f g : Filter X} (H : ClusterPt x <| f ⊓ g) : ClusterPt x f :=
  H.mono inf_le_left

/--
theorem `ClusterPt.of_inf_right` / 定理 `ClusterPt.of_inf_right`

English:
theorem ClusterPt.of_inf_right
  given: {f g : Filter X} (H : ClusterPt x <| f ⊓ g)
  proof: H.mono inf_le_right

中文:
定理 ClusterPt.of_inf_right
  条件: {f g : 滤子 X} (H : ClusterPt x <| f ⊓ g)
  证明: H.mono inf_le_right

Depends on / 依赖: H.mono, inf_le_right
-/
theorem ClusterPt.of_inf_right {f g : Filter X} (H : ClusterPt x <| f ⊓ g) :
    ClusterPt x g :=
  H.mono inf_le_right

section MapClusterPt

variable {F : Filter α} {u : α -> X} {x : X}

/--
theorem `mapClusterPt_def` / 定理 `mapClusterPt_def`

English:
theorem mapClusterPt_def
  statement: MapClusterPt x F u ↔ ClusterPt x (map u F)
  proof: Iff.rfl
alias ⟨MapClusterPt.clusterPt, _⟩ := mapClusterPt_def

中文:
定理 mapClusterPt_def
  结论: MapClusterPt x F u ↔ ClusterPt x (map u F)
  证明: Iff.rfl
alias ⟨MapClusterPt.clusterPt, _⟩ := mapClusterPt_def

Depends on / 依赖: Iff.rfl
-/
theorem mapClusterPt_def : MapClusterPt x F u ↔ ClusterPt x (map u F) := Iff.rfl
alias ⟨MapClusterPt.clusterPt, _⟩ := mapClusterPt_def

/--
theorem `Filter.EventuallyEq.mapClusterPt_iff` / 定理 `Filter.EventuallyEq.mapClusterPt_iff`

English:
theorem Filter.EventuallyEq.mapClusterPt_iff
  given: {v : α -> X} (h : u =ᶠ[F] v)
  proof: by
  simp only [mapClusterPt_def, map_congr h]

alias ⟨MapClusterPt.congrFun, _⟩ := Filter.EventuallyEq.mapClusterPt_iff

中文:
定理 滤子.EventuallyEq.mapClusterPt_iff
  条件: {v : α -> X} (h : u =ᶠ[F] v)
  证明: by
  simp only [mapClusterPt_def, map_congr h]

alias ⟨MapClusterPt.congrFun, _⟩ := Filter.EventuallyEq.mapClusterPt_iff

Depends on / 依赖: mapClusterPt_def, map_congr
-/
theorem Filter.EventuallyEq.mapClusterPt_iff {v : α -> X} (h : u =ᶠ[F] v) :
    MapClusterPt x F u ↔ MapClusterPt x F v := by
  simp only [mapClusterPt_def, map_congr h]

alias ⟨MapClusterPt.congrFun, _⟩ := Filter.EventuallyEq.mapClusterPt_iff

/--
theorem `MapClusterPt.mono` / 定理 `MapClusterPt.mono`

English:
theorem MapClusterPt.mono
  given: {G : Filter α} (h : MapClusterPt x F u) (hle : F <= G)
  proof: h.clusterPt.mono (map_mono hle)

中文:
定理 MapClusterPt.mono
  条件: {G : 滤子 α} (h : MapClusterPt x F u) (hle : F <= G)
  证明: h.clusterPt.mono (map_mono hle)

Depends on / 依赖: clusterPt, h.clusterPt.mono, map_mono
-/
theorem MapClusterPt.mono {G : Filter α} (h : MapClusterPt x F u) (hle : F <= G) :
    MapClusterPt x G u :=
  h.clusterPt.mono (map_mono hle)

/--
theorem `MapClusterPt.tendsto_comp'` / 定理 `MapClusterPt.tendsto_comp'`

English:
theorem MapClusterPt.tendsto_comp'
  statement: [TopologicalSpace Y] {f : X -> Y} {y : Y}
  proof: (tendsto_inf.2 ⟨hf, tendsto_map.mono_left inf_le_right⟩).neBot (hx := hu)

中文:
定理 MapClusterPt.tendsto_comp'
  结论: [拓扑空间 Y] {f : X -> Y} {y : Y}
  证明: (tendsto_inf.2 ⟨hf, tendsto_map.mono_left inf_le_right⟩).neBot (hx := hu)

Depends on / 依赖: inf_le_right, mono_left, tendsto_inf, tendsto_map, tendsto_map.mono_left
-/
theorem MapClusterPt.tendsto_comp' [TopologicalSpace Y] {f : X -> Y} {y : Y}
    (hf : Tendsto f (𝓝 x ⊓ map u F) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (f ∘ u) :=
  (tendsto_inf.2 ⟨hf, tendsto_map.mono_left inf_le_right⟩).neBot (hx := hu)

/--
theorem `MapClusterPt.tendsto_comp` / 定理 `MapClusterPt.tendsto_comp`

English:
theorem MapClusterPt.tendsto_comp
  statement: [TopologicalSpace Y] {f : X -> Y} {y : Y}
  proof: hu.tendsto_comp' (hf.mono_left inf_le_left)

中文:
定理 MapClusterPt.tendsto_comp
  结论: [拓扑空间 Y] {f : X -> Y} {y : Y}
  证明: hu.tendsto_comp' (hf.mono_left inf_le_left)

Depends on / 依赖: hf.mono_left, hu.tendsto_comp, inf_le_left, mono_left, tendsto_comp
-/
theorem MapClusterPt.tendsto_comp [TopologicalSpace Y] {f : X -> Y} {y : Y}
    (hf : Tendsto f (𝓝 x) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (f ∘ u) :=
  hu.tendsto_comp' (hf.mono_left inf_le_left)

/--
theorem `mapClusterPt_id_iff` / 定理 `mapClusterPt_id_iff`

English:
theorem mapClusterPt_id_iff
  given: [TopologicalSpace α] {a : α}
  statement: MapClusterPt a F id ↔ ClusterPt a F
  proof: by
  rw [MapClusterPt]; rw [map_id]

alias ⟨_, ClusterPt.mapClusterPt_id⟩ := mapClusterPt_id_iff

中文:
定理 mapClusterPt_id_iff
  条件: [拓扑空间 α] {a : α}
  结论: MapClusterPt a F id ↔ ClusterPt a F
  证明: by
  rw [MapClusterPt]; rw [map_id]

alias ⟨_, ClusterPt.mapClusterPt_id⟩ := mapClusterPt_id_iff

Depends on / 依赖: MapClusterPt, map_id
-/
theorem mapClusterPt_id_iff [TopologicalSpace α] {a : α} : MapClusterPt a F id ↔ ClusterPt a F := by
  rw [MapClusterPt]; rw [map_id]

alias ⟨_, ClusterPt.mapClusterPt_id⟩ := mapClusterPt_id_iff

/--
theorem `MapClusterPt.continuousAt_comp` / 定理 `MapClusterPt.continuousAt_comp`

English:
theorem MapClusterPt.continuousAt_comp
  statement: [TopologicalSpace Y] {f : X -> Y} (hf : ContinuousAt f x)
  proof: hu.tendsto_comp hf

中文:
定理 MapClusterPt.continuousAt_comp
  结论: [拓扑空间 Y] {f : X -> Y} (hf : ContinuousAt f x)
  证明: hu.tendsto_comp hf

Depends on / 依赖: hu.tendsto_comp, tendsto_comp
-/
theorem MapClusterPt.continuousAt_comp [TopologicalSpace Y] {f : X -> Y} (hf : ContinuousAt f x)
    (hu : MapClusterPt x F u) : MapClusterPt (f x) F (f ∘ u) :=
  hu.tendsto_comp hf

/--
theorem `ContinuousAt.mapClusterPt` / 定理 `ContinuousAt.mapClusterPt`

English:
theorem ContinuousAt.mapClusterPt
  statement: [TopologicalSpace α] {a : α} (hf : ContinuousAt u a)
  proof: hu.mapClusterPt_id.continuousAt_comp hf

中文:
定理 ContinuousAt.mapClusterPt
  结论: [拓扑空间 α] {a : α} (hf : ContinuousAt u a)
  证明: hu.mapClusterPt_id.continuousAt_comp hf

Depends on / 依赖: continuousAt_comp, hu.mapClusterPt_id.continuousAt_comp, mapClusterPt_id
-/
theorem ContinuousAt.mapClusterPt [TopologicalSpace α] {a : α} (hf : ContinuousAt u a)
    (hu : ClusterPt a F) : MapClusterPt (u a) F u :=
  hu.mapClusterPt_id.continuousAt_comp hf

/--
theorem `Filter.HasBasis.mapClusterPt_iff_frequently` / 定理 `Filter.HasBasis.mapClusterPt_iff_frequently`

English:
theorem Filter.HasBasis.mapClusterPt_iff_frequently
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X}
  proof: by
  simp_rw [MapClusterPt, hx.clusterPt_iff_frequently, frequently_map]

中文:
定理 滤子.有基.mapClusterPt_iff_frequently
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 X}
  证明: by
  simp_rw [MapClusterPt, hx.clusterPt_iff_frequently, frequently_map]

Depends on / 依赖: MapClusterPt, clusterPt_iff_frequently, frequently_map, hx.clusterPt_iff_frequently, simp_rw
-/
theorem Filter.HasBasis.mapClusterPt_iff_frequently {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X}
    (hx : (𝓝 x).HasBasis p s) : MapClusterPt x F u ↔ forall i, p i -> existsᶠ a in F, u a in s i := by
  simp_rw [MapClusterPt, hx.clusterPt_iff_frequently, frequently_map]

/--
theorem `mapClusterPt_iff_frequently` / 定理 `mapClusterPt_iff_frequently`

English:
theorem mapClusterPt_iff_frequently
  statement: MapClusterPt x F u ↔ forall s in 𝓝 x, existsᶠ a in F, u a in s
  proof: (𝓝 x).basis_sets.mapClusterPt_iff_frequently

中文:
定理 mapClusterPt_iff_frequently
  结论: MapClusterPt x F u ↔ 对任意 s in 𝓝 x, 存在ᶠ a in F, u a in s
  证明: (𝓝 x).basis_sets.mapClusterPt_iff_frequently

Depends on / 依赖: basis_sets, basis_sets.mapClusterPt_iff_frequently, mapClusterPt_iff_frequently
-/
theorem mapClusterPt_iff_frequently : MapClusterPt x F u ↔ forall s in 𝓝 x, existsᶠ a in F, u a in s :=
  (𝓝 x).basis_sets.mapClusterPt_iff_frequently

/--
theorem `MapClusterPt.frequently` / 定理 `MapClusterPt.frequently`

English:
theorem MapClusterPt.frequently
  given: (h : MapClusterPt x F u) {p : X -> Prop} (hp : forallᶠ y in 𝓝 x, p y)
  proof: h.clusterPt.frequently hp

中文:
定理 MapClusterPt.frequently
  条件: (h : MapClusterPt x F u) {p : X -> 命题} (hp : 对任意ᶠ y in 𝓝 x, p y)
  证明: h.clusterPt.frequently hp

Depends on / 依赖: clusterPt, frequently, h.clusterPt.frequently
-/
theorem MapClusterPt.frequently (h : MapClusterPt x F u) {p : X -> Prop} (hp : forallᶠ y in 𝓝 x, p y) :
    existsᶠ a in F, p (u a) :=
  h.clusterPt.frequently hp

/--
theorem `mapClusterPt_comp` / 定理 `mapClusterPt_comp`

English:
theorem mapClusterPt_comp
  given: {φ : α -> β} {u : β -> X}
  proof: Iff.rfl

中文:
定理 mapClusterPt_comp
  条件: {φ : α -> β} {u : β -> X}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mapClusterPt_comp {φ : α -> β} {u : β -> X} :
    MapClusterPt x F (u ∘ φ) ↔ MapClusterPt x (map φ F) u := Iff.rfl

/--
theorem `Filter.Tendsto.mapClusterPt` / 定理 `Filter.Tendsto.mapClusterPt`

English:
theorem Filter.Tendsto.mapClusterPt
  given: [NeBot F] (h : Tendsto u F (𝓝 x))
  statement: MapClusterPt x F u
  proof: .of_le_nhds h

中文:
定理 滤子.收敛.mapClusterPt
  条件: [NeBot F] (h : 收敛 u F (𝓝 x))
  结论: MapClusterPt x F u
  证明: .of_le_nhds h

Depends on / 依赖: of_le_nhds
-/
theorem Filter.Tendsto.mapClusterPt [NeBot F] (h : Tendsto u F (𝓝 x)) : MapClusterPt x F u :=
  .of_le_nhds h

/--
theorem `MapClusterPt.of_comp` / 定理 `MapClusterPt.of_comp`

English:
theorem MapClusterPt.of_comp
  statement: {φ : β -> α} {p : Filter β} (h : Tendsto φ p F)
  proof: H.clusterPt.mono map_mono h

中文:
定理 MapClusterPt.of_comp
  结论: {φ : β -> α} {p : 滤子 β} (h : 收敛 φ p F)
  证明: H.clusterPt.mono map_mono h

Depends on / 依赖: H.clusterPt.mono, clusterPt, map_mono
-/
theorem MapClusterPt.of_comp {φ : β -> α} {p : Filter β} (h : Tendsto φ p F)
    (H : MapClusterPt x p (u ∘ φ)) : MapClusterPt x F u :=
H.clusterPt.mono map_mono h

/--
theorem `IsClosed.mem_of_mapClusterPt` / 定理 `IsClosed.mem_of_mapClusterPt`

English:
theorem IsClosed.mem_of_mapClusterPt
  statement: {l : X} {s : Set X} {f : α -> X} {b : Filter α}
  proof: (hf.frequently' h).mem_of_closed hs

中文:
定理 是闭集.mem_of_mapClusterPt
  结论: {l : X} {s : 集合 X} {f : α -> X} {b : 滤子 α}
  证明: (hf.frequently' h).mem_of_closed hs

Depends on / 依赖: frequently, hf.frequently, mem_of_closed
-/
theorem IsClosed.mem_of_mapClusterPt {l : X} {s : Set X} {f : α -> X} {b : Filter α}
    (hs : IsClosed s) (hf : MapClusterPt l b f) (h : forallᶠ (x : α) in b, f x in s) : l in s :=
  (hf.frequently' h).mem_of_closed hs

/--
theorem `mapClusterPt_atTop_iff_forall_mem_closure` / 定理 `mapClusterPt_atTop_iff_forall_mem_closure`

English:
theorem mapClusterPt_atTop_iff_forall_mem_closure
  statement: {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
  proof: by
  simp [MapClusterPt, (atTop_basis.map x).clusterPt_iff_forall_mem_closure]

中文:
定理 mapClusterPt_atTop_iff_对任意_mem_closure
  结论: {ι : 类型} [预序 ι] [IsDirectedOrder ι]
  证明: by
  simp [MapClusterPt, (atTop_basis.map x).clusterPt_iff_forall_mem_closure]

Depends on / 依赖: MapClusterPt, atTop_basis, atTop_basis.map, clusterPt_iff_forall_mem_closure
-/
theorem mapClusterPt_atTop_iff_forall_mem_closure {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {x : ι -> X} {a : X} :
    MapClusterPt a atTop x ↔ forall i, a in closure (x '' Ici i) := by
  simp [MapClusterPt, (atTop_basis.map x).clusterPt_iff_forall_mem_closure]

end MapClusterPt

/--
theorem `accPt_sup` / 定理 `accPt_sup`

English:
theorem accPt_sup
  given: {x : X} {F G : Filter X}
  proof: by
  simp only [AccPt, inf_sup_left, sup_neBot]

中文:
定理 accPt_sup
  条件: {x : X} {F G : 滤子 X}
  证明: by
  simp only [AccPt, inf_sup_left, sup_neBot]

Depends on / 依赖: inf_sup_left, sup_neBot
-/
theorem accPt_sup {x : X} {F G : Filter X} :
    AccPt x (F ⊔ G) ↔ AccPt x F ∨ AccPt x G := by
  simp only [AccPt, inf_sup_left, sup_neBot]

/--
theorem `accPt_iff_clusterPt` / 定理 `accPt_iff_clusterPt`

English:
theorem accPt_iff_clusterPt
  given: {x : X} {F : Filter X}
  statement: AccPt x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F)
  proof: by
  rw [AccPt]; rw [nhdsWithin]; rw [ClusterPt]; rw [inf_assoc]

中文:
定理 accPt_iff_clusterPt
  条件: {x : X} {F : 滤子 X}
  结论: 聚点 x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F)
  证明: by
  rw [AccPt]; rw [nhdsWithin]; rw [ClusterPt]; rw [inf_assoc]

Depends on / 依赖: ClusterPt, inf_assoc, nhdsWithin
-/
theorem accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F) := by
  rw [AccPt]; rw [nhdsWithin]; rw [ClusterPt]; rw [inf_assoc]

/--
theorem `accPt_principal_iff_clusterPt` / 定理 `accPt_principal_iff_clusterPt`

English:
theorem accPt_principal_iff_clusterPt
  given: {x : X} {C : Set X}
  proof: by
  rw [accPt_iff_clusterPt]; rw [inf_principal]; rw [inter_comm]; rw [sdiff_eq]

中文:
定理 accPt_principal_iff_clusterPt
  条件: {x : X} {C : 集合 X}
  证明: by
  rw [accPt_iff_clusterPt]; rw [inf_principal]; rw [inter_comm]; rw [sdiff_eq]

Depends on / 依赖: accPt_iff_clusterPt, inf_principal, inter_comm, sdiff_eq
-/
theorem accPt_principal_iff_clusterPt {x : X} {C : Set X} :
    AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ { x })) := by
  rw [accPt_iff_clusterPt]; rw [inf_principal]; rw [inter_comm]; rw [sdiff_eq]

/--
theorem `accPt_iff_nhds` / 定理 `accPt_iff_nhds`

English:
theorem accPt_iff_nhds
  given: {x : X} {C : Set X}
  statement: AccPt x (𝓟 C) ↔ forall U in 𝓝 x, exists y in U inter C, y != x
  proof: by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff, Set.Nonempty,
    and_assoc]

中文:
定理 accPt_iff_nhds
  条件: {x : X} {C : 集合 X}
  结论: 聚点 x (𝓟 C) ↔ 对任意 U in 𝓝 x, 存在 y in U inter C, y != x
  证明: by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff, Set.Nonempty,
    and_assoc]

Depends on / 依赖: Nonempty, Set.Nonempty, accPt_principal_iff_clusterPt, and_assoc, clusterPt_principal_iff
-/
theorem accPt_iff_nhds {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ forall U in 𝓝 x, exists y in U inter C, y != x := by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff, Set.Nonempty,
    and_assoc]

/--
theorem `accPt_iff_frequently` / 定理 `accPt_iff_frequently`

English:
theorem accPt_iff_frequently
  given: {x : X} {C : Set X}
  statement: AccPt x (𝓟 C) ↔ existsᶠ y in 𝓝 x, y != x ∧ y in C
  proof: by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff_frequently, and_comm]

中文:
定理 accPt_iff_frequently
  条件: {x : X} {C : 集合 X}
  结论: 聚点 x (𝓟 C) ↔ 存在ᶠ y in 𝓝 x, y != x ∧ y in C
  证明: by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff_frequently, and_comm]

Depends on / 依赖: accPt_principal_iff_clusterPt, and_comm, clusterPt_principal_iff_frequently
-/
theorem accPt_iff_frequently {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ existsᶠ y in 𝓝 x, y != x ∧ y in C := by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff_frequently, and_comm]

/--
theorem `accPt_iff_frequently_nhdsNE` / 定理 `accPt_iff_frequently_nhdsNE`

English:
theorem accPt_iff_frequently_nhdsNE
  given: {X : Type*} [TopologicalSpace X] {x : X} {C : Set X}
  proof: by
  have : (existsᶠ z in 𝓝[!=] x, z in C) ↔ existsᶠ z in 𝓝 x, z in C ∧ z in ({x} : Set X)ᶜ :=
frequently_inf_principal.trans by simp only [and_comm]
  rw [accPt_iff_frequently]; rw [this]
  congr! 2
  tauto

中文:
定理 accPt_iff_frequently_nhdsNE
  条件: {X : 类型} [拓扑空间 X] {x : X} {C : 集合 X}
  证明: by
  have : (existsᶠ z in 𝓝[!=] x, z in C) ↔ existsᶠ z in 𝓝 x, z in C ∧ z in ({x} : Set X)ᶜ :=
frequently_inf_principal.trans by simp only [and_comm]
  rw [accPt_iff_frequently]; rw [this]
  congr! 2
  tauto

Depends on / 依赖: accPt_iff_frequently, and_comm, frequently_inf_principal, frequently_inf_principal.trans
-/
theorem accPt_iff_frequently_nhdsNE {X : Type*} [TopologicalSpace X] {x : X} {C : Set X} :
    AccPt x (𝓟 C) ↔ existsᶠ (y : X) in 𝓝[!=] x, y in C := by
  have : (existsᶠ z in 𝓝[!=] x, z in C) ↔ existsᶠ z in 𝓝 x, z in C ∧ z in ({x} : Set X)ᶜ :=
frequently_inf_principal.trans by simp only [and_comm]
  rw [accPt_iff_frequently]; rw [this]
  congr! 2
  tauto

/--
theorem `accPt_principal_iff_nhdsWithin` / 定理 `accPt_principal_iff_nhdsWithin`

English:
theorem accPt_principal_iff_nhdsWithin
  statement: AccPt x (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot
  proof: by
  rw [accPt_principal_iff_clusterPt]; rw [ClusterPt]; rw [nhdsWithin]

中文:
定理 accPt_principal_iff_nhdsWithin
  结论: 聚点 x (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot
  证明: by
  rw [accPt_principal_iff_clusterPt]; rw [ClusterPt]; rw [nhdsWithin]

Depends on / 依赖: ClusterPt, accPt_principal_iff_clusterPt, nhdsWithin
-/
theorem accPt_principal_iff_nhdsWithin : AccPt x (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot := by
  rw [accPt_principal_iff_clusterPt]; rw [ClusterPt]; rw [nhdsWithin]

/--
theorem `AccPt.mono` / 定理 `AccPt.mono`

English:
theorem AccPt.mono
  given: {F G : Filter X} (h : AccPt x F) (hFG : F <= G)
  statement: AccPt x G
  proof: NeBot.mono h (inf_le_inf_left _ hFG)

中文:
定理 聚点.mono
  条件: {F G : 滤子 X} (h : 聚点 x F) (hFG : F <= G)
  结论: 聚点 x G
  证明: NeBot.mono h (inf_le_inf_left _ hFG)

Depends on / 依赖: NeBot.mono, inf_le_inf_left
-/
theorem AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F <= G) : AccPt x G :=
  NeBot.mono h (inf_le_inf_left _ hFG)

/--
theorem `AccPt.clusterPt` / 定理 `AccPt.clusterPt`

English:
theorem AccPt.clusterPt
  given: {x : X} {F : Filter X} (h : AccPt x F)
  statement: ClusterPt x F
  proof: (accPt_iff_clusterPt.mp h).mono inf_le_right

中文:
定理 聚点.clusterPt
  条件: {x : X} {F : 滤子 X} (h : 聚点 x F)
  结论: ClusterPt x F
  证明: (accPt_iff_clusterPt.mp h).mono inf_le_right

Depends on / 依赖: accPt_iff_clusterPt, accPt_iff_clusterPt.mp, inf_le_right
-/
theorem AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) : ClusterPt x F :=
  (accPt_iff_clusterPt.mp h).mono inf_le_right

/--
theorem `clusterPt_principal` / 定理 `clusterPt_principal`

English:
theorem clusterPt_principal
  given: {x : X} {C : Set X}
  proof: by
  constructor
  · intro h
    by_contra! hc
    rw [accPt_principal_iff_clusterPt] at hc
    simp_all only [not_false_eq_true, sdiff_singleton_eq_self, not_true_eq_false, hc.1]
  · rintro (h | h)
    · exact clusterPt_principal_iff.mpr fun _ mem => ⟨x, ⟨mem_of_mem_nhds mem, h⟩⟩
    · exact h.clusterPt

中文:
定理 clusterPt_principal
  条件: {x : X} {C : 集合 X}
  证明: by
  constructor
  · intro h
    by_contra! hc
    rw [accPt_principal_iff_clusterPt] at hc
    simp_all only [not_false_eq_true, sdiff_singleton_eq_self, not_true_eq_false, hc.1]
  · rintro (h | h)
    · exact clusterPt_principal_iff.mpr fun _ mem => ⟨x, ⟨mem_of_mem_nhds mem, h⟩⟩
    · exact h.clusterPt

Depends on / 依赖: accPt_principal_iff_clusterPt, clusterPt, clusterPt_principal_iff, clusterPt_principal_iff.mpr, h.clusterPt, mem_of_mem_nhds, not_false_eq_true, not_true_eq_false, sdiff_singleton_eq_self
-/
theorem clusterPt_principal {x : X} {C : Set X} :
    ClusterPt x (𝓟 C) ↔ x in C ∨ AccPt x (𝓟 C) := by
  constructor
  · intro h
    by_contra! hc
    rw [accPt_principal_iff_clusterPt] at hc
    simp_all only [not_false_eq_true, sdiff_singleton_eq_self, not_true_eq_false, hc.1]
  · rintro (h | h)
    · exact clusterPt_principal_iff.mpr fun _ mem => ⟨x, ⟨mem_of_mem_nhds mem, h⟩⟩
    · exact h.clusterPt

/--
theorem `isClosed_setOfPred_clusterPt` / 定理 `isClosed_setOfPred_clusterPt`

English:
theorem isClosed_setOfPred_clusterPt
  given: {f : Filter X}
  statement: IsClosed { x | ClusterPt x f }
  proof: by
  simp only [clusterPt_iff_forall_mem_closure, ofPred_forall]
  exact isClosed_biInter fun _ _ => isClosed_closure

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_clusterPt := isClosed_setOfPred_clusterPt

中文:
定理 isClosed_setOfPred_clusterPt
  条件: {f : 滤子 X}
  结论: 是闭集 { x | ClusterPt x f }
  证明: by
  simp only [clusterPt_iff_forall_mem_closure, ofPred_forall]
  exact isClosed_biInter fun _ _ => isClosed_closure

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_clusterPt := isClosed_setOfPred_clusterPt

Depends on / 依赖: clusterPt_iff_forall_mem_closure, isClosed_biInter, isClosed_closure, ofPred_forall
-/
theorem isClosed_setOfPred_clusterPt {f : Filter X} : IsClosed { x | ClusterPt x f } := by
  simp only [clusterPt_iff_forall_mem_closure, ofPred_forall]
  exact isClosed_biInter fun _ _ => isClosed_closure

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_clusterPt := isClosed_setOfPred_clusterPt

/--
theorem `mem_closure_iff_clusterPt` / 定理 `mem_closure_iff_clusterPt`

English:
theorem mem_closure_iff_clusterPt
  statement: x in closure s ↔ ClusterPt x (𝓟 s)
  proof: mem_closure_iff_frequently.trans clusterPt_principal_iff_frequently.symm

alias ⟨_, ClusterPt.mem_closure⟩ := mem_closure_iff_clusterPt

中文:
定理 mem_closure_iff_clusterPt
  结论: x in closure s ↔ ClusterPt x (𝓟 s)
  证明: mem_closure_iff_frequently.trans clusterPt_principal_iff_frequently.symm

alias ⟨_, ClusterPt.mem_closure⟩ := mem_closure_iff_clusterPt

Depends on / 依赖: clusterPt_principal_iff_frequently, clusterPt_principal_iff_frequently.symm, mem_closure_iff_frequently, mem_closure_iff_frequently.trans
-/
theorem mem_closure_iff_clusterPt : x in closure s ↔ ClusterPt x (𝓟 s) :=
  mem_closure_iff_frequently.trans clusterPt_principal_iff_frequently.symm

alias ⟨_, ClusterPt.mem_closure⟩ := mem_closure_iff_clusterPt

/--
theorem `mem_closure_iff_nhds_ne_bot` / 定理 `mem_closure_iff_nhds_ne_bot`

English:
theorem mem_closure_iff_nhds_ne_bot
  statement: x in closure s ↔ 𝓝 x ⊓ 𝓟 s != ⊥
  proof: mem_closure_iff_clusterPt.trans neBot_iff

中文:
定理 mem_closure_iff_nhds_ne_bot
  结论: x in closure s ↔ 𝓝 x ⊓ 𝓟 s != ⊥
  证明: mem_closure_iff_clusterPt.trans neBot_iff

Depends on / 依赖: mem_closure_iff_clusterPt, mem_closure_iff_clusterPt.trans, neBot_iff
-/
theorem mem_closure_iff_nhds_ne_bot : x in closure s ↔ 𝓝 x ⊓ 𝓟 s != ⊥ :=
  mem_closure_iff_clusterPt.trans neBot_iff

/--
theorem `mem_closure_iff_nhdsWithin_neBot` / 定理 `mem_closure_iff_nhdsWithin_neBot`

English:
theorem mem_closure_iff_nhdsWithin_neBot
  statement: x in closure s ↔ NeBot (𝓝[s] x)
  proof: mem_closure_iff_clusterPt

中文:
定理 mem_closure_iff_nhdsWithin_neBot
  结论: x in closure s ↔ NeBot (𝓝[s] x)
  证明: mem_closure_iff_clusterPt

Depends on / 依赖: mem_closure_iff_clusterPt
-/
theorem mem_closure_iff_nhdsWithin_neBot : x in closure s ↔ NeBot (𝓝[s] x) :=
  mem_closure_iff_clusterPt

/--
lemma `notMem_closure_iff_nhdsWithin_eq_bot` / 引理 `notMem_closure_iff_nhdsWithin_eq_bot`

English:
lemma notMem_closure_iff_nhdsWithin_eq_bot
  statement: x ∉ closure s ↔ 𝓝[s] x = ⊥
  proof: by
  rw [mem_closure_iff_nhdsWithin_neBot]; rw [not_neBot]

中文:
引理 notMem_closure_iff_nhdsWithin_eq_bot
  结论: x ∉ closure s ↔ 𝓝[s] x = ⊥
  证明: by
  rw [mem_closure_iff_nhdsWithin_neBot]; rw [not_neBot]

Depends on / 依赖: mem_closure_iff_nhdsWithin_neBot, not_neBot
-/
lemma notMem_closure_iff_nhdsWithin_eq_bot : x ∉ closure s ↔ 𝓝[s] x = ⊥ := by
  rw [mem_closure_iff_nhdsWithin_neBot]; rw [not_neBot]

/--
theorem `mem_interior_iff_not_clusterPt_compl` / 定理 `mem_interior_iff_not_clusterPt_compl`

English:
theorem mem_interior_iff_not_clusterPt_compl
  statement: x in interior s ↔ ¬ClusterPt x (𝓟 sᶜ)
  proof: by
  rw [← mem_closure_iff_clusterPt]; rw [closure_compl]; rw [mem_compl_iff]; rw [not_not]

中文:
定理 mem_interior_iff_not_clusterPt_compl
  结论: x in interior s ↔ ¬ClusterPt x (𝓟 sᶜ)
  证明: by
  rw [← mem_closure_iff_clusterPt]; rw [closure_compl]; rw [mem_compl_iff]; rw [not_not]

Depends on / 依赖: closure_compl, mem_closure_iff_clusterPt, mem_compl_iff, not_not
-/
theorem mem_interior_iff_not_clusterPt_compl : x in interior s ↔ ¬ClusterPt x (𝓟 sᶜ) := by
  rw [← mem_closure_iff_clusterPt]; rw [closure_compl]; rw [mem_compl_iff]; rw [not_not]

/--
theorem `dense_compl_singleton` / 定理 `dense_compl_singleton`

English:
theorem dense_compl_singleton
  given: (x : X) [NeBot (𝓝[!=] x)]
  statement: Dense ({x}ᶜ : Set X)
  proof: by
  intro y
  rcases eq_or_ne y x with (rfl | hne)
  · rwa [mem_closure_iff_nhdsWithin_neBot]
  · exact subset_closure hne

中文:
定理 dense_compl_singleton
  条件: (x : X) [NeBot (𝓝[!=] x)]
  结论: 稠密 ({x}ᶜ : 集合 X)
  证明: by
  intro y
  rcases eq_or_ne y x with (rfl | hne)
  · rwa [mem_closure_iff_nhdsWithin_neBot]
  · exact subset_closure hne

Depends on / 依赖: eq_or_ne, mem_closure_iff_nhdsWithin_neBot, subset_closure
-/
theorem dense_compl_singleton (x : X) [NeBot (𝓝[!=] x)] : Dense ({x}ᶜ : Set X) := by
  intro y
  rcases eq_or_ne y x with (rfl | hne)
  · rwa [mem_closure_iff_nhdsWithin_neBot]
  · exact subset_closure hne

/--
theorem `closure_compl_singleton` / 定理 `closure_compl_singleton`

English:
theorem closure_compl_singleton
  given: (x : X) [NeBot (𝓝[!=] x)]
  statement: closure {x}ᶜ = (univ : Set X)
  proof: (dense_compl_singleton x).closure_eq

中文:
定理 closure_compl_singleton
  条件: (x : X) [NeBot (𝓝[!=] x)]
  结论: closure {x}ᶜ = (univ : 集合 X)
  证明: (dense_compl_singleton x).closure_eq

Depends on / 依赖: closure_eq, dense_compl_singleton
-/
theorem closure_compl_singleton (x : X) [NeBot (𝓝[!=] x)] : closure {x}ᶜ = (univ : Set X) :=
  (dense_compl_singleton x).closure_eq

/-- If `x` is not an isolated point of a topological space, then the interior of `{x}` is empty. -/
@[simp]
/--
theorem `interior_singleton` / 定理 `interior_singleton`

English:
theorem interior_singleton
  given: (x : X) [NeBot (𝓝[!=] x)]
  statement: interior {x} = (∅ : Set X)
  proof: interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)

中文:
定理 interior_singleton
  条件: (x : X) [NeBot (𝓝[!=] x)]
  结论: interior {x} = (∅ : 集合 X)
  证明: interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)

Depends on / 依赖: dense_compl_singleton, interior_eq_empty_iff_dense_compl
-/
theorem interior_singleton (x : X) [NeBot (𝓝[!=] x)] : interior {x} = (∅ : Set X) :=
  interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)

/--
theorem `not_isOpen_singleton` / 定理 `not_isOpen_singleton`

English:
theorem not_isOpen_singleton
  given: (x : X) [NeBot (𝓝[!=] x)]
  statement: ¬IsOpen ({x} : Set X)
  proof: dense_compl_singleton_iff_not_open.1 (dense_compl_singleton x)

中文:
定理 not_isOpen_singleton
  条件: (x : X) [NeBot (𝓝[!=] x)]
  结论: ¬是开集 ({x} : 集合 X)
  证明: dense_compl_singleton_iff_not_open.1 (dense_compl_singleton x)

Depends on / 依赖: dense_compl_singleton, dense_compl_singleton_iff_not_open
-/
theorem not_isOpen_singleton (x : X) [NeBot (𝓝[!=] x)] : ¬IsOpen ({x} : Set X) :=
  dense_compl_singleton_iff_not_open.1 (dense_compl_singleton x)

/--
theorem `closure_eq_cluster_pts` / 定理 `closure_eq_cluster_pts`

English:
theorem closure_eq_cluster_pts
  statement: closure s = { a | ClusterPt a (𝓟 s) }
  proof: Set.ext fun _ => mem_closure_iff_clusterPt

中文:
定理 closure_eq_cluster_pts
  结论: closure s = { a | ClusterPt a (𝓟 s) }
  证明: Set.ext fun _ => mem_closure_iff_clusterPt

Depends on / 依赖: Set.ext, mem_closure_iff_clusterPt
-/
theorem closure_eq_cluster_pts : closure s = { a | ClusterPt a (𝓟 s) } :=
  Set.ext fun _ => mem_closure_iff_clusterPt

/--
theorem `mem_closure_iff_nhds` / 定理 `mem_closure_iff_nhds`

English:
theorem mem_closure_iff_nhds
  statement: x in closure s ↔ forall t in 𝓝 x, (t inter s).Nonempty
  proof: mem_closure_iff_clusterPt.trans clusterPt_principal_iff

中文:
定理 mem_closure_iff_nhds
  结论: x in closure s ↔ 对任意 t in 𝓝 x, (t inter s).非空
  证明: mem_closure_iff_clusterPt.trans clusterPt_principal_iff

Depends on / 依赖: clusterPt_principal_iff, mem_closure_iff_clusterPt, mem_closure_iff_clusterPt.trans
-/
theorem mem_closure_iff_nhds : x in closure s ↔ forall t in 𝓝 x, (t inter s).Nonempty :=
  mem_closure_iff_clusterPt.trans clusterPt_principal_iff

/--
theorem `mem_closure_iff_nhds'` / 定理 `mem_closure_iff_nhds'`

English:
theorem mem_closure_iff_nhds'
  statement: x in closure s ↔ forall t in 𝓝 x, exists y : s, ↑y in t
  proof: by
  simp only [mem_closure_iff_nhds, Set.inter_nonempty_iff_exists_right, SetCoe.exists, exists_prop]

中文:
定理 mem_closure_iff_nhds'
  结论: x in closure s ↔ 对任意 t in 𝓝 x, 存在 y : s, ↑y in t
  证明: by
  simp only [mem_closure_iff_nhds, Set.inter_nonempty_iff_exists_right, SetCoe.exists, exists_prop]

Depends on / 依赖: Set.inter_nonempty_iff_exists_right, SetCoe, SetCoe.exists, exists_prop, inter_nonempty_iff_exists_right, mem_closure_iff_nhds
-/
theorem mem_closure_iff_nhds' : x in closure s ↔ forall t in 𝓝 x, exists y : s, ↑y in t := by
  simp only [mem_closure_iff_nhds, Set.inter_nonempty_iff_exists_right, SetCoe.exists, exists_prop]

/--
theorem `mem_closure_iff_comap_neBot` / 定理 `mem_closure_iff_comap_neBot`

English:
theorem mem_closure_iff_comap_neBot
  proof: by
  simp_rw [mem_closure_iff_nhds, comap_neBot_iff, Set.inter_nonempty_iff_exists_right,
    SetCoe.exists, exists_prop]

中文:
定理 mem_closure_iff_comap_neBot
  证明: by
  simp_rw [mem_closure_iff_nhds, comap_neBot_iff, Set.inter_nonempty_iff_exists_right,
    SetCoe.exists, exists_prop]

Depends on / 依赖: Set.inter_nonempty_iff_exists_right, SetCoe, SetCoe.exists, comap_neBot_iff, exists_prop, inter_nonempty_iff_exists_right, mem_closure_iff_nhds, simp_rw
-/
theorem mem_closure_iff_comap_neBot :
    x in closure s ↔ NeBot (comap ((↑) : s -> X) (𝓝 x)) := by
  simp_rw [mem_closure_iff_nhds, comap_neBot_iff, Set.inter_nonempty_iff_exists_right,
    SetCoe.exists, exists_prop]

/--
theorem `mem_closure_iff_nhds_basis'` / 定理 `mem_closure_iff_nhds_basis'`

English:
theorem mem_closure_iff_nhds_basis'
  given: {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).HasBasis p s)
  proof: mem_closure_iff_clusterPt.trans
(h.clusterPt_iff (hasBasis_principal _)).trans by simp only [forall_const]

中文:
定理 mem_closure_iff_nhds_basis'
  条件: {p : ι -> 命题} {s : ι -> 集合 X} (h : (𝓝 x).有基 p s)
  证明: mem_closure_iff_clusterPt.trans
(h.clusterPt_iff (hasBasis_principal _)).trans by simp only [forall_const]

Depends on / 依赖: clusterPt_iff, forall_const, h.clusterPt_iff, hasBasis_principal, mem_closure_iff_clusterPt, mem_closure_iff_clusterPt.trans
-/
theorem mem_closure_iff_nhds_basis' {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).HasBasis p s) :
    x in closure t ↔ forall i, p i -> (s i inter t).Nonempty :=
mem_closure_iff_clusterPt.trans
(h.clusterPt_iff (hasBasis_principal _)).trans by simp only [forall_const]

/--
theorem `mem_closure_iff_nhds_basis` / 定理 `mem_closure_iff_nhds_basis`

English:
theorem mem_closure_iff_nhds_basis
  given: {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).HasBasis p s)
  proof: (mem_closure_iff_nhds_basis' h).trans by
    simp only [Set.Nonempty, mem_inter_iff, and_comm]

中文:
定理 mem_closure_iff_nhds_basis
  条件: {p : ι -> 命题} {s : ι -> 集合 X} (h : (𝓝 x).有基 p s)
  证明: (mem_closure_iff_nhds_basis' h).trans by
    simp only [Set.Nonempty, mem_inter_iff, and_comm]

Depends on / 依赖: Nonempty, Set.Nonempty, and_comm, mem_closure_iff_nhds_basis, mem_inter_iff
-/
theorem mem_closure_iff_nhds_basis {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).HasBasis p s) :
    x in closure t ↔ forall i, p i -> exists y in t, y in s i :=
(mem_closure_iff_nhds_basis' h).trans by
    simp only [Set.Nonempty, mem_inter_iff, and_comm]

/--
theorem `clusterPt_iff_lift'_closure` / 定理 `clusterPt_iff_lift'_closure`

English:
theorem clusterPt_iff_lift'_closure
  given: {F : Filter X}
  proof: by
  simp_rw [clusterPt_iff_forall_mem_closure,
    (hasBasis_pure _).le_basis_iff F.basis_sets.lift'_closure, id, singleton_subset_iff, true_and,
    exists_const]

中文:
定理 clusterPt_iff_lift'_closure
  条件: {F : 滤子 X}
  证明: by
  simp_rw [clusterPt_iff_forall_mem_closure,
    (hasBasis_pure _).le_basis_iff F.basis_sets.lift'_closure, id, singleton_subset_iff, true_and,
    exists_const]

Depends on / 依赖: F.basis_sets.lift, _closure, basis_sets, clusterPt_iff_forall_mem_closure, exists_const, hasBasis_pure, le_basis_iff, simp_rw, singleton_subset_iff, true_and
-/
theorem clusterPt_iff_lift'_closure {F : Filter X} :
    ClusterPt x F ↔ pure x <= (F.lift' closure) := by
  simp_rw [clusterPt_iff_forall_mem_closure,
    (hasBasis_pure _).le_basis_iff F.basis_sets.lift'_closure, id, singleton_subset_iff, true_and,
    exists_const]

/--
theorem `clusterPt_iff_lift'_closure'` / 定理 `clusterPt_iff_lift'_closure'`

English:
theorem clusterPt_iff_lift'_closure'
  given: {F : Filter X}
  proof: by
  rw [clusterPt_iff_lift'_closure]; rw [inf_comm]
  constructor
  · intro h
    simp [h, pure_neBot]
  · intro h U hU
    simp_rw [← forall_mem_nonempty_iff_neBot, mem_inf_iff] at h
    simpa using h ({x} inter U) ⟨{x}, by simp, U, hU, rfl⟩

@[simp]

中文:
定理 clusterPt_iff_lift'_closure'
  条件: {F : 滤子 X}
  证明: by
  rw [clusterPt_iff_lift'_closure]; rw [inf_comm]
  constructor
  · intro h
    simp [h, pure_neBot]
  · intro h U hU
    simp_rw [← forall_mem_nonempty_iff_neBot, mem_inf_iff] at h
    simpa using h ({x} inter U) ⟨{x}, by simp, U, hU, rfl⟩

@[simp]
-/
theorem clusterPt_iff_lift'_closure' {F : Filter X} :
    ClusterPt x F ↔ (F.lift' closure ⊓ pure x).NeBot := by
  rw [clusterPt_iff_lift'_closure]; rw [inf_comm]
  constructor
  · intro h
    simp [h, pure_neBot]
  · intro h U hU
    simp_rw [← forall_mem_nonempty_iff_neBot, mem_inf_iff] at h
    simpa using h ({x} inter U) ⟨{x}, by simp, U, hU, rfl⟩

@[simp]
/--
theorem `clusterPt_lift'_closure_iff` / 定理 `clusterPt_lift'_closure_iff`

English:
theorem clusterPt_lift'_closure_iff
  given: {F : Filter X}
  proof: by
  simp [clusterPt_iff_lift'_closure, lift'_lift'_assoc (monotone_closure X) (monotone_closure X)]

中文:
定理 clusterPt_lift'_closure_iff
  条件: {F : 滤子 X}
  证明: by
  simp [clusterPt_iff_lift'_closure, lift'_lift'_assoc (monotone_closure X) (monotone_closure X)]

Depends on / 依赖: _assoc, _closure, _lift, clusterPt_iff_lift, monotone_closure
-/
theorem clusterPt_lift'_closure_iff {F : Filter X} :
    ClusterPt x (F.lift' closure) ↔ ClusterPt x F := by
  simp [clusterPt_iff_lift'_closure, lift'_lift'_assoc (monotone_closure X) (monotone_closure X)]

/--
theorem `isClosed_iff_clusterPt` / 定理 `isClosed_iff_clusterPt`

English:
theorem isClosed_iff_clusterPt
  statement: IsClosed s ↔ forall a, ClusterPt a (𝓟 s) -> a in s
  proof: calc
    IsClosed s ↔ closure s subseteq s := closure_subset_iff_isClosed.symm
    _ ↔ forall a, ClusterPt a (𝓟 s) -> a in s := by simp only [subset_def, mem_closure_iff_clusterPt]

中文:
定理 isClosed_iff_clusterPt
  结论: 是闭集 s ↔ 对任意 a, ClusterPt a (𝓟 s) -> a in s
  证明: calc
    IsClosed s ↔ closure s subseteq s := closure_subset_iff_isClosed.symm
    _ ↔ forall a, ClusterPt a (𝓟 s) -> a in s := by simp only [subset_def, mem_closure_iff_clusterPt]

Depends on / 依赖: ClusterPt, IsClosed, closure, closure_subset_iff_isClosed, closure_subset_iff_isClosed.symm, mem_closure_iff_clusterPt, subset_def, subseteq
-/
theorem isClosed_iff_clusterPt : IsClosed s ↔ forall a, ClusterPt a (𝓟 s) -> a in s :=
  calc
    IsClosed s ↔ closure s subseteq s := closure_subset_iff_isClosed.symm
    _ ↔ forall a, ClusterPt a (𝓟 s) -> a in s := by simp only [subset_def, mem_closure_iff_clusterPt]

/--
theorem `isClosed_iff_accPt` / 定理 `isClosed_iff_accPt`

English:
theorem isClosed_iff_accPt
  statement: IsClosed s ↔ forall a, AccPt a (𝓟 s) -> a in s
  proof: by
  simp [isClosed_iff_clusterPt, clusterPt_principal, or_imp]

中文:
定理 isClosed_iff_accPt
  结论: 是闭集 s ↔ 对任意 a, 聚点 a (𝓟 s) -> a in s
  证明: by
  simp [isClosed_iff_clusterPt, clusterPt_principal, or_imp]

Depends on / 依赖: clusterPt_principal, isClosed_iff_clusterPt, or_imp
-/
theorem isClosed_iff_accPt : IsClosed s ↔ forall a, AccPt a (𝓟 s) -> a in s := by
  simp [isClosed_iff_clusterPt, clusterPt_principal, or_imp]

/--
theorem `isClosed_iff_nhds` / 定理 `isClosed_iff_nhds`

English:
theorem isClosed_iff_nhds
  proof: by
  simp_rw [isClosed_iff_clusterPt, ClusterPt, inf_principal_neBot_iff]

中文:
定理 isClosed_iff_nhds
  证明: by
  simp_rw [isClosed_iff_clusterPt, ClusterPt, inf_principal_neBot_iff]

Depends on / 依赖: ClusterPt, inf_principal_neBot_iff, isClosed_iff_clusterPt, simp_rw
-/
theorem isClosed_iff_nhds :
    IsClosed s ↔ forall x, (forall U in 𝓝 x, (U inter s).Nonempty) -> x in s := by
  simp_rw [isClosed_iff_clusterPt, ClusterPt, inf_principal_neBot_iff]

/--
lemma `isClosed_iff_forall_filter` / 引理 `isClosed_iff_forall_filter`

English:
lemma isClosed_iff_forall_filter
  proof: by
  simp_rw [isClosed_iff_clusterPt]
exact ⟨fun hs x F F_ne FS Fx => hs _ NeBot.mono F_ne (le_inf Fx FS),
         fun hs x hx => hs x (𝓝 x ⊓ 𝓟 s) hx inf_le_right inf_le_left⟩

中文:
引理 isClosed_iff_对任意_filter
  证明: by
  simp_rw [isClosed_iff_clusterPt]
exact ⟨fun hs x F F_ne FS Fx => hs _ NeBot.mono F_ne (le_inf Fx FS),
         fun hs x hx => hs x (𝓝 x ⊓ 𝓟 s) hx inf_le_right inf_le_left⟩

Depends on / 依赖: F_ne, NeBot.mono, inf_le_left, inf_le_right, isClosed_iff_clusterPt, le_inf, simp_rw
-/
lemma isClosed_iff_forall_filter :
    IsClosed s ↔ forall x, forall F : Filter X, F.NeBot -> F <= 𝓟 s -> F <= 𝓝 x -> x in s := by
  simp_rw [isClosed_iff_clusterPt]
exact ⟨fun hs x F F_ne FS Fx => hs _ NeBot.mono F_ne (le_inf Fx FS),
         fun hs x hx => hs x (𝓝 x ⊓ 𝓟 s) hx inf_le_right inf_le_left⟩

/--
theorem `mem_closure_of_mem_closure_union` / 定理 `mem_closure_of_mem_closure_union`

English:
theorem mem_closure_of_mem_closure_union
  statement: (h : x in closure (s₁ union s₂))
  proof: by
  rw [mem_closure_iff_nhds_ne_bot] at *
  rwa [← sup_principal, inf_sup_left, inf_principal_eq_bot.mpr h₁, bot_sup_eq] at h

中文:
定理 mem_closure_of_mem_closure_union
  结论: (h : x in closure (s₁ union s₂))
  证明: by
  rw [mem_closure_iff_nhds_ne_bot] at *
  rwa [← sup_principal, inf_sup_left, inf_principal_eq_bot.mpr h₁, bot_sup_eq] at h

Depends on / 依赖: bot_sup_eq, inf_principal_eq_bot, inf_principal_eq_bot.mpr, inf_sup_left, mem_closure_iff_nhds_ne_bot, sup_principal
-/
theorem mem_closure_of_mem_closure_union (h : x in closure (s₁ union s₂))
    (h₁ : s₁ᶜ in 𝓝 x) : x in closure s₂ := by
  rw [mem_closure_iff_nhds_ne_bot] at *
  rwa [← sup_principal, inf_sup_left, inf_principal_eq_bot.mpr h₁, bot_sup_eq] at h
