/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.Clopen
/-!
# Separated maps and locally injective maps out of a topological space.

This module introduces a pair of dual notions `IsSeparatedMap` and `IsLocallyInjective`.

A function from a topological space `X` to a type `Y` is a separated map if any two distinct
points in `X` with the same image in `Y` can be separated by open neighborhoods.
A constant function is a separated map if and only if `X` is a `T2Space`.

A function from a topological space `X` is locally injective if every point of `X`
has a neighborhood on which `f` is injective.
A constant function is locally injective if and only if `X` is discrete.

Given `f : X → Y` we can form the pullback $X \times_Y X$; the diagonal map
$\Delta: X \to X \times_Y X$ is always an embedding. It is a closed embedding
iff `f` is a separated map, iff the equal locus of any two continuous maps
coequalized by `f` is closed. It is an open embedding iff `f` is locally injective,
iff any such equal locus is open. Therefore, if `f` is a locally injective separated map,
the equal locus of two continuous maps coequalized by `f` is clopen, so if the two maps
agree on a point, then they agree on the whole connected component.

The analogue of separated maps and locally injective maps in algebraic geometry are
separated morphisms and unramified morphisms, respectively.

## Reference

https://stacks.math.columbia.edu/tag/0CY0
-/

@[expose] public section

open Topology

variable {X Y A} [TopologicalSpace X] [TopologicalSpace A]

/--
lemma `Topology.IsEmbedding.toPullbackDiag` / 引理 `Topology.IsEmbedding.toPullbackDiag`

English:
lemma Topology.IsEmbedding.toPullbackDiag
  given: (f : X -> Y)
  statement: IsEmbedding (toPullbackDiag f)
  proof: .mk' _ (injective_toPullbackDiag f) fun x => by
    simp [nhds_induced, Filter.comap_comap, nhds_prod_eq, Filter.comap_prod, Function.comp_def,
      Filter.comap_id']

中文:
引理 Topology.IsEmbedding.toPullbackDiag
  条件: (f : X -> Y)
  结论: IsEmbedding (toPullbackDiag f)
  证明: .mk' _ (injective_toPullbackDiag f) fun x => by
    simp [nhds_induced, Filter.comap_comap, nhds_prod_eq, Filter.comap_prod, Function.comp_def,
      Filter.comap_id']
-/
protected lemma Topology.IsEmbedding.toPullbackDiag (f : X -> Y) : IsEmbedding (toPullbackDiag f) :=
  .mk' _ (injective_toPullbackDiag f) fun x => by
    simp [nhds_induced, Filter.comap_comap, nhds_prod_eq, Filter.comap_prod, Function.comp_def,
      Filter.comap_id']

/--
lemma `Continuous.mapPullback` / 引理 `Continuous.mapPullback`

English:
lemma Continuous.mapPullback
  statement: {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
  proof: by
  refine continuous_induced_rng.mpr (.prodMk ?_ ?_) <;>
    apply_rules [continuous_fst, continuous_snd, continuous_subtype_val, Continuous.comp]

中文:
引理 Continuous.mapPullback
  结论: {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
  证明: by
  refine continuous_induced_rng.mpr (.prodMk ?_ ?_) <;>
    apply_rules [continuous_fst, continuous_snd, continuous_subtype_val, Continuous.comp]

Depends on / 依赖: Continuous, Continuous.comp, apply_rules, continuous_fst, continuous_induced_rng, continuous_induced_rng.mpr, continuous_snd, continuous_subtype_val, prodMk
-/
lemma Continuous.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
    [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z₁] [TopologicalSpace Z₂]
    {f₁ : X₁ -> Y₁} {g₁ : Z₁ -> Y₁} {f₂ : X₂ -> Y₂} {g₂ : Z₂ -> Y₂}
    {mapX : X₁ -> X₂} (contX : Continuous mapX) {mapY : Y₁ -> Y₂}
    {mapZ : Z₁ -> Z₂} (contZ : Continuous mapZ)
    {commX : f₂ ∘ mapX = mapY ∘ f₁} {commZ : g₂ ∘ mapZ = mapY ∘ g₁} :
    Continuous (Function.mapPullback mapX mapY mapZ commX commZ) := by
  refine continuous_induced_rng.mpr (.prodMk ?_ ?_) <;>
    apply_rules [continuous_fst, continuous_snd, continuous_subtype_val, Continuous.comp]

/--
Definition of `IsSeparatedMap` / `IsSeparatedMap` 的定义

English:
definition IsSeparatedMap
  signature: (f : X -> Y)
  body: forall x₁ x₂, f x₁ = f x₂ ->
    x₁ != x₂ -> exists s₁ s₂, IsOpen s₁ ∧ IsOpen s₂ ∧ x₁ in s₁ ∧ x₂ in s₂ ∧ Disjoint s₁ s₂

中文:
定义 IsSeparatedMap
  签名: (f : X -> Y)
  定义体: forall x₁ x₂, f x₁ = f x₂ ->
    x₁ != x₂ -> exists s₁ s₂, IsOpen s₁ ∧ IsOpen s₂ ∧ x₁ in s₁ ∧ x₂ in s₂ ∧ Disjoint s₁ s₂
-/
def IsSeparatedMap (f : X -> Y) : Prop := forall x₁ x₂, f x₁ = f x₂ ->
    x₁ != x₂ -> exists s₁ s₂, IsOpen s₁ ∧ IsOpen s₂ ∧ x₁ in s₁ ∧ x₂ in s₂ ∧ Disjoint s₁ s₂

/--
lemma `t2space_iff_isSeparatedMap` / 引理 `t2space_iff_isSeparatedMap`

English:
lemma t2space_iff_isSeparatedMap
  given: (y : Y)
  statement: T2Space X ↔ IsSeparatedMap fun _ : X => y
  proof: ⟨fun ⟨t2⟩ _ _ _ hne => t2 hne, fun sep => ⟨fun x₁ x₂ hne => sep x₁ x₂ rfl hne⟩⟩

中文:
引理 t2space_iff_isSeparatedMap
  条件: (y : Y)
  结论: T2Space X ↔ IsSeparatedMap fun _ : X => y
  证明: ⟨fun ⟨t2⟩ _ _ _ hne => t2 hne, fun sep => ⟨fun x₁ x₂ hne => sep x₁ x₂ rfl hne⟩⟩
-/
lemma t2space_iff_isSeparatedMap (y : Y) : T2Space X ↔ IsSeparatedMap fun _ : X => y :=
  ⟨fun ⟨t2⟩ _ _ _ hne => t2 hne, fun sep => ⟨fun x₁ x₂ hne => sep x₁ x₂ rfl hne⟩⟩

/--
lemma `T2Space.isSeparatedMap` / 引理 `T2Space.isSeparatedMap`

English:
lemma T2Space.isSeparatedMap
  given: [T2Space X] (f : X -> Y)
  statement: IsSeparatedMap f
  proof: fun _ _ _ => t2_separation

中文:
引理 T2Space.isSeparatedMap
  条件: [T2Space X] (f : X -> Y)
  结论: IsSeparatedMap f
  证明: fun _ _ _ => t2_separation

Depends on / 依赖: t2_separation
-/
lemma T2Space.isSeparatedMap [T2Space X] (f : X -> Y) : IsSeparatedMap f := fun _ _ _ => t2_separation

/--
lemma `Function.Injective.isSeparatedMap` / 引理 `Function.Injective.isSeparatedMap`

English:
lemma Function.Injective.isSeparatedMap
  given: {f : X -> Y} (inj : f.Injective)
  statement: IsSeparatedMap f
  proof: fun _ _ he hne => (hne (inj he)).elim

中文:
引理 Function.Injective.isSeparatedMap
  条件: {f : X -> Y} (inj : f.Injective)
  结论: IsSeparatedMap f
  证明: fun _ _ he hne => (hne (inj he)).elim
-/
lemma Function.Injective.isSeparatedMap {f : X -> Y} (inj : f.Injective) : IsSeparatedMap f :=
  fun _ _ he hne => (hne (inj he)).elim

/--
lemma `isSeparatedMap_iff_disjoint_nhds` / 引理 `isSeparatedMap_iff_disjoint_nhds`

English:
lemma isSeparatedMap_iff_disjoint_nhds
  given: {f : X -> Y}
  statement: IsSeparatedMap f ↔
  proof: forall₃_congr fun x x' _ => by simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens x'),
    ← exists_and_left, and_assoc, and_comm, and_left_comm]

中文:
引理 isSeparatedMap_iff_disjoint_nhds
  条件: {f : X -> Y}
  结论: IsSeparatedMap f ↔
  证明: forall₃_congr fun x x' _ => by simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens x'),
    ← exists_and_left, and_assoc, and_comm, and_left_comm]

Depends on / 依赖: and_assoc, and_comm, and_left_comm, disjoint_iff, exists_and_left, nhds_basis_opens
-/
lemma isSeparatedMap_iff_disjoint_nhds {f : X -> Y} : IsSeparatedMap f ↔
    forall x₁ x₂, f x₁ = f x₂ -> x₁ != x₂ -> Disjoint (𝓝 x₁) (𝓝 x₂) :=
  forall₃_congr fun x x' _ => by simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens x'),
    ← exists_and_left, and_assoc, and_comm, and_left_comm]

/--
lemma `isSeparatedMap_iff_nhds` / 引理 `isSeparatedMap_iff_nhds`

English:
lemma isSeparatedMap_iff_nhds
  given: {f : X -> Y}
  statement: IsSeparatedMap f ↔
  proof: by
  simp_rw [isSeparatedMap_iff_disjoint_nhds, Filter.disjoint_iff]

中文:
引理 isSeparatedMap_iff_nhds
  条件: {f : X -> Y}
  结论: IsSeparatedMap f ↔
  证明: by
  simp_rw [isSeparatedMap_iff_disjoint_nhds, Filter.disjoint_iff]

Depends on / 依赖: Filter, Filter.disjoint_iff, disjoint_iff, isSeparatedMap_iff_disjoint_nhds, simp_rw
-/
lemma isSeparatedMap_iff_nhds {f : X -> Y} : IsSeparatedMap f ↔
    forall x₁ x₂, f x₁ = f x₂ -> x₁ != x₂ -> exists s₁ in 𝓝 x₁, exists s₂ in 𝓝 x₂, Disjoint s₁ s₂ := by
  simp_rw [isSeparatedMap_iff_disjoint_nhds, Filter.disjoint_iff]

open Set Filter in
/--
theorem `isSeparatedMap_iff_isClosed_diagonal` / 定理 `isSeparatedMap_iff_isClosed_diagonal`

English:
theorem isSeparatedMap_iff_isClosed_diagonal
  given: {f : X -> Y}
  proof: by
  simp_rw [isSeparatedMap_iff_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq]
  refine forall₄_congr fun x₁ x₂ _ _ => ⟨fun h => ?_, fun ⟨t, ht, t_sub⟩ => ?_⟩
  · simp_rw [← Filter.disjoint_iff, ← compl_diagonal_mem_prod] at h
    exact ⟨

中文:
定理 isSeparatedMap_iff_isClosed_diagonal
  条件: {f : X -> Y}
  证明: by
  simp_rw [isSeparatedMap_iff_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq]
  refine forall₄_congr fun x₁ x₂ _ _ => ⟨fun h => ?_, fun ⟨t, ht, t_sub⟩ => ?_⟩
  · simp_rw [← Filter.disjoint_iff, ← compl_diagonal_mem_prod] at h
    exact ⟨

Depends on / 依赖: Filter, Filter.disjoint_iff, Prod.forall, Subtype, Subtype.forall, compl_diagonal_mem_prod, disjoint_iff, disjoint_left, isOpen_compl_iff, isOpen_iff_mem_nhds, isSeparatedMap_iff_nhds, mem_prod_iff, mem_prod_iff.mp, nhds_induced, nhds_prod_eq, s_sub, simp_rw, subset_rfl, t_sub
-/
theorem isSeparatedMap_iff_isClosed_diagonal {f : X -> Y} :
    IsSeparatedMap f ↔ IsClosed f.pullbackDiagonal := by
  simp_rw [isSeparatedMap_iff_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq]
  refine forall₄_congr fun x₁ x₂ _ _ => ⟨fun h => ?_, fun ⟨t, ht, t_sub⟩ => ?_⟩
  · simp_rw [← Filter.disjoint_iff, ← compl_diagonal_mem_prod] at h
    exact ⟨_, h, subset_rfl⟩
  · obtain ⟨s₁, h₁, s₂, h₂, s_sub⟩ := mem_prod_iff.mp ht
    exact ⟨s₁, h₁, s₂, h₂, disjoint_left.2 fun x h₁ h₂ => @t_sub ⟨(x, x), rfl⟩ (s_sub ⟨h₁, h₂⟩) rfl⟩

/--
theorem `isSeparatedMap_iff_isClosedEmbedding` / 定理 `isSeparatedMap_iff_isClosedEmbedding`

English:
theorem isSeparatedMap_iff_isClosedEmbedding
  given: {f : X -> Y}
  proof: by
  rw [isSeparatedMap_iff_isClosed_diagonal]; rw [← range_toPullbackDiag]
  exact ⟨fun h => ⟨.toPullbackDiag f, h⟩, fun h => h.isClosed_range⟩

中文:
定理 isSeparatedMap_iff_isClosedEmbedding
  条件: {f : X -> Y}
  证明: by
  rw [isSeparatedMap_iff_isClosed_diagonal]; rw [← range_toPullbackDiag]
  exact ⟨fun h => ⟨.toPullbackDiag f, h⟩, fun h => h.isClosed_range⟩

Depends on / 依赖: h.isClosed_range, isClosed_range, isSeparatedMap_iff_isClosed_diagonal, range_toPullbackDiag, toPullbackDiag
-/
theorem isSeparatedMap_iff_isClosedEmbedding {f : X -> Y} :
    IsSeparatedMap f ↔ IsClosedEmbedding (toPullbackDiag f) := by
  rw [isSeparatedMap_iff_isClosed_diagonal]; rw [← range_toPullbackDiag]
  exact ⟨fun h => ⟨.toPullbackDiag f, h⟩, fun h => h.isClosed_range⟩

/--
theorem `isSeparatedMap_iff_isClosedMap` / 定理 `isSeparatedMap_iff_isClosedMap`

English:
theorem isSeparatedMap_iff_isClosedMap
  given: {f : X -> Y}
  proof: isSeparatedMap_iff_isClosedEmbedding.trans
    ⟨IsClosedEmbedding.isClosedMap, .of_continuous_injective_isClosedMap
      (IsEmbedding.toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩

中文:
定理 isSeparatedMap_iff_isClosedMap
  条件: {f : X -> Y}
  证明: isSeparatedMap_iff_isClosedEmbedding.trans
    ⟨IsClosedEmbedding.isClosedMap, .of_continuous_injective_isClosedMap
      (IsEmbedding.toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.isClosedMap, IsEmbedding, IsEmbedding.toPullbackDiag, continuous, injective_toPullbackDiag, isClosedMap, isSeparatedMap_iff_isClosedEmbedding, isSeparatedMap_iff_isClosedEmbedding.trans, of_continuous_injective_isClosedMap, toPullbackDiag
-/
theorem isSeparatedMap_iff_isClosedMap {f : X -> Y} :
    IsSeparatedMap f ↔ IsClosedMap (toPullbackDiag f) :=
  isSeparatedMap_iff_isClosedEmbedding.trans
    ⟨IsClosedEmbedding.isClosedMap, .of_continuous_injective_isClosedMap
      (IsEmbedding.toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩

open Function.Pullback in
/--
theorem `IsSeparatedMap.pullback` / 定理 `IsSeparatedMap.pullback`

English:
theorem IsSeparatedMap.pullback
  given: {f : X -> Y} (sep : IsSeparatedMap f) (g : A -> Y)
  proof: by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← preimage_map_fst_pullbackDiagonal]
  refine sep.preimage (Continuous.mapPullback ?_ ?_) <;>
  apply_rules [continuous_fst, continuous_subtype_val, Continuous.comp]

中文:
定理 IsSeparatedMap.pullback
  条件: {f : X -> Y} (sep : IsSeparatedMap f) (g : A -> Y)
  证明: by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← preimage_map_fst_pullbackDiagonal]
  refine sep.preimage (Continuous.mapPullback ?_ ?_) <;>
  apply_rules [continuous_fst, continuous_subtype_val, Continuous.comp]

Depends on / 依赖: Continuous, Continuous.comp, Continuous.mapPullback, apply_rules, continuous_fst, continuous_subtype_val, isSeparatedMap_iff_isClosed_diagonal, mapPullback, preimage, preimage_map_fst_pullbackDiagonal, sep.preimage
-/
theorem IsSeparatedMap.pullback {f : X -> Y} (sep : IsSeparatedMap f) (g : A -> Y) :
    IsSeparatedMap (@snd X Y A f g) := by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← preimage_map_fst_pullbackDiagonal]
  refine sep.preimage (Continuous.mapPullback ?_ ?_) <;>
  apply_rules [continuous_fst, continuous_subtype_val, Continuous.comp]

/--
theorem `IsSeparatedMap.comp_left` / 定理 `IsSeparatedMap.comp_left`

English:
theorem IsSeparatedMap.comp_left
  statement: {A} {f : X -> Y} (sep : IsSeparatedMap f) {g : Y -> A}
  proof: fun x₁ x₂ he => sep x₁ x₂ (inj he)

中文:
定理 IsSeparatedMap.comp_left
  结论: {A} {f : X -> Y} (sep : IsSeparatedMap f) {g : Y -> A}
  证明: fun x₁ x₂ he => sep x₁ x₂ (inj he)
-/
theorem IsSeparatedMap.comp_left {A} {f : X -> Y} (sep : IsSeparatedMap f) {g : Y -> A}
    (inj : g.Injective) : IsSeparatedMap (g ∘ f) := fun x₁ x₂ he => sep x₁ x₂ (inj he)

/--
theorem `IsSeparatedMap.comp_right` / 定理 `IsSeparatedMap.comp_right`

English:
theorem IsSeparatedMap.comp_right
  statement: {f : X -> Y} (sep : IsSeparatedMap f) {g : A -> X}
  proof: by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← inj.preimage_pullbackDiagonal]
  exact sep.preimage (cont.mapPullback cont)

中文:
定理 IsSeparatedMap.comp_right
  结论: {f : X -> Y} (sep : IsSeparatedMap f) {g : A -> X}
  证明: by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← inj.preimage_pullbackDiagonal]
  exact sep.preimage (cont.mapPullback cont)

Depends on / 依赖: cont.mapPullback, inj.preimage_pullbackDiagonal, isSeparatedMap_iff_isClosed_diagonal, mapPullback, preimage, preimage_pullbackDiagonal, sep.preimage
-/
theorem IsSeparatedMap.comp_right {f : X -> Y} (sep : IsSeparatedMap f) {g : A -> X}
    (cont : Continuous g) (inj : g.Injective) : IsSeparatedMap (f ∘ g) := by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← inj.preimage_pullbackDiagonal]
  exact sep.preimage (cont.mapPullback cont)

/--
Definition of `IsLocallyInjective` / `IsLocallyInjective` 的定义

English:
definition IsLocallyInjective
  signature: (f : X -> Y)
  body: forall x : X, exists U, IsOpen U ∧ x in U ∧ U.InjOn f

中文:
定义 IsLocallyInjective
  签名: (f : X -> Y)
  定义体: forall x : X, exists U, IsOpen U ∧ x in U ∧ U.InjOn f

Depends on / 依赖: IsOpen, U.InjOn
-/
def IsLocallyInjective (f : X -> Y) : Prop := forall x : X, exists U, IsOpen U ∧ x in U ∧ U.InjOn f

/--
lemma `Function.Injective.IsLocallyInjective` / 引理 `Function.Injective.IsLocallyInjective`

English:
lemma Function.Injective.IsLocallyInjective
  given: {f : X -> Y} (inj : f.Injective)
  proof: fun _ => ⟨_, isOpen_univ, trivial, fun _ _ _ _ => @inj _ _⟩

中文:
引理 Function.Injective.IsLocallyInjective
  条件: {f : X -> Y} (inj : f.Injective)
  证明: fun _ => ⟨_, isOpen_univ, trivial, fun _ _ _ _ => @inj _ _⟩

Depends on / 依赖: isOpen_univ
-/
lemma Function.Injective.IsLocallyInjective {f : X -> Y} (inj : f.Injective) :
    IsLocallyInjective f := fun _ => ⟨_, isOpen_univ, trivial, fun _ _ _ _ => @inj _ _⟩

/--
lemma `isLocallyInjective_iff_nhds` / 引理 `isLocallyInjective_iff_nhds`

English:
lemma isLocallyInjective_iff_nhds
  given: {f : X -> Y}
  proof: by
  constructor <;> intro h x
  · obtain ⟨U, ho, hm, hi⟩ := h x; exact ⟨U, ho.mem_nhds hm, hi⟩
  · obtain ⟨U, hn, hi⟩ := h x
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hn, hi.mono interior_subset⟩

中文:
引理 isLocallyInjective_iff_nhds
  条件: {f : X -> Y}
  证明: by
  constructor <;> intro h x
  · obtain ⟨U, ho, hm, hi⟩ := h x; exact ⟨U, ho.mem_nhds hm, hi⟩
  · obtain ⟨U, hn, hi⟩ := h x
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hn, hi.mono interior_subset⟩

Depends on / 依赖: hi.mono, ho.mem_nhds, interior, interior_subset, isOpen_interior, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.mpr, mem_nhds
-/
lemma isLocallyInjective_iff_nhds {f : X -> Y} :
    IsLocallyInjective f ↔ forall x : X, exists U in 𝓝 x, U.InjOn f := by
  constructor <;> intro h x
  · obtain ⟨U, ho, hm, hi⟩ := h x; exact ⟨U, ho.mem_nhds hm, hi⟩
  · obtain ⟨U, hn, hi⟩ := h x
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hn, hi.mono interior_subset⟩

/--
theorem `isLocallyInjective_iff_isOpen_diagonal` / 定理 `isLocallyInjective_iff_isOpen_diagonal`

English:
theorem isLocallyInjective_iff_isOpen_diagonal
  given: {f : X -> Y}
  proof: by
  simp_rw [isLocallyInjective_iff_nhds, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq, Filter.mem_comap]
  refine ⟨?_, fun h x => ?_⟩
  · rintro h x x' hx (rfl : x = x')
    obtain ⟨U, hn, hi⟩ := h x
    exact ⟨_, Filter.prod_mem_prod hn hn, fun {p} hp => hi hp.

中文:
定理 isLocallyInjective_iff_isOpen_diagonal
  条件: {f : X -> Y}
  证明: by
  simp_rw [isLocallyInjective_iff_nhds, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq, Filter.mem_comap]
  refine ⟨?_, fun h x => ?_⟩
  · rintro h x x' hx (rfl : x = x')
    obtain ⟨U, hn, hi⟩ := h x
    exact ⟨_, Filter.prod_mem_prod hn hn, fun {p} hp => hi hp.

Depends on / 依赖: Filter, Filter.inter_mem, Filter.mem_comap, Filter.mem_prod_iff.mp, Filter.prod_mem_prod, Prod.forall, Subtype, Subtype.forall, inter_mem, isLocallyInjective_iff_nhds, isOpen_iff_mem_nhds, mem_comap, mem_prod_iff, nhds_induced, nhds_prod_eq, prod_mem_prod, prod_sub, simp_rw, t_sub
-/
theorem isLocallyInjective_iff_isOpen_diagonal {f : X -> Y} :
    IsLocallyInjective f ↔ IsOpen f.pullbackDiagonal := by
  simp_rw [isLocallyInjective_iff_nhds, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq, Filter.mem_comap]
  refine ⟨?_, fun h x => ?_⟩
  · rintro h x x' hx (rfl : x = x')
    obtain ⟨U, hn, hi⟩ := h x
    exact ⟨_, Filter.prod_mem_prod hn hn, fun {p} hp => hi hp.1 hp.2 p.2⟩
  · obtain ⟨t, ht, t_sub⟩ := h x x rfl rfl
    obtain ⟨t₁, h₁, t₂, h₂, prod_sub⟩ := Filter.mem_prod_iff.mp ht
    exact ⟨t₁ inter t₂, Filter.inter_mem h₁ h₂,
      fun x₁ h₁ x₂ h₂ he => @t_sub ⟨(x₁, x₂), he⟩ (prod_sub ⟨h₁.1, h₂.2⟩)⟩

/--
theorem `IsLocallyInjective_iff_isOpenEmbedding` / 定理 `IsLocallyInjective_iff_isOpenEmbedding`

English:
theorem IsLocallyInjective_iff_isOpenEmbedding
  given: {f : X -> Y}
  proof: by
  rw [isLocallyInjective_iff_isOpen_diagonal]; rw [← range_toPullbackDiag]
  exact ⟨fun h => ⟨.toPullbackDiag f, h⟩, fun h => h.isOpen_range⟩

中文:
定理 IsLocallyInjective_iff_isOpenEmbedding
  条件: {f : X -> Y}
  证明: by
  rw [isLocallyInjective_iff_isOpen_diagonal]; rw [← range_toPullbackDiag]
  exact ⟨fun h => ⟨.toPullbackDiag f, h⟩, fun h => h.isOpen_range⟩

Depends on / 依赖: h.isOpen_range, isLocallyInjective_iff_isOpen_diagonal, isOpen_range, range_toPullbackDiag, toPullbackDiag
-/
theorem IsLocallyInjective_iff_isOpenEmbedding {f : X -> Y} :
    IsLocallyInjective f ↔ IsOpenEmbedding (toPullbackDiag f) := by
  rw [isLocallyInjective_iff_isOpen_diagonal]; rw [← range_toPullbackDiag]
  exact ⟨fun h => ⟨.toPullbackDiag f, h⟩, fun h => h.isOpen_range⟩

/--
theorem `isLocallyInjective_iff_isOpenMap` / 定理 `isLocallyInjective_iff_isOpenMap`

English:
theorem isLocallyInjective_iff_isOpenMap
  given: {f : X -> Y}
  proof: IsLocallyInjective_iff_isOpenEmbedding.trans
    ⟨IsOpenEmbedding.isOpenMap, .of_continuous_injective_isOpenMap
      (IsEmbedding.toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩

中文:
定理 isLocallyInjective_iff_isOpenMap
  条件: {f : X -> Y}
  证明: IsLocallyInjective_iff_isOpenEmbedding.trans
    ⟨IsOpenEmbedding.isOpenMap, .of_continuous_injective_isOpenMap
      (IsEmbedding.toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩

Depends on / 依赖: IsEmbedding, IsEmbedding.toPullbackDiag, IsLocallyInjective_iff_isOpenEmbedding, IsLocallyInjective_iff_isOpenEmbedding.trans, IsOpenEmbedding, IsOpenEmbedding.isOpenMap, continuous, injective_toPullbackDiag, isOpenMap, of_continuous_injective_isOpenMap, toPullbackDiag
-/
theorem isLocallyInjective_iff_isOpenMap {f : X -> Y} :
    IsLocallyInjective f ↔ IsOpenMap (toPullbackDiag f) :=
  IsLocallyInjective_iff_isOpenEmbedding.trans
    ⟨IsOpenEmbedding.isOpenMap, .of_continuous_injective_isOpenMap
      (IsEmbedding.toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩

/--
theorem `discreteTopology_iff_locallyInjective` / 定理 `discreteTopology_iff_locallyInjective`

English:
theorem discreteTopology_iff_locallyInjective
  given: (y : Y)
  proof: by
  rw [discreteTopology_iff_singleton_mem_nhds]; rw [isLocallyInjective_iff_nhds]
  refine forall_congr' fun x => ⟨fun h => ⟨{x}, h, Set.injOn_singleton _ _⟩, fun ⟨U, hU, inj⟩ => ?_⟩
  convert! hU; ext x'; refine ⟨?_, fun h => inj h (mem_of_mem_nhds hU) rfl⟩
  rintro rfl; exact mem_of_mem_nhds hU

中文:
定理 discreteTopology_iff_locallyInjective
  条件: (y : Y)
  证明: by
  rw [discreteTopology_iff_singleton_mem_nhds]; rw [isLocallyInjective_iff_nhds]
  refine forall_congr' fun x => ⟨fun h => ⟨{x}, h, Set.injOn_singleton _ _⟩, fun ⟨U, hU, inj⟩ => ?_⟩
  convert! hU; ext x'; refine ⟨?_, fun h => inj h (mem_of_mem_nhds hU) rfl⟩
  rintro rfl; exact mem_of_mem_nhds hU

Depends on / 依赖: Set.injOn_singleton, convert, discreteTopology_iff_singleton_mem_nhds, forall_congr, injOn_singleton, isLocallyInjective_iff_nhds, mem_of_mem_nhds
-/
theorem discreteTopology_iff_locallyInjective (y : Y) :
    DiscreteTopology X ↔ IsLocallyInjective fun _ : X => y := by
  rw [discreteTopology_iff_singleton_mem_nhds]; rw [isLocallyInjective_iff_nhds]
  refine forall_congr' fun x => ⟨fun h => ⟨{x}, h, Set.injOn_singleton _ _⟩, fun ⟨U, hU, inj⟩ => ?_⟩
  convert! hU; ext x'; refine ⟨?_, fun h => inj h (mem_of_mem_nhds hU) rfl⟩
  rintro rfl; exact mem_of_mem_nhds hU

/--
theorem `IsLocallyInjective.comp_left` / 定理 `IsLocallyInjective.comp_left`

English:
theorem IsLocallyInjective.comp_left
  statement: {A} {f : X -> Y} (hf : IsLocallyInjective f) {g : Y -> A}
  proof: fun x => let ⟨U, hU, hx, inj⟩ := hf x; ⟨U, hU, hx, hg.comp_injOn inj⟩

中文:
定理 IsLocallyInjective.comp_left
  结论: {A} {f : X -> Y} (hf : IsLocallyInjective f) {g : Y -> A}
  证明: fun x => let ⟨U, hU, hx, inj⟩ := hf x; ⟨U, hU, hx, hg.comp_injOn inj⟩

Depends on / 依赖: comp_injOn, hg.comp_injOn
-/
theorem IsLocallyInjective.comp_left {A} {f : X -> Y} (hf : IsLocallyInjective f) {g : Y -> A}
    (hg : g.Injective) : IsLocallyInjective (g ∘ f) :=
  fun x => let ⟨U, hU, hx, inj⟩ := hf x; ⟨U, hU, hx, hg.comp_injOn inj⟩

/--
theorem `IsLocallyInjective.comp_right` / 定理 `IsLocallyInjective.comp_right`

English:
theorem IsLocallyInjective.comp_right
  statement: {f : X -> Y} (hf : IsLocallyInjective f) {g : A -> X}
  proof: by
  rw [isLocallyInjective_iff_isOpen_diagonal] at hf ⊢
  rw [← hg.preimage_pullbackDiagonal]
  apply hf.preimage (cont.mapPullback cont)

中文:
定理 IsLocallyInjective.comp_right
  结论: {f : X -> Y} (hf : IsLocallyInjective f) {g : A -> X}
  证明: by
  rw [isLocallyInjective_iff_isOpen_diagonal] at hf ⊢
  rw [← hg.preimage_pullbackDiagonal]
  apply hf.preimage (cont.mapPullback cont)

Depends on / 依赖: cont.mapPullback, hf.preimage, hg.preimage_pullbackDiagonal, isLocallyInjective_iff_isOpen_diagonal, mapPullback, preimage, preimage_pullbackDiagonal
-/
theorem IsLocallyInjective.comp_right {f : X -> Y} (hf : IsLocallyInjective f) {g : A -> X}
    (cont : Continuous g) (hg : g.Injective) : IsLocallyInjective (f ∘ g) := by
  rw [isLocallyInjective_iff_isOpen_diagonal] at hf ⊢
  rw [← hg.preimage_pullbackDiagonal]
  apply hf.preimage (cont.mapPullback cont)

section eqLocus

variable {f : X -> Y} {g₁ g₂ : A -> X} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
include h₁ h₂

/--
theorem `IsSeparatedMap.isClosed_eqLocus` / 定理 `IsSeparatedMap.isClosed_eqLocus`

English:
theorem IsSeparatedMap.isClosed_eqLocus
  given: (sep : IsSeparatedMap f) (he : f ∘ g₁ = f ∘ g₂)
  proof: let g : A -> f.Pullback f := fun a => ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isSeparatedMap_iff_isClosed_diagonal.mp sep).preimage (by fun_prop : Continuous g)

中文:
定理 IsSeparatedMap.isClosed_eqLocus
  条件: (sep : IsSeparatedMap f) (he : f ∘ g₁ = f ∘ g₂)
  证明: let g : A -> f.Pullback f := fun a => ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isSeparatedMap_iff_isClosed_diagonal.mp sep).preimage (by fun_prop : Continuous g)

Depends on / 依赖: Continuous, Pullback, congr_fun, f.Pullback, fun_prop, isSeparatedMap_iff_isClosed_diagonal, isSeparatedMap_iff_isClosed_diagonal.mp, preimage
-/
theorem IsSeparatedMap.isClosed_eqLocus (sep : IsSeparatedMap f) (he : f ∘ g₁ = f ∘ g₂) :
    IsClosed {a | g₁ a = g₂ a} :=
  let g : A -> f.Pullback f := fun a => ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isSeparatedMap_iff_isClosed_diagonal.mp sep).preimage (by fun_prop : Continuous g)

/--
theorem `IsLocallyInjective.isOpen_eqLocus` / 定理 `IsLocallyInjective.isOpen_eqLocus`

English:
theorem IsLocallyInjective.isOpen_eqLocus
  given: (inj : IsLocallyInjective f) (he : f ∘ g₁ = f ∘ g₂)
  proof: let g : A -> f.Pullback f := fun a => ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isLocallyInjective_iff_isOpen_diagonal.mp inj).preimage (by fun_prop : Continuous g)

中文:
定理 IsLocallyInjective.isOpen_eqLocus
  条件: (inj : IsLocallyInjective f) (he : f ∘ g₁ = f ∘ g₂)
  证明: let g : A -> f.Pullback f := fun a => ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isLocallyInjective_iff_isOpen_diagonal.mp inj).preimage (by fun_prop : Continuous g)

Depends on / 依赖: Continuous, Pullback, congr_fun, f.Pullback, fun_prop, isLocallyInjective_iff_isOpen_diagonal, isLocallyInjective_iff_isOpen_diagonal.mp, preimage
-/
theorem IsLocallyInjective.isOpen_eqLocus (inj : IsLocallyInjective f) (he : f ∘ g₁ = f ∘ g₂) :
    IsOpen {a | g₁ a = g₂ a} :=
  let g : A -> f.Pullback f := fun a => ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isLocallyInjective_iff_isOpen_diagonal.mp inj).preimage (by fun_prop : Continuous g)

end eqLocus

variable {X E A : Type*} [TopologicalSpace E] [TopologicalSpace A] {p : E -> X}

namespace IsSeparatedMap

variable {s : Set A} {g g₁ g₂ : A -> E} (sep : IsSeparatedMap p) (inj : IsLocallyInjective p)
include sep inj

/--
theorem `eq_of_comp_eq` / 定理 `eq_of_comp_eq`

English:
theorem eq_of_comp_eq
  proof: funext fun a' => by
  apply (IsClopen.eq_univ ⟨sep.isClosed_eqLocus h₁ h₂ he, inj.isOpen_eqLocus h₁ h₂ he⟩ ⟨a, ha⟩).symm
    ▸ Set.mem_univ a'

中文:
定理 eq_of_comp_eq
  证明: funext fun a' => by
  apply (IsClopen.eq_univ ⟨sep.isClosed_eqLocus h₁ h₂ he, inj.isOpen_eqLocus h₁ h₂ he⟩ ⟨a, ha⟩).symm
    ▸ Set.mem_univ a'

Depends on / 依赖: IsClopen, IsClopen.eq_univ, Set.mem_univ, eq_univ, inj.isOpen_eqLocus, isClosed_eqLocus, isOpen_eqLocus, mem_univ, sep.isClosed_eqLocus
-/
theorem eq_of_comp_eq
    [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ := funext fun a' => by
  apply (IsClopen.eq_univ ⟨sep.isClosed_eqLocus h₁ h₂ he, inj.isOpen_eqLocus h₁ h₂ he⟩ ⟨a, ha⟩).symm
    ▸ Set.mem_univ a'

/--
theorem `eqOn_of_comp_eqOn` / 定理 `eqOn_of_comp_eqOn`

English:
theorem eqOn_of_comp_eqOn
  statement: (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
  proof: by
  rw [← Set.domRestrict_eq_domRestrict_iff] at he ⊢
  rw [continuousOn_iff_continuous_domRestrict] at h₁ h₂
  rw [isPreconnected_iff_preconnectedSpace] at hs
  exact sep.eq_of_comp_eq inj h₁ h₂ he ⟨a, has⟩ ha

中文:
定理 eqOn_of_comp_eqOn
  结论: (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
  证明: by
  rw [← Set.domRestrict_eq_domRestrict_iff] at he ⊢
  rw [continuousOn_iff_continuous_domRestrict] at h₁ h₂
  rw [isPreconnected_iff_preconnectedSpace] at hs
  exact sep.eq_of_comp_eq inj h₁ h₂ he ⟨a, has⟩ ha

Depends on / 依赖: Set.domRestrict_eq_domRestrict_iff, continuousOn_iff_continuous_domRestrict, domRestrict_eq_domRestrict_iff, eq_of_comp_eq, isPreconnected_iff_preconnectedSpace, sep.eq_of_comp_eq
-/
theorem eqOn_of_comp_eqOn (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (he : s.EqOn (p ∘ g₁) (p ∘ g₂)) {a : A} (has : a in s) (ha : g₁ a = g₂ a) : s.EqOn g₁ g₂ := by
  rw [← Set.domRestrict_eq_domRestrict_iff] at he ⊢
  rw [continuousOn_iff_continuous_domRestrict] at h₁ h₂
  rw [isPreconnected_iff_preconnectedSpace] at hs
  exact sep.eq_of_comp_eq inj h₁ h₂ he ⟨a, has⟩ ha

/--
theorem `const_of_comp` / 定理 `const_of_comp`

English:
theorem const_of_comp
  statement: [PreconnectedSpace A] (cont : Continuous g)
  proof: congr_fun (sep.eq_of_comp_eq inj cont continuous_const (funext fun a => he a a') a' rfl) a

中文:
定理 const_of_comp
  结论: [PreconnectedSpace A] (cont : Continuous g)
  证明: congr_fun (sep.eq_of_comp_eq inj cont continuous_const (funext fun a => he a a') a' rfl) a

Depends on / 依赖: congr_fun, continuous_const, eq_of_comp_eq, sep.eq_of_comp_eq
-/
theorem const_of_comp [PreconnectedSpace A] (cont : Continuous g)
    (he : forall a a', p (g a) = p (g a')) (a a') : g a = g a' :=
  congr_fun (sep.eq_of_comp_eq inj cont continuous_const (funext fun a => he a a') a' rfl) a

/--
theorem `constOn_of_comp` / 定理 `constOn_of_comp`

English:
theorem constOn_of_comp
  statement: (hs : IsPreconnected s) (cont : ContinuousOn g s)
  proof: sep.eqOn_of_comp_eqOn inj hs cont continuous_const.continuousOn
    (fun a ha => he a ha a' ha') ha' rfl ha

中文:
定理 constOn_of_comp
  结论: (hs : IsPreconnected s) (cont : ContinuousOn g s)
  证明: sep.eqOn_of_comp_eqOn inj hs cont continuous_const.continuousOn
    (fun a ha => he a ha a' ha') ha' rfl ha

Depends on / 依赖: continuousOn, continuous_const, continuous_const.continuousOn, eqOn_of_comp_eqOn, sep.eqOn_of_comp_eqOn
-/
theorem constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s)
    (he : forall a in s, forall a' in s, p (g a) = p (g a'))
    {a a'} (ha : a in s) (ha' : a' in s) : g a = g a' :=
  sep.eqOn_of_comp_eqOn inj hs cont continuous_const.continuousOn
    (fun a ha => he a ha a' ha') ha' rfl ha

end IsSeparatedMap
