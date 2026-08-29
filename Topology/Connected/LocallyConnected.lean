/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.Clopen

/-!
# Locally connected topological spaces

A topological space is **locally connected** if each neighborhood filter admits a basis
of connected *open* sets. Local connectivity is equivalent to each point having a basis
of connected (not necessarily open) sets --- but in a non-trivial way, so we choose this definition
and prove the equivalence later in `locallyConnectedSpace_iff_connected_basis`.
-/

public section

open Set Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι -> Type*} [TopologicalSpace α]
  {s t u v : Set α}

section LocallyConnectedSpace

/--
Definition of `LocallyConnectedSpace` / `LocallyConnectedSpace` 的定义

English:
class LocallyConnectedSpace
  parameters: (α : Type*) [TopologicalSpace α]
  axioms and operations (1):
    - open_connected_basis : forall x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x in s ∧ IsConnected s) id

中文:
类 LocallyConnectedSpace
  参数: (α : 类型) [TopologicalSpace α]
  公理与运算 (1 个):
    - open_connected_basis : 对任意 x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x in s ∧ IsConnected s) id
-/
class LocallyConnectedSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- Open connected neighborhoods form a basis of the neighborhoods filter. -/
  open_connected_basis : forall x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x in s ∧ IsConnected s) id

/--
theorem `locallyConnectedSpace_iff_hasBasis_isOpen_isConnected` / 定理 `locallyConnectedSpace_iff_hasBasis_isOpen_isConnected`

English:
theorem locallyConnectedSpace_iff_hasBasis_isOpen_isConnected
  proof: ⟨@LocallyConnectedSpace.open_connected_basis _ _, LocallyConnectedSpace.mk⟩

中文:
定理 locallyConnectedSpace_iff_hasBasis_isOpen_isConnected
  证明: ⟨@LocallyConnectedSpace.open_connected_basis _ _, LocallyConnectedSpace.mk⟩

Depends on / 依赖: LocallyConnectedSpace, LocallyConnectedSpace.mk, LocallyConnectedSpace.open_connected_basis, open_connected_basis
-/
theorem locallyConnectedSpace_iff_hasBasis_isOpen_isConnected :
    LocallyConnectedSpace α ↔
      forall x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x in s ∧ IsConnected s) id :=
  ⟨@LocallyConnectedSpace.open_connected_basis _ _, LocallyConnectedSpace.mk⟩

/--
theorem `locallyConnectedSpace_iff_subsets_isOpen_isConnected` / 定理 `locallyConnectedSpace_iff_subsets_isOpen_isConnected`

English:
theorem locallyConnectedSpace_iff_subsets_isOpen_isConnected
  proof: by
  simp_rw [locallyConnectedSpace_iff_hasBasis_isOpen_isConnected]
  refine forall_congr' fun _ => ?_
  constructor
  · intro h U hU
    rcases h.mem_iff.mp hU with ⟨V, hV, hVU⟩
    exact ⟨V, hVU, hV⟩
  · exact fun h => ⟨fun U => ⟨fun hU =>
      let ⟨V, hVU, hV⟩ := h U hU
      ⟨V, hV, hVU⟩, fun 

中文:
定理 locallyConnectedSpace_iff_subsets_isOpen_isConnected
  证明: by
  simp_rw [locallyConnectedSpace_iff_hasBasis_isOpen_isConnected]
  refine forall_congr' fun _ => ?_
  constructor
  · intro h U hU
    rcases h.mem_iff.mp hU with ⟨V, hV, hVU⟩
    exact ⟨V, hVU, hV⟩
  · exact fun h => ⟨fun U => ⟨fun hU =>
      let ⟨V, hVU, hV⟩ := h U hU
      ⟨V, hV, hVU⟩, fun 

Depends on / 依赖: forall_congr, h.mem_iff.mp, locallyConnectedSpace_iff_hasBasis_isOpen_isConnected, mem_iff, mem_nhds_iff, mem_nhds_iff.mpr, simp_rw
-/
theorem locallyConnectedSpace_iff_subsets_isOpen_isConnected :
    LocallyConnectedSpace α ↔
      forall x, forall U in 𝓝 x, exists V : Set α, V subseteq U ∧ IsOpen V ∧ x in V ∧ IsConnected V := by
  simp_rw [locallyConnectedSpace_iff_hasBasis_isOpen_isConnected]
  refine forall_congr' fun _ => ?_
  constructor
  · intro h U hU
    rcases h.mem_iff.mp hU with ⟨V, hV, hVU⟩
    exact ⟨V, hVU, hV⟩
  · exact fun h => ⟨fun U => ⟨fun hU =>
      let ⟨V, hVU, hV⟩ := h U hU
      ⟨V, hV, hVU⟩, fun ⟨V, ⟨hV, hxV, _⟩, hVU⟩ => mem_nhds_iff.mpr ⟨V, hVU, hV, hxV⟩⟩⟩

/-- A space with discrete topology is a locally connected space. -/
instance (priority := 100) DiscreteTopology.toLocallyConnectedSpace (α) [TopologicalSpace α]
    [DiscreteTopology α] : LocallyConnectedSpace α :=
  locallyConnectedSpace_iff_subsets_isOpen_isConnected.2 fun x _U hU =>
⟨{x}, singleton_subset_iff.2 mem_of_mem_nhds hU, isOpen_discrete _, rfl,
      isConnected_singleton⟩

/--
theorem `connectedComponentIn_mem_nhds` / 定理 `connectedComponentIn_mem_nhds`

English:
theorem connectedComponentIn_mem_nhds
  given: [LocallyConnectedSpace α] {F : Set α} {x : α} (h : F in 𝓝 x)
  proof: by
  rw [(LocallyConnectedSpace.open_connected_basis x).mem_iff] at h
  rcases h with ⟨s, ⟨h1s, hxs, h2s⟩, hsF⟩
  exact mem_nhds_iff.mpr ⟨s, h2s.isPreconnected.subset_connectedComponentIn hxs hsF, h1s, hxs⟩

中文:
定理 connectedComponentIn_mem_nhds
  条件: [LocallyConnectedSpace α] {F : Set α} {x : α} (h : F in 𝓝 x)
  证明: by
  rw [(LocallyConnectedSpace.open_connected_basis x).mem_iff] at h
  rcases h with ⟨s, ⟨h1s, hxs, h2s⟩, hsF⟩
  exact mem_nhds_iff.mpr ⟨s, h2s.isPreconnected.subset_connectedComponentIn hxs hsF, h1s, hxs⟩

Depends on / 依赖: LocallyConnectedSpace, LocallyConnectedSpace.open_connected_basis, h2s.isPreconnected.subset_connectedComponentIn, isPreconnected, mem_iff, mem_nhds_iff, mem_nhds_iff.mpr, open_connected_basis, subset_connectedComponentIn
-/
theorem connectedComponentIn_mem_nhds [LocallyConnectedSpace α] {F : Set α} {x : α} (h : F in 𝓝 x) :
    connectedComponentIn F x in 𝓝 x := by
  rw [(LocallyConnectedSpace.open_connected_basis x).mem_iff] at h
  rcases h with ⟨s, ⟨h1s, hxs, h2s⟩, hsF⟩
  exact mem_nhds_iff.mpr ⟨s, h2s.isPreconnected.subset_connectedComponentIn hxs hsF, h1s, hxs⟩

/--
theorem `IsOpen.connectedComponentIn` / 定理 `IsOpen.connectedComponentIn`

English:
theorem IsOpen.connectedComponentIn
  statement: [LocallyConnectedSpace α] {F : Set α} {x : α}
  proof: by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [connectedComponentIn_eq hy]
  exact connectedComponentIn_mem_nhds (hF.mem_nhds <| connectedComponentIn_subset F x hy)

中文:
定理 IsOpen.connectedComponentIn
  结论: [LocallyConnectedSpace α] {F : Set α} {x : α}
  证明: by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [connectedComponentIn_eq hy]
  exact connectedComponentIn_mem_nhds (hF.mem_nhds <| connectedComponentIn_subset F x hy)
-/
protected theorem IsOpen.connectedComponentIn [LocallyConnectedSpace α] {F : Set α} {x : α}
    (hF : IsOpen F) : IsOpen (connectedComponentIn F x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [connectedComponentIn_eq hy]
  exact connectedComponentIn_mem_nhds (hF.mem_nhds <| connectedComponentIn_subset F x hy)

/--
theorem `isOpen_connectedComponent` / 定理 `isOpen_connectedComponent`

English:
theorem isOpen_connectedComponent
  given: [LocallyConnectedSpace α] {x : α}
  proof: by
  rw [← connectedComponentIn_univ]
  exact isOpen_univ.connectedComponentIn

中文:
定理 isOpen_connectedComponent
  条件: [LocallyConnectedSpace α] {x : α}
  证明: by
  rw [← connectedComponentIn_univ]
  exact isOpen_univ.connectedComponentIn

Depends on / 依赖: connectedComponentIn, connectedComponentIn_univ, isOpen_univ, isOpen_univ.connectedComponentIn
-/
theorem isOpen_connectedComponent [LocallyConnectedSpace α] {x : α} :
    IsOpen (connectedComponent x) := by
  rw [← connectedComponentIn_univ]
  exact isOpen_univ.connectedComponentIn

/--
theorem `isClopen_connectedComponent` / 定理 `isClopen_connectedComponent`

English:
theorem isClopen_connectedComponent
  given: [LocallyConnectedSpace α] {x : α}
  proof: ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩

中文:
定理 isClopen_connectedComponent
  条件: [LocallyConnectedSpace α] {x : α}
  证明: ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩

Depends on / 依赖: isClosed_connectedComponent, isOpen_connectedComponent
-/
theorem isClopen_connectedComponent [LocallyConnectedSpace α] {x : α} :
    IsClopen (connectedComponent x) :=
  ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩

/--
theorem `locallyConnectedSpace_iff_connectedComponentIn_open` / 定理 `locallyConnectedSpace_iff_connectedComponentIn_open`

English:
theorem locallyConnectedSpace_iff_connectedComponentIn_open
  proof: by
  constructor
  · intro h
    exact fun F hF x _ => hF.connectedComponentIn
  · intro h
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    refine fun x U hU =>
        ⟨connectedComponentIn (interior U) x,
          (connectedComponentIn_subset _ _).trans interior_subset, h _ isOpe

中文:
定理 locallyConnectedSpace_iff_connectedComponentIn_open
  证明: by
  constructor
  · intro h
    exact fun F hF x _ => hF.connectedComponentIn
  · intro h
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    refine fun x U hU =>
        ⟨connectedComponentIn (interior U) x,
          (connectedComponentIn_subset _ _).trans interior_subset, h _ isOpe

Depends on / 依赖: connectedComponentIn, connectedComponentIn_subset, hF.connectedComponentIn, interior, interior_subset, isConnected_connectedComponentIn_iff, isConnected_connectedComponentIn_iff.mpr, isOpen_interior, locallyConnectedSpace_iff_subsets_isOpen_isConnected, mem_connectedComponentIn, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.mpr
-/
theorem locallyConnectedSpace_iff_connectedComponentIn_open :
    LocallyConnectedSpace α ↔
      forall F : Set α, IsOpen F -> forall x in F, IsOpen (connectedComponentIn F x) := by
  constructor
  · intro h
    exact fun F hF x _ => hF.connectedComponentIn
  · intro h
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    refine fun x U hU =>
        ⟨connectedComponentIn (interior U) x,
          (connectedComponentIn_subset _ _).trans interior_subset, h _ isOpen_interior x ?_,
          mem_connectedComponentIn ?_, isConnected_connectedComponentIn_iff.mpr ?_⟩ <;>
      exact mem_interior_iff_mem_nhds.mpr hU

/--
theorem `locallyConnectedSpace_iff_connected_subsets` / 定理 `locallyConnectedSpace_iff_connected_subsets`

English:
theorem locallyConnectedSpace_iff_connected_subsets
  proof: by
  constructor
  · rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro h x U hxU
    rcases h x U hxU with ⟨V, hVU, hV₁, hxV, hV₂⟩
    exact ⟨V, hV₁.mem_nhds hxV, hV₂.isPreconnected, hVU⟩
  · rw [locallyConnectedSpace_iff_connectedComponentIn_open]
    refine fun h U hU x _ => isOp

中文:
定理 locallyConnectedSpace_iff_connected_subsets
  证明: by
  constructor
  · rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro h x U hxU
    rcases h x U hxU with ⟨V, hVU, hV₁, hxV, hV₂⟩
    exact ⟨V, hV₁.mem_nhds hxV, hV₂.isPreconnected, hVU⟩
  · rw [locallyConnectedSpace_iff_connectedComponentIn_open]
    refine fun h U hU x _ => isOp

Depends on / 依赖: Filter, Filter.mem_of_superset, connectedComponentIn_eq, connectedComponentIn_subset, hU.mem_nhds, hV.subset_connectedComponentIn, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.mpr, isPreconnected, locallyConnectedSpace_iff_connectedComponentIn_open, locallyConnectedSpace_iff_subsets_isOpen_isConnected, mem_nhds, mem_of_superset, subset_connectedComponentIn
-/
theorem locallyConnectedSpace_iff_connected_subsets :
    LocallyConnectedSpace α ↔ forall (x : α), forall U in 𝓝 x, exists V in 𝓝 x, IsPreconnected V ∧ V subseteq U := by
  constructor
  · rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro h x U hxU
    rcases h x U hxU with ⟨V, hVU, hV₁, hxV, hV₂⟩
    exact ⟨V, hV₁.mem_nhds hxV, hV₂.isPreconnected, hVU⟩
  · rw [locallyConnectedSpace_iff_connectedComponentIn_open]
    refine fun h U hU x _ => isOpen_iff_mem_nhds.mpr fun y hy => ?_
    rw [connectedComponentIn_eq hy]
    rcases h y U (hU.mem_nhds <| (connectedComponentIn_subset _ _) hy) with ⟨V, hVy, hV, hVU⟩
    exact Filter.mem_of_superset hVy (hV.subset_connectedComponentIn (mem_of_mem_nhds hVy) hVU)

/--
theorem `locallyConnectedSpace_iff_connected_basis` / 定理 `locallyConnectedSpace_iff_connected_basis`

English:
theorem locallyConnectedSpace_iff_connected_basis
  proof: by
  rw [locallyConnectedSpace_iff_connected_subsets]
  exact forall_congr' fun x => Filter.hasBasis_self.symm

中文:
定理 locallyConnectedSpace_iff_connected_basis
  证明: by
  rw [locallyConnectedSpace_iff_connected_subsets]
  exact forall_congr' fun x => Filter.hasBasis_self.symm

Depends on / 依赖: Filter, Filter.hasBasis_self.symm, forall_congr, hasBasis_self, locallyConnectedSpace_iff_connected_subsets
-/
theorem locallyConnectedSpace_iff_connected_basis :
    LocallyConnectedSpace α ↔
      forall x, (𝓝 x).HasBasis (fun s : Set α => s in 𝓝 x ∧ IsPreconnected s) id := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  exact forall_congr' fun x => Filter.hasBasis_self.symm

/--
theorem `locallyConnectedSpace_of_connected_bases` / 定理 `locallyConnectedSpace_of_connected_bases`

English:
theorem locallyConnectedSpace_of_connected_bases
  statement: {ι : Type*} (b : α -> ι -> Set α) (p : α -> ι -> Prop)
  proof: by
  rw [locallyConnectedSpace_iff_connected_basis]
  exact fun x =>
    (hbasis x).to_hasBasis
      (fun i hi => ⟨b x i, ⟨(hbasis x).mem_of_mem hi, hconnected x i hi⟩, subset_rfl⟩) fun s hs =>
      ⟨(hbasis x).index s hs.1, ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩

中文:
定理 locallyConnectedSpace_of_connected_bases
  结论: {ι : 类型} (b : α -> ι -> Set α) (p : α -> ι -> 命题)
  证明: by
  rw [locallyConnectedSpace_iff_connected_basis]
  exact fun x =>
    (hbasis x).to_hasBasis
      (fun i hi => ⟨b x i, ⟨(hbasis x).mem_of_mem hi, hconnected x i hi⟩, subset_rfl⟩) fun s hs =>
      ⟨(hbasis x).index s hs.1, ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩

Depends on / 依赖: hbasis, hconnected, locallyConnectedSpace_iff_connected_basis, mem_of_mem, property_index, set_index_subset, subset_rfl, to_hasBasis
-/
theorem locallyConnectedSpace_of_connected_bases {ι : Type*} (b : α -> ι -> Set α) (p : α -> ι -> Prop)
    (hbasis : forall x, (𝓝 x).HasBasis (p x) (b x))
    (hconnected : forall x i, p x i -> IsPreconnected (b x i)) : LocallyConnectedSpace α := by
  rw [locallyConnectedSpace_iff_connected_basis]
  exact fun x =>
    (hbasis x).to_hasBasis
      (fun i hi => ⟨b x i, ⟨(hbasis x).mem_of_mem hi, hconnected x i hi⟩, subset_rfl⟩) fun s hs =>
      ⟨(hbasis x).index s hs.1, ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩

/--
theorem `TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected` / 定理 `TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected`

English:
theorem TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected
  given: [LocallyConnectedSpace α]
  proof: .of_hasBasis_nhds fun x =>
    (LocallyConnectedSpace.open_connected_basis x).congr
      (by grind [IsConnected, Set.Nonempty])
      (fun _ _ => rfl)

中文:
定理 TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected
  条件: [LocallyConnectedSpace α]
  证明: .of_hasBasis_nhds fun x =>
    (LocallyConnectedSpace.open_connected_basis x).congr
      (by grind [IsConnected, Set.Nonempty])
      (fun _ _ => rfl)

Depends on / 依赖: IsConnected, LocallyConnectedSpace, LocallyConnectedSpace.open_connected_basis, Nonempty, Set.Nonempty, of_hasBasis_nhds, open_connected_basis
-/
theorem TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected [LocallyConnectedSpace α] :
    TopologicalSpace.IsTopologicalBasis {s : Set α | IsOpen s ∧ IsPreconnected s} :=
  .of_hasBasis_nhds fun x =>
    (LocallyConnectedSpace.open_connected_basis x).congr
      (by grind [IsConnected, Set.Nonempty])
      (fun _ _ => rfl)

/--
theorem `locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected` / 定理 `locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected`

English:
theorem locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected
  proof: .isOpen_isPreconnected
  mpr h := ⟨fun _ => h.nhds_hasBasis.congr (by grind [IsConnected, Set.Nonempty]) (fun _ _ => rfl)⟩

中文:
定理 locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected
  证明: .isOpen_isPreconnected
  mpr h := ⟨fun _ => h.nhds_hasBasis.congr (by grind [IsConnected, Set.Nonempty]) (fun _ _ => rfl)⟩

Depends on / 依赖: isOpen_isPreconnected
-/
theorem locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected :
    LocallyConnectedSpace α ↔
      TopologicalSpace.IsTopologicalBasis {s : Set α | IsOpen s ∧ IsPreconnected s} where
  mp _ := .isOpen_isPreconnected
  mpr h := ⟨fun _ => h.nhds_hasBasis.congr (by grind [IsConnected, Set.Nonempty]) (fun _ _ => rfl)⟩

/--
lemma `Topology.IsOpenEmbedding.locallyConnectedSpace` / 引理 `Topology.IsOpenEmbedding.locallyConnectedSpace`

English:
lemma Topology.IsOpenEmbedding.locallyConnectedSpace
  statement: [LocallyConnectedSpace α] [TopologicalSpace β]
  proof: by
  refine locallyConnectedSpace_of_connected_bases (fun _ s => f ⁻¹' s)
    (fun x s => (IsOpen s ∧ f x in s ∧ IsConnected s) ∧ s subseteq range f) (fun x => ?_)
    (fun x s hxs => hxs.1.2.2.isPreconnected.preimage_of_isOpenMap h.injective h.isOpenMap hxs.2)
  rw [h.nhds_eq_comap]
.restrict_subse

中文:
引理 Topology.IsOpenEmbedding.locallyConnectedSpace
  结论: [LocallyConnectedSpace α] [TopologicalSpace β]
  证明: by
  refine locallyConnectedSpace_of_connected_bases (fun _ s => f ⁻¹' s)
    (fun x s => (IsOpen s ∧ f x in s ∧ IsConnected s) ∧ s subseteq range f) (fun x => ?_)
    (fun x s hxs => hxs.1.2.2.isPreconnected.preimage_of_isOpenMap h.injective h.isOpenMap hxs.2)
  rw [h.nhds_eq_comap]
.restrict_subse

Depends on / 依赖: IsConnected, IsOpen, LocallyConnectedSpace, LocallyConnectedSpace.open_connected_basis, h.injective, h.isOpenMap, h.isOpen_range.mem_nhds, h.nhds_eq_comap, injective, isOpenMap, isOpen_range, isPreconnected, isPreconnected.preimage_of_isOpenMap, locallyConnectedSpace_of_connected_bases, mem_nhds, mem_range_self, nhds_eq_comap, open_connected_basis, preimage_of_isOpenMap, restrict_subset
-/
lemma Topology.IsOpenEmbedding.locallyConnectedSpace [LocallyConnectedSpace α] [TopologicalSpace β]
    {f : β -> α} (h : IsOpenEmbedding f) : LocallyConnectedSpace β := by
  refine locallyConnectedSpace_of_connected_bases (fun _ s => f ⁻¹' s)
    (fun x s => (IsOpen s ∧ f x in s ∧ IsConnected s) ∧ s subseteq range f) (fun x => ?_)
    (fun x s hxs => hxs.1.2.2.isPreconnected.preimage_of_isOpenMap h.injective h.isOpenMap hxs.2)
  rw [h.nhds_eq_comap]
.restrict_subset exact LocallyConnectedSpace.open_connected_basis (f x)
.comap _ (h.isOpen_range.mem_nhds <| mem_range_self _)

/--
theorem `IsOpen.locallyConnectedSpace` / 定理 `IsOpen.locallyConnectedSpace`

English:
theorem IsOpen.locallyConnectedSpace
  given: [LocallyConnectedSpace α] {U : Set α} (hU : IsOpen U)
  proof: hU.isOpenEmbedding_subtypeVal.locallyConnectedSpace

中文:
定理 IsOpen.locallyConnectedSpace
  条件: [LocallyConnectedSpace α] {U : Set α} (hU : IsOpen U)
  证明: hU.isOpenEmbedding_subtypeVal.locallyConnectedSpace

Depends on / 依赖: hU.isOpenEmbedding_subtypeVal.locallyConnectedSpace, isOpenEmbedding_subtypeVal, locallyConnectedSpace
-/
theorem IsOpen.locallyConnectedSpace [LocallyConnectedSpace α] {U : Set α} (hU : IsOpen U) :
    LocallyConnectedSpace U :=
  hU.isOpenEmbedding_subtypeVal.locallyConnectedSpace

/--
theorem `Topology.IsCoinducing.locallyConnectedSpace` / 定理 `Topology.IsCoinducing.locallyConnectedSpace`

English:
theorem Topology.IsCoinducing.locallyConnectedSpace
  statement: [LocallyConnectedSpace α]
  proof: by
  refine locallyConnectedSpace_iff_connectedComponentIn_open.2 fun F hF y _ => ?_
  rw [← hf.isOpen_preimage]; rw [hf.continuous.continuousOn.preimage_connectedComponentIn]
  exact isOpen_biUnion fun x _ => (hF.preimage hf.continuous).connectedComponentIn

中文:
定理 Topology.IsCoinducing.locallyConnectedSpace
  结论: [LocallyConnectedSpace α]
  证明: by
  refine locallyConnectedSpace_iff_connectedComponentIn_open.2 fun F hF y _ => ?_
  rw [← hf.isOpen_preimage]; rw [hf.continuous.continuousOn.preimage_connectedComponentIn]
  exact isOpen_biUnion fun x _ => (hF.preimage hf.continuous).connectedComponentIn

Depends on / 依赖: connectedComponentIn, continuous, continuousOn, hF.preimage, hf.continuous, hf.continuous.continuousOn.preimage_connectedComponentIn, hf.isOpen_preimage, isOpen_biUnion, isOpen_preimage, locallyConnectedSpace_iff_connectedComponentIn_open, preimage, preimage_connectedComponentIn
-/
theorem Topology.IsCoinducing.locallyConnectedSpace [LocallyConnectedSpace α]
    [TopologicalSpace β] {f : α -> β} (hf : IsCoinducing f) : LocallyConnectedSpace β := by
  refine locallyConnectedSpace_iff_connectedComponentIn_open.2 fun F hF y _ => ?_
  rw [← hf.isOpen_preimage]; rw [hf.continuous.continuousOn.preimage_connectedComponentIn]
  exact isOpen_biUnion fun x _ => (hF.preimage hf.continuous).connectedComponentIn

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyConnectedSpace
  signature: α] : DiscreteTopology ConnectedComponents α
  body: by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c => ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
    connectedComponents_preimage_singleton, isOpen_connectedComponent]

中文:
实例 [LocallyConnectedSpace
  签名: α] : DiscreteTopology ConnectedComponents α
  定义体: by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c => ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
    connectedComponents_preimage_singleton, isOpen_connectedComponent]

Depends on / 依赖: ConnectedComponents, ConnectedComponents.isQuotientMap_coe.isOpen_preimage, ConnectedComponents.surjective_coe, connectedComponents_preimage_singleton, discreteTopology_iff_isOpen_singleton, discreteTopology_iff_isOpen_singleton.mpr, isOpen_connectedComponent, isOpen_preimage, isQuotientMap_coe, surjective_coe
-/
instance [LocallyConnectedSpace α] : DiscreteTopology ConnectedComponents α := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c => ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
    connectedComponents_preimage_singleton, isOpen_connectedComponent]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyConnectedSpace
  signature: α] [CompactSpace α] : Finite ConnectedComponents α
  body: finite_of_compact_of_discrete

中文:
实例 [LocallyConnectedSpace
  签名: α] [CompactSpace α] : Finite ConnectedComponents α
  定义体: finite_of_compact_of_discrete

Depends on / 依赖: finite_of_compact_of_discrete
-/
instance [LocallyConnectedSpace α] [CompactSpace α] : Finite ConnectedComponents α :=
  finite_of_compact_of_discrete

/--
Instance `Prod.locallyConnectedSpace` / 实例 `Prod.locallyConnectedSpace`

English:
instance Prod.locallyConnectedSpace
  signature: [TopologicalSpace β] [LocallyConnectedSpace α]
  body: by
  rw [locallyConnectedSpace_iff_connected_subsets]
  rintro ⟨x, y⟩ U hU
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
  exact ⟨connectedComponentIn u x ×ˢ connectedComponentIn v y,
    prod_mem_nhds (connectedComponentIn_mem_nhds hu) (connectedComponentIn_mem_nhds hv),
    isPreconnecte

中文:
实例 Prod.locallyConnectedSpace
  签名: [TopologicalSpace β] [LocallyConnectedSpace α]
  定义体: by
  rw [locallyConnectedSpace_iff_connected_subsets]
  rintro ⟨x, y⟩ U hU
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
  exact ⟨connectedComponentIn u x ×ˢ connectedComponentIn v y,
    prod_mem_nhds (connectedComponentIn_mem_nhds hu) (connectedComponentIn_mem_nhds hv),
    isPreconnecte

Depends on / 依赖: connectedComponentIn, connectedComponentIn_mem_nhds, connectedComponentIn_subset, isPreconnected_connectedComponentIn, isPreconnected_connectedComponentIn.prod, locallyConnectedSpace_iff_connected_subsets, mem_nhds_prod_iff, mem_nhds_prod_iff.mp, prod_mem_nhds, prod_mono
-/
instance Prod.locallyConnectedSpace [TopologicalSpace β] [LocallyConnectedSpace α]
    [LocallyConnectedSpace β] : LocallyConnectedSpace (α × β) := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  rintro ⟨x, y⟩ U hU
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
  exact ⟨connectedComponentIn u x ×ˢ connectedComponentIn v y,
    prod_mem_nhds (connectedComponentIn_mem_nhds hu) (connectedComponentIn_mem_nhds hv),
    isPreconnected_connectedComponentIn.prod isPreconnected_connectedComponentIn,
    (prod_mono (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)).trans huv⟩

/--
theorem `Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace` / 定理 `Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace`

English:
theorem Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace
  statement: [forall i, TopologicalSpace (X i)]
  proof: by
  refine locallyConnectedSpace_iff_connected_subsets.2 fun x U hU => ?_
  rw [nhds_pi]; rw [Filter.mem_pi] at hU
  obtain ⟨J, hJ, t, ht, htU⟩ := hU
  let K := J union {i | ¬PreconnectedSpace (X i)}
  refine ⟨K.pi fun i => connectedComponentIn (t i) (x i),
    set_pi_mem_nhds (hJ.union hfinite) fu

中文:
定理 Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace
  结论: [对任意 i, TopologicalSpace (X i)]
  证明: by
  refine locallyConnectedSpace_iff_connected_subsets.2 fun x U hU => ?_
  rw [nhds_pi]; rw [Filter.mem_pi] at hU
  obtain ⟨J, hJ, t, ht, htU⟩ := hU
  let K := J union {i | ¬PreconnectedSpace (X i)}
  refine ⟨K.pi fun i => connectedComponentIn (t i) (x i),
    set_pi_mem_nhds (hJ.union hfinite) fu

Depends on / 依赖: Filter, Filter.mem_pi, K.pi, PreconnectedSpace, classical, connectedComponentIn, connectedComponentIn_mem_nhds, connectedComponentIn_subset, hJ.union, hfinite, isPreconnected_univ_pi, locallyConnectedSpace_iff_connected_subsets, mem_pi, mem_union_left, nhds_pi, set_pi_mem_nhds, univ_pi_piecewise_univ
-/
theorem Pi.locallyConnectedSpace_of_finite_not_preconnectedSpace [forall i, TopologicalSpace (X i)]
    [forall i, LocallyConnectedSpace (X i)] (hfinite : {i | ¬PreconnectedSpace (X i)}.Finite) :
    LocallyConnectedSpace (forall i, X i) := by
  refine locallyConnectedSpace_iff_connected_subsets.2 fun x U hU => ?_
  rw [nhds_pi]; rw [Filter.mem_pi] at hU
  obtain ⟨J, hJ, t, ht, htU⟩ := hU
  let K := J union {i | ¬PreconnectedSpace (X i)}
  refine ⟨K.pi fun i => connectedComponentIn (t i) (x i),
    set_pi_mem_nhds (hJ.union hfinite) fun i _ => connectedComponentIn_mem_nhds (ht i), ?_,
    fun f hf => htU fun i hiJ => connectedComponentIn_subset _ _ (hf i (mem_union_left _ hiJ))⟩
  classical
  rw [← univ_pi_piecewise_univ]
  refine isPreconnected_univ_pi fun i => ?_
  by_cases hi : i in K
  · rw [piecewise_eq_of_mem _ _ _ hi]
    exact isPreconnected_connectedComponentIn
  · rw [piecewise_eq_of_notMem _ _ _ hi]
    have : PreconnectedSpace (X i) := not_not.mp (not_or.1 hi).2
    exact isPreconnected_univ

/--
Instance `Pi.locallyConnectedSpace_of_finite` / 实例 `Pi.locallyConnectedSpace_of_finite`

English:
instance Pi.locallyConnectedSpace_of_finite
  signature: [Finite ι] [forall i, TopologicalSpace (X i)]
  body: locallyConnectedSpace_of_finite_not_preconnectedSpace (toFinite _)

中文:
实例 Pi.locallyConnectedSpace_of_finite
  签名: [Finite ι] [对任意 i, TopologicalSpace (X i)]
  定义体: locallyConnectedSpace_of_finite_not_preconnectedSpace (toFinite _)

Depends on / 依赖: locallyConnectedSpace_of_finite_not_preconnectedSpace, toFinite
-/
instance Pi.locallyConnectedSpace_of_finite [Finite ι] [forall i, TopologicalSpace (X i)]
    [forall i, LocallyConnectedSpace (X i)] : LocallyConnectedSpace (forall i, X i) :=
  locallyConnectedSpace_of_finite_not_preconnectedSpace (toFinite _)

/--
Instance `Pi.locallyConnectedSpace` / 实例 `Pi.locallyConnectedSpace`

English:
instance Pi.locallyConnectedSpace
  signature: [forall i, TopologicalSpace (X i)]
  body: locallyConnectedSpace_of_finite_not_preconnectedSpace
    (finite_empty.subset fun _ hi => hi inferInstance)

中文:
实例 Pi.locallyConnectedSpace
  签名: [对任意 i, TopologicalSpace (X i)]
  定义体: locallyConnectedSpace_of_finite_not_preconnectedSpace
    (finite_empty.subset fun _ hi => hi inferInstance)

Depends on / 依赖: finite_empty, finite_empty.subset, locallyConnectedSpace_of_finite_not_preconnectedSpace, subset
-/
instance Pi.locallyConnectedSpace [forall i, TopologicalSpace (X i)]
    [forall i, LocallyConnectedSpace (X i)] [forall i, PreconnectedSpace (X i)] :
    LocallyConnectedSpace (forall i, X i) :=
  locallyConnectedSpace_of_finite_not_preconnectedSpace
    (finite_empty.subset fun _ hi => hi inferInstance)

/--
theorem `Pi.locallyConnectedSpace_iff` / 定理 `Pi.locallyConnectedSpace_iff`

English:
theorem Pi.locallyConnectedSpace_iff
  given: [forall i, TopologicalSpace (X i)]
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases isEmpty_or_nonempty (forall i, X i) with he | hne
    · exact .inl he
    obtain ⟨x⟩ := hne
    classical
    have : forall i, Nonempty (X i) := Classical.nonempty_pi.mp ⟨x⟩
    refine .inr ⟨fun i => ((isOpenMap_eval i).isQuotientMap (continuous_apply i)
    

中文:
定理 Pi.locallyConnectedSpace_iff
  条件: [对任意 i, TopologicalSpace (X i)]
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases isEmpty_or_nonempty (forall i, X i) with he | hne
    · exact .inl he
    obtain ⟨x⟩ := hne
    classical
    have : forall i, Nonempty (X i) := Classical.nonempty_pi.mp ⟨x⟩
    refine .inr ⟨fun i => ((isOpenMap_eval i).isQuotientMap (continuous_apply i)
    

Depends on / 依赖: Classical, Classical.nonempty_pi.mp, Filter, Filter.mem_pi, Function, Function.surjective_eval, Nonempty, classical, connectedComponent, continuous_apply, isEmpty_or_nonempty, isOpenMap_eval, isOpen_connectedComponent, isOpen_connectedComponent.mem_nhds, isQuotientMap, locallyConnectedSpace, mem_connectedComponent, mem_nhds, mem_pi, nhds_pi
-/
theorem Pi.locallyConnectedSpace_iff [forall i, TopologicalSpace (X i)] :
    LocallyConnectedSpace (forall i, X i) ↔
      IsEmpty (forall i, X i) ∨
        (forall i, LocallyConnectedSpace (X i)) ∧ {i | ¬PreconnectedSpace (X i)}.Finite := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases isEmpty_or_nonempty (forall i, X i) with he | hne
    · exact .inl he
    obtain ⟨x⟩ := hne
    classical
    have : forall i, Nonempty (X i) := Classical.nonempty_pi.mp ⟨x⟩
    refine .inr ⟨fun i => ((isOpenMap_eval i).isQuotientMap (continuous_apply i)
      (Function.surjective_eval i)).locallyConnectedSpace, ?_⟩
    have hVn : connectedComponent x in 𝓝 x :=
      isOpen_connectedComponent.mem_nhds mem_connectedComponent
    rw [nhds_pi]; rw [Filter.mem_pi] at hVn
    obtain ⟨J, hJ, t, ht, htV⟩ := hVn
    refine hJ.subset fun i hi => by_contra fun hiJ => hi ?_
    suffices himg : Function.eval i '' connectedComponent x = univ from
      ⟨himg ▸ isPreconnected_connectedComponent.image _ (continuous_apply i).continuousOn⟩
    refine (subset_univ _).antisymm fun z _ => ⟨Function.update x i z, htV fun j hj => ?_, by simp⟩
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hiJ)]
    exact mem_of_mem_nhds (ht j)
  · rintro (he | ⟨hloc, hfin⟩)
    · exact ⟨he.elim⟩
    · exact locallyConnectedSpace_of_finite_not_preconnectedSpace hfin

end LocallyConnectedSpace
