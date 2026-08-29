/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Alessandro D'Angelo
-/
module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sober

/-!
# The Krull dimension of a topological space

The Krull dimension of a topological space is the order-theoretic Krull dimension applied to the
collection of all its subsets that are closed and irreducible. Unfolding this definition, it is
the length of longest series of closed irreducible subsets ordered by inclusion.

## Main results

- `topologicalKrullDim_subspace_le`: For any subspace Y ⊆ X, we have dim(Y) ≤ dim(X)

## Implementation notes

The proofs use order-preserving maps between posets of irreducible closed sets to establish
dimension inequalities.
-/

@[expose] public section

open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

/--
Definition of `topologicalKrullDim` / `topologicalKrullDim` 的定义

English:
definition topologicalKrullDim
  signature: (T : Type*) [TopologicalSpace T]
  body: krullDim (IrreducibleCloseds T)

中文:
定义 topologicalKrullDim
  签名: (T : 类型) [拓扑空间 T]
  定义体: krullDim (IrreducibleCloseds T)

Depends on / 依赖: IrreducibleCloseds, krullDim
-/
noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot Nat∞ :=
  krullDim (IrreducibleCloseds T)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-!
### Main dimension theorems -/

/--
theorem `Topology.IsInducing.topologicalKrullDim_le` / 定理 `Topology.IsInducing.topologicalKrullDim_le`

English:
theorem Topology.IsInducing.topologicalKrullDim_le
  given: {f : Y -> X} (hf : IsInducing f)
  proof: krullDim_le_of_strictMono _ (map_strictMono_of_isInducing hf)

中文:
定理 拓扑.是Inducing.topologicalKrullDim_le
  条件: {f : Y -> X} (hf : 是Inducing f)
  证明: krullDim_le_of_strictMono _ (map_strictMono_of_isInducing hf)

Depends on / 依赖: krullDim_le_of_strictMono, map_strictMono_of_isInducing
-/
theorem Topology.IsInducing.topologicalKrullDim_le {f : Y -> X} (hf : IsInducing f) :
    topologicalKrullDim Y <= topologicalKrullDim X :=
  krullDim_le_of_strictMono _ (map_strictMono_of_isInducing hf)

/--
theorem `IsHomeomorph.topologicalKrullDim_eq` / 定理 `IsHomeomorph.topologicalKrullDim_eq`

English:
theorem IsHomeomorph.topologicalKrullDim_eq
  given: (f : X -> Y) (h : IsHomeomorph f)
  proof: have fwd : topologicalKrullDim X <= topologicalKrullDim Y :=
    h.isInducing.topologicalKrullDim_le
  have bwd : topologicalKrullDim Y <= topologicalKrullDim X :=
    (h.homeomorph f).symm.isInducing.topologicalKrullDim_le
  le_antisymm fwd bwd

中文:
定理 是同胚.topologicalKrullDim_eq
  条件: (f : X -> Y) (h : 是同胚 f)
  证明: have fwd : topologicalKrullDim X <= topologicalKrullDim Y :=
    h.isInducing.topologicalKrullDim_le
  have bwd : topologicalKrullDim Y <= topologicalKrullDim X :=
    (h.homeomorph f).symm.isInducing.topologicalKrullDim_le
  le_antisymm fwd bwd

Depends on / 依赖: h.homeomorph, h.isInducing.topologicalKrullDim_le, homeomorph, isInducing, le_antisymm, symm.isInducing.topologicalKrullDim_le, topologicalKrullDim, topologicalKrullDim_le
-/
theorem IsHomeomorph.topologicalKrullDim_eq (f : X -> Y) (h : IsHomeomorph f) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  have fwd : topologicalKrullDim X <= topologicalKrullDim Y :=
    h.isInducing.topologicalKrullDim_le
  have bwd : topologicalKrullDim Y <= topologicalKrullDim X :=
    (h.homeomorph f).symm.isInducing.topologicalKrullDim_le
  le_antisymm fwd bwd

/--
theorem `topologicalKrullDim_subspace_le` / 定理 `topologicalKrullDim_subspace_le`

English:
theorem topologicalKrullDim_subspace_le
  given: (X : Type*) [TopologicalSpace X] (Y : Set X)
  proof: IsInducing.subtypeVal.topologicalKrullDim_le

中文:
定理 topologicalKrullDim_subspace_le
  条件: (X : 类型) [拓扑空间 X] (Y : 集合 X)
  证明: IsInducing.subtypeVal.topologicalKrullDim_le

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.topologicalKrullDim_le, subtypeVal, topologicalKrullDim_le
-/
theorem topologicalKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    topologicalKrullDim Y <= topologicalKrullDim X :=
  IsInducing.subtypeVal.topologicalKrullDim_le

/--
theorem `topologicalKrullDim_zero_of_discreteTopology` / 定理 `topologicalKrullDim_zero_of_discreteTopology`

English:
theorem topologicalKrullDim_zero_of_discreteTopology
  proof: by
  refine krullDim_nonpos_iff_forall_isMax.mpr fun Z Y h => (h.antisymm' fun x hx => ?_).le
  obtain ⟨z, hz⟩ := Z.2.nonempty
  rwa [DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible Y.2.isPreirreducible hx (h hz)]

中文:
定理 topologicalKrullDim_zero_of_discreteTopology
  证明: by
  refine krullDim_nonpos_iff_forall_isMax.mpr fun Z Y h => (h.antisymm' fun x hx => ?_).le
  obtain ⟨z, hz⟩ := Z.2.nonempty
  rwa [DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible Y.2.isPreirreducible hx (h hz)]

Depends on / 依赖: DiscreteTopology, DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible, antisymm, h.antisymm, isDiscrete, isPreirreducible, krullDim_nonpos_iff_forall_isMax, krullDim_nonpos_iff_forall_isMax.mpr, nonempty, subsingleton_of_isPreirreducible
-/
theorem topologicalKrullDim_zero_of_discreteTopology
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    topologicalKrullDim X <= 0 := by
  refine krullDim_nonpos_iff_forall_isMax.mpr fun Z Y h => (h.antisymm' fun x hx => ?_).le
  obtain ⟨z, hz⟩ := Z.2.nonempty
  rwa [DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible Y.2.isPreirreducible hx (h hz)]

/--
lemma `Topology.IsOpenEmbedding.coheight_map` / 引理 `Topology.IsOpenEmbedding.coheight_map`

English:
lemma Topology.IsOpenEmbedding.coheight_map
  statement: {f : X -> Y} (hf : IsOpenEmbedding f)
  proof: by
  rw [← coheight_orderIso (orderIsoOfIsOpenEmbedding f hf) Z]
  refine .symm (coheight_eq_of_strictMono Subtype.val (Subtype.strictMono_coe _) ?_ _)
  intro a b hlt
  exact ⟨⟨b, a.2.mono (Set.preimage_mono hlt.le)⟩, hlt, rfl⟩

中文:
引理 拓扑.是开嵌入.coheight_map
  结论: {f : X -> Y} (hf : 是开嵌入 f)
  证明: by
  rw [← coheight_orderIso (orderIsoOfIsOpenEmbedding f hf) Z]
  refine .symm (coheight_eq_of_strictMono Subtype.val (Subtype.strictMono_coe _) ?_ _)
  intro a b hlt
  exact ⟨⟨b, a.2.mono (Set.preimage_mono hlt.le)⟩, hlt, rfl⟩

Depends on / 依赖: Set.preimage_mono, Subtype, Subtype.strictMono_coe, Subtype.val, coheight_eq_of_strictMono, coheight_orderIso, hlt.le, orderIsoOfIsOpenEmbedding, preimage_mono, strictMono_coe
-/
lemma Topology.IsOpenEmbedding.coheight_map {f : X -> Y} (hf : IsOpenEmbedding f)
    (Z : TopologicalSpace.IrreducibleCloseds X) :
    Order.coheight (map f hf.continuous Z) = Order.coheight Z := by
  rw [← coheight_orderIso (orderIsoOfIsOpenEmbedding f hf) Z]
  refine .symm (coheight_eq_of_strictMono Subtype.val (Subtype.strictMono_coe _) ?_ _)
  intro a b hlt
  exact ⟨⟨b, a.2.mono (Set.preimage_mono hlt.le)⟩, hlt, rfl⟩

attribute [local instance] specializationOrder in
/--
lemma `Topology.IsOpenEmbedding.coheight_eq` / 引理 `Topology.IsOpenEmbedding.coheight_eq`

English:
lemma Topology.IsOpenEmbedding.coheight_eq
  statement: [QuasiSober Y] [T0Space Y] [QuasiSober X] [T0Space X]
  proof: by
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := Y)).symm (f x)]; rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x]; rw [← Topology.IsOpenEmbedding.coheight_map hf]
  congr
  ext : 1
  simp [closure_image_closure hf.continuous]

中文:
引理 拓扑.是开嵌入.coheight_eq
  结论: [拟醇 Y] [T0空间 Y] [拟醇 X] [T0空间 X]
  证明: by
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := Y)).symm (f x)]; rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x]; rw [← Topology.IsOpenEmbedding.coheight_map hf]
  congr
  ext : 1
  simp [closure_image_closure hf.continuous]

Depends on / 依赖: IsOpenEmbedding, Topology, Topology.IsOpenEmbedding.coheight_map, closure_image_closure, coheight_map, coheight_orderIso, continuous, hf.continuous, irreducibleSetEquivPoints
-/
lemma Topology.IsOpenEmbedding.coheight_eq [QuasiSober Y] [T0Space Y] [QuasiSober X] [T0Space X]
    {x : X} (f : X -> Y) (hf : IsOpenEmbedding f) : coheight (f x) = coheight x := by
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := Y)).symm (f x)]; rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x]; rw [← Topology.IsOpenEmbedding.coheight_map hf]
  congr
  ext : 1
  simp [closure_image_closure hf.continuous]
