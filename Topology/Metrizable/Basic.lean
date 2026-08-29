/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.UniformSpace.Pi

/-!
# Metrizable Spaces

In this file we define metrizable topological spaces, i.e., topological spaces for which there
exists a metric space structure that generates the same topology.
We define it without any reference to metric spaces in order to avoid importing the real numbers.
For the proof that metrizable spaces admit a compatible metric,
see `Mathlib/Topology/Metrizable/Uniformity.lean`.
-/

-- don't import the real numbers
assert_not_exists AddMonoidWithOne

public section

open Filter Set Topology Uniformity UniformSpace SetRel

namespace TopologicalSpace

variable {ι X Y : Type*} {A : ι -> Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [forall i, TopologicalSpace (A i)]

/--
Definition of `PseudoMetrizableSpace` / `PseudoMetrizableSpace` 的定义

English:
class PseudoMetrizableSpace
  parameters: (X : Type*) [t : TopologicalSpace X]
  axioms and operations (1):
    - exists_countably_generated : exists u : UniformSpace X, u.toTopologicalSpace = t ∧ (uniformity X).IsCountablyGenerated

中文:
类 PseudoMetrizableSpace
  参数: (X : 类型) [t : TopologicalSpace X]
  公理与运算 (1 个):
    - exists_countably_generated : 存在 u : UniformSpace X, u.toTopologicalSpace = t ∧ (uniformity X).IsCountablyGenerated
-/
class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_countably_generated :
    exists u : UniformSpace X, u.toTopologicalSpace = t ∧ (uniformity X).IsCountablyGenerated

/-- A uniform space with countably generated `𝓤 X` is pseudometrizable. -/
instance (priority := 100) _root_.UniformSpace.pseudoMetrizableSpace {X : Type*}
    [u : UniformSpace X] [hu : IsCountablyGenerated (uniformity X)] : PseudoMetrizableSpace X :=
  ⟨⟨u, rfl, hu⟩⟩

-- see note [reducible non-instances]
/--
Definition of `pseudoMetrizableSpaceUniformity` / `pseudoMetrizableSpaceUniformity` 的定义

English:
abbreviation pseudoMetrizableSpaceUniformity
  signature: (X : Type*) [TopologicalSpace X]
  body: h.exists_countably_generated.choose.replaceTopology
    h.exists_countably_generated.choose_spec.1.symm

example {X : Type*} [t : TopologicalSpace X] [PseudoMetrizableSpace X] :
    (pseudoMetrizableSpaceUniformity X).toTopologicalSpace = t := by
  with_reducible_and_instances rfl

中文:
缩写 pseudoMetrizableSpaceUniformity
  签名: (X : 类型) [TopologicalSpace X]
  定义体: h.exists_countably_generated.choose.replaceTopology
    h.exists_countably_generated.choose_spec.1.symm

example {X : Type*} [t : TopologicalSpace X] [PseudoMetrizableSpace X] :
    (pseudoMetrizableSpaceUniformity X).toTopologicalSpace = t := by
  with_reducible_and_instances rfl

Depends on / 依赖: choose_spec, exists_countably_generated, h.exists_countably_generated.choose.replaceTopology, h.exists_countably_generated.choose_spec, replaceTopology
-/
noncomputable abbrev pseudoMetrizableSpaceUniformity (X : Type*) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : UniformSpace X :=
  h.exists_countably_generated.choose.replaceTopology
    h.exists_countably_generated.choose_spec.1.symm

example {X : Type*} [t : TopologicalSpace X] [PseudoMetrizableSpace X] :
    (pseudoMetrizableSpaceUniformity X).toTopologicalSpace = t := by
  with_reducible_and_instances rfl

/--
theorem `pseudoMetrizableSpaceUniformity_countably_generated` / 定理 `pseudoMetrizableSpaceUniformity_countably_generated`

English:
theorem pseudoMetrizableSpaceUniformity_countably_generated
  proof: h.exists_countably_generated.choose_spec.2

中文:
定理 pseudoMetrizableSpaceUniformity_countably_generated
  证明: h.exists_countably_generated.choose_spec.2

Depends on / 依赖: choose_spec, exists_countably_generated, h.exists_countably_generated.choose_spec
-/
theorem pseudoMetrizableSpaceUniformity_countably_generated
    (X : Type*) [TopologicalSpace X] [h : PseudoMetrizableSpace X] :
    𝓤[pseudoMetrizableSpaceUniformity X].IsCountablyGenerated :=
  h.exists_countably_generated.choose_spec.2

/--
Instance `pseudoMetrizableSpace_prod` / 实例 `pseudoMetrizableSpace_prod`

English:
instance pseudoMetrizableSpace_prod
  signature: [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
  body: let : UniformSpace X := pseudoMetrizableSpaceUniformity X
  have : (uniformity X).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated X
  let : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUni

中文:
实例 pseudoMetrizableSpace_prod
  签名: [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
  定义体: let : UniformSpace X := pseudoMetrizableSpaceUniformity X
  have : (uniformity X).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated X
  let : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUni

Depends on / 依赖: IsCountablyGenerated, UniformSpace, pseudoMetrizableSpaceUniformity, pseudoMetrizableSpaceUniformity_countably_generated, uniformity
-/
instance pseudoMetrizableSpace_prod [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y] :
    PseudoMetrizableSpace (X × Y) :=
  let : UniformSpace X := pseudoMetrizableSpaceUniformity X
  have : (uniformity X).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated X
  let : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated Y
  inferInstance

/--
theorem `_root_.Topology.IsInducing.pseudoMetrizableSpace` / 定理 `_root_.Topology.IsInducing.pseudoMetrizableSpace`

English:
theorem _root_.Topology.IsInducing.pseudoMetrizableSpace
  statement: [PseudoMetrizableSpace Y] {f : X -> Y}
  proof: let u : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated Y
  ⟨⟨u.comap f, u.toTopologicalSpace_comap.trans hf.eq_induced.symm,
    Filter.comap.isCountablyGenerated (uniformity Y) (Prod.map f f

中文:
定理 _root_.Topology.IsInducing.pseudoMetrizableSpace
  结论: [PseudoMetrizableSpace Y] {f : X -> Y}
  证明: let u : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated Y
  ⟨⟨u.comap f, u.toTopologicalSpace_comap.trans hf.eq_induced.symm,
    Filter.comap.isCountablyGenerated (uniformity Y) (Prod.map f f

Depends on / 依赖: Filter, Filter.comap.isCountablyGenerated, IsCountablyGenerated, Prod.map, UniformSpace, eq_induced, hf.eq_induced.symm, isCountablyGenerated, pseudoMetrizableSpaceUniformity, pseudoMetrizableSpaceUniformity_countably_generated, toTopologicalSpace_comap, u.comap, u.toTopologicalSpace_comap.trans, uniformity
-/
theorem _root_.Topology.IsInducing.pseudoMetrizableSpace [PseudoMetrizableSpace Y] {f : X -> Y}
    (hf : IsInducing f) : PseudoMetrizableSpace X :=
  let u : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated Y
  ⟨⟨u.comap f, u.toTopologicalSpace_comap.trans hf.eq_induced.symm,
    Filter.comap.isCountablyGenerated (uniformity Y) (Prod.map f f)⟩⟩

/-- Every pseudo-metrizable space is first countable. -/
instance (priority := 100) PseudoMetrizableSpace.firstCountableTopology
    [h : PseudoMetrizableSpace X] : FirstCountableTopology X :=
  let : UniformSpace X := pseudoMetrizableSpaceUniformity X
  have : (uniformity X).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated X
  inferInstance

/--
Instance `PseudoMetrizableSpace.subtype` / 实例 `PseudoMetrizableSpace.subtype`

English:
instance PseudoMetrizableSpace.subtype
  signature: [PseudoMetrizableSpace X] (s : Set X)
  body: IsInducing.subtypeVal.pseudoMetrizableSpace

中文:
实例 PseudoMetrizableSpace.subtype
  签名: [PseudoMetrizableSpace X] (s : Set X)
  定义体: IsInducing.subtypeVal.pseudoMetrizableSpace

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.pseudoMetrizableSpace, pseudoMetrizableSpace, subtypeVal
-/
instance PseudoMetrizableSpace.subtype [PseudoMetrizableSpace X] (s : Set X) :
    PseudoMetrizableSpace s :=
  IsInducing.subtypeVal.pseudoMetrizableSpace

/--
Instance `pseudoMetrizableSpace_pi` / 实例 `pseudoMetrizableSpace_pi`

English:
instance pseudoMetrizableSpace_pi
  signature: [forall i, PseudoMetrizableSpace (A i)]
  body: let := fun i => pseudoMetrizableSpaceUniformity (A i)
  have := fun i => pseudoMetrizableSpaceUniformity_countably_generated (A i)
  inferInstance

中文:
实例 pseudoMetrizableSpace_pi
  签名: [对任意 i, PseudoMetrizableSpace (A i)]
  定义体: let := fun i => pseudoMetrizableSpaceUniformity (A i)
  have := fun i => pseudoMetrizableSpaceUniformity_countably_generated (A i)
  inferInstance

Depends on / 依赖: pseudoMetrizableSpaceUniformity, pseudoMetrizableSpaceUniformity_countably_generated
-/
instance pseudoMetrizableSpace_pi [forall i, PseudoMetrizableSpace (A i)] :
    PseudoMetrizableSpace (forall i, A i) :=
  let := fun i => pseudoMetrizableSpaceUniformity (A i)
  have := fun i => pseudoMetrizableSpaceUniformity_countably_generated (A i)
  inferInstance

/--
Instance `PseudoMetrizableSpace.regularSpace` / 实例 `PseudoMetrizableSpace.regularSpace`

English:
instance PseudoMetrizableSpace.regularSpace
  signature: [PseudoMetrizableSpace X]
  body: let := pseudoMetrizableSpaceUniformity X
  inferInstance

中文:
实例 PseudoMetrizableSpace.regularSpace
  签名: [PseudoMetrizableSpace X]
  定义体: let := pseudoMetrizableSpaceUniformity X
  inferInstance

Depends on / 依赖: pseudoMetrizableSpaceUniformity
-/
instance PseudoMetrizableSpace.regularSpace [PseudoMetrizableSpace X] : RegularSpace X :=
  let := pseudoMetrizableSpaceUniformity X
  inferInstance

instance (priority := 100) IndiscreteTopology.pseudoMetrizableSpace [IndiscreteTopology X] :
    PseudoMetrizableSpace X where
  exists_countably_generated :=
    ⟨⊤, (IndiscreteTopology.eq_top X).symm, isCountablyGenerated_top⟩

/--
Definition of `MetrizableSpace` / `MetrizableSpace` 的定义

English:
class MetrizableSpace
  parameters: (X : Type*) [t : TopologicalSpace X]
  (no additional axioms)

中文:
类 MetrizableSpace
  参数: (X : 类型) [t : TopologicalSpace X]
  (无附加公理)
-/
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop extends
    PseudoMetrizableSpace X, T0Space X

-- See note [lower instance priority]
attribute [instance 100] MetrizableSpace.toT0Space
attribute [instance 100] MetrizableSpace.toPseudoMetrizableSpace

instance (priority := 100) PseudoMetrizableSpace.toMetrizableSpace
    [T0Space X] [h : PseudoMetrizableSpace X] : MetrizableSpace X where

instance (priority := 100) t2Space_of_metrizableSpace [MetrizableSpace X] : T2Space X :=
  letI : UniformSpace X := pseudoMetrizableSpaceUniformity X
  inferInstance

/--
Instance `metrizableSpace_prod` / 实例 `metrizableSpace_prod`

English:
instance metrizableSpace_prod
  signature: [MetrizableSpace X] [MetrizableSpace Y]

中文:
实例 metrizableSpace_prod
  签名: [MetrizableSpace X] [MetrizableSpace Y]
-/
instance metrizableSpace_prod [MetrizableSpace X] [MetrizableSpace Y] :
    MetrizableSpace (X × Y) where

/--
theorem `_root_.Topology.IsEmbedding.metrizableSpace` / 定理 `_root_.Topology.IsEmbedding.metrizableSpace`

English:
theorem _root_.Topology.IsEmbedding.metrizableSpace
  statement: [MetrizableSpace Y] {f : X -> Y}
  proof: hf.toIsInducing.pseudoMetrizableSpace
  toT0Space := hf.t0Space

中文:
定理 _root_.Topology.IsEmbedding.metrizableSpace
  结论: [MetrizableSpace Y] {f : X -> Y}
  证明: hf.toIsInducing.pseudoMetrizableSpace
  toT0Space := hf.t0Space

Depends on / 依赖: hf.toIsInducing.pseudoMetrizableSpace, pseudoMetrizableSpace, toIsInducing
-/
theorem _root_.Topology.IsEmbedding.metrizableSpace [MetrizableSpace Y] {f : X -> Y}
    (hf : IsEmbedding f) : MetrizableSpace X where
  toPseudoMetrizableSpace := hf.toIsInducing.pseudoMetrizableSpace
  toT0Space := hf.t0Space

/--
Instance `MetrizableSpace.subtype` / 实例 `MetrizableSpace.subtype`

English:
instance MetrizableSpace.subtype
  signature: [MetrizableSpace X] (s : Set X)
  body: IsEmbedding.subtypeVal.metrizableSpace

中文:
实例 MetrizableSpace.subtype
  签名: [MetrizableSpace X] (s : Set X)
  定义体: IsEmbedding.subtypeVal.metrizableSpace

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.metrizableSpace, metrizableSpace, subtypeVal
-/
instance MetrizableSpace.subtype [MetrizableSpace X] (s : Set X) : MetrizableSpace s :=
  IsEmbedding.subtypeVal.metrizableSpace

/--
Instance `metrizableSpace_pi` / 实例 `metrizableSpace_pi`

English:
instance metrizableSpace_pi
  signature: [forall i, MetrizableSpace (A i)]

中文:
实例 metrizableSpace_pi
  签名: [对任意 i, MetrizableSpace (A i)]
-/
instance metrizableSpace_pi [forall i, MetrizableSpace (A i)] : MetrizableSpace (forall i, A i) where

/--
theorem `IsSeparable.secondCountableTopology` / 定理 `IsSeparable.secondCountableTopology`

English:
theorem IsSeparable.secondCountableTopology
  statement: [PseudoMetrizableSpace X] {s : Set X}
  proof: let ⟨u, hu, hs⟩ := hs
  have := hu.to_subtype
  have : SeparableSpace (closure u) :=
    ⟨Set.range (u.inclusion subset_closure), Set.countable_range (u.inclusion subset_closure),
Subtype.dense_iff.2 by rw [← Set.range_comp, Set.val_comp_inclusion, Subtype.range_coe]⟩
  let := pseudoMetrizableSpaceU

中文:
定理 IsSeparable.secondCountableTopology
  结论: [PseudoMetrizableSpace X] {s : Set X}
  证明: let ⟨u, hu, hs⟩ := hs
  have := hu.to_subtype
  have : SeparableSpace (closure u) :=
    ⟨Set.range (u.inclusion subset_closure), Set.countable_range (u.inclusion subset_closure),
Subtype.dense_iff.2 by rw [← Set.range_comp, Set.val_comp_inclusion, Subtype.range_coe]⟩
  let := pseudoMetrizableSpaceU

Depends on / 依赖: IsEmbedding, SeparableSpace, Set.countable_range, Set.range, Set.range_comp, Set.val_comp_inclusion, Subtype, Subtype.dense_iff, Subtype.range_coe, Topology, Topology.IsEmbedding.inclusion, closure, countable_range, dense_iff, hu.to_subtype, inclusion, pseudoMetrizableSpaceUniformity, pseudoMetrizableSpaceUniformity_countably_generated, range_coe, range_comp
-/
theorem IsSeparable.secondCountableTopology [PseudoMetrizableSpace X] {s : Set X}
    (hs : IsSeparable s) : SecondCountableTopology s :=
  let ⟨u, hu, hs⟩ := hs
  have := hu.to_subtype
  have : SeparableSpace (closure u) :=
    ⟨Set.range (u.inclusion subset_closure), Set.countable_range (u.inclusion subset_closure),
Subtype.dense_iff.2 by rw [← Set.range_comp, Set.val_comp_inclusion, Subtype.range_coe]⟩
  let := pseudoMetrizableSpaceUniformity (closure u)
  have := pseudoMetrizableSpaceUniformity_countably_generated (closure u)
  have := secondCountable_of_separable (closure u)
  (Topology.IsEmbedding.inclusion hs).secondCountableTopology

instance (X : Type*) [TopologicalSpace X] [LindelofSpace X] [PseudoMetrizableSpace X] :
    SecondCountableTopology X := by
  let := pseudoMetrizableSpaceUniformity X
  have := pseudoMetrizableSpaceUniformity_countably_generated X
  suffices _ : SeparableSpace X from secondCountable_of_separable X
  obtain ⟨V, hVb, hVs⟩ := has_seq_basis X
  choose U hUc hUu using fun n =>
    LindelofSpace.elim_nhds_subcover (fun x => ball x (V n))
      (fun x => ball_mem_nhds x (hVb.mem n))
  refine ⟨Set.iUnion U, Set.countable_iUnion hUc, fun x => ?_⟩
  rw [mem_closure_iff_frequently]; rw [nhds_eq_comap_uniformity]; rw [frequently_comap]; rw [hVb.frequently_iff]
  intro n _
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (Set.eq_univ_iff_forall.1 (hUu n) x)
  rw [ball_eq_of_symmetry] at hx
  exact ⟨(x, i), hx, i, rfl, Set.mem_iUnion_of_mem n hi⟩

/--
theorem `IsSeparable.exists_countable_dense_subset` / 定理 `IsSeparable.exists_countable_dense_subset`

English:
theorem IsSeparable.exists_countable_dense_subset
  statement: [PseudoMetrizableSpace X]
  proof: by
  let := pseudoMetrizableSpaceUniformity X
  have := pseudoMetrizableSpaceUniformity_countably_generated X
  apply subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨t, htc, hst⟩ := hs
  refine ⟨t, htc, fun x hx => ?_⟩
  obtain ⟨y, hyx, hyt⟩ := mem_closure_iff_ball.1 (hst hx) (sy

中文:
定理 IsSeparable.exists_countable_dense_subset
  结论: [PseudoMetrizableSpace X]
  证明: by
  let := pseudoMetrizableSpaceUniformity X
  have := pseudoMetrizableSpaceUniformity_countably_generated X
  apply subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨t, htc, hst⟩ := hs
  refine ⟨t, htc, fun x hx => ?_⟩
  obtain ⟨y, hyx, hyt⟩ := mem_closure_iff_ball.1 (hst hx) (sy

Depends on / 依赖: SetRel, SetRel.symmetrize_subset_inv, ball_mono, mem_biUnion, mem_closure_iff_ball, pseudoMetrizableSpaceUniformity, pseudoMetrizableSpaceUniformity_countably_generated, subset_countable_closure_of_almost_dense_set, symmetrize_mem_uniformity, symmetrize_subset_inv
-/
theorem IsSeparable.exists_countable_dense_subset [PseudoMetrizableSpace X]
    {s : Set X} (hs : IsSeparable s) : exists t, t subseteq s ∧ t.Countable ∧ s subseteq closure t := by
  let := pseudoMetrizableSpaceUniformity X
  have := pseudoMetrizableSpaceUniformity_countably_generated X
  apply subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨t, htc, hst⟩ := hs
  refine ⟨t, htc, fun x hx => ?_⟩
  obtain ⟨y, hyx, hyt⟩ := mem_closure_iff_ball.1 (hst hx) (symmetrize_mem_uniformity hU)
  exact mem_biUnion hyt (ball_mono SetRel.symmetrize_subset_inv x hyx)

/--
theorem `IsSeparable.separableSpace` / 定理 `IsSeparable.separableSpace`

English:
theorem IsSeparable.separableSpace
  given: [PseudoMetrizableSpace X] {s : Set X} (hs : IsSeparable s)
  proof: by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, hst⟩
  lift t to Set s using hts
  refine ⟨⟨t, countable_of_injective_of_countable_image Subtype.coe_injective.injOn htc, ?_⟩⟩
  rwa [IsInducing.subtypeVal.dense_iff, Subtype.forall]

中文:
定理 IsSeparable.separableSpace
  条件: [PseudoMetrizableSpace X] {s : Set X} (hs : IsSeparable s)
  证明: by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, hst⟩
  lift t to Set s using hts
  refine ⟨⟨t, countable_of_injective_of_countable_image Subtype.coe_injective.injOn htc, ?_⟩⟩
  rwa [IsInducing.subtypeVal.dense_iff, Subtype.forall]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.dense_iff, Subtype, Subtype.coe_injective.injOn, Subtype.forall, coe_injective, countable_of_injective_of_countable_image, dense_iff, exists_countable_dense_subset, hs.exists_countable_dense_subset, subtypeVal
-/
theorem IsSeparable.separableSpace [PseudoMetrizableSpace X] {s : Set X} (hs : IsSeparable s) :
    SeparableSpace s := by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, hst⟩
  lift t to Set s using hts
  refine ⟨⟨t, countable_of_injective_of_countable_image Subtype.coe_injective.injOn htc, ?_⟩⟩
  rwa [IsInducing.subtypeVal.dense_iff, Subtype.forall]

instance (priority := 100) DiscreteTopology.metrizableSpace [DiscreteTopology X] :
    MetrizableSpace X where
  exists_countably_generated :=
    ⟨⊥, DiscreteTopology.eq_bot.symm, Filter.isCountablyGenerated_principal SetRel.id⟩

end TopologicalSpace
