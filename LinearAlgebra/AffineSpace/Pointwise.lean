/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-! # Pointwise instances on `AffineSubspace`s

This file provides the additive action `AffineSubspace.pointwiseAddAction` in the
`Pointwise` locale.

-/

@[expose] public section


open Affine Pointwise

open Set

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

namespace AffineSubspace
section Ring
variable [Ring k]
variable [AddCommGroup V] [Module k V] [AffineSpace V P]
variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseVAdd` / `pointwiseVAdd` 的定义

English:
definition pointwiseVAdd
  signature: : VAdd V (AffineSubspace k P) where
  body: s.map (AffineEquiv.constVAdd k P x)

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseVAdd

中文:
定义 pointwiseVAdd
  签名: : VAdd V (AffineSubspace k P) where
  定义体: s.map (AffineEquiv.constVAdd k P x)

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseVAdd
-/
protected def pointwiseVAdd : VAdd V (AffineSubspace k P) where
  vadd x s := s.map (AffineEquiv.constVAdd k P x)

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseVAdd

/--
lemma `coe_pointwise_vadd` / 引理 `coe_pointwise_vadd`

English:
lemma coe_pointwise_vadd
  given: (v : V) (s : AffineSubspace k P)
  proof: rfl

中文:
引理 coe_pointwise_vadd
  条件: (v : V) (s : AffineSubspace k P)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_pointwise_vadd (v : V) (s : AffineSubspace k P) :
    ((v +ᵥ s : AffineSubspace k P) : Set P) = v +ᵥ (s : Set P) := rfl

/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseAddAction` / `pointwiseAddAction` 的定义

English:
definition pointwiseAddAction
  signature: : AddAction V (AffineSubspace k P)
  body: SetLike.coe_injective.addAction _ coe_pointwise_vadd

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseAddAction

中文:
定义 pointwiseAddAction
  签名: : AddAction V (AffineSubspace k P)
  定义体: SetLike.coe_injective.addAction _ coe_pointwise_vadd

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseAddAction
-/
protected def pointwiseAddAction : AddAction V (AffineSubspace k P) :=
  SetLike.coe_injective.addAction _ coe_pointwise_vadd

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseAddAction

/--
theorem `pointwise_vadd_eq_map` / 定理 `pointwise_vadd_eq_map`

English:
theorem pointwise_vadd_eq_map
  given: (v : V) (s : AffineSubspace k P)
  proof: rfl

中文:
定理 pointwise_vadd_eq_map
  条件: (v : V) (s : AffineSubspace k P)
  证明: rfl
-/
theorem pointwise_vadd_eq_map (v : V) (s : AffineSubspace k P) :
    v +ᵥ s = s.map (AffineEquiv.constVAdd k P v) :=
  rfl

/--
theorem `vadd_mem_pointwise_vadd_iff` / 定理 `vadd_mem_pointwise_vadd_iff`

English:
theorem vadd_mem_pointwise_vadd_iff
  given: {v : V} {s : AffineSubspace k P} {p : P}
  proof: vadd_mem_vadd_set_iff

中文:
定理 vadd_mem_pointwise_vadd_iff
  条件: {v : V} {s : AffineSubspace k P} {p : P}
  证明: vadd_mem_vadd_set_iff

Depends on / 依赖: OrderDual, OrderDual.opensMeasurableSpace, TopologicalSpace, opensMeasurableSpace, vadd_mem_vadd_set_iff
-/
theorem vadd_mem_pointwise_vadd_iff {v : V} {s : AffineSubspace k P} {p : P} :
    v +ᵥ p in v +ᵥ s ↔ p in s :=
  vadd_mem_vadd_set_iff

/--
theorem `pointwise_vadd_bot` / 定理 `pointwise_vadd_bot`

English:
theorem pointwise_vadd_bot
  given: (v : V)
  statement: v +ᵥ (⊥ : AffineSubspace k P) = ⊥
  proof: by
  ext; simp [pointwise_vadd_eq_map, map_bot]

中文:
定理 pointwise_vadd_bot
  条件: (v : V)
  结论: v +ᵥ (⊥ : AffineSubspace k P) = ⊥
  证明: by
  ext; simp [pointwise_vadd_eq_map, map_bot]

Depends on / 依赖: OrderDual, OrderDual.borelSpace, TopologicalSpace, borelSpace
-/
@[simp] theorem pointwise_vadd_bot (v : V) : v +ᵥ (⊥ : AffineSubspace k P) = ⊥ := by
  ext; simp [pointwise_vadd_eq_map, map_bot]

/--
lemma `pointwise_vadd_top` / 引理 `pointwise_vadd_top`

English:
lemma pointwise_vadd_top
  given: (v : V)
  statement: v +ᵥ (⊤ : AffineSubspace k P) = ⊤
  proof: by
  ext; simp [pointwise_vadd_eq_map, vadd_eq_iff_eq_neg_vadd]

中文:
引理 pointwise_vadd_top
  条件: (v : V)
  结论: v +ᵥ (⊤ : AffineSubspace k P) = ⊤
  证明: by
  ext; simp [pointwise_vadd_eq_map, vadd_eq_iff_eq_neg_vadd]

Depends on / 依赖: BorelSpace, BorelSpace.opensMeasurable, TopologicalSpace, opensMeasurable
-/
@[simp] lemma pointwise_vadd_top (v : V) : v +ᵥ (⊤ : AffineSubspace k P) = ⊤ := by
  ext; simp [pointwise_vadd_eq_map, vadd_eq_iff_eq_neg_vadd]

/--
theorem `pointwise_vadd_direction` / 定理 `pointwise_vadd_direction`

English:
theorem pointwise_vadd_direction
  given: (v : V) (s : AffineSubspace k P)
  proof: by
  rw [pointwise_vadd_eq_map]; rw [map_direction]
  exact Submodule.map_id _

中文:
定理 pointwise_vadd_direction
  条件: (v : V) (s : AffineSubspace k P)
  证明: by
  rw [pointwise_vadd_eq_map]; rw [map_direction]
  exact Submodule.map_id _

Depends on / 依赖: Submodule, Submodule.map_id, map_direction, map_id, pointwise_vadd_eq_map
-/
theorem pointwise_vadd_direction (v : V) (s : AffineSubspace k P) :
    (v +ᵥ s).direction = s.direction := by
  rw [pointwise_vadd_eq_map]; rw [map_direction]
  exact Submodule.map_id _

/--
theorem `pointwise_vadd_span` / 定理 `pointwise_vadd_span`

English:
theorem pointwise_vadd_span
  given: (v : V) (s : Set P)
  statement: v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s)
  proof: map_span _ s

中文:
定理 pointwise_vadd_span
  条件: (v : V) (s : Set P)
  结论: v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s)
  证明: map_span _ s

Depends on / 依赖: map_span
-/
theorem pointwise_vadd_span (v : V) (s : Set P) : v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s) :=
  map_span _ s

/--
theorem `map_pointwise_vadd` / 定理 `map_pointwise_vadd`

English:
theorem map_pointwise_vadd
  given: (f : P₁ ->ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁)
  proof: by
  rw [pointwise_vadd_eq_map]; rw [pointwise_vadd_eq_map]; rw [map_map]; rw [map_map]
  congr 1
  ext
  exact f.map_vadd _ _

中文:
定理 map_pointwise_vadd
  条件: (f : P₁ ->ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁)
  证明: by
  rw [pointwise_vadd_eq_map]; rw [pointwise_vadd_eq_map]; rw [map_map]; rw [map_map]
  congr 1
  ext
  exact f.map_vadd _ _

Depends on / 依赖: f.map_vadd, map_map, map_vadd, pointwise_vadd_eq_map
-/
theorem map_pointwise_vadd (f : P₁ ->ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁) :
    (v +ᵥ s).map f = f.linear v +ᵥ s.map f := by
  rw [pointwise_vadd_eq_map]; rw [pointwise_vadd_eq_map]; rw [map_map]; rw [map_map]
  congr 1
  ext
  exact f.map_vadd _ _

section SMul
variable [DistribSMul M V] [SMulCommClass M k V] {a : M} {s : AffineSubspace k V}
  {p : V}

/-- The multiplicative action on an affine subspace corresponding to applying the action to every
element.

This is available as an instance in the `Pointwise` locale.

TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineSubspace k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
@[instance_reducible]
/--
Definition of `pointwiseSMul` / `pointwiseSMul` 的定义

English:
definition pointwiseSMul
  signature: : SMul M (AffineSubspace k V) where
  body: s.map (DistribSMul.toLinearMap k _ a).toAffineMap

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseSMul

@[simp, norm_cast]

中文:
定义 pointwiseSMul
  签名: : SMul M (AffineSubspace k V) where
  定义体: s.map (DistribSMul.toLinearMap k _ a).toAffineMap

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseSMul

@[simp, norm_cast]
-/
protected def pointwiseSMul : SMul M (AffineSubspace k V) where
  smul a s := s.map (DistribSMul.toLinearMap k _ a).toAffineMap

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseSMul

@[simp, norm_cast]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (a : M) (s : AffineSubspace k V)
  statement: ↑(a • s) = a • (s : Set V)
  proof: rfl

中文:
引理 coe_smul
  条件: (a : M) (s : AffineSubspace k V)
  结论: ↑(a • s) = a • (s : Set V)
  证明: rfl

Depends on / 依赖: BorelSpace, BorelSpace.countablyGenerated, TopologicalSpace, countablyGenerated
-/
lemma coe_smul (a : M) (s : AffineSubspace k V) : ↑(a • s) = a • (s : Set V) := rfl

/--
lemma `smul_eq_map` / 引理 `smul_eq_map`

English:
lemma smul_eq_map
  given: (a : M) (s : AffineSubspace k V)
  proof: rfl

中文:
引理 smul_eq_map
  条件: (a : M) (s : AffineSubspace k V)
  证明: rfl
-/
lemma smul_eq_map (a : M) (s : AffineSubspace k V) :
    a • s = s.map (DistribSMul.toLinearMap k _ a).toAffineMap := rfl

/--
lemma `smul_mem_smul_iff` / 引理 `smul_mem_smul_iff`

English:
lemma smul_mem_smul_iff
  given: {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V] {a : G}
  proof: smul_mem_smul_set_iff

中文:
引理 smul_mem_smul_iff
  条件: {G : 类型} [Group G] [DistribMulAction G V] [SMulCommClass G k V] {a : G}
  证明: smul_mem_smul_set_iff

Depends on / 依赖: smul_mem_smul_set_iff
-/
lemma smul_mem_smul_iff {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V] {a : G} :
    a • p in a • s ↔ p in s := smul_mem_smul_set_iff

/--
lemma `smul_bot` / 引理 `smul_bot`

English:
lemma smul_bot
  given: (a : M)
  statement: a • (⊥ : AffineSubspace k V) = ⊥
  proof: by
  ext; simp [smul_eq_map, map_bot]

中文:
引理 smul_bot
  条件: (a : M)
  结论: a • (⊥ : AffineSubspace k V) = ⊥
  证明: by
  ext; simp [smul_eq_map, map_bot]
-/
@[simp] lemma smul_bot (a : M) : a • (⊥ : AffineSubspace k V) = ⊥ := by
  ext; simp [smul_eq_map, map_bot]

/--
lemma `smul_span` / 引理 `smul_span`

English:
lemma smul_span
  given: (a : M) (s : Set V)
  statement: a • affineSpan k s = affineSpan k (a • s)
  proof: map_span _ s

中文:
引理 smul_span
  条件: (a : M) (s : Set V)
  结论: a • affineSpan k s = affineSpan k (a • s)
  证明: map_span _ s

Depends on / 依赖: HasCountableSeparatingOn, IsOpen, map_span
-/
lemma smul_span (a : M) (s : Set V) : a • affineSpan k s = affineSpan k (a • s) := map_span _ s

end SMul

section MulAction
variable [Monoid M] [DistribMulAction M V] [SMulCommClass M k V] {a : M} {s : AffineSubspace k V}
  {p : V}

/-- The multiplicative action on an affine subspace corresponding to applying the action to every
element.

This is available as an instance in the `Pointwise` locale.

TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineSubspace k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
@[instance_reducible]
/--
Definition of `mulAction` / `mulAction` 的定义

English:
definition mulAction
  signature: : MulAction M (AffineSubspace k V)
  body: SetLike.coe_injective.mulAction _ coe_smul

scoped[Pointwise] attribute [instance] AffineSubspace.mulAction

中文:
定义 mulAction
  签名: : MulAction M (AffineSubspace k V)
  定义体: SetLike.coe_injective.mulAction _ coe_smul

scoped[Pointwise] attribute [instance] AffineSubspace.mulAction
-/
protected def mulAction : MulAction M (AffineSubspace k V) :=
  SetLike.coe_injective.mulAction _ coe_smul

scoped[Pointwise] attribute [instance] AffineSubspace.mulAction

/--
lemma `smul_mem_smul_iff_of_isUnit` / 引理 `smul_mem_smul_iff_of_isUnit`

English:
lemma smul_mem_smul_iff_of_isUnit
  given: (ha : IsUnit a)
  statement: a • p in a • s ↔ p in s
  proof: smul_mem_smul_iff (a := ha.unit)

中文:
引理 smul_mem_smul_iff_of_isUnit
  条件: (ha : IsUnit a)
  结论: a • p in a • s ↔ p in s
  证明: smul_mem_smul_iff (a := ha.unit)

Depends on / 依赖: ha.unit, smul_mem_smul_iff
-/
lemma smul_mem_smul_iff_of_isUnit (ha : IsUnit a) : a • p in a • s ↔ p in s :=
  smul_mem_smul_iff (a := ha.unit)

/--
lemma `smul_mem_smul_iff₀` / 引理 `smul_mem_smul_iff₀`

English:
lemma smul_mem_smul_iff₀
  statement: {G₀ : Type*} [GroupWithZero G₀] [DistribMulAction G₀ V]
  proof: smul_mem_smul_iff_of_isUnit ha.isUnit

中文:
引理 smul_mem_smul_iff₀
  结论: {G₀ : 类型} [GroupWithZero G₀] [DistribMulAction G₀ V]
  证明: smul_mem_smul_iff_of_isUnit ha.isUnit

Depends on / 依赖: ha.isUnit, isUnit, smul_mem_smul_iff_of_isUnit
-/
lemma smul_mem_smul_iff₀ {G₀ : Type*} [GroupWithZero G₀] [DistribMulAction G₀ V]
    [SMulCommClass G₀ k V] {a : G₀} (ha : a != 0) : a • p in a • s ↔ p in s :=
  smul_mem_smul_iff_of_isUnit ha.isUnit

/--
lemma `smul_top` / 引理 `smul_top`

English:
lemma smul_top
  given: (ha : IsUnit a)
  statement: a • (⊤ : AffineSubspace k V) = ⊤
  proof: by
  ext x; simpa [smul_eq_map, map_top] using ⟨ha.unit⁻¹ • x, smul_inv_smul ha.unit _⟩

中文:
引理 smul_top
  条件: (ha : IsUnit a)
  结论: a • (⊤ : AffineSubspace k V) = ⊤
  证明: by
  ext x; simpa [smul_eq_map, map_top] using ⟨ha.unit⁻¹ • x, smul_inv_smul ha.unit _⟩
-/
@[simp] lemma smul_top (ha : IsUnit a) : a • (⊤ : AffineSubspace k V) = ⊤ := by
  ext x; simpa [smul_eq_map, map_top] using ⟨ha.unit⁻¹ • x, smul_inv_smul ha.unit _⟩

end MulAction

end Ring

section Field
variable [Field k] [AddCommGroup V] [Module k V] {a : k}

@[simp]
/--
lemma `direction_smul` / 引理 `direction_smul`

English:
lemma direction_smul
  given: (ha : a != 0) (s : AffineSubspace k V)
  statement: (a • s).direction = s.direction
  proof: by
  have : DistribSMul.toLinearMap k V a = a • LinearMap.id := by
    ext; simp
  simp [smul_eq_map, map_direction, this, Submodule.map_smul, ha]

中文:
引理 direction_smul
  条件: (ha : a != 0) (s : AffineSubspace k V)
  结论: (a • s).direction = s.direction
  证明: by
  have : DistribSMul.toLinearMap k V a = a • LinearMap.id := by
    ext; simp
  simp [smul_eq_map, map_direction, this, Submodule.map_smul, ha]

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap, LinearMap, LinearMap.id, Submodule, Submodule.map_smul, map_direction, map_smul, smul_eq_map, toLinearMap
-/
lemma direction_smul (ha : a != 0) (s : AffineSubspace k V) : (a • s).direction = s.direction := by
  have : DistribSMul.toLinearMap k V a = a • LinearMap.id := by
    ext; simp
  simp [smul_eq_map, map_direction, this, Submodule.map_smul, ha]

end Field
end AffineSubspace
