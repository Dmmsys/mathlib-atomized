/-
Copyright (c) 2022 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Affine map restrictions

This file defines restrictions of affine maps.

## Main definitions

* The domain and codomain of an affine map can be restricted using
  `AffineMap.restrict`.

## Main theorems

* The associated linear map of the restriction is the restriction of the
  linear map associated to the original affine map.
* The restriction is injective if the original map is injective.
* The restriction in surjective if the codomain is the image of the domain.
-/

@[expose] public section


variable {k V₁ P₁ V₂ P₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂] [Module k V₁]
  [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

/--
Instance `AffineSubspace.nonempty_map` / 实例 `AffineSubspace.nonempty_map`

English:
instance AffineSubspace.nonempty_map
  signature: {E : AffineSubspace k P₁} [Ene : Nonempty E]
  body: by
  obtain ⟨x, hx⟩ := id Ene
  exact ⟨⟨φ x, AffineSubspace.mem_map.mpr ⟨x, hx, rfl⟩⟩⟩

中文:
实例 仿射子空间.nonempty_map
  签名: {E : 仿射子空间 k P₁} [Ene : 非空 E]
  定义体: by
  obtain ⟨x, hx⟩ := id Ene
  exact ⟨⟨φ x, AffineSubspace.mem_map.mpr ⟨x, hx, rfl⟩⟩⟩

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_map.mpr, mem_map
-/
instance AffineSubspace.nonempty_map {E : AffineSubspace k P₁} [Ene : Nonempty E]
    {φ : P₁ ->ᵃ[k] P₂} : Nonempty (E.map φ) := by
  obtain ⟨x, hx⟩ := id Ene
  exact ⟨⟨φ x, AffineSubspace.mem_map.mpr ⟨x, hx, rfl⟩⟩⟩

/--
Definition of `AffineMap.restrict` / `AffineMap.restrict` 的定义

English:
definition AffineMap.restrict
  signature: (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁} {F : AffineSubspace k P₂}
  body: by
  refine ⟨?_, ?_, ?_⟩
· exact fun x => ⟨φ x, hEF AffineSubspace.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  · refine φ.linear.restrict (?_ : E.direction <= F.direction.comap φ.linear)
    rw [← Submodule.map_le_iff_le_comap]; rw [← AffineSubspace.map_direction]
    exact AffineSubspace.direction_le hEF
 

中文:
定义 仿射映射.restrict
  签名: (φ : P₁ ->ᵃ[k] P₂) {E : 仿射子空间 k P₁} {F : 仿射子空间 k P₂}
  定义体: by
  refine ⟨?_, ?_, ?_⟩
· exact fun x => ⟨φ x, hEF AffineSubspace.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  · refine φ.linear.restrict (?_ : E.direction <= F.direction.comap φ.linear)
    rw [← Submodule.map_le_iff_le_comap]; rw [← AffineSubspace.map_direction]
    exact AffineSubspace.direction_le hEF
 

Depends on / 依赖: AffineMap, AffineMap.map_vadd, AffineSubspace, AffineSubspace.coe_vadd, AffineSubspace.direction_le, AffineSubspace.map_direction, AffineSubspace.mem_map.mpr, E.direction, F.direction.comap, Submodule, Submodule.map_le_iff_le_comap, Subtype, Subtype.ext_iff, coe_vadd, direction, direction_le, ext_iff, linear, linear.restrict, map_direction
-/
def AffineMap.restrict (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁} {F : AffineSubspace k P₂}
    [Nonempty E] [Nonempty F] (hEF : E.map φ <= F) : E ->ᵃ[k] F := by
  refine ⟨?_, ?_, ?_⟩
· exact fun x => ⟨φ x, hEF AffineSubspace.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  · refine φ.linear.restrict (?_ : E.direction <= F.direction.comap φ.linear)
    rw [← Submodule.map_le_iff_le_comap]; rw [← AffineSubspace.map_direction]
    exact AffineSubspace.direction_le hEF
  · intro p v
    simp only [Subtype.ext_iff, AffineSubspace.coe_vadd]
    apply AffineMap.map_vadd

/--
theorem `AffineMap.restrict.coe_apply` / 定理 `AffineMap.restrict.coe_apply`

English:
theorem AffineMap.restrict.coe_apply
  statement: (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁}
  proof: rfl

中文:
定理 仿射映射.restrict.coe_apply
  结论: (φ : P₁ ->ᵃ[k] P₂) {E : 仿射子空间 k P₁}
  证明: rfl
-/
theorem AffineMap.restrict.coe_apply (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ <= F) (x : E) :
    ↑(φ.restrict hEF x) = φ x :=
  rfl

/--
theorem `AffineMap.restrict.linear_aux` / 定理 `AffineMap.restrict.linear_aux`

English:
theorem AffineMap.restrict.linear_aux
  statement: {φ : P₁ ->ᵃ[k] P₂} {E : AffineSubspace k P₁}
  proof: by
  rw [← Submodule.map_le_iff_le_comap]; rw [← AffineSubspace.map_direction]
  exact AffineSubspace.direction_le hEF

中文:
定理 仿射映射.restrict.linear_aux
  结论: {φ : P₁ ->ᵃ[k] P₂} {E : 仿射子空间 k P₁}
  证明: by
  rw [← Submodule.map_le_iff_le_comap]; rw [← AffineSubspace.map_direction]
  exact AffineSubspace.direction_le hEF

Depends on / 依赖: AffineSubspace, AffineSubspace.direction_le, AffineSubspace.map_direction, Submodule, Submodule.map_le_iff_le_comap, direction_le, map_direction, map_le_iff_le_comap
-/
theorem AffineMap.restrict.linear_aux {φ : P₁ ->ᵃ[k] P₂} {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} (hEF : E.map φ <= F) : E.direction <= F.direction.comap φ.linear := by
  rw [← Submodule.map_le_iff_le_comap]; rw [← AffineSubspace.map_direction]
  exact AffineSubspace.direction_le hEF

/--
theorem `AffineMap.restrict.linear` / 定理 `AffineMap.restrict.linear`

English:
theorem AffineMap.restrict.linear
  statement: (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁}
  proof: rfl

中文:
定理 仿射映射.restrict.linear
  结论: (φ : P₁ ->ᵃ[k] P₂) {E : 仿射子空间 k P₁}
  证明: rfl
-/
theorem AffineMap.restrict.linear (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ <= F) :
    (φ.restrict hEF).linear = φ.linear.restrict (AffineMap.restrict.linear_aux hEF) :=
  rfl

/--
theorem `AffineMap.restrict.injective` / 定理 `AffineMap.restrict.injective`

English:
theorem AffineMap.restrict.injective
  statement: {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Injective φ)
  proof: by
  intro x y h
  simp only [Subtype.ext_iff, AffineMap.restrict.coe_apply] at h ⊢
  exact hφ h

中文:
定理 仿射映射.restrict.injective
  结论: {φ : P₁ ->ᵃ[k] P₂} (hφ : 函数.单射 φ)
  证明: by
  intro x y h
  simp only [Subtype.ext_iff, AffineMap.restrict.coe_apply] at h ⊢
  exact hφ h

Depends on / 依赖: AffineMap, AffineMap.restrict.coe_apply, Subtype, Subtype.ext_iff, coe_apply, ext_iff, restrict
-/
theorem AffineMap.restrict.injective {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Injective φ)
    {E : AffineSubspace k P₁} {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F]
    (hEF : E.map φ <= F) : Function.Injective (AffineMap.restrict φ hEF) := by
  intro x y h
  simp only [Subtype.ext_iff, AffineMap.restrict.coe_apply] at h ⊢
  exact hφ h

/--
theorem `AffineMap.restrict.surjective` / 定理 `AffineMap.restrict.surjective`

English:
theorem AffineMap.restrict.surjective
  statement: (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁}
  proof: by
  rintro ⟨x, hx : x in F⟩
  rw [← h]; rw [AffineSubspace.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, rfl⟩

中文:
定理 仿射映射.restrict.surjective
  结论: (φ : P₁ ->ᵃ[k] P₂) {E : 仿射子空间 k P₁}
  证明: by
  rintro ⟨x, hx : x in F⟩
  rw [← h]; rw [AffineSubspace.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, rfl⟩

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_map, mem_map
-/
theorem AffineMap.restrict.surjective (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (h : E.map φ = F) :
    Function.Surjective (AffineMap.restrict φ (le_of_eq h)) := by
  rintro ⟨x, hx : x in F⟩
  rw [← h]; rw [AffineSubspace.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, rfl⟩

/--
theorem `AffineMap.restrict.bijective` / 定理 `AffineMap.restrict.bijective`

English:
theorem AffineMap.restrict.bijective
  statement: {E : AffineSubspace k P₁} [Nonempty E] {φ : P₁ ->ᵃ[k] P₂}
  proof: ⟨AffineMap.restrict.injective hφ _, AffineMap.restrict.surjective _ rfl⟩

中文:
定理 仿射映射.restrict.bijective
  结论: {E : 仿射子空间 k P₁} [非空 E] {φ : P₁ ->ᵃ[k] P₂}
  证明: ⟨AffineMap.restrict.injective hφ _, AffineMap.restrict.surjective _ rfl⟩

Depends on / 依赖: AffineMap, AffineMap.restrict.injective, AffineMap.restrict.surjective, injective, restrict, surjective
-/
theorem AffineMap.restrict.bijective {E : AffineSubspace k P₁} [Nonempty E] {φ : P₁ ->ᵃ[k] P₂}
    (hφ : Function.Injective φ) : Function.Bijective (φ.restrict (le_refl (E.map φ))) :=
  ⟨AffineMap.restrict.injective hφ _, AffineMap.restrict.surjective _ rfl⟩

namespace AffineEquiv

/--
Definition of `affineSubspaceMap` / `affineSubspaceMap` 的定义

English:
definition affineSubspaceMap
  signature: (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
  body: .ofBijective (AffineMap.restrict.bijective e.injective)

@[simp]

中文:
定义 affineSubspaceMap
  签名: (e : P₁ ≃ᵃ[k] P₂) (s : 仿射子空间 k P₁)
  定义体: .ofBijective (AffineMap.restrict.bijective e.injective)

@[simp]

Depends on / 依赖: AffineMap, AffineMap.restrict.bijective, bijective, e.injective, injective, ofBijective, restrict
-/
noncomputable def affineSubspaceMap (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
    [Nonempty s] : s ≃ᵃ[k] s.map e.toAffineMap :=
  .ofBijective (AffineMap.restrict.bijective e.injective)

@[simp]
/--
theorem `affineSubspaceMap_apply` / 定理 `affineSubspaceMap_apply`

English:
theorem affineSubspaceMap_apply
  statement: (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
  proof: rfl

@[simp]

中文:
定理 affineSubspaceMap_apply
  结论: (e : P₁ ≃ᵃ[k] P₂) (s : 仿射子空间 k P₁)
  证明: rfl

@[simp]
-/
theorem affineSubspaceMap_apply (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
    [Nonempty s] (x : s) : e.affineSubspaceMap s x = e x :=
  rfl

@[simp]
/--
theorem `affineSubspaceMap_apply_symm_apply` / 定理 `affineSubspaceMap_apply_symm_apply`

English:
theorem affineSubspaceMap_apply_symm_apply
  statement: (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
  proof: congrArg Subtype.val (e.affineSubspaceMap s).apply_symm_apply x

中文:
定理 affineSubspaceMap_apply_symm_apply
  结论: (e : P₁ ≃ᵃ[k] P₂) (s : 仿射子空间 k P₁)
  证明: congrArg Subtype.val (e.affineSubspaceMap s).apply_symm_apply x

Depends on / 依赖: Subtype, Subtype.val, affineSubspaceMap, apply_symm_apply, e.affineSubspaceMap
-/
theorem affineSubspaceMap_apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
    [Nonempty s] (x : s.map e.toAffineMap) : e ((e.affineSubspaceMap s).symm x) = x :=
congrArg Subtype.val (e.affineSubspaceMap s).apply_symm_apply x

end AffineEquiv
