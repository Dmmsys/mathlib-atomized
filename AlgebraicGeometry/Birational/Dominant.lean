/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
/-!

# Dominant rational maps

This file defines `RationalMap.IsDominant` and establishes its connection to
`IsDominant` on the underlying partial maps.

## Main definition

- `Scheme.RationalMap.IsDominant`: a rational map is dominant if some (equivalently, any)
  representative partial map has dominant underlying morphism.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace Scheme

namespace PartialMap

set_option backward.defeqAttrib.useBackward true in
/--
Instance `isDominant_restrict_hom` / 实例 `isDominant_restrict_hom`

English:
instance isDominant_restrict_hom
  signature: (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
  body: by
  dsimp only [restrict_domain, restrict_hom]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU hU'
  rwa [IsDominant.comp_iff]

中文:
实例 isDominant_restrict_hom
  签名: (f : X.Partial映射 Y) [是Dominant f.hom] (U : X.Opens)
  定义体: by
  dsimp only [restrict_domain, restrict_hom]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU hU'
  rwa [IsDominant.comp_iff]

Depends on / 依赖: IsDominant, IsDominant.comp_iff, Opens.isDominant_homOfLE, X.homOfLE, comp_iff, homOfLE, isDominant_homOfLE, restrict_domain, restrict_hom
-/
instance isDominant_restrict_hom (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U <= f.domain) : IsDominant (f.restrict U hU hU').hom := by
  dsimp only [restrict_domain, restrict_hom]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU hU'
  rwa [IsDominant.comp_iff]

/--
lemma `isDominant_hom_of_isDominant_restrict_hom` / 引理 `isDominant_hom_of_isDominant_restrict_hom`

English:
lemma isDominant_hom_of_isDominant_restrict_hom
  statement: (f : X.PartialMap Y) (U : X.Opens)
  proof: IsDominant.of_comp (X.homOfLE hU') f.hom (H := H)

中文:
引理 isDominant_hom_of_isDominant_restrict_hom
  结论: (f : X.Partial映射 Y) (U : X.Opens)
  证明: IsDominant.of_comp (X.homOfLE hU') f.hom (H := H)

Depends on / 依赖: IsDominant, IsDominant.of_comp, X.homOfLE, f.hom, homOfLE, of_comp
-/
lemma isDominant_hom_of_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U <= f.domain) [H : IsDominant (f.restrict U hU hU').hom] :
    IsDominant f.hom :=
  IsDominant.of_comp (X.homOfLE hU') f.hom (H := H)

/--
lemma `isDominant_hom_iff_isDominant_restrict_hom` / 引理 `isDominant_hom_iff_isDominant_restrict_hom`

English:
lemma isDominant_hom_iff_isDominant_restrict_hom
  statement: (f : X.PartialMap Y) (U : X.Opens)
  proof: ⟨fun _ => f.isDominant_restrict_hom U hU hU',
    fun _ => f.isDominant_hom_of_isDominant_restrict_hom U hU hU'⟩

中文:
引理 isDominant_hom_iff_isDominant_restrict_hom
  结论: (f : X.Partial映射 Y) (U : X.Opens)
  证明: ⟨fun _ => f.isDominant_restrict_hom U hU hU',
    fun _ => f.isDominant_hom_of_isDominant_restrict_hom U hU hU'⟩

Depends on / 依赖: f.isDominant_hom_of_isDominant_restrict_hom, f.isDominant_restrict_hom, isDominant_hom_of_isDominant_restrict_hom, isDominant_restrict_hom
-/
lemma isDominant_hom_iff_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U <= f.domain) :
    IsDominant f.hom ↔ IsDominant (f.restrict U hU hU').hom :=
  ⟨fun _ => f.isDominant_restrict_hom U hU hU',
    fun _ => f.isDominant_hom_of_isDominant_restrict_hom U hU hU'⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isDominant_hom_iff_of_equiv` / 引理 `isDominant_hom_iff_of_equiv`

English:
lemma isDominant_hom_iff_of_equiv
  given: (f g : X.PartialMap Y) (h : f.equiv g)
  proof: by
  obtain ⟨W, hW, hWl, hWr, h⟩ := h
  have e₁ := isDominant_hom_iff_isDominant_restrict_hom f W hW hWl
  have e₂ := isDominant_hom_iff_isDominant_restrict_hom g W hW hWr
  dsimp only [restrict_domain, restrict_hom] at ⊢ e₁ e₂ h
  rw [e₁]; rw [h]; rw [← e₂]

中文:
引理 isDominant_hom_iff_of_equiv
  条件: (f g : X.Partial映射 Y) (h : f.equiv g)
  证明: by
  obtain ⟨W, hW, hWl, hWr, h⟩ := h
  have e₁ := isDominant_hom_iff_isDominant_restrict_hom f W hW hWl
  have e₂ := isDominant_hom_iff_isDominant_restrict_hom g W hW hWr
  dsimp only [restrict_domain, restrict_hom] at ⊢ e₁ e₂ h
  rw [e₁]; rw [h]; rw [← e₂]

Depends on / 依赖: isDominant_hom_iff_isDominant_restrict_hom, restrict_domain, restrict_hom
-/
lemma isDominant_hom_iff_of_equiv (f g : X.PartialMap Y) (h : f.equiv g) :
    IsDominant f.hom ↔ IsDominant g.hom := by
  obtain ⟨W, hW, hWl, hWr, h⟩ := h
  have e₁ := isDominant_hom_iff_isDominant_restrict_hom f W hW hWl
  have e₂ := isDominant_hom_iff_isDominant_restrict_hom g W hW hWr
  dsimp only [restrict_domain, restrict_hom] at ⊢ e₁ e₂ h
  rw [e₁]; rw [h]; rw [← e₂]

end PartialMap

/-- A rational map is dominant if some (equivalently, any) representative partial map has
dominant underlying morphism. -/
@[mk_iff, stacks 0A1Z]
/--
Definition of `RationalMap.IsDominant` / `RationalMap.IsDominant` 的定义

English:
class RationalMap.IsDominant
  parameters: (f : X ⤏ Y)
  axioms and operations (2):
    - out : Quotient.liftOn f (fun g => IsDominant g.hom) fun _ _ h => propext (PartialMap.isDominant_hom_iff_of_equiv _ _ h)
    - @[simp]

中文:
类 RationalMap.是Dominant
  参数: (f : X ⤏ Y)
  公理与运算 (2 个):
    - out : 商.liftOn f (fun g => 是Dominant g.hom) fun _ _ h => propext (Partial映射.isDominant_hom_iff_of_equiv _ _ h)
    - @[simp]
-/
protected class RationalMap.IsDominant (f : X ⤏ Y) : Prop where
out : Quotient.liftOn f (fun g => IsDominant g.hom) fun _ _ h =>
    propext (PartialMap.isDominant_hom_iff_of_equiv _ _ h)

@[simp]
/--
lemma `PartialMap.isDominant_toRationalMap_iff` / 引理 `PartialMap.isDominant_toRationalMap_iff`

English:
lemma PartialMap.isDominant_toRationalMap_iff
  given: (f : X.PartialMap Y)
  proof: f.toRationalMap.isDominant_iff

中文:
引理 Partial映射.isDominant_toRationalMap_iff
  条件: (f : X.Partial映射 Y)
  证明: f.toRationalMap.isDominant_iff

Depends on / 依赖: f.toRationalMap.isDominant_iff, isDominant_iff, toRationalMap
-/
lemma PartialMap.isDominant_toRationalMap_iff (f : X.PartialMap Y) :
    f.toRationalMap.IsDominant ↔ IsDominant f.hom :=
  f.toRationalMap.isDominant_iff

instance (f : X.PartialMap Y) [IsDominant f.hom] :
    f.toRationalMap.IsDominant := by
  rwa [f.isDominant_toRationalMap_iff]

instance (f : X ⤏ Y) [f.IsDominant] :
    IsDominant f.representative.hom := by
  rwa [← f.representative.isDominant_toRationalMap_iff, f.toRationalMap_representative]

end Scheme

end AlgebraicGeometry
