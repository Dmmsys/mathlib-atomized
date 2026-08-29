/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# Quasi-isomorphisms of short complexes

This file introduces the typeclass `QuasiIso φ` for a morphism `φ : S₁ ⟶ S₂`
of short complexes (which have homology): the condition is that the induced
morphism `homologyMap φ` in homology is an isomorphism.

-/

public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

/--
Definition of `QuasiIso` / `QuasiIso` 的定义

English:
class QuasiIso
  parameters: (φ : S₁ ⟶ S₂)
  axioms and operations (1):
    - isIso' : IsIso (homologyMap φ)

中文:
类 QuasiIso
  参数: (φ : S₁ ⟶ S₂)
  公理与运算 (1 个):
    - isIso' : IsIso (homologyMap φ)
-/
class QuasiIso (φ : S₁ ⟶ S₂) : Prop where
  /-- the homology map is an isomorphism -/
  isIso' : IsIso (homologyMap φ)

/--
Instance `QuasiIso.isIso` / 实例 `QuasiIso.isIso`

English:
instance QuasiIso.isIso
  signature: (φ : S₁ ⟶ S₂) [QuasiIso φ]
  body: QuasiIso.isIso'

中文:
实例 QuasiIso.isIso
  签名: (φ : S₁ ⟶ S₂) [QuasiIso φ]
  定义体: QuasiIso.isIso'

Depends on / 依赖: QuasiIso, QuasiIso.isIso
-/
instance QuasiIso.isIso (φ : S₁ ⟶ S₂) [QuasiIso φ] : IsIso (homologyMap φ) := QuasiIso.isIso'

/--
lemma `quasiIso_iff` / 引理 `quasiIso_iff`

English:
lemma quasiIso_iff
  given: (φ : S₁ ⟶ S₂)
  proof: by
  constructor
  · intro h
    infer_instance
  · intro h
    exact ⟨h⟩

中文:
引理 quasiIso_iff
  条件: (φ : S₁ ⟶ S₂)
  证明: by
  constructor
  · intro h
    infer_instance
  · intro h
    exact ⟨h⟩

Depends on / 依赖: infer_instance
-/
lemma quasiIso_iff (φ : S₁ ⟶ S₂) :
    QuasiIso φ ↔ IsIso (homologyMap φ) := by
  constructor
  · intro h
    infer_instance
  · intro h
    exact ⟨h⟩

/--
Instance `quasiIso_of_isIso` / 实例 `quasiIso_of_isIso`

English:
instance quasiIso_of_isIso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ]
  body: ⟨(homologyMapIso (asIso φ)).isIso_hom⟩

中文:
实例 quasiIso_of_isIso
  签名: (φ : S₁ ⟶ S₂) [IsIso φ]
  定义体: ⟨(homologyMapIso (asIso φ)).isIso_hom⟩

Depends on / 依赖: homologyMapIso, isIso_hom
-/
instance quasiIso_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ] : QuasiIso φ :=
  ⟨(homologyMapIso (asIso φ)).isIso_hom⟩

/--
Instance `quasiIso_comp` / 实例 `quasiIso_comp`

English:
instance quasiIso_comp
  signature: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] [hφ' : QuasiIso φ']
  body: by
  rw [quasiIso_iff] at hφ hφ' ⊢
  rw [homologyMap_comp]
  infer_instance

中文:
实例 quasiIso_comp
  签名: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] [hφ' : QuasiIso φ']
  定义体: by
  rw [quasiIso_iff] at hφ hφ' ⊢
  rw [homologyMap_comp]
  infer_instance

Depends on / 依赖: homologyMap_comp, infer_instance, quasiIso_iff
-/
instance quasiIso_comp (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') := by
  rw [quasiIso_iff] at hφ hφ' ⊢
  rw [homologyMap_comp]
  infer_instance

/--
lemma `quasiIso_of_comp_left` / 引理 `quasiIso_of_comp_left`

English:
lemma quasiIso_of_comp_left
  statement: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
  proof: by
  rw [quasiIso_iff] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ) (homologyMap φ')

中文:
引理 quasiIso_of_comp_left
  结论: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
  证明: by
  rw [quasiIso_iff] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ) (homologyMap φ')

Depends on / 依赖: IsIso.of_isIso_comp_left, homologyMap, homologyMap_comp, of_isIso_comp_left, quasiIso_iff
-/
lemma quasiIso_of_comp_left (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
    [hφ : QuasiIso φ] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ' := by
  rw [quasiIso_iff] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ) (homologyMap φ')

/--
lemma `quasiIso_iff_comp_left` / 引理 `quasiIso_iff_comp_left`

English:
lemma quasiIso_iff_comp_left
  given: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ]
  proof: by
  constructor
  · intro
    exact quasiIso_of_comp_left φ φ'
  · intro
    exact quasiIso_comp φ φ'

中文:
引理 quasiIso_iff_comp_left
  条件: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ]
  证明: by
  constructor
  · intro
    exact quasiIso_of_comp_left φ φ'
  · intro
    exact quasiIso_comp φ φ'

Depends on / 依赖: quasiIso_comp, quasiIso_of_comp_left
-/
lemma quasiIso_iff_comp_left (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ : QuasiIso φ] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ' := by
  constructor
  · intro
    exact quasiIso_of_comp_left φ φ'
  · intro
    exact quasiIso_comp φ φ'

/--
lemma `quasiIso_of_comp_right` / 引理 `quasiIso_of_comp_right`

English:
lemma quasiIso_of_comp_right
  statement: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
  proof: by
  rw [quasiIso_iff] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ) (homologyMap φ')

中文:
引理 quasiIso_of_comp_right
  结论: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
  证明: by
  rw [quasiIso_iff] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ) (homologyMap φ')

Depends on / 依赖: IsIso.of_isIso_comp_right, homologyMap, homologyMap_comp, of_isIso_comp_right, quasiIso_iff
-/
lemma quasiIso_of_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
    [hφ' : QuasiIso φ'] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ := by
  rw [quasiIso_iff] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ) (homologyMap φ')

/--
lemma `quasiIso_iff_comp_right` / 引理 `quasiIso_iff_comp_right`

English:
lemma quasiIso_iff_comp_right
  given: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ' : QuasiIso φ']
  proof: by
  constructor
  · intro
    exact quasiIso_of_comp_right φ φ'
  · intro
    exact quasiIso_comp φ φ'

中文:
引理 quasiIso_iff_comp_right
  条件: (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ' : QuasiIso φ']
  证明: by
  constructor
  · intro
    exact quasiIso_of_comp_right φ φ'
  · intro
    exact quasiIso_comp φ φ'

Depends on / 依赖: quasiIso_comp, quasiIso_of_comp_right
-/
lemma quasiIso_iff_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ := by
  constructor
  · intro
    exact quasiIso_of_comp_right φ φ'
  · intro
    exact quasiIso_comp φ φ'

set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIso_of_arrow_mk_iso` / 引理 `quasiIso_of_arrow_mk_iso`

English:
lemma quasiIso_of_arrow_mk_iso
  statement: (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ')
  proof: by
  let α : S₃ ⟶ S₁ := e.inv.left
  let β : S₂ ⟶ S₄ := e.hom.right
  suffices φ' = α ≫ φ ≫ β by
    rw [this]
    infer_instance
  simp only [α, β, Arrow.w_mk_right_assoc, Arrow.mk_hom,
    ← Arrow.comp_right, e.inv_hom_id, Arrow.id_right, comp_id]

中文:
引理 quasiIso_of_arrow_mk_iso
  结论: (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ')
  证明: by
  let α : S₃ ⟶ S₁ := e.inv.left
  let β : S₂ ⟶ S₄ := e.hom.right
  suffices φ' = α ≫ φ ≫ β by
    rw [this]
    infer_instance
  simp only [α, β, Arrow.w_mk_right_assoc, Arrow.mk_hom,
    ← Arrow.comp_right, e.inv_hom_id, Arrow.id_right, comp_id]

Depends on / 依赖: Arrow.comp_right, Arrow.id_right, Arrow.mk_hom, Arrow.w_mk_right_assoc, comp_id, comp_right, e.hom.right, e.inv.left, e.inv_hom_id, id_right, infer_instance, inv_hom_id, mk_hom, w_mk_right_assoc
-/
lemma quasiIso_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ')
    [hφ : QuasiIso φ] : QuasiIso φ' := by
  let α : S₃ ⟶ S₁ := e.inv.left
  let β : S₂ ⟶ S₄ := e.hom.right
  suffices φ' = α ≫ φ ≫ β by
    rw [this]
    infer_instance
  simp only [α, β, Arrow.w_mk_right_assoc, Arrow.mk_hom,
    ← Arrow.comp_right, e.inv_hom_id, Arrow.id_right, comp_id]

/--
lemma `quasiIso_iff_of_arrow_mk_iso` / 引理 `quasiIso_iff_of_arrow_mk_iso`

English:
lemma quasiIso_iff_of_arrow_mk_iso
  given: (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ')
  proof: ⟨fun _ => quasiIso_of_arrow_mk_iso φ φ' e, fun _ => quasiIso_of_arrow_mk_iso φ' φ e.symm⟩

中文:
引理 quasiIso_iff_of_arrow_mk_iso
  条件: (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ')
  证明: ⟨fun _ => quasiIso_of_arrow_mk_iso φ φ' e, fun _ => quasiIso_of_arrow_mk_iso φ' φ e.symm⟩

Depends on / 依赖: e.symm, quasiIso_of_arrow_mk_iso
-/
lemma quasiIso_iff_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ') :
    QuasiIso φ ↔ QuasiIso φ' :=
  ⟨fun _ => quasiIso_of_arrow_mk_iso φ φ' e, fun _ => quasiIso_of_arrow_mk_iso φ' φ e.symm⟩

/--
lemma `LeftHomologyMapData.quasiIso_iff` / 引理 `LeftHomologyMapData.quasiIso_iff`

English:
lemma LeftHomologyMapData.quasiIso_iff
  statement: {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
  proof: by
  rw [ShortComplex.quasiIso_iff]; rw [γ.homologyMap_eq]
  constructor
  · intro h
    have : IsIso (γ.φH ≫ (LeftHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (LeftHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (LeftHomologyData.homologyIso h₂).inv
 

中文:
引理 LeftHomologyMapData.quasiIso_iff
  结论: {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
  证明: by
  rw [ShortComplex.quasiIso_iff]; rw [γ.homologyMap_eq]
  constructor
  · intro h
    have : IsIso (γ.φH ≫ (LeftHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (LeftHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (LeftHomologyData.homologyIso h₂).inv
 

Depends on / 依赖: IsIso.of_isIso_comp_left, IsIso.of_isIso_comp_right, LeftHomologyData, LeftHomologyData.homologyIso, ShortComplex, ShortComplex.quasiIso_iff, homologyIso, homologyMap_eq, infer_instance, of_isIso_comp_left, of_isIso_comp_right, quasiIso_iff
-/
lemma LeftHomologyMapData.quasiIso_iff {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
    {h₂ : S₂.LeftHomologyData} (γ : LeftHomologyMapData φ h₁ h₂) :
    QuasiIso φ ↔ IsIso γ.φH := by
  rw [ShortComplex.quasiIso_iff]; rw [γ.homologyMap_eq]
  constructor
  · intro h
    have : IsIso (γ.φH ≫ (LeftHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (LeftHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (LeftHomologyData.homologyIso h₂).inv
  · intro h
    infer_instance

/--
lemma `RightHomologyMapData.quasiIso_iff` / 引理 `RightHomologyMapData.quasiIso_iff`

English:
lemma RightHomologyMapData.quasiIso_iff
  statement: {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
  proof: by
  rw [ShortComplex.quasiIso_iff]; rw [γ.homologyMap_eq]
  constructor
  · intro h
    have : IsIso (γ.φH ≫ (RightHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (RightHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (RightHomologyData.homologyIso h₂).in

中文:
引理 RightHomologyMapData.quasiIso_iff
  结论: {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
  证明: by
  rw [ShortComplex.quasiIso_iff]; rw [γ.homologyMap_eq]
  constructor
  · intro h
    have : IsIso (γ.φH ≫ (RightHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (RightHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (RightHomologyData.homologyIso h₂).in

Depends on / 依赖: IsIso.of_isIso_comp_left, IsIso.of_isIso_comp_right, RightHomologyData, RightHomologyData.homologyIso, ShortComplex, ShortComplex.quasiIso_iff, homologyIso, homologyMap_eq, infer_instance, of_isIso_comp_left, of_isIso_comp_right, quasiIso_iff
-/
lemma RightHomologyMapData.quasiIso_iff {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} (γ : RightHomologyMapData φ h₁ h₂) :
    QuasiIso φ ↔ IsIso γ.φH := by
  rw [ShortComplex.quasiIso_iff]; rw [γ.homologyMap_eq]
  constructor
  · intro h
    have : IsIso (γ.φH ≫ (RightHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (RightHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (RightHomologyData.homologyIso h₂).inv
  · intro h
    infer_instance

/--
lemma `quasiIso_iff_isIso_leftHomologyMap'` / 引理 `quasiIso_iff_isIso_leftHomologyMap'`

English:
lemma quasiIso_iff_isIso_leftHomologyMap'
  statement: (φ : S₁ ⟶ S₂)
  proof: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff]; rw [γ.leftHomologyMap'_eq]

中文:
引理 quasiIso_iff_isIso_leftHomologyMap'
  结论: (φ : S₁ ⟶ S₂)
  证明: by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff]; rw [γ.leftHomologyMap'_eq]

Depends on / 依赖: LeftHomologyMapData, leftHomologyMap, quasiIso_iff
-/
lemma quasiIso_iff_isIso_leftHomologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    QuasiIso φ ↔ IsIso (leftHomologyMap' φ h₁ h₂) := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff]; rw [γ.leftHomologyMap'_eq]

/--
lemma `quasiIso_iff_isIso_rightHomologyMap'` / 引理 `quasiIso_iff_isIso_rightHomologyMap'`

English:
lemma quasiIso_iff_isIso_rightHomologyMap'
  statement: (φ : S₁ ⟶ S₂)
  proof: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff]; rw [γ.rightHomologyMap'_eq]

中文:
引理 quasiIso_iff_isIso_rightHomologyMap'
  结论: (φ : S₁ ⟶ S₂)
  证明: by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff]; rw [γ.rightHomologyMap'_eq]

Depends on / 依赖: RightHomologyMapData, quasiIso_iff, rightHomologyMap
-/
lemma quasiIso_iff_isIso_rightHomologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    QuasiIso φ ↔ IsIso (rightHomologyMap' φ h₁ h₂) := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff]; rw [γ.rightHomologyMap'_eq]

/--
lemma `quasiIso_iff_isIso_homologyMap'` / 引理 `quasiIso_iff_isIso_homologyMap'`

English:
lemma quasiIso_iff_isIso_homologyMap'
  statement: (φ : S₁ ⟶ S₂)
  proof: quasiIso_iff_isIso_leftHomologyMap' _ _ _

中文:
引理 quasiIso_iff_isIso_homologyMap'
  结论: (φ : S₁ ⟶ S₂)
  证明: quasiIso_iff_isIso_leftHomologyMap' _ _ _

Depends on / 依赖: quasiIso_iff_isIso_leftHomologyMap
-/
lemma quasiIso_iff_isIso_homologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    QuasiIso φ ↔ IsIso (homologyMap' φ h₁ h₂) :=
  quasiIso_iff_isIso_leftHomologyMap' _ _ _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `quasiIso_of_epi_of_isIso_of_mono` / 引理 `quasiIso_of_epi_of_isIso_of_mono`

English:
lemma quasiIso_of_epi_of_isIso_of_mono
  given: (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃]
  proof: by
  rw [((LeftHomologyMapData.ofEpiOfIsIsoOfMono φ) S₁.leftHomologyData).quasiIso_iff]
  dsimp
  infer_instance

中文:
引理 quasiIso_of_epi_of_isIso_of_mono
  条件: (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃]
  证明: by
  rw [((LeftHomologyMapData.ofEpiOfIsIsoOfMono φ) S₁.leftHomologyData).quasiIso_iff]
  dsimp
  infer_instance

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.ofEpiOfIsIsoOfMono, infer_instance, leftHomologyData, ofEpiOfIsIsoOfMono, quasiIso_iff
-/
lemma quasiIso_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    QuasiIso φ := by
  rw [((LeftHomologyMapData.ofEpiOfIsIsoOfMono φ) S₁.leftHomologyData).quasiIso_iff]
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
lemma `quasiIso_opMap_iff` / 引理 `quasiIso_opMap_iff`

English:
lemma quasiIso_opMap_iff
  given: (φ : S₁ ⟶ S₂)
  proof: by
  have γ : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  rw [γ.left.quasiIso_iff]; rw [γ.op.right.quasiIso_iff]
  dsimp
  constructor
  · intro h
    apply isIso_of_op
  · intro h
    infer_instance

中文:
引理 quasiIso_opMap_iff
  条件: (φ : S₁ ⟶ S₂)
  证明: by
  have γ : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  rw [γ.left.quasiIso_iff]; rw [γ.op.right.quasiIso_iff]
  dsimp
  constructor
  · intro h
    apply isIso_of_op
  · intro h
    infer_instance

Depends on / 依赖: HomologyMapData, homologyData, infer_instance, isIso_of_op, left.quasiIso_iff, op.right.quasiIso_iff, quasiIso_iff
-/
lemma quasiIso_opMap_iff (φ : S₁ ⟶ S₂) :
    QuasiIso (opMap φ) ↔ QuasiIso φ := by
  have γ : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  rw [γ.left.quasiIso_iff]; rw [γ.op.right.quasiIso_iff]
  dsimp
  constructor
  · intro h
    apply isIso_of_op
  · intro h
    infer_instance

/--
lemma `quasiIso_opMap` / 引理 `quasiIso_opMap`

English:
lemma quasiIso_opMap
  given: (φ : S₁ ⟶ S₂) [QuasiIso φ]
  proof: by
  rw [quasiIso_opMap_iff]
  infer_instance

中文:
引理 quasiIso_opMap
  条件: (φ : S₁ ⟶ S₂) [QuasiIso φ]
  证明: by
  rw [quasiIso_opMap_iff]
  infer_instance

Depends on / 依赖: infer_instance, quasiIso_opMap_iff
-/
lemma quasiIso_opMap (φ : S₁ ⟶ S₂) [QuasiIso φ] :
    QuasiIso (opMap φ) := by
  rw [quasiIso_opMap_iff]
  infer_instance

/--
lemma `quasiIso_unopMap` / 引理 `quasiIso_unopMap`

English:
lemma quasiIso_unopMap
  statement: {S₁ S₂ : ShortComplex Cᵒᵖ} [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  rw [← quasiIso_opMap_iff]
  change QuasiIso φ
  infer_instance

中文:
引理 quasiIso_unopMap
  结论: {S₁ S₂ : ShortComplex Cᵒᵖ} [S₁.HasHomology] [S₂.HasHomology]
  证明: by
  rw [← quasiIso_opMap_iff]
  change QuasiIso φ
  infer_instance

Depends on / 依赖: QuasiIso, infer_instance, quasiIso_opMap_iff
-/
lemma quasiIso_unopMap {S₁ S₂ : ShortComplex Cᵒᵖ} [S₁.HasHomology] [S₂.HasHomology]
    [S₁.unop.HasHomology] [S₂.unop.HasHomology]
    (φ : S₁ ⟶ S₂) [QuasiIso φ] : QuasiIso (unopMap φ) := by
  rw [← quasiIso_opMap_iff]
  change QuasiIso φ
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIso_iff_isIso_liftCycles` / 引理 `quasiIso_iff_isIso_liftCycles`

English:
lemma quasiIso_iff_isIso_liftCycles
  statement: (φ : S₁ ⟶ S₂)
  proof: by
  let H : LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁)
      (LeftHomologyData.ofIsLimitKernelFork S₂ hf₂ _ S₂.cyclesIsKernel) :=
    { φK := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp])
      φH := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp]) }
  exact H.quasiIso

中文:
引理 quasiIso_iff_isIso_liftCycles
  结论: (φ : S₁ ⟶ S₂)
  证明: by
  let H : LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁)
      (LeftHomologyData.ofIsLimitKernelFork S₂ hf₂ _ S₂.cyclesIsKernel) :=
    { φK := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp])
      φH := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp]) }
  exact H.quasiIso

Depends on / 依赖: H.quasiIso_iff, LeftHomologyData, LeftHomologyData.ofIsLimitKernelFork, LeftHomologyData.ofZeros, LeftHomologyMapData, cyclesIsKernel, liftCycles, ofIsLimitKernelFork, ofZeros, quasiIso_iff, zero_comp
-/
lemma quasiIso_iff_isIso_liftCycles (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) :
    QuasiIso φ ↔ IsIso (S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp])) := by
  let H : LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁)
      (LeftHomologyData.ofIsLimitKernelFork S₂ hf₂ _ S₂.cyclesIsKernel) :=
    { φK := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp])
      φH := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp]) }
  exact H.quasiIso_iff

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIso_iff_isIso_descOpcycles` / 引理 `quasiIso_iff_isIso_descOpcycles`

English:
lemma quasiIso_iff_isIso_descOpcycles
  statement: (φ : S₁ ⟶ S₂)
  proof: by
  let H : RightHomologyMapData φ
      (RightHomologyData.ofIsColimitCokernelCofork S₁ hg₁ _ S₁.opcyclesIsCokernel)
        (RightHomologyData.ofZeros S₂ hf₂ hg₂) :=
    { φQ := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])
      φH := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, com

中文:
引理 quasiIso_iff_isIso_descOpcycles
  结论: (φ : S₁ ⟶ S₂)
  证明: by
  let H : RightHomologyMapData φ
      (RightHomologyData.ofIsColimitCokernelCofork S₁ hg₁ _ S₁.opcyclesIsCokernel)
        (RightHomologyData.ofZeros S₂ hf₂ hg₂) :=
    { φQ := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])
      φH := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, com

Depends on / 依赖: H.quasiIso_iff, RightHomologyData, RightHomologyData.ofIsColimitCokernelCofork, RightHomologyData.ofZeros, RightHomologyMapData, comp_zero, descOpcycles, ofIsColimitCokernelCofork, ofZeros, opcyclesIsCokernel, quasiIso_iff
-/
lemma quasiIso_iff_isIso_descOpcycles (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    QuasiIso φ ↔ IsIso (S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])) := by
  let H : RightHomologyMapData φ
      (RightHomologyData.ofIsColimitCokernelCofork S₁ hg₁ _ S₁.opcyclesIsCokernel)
        (RightHomologyData.ofZeros S₂ hf₂ hg₂) :=
    { φQ := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])
      φH := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero]) }
  exact H.quasiIso_iff

end ShortComplex

end CategoryTheory
