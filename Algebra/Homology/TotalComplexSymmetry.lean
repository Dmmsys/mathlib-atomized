/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.TotalComplex

/-! # The symmetry of the total complex of a bicomplex

Let `K : HomologicalComplex₂ C c₁ c₂` be a bicomplex. If we assume both
`[TotalComplexShape c₁ c₂ c]` and `[TotalComplexShape c₂ c₁ c]`, we may form
the total complex `K.total c` and `K.flip.total c`.

In this file, we show that if we assume `[TotalComplexShapeSymmetry c₁ c₂ c]`,
then there is an isomorphism `K.totalFlipIso c : K.flip.total c ≅ K.total c`.

Moreover, if we also have `[TotalComplexShapeSymmetry c₂ c₁ c]` and that the signs
are compatible `[TotalComplexShapeSymmetrySymmetry c₁ c₂ c]`, then the isomorphisms
`K.totalFlipIso c` and `K.flip.totalFlipIso c` are inverse to each other.

-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

open CategoryTheory Category Limits

namespace HomologicalComplex₂

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (K : HomologicalComplex₂ C c₁ c₂)
    (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
    [TotalComplexShapeSymmetry c₁ c₂ c]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.HasTotal
  signature: c] : K.flip.HasTotal c
  body: fun j =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) _
    (ComplexShape.symmetryEquiv c₁ c₂ c j) (fun _ => Iso.refl _)

中文:
实例 [K.HasTotal
  签名: c] : K.flip.HasTotal c
  定义体: fun j =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) _
    (ComplexShape.symmetryEquiv c₁ c₂ c j) (fun _ => Iso.refl _)
-/
instance [K.HasTotal c] : K.flip.HasTotal c := fun j =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) _
    (ComplexShape.symmetryEquiv c₁ c₂ c j) (fun _ => Iso.refl _)

/--
lemma `flip_hasTotal_iff` / 引理 `flip_hasTotal_iff`

English:
lemma flip_hasTotal_iff
  statement: K.flip.HasTotal c ↔ K.HasTotal c
  proof: by
  constructor
  · intro
    change K.flip.flip.HasTotal c
    have := TotalComplexShapeSymmetry.symmetry c₁ c₂ c
    infer_instance
  · intro
    infer_instance

中文:
引理 flip_hasTotal_iff
  结论: K.flip.HasTotal c ↔ K.HasTotal c
  证明: by
  constructor
  · intro
    change K.flip.flip.HasTotal c
    have := TotalComplexShapeSymmetry.symmetry c₁ c₂ c
    infer_instance
  · intro
    infer_instance

Depends on / 依赖: HasTotal, K.flip.flip.HasTotal, TotalComplexShapeSymmetry, TotalComplexShapeSymmetry.symmetry, infer_instance, symmetry
-/
lemma flip_hasTotal_iff : K.flip.HasTotal c ↔ K.HasTotal c := by
  constructor
  · intro
    change K.flip.flip.HasTotal c
    have := TotalComplexShapeSymmetry.symmetry c₁ c₂ c
    infer_instance
  · intro
    infer_instance

variable [K.HasTotal c] [DecidableEq J]

attribute [local simp] smul_smul

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `totalFlipIsoX` / `totalFlipIsoX` 的定义

English:
definition totalFlipIsoX
  signature: (j : J)
  body: K.flip.totalDesc (fun i₂ i₁ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.ιTotal c i₁ i₂ j (by
    rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂]; rw [h]))
  inv := K.totalDesc (fun i₁ i₂ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.flip.ιTotal c i₂ i₁ j (by
    rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂]; rw [h]))
  hom_inv

中文:
定义 totalFlipIsoX
  签名: (j : J)
  定义体: K.flip.totalDesc (fun i₂ i₁ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.ιTotal c i₁ i₂ j (by
    rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂]; rw [h]))
  inv := K.totalDesc (fun i₁ i₂ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.flip.ιTotal c i₂ i₁ j (by
    rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂]; rw [h]))
  hom_inv

Depends on / 依赖: ComplexShape, K.flip, K.flip.totalDesc, K.totalDesc, hom_inv_id, inv_hom_id, totalDesc
-/
noncomputable def totalFlipIsoX (j : J) : (K.flip.total c).X j ≅ (K.total c).X j where
  hom := K.flip.totalDesc (fun i₂ i₁ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.ιTotal c i₁ i₂ j (by
    rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂]; rw [h]))
  inv := K.totalDesc (fun i₁ i₂ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.flip.ιTotal c i₂ i₁ j (by
    rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂]; rw [h]))
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `totalFlipIsoX_hom_D₁` / 引理 `totalFlipIsoX_hom_D₁`

English:
lemma totalFlipIsoX_hom_D₁
  given: (j j' : J)
  proof: by
  by_cases h₀ : c.Rel j j'
  · ext i₂ i₁ h₁
    dsimp [totalFlipIsoX]
    rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [ι_D₁]; rw [ι_D₂_assoc]
    dsimp
    by_cases h₂ : c₁.Rel i₁ (c₁.next i₁)
    · have h₃ : ComplexShape.π c₂ c₁ c ⟨i₂, c₁.next i₁⟩ = j' := by
        rw [← ComplexShap

中文:
引理 totalFlipIsoX_hom_D₁
  条件: (j j' : J)
  证明: by
  by_cases h₀ : c.Rel j j'
  · ext i₂ i₁ h₁
    dsimp [totalFlipIsoX]
    rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [ι_D₁]; rw [ι_D₂_assoc]
    dsimp
    by_cases h₂ : c₁.Rel i₁ (c₁.next i₁)
    · have h₃ : ComplexShape.π c₂ c₁ c ⟨i₂, c₁.next i₁⟩ = j' := by
        rw [← ComplexShap

Depends on / 依赖: ComplexShape, ComplexShape.next_, K.flip.d, Linear, Linear.units_sm, Linear.units_smul_comp, c.Rel, c.next_eq, next_eq, totalFlipIsoX, units_sm, units_smul_comp
-/
lemma totalFlipIsoX_hom_D₁ (j j' : J) :
    (K.totalFlipIsoX c j).hom ≫ K.D₁ c j j' =
      K.flip.D₂ c j j' ≫ (K.totalFlipIsoX c j').hom := by
  by_cases h₀ : c.Rel j j'
  · ext i₂ i₁ h₁
    dsimp [totalFlipIsoX]
    rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [ι_D₁]; rw [ι_D₂_assoc]
    dsimp
    by_cases h₂ : c₁.Rel i₁ (c₁.next i₁)
    · have h₃ : ComplexShape.π c₂ c₁ c ⟨i₂, c₁.next i₁⟩ = j' := by
        rw [← ComplexShape.next_π₂ c₂ c i₂ h₂]; rw [h₁]; rw [c.next_eq' h₀]
      have h₄ : ComplexShape.π c₁ c₂ c ⟨c₁.next i₁, i₂⟩ = j' := by
        rw [← h₃]; rw [ComplexShape.π_symm c₁ c₂ c]
      rw [K.d₁_eq _ h₂ _ _ h₄]; rw [K.flip.d₂_eq _ _ h₂ _ h₃]; rw [Linear.units_smul_comp]; rw [assoc]; rw [ι_totalDesc]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [smul_smul]; rw [ComplexShape.σ_ε₁ c₂ c h₂ i₂]
      dsimp only [flip_X_X, flip_X_d]
    · rw [K.d₁_eq_zero _ _ _ _ h₂, K.flip.d₂_eq_zero _ _ _ _ h₂, smul_zero, zero_comp]
  · rw [K.D₁_shape _ _ _ h₀, K.flip.D₂_shape c _ _ h₀, zero_comp, comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `totalFlipIsoX_hom_D₂` / 引理 `totalFlipIsoX_hom_D₂`

English:
lemma totalFlipIsoX_hom_D₂
  given: (j j' : J)
  proof: by
  by_cases h₀ : c.Rel j j'
  · ext i₂ i₁ h₁
    dsimp [totalFlipIsoX]
    rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [ι_D₂]; rw [ι_D₁_assoc]
    dsimp
    by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
    · have h₃ : ComplexShape.π c₂ c₁ c (ComplexShape.next c₂ i₂, i₁) = j' := by
        rw [

中文:
引理 totalFlipIsoX_hom_D₂
  条件: (j j' : J)
  证明: by
  by_cases h₀ : c.Rel j j'
  · ext i₂ i₁ h₁
    dsimp [totalFlipIsoX]
    rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [ι_D₂]; rw [ι_D₁_assoc]
    dsimp
    by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
    · have h₃ : ComplexShape.π c₂ c₁ c (ComplexShape.next c₂ i₂, i₁) = j' := by
        rw [

Depends on / 依赖: ComplexShape, ComplexShape.next, ComplexShape.next_, K.flip.d, Linear, Linear.units_smul_comp, c.Rel, c.next_eq, next_eq, totalFlipIsoX, units_smul_comp
-/
lemma totalFlipIsoX_hom_D₂ (j j' : J) :
    (K.totalFlipIsoX c j).hom ≫ K.D₂ c j j' =
      K.flip.D₁ c j j' ≫ (K.totalFlipIsoX c j').hom := by
  by_cases h₀ : c.Rel j j'
  · ext i₂ i₁ h₁
    dsimp [totalFlipIsoX]
    rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [ι_D₂]; rw [ι_D₁_assoc]
    dsimp
    by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
    · have h₃ : ComplexShape.π c₂ c₁ c (ComplexShape.next c₂ i₂, i₁) = j' := by
        rw [← ComplexShape.next_π₁ c₁ c h₂ i₁]; rw [h₁]; rw [c.next_eq' h₀]
      have h₄ : ComplexShape.π c₁ c₂ c (i₁, ComplexShape.next c₂ i₂) = j' := by
        rw [← h₃]; rw [ComplexShape.π_symm c₁ c₂ c]
      rw [K.d₂_eq _ _ h₂ _ h₄]; rw [K.flip.d₁_eq _ h₂ _ _ h₃]; rw [Linear.units_smul_comp]; rw [assoc]; rw [ι_totalDesc]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [smul_smul]; rw [ComplexShape.σ_ε₂ c₁ c i₁ h₂]
      rfl
    · rw [K.d₂_eq_zero _ _ _ _ h₂, K.flip.d₁_eq_zero _ _ _ _ h₂, smul_zero, zero_comp]
  · rw [K.D₂_shape _ _ _ h₀, K.flip.D₁_shape c _ _ h₀, zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `totalFlipIso` / `totalFlipIso` 的定义

English:
definition totalFlipIso
  signature: : K.flip.total c ≅ K.total c
  body: HomologicalComplex.Hom.isoOfComponents (K.totalFlipIsoX c) (fun j j' _ => by
    simp only [total_d, Preadditive.comp_add, totalFlipIsoX_hom_D₁,
      totalFlipIsoX_hom_D₂, Preadditive.add_comp]
    rw [add_comm])

#adaptation_note

中文:
定义 totalFlipIso
  签名: : K.flip.total c ≅ K.total c
  定义体: HomologicalComplex.Hom.isoOfComponents (K.totalFlipIsoX c) (fun j j' _ => by
    simp only [total_d, Preadditive.comp_add, totalFlipIsoX_hom_D₁,
      totalFlipIsoX_hom_D₂, Preadditive.add_comp]
    rw [add_comm])

#adaptation_note

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, K.totalFlipIsoX, Preadditive, Preadditive.add_comp, Preadditive.comp_add, add_comm, add_comp, comp_add, isoOfComponents, totalFlipIsoX, total_d
-/
noncomputable def totalFlipIso : K.flip.total c ≅ K.total c :=
  HomologicalComplex.Hom.isoOfComponents (K.totalFlipIsoX c) (fun j j' _ => by
    simp only [total_d, Preadditive.comp_add, totalFlipIsoX_hom_D₁,
      totalFlipIsoX_hom_D₂, Preadditive.add_comp]
    rw [add_comm])

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `totalFlipIso_hom_f_D₁` / 引理 `totalFlipIso_hom_f_D₁`

English:
lemma totalFlipIso_hom_f_D₁
  given: (j j' : J)
  proof: by
  apply totalFlipIsoX_hom_D₁

#adaptation_note

中文:
引理 totalFlipIso_hom_f_D₁
  条件: (j j' : J)
  证明: by
  apply totalFlipIsoX_hom_D₁

#adaptation_note
-/
lemma totalFlipIso_hom_f_D₁ (j j' : J) :
    (K.totalFlipIso c).hom.f j ≫ K.D₁ c j j' =
      K.flip.D₂ c j j' ≫ (K.totalFlipIso c).hom.f j' := by
  apply totalFlipIsoX_hom_D₁

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `totalFlipIso_hom_f_D₂` / 引理 `totalFlipIso_hom_f_D₂`

English:
lemma totalFlipIso_hom_f_D₂
  given: (j j' : J)
  proof: by
  apply totalFlipIsoX_hom_D₂

中文:
引理 totalFlipIso_hom_f_D₂
  条件: (j j' : J)
  证明: by
  apply totalFlipIsoX_hom_D₂
-/
lemma totalFlipIso_hom_f_D₂ (j j' : J) :
    (K.totalFlipIso c).hom.f j ≫ K.D₂ c j j' =
      K.flip.D₁ c j j' ≫ (K.totalFlipIso c).hom.f j' := by
  apply totalFlipIsoX_hom_D₂

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `ιTotal_totalFlipIso_f_hom` / 引理 `ιTotal_totalFlipIso_f_hom`

English:
lemma ιTotal_totalFlipIso_f_hom
  proof: by
  simp [totalFlipIso, totalFlipIsoX]

中文:
引理 ιTotal_totalFlipIso_f_hom
  证明: by
  simp [totalFlipIso, totalFlipIsoX]

Depends on / 依赖: totalFlipIso, totalFlipIsoX
-/
lemma ιTotal_totalFlipIso_f_hom
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₂ c₁ c (i₂, i₁) = j) :
    K.flip.ιTotal c i₂ i₁ j h ≫ (K.totalFlipIso c).hom.f j =
      ComplexShape.σ c₁ c₂ c i₁ i₂ • K.ιTotal c i₁ i₂ j
        (by rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂, h]) := by
  simp [totalFlipIso, totalFlipIsoX]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `ιTotal_totalFlipIso_f_inv` / 引理 `ιTotal_totalFlipIso_f_inv`

English:
lemma ιTotal_totalFlipIso_f_inv
  proof: by
  simp [totalFlipIso, totalFlipIsoX]

中文:
引理 ιTotal_totalFlipIso_f_inv
  证明: by
  simp [totalFlipIso, totalFlipIsoX]

Depends on / 依赖: totalFlipIso, totalFlipIsoX
-/
lemma ιTotal_totalFlipIso_f_inv
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    K.ιTotal c i₁ i₂ j h ≫ (K.totalFlipIso c).inv.f j =
      ComplexShape.σ c₁ c₂ c i₁ i₂ • K.flip.ιTotal c i₂ i₁ j
        (by rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂, h]) := by
  simp [totalFlipIso, totalFlipIsoX]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: K.flip.flip.HasTotal c
  body: (inferInstance : K.HasTotal c)

中文:
实例 :
  签名: K.flip.flip.HasTotal c
  定义体: (inferInstance : K.HasTotal c)

Depends on / 依赖: HasTotal, K.HasTotal
-/
instance : K.flip.flip.HasTotal c := (inferInstance : K.HasTotal c)

section

variable [TotalComplexShapeSymmetry c₂ c₁ c] [TotalComplexShapeSymmetrySymmetry c₁ c₂ c]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `flip_totalFlipIso` / 引理 `flip_totalFlipIso`

English:
lemma flip_totalFlipIso
  statement: K.flip.totalFlipIso c = (K.totalFlipIso c).symm
  proof: by
  ext j i₁ i₂ h
  rw [Iso.symm_hom]; rw [ιTotal_totalFlipIso_f_hom]
  dsimp only [flip_flip]
  rw [ιTotal_totalFlipIso_f_inv]; rw [ComplexShape.σ_symm]

中文:
引理 flip_totalFlipIso
  结论: K.flip.totalFlipIso c = (K.totalFlipIso c).symm
  证明: by
  ext j i₁ i₂ h
  rw [Iso.symm_hom]; rw [ιTotal_totalFlipIso_f_hom]
  dsimp only [flip_flip]
  rw [ιTotal_totalFlipIso_f_inv]; rw [ComplexShape.σ_symm]

Depends on / 依赖: ComplexShape, Iso.symm_hom, flip_flip, symm_hom
-/
lemma flip_totalFlipIso : K.flip.totalFlipIso c = (K.totalFlipIso c).symm := by
  ext j i₁ i₂ h
  rw [Iso.symm_hom]; rw [ιTotal_totalFlipIso_f_hom]
  dsimp only [flip_flip]
  rw [ιTotal_totalFlipIso_f_inv]; rw [ComplexShape.σ_symm]

end

end HomologicalComplex₂
