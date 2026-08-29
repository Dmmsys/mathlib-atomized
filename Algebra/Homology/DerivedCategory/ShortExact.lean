/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The distinguished triangle attached to a short exact sequence of cochain complexes

Given a short exact short complex `S` in the category `CochainComplex C ℤ`,
we construct a distinguished triangle
`Q.obj S.X₁ ⟶ Q.obj S.X₂ ⟶ Q.obj S.X₃ ⟶ (Q.obj S.X₃)⟦1⟧`
in the derived category of `C`.
(See `triangleOfSES` and `triangleOfSES_distinguished`.)

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Category Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex C Int)} (hS : S.ShortExact)

/--
Definition of `triangleOfSESδ` / `triangleOfSESδ` 的定义

English:
definition triangleOfSESδ
  signature: :
  body: have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  inv (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
    Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
    (Q.commShiftIso (1 : Int)).hom.app S.X₁

中文:
定义 triangleOfSESδ
  签名: :
  定义体: have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  inv (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
    Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
    (Q.commShiftIso (1 : Int)).hom.app S.X₁

Depends on / 依赖: CochainComplex, CochainComplex.mappingCone.descShortComplex, CochainComplex.mappingCone.quasiIso_descShortComplex, CochainComplex.mappingCone.triangle, Q.commShiftIso, Q.map, commShiftIso, descShortComplex, hom.app, mappingCone, quasiIso_descShortComplex, triangle
-/
noncomputable def triangleOfSESδ :
    Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : Int)⟧ :=
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  inv (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
    Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
    (Q.commShiftIso (1 : Int)).hom.app S.X₁

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `descShortComplex_triangleOfSESδ` / 引理 `descShortComplex_triangleOfSESδ`

English:
lemma descShortComplex_triangleOfSESδ
  proof: by
  simp [triangleOfSESδ]

中文:
引理 descShortComplex_triangleOfSESδ
  证明: by
  simp [triangleOfSESδ]
-/
lemma descShortComplex_triangleOfSESδ :
    dsimp% Q.map (CochainComplex.mappingCone.descShortComplex S) ≫ triangleOfSESδ hS =
    Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
      (Functor.commShiftIso Q 1).hom.app S.X₁ := by
  simp [triangleOfSESδ]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `triangleOfSESδ_naturality` / 引理 `triangleOfSESδ_naturality`

English:
lemma triangleOfSESδ_naturality
  statement: {S₁ S₂ : ShortComplex (CochainComplex C Int)}
  proof: by
  simp only [triangleOfSESδ, Category.assoc,
    IsIso.inv_comp_eq]
  rw [← Functor.comp_map]; rw [← (Q.commShiftIso (1 : Int)).hom.naturality]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Iso.app_hom]; rw [Iso.cancel_iso_hom_right]; rw [← Q.m

中文:
引理 triangleOfSESδ_naturality
  结论: {S₁ S₂ : 短复形 (上链复形 C 整数)}
  证明: by
  simp only [triangleOfSESδ, Category.assoc,
    IsIso.inv_comp_eq]
  rw [← Functor.comp_map]; rw [← (Q.commShiftIso (1 : Int)).hom.naturality]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Iso.app_hom]; rw [Iso.cancel_iso_hom_right]; rw [← Q.m

Depends on / 依赖: Category, Category.assoc, Category.comp_id, CochainComplex, CochainComplex.mappingCone.descShortComplex_naturality, Functor, Functor.comp_map, Functor.map_comp, IsIso.hom_inv_id, IsIso.inv_comp_eq, Iso.app_hom, Iso.cancel_iso_hom_right, Q.commShiftIso, Q.map_comp, app_hom, cancel_iso_hom_right, commShiftIso, comp_id, comp_map, descShortComplex_naturality
-/
lemma triangleOfSESδ_naturality {S₁ S₂ : ShortComplex (CochainComplex C Int)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    triangleOfSESδ hS₁ ≫ (Q.map f.τ₁)⟦1⟧' = Q.map f.τ₃ ≫ triangleOfSESδ hS₂ := by
  simp only [triangleOfSESδ, Category.assoc,
    IsIso.inv_comp_eq]
  rw [← Functor.comp_map]; rw [← (Q.commShiftIso (1 : Int)).hom.naturality]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Iso.app_hom]; rw [Iso.cancel_iso_hom_right]; rw [← Q.map_comp]
  simp only [Functor.comp_map, ← CochainComplex.mappingCone.descShortComplex_naturality f,
    Functor.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Q.map_comp]; rw [← Q.map_comp]
  congr 1
  exact (CochainComplex.mappingCone.triangleMap S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm).comm₃

/-- The distinguished triangle in the derived category associated to a short
exact sequence of cochain complexes. -/
@[simps!]
/--
Definition of `triangleOfSES` / `triangleOfSES` 的定义

English:
definition triangleOfSES
  signature: : Triangle (DerivedCategory C)
  body: Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

中文:
定义 triangleOfSES
  签名: : Triangle (导出范畴 C)
  定义体: Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

Depends on / 依赖: Q.map, Triangle, Triangle.mk
-/
noncomputable def triangleOfSES : Triangle (DerivedCategory C) :=
  Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `triangleOfSESIso` / `triangleOfSESIso` 的定义

English:
definition triangleOfSESIso
  signature: :
  body: by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  refine Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (asIso (Q.map (CochainComplex.mappingCone.descShortComplex S))) ?_ ?_ ?_)
  · dsimp [triangleOfSES]
    simp only [comp_id, id_comp]
  · dsimp
    simp only [← Q.m

中文:
定义 triangleOfSESIso
  签名: :
  定义体: by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  refine Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (asIso (Q.map (CochainComplex.mappingCone.descShortComplex S))) ?_ ?_ ?_)
  · dsimp [triangleOfSES]
    simp only [comp_id, id_comp]
  · dsimp
    simp only [← Q.m

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, CochainComplex, CochainComplex.mappingCone.descShortComplex, CochainComplex.mappingCone.inr_descShortComplex, CochainComplex.mappingCone.quasiIso_descShortComplex, Functor, IsIso.hom_inv_id_assoc, Iso.refl, Iso.symm, Q.map, Q.map_comp, Triangle, Triangle.isoMk, comp_id, descShortComplex, hom_inv_id_assoc, id_comp, inr_descShortComplex, map_comp
-/
noncomputable def triangleOfSESIso :
    triangleOfSES hS ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle S.f) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  refine Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (asIso (Q.map (CochainComplex.mappingCone.descShortComplex S))) ?_ ?_ ?_)
  · dsimp [triangleOfSES]
    simp only [comp_id, id_comp]
  · dsimp
    simp only [← Q.map_comp, CochainComplex.mappingCone.inr_descShortComplex, id_comp]
  · dsimp [triangleOfSESδ]
    rw [CategoryTheory.Functor.map_id]; rw [comp_id]; rw [IsIso.hom_inv_id_assoc]

/--
lemma `triangleOfSES_distinguished` / 引理 `triangleOfSES_distinguished`

English:
lemma triangleOfSES_distinguished
  proof: by
  rw [mem_distTriang_iff]
  exact ⟨_, _, S.f, ⟨triangleOfSESIso hS⟩⟩

中文:
引理 triangleOfSES_distinguished
  证明: by
  rw [mem_distTriang_iff]
  exact ⟨_, _, S.f, ⟨triangleOfSESIso hS⟩⟩

Depends on / 依赖: mem_distTriang_iff, triangleOfSESIso
-/
lemma triangleOfSES_distinguished :
    triangleOfSES hS in distTriang (DerivedCategory C) := by
  rw [mem_distTriang_iff]
  exact ⟨_, _, S.f, ⟨triangleOfSESIso hS⟩⟩

section map

variable {S₁ S₂ : ShortComplex (CochainComplex C Int)} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
  (f : S₁ ⟶ S₂)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The morphism `triangleOfSES h₁ ⟶ triangleOfSES h₂` that is induced by a morphism of short
exact sequences of cochain complexes.
-/
@[simps]
/--
Definition of `triangleOfSES.map` / `triangleOfSES.map` 的定义

English:
definition triangleOfSES.map
  signature: : triangleOfSES h₁ ⟶ triangleOfSES h₂ where
  body: Q.map f.τ₁
  hom₂ := Q.map f.τ₂
  hom₃ := Q.map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    dsimp [triangleOfSES, triangleOfSESδ]
    rw [assoc]; rw [assoc]; rw [IsIso.inv_comp_eq]; rw [← Functor.map_comp_assoc]; rw [← Co

中文:
定义 triangleOfSES.map
  签名: : triangleOfSES h₁ ⟶ triangleOfSES h₂ where
  定义体: Q.map f.τ₁
  hom₂ := Q.map f.τ₂
  hom₃ := Q.map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    dsimp [triangleOfSES, triangleOfSESδ]
    rw [assoc]; rw [assoc]; rw [IsIso.inv_comp_eq]; rw [← Functor.map_comp_assoc]; rw [← Co

Depends on / 依赖: Q.map
-/
noncomputable def triangleOfSES.map : triangleOfSES h₁ ⟶ triangleOfSES h₂ where
  hom₁ := Q.map f.τ₁
  hom₂ := Q.map f.τ₂
  hom₃ := Q.map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    dsimp [triangleOfSES, triangleOfSESδ]
    rw [assoc]; rw [assoc]; rw [IsIso.inv_comp_eq]; rw [← Functor.map_comp_assoc]; rw [← CochainComplex.mappingCone.map_descShortComplex]; rw [Functor.map_comp_assoc]; rw [IsIso.hom_inv_id_assoc]; rw [← Functor.commShiftIso_hom_naturality]; rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]
    congr 2
    exact (CochainComplex.mappingCone.triangleMap S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm).comm₃

end map

end DerivedCategory
