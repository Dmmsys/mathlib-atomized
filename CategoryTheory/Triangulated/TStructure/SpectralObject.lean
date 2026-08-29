/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.SpectralObject
public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# Spectral objects attached to t-structures

Let `C` be a triangulated category equipped with a t-structure `t`.
We define a functor `t.ω₁ : ComposableArrows EInt 1 ⥤ C ⥤ C` which sends
a map `a ⟶ b` in `EInt` (i.e. `a ≤ b`) to the functor
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`. (Roughly speaking, we "keep" the
`t`-homology only in degree `n` such that `a ≤ n < b`.)
When we have two composable morphisms `f : a ⟶ b` and `g : b ⟶ c` in `EInt`,
we define a connecting homomorphism
`ω₁δ : t.ω₁.obj (mk₁ g) ⟶ t.ω₁.obj (mk₁ f) ⋙ shiftFunctor C (1 : ℤ)`, and
this gives distinguished triangles that are functorial both in `X : C`
and `a ⟶ b ⟶ c` in `ComposableArrows EInt 2`.

In other words, for each `X : C`, we define a spectral
object `t.spectralObject X : SpectralObject C EInt` in the
triangulated category `C`, and this extends to a functor
`t.spectralObjectFunctor : C ⥤ SpectralObject C EInt`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated ZeroObject Preadditive ComposableArrows

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C Int]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

set_option backward.defeqAttrib.useBackward true in
/-- Given a t-structure `t` on a triangulated category `C`, this is the functor
`ComposableArrows EInt 1 ⥤ C ⥤ C` which sends an arrows `a ⟶ b` in `EInt`
to the functor `t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`. -/
@[simps]
/--
Definition of `ω₁` / `ω₁` 的定义

English:
definition ω₁
  signature: : ComposableArrows EInt 1 ⥤ C ⥤ C where
  body: t.eTruncLT.obj (D.obj 1) ⋙ t.eTruncGE.obj (D.obj 0)
  map φ := t.eTruncLT.map (φ.app 1) ◫ t.eTruncGE.map (φ.app 0)

中文:
定义 ω₁
  签名: : ComposableArrows E整数 1 ⥤ C ⥤ C where
  定义体: t.eTruncLT.obj (D.obj 1) ⋙ t.eTruncGE.obj (D.obj 0)
  map φ := t.eTruncLT.map (φ.app 1) ◫ t.eTruncGE.map (φ.app 0)

Depends on / 依赖: D.obj, eTruncGE, eTruncLT, t.eTruncGE.obj, t.eTruncLT.obj
-/
noncomputable def ω₁ : ComposableArrows EInt 1 ⥤ C ⥤ C where
  obj D := t.eTruncLT.obj (D.obj 1) ⋙ t.eTruncGE.obj (D.obj 0)
  map φ := t.eTruncLT.map (φ.app 1) ◫ t.eTruncGE.map (φ.app 0)

variable [IsTriangulated C]

section

variable (a b c : EInt) (hab : a <= b) (hbc : b <= c)

open CategoryTheory.Functor in
/-- The connecting homomorphism (as a natural transformation) for the spectral
objects attached to the objects of a triangulated equipped with a t-structure. -/
@[simps!]
/--
Definition of `ω₁δ` / `ω₁δ` 的定义

English:
definition ω₁δ
  signature: :
  body: whiskerLeft _ (t.eTruncGEToGEGE a b) ≫ (associator _ _ _).inv ≫
    (t.ω₁.obj (mk₁ (homOfLE (hab.trans hbc)))).whiskerLeft (t.eTruncGEδLT.app b) ≫
      (associator _ _ _).inv ≫
        whiskerRight ((associator _ _ _).hom ≫ whiskerLeft _ (t.eTruncLTGEIsoGELT a b).hom ≫
          (associator _ _ _).inv ≫ whiskerRight (t.eTruncLTLTToLT c b) _) _

中文:
定义 ω₁δ
  签名: :
  定义体: whiskerLeft _ (t.eTruncGEToGEGE a b) ≫ (associator _ _ _).inv ≫
    (t.ω₁.obj (mk₁ (homOfLE (hab.trans hbc)))).whiskerLeft (t.eTruncGEδLT.app b) ≫
      (associator _ _ _).inv ≫
        whiskerRight ((associator _ _ _).hom ≫ whiskerLeft _ (t.eTruncLTGEIsoGELT a b).hom ≫
          (associator _ _ _).inv ≫ whiskerRight (t.eTruncLTLTToLT c b) _) _

Depends on / 依赖: LT.app, associator, eTruncGEToGEGE, eTruncLTGEIsoGELT, eTruncLTLTToLT, hab.trans, homOfLE, t.eTruncGE, t.eTruncGEToGEGE, t.eTruncLTGEIsoGELT, t.eTruncLTLTToLT, whiskerLeft, whiskerRight
-/
noncomputable def ω₁δ :
    t.ω₁.obj (mk₁ (homOfLE hbc)) ⟶ t.ω₁.obj (mk₁ (homOfLE hab)) ⋙ shiftFunctor C (1 : Int) :=
  whiskerLeft _ (t.eTruncGEToGEGE a b) ≫ (associator _ _ _).inv ≫
    (t.ω₁.obj (mk₁ (homOfLE (hab.trans hbc)))).whiskerLeft (t.eTruncGEδLT.app b) ≫
      (associator _ _ _).inv ≫
        whiskerRight ((associator _ _ _).hom ≫ whiskerLeft _ (t.eTruncLTGEIsoGELT a b).hom ≫
          (associator _ _ _).inv ≫ whiskerRight (t.eTruncLTLTToLT c b) _) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ω₁δ_naturality` / 引理 `ω₁δ_naturality`

English:
lemma ω₁δ_naturality
  statement: (a' b' c' : EInt) (hab' : a' <= b') (hbc' : b' <= c')
  proof: by
  ext
  dsimp
  simp only [ω₁δ_app, ← Functor.map_comp, NatTrans.naturality_assoc, Functor.comp_map,
    Category.assoc, ← Functor.map_comp_assoc, NatTrans.naturality_app_assoc,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app, NatTrans.naturality]
  congr 2
  simp only [Functor.map_comp, Category.assoc]
  have h₁ := t.eTruncLTGEIsoGELT_naturality_app a b hab a' b' hab' (homMk₁ (φ.app 0) (φ.app 1))
  rw [← reassoc_of% dsimp% h₁]; rw [← eTruncLTGEIsoGELT_hom_naturality]; rw [← eTruncLTGEIsoGELT_hom_naturality]; rw [← t.eTruncLT_map_app_eTruncLTι_app (φ.app 2)]
  simp only [↓NatTrans.naturality_assoc, ↓← Functor.map_comp_assoc]
  simp

中文:
引理 ω₁δ_naturality
  结论: (a' b' c' : E整数) (hab' : a' <= b') (hbc' : b' <= c')
  证明: by
  ext
  dsimp
  simp only [ω₁δ_app, ← Functor.map_comp, NatTrans.naturality_assoc, Functor.comp_map,
    Category.assoc, ← Functor.map_comp_assoc, NatTrans.naturality_app_assoc,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app, NatTrans.naturality]
  congr 2
  simp only [Functor.map_comp, Category.assoc]
  have h₁ := t.eTruncLTGEIsoGELT_naturality_app a b hab a' b' hab' (homMk₁ (φ.app 0) (φ.app 1))
  rw [← reassoc_of% dsimp% h₁]; rw [← eTruncLTGEIsoGELT_hom_naturality]; rw [← eTruncLTGEIsoGELT_hom_naturality]; rw [← t.eTruncLT_map_app_eTruncLTι_app (φ.app 2)]
  simp only [↓NatTrans.naturality_assoc, ↓← Functor.map_comp_assoc]
  simp

Depends on / 依赖: Category, Category.assoc, Functor, Functor.comp_map, Functor.map_comp, Functor.map_comp_assoc, Functor.whiskerRight_app, Functor.whiskeringRight_obj_map, NatTrans, NatTrans.naturality, NatTrans.naturality_app_assoc, NatTrans.naturality_assoc, comp_map, eTruncLTGEIsoGELT_hom_nat, eTruncLTGEIsoGELT_hom_naturality, eTruncLTGEIsoGELT_naturality_app, map_comp, map_comp_assoc, naturality, naturality_app_assoc
-/
lemma ω₁δ_naturality (a' b' c' : EInt) (hab' : a' <= b') (hbc' : b' <= c')
    (φ : mk₂ (homOfLE hab) (homOfLE hbc) ⟶ mk₂ (homOfLE hab') (homOfLE hbc')) :
    t.ω₁.map (homMk₁ (φ.app 1) (φ.app 2)) ≫ t.ω₁δ a' b' c' hab' hbc' =
      t.ω₁δ a b c hab hbc ≫ Functor.whiskerRight (t.ω₁.map (homMk₁ (φ.app 0) (φ.app 1))) _ := by
  ext
  dsimp
  simp only [ω₁δ_app, ← Functor.map_comp, NatTrans.naturality_assoc, Functor.comp_map,
    Category.assoc, ← Functor.map_comp_assoc, NatTrans.naturality_app_assoc,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app, NatTrans.naturality]
  congr 2
  simp only [Functor.map_comp, Category.assoc]
  have h₁ := t.eTruncLTGEIsoGELT_naturality_app a b hab a' b' hab' (homMk₁ (φ.app 0) (φ.app 1))
  rw [← reassoc_of% dsimp% h₁]; rw [← eTruncLTGEIsoGELT_hom_naturality]; rw [← eTruncLTGEIsoGELT_hom_naturality]; rw [← t.eTruncLT_map_app_eTruncLTι_app (φ.app 2)]
  simp only [↓NatTrans.naturality_assoc, ↓← Functor.map_comp_assoc]
  simp

/-- The functorial (distinguished) triangles that are part of the spectral
object attached to objects in a triangulated category equipped with a t-structure. -/
@[simps!]
/--
Definition of `triangleω₁δ` / `triangleω₁δ` 的定义

English:
definition triangleω₁δ
  signature: : C ⥤ Triangle C
  body: Triangle.functorMk (t.ω₁.map (twoδ₂Toδ₁' a b c hab hbc))
    (t.ω₁.map (twoδ₁Toδ₀' a b c hab hbc)) (t.ω₁δ a b c hab hbc)

中文:
定义 triangleω₁δ
  签名: : C ⥤ Triangle C
  定义体: Triangle.functorMk (t.ω₁.map (twoδ₂Toδ₁' a b c hab hbc))
    (t.ω₁.map (twoδ₁Toδ₀' a b c hab hbc)) (t.ω₁δ a b c hab hbc)

Depends on / 依赖: Triangle, Triangle.functorMk, functorMk
-/
noncomputable def triangleω₁δ : C ⥤ Triangle C :=
  Triangle.functorMk (t.ω₁.map (twoδ₂Toδ₁' a b c hab hbc))
    (t.ω₁.map (twoδ₁Toδ₀' a b c hab hbc)) (t.ω₁δ a b c hab hbc)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `triangleω₁δObjIso` / `triangleω₁δObjIso` 的定义

English:
definition triangleω₁δObjIso
  signature: (X : C)
  body: by
  refine Triangle.isoMk _ _ ((t.eTruncGE.obj a).mapIso ((t.eTruncLTLTIsoLT c b hbc).symm.app X) ≪≫
    (t.eTruncLTGEIsoGELT a b).symm.app _) (Iso.refl _) ((t.eTruncGEIsoGEGE a b hab).app _) ?_ ?_ ?_
  · dsimp
    simp only [triangleω₁δ_obj_mor₁, homOfLE_leOfHom, Category.comp_id, Category.assoc]
    rw [← cancel_epi ((t.eTruncGE.obj a).map ((t.eTruncLTLTIsoLT c b hbc).hom.app X))]; rw [← Functor.map_comp_assoc]; rw [Iso.hom_inv_id_app]; rw [Functor.map_id]; rw [Category.id_comp]; rw [← cancel_epi ((t.eTruncLTGEIsoGELT a b).hom.app ((t.eTruncLT.obj c).obj X))]; rw [Iso.hom_inv_id_app_assoc]; rw [eTruncLTLTIsoLT_hom]; rw [eTruncLTLTToLT_app]; rw [← Functor.map_comp]; rw [eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app]
    simp
  · dsimp
    simp only [triangleω₁δ_obj_mor₂, eTruncGEToGEGE_app, Category.id_comp,
      ← t.eTruncGEπ_app_eTruncGE_map_app (homOfLE hab), ← NatTrans.naturality,
      eTruncGE_obj_map_eTruncGEπ_app]
  · simp [← Functor.map_comp_assoc, ← Functor.map_comp]

中文:
定义 triangleω₁δObjIso
  签名: (X : C)
  定义体: by
  refine Triangle.isoMk _ _ ((t.eTruncGE.obj a).mapIso ((t.eTruncLTLTIsoLT c b hbc).symm.app X) ≪≫
    (t.eTruncLTGEIsoGELT a b).symm.app _) (Iso.refl _) ((t.eTruncGEIsoGEGE a b hab).app _) ?_ ?_ ?_
  · dsimp
    simp only [triangleω₁δ_obj_mor₁, homOfLE_leOfHom, Category.comp_id, Category.assoc]
    rw [← cancel_epi ((t.eTruncGE.obj a).map ((t.eTruncLTLTIsoLT c b hbc).hom.app X))]; rw [← Functor.map_comp_assoc]; rw [Iso.hom_inv_id_app]; rw [Functor.map_id]; rw [Category.id_comp]; rw [← cancel_epi ((t.eTruncLTGEIsoGELT a b).hom.app ((t.eTruncLT.obj c).obj X))]; rw [Iso.hom_inv_id_app_assoc]; rw [eTruncLTLTIsoLT_hom]; rw [eTruncLTLTToLT_app]; rw [← Functor.map_comp]; rw [eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app]
    simp
  · dsimp
    simp only [triangleω₁δ_obj_mor₂, eTruncGEToGEGE_app, Category.id_comp,
      ← t.eTruncGEπ_app_eTruncGE_map_app (homOfLE hab), ← NatTrans.naturality,
      eTruncGE_obj_map_eTruncGEπ_app]
  · simp [← Functor.map_comp_assoc, ← Functor.map_comp]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, Functor, Functor.map_comp_assoc, Functor.map_id, Iso.hom_inv_id_app, Iso.refl, Triangle, Triangle.isoMk, cancel_epi, comp_id, eTruncGE, eTruncGEIsoGEGE, eTruncL, eTruncLTGEIsoGELT, eTruncLTLTIsoLT, hom.app, homOfLE_leOfHom
-/
noncomputable def triangleω₁δObjIso (X : C) :
    (t.triangleω₁δ a b c hab hbc).obj X ≅
      (t.eTriangleLTGE.obj b).obj ((t.ω₁.obj (mk₁ (homOfLE (hab.trans hbc)))).obj X) := by
  refine Triangle.isoMk _ _ ((t.eTruncGE.obj a).mapIso ((t.eTruncLTLTIsoLT c b hbc).symm.app X) ≪≫
    (t.eTruncLTGEIsoGELT a b).symm.app _) (Iso.refl _) ((t.eTruncGEIsoGEGE a b hab).app _) ?_ ?_ ?_
  · dsimp
    simp only [triangleω₁δ_obj_mor₁, homOfLE_leOfHom, Category.comp_id, Category.assoc]
    rw [← cancel_epi ((t.eTruncGE.obj a).map ((t.eTruncLTLTIsoLT c b hbc).hom.app X))]; rw [← Functor.map_comp_assoc]; rw [Iso.hom_inv_id_app]; rw [Functor.map_id]; rw [Category.id_comp]; rw [← cancel_epi ((t.eTruncLTGEIsoGELT a b).hom.app ((t.eTruncLT.obj c).obj X))]; rw [Iso.hom_inv_id_app_assoc]; rw [eTruncLTLTIsoLT_hom]; rw [eTruncLTLTToLT_app]; rw [← Functor.map_comp]; rw [eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app]
    simp
  · dsimp
    simp only [triangleω₁δ_obj_mor₂, eTruncGEToGEGE_app, Category.id_comp,
      ← t.eTruncGEπ_app_eTruncGE_map_app (homOfLE hab), ← NatTrans.naturality,
      eTruncGE_obj_map_eTruncGEπ_app]
  · simp [← Functor.map_comp_assoc, ← Functor.map_comp]

/--
lemma `triangleω₁δ_distinguished` / 引理 `triangleω₁δ_distinguished`

English:
lemma triangleω₁δ_distinguished
  given: (X : C)
  statement: (t.triangleω₁δ a b c hab hbc).obj X in distTriang _
  proof: isomorphic_distinguished _ (t.eTriangleLTGE_distinguished b _) _
    (t.triangleω₁δObjIso a b c hab hbc X)

中文:
引理 triangleω₁δ_distinguished
  条件: (X : C)
  结论: (t.triangleω₁δ a b c hab hbc).obj X in distTriang _
  证明: isomorphic_distinguished _ (t.eTriangleLTGE_distinguished b _) _
    (t.triangleω₁δObjIso a b c hab hbc X)

Depends on / 依赖: eTriangleLTGE_distinguished, isomorphic_distinguished, t.eTriangleLTGE_distinguished, t.triangle
-/
lemma triangleω₁δ_distinguished (X : C) : (t.triangleω₁δ a b c hab hbc).obj X in distTriang _ :=
  isomorphic_distinguished _ (t.eTriangleLTGE_distinguished b _) _
    (t.triangleω₁δObjIso a b c hab hbc X)

end

/-- The spectral object attached to an object `X : C` in a category
equipped with a t-structure. It consists of all truncations of `X`. -/
@[simps ω₁]
/--
Definition of `spectralObject` / `spectralObject` 的定义

English:
definition spectralObject
  signature: (X : C)
  body: t.ω₁ ⋙ (evaluation _ _).obj X
  δ'.app D := (t.ω₁δ (D.obj 0) (D.obj 1) (D.obj 2)
    (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))).app X
  δ'.naturality {D D'} φ := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    obtain ⟨a', b', c', f', g', rfl⟩ := mk₂_surjective D'
    exact NatTrans.congr_app (t.ω₁δ_naturality a b c (leOfHom f) (leOfHom g)
      a' b' c' (leOfHom f') (leOfHom g') φ) X
  distinguished' D := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    exact t.triangleω₁δ_distinguished a b c (leOfHom f) (leOfHom g) X

@[simp]

中文:
定义 spectralObject
  签名: (X : C)
  定义体: t.ω₁ ⋙ (evaluation _ _).obj X
  δ'.app D := (t.ω₁δ (D.obj 0) (D.obj 1) (D.obj 2)
    (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))).app X
  δ'.naturality {D D'} φ := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    obtain ⟨a', b', c', f', g', rfl⟩ := mk₂_surjective D'
    exact NatTrans.congr_app (t.ω₁δ_naturality a b c (leOfHom f) (leOfHom g)
      a' b' c' (leOfHom f') (leOfHom g') φ) X
  distinguished' D := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    exact t.triangleω₁δ_distinguished a b c (leOfHom f) (leOfHom g) X

@[simp]

Depends on / 依赖: evaluation
-/
noncomputable def spectralObject (X : C) : SpectralObject C EInt where
  ω₁ := t.ω₁ ⋙ (evaluation _ _).obj X
  δ'.app D := (t.ω₁δ (D.obj 0) (D.obj 1) (D.obj 2)
    (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))).app X
  δ'.naturality {D D'} φ := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    obtain ⟨a', b', c', f', g', rfl⟩ := mk₂_surjective D'
    exact NatTrans.congr_app (t.ω₁δ_naturality a b c (leOfHom f) (leOfHom g)
      a' b' c' (leOfHom f') (leOfHom g') φ) X
  distinguished' D := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    exact t.triangleω₁δ_distinguished a b c (leOfHom f) (leOfHom g) X

@[simp]
/--
lemma `spectralObject_δ` / 引理 `spectralObject_δ`

English:
lemma spectralObject_δ
  given: (X : C) {a b c : EInt} (f : a ⟶ b) (g : b ⟶ c)
  proof: rfl

中文:
引理 spectralObject_δ
  条件: (X : C) {a b c : E整数} (f : a ⟶ b) (g : b ⟶ c)
  证明: rfl
-/
lemma spectralObject_δ (X : C) {a b c : EInt} (f : a ⟶ b) (g : b ⟶ c) :
    (t.spectralObject X).δ f g = (t.ω₁δ a b c (leOfHom f) (leOfHom g)).app X := rfl

/-- The spectral object attached to an object `X : C` in a category
equipped with a t-structure, as a functor `C ⥤ SpectralObject C EInt`. -/
@[simps]
/--
Definition of `spectralObjectFunctor` / `spectralObjectFunctor` 的定义

English:
definition spectralObjectFunctor
  signature: : C ⥤ SpectralObject C EInt where
  body: t.spectralObject
  map φ :=
    { hom := Functor.whiskerLeft _ ((evaluation _ _).map φ)
      comm f g := ((t.ω₁δ _ _ _ (leOfHom f) (leOfHom g)).naturality φ).symm }

中文:
定义 spectralObjectFunctor
  签名: : C ⥤ SpectralObject C E整数 where
  定义体: t.spectralObject
  map φ :=
    { hom := Functor.whiskerLeft _ ((evaluation _ _).map φ)
      comm f g := ((t.ω₁δ _ _ _ (leOfHom f) (leOfHom g)).naturality φ).symm }

Depends on / 依赖: spectralObject, t.spectralObject
-/
noncomputable def spectralObjectFunctor : C ⥤ SpectralObject C EInt where
  obj := t.spectralObject
  map φ :=
    { hom := Functor.whiskerLeft _ ((evaluation _ _).map φ)
      comm f g := ((t.ω₁δ _ _ _ (leOfHom f) (leOfHom g)).naturality φ).symm }

end TStructure

end Triangulated

end CategoryTheory
