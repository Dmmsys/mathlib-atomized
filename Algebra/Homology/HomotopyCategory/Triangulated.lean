/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-! # The triangulated structure on the homotopy category of complexes

In this file, we show that for any additive category `C`,
the pretriangulated category `HomotopyCategory C (ComplexShape.up ℤ)` is triangulated.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Pretriangulated ComposableArrows

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe v

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C Int} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

namespace CochainComplex

open HomComplex mappingCone

/-- Given two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in the category
of cochain complexes, this is the canonical triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`. -/
@[simps! mor₁ mor₂ mor₃ obj₁ obj₂ obj₃]
/--
Definition of `mappingConeCompTriangle` / `mappingConeCompTriangle` 的定义

English:
definition mappingConeCompTriangle
  signature: : Triangle (CochainComplex C Int)
  body: Triangle.mk (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp]))
    (map (f ≫ g) g f (𝟙 X₃) (by rw [comp_id]))
    ((triangle g).mor₃ ≫ (inr f)⟦1⟧')

中文:
定义 mappingConeCompTriangle
  签名: : Triangle (上链复形 C 整数)
  定义体: Triangle.mk (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp]))
    (map (f ≫ g) g f (𝟙 X₃) (by rw [comp_id]))
    ((triangle g).mor₃ ≫ (inr f)⟦1⟧')

Depends on / 依赖: Triangle, Triangle.mk, comp_id, id_comp, triangle
-/
noncomputable def mappingConeCompTriangle : Triangle (CochainComplex C Int) :=
  Triangle.mk (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp]))
    (map (f ≫ g) g f (𝟙 X₃) (by rw [comp_id]))
    ((triangle g).mor₃ ≫ (inr f)⟦1⟧')

/--
Definition of `mappingConeCompTriangleh` / `mappingConeCompTriangleh` 的定义

English:
definition mappingConeCompTriangleh
  signature: :
  body: (HomotopyCategory.quotient _ _).mapTriangle.obj (mappingConeCompTriangle f g)

中文:
定义 mappingConeCompTriangleh
  签名: :
  定义体: (HomotopyCategory.quotient _ _).mapTriangle.obj (mappingConeCompTriangle f g)

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quotient, mapTriangle, mapTriangle.obj, mappingConeCompTriangle, quotient
-/
noncomputable def mappingConeCompTriangleh :
    Triangle (HomotopyCategory C (ComplexShape.up Int)) :=
  (HomotopyCategory.quotient _ _).mapTriangle.obj (mappingConeCompTriangle f g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mappingConeCompTriangle_mor₃_naturality` / 引理 `mappingConeCompTriangle_mor₃_naturality`

English:
lemma mappingConeCompTriangle_mor₃_naturality
  statement: {Y₁ Y₂ Y₃ : CochainComplex C Int} (f' : Y₁ ⟶ Y₂)
  proof: by
  ext n
  dsimp [map]
  -- the following list of lemmas was obtained by doing simp? [ext_from_iff _ (n + 1) _ rfl]
  simp only [Int.reduceNeg, Fin.isValue, assoc, inr_f_desc_f, HomologicalComplex.comp_f,
    ext_from_iff _ (n + 1) _ rfl, inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v, Cochain.of

中文:
引理 mappingConeCompTriangle_mor₃_naturality
  结论: {Y₁ Y₂ Y₃ : 上链复形 C 整数} (f' : Y₁ ⟶ Y₂)
  证明: by
  ext n
  dsimp [map]
  -- the following list of lemmas was obtained by doing simp? [ext_from_iff _ (n + 1) _ rfl]
  simp only [Int.reduceNeg, Fin.isValue, assoc, inr_f_desc_f, HomologicalComplex.comp_f,
    ext_from_iff _ (n + 1) _ rfl, inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v, Cochain.of
-/
lemma mappingConeCompTriangle_mor₃_naturality {Y₁ Y₂ Y₃ : CochainComplex C Int} (f' : Y₁ ⟶ Y₂)
    (g' : Y₂ ⟶ Y₃) (φ : mk₂ f g ⟶ mk₂ f' g') :
    map g g' (φ.app 1) (φ.app 2) (naturality' φ 1 2) ≫ (mappingConeCompTriangle f' g').mor₃ =
      (mappingConeCompTriangle f g).mor₃ ≫
        (map f f' (φ.app 0) (φ.app 1) (naturality' φ 0 1))⟦1⟧' := by
  ext n
  dsimp [map]
  -- the following list of lemmas was obtained by doing simp? [ext_from_iff _ (n + 1) _ rfl]
  simp only [Int.reduceNeg, Fin.isValue, assoc, inr_f_desc_f, HomologicalComplex.comp_f,
    ext_from_iff _ (n + 1) _ rfl, inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    inl_v_triangle_mor₃_f_assoc, triangle_obj₁, shiftFunctor_obj_X', shiftFunctor_obj_X,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Preadditive.neg_comp,
    id_comp, Preadditive.comp_neg, inr_f_desc_f_assoc, inr_f_triangle_mor₃_f_assoc, zero_comp,
    comp_zero, and_self]

namespace MappingConeCompHomotopyEquiv

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: :
  body: lift _ (descCocycle g (Cochain.ofHom (inr f)) 0 (zero_add 1) (by simp))
    (descCochain _ 0 (Cochain.ofHom (inr (f ≫ g))) (neg_add_cancel 1)) (by
      ext p _ rfl
      dsimp [mappingConeCompTriangle, map]
      simp [ext_from_iff _ _ _ rfl, inl_v_d_assoc _ (p + 1) p (p + 2) (by lia) (by lia)])

中文:
定义 hom
  签名: :
  定义体: lift _ (descCocycle g (Cochain.ofHom (inr f)) 0 (zero_add 1) (by simp))
    (descCochain _ 0 (Cochain.ofHom (inr (f ≫ g))) (neg_add_cancel 1)) (by
      ext p _ rfl
      dsimp [mappingConeCompTriangle, map]
      simp [ext_from_iff _ _ _ rfl, inl_v_d_assoc _ (p + 1) p (p + 2) (by lia) (by lia)])

Depends on / 依赖: Cochain, Cochain.ofHom, descCochain, descCocycle, ext_from_iff, inl_v_d_assoc, mappingConeCompTriangle, neg_add_cancel, zero_add
-/
noncomputable def hom :
    mappingCone g ⟶ mappingCone (mappingConeCompTriangle f g).mor₁ :=
  lift _ (descCocycle g (Cochain.ofHom (inr f)) 0 (zero_add 1) (by simp))
    (descCochain _ 0 (Cochain.ofHom (inr (f ≫ g))) (neg_add_cancel 1)) (by
      ext p _ rfl
      dsimp [mappingConeCompTriangle, map]
      simp [ext_from_iff _ _ _ rfl, inl_v_d_assoc _ (p + 1) p (p + 2) (by lia) (by lia)])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : mappingCone (mappingConeCompTriangle f g).mor₁ ⟶ mappingCone g
  body: desc _ ((snd f).comp (inl g) (zero_add (-1)))
    (desc _ ((Cochain.ofHom f).comp (inl g) (zero_add (-1))) (inr g) (by simp)) (by
      ext p
      rw [ext_from_iff _ (p + 1) _ rfl]; rw [ext_to_iff _ _ (p + 1) rfl]
      simp [map, δ_zero_cochain_comp,
        Cochain.comp_v _ _ (add_neg_cancel 1) p

中文:
定义 inv
  签名: : mappingCone (mappingConeCompTriangle f g).mor₁ ⟶ mappingCone g
  定义体: desc _ ((snd f).comp (inl g) (zero_add (-1)))
    (desc _ ((Cochain.ofHom f).comp (inl g) (zero_add (-1))) (inr g) (by simp)) (by
      ext p
      rw [ext_from_iff _ (p + 1) _ rfl]; rw [ext_to_iff _ _ (p + 1) rfl]
      simp [map, δ_zero_cochain_comp,
        Cochain.comp_v _ _ (add_neg_cancel 1) p

Depends on / 依赖: Cochain, Cochain.comp_v, Cochain.ofHom, add_neg_cancel, comp_v, ext_from_iff, ext_to_iff, zero_add
-/
noncomputable def inv : mappingCone (mappingConeCompTriangle f g).mor₁ ⟶ mappingCone g :=
  desc _ ((snd f).comp (inl g) (zero_add (-1)))
    (desc _ ((Cochain.ofHom f).comp (inl g) (zero_add (-1))) (inr g) (by simp)) (by
      ext p
      rw [ext_from_iff _ (p + 1) _ rfl]; rw [ext_to_iff _ _ (p + 1) rfl]
      simp [map, δ_zero_cochain_comp,
        Cochain.comp_v _ _ (add_neg_cancel 1) p (p + 1) p (by lia) (by lia)])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `hom_inv_id` / 引理 `hom_inv_id`

English:
lemma hom_inv_id
  statement: hom f g ≫ inv f g = 𝟙 _
  proof: by
  ext n
  simp [hom, inv, lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

中文:
引理 hom_inv_id
  结论: hom f g ≫ inv f g = 𝟙 _
  证明: by
  ext n
  simp [hom, inv, lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

Depends on / 依赖: ext_from_iff, lift_desc_f
-/
lemma hom_inv_id : hom f g ≫ inv f g = 𝟙 _ := by
  ext n
  simp [hom, inv, lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homotopyInvHomId` / `homotopyInvHomId` 的定义

English:
definition homotopyInvHomId
  signature: : Homotopy (inv f g ≫ hom f g) (𝟙 _)
  body: (Cochain.equivHomotopy _ _).symm ⟨-((snd _).comp ((fst (f ≫ g)).1.comp
    ((inl f).comp (inl _) (by decide)) (show 1 + (-2) = -1 by decide)) (zero_add (-1))), by
      rw [δ_neg]; rw [δ_zero_cochain_comp _ _ _ (neg_add_cancel 1)]; rw [Int.negOnePow_neg]; rw [Int.negOnePow_one]; rw [Units.neg_smul];

中文:
定义 homotopyInvHomId
  签名: : 同伦 (inv f g ≫ hom f g) (𝟙 _)
  定义体: (Cochain.equivHomotopy _ _).symm ⟨-((snd _).comp ((fst (f ≫ g)).1.comp
    ((inl f).comp (inl _) (by decide)) (show 1 + (-2) = -1 by decide)) (zero_add (-1))), by
      rw [δ_neg]; rw [δ_zero_cochain_comp _ _ _ (neg_add_cancel 1)]; rw [Int.negOnePow_neg]; rw [Int.negOnePow_one]; rw [Units.neg_smul];

Depends on / 依赖: Cochain, Cochain.equivHomotopy, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, equivHomotopy, negOnePow_neg, negOnePow_one, neg_add_cancel, neg_smul, one_smul, zero_add
-/
noncomputable def homotopyInvHomId : Homotopy (inv f g ≫ hom f g) (𝟙 _) :=
  (Cochain.equivHomotopy _ _).symm ⟨-((snd _).comp ((fst (f ≫ g)).1.comp
    ((inl f).comp (inl _) (by decide)) (show 1 + (-2) = -1 by decide)) (zero_add (-1))), by
      rw [δ_neg]; rw [δ_zero_cochain_comp _ _ _ (neg_add_cancel 1)]; rw [Int.negOnePow_neg]; rw [Int.negOnePow_one]; rw [Units.neg_smul]; rw [one_smul]; rw [δ_comp _ _ (show 1 + (-2) = -1 by decide) 2 (-1) 0 (by decide)
          (by decide) (by decide)]; rw [δ_comp _ _ (show (-1) + (-1) = -2 by decide) 0 0 (-1) (by decide)
          (by decide) (by decide)]; rw [Int.negOnePow_neg]; rw [Int.negOnePow_neg]; rw [Int.negOnePow_even 2 ⟨1]; rw [by decide⟩]; rw [Int.negOnePow_one]; rw [Units.neg_smul]; rw [one_smul]; rw [one_smul]; rw [δ_inl]; rw [δ_inl]; rw [δ_snd]; rw [Cocycle.δ_eq_zero]; rw [Cochain.zero_comp]; rw [add_zero]; rw [Cochain.neg_comp]; rw [neg_neg]
      ext n
      rw [ext_from_iff _ (n + 1) n rfl]; rw [ext_from_iff _ (n + 1) n rfl]; rw [ext_from_iff _ (n + 2) (n + 1) (by lia)]
      dsimp [hom, inv]
      simp [ext_to_iff _ n (n + 1) rfl, map, Cochain.comp_v _ _
          (add_neg_cancel 1) n (n + 1) n (by lia) (by lia),
        Cochain.comp_v _ _ (show 1 + -2 = -1 by decide) (n + 1) (n + 2) n
          (by lia) (by lia),
        Cochain.comp_v _ _ (show (-1) + -1 = -2 by decide) (n + 2) (n + 1) n
          (by lia) (by lia)]⟩

end MappingConeCompHomotopyEquiv

/--
Definition of `mappingConeCompHomotopyEquiv` / `mappingConeCompHomotopyEquiv` 的定义

English:
definition mappingConeCompHomotopyEquiv
  signature: : HomotopyEquiv (mappingCone g)
  body: MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := MappingConeCompHomotopyEquiv.homotopyInvHomId f g

@[reassoc (attr := simp)]

中文:
定义 mappingConeCompHomotopyEquiv
  签名: : 同伦等价 (mappingCone g)
  定义体: MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := MappingConeCompHomotopyEquiv.homotopyInvHomId f g

@[reassoc (attr := simp)]

Depends on / 依赖: MappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom
-/
noncomputable def mappingConeCompHomotopyEquiv : HomotopyEquiv (mappingCone g)
    (mappingCone (mappingConeCompTriangle f g).mor₁) where
  hom := MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := MappingConeCompHomotopyEquiv.homotopyInvHomId f g

@[reassoc (attr := simp)]
/--
lemma `mappingConeCompHomotopyEquiv_hom_inv_id` / 引理 `mappingConeCompHomotopyEquiv_hom_inv_id`

English:
lemma mappingConeCompHomotopyEquiv_hom_inv_id
  proof: by
  simp [mappingConeCompHomotopyEquiv]

中文:
引理 mappingConeCompHomotopyEquiv_hom_inv_id
  证明: by
  simp [mappingConeCompHomotopyEquiv]

Depends on / 依赖: mappingConeCompHomotopyEquiv
-/
lemma mappingConeCompHomotopyEquiv_hom_inv_id :
    (mappingConeCompHomotopyEquiv f g).hom ≫
      (mappingConeCompHomotopyEquiv f g).inv = 𝟙 _ := by
  simp [mappingConeCompHomotopyEquiv]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `mappingConeCompHomotopyEquiv_comm₁` / 引理 `mappingConeCompHomotopyEquiv_comm₁`

English:
lemma mappingConeCompHomotopyEquiv_comm₁
  proof: by
  simp [map, mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv]

中文:
引理 mappingConeCompHomotopyEquiv_comm₁
  证明: by
  simp [map, mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv]

Depends on / 依赖: MappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv, mappingConeCompHomotopyEquiv
-/
lemma mappingConeCompHomotopyEquiv_comm₁ :
    inr (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp])) ≫
      (mappingConeCompHomotopyEquiv f g).inv = (mappingConeCompTriangle f g).mor₂ := by
  simp [map, mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mappingConeCompHomotopyEquiv_comm₂` / 引理 `mappingConeCompHomotopyEquiv_comm₂`

English:
lemma mappingConeCompHomotopyEquiv_comm₂
  proof: by
  ext n
  simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom,
    lift_f _ _ _ _ _ (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

中文:
引理 mappingConeCompHomotopyEquiv_comm₂
  证明: by
  ext n
  simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom,
    lift_f _ _ _ _ _ (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

Depends on / 依赖: IsIso.hom_inv_id, IsIso.inv_hom_id, IsIso.inv_hom_id_assoc, MappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom, _i_assoc, cancel_mono, comp_id, cyclesMap, ext_from_iff, hom_inv_id, id_comp, inv_hom_id, inv_hom_id_assoc, liftK_i, liftK_i_assoc, lift_f, mappingConeCompHomotopyEquiv, zero_comp
-/
lemma mappingConeCompHomotopyEquiv_comm₂ :
    (mappingConeCompHomotopyEquiv f g).hom ≫
      (triangle (mappingConeCompTriangle f g).mor₁).mor₃ =
      (mappingConeCompTriangle f g).mor₃ := by
  ext n
  simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom,
    lift_f _ _ _ _ _ (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `mappingConeCompTriangleh_comm₁` / 引理 `mappingConeCompTriangleh_comm₁`

English:
lemma mappingConeCompTriangleh_comm₁
  proof: by
  rw [← cancel_mono (HomotopyCategory.isoOfHomotopyEquiv
      (mappingConeCompHomotopyEquiv f g)).inv]; rw [assoc]
  dsimp [mappingConeCompTriangleh]
  rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [mappingConeCompHomotopyEquiv_hom_inv_id]; rw [comp_id]; rw [mappi

中文:
引理 mappingConeCompTriangleh_comm₁
  证明: by
  rw [← cancel_mono (HomotopyCategory.isoOfHomotopyEquiv
      (mappingConeCompHomotopyEquiv f g)).inv]; rw [assoc]
  dsimp [mappingConeCompTriangleh]
  rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [mappingConeCompHomotopyEquiv_hom_inv_id]; rw [comp_id]; rw [mappi

Depends on / 依赖: Functor, Functor.map_comp, HomotopyCategory, HomotopyCategory.isoOfHomotopyEquiv, cancel_mono, comp_id, isoOfHomotopyEquiv, map_comp, mappingConeCompHomotopyEquiv, mappingConeCompHomotopyEquiv_hom_inv_id, mappingConeCompTriangleh
-/
lemma mappingConeCompTriangleh_comm₁ :
    (mappingConeCompTriangleh f g).mor₂ ≫
      (HomotopyCategory.quotient _ _).map (mappingConeCompHomotopyEquiv f g).hom =
    (HomotopyCategory.quotient _ _).map (mappingCone.inr _) := by
  rw [← cancel_mono (HomotopyCategory.isoOfHomotopyEquiv
      (mappingConeCompHomotopyEquiv f g)).inv]; rw [assoc]
  dsimp [mappingConeCompTriangleh]
  rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [mappingConeCompHomotopyEquiv_hom_inv_id]; rw [comp_id]; rw [mappingConeCompHomotopyEquiv_comm₁ f g]; rw [mappingConeCompTriangle_mor₂]

end CochainComplex

namespace HomotopyCategory

open CochainComplex

variable [HasZeroObject C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `mappingConeCompTriangleh_distinguished` / 引理 `mappingConeCompTriangleh_distinguished`

English:
lemma mappingConeCompTriangleh_distinguished
  proof: by
  refine ⟨_, _, (mappingConeCompTriangle f g).mor₁, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (isoOfHomotopyEquiv
    (mappingConeCompHomotopyEquiv f g)) (by cat_disch) (by simp) ?_
  dsimp [mappingConeCompTriangleh]
  rw [CategoryTheory.Functor.map_id]; rw [comp_id]; rw [← Func

中文:
引理 mappingConeCompTriangleh_distinguished
  证明: by
  refine ⟨_, _, (mappingConeCompTriangle f g).mor₁, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (isoOfHomotopyEquiv
    (mappingConeCompHomotopyEquiv f g)) (by cat_disch) (by simp) ?_
  dsimp [mappingConeCompTriangleh]
  rw [CategoryTheory.Functor.map_id]; rw [comp_id]; rw [← Func

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, Functor.map_comp_assoc, Iso.refl, Triangle, Triangle.isoMk, cat_disch, comp_id, isoOfHomotopyEquiv, map_comp_assoc, map_id, mappingConeCompHomotopyEquiv, mappingConeCompTriangle, mappingConeCompTriangleh
-/
lemma mappingConeCompTriangleh_distinguished :
    (mappingConeCompTriangleh f g) in
      distTriang (HomotopyCategory C (ComplexShape.up Int)) := by
  refine ⟨_, _, (mappingConeCompTriangle f g).mor₁, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (isoOfHomotopyEquiv
    (mappingConeCompHomotopyEquiv f g)) (by cat_disch) (by simp) ?_
  dsimp [mappingConeCompTriangleh]
  rw [CategoryTheory.Functor.map_id]; rw [comp_id]; rw [← Functor.map_comp_assoc]
  congr 2
  exact (mappingConeCompHomotopyEquiv_comm₂ f g).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTriangulated (HomotopyCategory C (ComplexShape.up Int))
  body: IsTriangulated.mk' (by
    rintro ⟨X₁ : CochainComplex C Int⟩ ⟨X₂ : CochainComplex C Int⟩ ⟨X₃ : CochainComplex C Int⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up Int)).map_surjective u₁₂'
    obtain ⟨u₂₃, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up Int)

中文:
实例 :
  签名: 是三角 (HomotopyCategory C (余mplexShape.up 整数))
  定义体: IsTriangulated.mk' (by
    rintro ⟨X₁ : CochainComplex C Int⟩ ⟨X₂ : CochainComplex C Int⟩ ⟨X₃ : CochainComplex C Int⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up Int)).map_surjective u₁₂'
    obtain ⟨u₂₃, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up Int)

Depends on / 依赖: CochainComplex, ComplexShape, ComplexShape.up, HomotopyCategory, HomotopyCategory.quotient, IsTriangulated, IsTriangulated.mk, Iso.refl, map_surjective, mappingCone_triangleh_distinguished, quotient
-/
noncomputable instance : IsTriangulated (HomotopyCategory C (ComplexShape.up Int)) :=
  IsTriangulated.mk' (by
    rintro ⟨X₁ : CochainComplex C Int⟩ ⟨X₂ : CochainComplex C Int⟩ ⟨X₃ : CochainComplex C Int⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up Int)).map_surjective u₁₂'
    obtain ⟨u₂₃, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up Int)).map_surjective u₂₃'
    refine ⟨_, _, _, _, _, _, _, _, Iso.refl _, Iso.refl _, Iso.refl _, by simp, by simp,
        _, _, mappingCone_triangleh_distinguished u₁₂,
        _, _, mappingCone_triangleh_distinguished u₂₃,
        _, _, mappingCone_triangleh_distinguished (u₁₂ ≫ u₂₃), ⟨?_⟩⟩
    let α := mappingCone.triangleMap u₁₂ (u₁₂ ≫ u₂₃) (𝟙 X₁) u₂₃ (by rw [id_comp])
    let β := mappingCone.triangleMap (u₁₂ ≫ u₂₃) u₂₃ u₁₂ (𝟙 X₃) (by rw [comp_id])
    refine Triangulated.Octahedron.mk ((HomotopyCategory.quotient _ _).map α.hom₃)
      ((HomotopyCategory.quotient _ _).map β.hom₃) ?_ ?_ ?_ ?_ ?_
    · exact ((quotient _ _).mapTriangle.map α).comm₂
    · exact ((quotient _ _).mapTriangle.map α).comm₃.symm.trans (by dsimp [α]; simp)
    · exact ((quotient _ _).mapTriangle.map β).comm₂.trans (by dsimp [β]; simp)
    · exact ((quotient _ _).mapTriangle.map β).comm₃
    · refine isomorphic_distinguished _ (mappingConeCompTriangleh_distinguished u₁₂ u₂₃) _ ?_
      exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by dsimp [α, mappingConeCompTriangleh]; simp)
        (by dsimp [β, mappingConeCompTriangleh]; simp)
        (by dsimp [mappingConeCompTriangleh]; simp))

end HomotopyCategory
