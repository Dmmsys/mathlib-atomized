/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.Iso

/-!
# Conjugate morphisms by isomorphisms

We define
`CategoryTheory.Iso.homCongr : (X ≅ X₁) → (Y ≅ Y₁) → (X ⟶ Y) ≃ (X₁ ⟶ Y₁)`,
cf. `Equiv.arrowCongr`,
and `CategoryTheory.Iso.isoCongr : (f : X₁ ≅ X₂) → (g : Y₁ ≅ Y₂) → (X₁ ≅ Y₁) ≃ (X₂ ≅ Y₂)`.

As corollaries, an isomorphism `α : X ≅ Y` defines
- a monoid isomorphism
  `CategoryTheory.Iso.conj : End X ≃* End Y` by `α.conj f = α.inv ≫ f ≫ α.hom`;
- a group isomorphism `CategoryTheory.Iso.conjAut : Aut X ≃* Aut Y` by
  `α.conjAut f = α.symm ≪≫ f ≪≫ α`
  which can be found in `CategoryTheory.Conj`.
-/

@[expose] public section


set_option mathlib.tactic.category.grind true

universe v u

namespace CategoryTheory

namespace Iso

variable {C : Type u} [Category.{v} C]

/-- If `X` is isomorphic to `X₁` and `Y` is isomorphic to `Y₁`, then
there is a natural bijection between `X ⟶ Y` and `X₁ ⟶ Y₁`. See also `Equiv.arrowCongr`. -/
@[simps apply]
/--
Definition of `homCongr` / `homCongr` 的定义

English:
definition homCongr
  signature: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
  body: α.inv ≫ f ≫ β.hom
  invFun f := α.hom ≫ f ≫ β.inv
  left_inv f :=
    show α.hom ≫ (α.inv ≫ f ≫ β.hom) ≫ β.inv = f by
      rw [Category.assoc]; rw [Category.assoc]; rw [β.hom_inv_id]; rw [α.hom_inv_id_assoc]; rw [Category.comp_id]
  right_inv f :=
    show α.inv ≫ (α.hom ≫ f ≫ β.inv) ≫ β.hom = f by
      rw [Category.assoc]; rw [Category.assoc]; rw [β.inv_hom_id]; rw [α.inv_hom_id_assoc]; rw [Category.comp_id]

中文:
定义 homCongr
  签名: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
  定义体: α.inv ≫ f ≫ β.hom
  invFun f := α.hom ≫ f ≫ β.inv
  left_inv f :=
    show α.hom ≫ (α.inv ≫ f ≫ β.hom) ≫ β.inv = f by
      rw [Category.assoc]; rw [Category.assoc]; rw [β.hom_inv_id]; rw [α.hom_inv_id_assoc]; rw [Category.comp_id]
  right_inv f :=
    show α.inv ≫ (α.hom ≫ f ≫ β.inv) ≫ β.hom = f by
      rw [Category.assoc]; rw [Category.assoc]; rw [β.inv_hom_id]; rw [α.inv_hom_id_assoc]; rw [Category.comp_id]
-/
def homCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) : (X ⟶ Y) ≃ (X₁ ⟶ Y₁) where
  toFun f := α.inv ≫ f ≫ β.hom
  invFun f := α.hom ≫ f ≫ β.inv
  left_inv f :=
    show α.hom ≫ (α.inv ≫ f ≫ β.hom) ≫ β.inv = f by
      rw [Category.assoc]; rw [Category.assoc]; rw [β.hom_inv_id]; rw [α.hom_inv_id_assoc]; rw [Category.comp_id]
  right_inv f :=
    show α.inv ≫ (α.hom ≫ f ≫ β.inv) ≫ β.hom = f by
      rw [Category.assoc]; rw [Category.assoc]; rw [β.inv_hom_id]; rw [α.inv_hom_id_assoc]; rw [Category.comp_id]

/--
theorem `homCongr_comp` / 定理 `homCongr_comp`

English:
theorem homCongr_comp
  statement: {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁) (f : X ⟶ Y)
  proof: by simp

中文:
定理 homCongr_comp
  结论: {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁) (f : X ⟶ Y)
  证明: by simp
-/
theorem homCongr_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁) (f : X ⟶ Y)
    (g : Y ⟶ Z) : α.homCongr γ (f ≫ g) = α.homCongr β f ≫ β.homCongr γ g := by simp

/--
theorem `homCongr_refl` / 定理 `homCongr_refl`

English:
theorem homCongr_refl
  given: {X Y : C} (f : X ⟶ Y)
  statement: (Iso.refl X).homCongr (Iso.refl Y) f = f
  proof: by simp

中文:
定理 homCongr_refl
  条件: {X Y : C} (f : X ⟶ Y)
  结论: (同构.refl X).homCongr (同构.refl Y) f = f
  证明: by simp
-/
theorem homCongr_refl {X Y : C} (f : X ⟶ Y) : (Iso.refl X).homCongr (Iso.refl Y) f = f := by simp

/--
theorem `homCongr_trans` / 定理 `homCongr_trans`

English:
theorem homCongr_trans
  statement: {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂) (α₂ : X₂ ≅ X₃)
  proof: by simp

@[simp]

中文:
定理 homCongr_trans
  结论: {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂) (α₂ : X₂ ≅ X₃)
  证明: by simp

@[simp]
-/
theorem homCongr_trans {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂) (α₂ : X₂ ≅ X₃)
    (β₂ : Y₂ ≅ Y₃) (f : X₁ ⟶ Y₁) :
    (α₁ ≪≫ α₂).homCongr (β₁ ≪≫ β₂) f = (α₁.homCongr β₁).trans (α₂.homCongr β₂) f := by simp

@[simp]
/--
theorem `homCongr_symm` / 定理 `homCongr_symm`

English:
theorem homCongr_symm
  given: {X₁ Y₁ X₂ Y₂ : C} (α : X₁ ≅ X₂) (β : Y₁ ≅ Y₂)
  proof: rfl

中文:
定理 homCongr_symm
  条件: {X₁ Y₁ X₂ Y₂ : C} (α : X₁ ≅ X₂) (β : Y₁ ≅ Y₂)
  证明: rfl
-/
theorem homCongr_symm {X₁ Y₁ X₂ Y₂ : C} (α : X₁ ≅ X₂) (β : Y₁ ≅ Y₂) :
    (α.homCongr β).symm = α.symm.homCongr β.symm :=
  rfl

attribute [grind _=_] Iso.trans_assoc
attribute [grind =] Iso.symm_self_id Iso.self_symm_id Iso.refl_trans Iso.trans_refl

attribute [local grind =] Function.LeftInverse Function.RightInverse in
/-- If `X` is isomorphic to `X₁` and `Y` is isomorphic to `Y₁`, then
there is a bijection between `X ≅ Y` and `X₁ ≅ Y₁`. -/
@[simps]
/--
Definition of `isoCongr` / `isoCongr` 的定义

English:
definition isoCongr
  signature: {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ≅ X₂) (g : Y₁ ≅ Y₂)
  body: f.symm.trans h.trans g
invFun h := f.trans h.trans g.symm
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 isoCongr
  签名: {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ≅ X₂) (g : Y₁ ≅ Y₂)
  定义体: f.symm.trans h.trans g
invFun h := f.trans h.trans g.symm
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: f.symm.trans, h.trans
-/
def isoCongr {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ≅ X₂) (g : Y₁ ≅ Y₂) : (X₁ ≅ Y₁) ≃ (X₂ ≅ Y₂) where
toFun h := f.symm.trans h.trans g
invFun h := f.trans h.trans g.symm
  left_inv := by cat_disch
  right_inv := by cat_disch

/--
Definition of `isoCongrLeft` / `isoCongrLeft` 的定义

English:
definition isoCongrLeft
  signature: {X₁ X₂ Y : C} (f : X₁ ≅ X₂)
  body: isoCongr f (Iso.refl _)

中文:
定义 isoCongrLeft
  签名: {X₁ X₂ Y : C} (f : X₁ ≅ X₂)
  定义体: isoCongr f (Iso.refl _)

Depends on / 依赖: Iso.refl, isoCongr
-/
def isoCongrLeft {X₁ X₂ Y : C} (f : X₁ ≅ X₂) : (X₁ ≅ Y) ≃ (X₂ ≅ Y) :=
  isoCongr f (Iso.refl _)

/--
Definition of `isoCongrRight` / `isoCongrRight` 的定义

English:
definition isoCongrRight
  signature: {X Y₁ Y₂ : C} (g : Y₁ ≅ Y₂)
  body: isoCongr (Iso.refl _) g

中文:
定义 isoCongrRight
  签名: {X Y₁ Y₂ : C} (g : Y₁ ≅ Y₂)
  定义体: isoCongr (Iso.refl _) g

Depends on / 依赖: Iso.refl, isoCongr
-/
def isoCongrRight {X Y₁ Y₂ : C} (g : Y₁ ≅ Y₂) : (X ≅ Y₁) ≃ (X ≅ Y₂) :=
  isoCongr (Iso.refl _) g

end Iso

namespace Functor

universe v₁ u₁

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D)

/--
theorem `map_homCongr` / 定理 `map_homCongr`

English:
theorem map_homCongr
  given: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y)
  proof: by simp

中文:
定理 map_homCongr
  条件: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y)
  证明: by simp

Depends on / 依赖: Set.initialSegIic, hasIterationOfShape_of_initialSeg, initialSegIic
-/
theorem map_homCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y) :
    F.map (Iso.homCongr α β f) = Iso.homCongr (F.mapIso α) (F.mapIso β) (F.map f) := by simp

/--
theorem `map_isoCongr` / 定理 `map_isoCongr`

English:
theorem map_isoCongr
  given: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ≅ Y)
  proof: by
  simp

中文:
定理 map_isoCongr
  条件: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ≅ Y)
  证明: by
  simp
-/
theorem map_isoCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ≅ Y) :
    F.mapIso (Iso.isoCongr α β f) = Iso.isoCongr (F.mapIso α) (F.mapIso β) (F.mapIso f) := by
  simp

end Functor

end CategoryTheory
