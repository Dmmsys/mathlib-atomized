/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.HomCongr

/-!
# Conjugate morphisms by isomorphisms

An isomorphism `α : X ≅ Y` defines
- a monoid isomorphism
  `CategoryTheory.Iso.conj : End X ≃* End Y` by `α.conj f = α.inv ≫ f ≫ α.hom`;
- a group isomorphism `CategoryTheory.Iso.conjAut : Aut X ≃* Aut Y` by
  `α.conjAut f = α.symm ≪≫ f ≪≫ α`
  using
  `CategoryTheory.Iso.homCongr : (X ≅ X₁) → (Y ≅ Y₁) → (X ⟶ Y) ≃ (X₁ ⟶ Y₁)`
  and `CategoryTheory.Iso.isoCongr : (f : X₁ ≅ X₂) → (g : Y₁ ≅ Y₂) → (X₁ ≅ Y₁) ≃ (X₂ ≅ Y₂)`
  which are defined in `CategoryTheory.HomCongr`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace Iso

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (α : X ≅ Y)

/--
Definition of `conj` / `conj` 的定义

English:
definition conj
  signature: : End X ≃* End Y
  body: { homCongr α α with map_mul' := fun f g => homCongr_comp α α α g f }

中文:
定义 conj
  签名: : End X ≃* End Y
  定义体: { homCongr α α with map_mul' := fun f g => homCongr_comp α α α g f }

Depends on / 依赖: homCongr, homCongr_comp, map_mul
-/
def conj : End X ≃* End Y :=
  { homCongr α α with map_mul' := fun f g => homCongr_comp α α α g f }

/--
theorem `conj_apply` / 定理 `conj_apply`

English:
theorem conj_apply
  given: (f : End X)
  statement: α.conj f = α.inv ≫ f ≫ α.hom
  proof: rfl

@[simp]

中文:
定理 conj_apply
  条件: (f : End X)
  结论: α.conj f = α.inv ≫ f ≫ α.hom
  证明: rfl

@[simp]
-/
theorem conj_apply (f : End X) : α.conj f = α.inv ≫ f ≫ α.hom :=
  rfl

@[simp]
/--
theorem `conj_comp` / 定理 `conj_comp`

English:
theorem conj_comp
  given: (f g : End X)
  statement: α.conj (f ≫ g) = α.conj f ≫ α.conj g
  proof: map_mul α.conj g f

@[simp]

中文:
定理 conj_comp
  条件: (f g : End X)
  结论: α.conj (f ≫ g) = α.conj f ≫ α.conj g
  证明: map_mul α.conj g f

@[simp]

Depends on / 依赖: map_mul
-/
theorem conj_comp (f g : End X) : α.conj (f ≫ g) = α.conj f ≫ α.conj g :=
  map_mul α.conj g f

@[simp]
/--
theorem `conj_id` / 定理 `conj_id`

English:
theorem conj_id
  statement: α.conj (𝟙 X) = 𝟙 Y
  proof: map_one α.conj

中文:
定理 conj_id
  结论: α.conj (𝟙 X) = 𝟙 Y
  证明: map_one α.conj

Depends on / 依赖: map_one
-/
theorem conj_id : α.conj (𝟙 X) = 𝟙 Y :=
  map_one α.conj

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `refl_conj` / 定理 `refl_conj`

English:
theorem refl_conj
  given: (f : End X)
  statement: (Iso.refl X).conj f = f
  proof: by
  rw [conj_apply]; rw [Iso.refl_inv]; rw [Iso.refl_hom]; rw [Category.id_comp]; rw [Category.comp_id]

@[simp]

中文:
定理 refl_conj
  条件: (f : End X)
  结论: (Iso.refl X).conj f = f
  证明: by
  rw [conj_apply]; rw [Iso.refl_inv]; rw [Iso.refl_hom]; rw [Category.id_comp]; rw [Category.comp_id]

@[simp]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Iso.refl_hom, Iso.refl_inv, comp_id, conj_apply, id_comp, refl_hom, refl_inv
-/
theorem refl_conj (f : End X) : (Iso.refl X).conj f = f := by
  rw [conj_apply]; rw [Iso.refl_inv]; rw [Iso.refl_hom]; rw [Category.id_comp]; rw [Category.comp_id]

@[simp]
/--
theorem `trans_conj` / 定理 `trans_conj`

English:
theorem trans_conj
  given: {Z : C} (β : Y ≅ Z) (f : End X)
  statement: (α ≪≫ β).conj f = β.conj (α.conj f)
  proof: homCongr_trans α α β β f

@[simp]

中文:
定理 trans_conj
  条件: {Z : C} (β : Y ≅ Z) (f : End X)
  结论: (α ≪≫ β).conj f = β.conj (α.conj f)
  证明: homCongr_trans α α β β f

@[simp]

Depends on / 依赖: homCongr_trans
-/
theorem trans_conj {Z : C} (β : Y ≅ Z) (f : End X) : (α ≪≫ β).conj f = β.conj (α.conj f) :=
  homCongr_trans α α β β f

@[simp]
/--
theorem `symm_self_conj` / 定理 `symm_self_conj`

English:
theorem symm_self_conj
  given: (f : End X)
  statement: α.symm.conj (α.conj f) = f
  proof: by
  rw [← trans_conj]; rw [α.self_symm_id]; rw [refl_conj]

@[simp]

中文:
定理 symm_self_conj
  条件: (f : End X)
  结论: α.symm.conj (α.conj f) = f
  证明: by
  rw [← trans_conj]; rw [α.self_symm_id]; rw [refl_conj]

@[simp]

Depends on / 依赖: refl_conj, self_symm_id, trans_conj
-/
theorem symm_self_conj (f : End X) : α.symm.conj (α.conj f) = f := by
  rw [← trans_conj]; rw [α.self_symm_id]; rw [refl_conj]

@[simp]
/--
theorem `self_symm_conj` / 定理 `self_symm_conj`

English:
theorem self_symm_conj
  given: (f : End Y)
  statement: α.conj (α.symm.conj f) = f
  proof: α.symm.symm_self_conj f

@[simp]

中文:
定理 self_symm_conj
  条件: (f : End Y)
  结论: α.conj (α.symm.conj f) = f
  证明: α.symm.symm_self_conj f

@[simp]

Depends on / 依赖: symm.symm_self_conj, symm_self_conj
-/
theorem self_symm_conj (f : End Y) : α.conj (α.symm.conj f) = f :=
  α.symm.symm_self_conj f

@[simp]
/--
theorem `conj_pow` / 定理 `conj_pow`

English:
theorem conj_pow
  given: (f : End X) (n : Nat)
  statement: α.conj (f ^ n) = α.conj f ^ n
  proof: α.conj.toMonoidHom.map_pow f n

中文:
定理 conj_pow
  条件: (f : End X) (n : 自然数)
  结论: α.conj (f ^ n) = α.conj f ^ n
  证明: α.conj.toMonoidHom.map_pow f n

Depends on / 依赖: conj.toMonoidHom.map_pow, map_pow, toMonoidHom
-/
theorem conj_pow (f : End X) (n : Nat) : α.conj (f ^ n) = α.conj f ^ n :=
  α.conj.toMonoidHom.map_pow f n

-- TODO: change definition so that `conjAut_apply` becomes a `rfl`?
/--
Definition of `conjAut` / `conjAut` 的定义

English:
definition conjAut
  signature: : Aut X ≃* Aut Y
  body: (Aut.unitsEndEquivAut X).symm.trans (Units.mapEquiv α.conj).trans Aut.unitsEndEquivAut Y

中文:
定义 conjAut
  签名: : Aut X ≃* Aut Y
  定义体: (Aut.unitsEndEquivAut X).symm.trans (Units.mapEquiv α.conj).trans Aut.unitsEndEquivAut Y

Depends on / 依赖: Aut.unitsEndEquivAut, Units.mapEquiv, mapEquiv, symm.trans, unitsEndEquivAut
-/
def conjAut : Aut X ≃* Aut Y :=
(Aut.unitsEndEquivAut X).symm.trans (Units.mapEquiv α.conj).trans Aut.unitsEndEquivAut Y

/--
theorem `conjAut_apply` / 定理 `conjAut_apply`

English:
theorem conjAut_apply
  given: (f : Aut X)
  statement: α.conjAut f = α.symm ≪≫ f ≪≫ α
  proof: by cat_disch

@[simp]

中文:
定理 conjAut_apply
  条件: (f : Aut X)
  结论: α.conjAut f = α.symm ≪≫ f ≪≫ α
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch, preservesLimitIso
-/
theorem conjAut_apply (f : Aut X) : α.conjAut f = α.symm ≪≫ f ≪≫ α := by cat_disch

@[simp]
/--
theorem `conjAut_hom` / 定理 `conjAut_hom`

English:
theorem conjAut_hom
  given: (f : Aut X)
  statement: (α.conjAut f).hom = α.conj f.hom
  proof: rfl

中文:
定理 conjAut_hom
  条件: (f : Aut X)
  结论: (α.conjAut f).hom = α.conj f.hom
  证明: rfl
-/
theorem conjAut_hom (f : Aut X) : (α.conjAut f).hom = α.conj f.hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `trans_conjAut` / 定理 `trans_conjAut`

English:
theorem trans_conjAut
  given: {Z : C} (β : Y ≅ Z) (f : Aut X)
  proof: by
  simp only [conjAut_apply, Iso.trans_symm, Iso.trans_assoc]

@[simp]

中文:
定理 trans_conjAut
  条件: {Z : C} (β : Y ≅ Z) (f : Aut X)
  证明: by
  simp only [conjAut_apply, Iso.trans_symm, Iso.trans_assoc]

@[simp]

Depends on / 依赖: Iso.trans_assoc, Iso.trans_symm, conjAut_apply, trans_assoc, trans_symm
-/
theorem trans_conjAut {Z : C} (β : Y ≅ Z) (f : Aut X) :
    (α ≪≫ β).conjAut f = β.conjAut (α.conjAut f) := by
  simp only [conjAut_apply, Iso.trans_symm, Iso.trans_assoc]

@[simp]
/--
theorem `conjAut_mul` / 定理 `conjAut_mul`

English:
theorem conjAut_mul
  given: (f g : Aut X)
  statement: α.conjAut (f * g) = α.conjAut f * α.conjAut g
  proof: map_mul α.conjAut f g

@[simp]

中文:
定理 conjAut_mul
  条件: (f g : Aut X)
  结论: α.conjAut (f * g) = α.conjAut f * α.conjAut g
  证明: map_mul α.conjAut f g

@[simp]

Depends on / 依赖: conjAut, map_mul
-/
theorem conjAut_mul (f g : Aut X) : α.conjAut (f * g) = α.conjAut f * α.conjAut g :=
  map_mul α.conjAut f g

@[simp]
/--
theorem `conjAut_trans` / 定理 `conjAut_trans`

English:
theorem conjAut_trans
  given: (f g : Aut X)
  statement: α.conjAut (f ≪≫ g) = α.conjAut f ≪≫ α.conjAut g
  proof: conjAut_mul α g f

@[simp]

中文:
定理 conjAut_trans
  条件: (f g : Aut X)
  结论: α.conjAut (f ≪≫ g) = α.conjAut f ≪≫ α.conjAut g
  证明: conjAut_mul α g f

@[simp]

Depends on / 依赖: conjAut_mul
-/
theorem conjAut_trans (f g : Aut X) : α.conjAut (f ≪≫ g) = α.conjAut f ≪≫ α.conjAut g :=
  conjAut_mul α g f

@[simp]
/--
theorem `conjAut_pow` / 定理 `conjAut_pow`

English:
theorem conjAut_pow
  given: (f : Aut X) (n : Nat)
  statement: α.conjAut (f ^ n) = α.conjAut f ^ n
  proof: map_pow α.conjAut f n

@[simp]

中文:
定理 conjAut_pow
  条件: (f : Aut X) (n : 自然数)
  结论: α.conjAut (f ^ n) = α.conjAut f ^ n
  证明: map_pow α.conjAut f n

@[simp]

Depends on / 依赖: conjAut, map_pow
-/
theorem conjAut_pow (f : Aut X) (n : Nat) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  map_pow α.conjAut f n

@[simp]
/--
theorem `conjAut_zpow` / 定理 `conjAut_zpow`

English:
theorem conjAut_zpow
  given: (f : Aut X) (n : Int)
  statement: α.conjAut (f ^ n) = α.conjAut f ^ n
  proof: map_zpow α.conjAut f n

中文:
定理 conjAut_zpow
  条件: (f : Aut X) (n : 整数)
  结论: α.conjAut (f ^ n) = α.conjAut f ^ n
  证明: map_zpow α.conjAut f n

Depends on / 依赖: conjAut, map_zpow
-/
theorem conjAut_zpow (f : Aut X) (n : Int) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  map_zpow α.conjAut f n

end Iso

namespace Functor

universe v₁ u₁

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D)

/--
theorem `map_conj` / 定理 `map_conj`

English:
theorem map_conj
  given: {X Y : C} (α : X ≅ Y) (f : End X)
  proof: map_homCongr F α α f

中文:
定理 map_conj
  条件: {X Y : C} (α : X ≅ Y) (f : End X)
  证明: map_homCongr F α α f

Depends on / 依赖: map_homCongr
-/
theorem map_conj {X Y : C} (α : X ≅ Y) (f : End X) :
    F.map (α.conj f) = (F.mapIso α).conj (F.map f) :=
  map_homCongr F α α f

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `map_conjAut` / 定理 `map_conjAut`

English:
theorem map_conjAut
  given: (F : C ⥤ D) {X Y : C} (α : X ≅ Y) (f : Aut X)
  proof: by
  ext; simp only [mapIso_hom, Iso.conjAut_hom, F.map_conj]

中文:
定理 map_conjAut
  条件: (F : C ⥤ D) {X Y : C} (α : X ≅ Y) (f : Aut X)
  证明: by
  ext; simp only [mapIso_hom, Iso.conjAut_hom, F.map_conj]

Depends on / 依赖: F.map_conj, Iso.conjAut_hom, conjAut_hom, mapIso_hom, map_conj
-/
theorem map_conjAut (F : C ⥤ D) {X Y : C} (α : X ≅ Y) (f : Aut X) :
    F.mapIso (α.conjAut f) = (F.mapIso α).conjAut (F.mapIso f) := by
  ext; simp only [mapIso_hom, Iso.conjAut_hom, F.map_conj]

-- alternative proof: by simp only [Iso.conjAut_apply, F.mapIso_trans, F.mapIso_symm]
end Functor

end CategoryTheory
