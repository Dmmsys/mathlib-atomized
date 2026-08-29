/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# The category of R-modules has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `ModuleCat R` is an abelian category.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

attribute [local ext] Subtype.ext

section

-- implementation details of `HasImage` for ModuleCat; use the API, not these
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: : ModuleCat R
  body: ModuleCat.of R (LinearMap.range f.hom)

中文:
定义 像
  签名: : 模范畴 R
  定义体: ModuleCat.of R (LinearMap.range f.hom)

Depends on / 依赖: LinearMap, LinearMap.range, ModuleCat, ModuleCat.of, f.hom
-/
def image : ModuleCat R :=
  ModuleCat.of R (LinearMap.range f.hom)

/--
Definition of `image.ι` / `image.ι` 的定义

English:
definition image.ι
  signature: : image f ⟶ H
  body: ofHom (LinearMap.range f.hom).subtype

中文:
定义 像.ι
  签名: : 像 f ⟶ H
  定义体: ofHom (LinearMap.range f.hom).subtype
-/
def image.ι : image f ⟶ H :=
  ofHom (LinearMap.range f.hom).subtype

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (image.ι f)
  body: ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

中文:
实例 :
  签名: 单态射 (像.ι f)
  定义体: ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, Subtype, Subtype.val_injective, mono_of_injective, val_injective
-/
instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

/--
Definition of `factorThruImage` / `factorThruImage` 的定义

English:
definition factorThruImage
  signature: : G ⟶ image f
  body: ofHom f.hom.rangeRestrict

中文:
定义 factorThruImage
  签名: : G ⟶ 像 f
  定义体: ofHom f.hom.rangeRestrict

Depends on / 依赖: f.hom.rangeRestrict, rangeRestrict
-/
def factorThruImage : G ⟶ image f :=
  ofHom f.hom.rangeRestrict

/--
theorem `image.fac` / 定理 `image.fac`

English:
theorem image.fac
  statement: factorThruImage f ≫ image.ι f = f
  proof: rfl

中文:
定理 像.fac
  结论: factorThruImage f ≫ 像.ι f = f
  证明: rfl
-/
theorem image.fac : factorThruImage f ≫ image.ι f = f :=
  rfl

attribute [local simp] image.fac

variable {f}

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `image.lift` / `image.lift` 的定义

English:
definition image.lift
  signature: (F' : MonoFactorisation f)
  body: ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f -> F'.I)
    map_add' := fun x y => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_add]
      change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl
    map_smul' := fun c x => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_smul]
      change (F'.e ≫ F'.m) _ = _ • (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl }

中文:
定义 像.lift
  签名: (F' : 单态射分解 f)
  定义体: ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f -> F'.I)
    map_add' := fun x y => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_add]
      change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl
    map_smul' := fun c x => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_smul]
      change (F'.e ≫ F'.m) _ = _ • (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl }
-/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f -> F'.I)
    map_add' := fun x y => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_add]
      change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl
    map_smul' := fun c x => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_smul]
      change (F'.e ≫ F'.m) _ = _ • (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl }

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `image.lift_fac` / 定理 `image.lift_fac`

English:
theorem image.lift_fac
  given: (F' : MonoFactorisation f)
  statement: image.lift F' ≫ F'.m = image.ι f
  proof: by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac]; rw [(Classical.indefiniteDescription _ x.2).2]
  rfl

中文:
定理 像.lift_fac
  条件: (F' : 单态射分解 f)
  结论: 像.lift F' ≫ F'.m = 像.ι f
  证明: by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac]; rw [(Classical.indefiniteDescription _ x.2).2]
  rfl
-/
theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac]; rw [(Classical.indefiniteDescription _ x.2).2]
  rfl

end

/--
Definition of `monoFactorisation` / `monoFactorisation` 的定义

English:
definition monoFactorisation
  signature: : MonoFactorisation f where
  body: image f
  m := image.ι f
  e := factorThruImage f

中文:
定义 monoFactorisation
  签名: : 单态射分解 f where
  定义体: image f
  m := image.ι f
  e := factorThruImage f
-/
def monoFactorisation : MonoFactorisation f where
  I := image f
  m := image.ι f
  e := factorThruImage f

/--
Definition of `isImage` / `isImage` 的定义

English:
definition isImage
  signature: : IsImage (monoFactorisation f) where
  body: image.lift
  lift_fac := image.lift_fac

中文:
定义 isImage
  签名: : 是像 (monoFactorisation f) where
  定义体: image.lift
  lift_fac := image.lift_fac

Depends on / 依赖: image.lift
-/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac := image.lift_fac

/--
Definition of `imageIsoRange` / `imageIsoRange` 的定义

English:
definition imageIsoRange
  signature: {G H : ModuleCat.{v} R} (f : G ⟶ H)
  body: IsImage.isoExt (Image.isImage f) (isImage f)

@[simp, reassoc, elementwise]

中文:
定义 imageIsoRange
  签名: {G H : 模范畴.{v} R} (f : G ⟶ H)
  定义体: IsImage.isoExt (Image.isImage f) (isImage f)

@[simp, reassoc, elementwise]

Depends on / 依赖: Image.isImage, IsImage, IsImage.isoExt, isImage, isoExt
-/
noncomputable def imageIsoRange {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    Limits.image f ≅ ModuleCat.of R (LinearMap.range f.hom) :=
  IsImage.isoExt (Image.isImage f) (isImage f)

@[simp, reassoc, elementwise]
/--
theorem `imageIsoRange_inv_image_ι` / 定理 `imageIsoRange_inv_image_ι`

English:
theorem imageIsoRange_inv_image_ι
  given: {G H : ModuleCat.{v} R} (f : G ⟶ H)
  proof: IsImage.isoExt_inv_m _ _

@[simp, reassoc, elementwise]

中文:
定理 imageIsoRange_inv_image_ι
  条件: {G H : 模范畴.{v} R} (f : G ⟶ H)
  证明: IsImage.isoExt_inv_m _ _

@[simp, reassoc, elementwise]

Depends on / 依赖: IsImage, IsImage.isoExt_inv_m, isoExt_inv_m
-/
theorem imageIsoRange_inv_image_ι {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (imageIsoRange f).inv ≫ Limits.image.ι f = ModuleCat.ofHom (LinearMap.range f.hom).subtype :=
  IsImage.isoExt_inv_m _ _

@[simp, reassoc, elementwise]
/--
theorem `imageIsoRange_hom_subtype` / 定理 `imageIsoRange_hom_subtype`

English:
theorem imageIsoRange_hom_subtype
  given: {G H : ModuleCat.{v} R} (f : G ⟶ H)
  proof: by
  rw [← imageIsoRange_inv_image_ι f]; rw [Iso.hom_inv_id_assoc]

中文:
定理 imageIsoRange_hom_subtype
  条件: {G H : 模范畴.{v} R} (f : G ⟶ H)
  证明: by
  rw [← imageIsoRange_inv_image_ι f]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id_assoc, hom_inv_id_assoc
-/
theorem imageIsoRange_hom_subtype {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (imageIsoRange f).hom ≫ ModuleCat.ofHom (LinearMap.range f.hom).subtype = Limits.image.ι f := by
  rw [← imageIsoRange_inv_image_ι f]; rw [Iso.hom_inv_id_assoc]

end ModuleCat
