/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# The category of commutative additive groups has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `AddCommGrpCat` is an abelian category.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AddCommGrpCat

-- Note that because `injective_of_mono` is currently only proved in `Type 0`,
-- we restrict to the lowest universe here for now.
variable {G H : AddCommGrpCat.{0}} (f : G ⟶ H)

attribute [local ext] Subtype.ext

section

-- implementation details of `IsImage` for `AddCommGrpCat`; use the API, not these
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: : AddCommGrpCat
  body: AddCommGrpCat.of (AddMonoidHom.range f.hom)

中文:
定义 image
  签名: : AddCommGrpCat
  定义体: AddCommGrpCat.of (AddMonoidHom.range f.hom)

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, AddMonoidHom, AddMonoidHom.range, f.hom
-/
def image : AddCommGrpCat :=
  AddCommGrpCat.of (AddMonoidHom.range f.hom)

/--
Definition of `image.ι` / `image.ι` 的定义

English:
definition image.ι
  signature: : image f ⟶ H
  body: ofHom f.hom.range.subtype

中文:
定义 image.ι
  签名: : image f ⟶ H
  定义体: ofHom f.hom.range.subtype

Depends on / 依赖: f.hom.range.subtype, subtype
-/
def image.ι : image f ⟶ H :=
  ofHom f.hom.range.subtype

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (image.ι f)
  body: ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

中文:
实例 :
  签名: Mono (image.ι f)
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
  签名: : G ⟶ image f
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
  proof: by
  ext
  rfl

中文:
定理 image.fac
  结论: factorThruImage f ≫ image.ι f = f
  证明: by
  ext
  rfl
-/
theorem image.fac : factorThruImage f ≫ image.ι f = f := by
  ext
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
    map_zero' := by
      have := F'.m_mono
      apply injective_of_mono F'.m
      change (F'.e ≫ F'.m) _ = _
      rw [F'.fac]; rw [map_zero]
      exact (Classical.indefiniteDescription (fun y => f y =

中文:
定义 image.lift
  签名: (F' : MonoFactorisation f)
  定义体: ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f -> F'.I)
    map_zero' := by
      have := F'.m_mono
      apply injective_of_mono F'.m
      change (F'.e ≫ F'.m) _ = _
      rw [F'.fac]; rw [map_zero]
      exact (Classical.indefiniteDescription (fun y => f y =

Depends on / 依赖: Classical, Classical.indefiniteDescription, indefiniteDescription, injective_of_mono, m_mono, map_add, map_zero
-/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f -> F'.I)
    map_zero' := by
      have := F'.m_mono
      apply injective_of_mono F'.m
      change (F'.e ≫ F'.m) _ = _
      rw [F'.fac]; rw [map_zero]
      exact (Classical.indefiniteDescription (fun y => f y = 0) _).2
    map_add' := by
      intro x y
      have := F'.m_mono
      apply injective_of_mono F'.m
      rw [map_add]
      change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
      rw [F'.fac]
      rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
      rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
      rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
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
定理 image.lift_fac
  条件: (F' : MonoFactorisation f)
  结论: image.lift F' ≫ F'.m = image.ι f
  证明: by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac]; rw [(Classical.indefiniteDescription _ x.2).2]
  rfl

Depends on / 依赖: Classical, Classical.indefiniteDescription, indefiniteDescription
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
  签名: : MonoFactorisation f where
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
  签名: : IsImage (monoFactorisation f) where
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
  signature: {G H : AddCommGrpCat.{0}} (f : G ⟶ H)
  body: IsImage.isoExt (Image.isImage f) (isImage f)

中文:
定义 imageIsoRange
  签名: {G H : AddCommGrpCat.{0}} (f : G ⟶ H)
  定义体: IsImage.isoExt (Image.isImage f) (isImage f)

Depends on / 依赖: Image.isImage, IsImage, IsImage.isoExt, isImage, isoExt
-/
noncomputable def imageIsoRange {G H : AddCommGrpCat.{0}} (f : G ⟶ H) :
    Limits.image f ≅ AddCommGrpCat.of f.hom.range :=
  IsImage.isoExt (Image.isImage f) (isImage f)

end AddCommGrpCat
