/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# `Grp (Type u) ≌ GrpCat.{u}`

The category of internal group objects in `Type`
is equivalent to the category of "native" bundled groups.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

@[expose] public section

assert_not_exists Field

universe v u

open CategoryTheory MonObj

namespace GrpTypeEquivalenceGrp

/--
Instance `grpGroup` / 实例 `grpGroup`

English:
instance grpGroup
  signature: (A : Type u) [GrpObj A]
  body: { MonTypeEquivalenceMon.monMonoid A with
    inv := ι[A]
    inv_mul_cancel a := ConcreteCategory.congr_hom (GrpObj.left_inv A) a }

中文:
实例 grpGroup
  签名: (A : 类型u) [GrpObj A]
  定义体: { MonTypeEquivalenceMon.monMonoid A with
    inv := ι[A]
    inv_mul_cancel a := ConcreteCategory.congr_hom (GrpObj.left_inv A) a }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, GrpObj, GrpObj.left_inv, MonTypeEquivalenceMon, MonTypeEquivalenceMon.monMonoid, congr_hom, inv_mul_cancel, left_inv, monMonoid
-/
instance grpGroup (A : Type u) [GrpObj A] : Group A :=
  { MonTypeEquivalenceMon.monMonoid A with
    inv := ι[A]
    inv_mul_cancel a := ConcreteCategory.congr_hom (GrpObj.left_inv A) a }

/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Grp (Type u) ⥤ GrpCat.{u} where
  body: GrpCat.of A.X
  map f := GrpCat.ofHom (MonTypeEquivalenceMon.functor.map f.hom).hom

中文:
定义 functor
  签名: : 群 (类型u) ⥤ 群范畴.{u} where
  定义体: GrpCat.of A.X
  map f := GrpCat.ofHom (MonTypeEquivalenceMon.functor.map f.hom).hom

Depends on / 依赖: GrpCat, GrpCat.of
-/
noncomputable def functor : Grp (Type u) ⥤ GrpCat.{u} where
  obj A := GrpCat.of A.X
  map f := GrpCat.ofHom (MonTypeEquivalenceMon.functor.map f.hom).hom

/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : GrpCat.{u} ⥤ Grp (Type u) where
  body: { MonTypeEquivalenceMon.inverse.obj ((forget₂ GrpCat MonCat).obj A) with
      grp :=
        { inv := ↾((·⁻¹) : A -> A)
          left_inv := by
            ext x
            exact inv_mul_cancel (G := A) x
          right_inv := by
            ext x
            exact mul_inv_cancel (G := A) x } }
  map f := Grp.homMk' (MonTypeEquivalenceMon.inverse.map ((forget₂ GrpCat MonCat).map f))

中文:
定义 inverse
  签名: : 群范畴.{u} ⥤ 群 (类型u) where
  定义体: { MonTypeEquivalenceMon.inverse.obj ((forget₂ GrpCat MonCat).obj A) with
      grp :=
        { inv := ↾((·⁻¹) : A -> A)
          left_inv := by
            ext x
            exact inv_mul_cancel (G := A) x
          right_inv := by
            ext x
            exact mul_inv_cancel (G := A) x } }
  map f := Grp.homMk' (MonTypeEquivalenceMon.inverse.map ((forget₂ GrpCat MonCat).map f))

Depends on / 依赖: Grp.homMk, GrpCat, MonCat, MonTypeEquivalenceMon, MonTypeEquivalenceMon.inverse.map, MonTypeEquivalenceMon.inverse.obj, inv_mul_cancel, inverse, left_inv, mul_inv_cancel, right_inv
-/
noncomputable def inverse : GrpCat.{u} ⥤ Grp (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ GrpCat MonCat).obj A) with
      grp :=
        { inv := ↾((·⁻¹) : A -> A)
          left_inv := by
            ext x
            exact inv_mul_cancel (G := A) x
          right_inv := by
            ext x
            exact mul_inv_cancel (G := A) x } }
  map f := Grp.homMk' (MonTypeEquivalenceMon.inverse.map ((forget₂ GrpCat MonCat).map f))

end GrpTypeEquivalenceGrp

/--
Definition of `grpTypeEquivalenceGrp` / `grpTypeEquivalenceGrp` 的定义

English:
definition grpTypeEquivalenceGrp
  signature: : Grp (Type u) ≌ GrpCat.{u} where
  body: GrpTypeEquivalenceGrp.functor
  inverse := GrpTypeEquivalenceGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

中文:
定义 grpTypeEquivalenceGrp
  签名: : 群 (类型u) ≌ 群范畴.{u} where
  定义体: GrpTypeEquivalenceGrp.functor
  inverse := GrpTypeEquivalenceGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

Depends on / 依赖: GrpTypeEquivalenceGrp, GrpTypeEquivalenceGrp.functor, functor
-/
noncomputable def grpTypeEquivalenceGrp : Grp (Type u) ≌ GrpCat.{u} where
  functor := GrpTypeEquivalenceGrp.functor
  inverse := GrpTypeEquivalenceGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/--
Definition of `grpTypeEquivalenceGrpForget` / `grpTypeEquivalenceGrpForget` 的定义

English:
definition grpTypeEquivalenceGrpForget
  signature: :
  body: Iso.refl _

中文:
定义 grpTypeEquivalenceGrpForget
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def grpTypeEquivalenceGrpForget :
    GrpTypeEquivalenceGrp.functor ⋙ forget₂ GrpCat MonCat ≅
      Grp.forget₂Mon (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _
