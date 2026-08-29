/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# `Mon Type u ≌ MonCat.{u}`

The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe v u

open CategoryTheory MonObj ConcreteCategory

namespace MonTypeEquivalenceMon

/--
Instance `monMonoid` / 实例 `monMonoid`

English:
instance monMonoid
  signature: (A : Type u) [MonObj A]
  body: η[A] PUnit.unit
  mul x y := μ[A] (x, y)
  one_mul x := by convert! congr_hom (CC := fun X => X) (one_mul A) (PUnit.unit, x)
  mul_one x := by convert! congr_hom (CC := fun X => X) (mul_one A) (x, PUnit.unit)
  mul_assoc x y z := by convert! congr_hom (CC := fun X => X) (mul_assoc A) ((x, y), z)

中文:
实例 monMonoid
  签名: (A : 类型u) [MonObj A]
  定义体: η[A] PUnit.unit
  mul x y := μ[A] (x, y)
  one_mul x := by convert! congr_hom (CC := fun X => X) (one_mul A) (PUnit.unit, x)
  mul_one x := by convert! congr_hom (CC := fun X => X) (mul_one A) (x, PUnit.unit)
  mul_assoc x y z := by convert! congr_hom (CC := fun X => X) (mul_assoc A) ((x, y), z)

Depends on / 依赖: PUnit.unit
-/
instance monMonoid (A : Type u) [MonObj A] : Monoid A where
  one := η[A] PUnit.unit
  mul x y := μ[A] (x, y)
  one_mul x := by convert! congr_hom (CC := fun X => X) (one_mul A) (PUnit.unit, x)
  mul_one x := by convert! congr_hom (CC := fun X => X) (mul_one A) (x, PUnit.unit)
  mul_assoc x y z := by convert! congr_hom (CC := fun X => X) (mul_assoc A) ((x, y), z)

/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Mon (Type u) ⥤ MonCat.{u} where
  body: MonCat.of A.X
  map f := MonCat.ofHom
    { toFun := f.hom
      map_one' := congr_hom (IsMonHom.one_hom f.hom) PUnit.unit
      map_mul' x y := congr_hom (CC := fun X => X) (IsMonHom.mul_hom f.hom) (x, y) }

中文:
定义 functor
  签名: : Mon (类型u) ⥤ MonCat.{u} where
  定义体: MonCat.of A.X
  map f := MonCat.ofHom
    { toFun := f.hom
      map_one' := congr_hom (IsMonHom.one_hom f.hom) PUnit.unit
      map_mul' x y := congr_hom (CC := fun X => X) (IsMonHom.mul_hom f.hom) (x, y) }

Depends on / 依赖: MonCat, MonCat.of
-/
noncomputable def functor : Mon (Type u) ⥤ MonCat.{u} where
  obj A := MonCat.of A.X
  map f := MonCat.ofHom
    { toFun := f.hom
      map_one' := congr_hom (IsMonHom.one_hom f.hom) PUnit.unit
      map_mul' x y := congr_hom (CC := fun X => X) (IsMonHom.mul_hom f.hom) (x, y) }

attribute [local simp] types_tensorObj_def types_tensorUnit_def in
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : MonCat.{u} ⥤ Mon (Type u) where
  body: { X := A
      mon :=
        { one := ↾fun _ => 1
          mul := ↾fun p => p.1 * p.2
          one_mul := by cat_disch
          mul_one := by cat_disch
          mul_assoc := by ext ⟨⟨x, y⟩, z⟩; simp [_root_.mul_assoc] } }
  map f := .mk' (↾f)
    (one_f := by
      #adaptation_note /-- Prior to

中文:
定义 inverse
  签名: : MonCat.{u} ⥤ Mon (类型u) where
  定义体: { X := A
      mon :=
        { one := ↾fun _ => 1
          mul := ↾fun p => p.1 * p.2
          one_mul := by cat_disch
          mul_one := by cat_disch
          mul_assoc := by ext ⟨⟨x, y⟩, z⟩; simp [_root_.mul_assoc] } }
  map f := .mk' (↾f)
    (one_f := by
      #adaptation_note /-- Prior to

Depends on / 依赖: _root_, _root_.mul_assoc, adaptation_note, argument, auto_param, cat_disch, github, github.com, instances, leanprover, mul_assoc, mul_f, mul_one, one_f, one_mul, provided
-/
noncomputable def inverse : MonCat.{u} ⥤ Mon (Type u) where
  obj A :=
    { X := A
      mon :=
        { one := ↾fun _ => 1
          mul := ↾fun p => p.1 * p.2
          one_mul := by cat_disch
          mul_one := by cat_disch
          mul_assoc := by ext ⟨⟨x, y⟩, z⟩; simp [_root_.mul_assoc] } }
  map f := .mk' (↾f)
    (one_f := by
      #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
      this argument was provided by the auto_param. -/
      simp +instances only
      cat_disch)
    (mul_f := by
      #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
      this argument was provided by the auto_param. -/
      simp +instances only
      cat_disch)

end MonTypeEquivalenceMon

open MonTypeEquivalenceMon

/--
Definition of `monTypeEquivalenceMon` / `monTypeEquivalenceMon` 的定义

English:
definition monTypeEquivalenceMon
  signature: : Mon (Type u) ≌ MonCat.{u} where
  body: functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

中文:
定义 monTypeEquivalenceMon
  签名: : Mon (类型u) ≌ MonCat.{u} where
  定义体: functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

Depends on / 依赖: functor
-/
noncomputable def monTypeEquivalenceMon : Mon (Type u) ≌ MonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/--
Definition of `monTypeEquivalenceMonForget` / `monTypeEquivalenceMonForget` 的定义

English:
definition monTypeEquivalenceMonForget
  signature: :
  body: NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

中文:
定义 monTypeEquivalenceMonForget
  签名: :
  定义体: NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
noncomputable def monTypeEquivalenceMonForget :
    MonTypeEquivalenceMon.functor ⋙ forget MonCat ≅ Mon.forget (Type u) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/--
Instance `monTypeInhabited` / 实例 `monTypeInhabited`

English:
instance monTypeInhabited
  signature: : Inhabited (Mon (Type u))
  body: ⟨MonTypeEquivalenceMon.inverse.obj (MonCat.of PUnit)⟩

中文:
实例 monTypeInhabited
  签名: : Inhabited (Mon (类型u))
  定义体: ⟨MonTypeEquivalenceMon.inverse.obj (MonCat.of PUnit)⟩

Depends on / 依赖: MonCat, MonCat.of, MonTypeEquivalenceMon, MonTypeEquivalenceMon.inverse.obj, inverse
-/
noncomputable instance monTypeInhabited : Inhabited (Mon (Type u)) :=
  ⟨MonTypeEquivalenceMon.inverse.obj (MonCat.of PUnit)⟩

namespace CommMonTypeEquivalenceCommMon

/--
Instance `commMonCommMonoid` / 实例 `commMonCommMonoid`

English:
instance commMonCommMonoid
  signature: (A : Type u) [MonObj A] [IsCommMonObj A]
  body: { MonTypeEquivalenceMon.monMonoid A with
    mul_comm := fun x y => by
      convert! congr_hom (CC := fun X => X) (IsCommMonObj.mul_comm A) (y, x) }

中文:
实例 commMonCommMonoid
  签名: (A : 类型u) [MonObj A] [IsCommMonObj A]
  定义体: { MonTypeEquivalenceMon.monMonoid A with
    mul_comm := fun x y => by
      convert! congr_hom (CC := fun X => X) (IsCommMonObj.mul_comm A) (y, x) }

Depends on / 依赖: IsCommMonObj, IsCommMonObj.mul_comm, MonTypeEquivalenceMon, MonTypeEquivalenceMon.monMonoid, congr_hom, convert, monMonoid, mul_comm
-/
instance commMonCommMonoid (A : Type u) [MonObj A] [IsCommMonObj A] : CommMonoid A :=
  { MonTypeEquivalenceMon.monMonoid A with
    mul_comm := fun x y => by
      convert! congr_hom (CC := fun X => X) (IsCommMonObj.mul_comm A) (y, x) }

/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : CommMon (Type u) ⥤ CommMonCat.{u} where
  body: CommMonCat.of A.X
  map f := CommMonCat.ofHom (MonTypeEquivalenceMon.functor.map f.hom).hom

中文:
定义 functor
  签名: : CommMon (类型u) ⥤ CommMonCat.{u} where
  定义体: CommMonCat.of A.X
  map f := CommMonCat.ofHom (MonTypeEquivalenceMon.functor.map f.hom).hom

Depends on / 依赖: CommMonCat, CommMonCat.of
-/
noncomputable def functor : CommMon (Type u) ⥤ CommMonCat.{u} where
  obj A := CommMonCat.of A.X
  map f := CommMonCat.ofHom (MonTypeEquivalenceMon.functor.map f.hom).hom

/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : CommMonCat.{u} ⥤ CommMon (Type u) where
  body: { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMonCat MonCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := CommMon.homMk (MonTypeEquivalenceMon.inverse.map ((forget₂ CommMonCat MonCat).map f))

中文:
定义 inverse
  签名: : CommMonCat.{u} ⥤ CommMon (类型u) where
  定义体: { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMonCat MonCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := CommMon.homMk (MonTypeEquivalenceMon.inverse.map ((forget₂ CommMonCat MonCat).map f))

Depends on / 依赖: CommMon, CommMon.homMk, CommMonCat, CommMonoid, CommMonoid.mul_comm, MonCat, MonTypeEquivalenceMon, MonTypeEquivalenceMon.inverse.map, MonTypeEquivalenceMon.inverse.obj, inverse, mul_comm
-/
noncomputable def inverse : CommMonCat.{u} ⥤ CommMon (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMonCat MonCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := CommMon.homMk (MonTypeEquivalenceMon.inverse.map ((forget₂ CommMonCat MonCat).map f))

end CommMonTypeEquivalenceCommMon

open CommMonTypeEquivalenceCommMon

/--
Definition of `commMonTypeEquivalenceCommMon` / `commMonTypeEquivalenceCommMon` 的定义

English:
definition commMonTypeEquivalenceCommMon
  signature: : CommMon (Type u) ≌ CommMonCat.{u} where
  body: functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

中文:
定义 commMonTypeEquivalenceCommMon
  签名: : CommMon (类型u) ≌ CommMonCat.{u} where
  定义体: functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

Depends on / 依赖: functor
-/
noncomputable def commMonTypeEquivalenceCommMon : CommMon (Type u) ≌ CommMonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/--
Definition of `commMonTypeEquivalenceCommMonForget` / `commMonTypeEquivalenceCommMonForget` 的定义

English:
definition commMonTypeEquivalenceCommMonForget
  signature: :
  body: Iso.refl _

中文:
定义 commMonTypeEquivalenceCommMonForget
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def commMonTypeEquivalenceCommMonForget :
    CommMonTypeEquivalenceCommMon.functor ⋙ forget₂ CommMonCat MonCat ≅
      CommMon.forget₂Mon (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _
