/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# `CommGrp (Type u) ≌ CommGrpCat.{u}`

The category of internal commutative group objects in `Type`
is equivalent to the category of "native" bundled commutative groups.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

@[expose] public section

assert_not_exists Field

universe v u

open CategoryTheory MonObj ConcreteCategory

namespace CommGrpTypeEquivalenceCommGrp

/--
Instance `commGrpCommGroup` / 实例 `commGrpCommGroup`

English:
instance commGrpCommGroup
  signature: (A : Type u) [GrpObj A] [IsCommMonObj A]
  body: { GrpTypeEquivalenceGrp.grpGroup A with
    mul_comm := fun x y => by
      convert! congr_hom (CC := fun X => X) (IsCommMonObj.mul_comm A) (y, x) }

中文:
实例 commGrpCommGroup
  签名: (A : 类型u) [GrpObj A] [是交换MonObj A]
  定义体: { GrpTypeEquivalenceGrp.grpGroup A with
    mul_comm := fun x y => by
      convert! congr_hom (CC := fun X => X) (IsCommMonObj.mul_comm A) (y, x) }

Depends on / 依赖: GrpTypeEquivalenceGrp, GrpTypeEquivalenceGrp.grpGroup, IsCommMonObj, IsCommMonObj.mul_comm, W_isInvertedBy_presheafFiber, W_toSheafify, congr_hom, convert, grpGroup, mul_comm
-/
instance commGrpCommGroup (A : Type u) [GrpObj A] [IsCommMonObj A] : CommGroup A :=
  { GrpTypeEquivalenceGrp.grpGroup A with
    mul_comm := fun x y => by
      convert! congr_hom (CC := fun X => X) (IsCommMonObj.mul_comm A) (y, x) }

/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : CommGrp (Type u) ⥤ CommGrpCat.{u} where
  body: CommGrpCat.of A.X
  map f := CommGrpCat.ofHom (GrpTypeEquivalenceGrp.functor.map f.hom).hom

中文:
定义 functor
  签名: : 交换群 (类型u) ⥤ 交换群范畴.{u} where
  定义体: CommGrpCat.of A.X
  map f := CommGrpCat.ofHom (GrpTypeEquivalenceGrp.functor.map f.hom).hom

Depends on / 依赖: CommGrpCat, CommGrpCat.of
-/
noncomputable def functor : CommGrp (Type u) ⥤ CommGrpCat.{u} where
  obj A := CommGrpCat.of A.X
  map f := CommGrpCat.ofHom (GrpTypeEquivalenceGrp.functor.map f.hom).hom

/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : CommGrpCat.{u} ⥤ CommGrp (Type u) where
  body: { grpTypeEquivalenceGrp.inverse.obj ((forget₂ CommGrpCat GrpCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := InducedCategory.homMk
    (GrpTypeEquivalenceGrp.inverse.map ((forget₂ CommGrpCat GrpCat).map f))

@[simp]

中文:
定义 inverse
  签名: : 交换群范畴.{u} ⥤ 交换群 (类型u) where
  定义体: { grpTypeEquivalenceGrp.inverse.obj ((forget₂ CommGrpCat GrpCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := InducedCategory.homMk
    (GrpTypeEquivalenceGrp.inverse.map ((forget₂ CommGrpCat GrpCat).map f))

@[simp]

Depends on / 依赖: CommGrpCat, CommMonoid, CommMonoid.mul_comm, GrpCat, GrpTypeEquivalenceGrp, GrpTypeEquivalenceGrp.inverse.map, InducedCategory, InducedCategory.homMk, grpTypeEquivalenceGrp, grpTypeEquivalenceGrp.inverse.obj, inverse, mul_comm
-/
noncomputable def inverse : CommGrpCat.{u} ⥤ CommGrp (Type u) where
  obj A :=
    { grpTypeEquivalenceGrp.inverse.obj ((forget₂ CommGrpCat GrpCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := InducedCategory.homMk
    (GrpTypeEquivalenceGrp.inverse.map ((forget₂ CommGrpCat GrpCat).map f))

@[simp]
/--
theorem `inverse_obj_X` / 定理 `inverse_obj_X`

English:
theorem inverse_obj_X
  given: {A : CommGrpCat.{u}}
  statement: (inverse.obj A).X = A
  proof: rfl

@[simp]

中文:
定理 inverse_obj_X
  条件: {A : 交换群范畴.{u}}
  结论: (inverse.obj A).X = A
  证明: rfl

@[simp]
-/
theorem inverse_obj_X {A : CommGrpCat.{u}} : (inverse.obj A).X = A := rfl

@[simp]
/--
theorem `inverse_obj_one` / 定理 `inverse_obj_one`

English:
theorem inverse_obj_one
  given: {A : CommGrpCat.{u}} {x}
  statement: dsimp% η[(inverse.obj A).X] x = (1 : A)
  proof: rfl

@[simp]

中文:
定理 inverse_obj_one
  条件: {A : 交换群范畴.{u}} {x}
  结论: dsimp% η[(inverse.obj A).X] x = (1 : A)
  证明: rfl

@[simp]
-/
theorem inverse_obj_one {A : CommGrpCat.{u}} {x} : dsimp% η[(inverse.obj A).X] x = (1 : A) := rfl

@[simp]
/--
theorem `inverse_obj_mul` / 定理 `inverse_obj_mul`

English:
theorem inverse_obj_mul
  given: {A : CommGrpCat.{u}} {p}
  proof: rfl

@[simp]

中文:
定理 inverse_obj_mul
  条件: {A : 交换群范畴.{u}} {p}
  证明: rfl

@[simp]
-/
theorem inverse_obj_mul {A : CommGrpCat.{u}} {p} :
    dsimp% μ[(inverse.obj A).X] p = (p.1 : A) * p.2 :=
  rfl

@[simp]
/--
theorem `inverse_obj_inv` / 定理 `inverse_obj_inv`

English:
theorem inverse_obj_inv
  given: {A : CommGrpCat.{u}} {x}
  statement: dsimp% ι[(inverse.obj A).X] x = (x : A)⁻¹
  proof: rfl

中文:
定理 inverse_obj_inv
  条件: {A : 交换群范畴.{u}} {x}
  结论: dsimp% ι[(inverse.obj A).X] x = (x : A)⁻¹
  证明: rfl
-/
theorem inverse_obj_inv {A : CommGrpCat.{u}} {x} : dsimp% ι[(inverse.obj A).X] x = (x : A)⁻¹ := rfl

end CommGrpTypeEquivalenceCommGrp

/--
Definition of `commGrpTypeEquivalenceCommGrp` / `commGrpTypeEquivalenceCommGrp` 的定义

English:
definition commGrpTypeEquivalenceCommGrp
  signature: : CommGrp (Type u) ≌ CommGrpCat.{u} where
  body: CommGrpTypeEquivalenceCommGrp.functor
  inverse := CommGrpTypeEquivalenceCommGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

中文:
定义 commGrpTypeEquivalenceCommGrp
  签名: : 交换群 (类型u) ≌ 交换群范畴.{u} where
  定义体: CommGrpTypeEquivalenceCommGrp.functor
  inverse := CommGrpTypeEquivalenceCommGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

Depends on / 依赖: CommGrpTypeEquivalenceCommGrp, CommGrpTypeEquivalenceCommGrp.functor, functor
-/
noncomputable def commGrpTypeEquivalenceCommGrp : CommGrp (Type u) ≌ CommGrpCat.{u} where
  functor := CommGrpTypeEquivalenceCommGrp.functor
  inverse := CommGrpTypeEquivalenceCommGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/--
Definition of `commGrpTypeEquivalenceCommGrpForgetGrp` / `commGrpTypeEquivalenceCommGrpForgetGrp` 的定义

English:
definition commGrpTypeEquivalenceCommGrpForgetGrp
  signature: :
  body: Iso.refl _

中文:
定义 commGrpTypeEquivalenceCommGrpForgetGrp
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def commGrpTypeEquivalenceCommGrpForgetGrp :
    CommGrpTypeEquivalenceCommGrp.functor ⋙ forget₂ CommGrpCat GrpCat ≅
      CommGrp.forget₂Grp (Type u) ⋙ GrpTypeEquivalenceGrp.functor :=
  Iso.refl _

/--
Definition of `commGrpTypeEquivalenceCommGrpForgetCommMon` / `commGrpTypeEquivalenceCommGrpForgetCommMon` 的定义

English:
definition commGrpTypeEquivalenceCommGrpForgetCommMon
  signature: :
  body: Iso.refl _

中文:
定义 commGrpTypeEquivalenceCommGrpForgetCommMon
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def commGrpTypeEquivalenceCommGrpForgetCommMon :
    CommGrpTypeEquivalenceCommGrp.functor ⋙ forget₂ CommGrpCat CommMonCat ≅
      CommGrp.forget₂CommMon (Type u) ⋙ CommMonTypeEquivalenceCommMon.functor :=
  Iso.refl _
