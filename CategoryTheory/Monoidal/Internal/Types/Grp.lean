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

/-
**GrpTypeEquivalenceGrp.grpGroup** 是 Mathlib 中的一个实例，位于命名空间 `GrpTypeEquivalenceGr
p`。
形式化陈述：grpGroup (A : Type u) [GrpObj A] : Group A
参数：A : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance grpGroup (A : Type u) [GrpObj A] : Group A :=
  { MonTypeEquivalenceMon.monMonoid A with
    inv := ι[A]
    inv_mul_cancel a := ConcreteCategory.congr_hom (GrpObj.left_inv A) a }

/-- Converting a group object in `Type u` into a group. -/
/-
**GrpTypeEquivalenceGrp.functor** 是 Mathlib 中的一个定义，位于命名空间 `GrpTypeEquivalenceGrp
`。
形式化陈述：functor : Grp (Type u) ⥤ GrpCat.{u} where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converting a group object in `Type u` into a group.
-/
noncomputable def functor : Grp (Type u) ⥤ GrpCat.{u} where
  obj A := GrpCat.of A.X
  map f := GrpCat.ofHom (MonTypeEquivalenceMon.functor.map f.hom).hom

/-- Converting a group into a group object in `Type u`. -/
/-
**GrpTypeEquivalenceGrp.inverse** 是 Mathlib 中的一个定义，位于命名空间 `GrpTypeEquivalenceGrp
`。
形式化陈述：inverse : GrpCat.{u} ⥤ Grp (Type u) where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converting a group into a group object in `Type u`.
-/
noncomputable def inverse : GrpCat.{u} ⥤ Grp (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ GrpCat MonCat).obj A) with
      grp :=
        { inv := ↾((·⁻¹) : A → A)
          left_inv := by
            ext x
            exact inv_mul_cancel (G := A) x
          right_inv := by
            ext x
            exact mul_inv_cancel (G := A) x } }
  map f := Grp.homMk' (MonTypeEquivalenceMon.inverse.map ((forget₂ GrpCat MonCat).map f))

end GrpTypeEquivalenceGrp

/-- The category of group objects in `Type u` is equivalent to the category of groups. -/
/-
**grpTypeEquivalenceGrp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：grpTypeEquivalenceGrp : Grp (Type u) ≌ GrpCat.{u} where functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The category of group objects in `Type u` is equivalent to the category of group
s.
-/
noncomputable def grpTypeEquivalenceGrp : Grp (Type u) ≌ GrpCat.{u} where
  functor := GrpTypeEquivalenceGrp.functor
  inverse := GrpTypeEquivalenceGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/-- The equivalences `Mon (Type u) ≌ MonCat.{u}` and `Grp (Type u) ≌ GrpCat.{u}`
are naturally compatible with the forgetful functors to `MonCat` and `Mon (Type u)`.
-/
/-
**grpTypeEquivalenceGrpForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：grpTypeEquivalenceGrpForget : GrpTypeEquivalenceGrp.functor ⋙ forget₂ GrpC
at MonCat ≅ Grp.forget₂Mon (Type u) ⋙ MonTypeEquivalenceMon.functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalences `Mon (Type u) ≌ MonCat.{u}` and `Grp (Type u) ≌ GrpCat.{u}`
are naturally compatible with the forgetful functors to `MonCat` and `Mon (Type 
u)`.
-/
noncomputable def grpTypeEquivalenceGrpForget :
    GrpTypeEquivalenceGrp.functor ⋙ forget₂ GrpCat MonCat ≅
      Grp.forget₂Mon (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _
