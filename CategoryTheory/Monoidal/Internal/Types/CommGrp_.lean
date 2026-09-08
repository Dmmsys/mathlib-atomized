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

/-
**CommGrpTypeEquivalenceCommGrp.commGrpCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Comm
GrpTypeEquivalenceCommGrp`。
形式化陈述：commGrpCommGroup (A : Type u) [GrpObj A] [IsCommMonObj A] : CommGroup A
参数：A : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commGrpCommGroup (A : Type u) [GrpObj A] [IsCommMonObj A] : CommGroup A :=
  { GrpTypeEquivalenceGrp.grpGroup A with
    mul_comm := fun x y => by
      convert! congr_hom (CC := fun X ↦ X) (IsCommMonObj.mul_comm A) (y, x) }

/-- Converting a commutative group object in `Type u` into a group. -/
/-
**CommGrpTypeEquivalenceCommGrp.functor** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpTypeEq
uivalenceCommGrp`。
形式化陈述：functor : CommGrp (Type u) ⥤ CommGrpCat.{u} where obj A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommGrp.comm`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   [inst_2
 : CategoryTheory…

--- 原说明 ---
Converting a commutative group object in `Type u` into a group.
-/
noncomputable def functor : CommGrp (Type u) ⥤ CommGrpCat.{u} where
  obj A := CommGrpCat.of A.X
  map f := CommGrpCat.ofHom (GrpTypeEquivalenceGrp.functor.map f.hom).hom

/-- Converting a group into a group object in `Type u`. -/
/-
**CommGrpTypeEquivalenceCommGrp.inverse** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpTypeEq
uivalenceCommGrp`。
形式化陈述：inverse : CommGrpCat.{u} ⥤ CommGrp (Type u) where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converting a group into a group object in `Type u`.
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
/-
**CommGrpTypeEquivalenceCommGrp.inverse_obj_X** 是 Mathlib 中的一个定理，位于命名空间 `CommGrp
TypeEquivalenceCommGrp`。
形式化陈述：inverse_obj_X {A : CommGrpCat.{u}} : (inverse.obj A).X = A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inverse_obj_X {A : CommGrpCat.{u}} : (inverse.obj A).X = A := rfl

@[simp]
/-
**CommGrpTypeEquivalenceCommGrp.inverse_obj_one** 是 Mathlib 中的一个定理，位于命名空间 `CommG
rpTypeEquivalenceCommGrp`。
形式化陈述：inverse_obj_one {A : CommGrpCat.{u}} {x} : dsimp% η[(inverse.obj A).X] x =
 (1 : A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inverse_obj_one {A : CommGrpCat.{u}} {x} : dsimp% η[(inverse.obj A).X] x = (1 : A) := rfl

@[simp]
/-
**CommGrpTypeEquivalenceCommGrp.inverse_obj_mul** 是 Mathlib 中的一个定理，位于命名空间 `CommG
rpTypeEquivalenceCommGrp`。
形式化陈述：inverse_obj_mul {A : CommGrpCat.{u}} {p} : dsimp% μ[(inverse.obj A).X] p =
 (p.1 : A) * p.2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inverse_obj_mul {A : CommGrpCat.{u}} {p} :
    dsimp% μ[(inverse.obj A).X] p = (p.1 : A) * p.2 :=
  rfl

@[simp]
/-
**CommGrpTypeEquivalenceCommGrp.inverse_obj_inv** 是 Mathlib 中的一个定理，位于命名空间 `CommG
rpTypeEquivalenceCommGrp`。
形式化陈述：inverse_obj_inv {A : CommGrpCat.{u}} {x} : dsimp% ι[(inverse.obj A).X] x =
 (x : A)⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inverse_obj_inv {A : CommGrpCat.{u}} {x} : dsimp% ι[(inverse.obj A).X] x = (x : A)⁻¹ := rfl

end CommGrpTypeEquivalenceCommGrp

/-- The category of commutative group objects in `Type u` is equivalent to the category of
commutative groups. -/
/-
**commGrpTypeEquivalenceCommGrp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commGrpTypeEquivalenceCommGrp : CommGrp (Type u) ≌ CommGrpCat.{u} where fu
nctor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The category of commutative group objects in `Type u` is equivalent to the categ
ory of
commutative groups.
-/
noncomputable def commGrpTypeEquivalenceCommGrp : CommGrp (Type u) ≌ CommGrpCat.{u} where
  functor := CommGrpTypeEquivalenceCommGrp.functor
  inverse := CommGrpTypeEquivalenceCommGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/-- The equivalences `Grp (Type u) ≌ GrpCat.{u}` and `CommGrp (Type u) ≌ CommGrpCat.{u}`
are naturally compatible with the forgetful functors to `GrpCat` and `Grp (Type u)`.
-/
/-
**commGrpTypeEquivalenceCommGrpForgetGrp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commGrpTypeEquivalenceCommGrpForgetGrp : CommGrpTypeEquivalenceCommGrp.fun
ctor ⋙ forget₂ CommGrpCat GrpCat ≅ CommGrp.forget₂Grp (Type u) ⋙ GrpTypeEquivale
nceGrp.functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalences `Grp (Type u) ≌ GrpCat.{u}` and `CommGrp (Type u) ≌ CommGrpCat.
{u}`
are naturally compatible with the forgetful functors to `GrpCat` and `Grp (Type 
u)`.
-/
noncomputable def commGrpTypeEquivalenceCommGrpForgetGrp :
    CommGrpTypeEquivalenceCommGrp.functor ⋙ forget₂ CommGrpCat GrpCat ≅
      CommGrp.forget₂Grp (Type u) ⋙ GrpTypeEquivalenceGrp.functor :=
  Iso.refl _

/-- The equivalences `CommMon (Type u) ≌ CommMonCat.{u}` and `CommGrp (Type u) ≌ CommGrpCat.{u}`
are naturally compatible with the forgetful functors to `GrpCat` and `Grp (Type u)`.
-/
/-
**commGrpTypeEquivalenceCommGrpForgetCommMon** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commGrpTypeEquivalenceCommGrpForgetCommMon : CommGrpTypeEquivalenceCommGrp
.functor ⋙ forget₂ CommGrpCat CommMonCat ≅ CommGrp.forget₂CommMon (Type u) ⋙ Com
mMonTypeEquivalenceCommMon.functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalences `CommMon (Type u) ≌ CommMonCat.{u}` and `CommGrp (Type u) ≌ Com
mGrpCat.{u}`
are naturally compatible with the forgetful functors to `GrpCat` and `Grp (Type 
u)`.
-/
noncomputable def commGrpTypeEquivalenceCommGrpForgetCommMon :
    CommGrpTypeEquivalenceCommGrp.functor ⋙ forget₂ CommGrpCat CommMonCat ≅
      CommGrp.forget₂CommMon (Type u) ⋙ CommMonTypeEquivalenceCommMon.functor :=
  Iso.refl _
