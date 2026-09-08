/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.CategoryTheory.Category.Bipointed

/-!
# The category of groups with zero

This file defines `GrpWithZero`, the category of groups with zero.
-/

@[expose] public section

assert_not_exists Ring

universe u

open CategoryTheory

/-- The category of groups with zero. -/
/-
**GrpWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of groups with zero.
-/
structure GrpWithZero where
  /-- Construct a bundled `GrpWithZero` from a `GroupWithZero`. -/
  of ::
  /-- The underlying group with zero. -/
  carrier : Type*
  [str : GroupWithZero carrier]

attribute [instance] GrpWithZero.str

namespace GrpWithZero

/-
**GrpWithZero.** 是 Mathlib 中的一个实例，位于命名空间 `GrpWithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort GrpWithZero Type* :=
  ⟨carrier⟩
/-
**GrpWithZero.** 是 Mathlib 中的一个实例，位于命名空间 `GrpWithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited GrpWithZero :=
  ⟨of (WithZero PUnit)⟩
/-
**GrpWithZero.** 是 Mathlib 中的一个实例，位于命名空间 `GrpWithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory.{u} GrpWithZero where
  Hom X Y := MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp f g := g.comp f
/-
**GrpWithZero.groupWithZeroConcreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `GrpWithZe
ro`。
形式化陈述：groupWithZeroConcreteCategory : ConcreteCategory GrpWithZero (MonoidWithZe
roHom · ·) where hom f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance groupWithZeroConcreteCategory : ConcreteCategory GrpWithZero (MonoidWithZeroHom · ·) where
  hom f := f
  ofHom f := f

/-- Typecheck a `MonoidWithZeroHom` as a morphism in `GrpWithZero`. -/
/-
**GrpWithZero.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `GrpWithZero`。
形式化陈述：ofHom {X Y : Type u} [GroupWithZero X] [GroupWithZero Y] (f : MonoidWithZe
roHom X Y) : of X ⟶ of Y
参数：f : MonoidWithZeroHom X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `MonoidWithZeroHom` as a morphism in `GrpWithZero`.
-/
abbrev ofHom {X Y : Type u} [GroupWithZero X] [GroupWithZero Y]
    (f : MonoidWithZeroHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom f

@[simp]
/-
**GrpWithZero.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `GrpWithZero`。
形式化陈述：hom_id {X : GrpWithZero} : ConcreteCategory.hom (𝟙 X : X ⟶ X) = MonoidWith
ZeroHom.id X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : GrpWithZero} : ConcreteCategory.hom (𝟙 X : X ⟶ X) = MonoidWithZeroHom.id X := rfl

@[simp]
/-
**GrpWithZero.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `GrpWithZero`。
形式化陈述：hom_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} : ConcreteCategory.
hom (f ≫ g) = g.comp f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} :
    ConcreteCategory.hom (f ≫ g) = g.comp f := rfl
/-
**GrpWithZero.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `GrpWithZero`。
形式化陈述：coe_id {X : GrpWithZero} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_id {X : GrpWithZero} : (𝟙 X : X → X) = id := rfl
/-
**GrpWithZero.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `GrpWithZero`。
形式化陈述：coe_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) 
= g ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl
/-
**GrpWithZero.forget_map** 是 Mathlib 中的一个定理，位于命名空间 `GrpWithZero`。
形式化陈述：∀ {X Y : GrpWithZero} (f : X ⟶ Y),   ⇑(CategoryTheory.ConcreteCategory.hom
 ((CategoryTheory.forget GrpWithZero).map f)) =     ⇑(CategoryTheory.ConcreteCat
egory.hom f)
参数：f : X ⟶ Y；CategoryTheory.ConcreteCategory.hom ((CategoryTheory.forget GrpWith
Zero).map f)；CategoryTheory.ConcreteCategory.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_map {X Y : GrpWithZero} (f : X ⟶ Y) :
    (forget GrpWithZero).map f = (f : _ → _) :=
  rfl
/-
**GrpWithZero.hasForgetToBipointed** 是 Mathlib 中的一个实例，位于命名空间 `GrpWithZero`。
形式化陈述：hasForgetToBipointed : HasForget₂ GrpWithZero Bipointed where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToBipointed : HasForget₂ GrpWithZero Bipointed where
  forget₂ :=
      { obj := fun X => ⟨X, 0, 1⟩
        map := fun f => ⟨f, f.map_zero', f.map_one'⟩ }
/-
**GrpWithZero.hasForgetToMon** 是 Mathlib 中的一个实例，位于命名空间 `GrpWithZero`。
形式化陈述：hasForgetToMon : HasForget₂ GrpWithZero MonCat where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToMon : HasForget₂ GrpWithZero MonCat where
  forget₂ :=
      { obj := fun X => MonCat.of X
        map := fun f => MonCat.ofHom f.toMonoidHom }

/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps]
/-
**GrpWithZero.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `GrpWithZero.Iso`。
形式化陈述：{α β : GrpWithZero} → α.carrier ≃* β.carrier → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of groups with zero from a group isomorphism between t
hem.
-/
def Iso.mk {α β : GrpWithZero.{u}} (e : α ≃* β) : α ≅ β where
  hom := ofHom (.ofClass e)
  inv := ofHom (.ofClass e.symm)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _

end GrpWithZero

