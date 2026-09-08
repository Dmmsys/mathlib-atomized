/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Objects of a category up to an isomorphism

`IsIsomorphic X Y := Nonempty (X ≅ Y)` is an equivalence relation on the objects of a category.
The quotient with respect to this relation defines a functor from our category to `Type`.
-/

@[expose] public section


universe v u

namespace CategoryTheory

section Category

variable {C : Type u} [Category.{v} C]

/-- An object `X` is isomorphic to an object `Y` if `X ≅ Y` is nonempty. -/
/-
**CategoryTheory.IsIsomorphic** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsIsomorphic : C -> C -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` is isomorphic to an object `Y` if `X ≅ Y` is nonempty.
-/
def IsIsomorphic : C → C → Prop := fun X Y => Nonempty (X ≅ Y)

variable (C)

/-- `IsIsomorphic` defines a setoid. -/
@[instance_reducible]
/-
**CategoryTheory.isIsomorphicSetoid** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：isIsomorphicSetoid : Setoid C where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsIsomorphic` defines a setoid.
-/
def isIsomorphicSetoid : Setoid C where
  r := IsIsomorphic
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨α⟩ => ⟨α.symm⟩, fun ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩

end Category

/-- The functor that sends each category to the quotient space of its objects up to an isomorphism.
-/
/-
**CategoryTheory.isomorphismClasses** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：isomorphismClasses : Cat.{v, u} ⥤ Type u where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor that sends each category to the quotient space of its objects up to 
an isomorphism.
-/
def isomorphismClasses : Cat.{v, u} ⥤ Type u where
  obj C := Quotient (isIsomorphicSetoid C.α)
  map {_ _} F := ↾(Quot.map F.toFunctor.obj fun _ _ ⟨f⟩ => ⟨F.toFunctor.mapIso f⟩)
  map_id {C} := by  -- Porting note: this used to be `tidy`
    ext x
    apply @Quot.recOn _ _ _ x
    all_goals cat_disch
  map_comp {C D E} f g := by -- Porting note(s): idem
    ext x
    apply @Quot.recOn _ _ _ x
    all_goals cat_disch
/-
**CategoryTheory.Groupoid.isIsomorphic_iff_nonempty_hom** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Groupoid`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] {X Y : C}, CategoryTheor
y.IsIsomorphic X Y ↔ Nonempty (X ⟶ Y)
参数：X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
-/
theorem Groupoid.isIsomorphic_iff_nonempty_hom {C : Type u} [Groupoid.{v} C] {X Y : C} :
    IsIsomorphic X Y ↔ Nonempty (X ⟶ Y) :=
  (Groupoid.isoEquivHom X Y).nonempty_congr

end CategoryTheory

