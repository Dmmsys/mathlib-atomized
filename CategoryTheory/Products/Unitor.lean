/-
Copyright (c) 2024 Shanghe Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanghe Chen
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The left/right unitor equivalences `1 × C ≌ C` and `C × 1 ≌ C`.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory.prod

open scoped CategoryTheory.Prod

variable (C : Type u) [Category.{v} C]

/-- The left unitor functor `1 × C ⥤ C` -/
@[simps]
/-
**CategoryTheory.prod.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.prod`
。
形式化陈述：leftUnitor : Discrete (PUnit : Type w) × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left unitor functor `1 × C ⥤ C`
-/
def leftUnitor : Discrete (PUnit : Type w) × C ⥤ C where
  obj X := X.2
  map f := f.2

/-- The right unitor functor `C × 1 ⥤ C` -/
@[simps]
/-
**CategoryTheory.prod.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.prod
`。
形式化陈述：rightUnitor : C × Discrete (PUnit : Type w) ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right unitor functor `C × 1 ⥤ C`
-/
def rightUnitor : C × Discrete (PUnit : Type w) ⥤ C where
  obj X := X.1
  map f := f.1

/-- The left inverse unitor `C ⥤ 1 × C` -/
@[simps]
/-
**CategoryTheory.prod.leftInverseUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.prod`。
形式化陈述：leftInverseUnitor : C ⥤ Discrete (PUnit : Type w) × C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left inverse unitor `C ⥤ 1 × C`
-/
def leftInverseUnitor : C ⥤ Discrete (PUnit : Type w) × C where
  obj X := ⟨⟨PUnit.unit⟩, X⟩
  map f := 𝟙 _ ×ₘ f

/-- The right inverse unitor `C ⥤ C × 1` -/
@[simps]
/-
**CategoryTheory.prod.rightInverseUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.prod`。
形式化陈述：rightInverseUnitor : C ⥤ C × Discrete (PUnit : Type w) where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inverse unitor `C ⥤ C × 1`
-/
def rightInverseUnitor : C ⥤ C × Discrete (PUnit : Type w) where
  obj X := ⟨X, ⟨PUnit.unit⟩⟩
  map f := f ×ₘ 𝟙 _

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories expressing left unity of products of categories. -/
@[simps]
/-
**CategoryTheory.prod.leftUnitorEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.prod`。
形式化陈述：leftUnitorEquivalence : Discrete (PUnit : Type w) × C ≌ C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories expressing left unity of products of categories.
-/
def leftUnitorEquivalence : Discrete (PUnit : Type w) × C ≌ C where
  functor := leftUnitor C
  inverse := leftInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories expressing right unity of products of categories. -/
@[simps]
/-
**CategoryTheory.prod.rightUnitorEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.prod`。
形式化陈述：rightUnitorEquivalence : C × Discrete (PUnit : Type w) ≌ C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories expressing right unity of products of categories.
-/
def rightUnitorEquivalence : C × Discrete (PUnit : Type w) ≌ C where
  functor := rightUnitor C
  inverse := rightInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _
/-
**CategoryTheory.prod.leftUnitor_isEquivalence** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.prod`。
形式化陈述：leftUnitor_isEquivalence : (leftUnitor C).IsEquivalence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance leftUnitor_isEquivalence : (leftUnitor C).IsEquivalence :=
  (leftUnitorEquivalence C).isEquivalence_functor
/-
**CategoryTheory.prod.rightUnitor_isEquivalence** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.prod`。
形式化陈述：rightUnitor_isEquivalence : (rightUnitor C).IsEquivalence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance rightUnitor_isEquivalence : (rightUnitor C).IsEquivalence :=
  (rightUnitorEquivalence C).isEquivalence_functor

end CategoryTheory.prod

