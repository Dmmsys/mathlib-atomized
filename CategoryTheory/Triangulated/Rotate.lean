/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Triangulated.Basic

/-!
# Rotate

This file adds the ability to rotate triangles and triangle morphisms.
It also shows that rotation gives an equivalence on the category of triangles.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasShift C ℤ]
variable (X : C)

/-- If you rotate a triangle, you get another triangle.
Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `rotate` gives a triangle of the form:
```
      g       h        -f⟦1⟧'
  Y  ───> Z  ───>  X⟦1⟧ ───> Y⟦1⟧
```
-/
@[simps!]
/-
**CategoryTheory.Pretriangulated.Triangle.rotate** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Pretriangulated.Triangle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Preadditive C] →       [inst_2 : CategoryTheory.HasShift C ℤ] →         C
ategoryTheory.Pretriangulated.Triangle C → CategoryTheory.Pretriangulated.Triang
le C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If you rotate a triangle, you get another triangle.
Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `rotate` gives a triangle of the form:
```
      g       h        -f⟦1⟧'
  Y  ───> Z  ───>  X⟦1⟧ ───> Y⟦1⟧
```
-/
def Triangle.rotate (T : Triangle C) : Triangle C :=
  Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦1⟧')

section

/-- Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `invRotate` gives a triangle that can be thought of as:
```
        -h⟦-1⟧'     f       g
  Z⟦-1⟧  ───>  X  ───> Y  ───> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `Z⟦-1⟧⟦1⟧` is
not necessarily equal to `Z`, but it is isomorphic, by the `counitIso` of `shiftEquiv C 1`)
-/
@[simps!]
/-
**CategoryTheory.Pretriangulated.Triangle.invRotate** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Pretriangulated.Triangle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Preadditive C] →       [inst_2 : CategoryTheory.HasShift C ℤ] →         C
ategoryTheory.Pretriangulated.Triangle C → CategoryTheory.Pretriangulated.Triang
le C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `invRotate` gives a triangle that can be thought of as:
```
        -h⟦-1⟧'     f       g
  Z⟦-1⟧  ───>  X  ───> Y  ───> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `
Z⟦-1⟧⟦1⟧` is
not necessarily equal to `Z`, but it is isomorphic, by the `counitIso` of `shift
Equiv C 1`)
-/
def Triangle.invRotate (T : Triangle C) : Triangle C :=
  Triangle.mk (-T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftEquiv C (1 : ℤ)).unitIso.inv.app _) (T.mor₁)
    (T.mor₂ ≫ (shiftEquiv C (1 : ℤ)).counitIso.inv.app _)

end

attribute [local simp] shift_shift_neg' shift_neg_shift'
  shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app
  shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app

variable (C)

set_option backward.defeqAttrib.useBackward true in
/-- Rotating triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
/-
**CategoryTheory.Pretriangulated.rotate** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Pretriangulated`。
形式化陈述：rotate : Triangle C ⥤ Triangle C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rotating triangles gives an endofunctor on the category of triangles in `C`.
-/
def rotate : Triangle C ⥤ Triangle C where
  obj := Triangle.rotate
  map f :=
  { hom₁ := f.hom₂
    hom₂ := f.hom₃
    hom₃ := f.hom₁⟦1⟧'
    comm₃ := by
      dsimp
      simp only [comp_neg, neg_comp, ← Functor.map_comp, f.comm₁] }

set_option backward.isDefEq.respectTransparency false in
/-- The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
/-
**CategoryTheory.Pretriangulated.invRotate** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Pretriangulated`。
形式化陈述：invRotate : Triangle C ⥤ Triangle C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse rotation of triangles gives an endofunctor on the category of triang
les in `C`.
-/
def invRotate : Triangle C ⥤ Triangle C where
  obj := Triangle.invRotate
  map f :=
  { hom₁ := f.hom₃⟦-1⟧'
    hom₂ := f.hom₁
    hom₃ := f.hom₂
    comm₁ := by
      dsimp
      simp only [comp_neg, ← Functor.map_comp_assoc, ← f.comm₃]
      rw [Functor.map_comp]
      simp }

variable {C}
variable [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]

set_option backward.isDefEq.respectTransparency false in
/-- The unit isomorphism of the auto-equivalence of categories `triangleRotation C` of
`Triangle C` given by the rotation of triangles. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.rotCompInvRot** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Pretriangulated`。
形式化陈述：rotCompInvRot : 𝟭 (Triangle C) ≅ rotate C ⋙ invRotate C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit isomorphism of the auto-equivalence of categories `triangleRotation C` 
of
`Triangle C` given by the rotation of triangles.
-/
def rotCompInvRot : 𝟭 (Triangle C) ≅ rotate C ⋙ invRotate C :=
  NatIso.ofComponents fun T => Triangle.isoMk _ _
    ((shiftEquiv C (1 : ℤ)).unitIso.app T.obj₁) (Iso.refl _) (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The counit isomorphism of the auto-equivalence of categories `triangleRotation C` of
`Triangle C` given by the rotation of triangles. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.invRotCompRot** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Pretriangulated`。
形式化陈述：invRotCompRot : invRotate C ⋙ rotate C ≅ 𝟭 (Triangle C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism of the auto-equivalence of categories `triangleRotation C
` of
`Triangle C` given by the rotation of triangles.
-/
def invRotCompRot : invRotate C ⋙ rotate C ≅ 𝟭 (Triangle C) :=
  NatIso.ofComponents fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftEquiv C (1 : ℤ)).counitIso.app T.obj₃)

set_option backward.isDefEq.respectTransparency false in
variable (C) in
/-- Rotating triangles gives an auto-equivalence on the category of triangles in `C`.
-/
@[simps]
/-
**CategoryTheory.Pretriangulated.triangleRotation** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Pretriangulated`。
形式化陈述：triangleRotation : Equivalence (Triangle C) (Triangle C) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rotating triangles gives an auto-equivalence on the category of triangles in `C`
.
-/
def triangleRotation : Equivalence (Triangle C) (Triangle C) where
  functor := rotate C
  inverse := invRotate C
  unitIso := rotCompInvRot
  counitIso := invRotCompRot
/-
**CategoryTheory.Pretriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pret
riangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (rotate C).IsEquivalence := by
  change (triangleRotation C).functor.IsEquivalence
  infer_instance
/-
**CategoryTheory.Pretriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pret
riangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (invRotate C).IsEquivalence := by
  change (triangleRotation C).inverse.IsEquivalence
  infer_instance

end CategoryTheory.Pretriangulated

