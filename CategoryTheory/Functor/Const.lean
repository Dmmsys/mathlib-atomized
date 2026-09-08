/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Opposites

/-!
# The constant functor

`const J : C ⥤ (J ⥤ C)` is the functor that sends an object `X : C` to the functor `J ⥤ C` sending
every object in `J` to `X`, and every morphism to `𝟙 X`.

When `J` is nonempty, `const` is faithful.

We have `(const J).obj X ⋙ F ≅ (const J).obj (F.obj X)` for any `F : C ⥤ D`.
-/

@[expose] public section

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.Functor

variable (J : Type u₁) [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]

/-- The functor sending `X : C` to the constant functor `J ⥤ C` sending everything to `X`.
-/
@[simps, implicit_reducible]
/-
**CategoryTheory.Functor.const** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：const : C ⥤ J ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending `X : C` to the constant functor `J ⥤ C` sending everything t
o `X`.
-/
def const : C ⥤ J ⥤ C where
  obj X :=
    { obj := fun _ => X
      map := fun _ => 𝟙 X }
  map {X Y} f := { app := fun _ => f }

attribute [to_dual self] const_obj_map
attribute [to_dual self (reorder := X Y)] const_map_app

namespace const

open Opposite

variable {J}

set_option backward.defeqAttrib.useBackward true in
/-- The constant functor `Jᵒᵖ ⥤ Cᵒᵖ` sending everything to `op X`
is (naturally isomorphic to) the opposite of the constant functor `J ⥤ C` sending everything to `X`.
-/
@[simps]
/-
**CategoryTheory.Functor.const.opObjOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor.const`。
形式化陈述：opObjOp (X : C) : (const Jᵒᵖ).obj (op X) ≅ ((const J).obj X).op where hom
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant functor `Jᵒᵖ ⥤ Cᵒᵖ` sending everything to `op X`
is (naturally isomorphic to) the opposite of the constant functor `J ⥤ C` sendin
g everything to `X`.
-/
def opObjOp (X : C) : (const Jᵒᵖ).obj (op X) ≅ ((const J).obj X).op where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

set_option backward.defeqAttrib.useBackward true in
/-- The constant functor `Jᵒᵖ ⥤ C` sending everything to `unop X`
is (naturally isomorphic to) the opposite of
the constant functor `J ⥤ Cᵒᵖ` sending everything to `X`.
-/
/-
**CategoryTheory.Functor.const.opObjUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor.const`。
形式化陈述：opObjUnop (X : Cᵒᵖ) : (const Jᵒᵖ).obj (unop X) ≅ ((const J).obj X).leftOp 
where hom
参数：X : Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant functor `Jᵒᵖ ⥤ C` sending everything to `unop X`
is (naturally isomorphic to) the opposite of
the constant functor `J ⥤ Cᵒᵖ` sending everything to `X`.
-/
def opObjUnop (X : Cᵒᵖ) : (const Jᵒᵖ).obj (unop X) ≅ ((const J).obj X).leftOp where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

-- Lean needs some help with universes here.
@[simp]
/-
**CategoryTheory.Functor.const.opObjUnop_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor.const`。
形式化陈述：opObjUnop_hom_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).hom.app j =
 𝟙 _
参数：X : Cᵒᵖ；j : Jᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem opObjUnop_hom_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).hom.app j = 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.const.opObjUnop_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor.const`。
形式化陈述：opObjUnop_inv_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).inv.app j =
 𝟙 _
参数：X : Cᵒᵖ；j : Jᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem opObjUnop_inv_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).inv.app j = 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.const.unop_functor_op_obj_map** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.const`。
形式化陈述：unop_functor_op_obj_map (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂) : (unop ((Func
tor.op (const J)).obj X)).map f = 𝟙 (unop X)
参数：X : Cᵒᵖ；f : j₁ ⟶ j₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_functor_op_obj_map (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    (unop ((Functor.op (const J)).obj X)).map f = 𝟙 (unop X) :=
  rfl

end const

section

variable {D : Type u₃} [Category.{v₃} D]

set_option backward.defeqAttrib.useBackward true in
/-- These are actually equal, of course, but not definitionally equal
  (the equality requires `F.map (𝟙 _) = 𝟙 _`). A natural isomorphism is
  more convenient than an equality between functors (compare id_to_iso). -/
@[simps]
/-
**CategoryTheory.Functor.constComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：constComp (X : C) (F : C ⥤ D) : (const J).obj X ⋙ F ≅ (const J).obj (F.obj
 X) where hom
参数：X : C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These are actually equal, of course, but not definitionally equal
  (the equality requires `F.map (𝟙 _) = 𝟙 _`). A natural isomorphism is
  more convenient than an equality between functors (compare id_to_iso).
-/
def constComp (X : C) (F : C ⥤ D) : (const J).obj X ⋙ F ≅ (const J).obj (F.obj X) where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

/-- If `J` is nonempty, then the constant functor over `J` is faithful. -/
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `J` is nonempty, then the constant functor over `J` is faithful.
-/
instance [Nonempty J] : Faithful (const J : C ⥤ J ⥤ C) where
  map_injective e := NatTrans.congr_app e (Classical.arbitrary J)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism
`F ⋙ Functor.const J ≅ Functor.const F ⋙ (whiskeringRight J _ _).obj L`. -/
@[simps!]
/-
**CategoryTheory.Functor.compConstIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：compConstIso (F : C ⥤ D) : F ⋙ Functor.const J ≅ Functor.const J ⋙ (whiske
ringRight J C D).obj F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism
`F ⋙ Functor.const J ≅ Functor.const F ⋙ (whiskeringRight J _ _).obj L`.
-/
def compConstIso (F : C ⥤ D) :
    F ⋙ Functor.const J ≅ Functor.const J ⋙ (whiskeringRight J C D).obj F :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism
`const D ⋙ (whiskeringLeft J _ _).obj F ≅ const J` -/
@[simps!]
/-
**CategoryTheory.Functor.constCompWhiskeringLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：constCompWhiskeringLeftIso (F : J ⥤ D) : const D ⋙ (whiskeringLeft J D C).
obj F ≅ const J
参数：F : J ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism
`const D ⋙ (whiskeringLeft J _ _).obj F ≅ const J`
-/
def constCompWhiskeringLeftIso (F : J ⥤ D) :
    const D ⋙ (whiskeringLeft J D C).obj F ≅ const J :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => Iso.refl _

end

end CategoryTheory.Functor

