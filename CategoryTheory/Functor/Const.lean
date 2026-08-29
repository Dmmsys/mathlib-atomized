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
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: : C ⥤ J ⥤ C where
  body: { obj := fun _ => X
      map := fun _ => 𝟙 X }
  map {X Y} f := { app := fun _ => f }

中文:
定义 const
  签名: : C ⥤ J ⥤ C where
  定义体: { obj := fun _ => X
      map := fun _ => 𝟙 X }
  map {X Y} f := { app := fun _ => f }
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
/--
Definition of `opObjOp` / `opObjOp` 的定义

English:
definition opObjOp
  signature: (X : C)
  body: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

中文:
定义 opObjOp
  签名: (X : C)
  定义体: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
-/
def opObjOp (X : C) : (const Jᵒᵖ).obj (op X) ≅ ((const J).obj X).op where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `opObjUnop` / `opObjUnop` 的定义

English:
definition opObjUnop
  signature: (X : Cᵒᵖ)
  body: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

中文:
定义 opObjUnop
  签名: (X : Cᵒᵖ)
  定义体: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
-/
def opObjUnop (X : Cᵒᵖ) : (const Jᵒᵖ).obj (unop X) ≅ ((const J).obj X).leftOp where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

-- Lean needs some help with universes here.
@[simp]
/--
theorem `opObjUnop_hom_app` / 定理 `opObjUnop_hom_app`

English:
theorem opObjUnop_hom_app
  given: (X : Cᵒᵖ) (j : Jᵒᵖ)
  statement: (opObjUnop.{v₁, v₂} X).hom.app j = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 opObjUnop_hom_app
  条件: (X : Cᵒᵖ) (j : Jᵒᵖ)
  结论: (opObjUnop.{v₁, v₂} X).hom.app j = 𝟙 _
  证明: rfl

@[simp]
-/
theorem opObjUnop_hom_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).hom.app j = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `opObjUnop_inv_app` / 定理 `opObjUnop_inv_app`

English:
theorem opObjUnop_inv_app
  given: (X : Cᵒᵖ) (j : Jᵒᵖ)
  statement: (opObjUnop.{v₁, v₂} X).inv.app j = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 opObjUnop_inv_app
  条件: (X : Cᵒᵖ) (j : Jᵒᵖ)
  结论: (opObjUnop.{v₁, v₂} X).inv.app j = 𝟙 _
  证明: rfl

@[simp]
-/
theorem opObjUnop_inv_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).inv.app j = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `unop_functor_op_obj_map` / 定理 `unop_functor_op_obj_map`

English:
theorem unop_functor_op_obj_map
  given: (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂)
  proof: rfl

中文:
定理 unop_functor_op_obj_map
  条件: (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂)
  证明: rfl
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
/--
Definition of `constComp` / `constComp` 的定义

English:
definition constComp
  signature: (X : C) (F : C ⥤ D)
  body: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

中文:
定义 constComp
  签名: (X : C) (F : C ⥤ D)
  定义体: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
-/
def constComp (X : C) (F : C ⥤ D) : (const J).obj X ⋙ F ≅ (const J).obj (F.obj X) where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: J] : Faithful (const J
  body: NatTrans.congr_app e (Classical.arbitrary J)

中文:
实例 [非空
  签名: J] : 忠实 (const J
  定义体: NatTrans.congr_app e (Classical.arbitrary J)

Depends on / 依赖: Classical, Classical.arbitrary, NatTrans, NatTrans.congr_app, arbitrary, congr_app
-/
instance [Nonempty J] : Faithful (const J : C ⥤ J ⥤ C) where
  map_injective e := NatTrans.congr_app e (Classical.arbitrary J)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism
`F ⋙ Functor.const J ≅ Functor.const F ⋙ (whiskeringRight J _ _).obj L`. -/
@[simps!]
/--
Definition of `compConstIso` / `compConstIso` 的定义

English:
definition compConstIso
  signature: (F : C ⥤ D)
  body: NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (by cat_disch)

中文:
定义 compConstIso
  签名: (F : C ⥤ D)
  定义体: NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, cat_disch, ofComponents
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
/--
Definition of `constCompWhiskeringLeftIso` / `constCompWhiskeringLeftIso` 的定义

English:
definition constCompWhiskeringLeftIso
  signature: (F : J ⥤ D)
  body: NatIso.ofComponents fun X => NatIso.ofComponents fun Y => Iso.refl _

中文:
定义 constCompWhiskeringLeftIso
  签名: (F : J ⥤ D)
  定义体: NatIso.ofComponents fun X => NatIso.ofComponents fun Y => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def constCompWhiskeringLeftIso (F : J ⥤ D) :
    const D ⋙ (whiskeringLeft J D C).obj F ≅ const J :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => Iso.refl _

end

end CategoryTheory.Functor
