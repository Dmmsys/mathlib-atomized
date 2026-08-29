/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The Yoneda embedding for `R`-linear categories

The Yoneda embedding for `R`-linear categories `C`,
sends an object `X : C` to the `ModuleCat R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `ModuleCat.of R (unop Y ⟶ X)`.

TODO: `linearYoneda R C` is `R`-linear.
TODO: In fact, `linearYoneda` itself is additive and `R`-linear.
-/

@[expose] public section


universe w v u

open Opposite CategoryTheory.Functor

namespace CategoryTheory

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable (C)

/-- The Yoneda embedding for `R`-linear categories `C`
sending an object `X : C` to the `ModuleCat R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `ModuleCat.of R (unop Y ⟶ X)`. -/
@[simps]
/--
Definition of `linearYoneda` / `linearYoneda` 的定义

English:
definition linearYoneda
  signature: : C ⥤ Cᵒᵖ ⥤ ModuleCat R where
  body: { obj := fun Y => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.leftComp R _ f.unop) }
  map {X₁ X₂} f :=
    { app := fun Y => @ModuleCat.ofHom R _ (Y.unop ⟶ X₁) (Y.unop ⟶ X₂) _ _ _ _
        (Linear.rightComp R _ f) }

中文:
定义 linearYoneda
  签名: : C ⥤ Cᵒᵖ ⥤ ModuleCat R where
  定义体: { obj := fun Y => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.leftComp R _ f.unop) }
  map {X₁ X₂} f :=
    { app := fun Y => @ModuleCat.ofHom R _ (Y.unop ⟶ X₁) (Y.unop ⟶ X₂) _ _ _ _
        (Linear.rightComp R _ f) }

Depends on / 依赖: Linear, Linear.leftComp, Linear.rightComp, ModuleCat, ModuleCat.of, ModuleCat.ofHom, Y.unop, f.unop, leftComp, rightComp
-/
def linearYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat R where
  obj X :=
    { obj := fun Y => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.leftComp R _ f.unop) }
  map {X₁ X₂} f :=
    { app := fun Y => @ModuleCat.ofHom R _ (Y.unop ⟶ X₁) (Y.unop ⟶ X₂) _ _ _ _
        (Linear.rightComp R _ f) }

/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `Y : Cᵒᵖ` to the `ModuleCat R`-valued copresheaf on `C`,
with value on `X : C` given by `ModuleCat.of R (unop Y ⟶ X)`. -/
@[simps]
/--
Definition of `linearCoyoneda` / `linearCoyoneda` 的定义

English:
definition linearCoyoneda
  signature: : Cᵒᵖ ⥤ C ⥤ ModuleCat R where
  body: { obj := fun X => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.rightComp R _ f) }
  map {Y₁ Y₂} f :=
    { app := fun X => @ModuleCat.ofHom R _ (unop Y₁ ⟶ X) (unop Y₂ ⟶ X) _ _ _ _
        (Linear.leftComp _ _ f.unop) }

中文:
定义 linearCoyoneda
  签名: : Cᵒᵖ ⥤ C ⥤ ModuleCat R where
  定义体: { obj := fun X => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.rightComp R _ f) }
  map {Y₁ Y₂} f :=
    { app := fun X => @ModuleCat.ofHom R _ (unop Y₁ ⟶ X) (unop Y₂ ⟶ X) _ _ _ _
        (Linear.leftComp _ _ f.unop) }

Depends on / 依赖: Linear, Linear.leftComp, Linear.rightComp, ModuleCat, ModuleCat.of, ModuleCat.ofHom, f.unop, leftComp, rightComp
-/
def linearCoyoneda : Cᵒᵖ ⥤ C ⥤ ModuleCat R where
  obj Y :=
    { obj := fun X => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.rightComp R _ f) }
  map {Y₁ Y₂} f :=
    { app := fun X => @ModuleCat.ofHom R _ (unop Y₁ ⟶ X) (unop Y₂ ⟶ X) _ _ _ _
        (Linear.leftComp _ _ f.unop) }

/--
Instance `linearYoneda_obj_additive` / 实例 `linearYoneda_obj_additive`

English:
instance linearYoneda_obj_additive
  signature: (X : C)

中文:
实例 linearYoneda_obj_additive
  签名: (X : C)
-/
instance linearYoneda_obj_additive (X : C) : ((linearYoneda R C).obj X).Additive where

/--
Instance `linearCoyoneda_obj_additive` / 实例 `linearCoyoneda_obj_additive`

English:
instance linearCoyoneda_obj_additive
  signature: (Y : Cᵒᵖ)

中文:
实例 linearCoyoneda_obj_additive
  签名: (Y : Cᵒᵖ)
-/
instance linearCoyoneda_obj_additive (Y : Cᵒᵖ) : ((linearCoyoneda R C).obj Y).Additive where

@[simp]
/--
theorem `whiskering_linearYoneda` / 定理 `whiskering_linearYoneda`

English:
theorem whiskering_linearYoneda
  proof: rfl

@[simp]

中文:
定理 whiskering_linearYoneda
  证明: rfl

@[simp]
-/
theorem whiskering_linearYoneda :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = yoneda :=
  rfl

@[simp]
/--
theorem `whiskering_linearYoneda₂` / 定理 `whiskering_linearYoneda₂`

English:
theorem whiskering_linearYoneda₂
  proof: rfl

@[simp]

中文:
定理 whiskering_linearYoneda₂
  证明: rfl

@[simp]
-/
theorem whiskering_linearYoneda₂ :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) =
      preadditiveYoneda :=
  rfl

@[simp]
/--
theorem `whiskering_linearCoyoneda` / 定理 `whiskering_linearCoyoneda`

English:
theorem whiskering_linearCoyoneda
  proof: rfl

@[simp]

中文:
定理 whiskering_linearCoyoneda
  证明: rfl

@[simp]
-/
theorem whiskering_linearCoyoneda :
    linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = coyoneda :=
  rfl

@[simp]
/--
theorem `whiskering_linearCoyoneda₂` / 定理 `whiskering_linearCoyoneda₂`

English:
theorem whiskering_linearCoyoneda₂
  proof: rfl

中文:
定理 whiskering_linearCoyoneda₂
  证明: rfl
-/
theorem whiskering_linearCoyoneda₂ :
    linearCoyoneda R C ⋙
        (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) =
      preadditiveCoyoneda :=
  rfl

/--
Instance `full_linearYoneda` / 实例 `full_linearYoneda`

English:
instance full_linearYoneda
  signature: : (linearYoneda R C).Full
  body: let _ : Functor.Full (linearYoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Yoneda.yoneda_full
  Functor.Full.of_comp_faithful (linearYoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))

中文:
实例 full_linearYoneda
  签名: : (linearYoneda R C).Full
  定义体: let _ : Functor.Full (linearYoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Yoneda.yoneda_full
  Functor.Full.of_comp_faithful (linearYoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))

Depends on / 依赖: Functor, Functor.Full, Functor.Full.of_comp_faithful, ModuleCat, Yoneda, Yoneda.yoneda_full, forget, linearYoneda, of_comp_faithful, whiskeringRight, yoneda_full
-/
instance full_linearYoneda : (linearYoneda R C).Full :=
  let _ : Functor.Full (linearYoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Yoneda.yoneda_full
  Functor.Full.of_comp_faithful (linearYoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))

/--
Instance `full_linearCoyoneda` / 实例 `full_linearCoyoneda`

English:
instance full_linearCoyoneda
  signature: : (linearCoyoneda R C).Full
  body: let _ : Functor.Full (linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful (linearCoyoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))

中文:
实例 full_linearCoyoneda
  签名: : (linearCoyoneda R C).Full
  定义体: let _ : Functor.Full (linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful (linearCoyoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))

Depends on / 依赖: Coyoneda, Coyoneda.coyoneda_full, Functor, Functor.Full, Functor.Full.of_comp_faithful, ModuleCat, coyoneda_full, forget, linearCoyoneda, of_comp_faithful, whiskeringRight
-/
instance full_linearCoyoneda : (linearCoyoneda R C).Full :=
  let _ : Functor.Full (linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful (linearCoyoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))

/--
Instance `faithful_linearYoneda` / 实例 `faithful_linearYoneda`

English:
instance faithful_linearYoneda
  signature: : (linearYoneda R C).Faithful
  body: Functor.Faithful.of_comp_eq (whiskering_linearYoneda R C)

中文:
实例 faithful_linearYoneda
  签名: : (linearYoneda R C).Faithful
  定义体: Functor.Faithful.of_comp_eq (whiskering_linearYoneda R C)

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_comp_eq, of_comp_eq, whiskering_linearYoneda
-/
instance faithful_linearYoneda : (linearYoneda R C).Faithful :=
  Functor.Faithful.of_comp_eq (whiskering_linearYoneda R C)

/--
Instance `faithful_linearCoyoneda` / 实例 `faithful_linearCoyoneda`

English:
instance faithful_linearCoyoneda
  signature: : (linearCoyoneda R C).Faithful
  body: Functor.Faithful.of_comp_eq (whiskering_linearCoyoneda R C)

中文:
实例 faithful_linearCoyoneda
  签名: : (linearCoyoneda R C).Faithful
  定义体: Functor.Faithful.of_comp_eq (whiskering_linearCoyoneda R C)

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_comp_eq, of_comp_eq, whiskering_linearCoyoneda
-/
instance faithful_linearCoyoneda : (linearCoyoneda R C).Faithful :=
  Functor.Faithful.of_comp_eq (whiskering_linearCoyoneda R C)

end CategoryTheory
