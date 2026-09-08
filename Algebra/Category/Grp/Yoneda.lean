/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.CategoryTheory.Yoneda

/-!
# Yoneda embeddings

This file defines a few Yoneda embeddings for the category of commutative groups.
-/

@[expose] public section

open CategoryTheory

universe u

/-- The `CommGrpCat`-valued coyoneda embedding. -/
@[to_additive (attr := simps) /-- The `AddCommGrpCat`-valued coyoneda embedding. -/]
/-
**CommGrpCat.coyoneda** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommGrpCat.coyoneda : CommGrpCatᵒᵖ ⥤ CommGrpCat ⥤ CommGrpCat where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CommGrpCat`-valued coyoneda embedding.
-/
def CommGrpCat.coyoneda : CommGrpCatᵒᵖ ⥤ CommGrpCat ⥤ CommGrpCat where
  obj M := { obj N := of (M.unop →* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

set_option backward.defeqAttrib.useBackward true in
/-- The `CommGrpCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/
@[to_additive (attr := simps!)
/-- The `AddCommGrpCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/]
/-
**CommGrpCat.coyonedaForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommGrpCat.coyonedaForget : coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj
 (forget _) ≅ CategoryTheory.coyoneda
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def CommGrpCat.coyonedaForget :
    coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  dsimp% NatIso.ofComponents fun X ↦ NatIso.ofComponents fun Y ↦ {
    hom := ↾fun f ↦ ofHom f,
    inv := ↾fun f ↦ f.hom }

/-- The Hom bifunctor sending a type `X` and a commutative group `G` to the commutative group
`X → G` with pointwise operations.

This is also the coyoneda embedding of `Type` into `CommGrpCat`-valued presheaves of commutative
groups. -/
@[to_additive (attr := simps)
/-- The Hom bifunctor sending a type `X` and a commutative group `G` to the commutative group
`X → G` with pointwise operations.

This is also the coyoneda embedding of `Type` into `AddCommGrpCat`-valued presheaves of commutative
groups. -/]
/-
**CommGrpCat.coyonedaType** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommGrpCat.coyonedaType : (Type u)ᵒᵖ ⥤ CommGrpCat.{u} ⥤ CommGrpCat.{u} whe
re obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def CommGrpCat.coyonedaType : (Type u)ᵒᵖ ⥤ CommGrpCat.{u} ⥤ CommGrpCat.{u} where
  obj X := { obj G := of <| X.unop → G
             map f := ofHom <| MonoidHom.pi fun i ↦ f.hom.comp <| Pi.evalMonoidHom _ i }
  map f := { app G := ofHom <| MonoidHom.pi fun i ↦ Pi.evalMonoidHom _ <| f.unop i }
