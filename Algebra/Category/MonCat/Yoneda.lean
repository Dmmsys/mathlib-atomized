/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.CategoryTheory.Yoneda

/-!
# Yoneda embeddings

This file defines a few Yoneda embeddings for the category of commutative monoids.
-/

@[expose] public section

open CategoryTheory

universe u

/-- The `CommMonCat`-valued coyoneda embedding. -/
@[to_additive (attr := simps)
/-- The `AddCommMonCat`-valued coyoneda embedding. -/]
/-
**CommMonCat.coyoneda** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommMonCat.coyoneda : CommMonCatᵒᵖ ⥤ CommMonCat ⥤ CommMonCat where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def CommMonCat.coyoneda : CommMonCatᵒᵖ ⥤ CommMonCat ⥤ CommMonCat where
  obj M := { obj N := of (M.unop →* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

set_option backward.defeqAttrib.useBackward true in
/-- The `CommMonCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/
@[to_additive (attr := simps!)
/-- The `AddCommMonCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/]
/-
**CommMonCat.coyonedaForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommMonCat.coyonedaForget : coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj
 (forget _) ≅ CategoryTheory.coyoneda
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def CommMonCat.coyonedaForget :
    coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  dsimp% NatIso.ofComponents fun X ↦ NatIso.ofComponents fun Y ↦ {
    hom := ↾fun f ↦ ofHom f
    inv := ↾fun f ↦ f.hom }

/-- The Hom bifunctor sending a type `X` and a commutative monoid `M` to the commutative monoid
`X → M` with pointwise operations.

This is also the coyoneda embedding of `Type` into `CommMonCat`-valued presheaves of commutative
monoids. -/
@[to_additive (attr := simps)
/-- The Hom bifunctor sending a type `X` and a commutative monoid `M` to the commutative monoid
`X → M` with pointwise operations.

This is also the coyoneda embedding of `Type` into `AddCommMonCat`-valued presheaves of commutative
monoids. -/]
/-
**CommMonCat.coyonedaType** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommMonCat.coyonedaType : Type uᵒᵖ ⥤ CommMonCat.{u} ⥤ CommMonCat.{u} where
 obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def CommMonCat.coyonedaType : Type uᵒᵖ ⥤ CommMonCat.{u} ⥤ CommMonCat.{u} where
  obj X := { obj M := of <| X.unop → M
             map f := ofHom <| MonoidHom.pi fun i ↦ f.hom.comp <| Pi.evalMonoidHom _ i }
  map f := { app N := ofHom <| MonoidHom.pi fun i ↦ Pi.evalMonoidHom _ <| f.unop i }
