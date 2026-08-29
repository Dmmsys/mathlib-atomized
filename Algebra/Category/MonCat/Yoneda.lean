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
/--
Definition of `CommMonCat.coyoneda` / `CommMonCat.coyoneda` 的定义

English:
definition CommMonCat.coyoneda
  signature: : CommMonCatᵒᵖ ⥤ CommMonCat ⥤ CommMonCat where
  body: { obj N := of (M.unop ->* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

中文:
定义 交换幺半群范畴.coyoneda
  签名: : CommMonCatᵒᵖ ⥤ 交换幺半群范畴 ⥤ 交换幺半群范畴 where
  定义体: { obj N := of (M.unop ->* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

Depends on / 依赖: M.unop, compHom, f.hom
-/
def CommMonCat.coyoneda : CommMonCatᵒᵖ ⥤ CommMonCat ⥤ CommMonCat where
  obj M := { obj N := of (M.unop ->* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

set_option backward.defeqAttrib.useBackward true in
/-- The `CommMonCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/
@[to_additive (attr := simps!)
/-- The `AddCommMonCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/]
/--
Definition of `CommMonCat.coyonedaForget` / `CommMonCat.coyonedaForget` 的定义

English:
definition CommMonCat.coyonedaForget
  signature: :
  body: dsimp% NatIso.ofComponents fun X => NatIso.ofComponents fun Y => {
    hom := ↾fun f => ofHom f
    inv := ↾fun f => f.hom }

中文:
定义 交换幺半群范畴.coyonedaForget
  签名: :
  定义体: dsimp% NatIso.ofComponents fun X => NatIso.ofComponents fun Y => {
    hom := ↾fun f => ofHom f
    inv := ↾fun f => f.hom }

Depends on / 依赖: NatIso, NatIso.ofComponents, f.hom, ofComponents
-/
def CommMonCat.coyonedaForget :
    coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  dsimp% NatIso.ofComponents fun X => NatIso.ofComponents fun Y => {
    hom := ↾fun f => ofHom f
    inv := ↾fun f => f.hom }

/-- The Hom bifunctor sending a type `X` and a commutative monoid `M` to the commutative monoid
`X → M` with pointwise operations.

This is also the coyoneda embedding of `Type` into `CommMonCat`-valued presheaves of commutative
monoids. -/
@[to_additive (attr := simps)
/-- The Hom bifunctor sending a type `X` and a commutative monoid `M` to the commutative monoid
`X → M` with pointwise operations.

This is also the coyoneda embedding of `Type` into `AddCommMonCat`-valued presheaves of commutative
monoids. -/]
/--
Definition of `CommMonCat.coyonedaType` / `CommMonCat.coyonedaType` 的定义

English:
definition CommMonCat.coyonedaType
  signature: : Type uᵒᵖ ⥤ CommMonCat.{u} ⥤ CommMonCat.{u} where
  body: { obj M := of <| X.unop -> M
map f := ofHom MonoidHom.pi fun i => f.hom.comp Pi.evalMonoidHom _ i }
  map f := { app N := ofHom <| MonoidHom.pi fun i => Pi.evalMonoidHom _ <| f.unop i }

中文:
定义 交换幺半群范畴.coyonedaType
  签名: : 类型uᵒᵖ ⥤ 交换幺半群范畴.{u} ⥤ 交换幺半群范畴.{u} where
  定义体: { obj M := of <| X.unop -> M
map f := ofHom MonoidHom.pi fun i => f.hom.comp Pi.evalMonoidHom _ i }
  map f := { app N := ofHom <| MonoidHom.pi fun i => Pi.evalMonoidHom _ <| f.unop i }

Depends on / 依赖: X.unop
-/
def CommMonCat.coyonedaType : Type uᵒᵖ ⥤ CommMonCat.{u} ⥤ CommMonCat.{u} where
  obj X := { obj M := of <| X.unop -> M
map f := ofHom MonoidHom.pi fun i => f.hom.comp Pi.evalMonoidHom _ i }
  map f := { app N := ofHom <| MonoidHom.pi fun i => Pi.evalMonoidHom _ <| f.unop i }
