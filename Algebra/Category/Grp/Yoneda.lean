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
/--
Definition of `CommGrpCat.coyoneda` / `CommGrpCat.coyoneda` 的定义

English:
definition CommGrpCat.coyoneda
  signature: : CommGrpCatᵒᵖ ⥤ CommGrpCat ⥤ CommGrpCat where
  body: { obj N := of (M.unop ->* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

中文:
定义 CommGrpCat.coyoneda
  签名: : CommGrpCatᵒᵖ ⥤ CommGrpCat ⥤ CommGrpCat where
  定义体: { obj N := of (M.unop ->* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

Depends on / 依赖: M.unop, compHom, f.hom
-/
def CommGrpCat.coyoneda : CommGrpCatᵒᵖ ⥤ CommGrpCat ⥤ CommGrpCat where
  obj M := { obj N := of (M.unop ->* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

set_option backward.defeqAttrib.useBackward true in
/-- The `CommGrpCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/
@[to_additive (attr := simps!)
/-- The `AddCommGrpCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/]
/--
Definition of `CommGrpCat.coyonedaForget` / `CommGrpCat.coyonedaForget` 的定义

English:
definition CommGrpCat.coyonedaForget
  signature: :
  body: dsimp% NatIso.ofComponents fun X => NatIso.ofComponents fun Y => {
    hom := ↾fun f => ofHom f,
    inv := ↾fun f => f.hom }

中文:
定义 CommGrpCat.coyonedaForget
  签名: :
  定义体: dsimp% NatIso.ofComponents fun X => NatIso.ofComponents fun Y => {
    hom := ↾fun f => ofHom f,
    inv := ↾fun f => f.hom }

Depends on / 依赖: NatIso, NatIso.ofComponents, f.hom, ofComponents
-/
def CommGrpCat.coyonedaForget :
    coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  dsimp% NatIso.ofComponents fun X => NatIso.ofComponents fun Y => {
    hom := ↾fun f => ofHom f,
    inv := ↾fun f => f.hom }

/-- The Hom bifunctor sending a type `X` and a commutative group `G` to the commutative group
`X → G` with pointwise operations.

This is also the coyoneda embedding of `Type` into `CommGrpCat`-valued presheaves of commutative
groups. -/
@[to_additive (attr := simps)
/-- The Hom bifunctor sending a type `X` and a commutative group `G` to the commutative group
`X → G` with pointwise operations.

This is also the coyoneda embedding of `Type` into `AddCommGrpCat`-valued presheaves of commutative
groups. -/]
/--
Definition of `CommGrpCat.coyonedaType` / `CommGrpCat.coyonedaType` 的定义

English:
definition CommGrpCat.coyonedaType
  signature: : (Type u)ᵒᵖ ⥤ CommGrpCat.{u} ⥤ CommGrpCat.{u} where
  body: { obj G := of <| X.unop -> G
map f := ofHom MonoidHom.pi fun i => f.hom.comp Pi.evalMonoidHom _ i }
  map f := { app G := ofHom <| MonoidHom.pi fun i => Pi.evalMonoidHom _ <| f.unop i }

中文:
定义 CommGrpCat.coyonedaType
  签名: : (类型u)ᵒᵖ ⥤ CommGrpCat.{u} ⥤ CommGrpCat.{u} where
  定义体: { obj G := of <| X.unop -> G
map f := ofHom MonoidHom.pi fun i => f.hom.comp Pi.evalMonoidHom _ i }
  map f := { app G := ofHom <| MonoidHom.pi fun i => Pi.evalMonoidHom _ <| f.unop i }

Depends on / 依赖: X.unop
-/
def CommGrpCat.coyonedaType : (Type u)ᵒᵖ ⥤ CommGrpCat.{u} ⥤ CommGrpCat.{u} where
  obj X := { obj G := of <| X.unop -> G
map f := ofHom MonoidHom.pi fun i => f.hom.comp Pi.evalMonoidHom _ i }
  map f := { app G := ofHom <| MonoidHom.pi fun i => Pi.evalMonoidHom _ <| f.unop i }
