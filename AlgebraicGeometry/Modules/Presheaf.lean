/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The category of presheaves of modules over a scheme

In this file, given a scheme `X`, we define the category of presheaves
of modules over `X`. As categories of presheaves of modules are
defined for presheaves of rings (and not presheaves of commutative rings),
we also introduce a definition `X.ringCatSheaf` for the underlying sheaf
of rings of `X`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X Y : Scheme.{u})

/--
Definition of `ringCatSheaf` / `ringCatSheaf` 的定义

English:
abbreviation ringCatSheaf
  signature: : TopCat.Sheaf RingCat.{u} X
  body: (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

中文:
缩写 ringCatSheaf
  签名: : 顶元素范畴.层 环范畴.{u} X
  定义体: (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

Depends on / 依赖: CommRingCat, RingCat, X.sheaf, sheafCompose
-/
abbrev ringCatSheaf : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of presheaves of modules over a scheme. -/
nonrec abbrev PresheafOfModules := PresheafOfModules.{u} X.ringCatSheaf.obj

variable {X Y} in
/--
Definition of `Hom.toRingCatSheafHom` / `Hom.toRingCatSheafHom` 的定义

English:
definition Hom.toRingCatSheafHom
  signature: (f : X ⟶ Y)
  body: Functor.whiskerRight f.c _

中文:
定义 态射.toRingCatSheafHom
  签名: (f : X ⟶ Y)
  定义体: Functor.whiskerRight f.c _

Depends on / 依赖: Functor, Functor.whiskerRight, whiskerRight
-/
def Hom.toRingCatSheafHom (f : X ⟶ Y) :
    Y.ringCatSheaf ⟶ ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      _ _ _).obj X.ringCatSheaf where
  hom := Functor.whiskerRight f.c _

end AlgebraicGeometry.Scheme
