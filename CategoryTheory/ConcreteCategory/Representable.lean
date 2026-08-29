/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.ConcreteCategory.Forget

/-!

# Representable functors in concrete categories

This file provides some API for the situation `(F ⋙ forget D).RepresentableBy Y`.
-/

@[expose] public section

namespace CategoryTheory.Functor.RepresentableBy

open Opposite

variable {C D : Type*} [Category* C] [Category* D] {F : Cᵒᵖ ⥤ D}
    {CD : D -> Type*} {FD : D -> D -> Type*} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] {Y : C} (α : (F ⋙ forget D).RepresentableBy Y)

/--
Definition of `homEquiv'` / `homEquiv'` 的定义

English:
definition homEquiv'
  signature: {X : C}
  body: α.homEquiv

中文:
定义 homEquiv'
  签名: {X : C}
  定义体: α.homEquiv

Depends on / 依赖: homEquiv
-/
def homEquiv' {X : C} : (X ⟶ Y) ≃ ToType (F.obj (op X)) := α.homEquiv

/--
lemma `homEquiv'_comp` / 引理 `homEquiv'_comp`

English:
lemma homEquiv'_comp
  given: {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y)
  proof: α.homEquiv_comp _ _

中文:
引理 homEquiv'_comp
  条件: {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y)
  证明: α.homEquiv_comp _ _
-/
lemma homEquiv'_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    α.homEquiv' (f ≫ g) = F.map f.op (α.homEquiv' g) := α.homEquiv_comp _ _

end CategoryTheory.Functor.RepresentableBy
