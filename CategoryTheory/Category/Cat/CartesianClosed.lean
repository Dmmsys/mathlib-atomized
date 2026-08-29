/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Cartesian closed structure on `Cat`

The category of small categories is Cartesian closed, with the exponential at a category `C`
defined by the functor category mapping out of `C`.

Adjoint transposition is defined by currying and uncurrying.

TODO: It would be useful to investigate and formalize further compatibilities along the
lines of `Cat.ihom_obj` and `Cat.ihom_map`, relating currying of functors with currying in
monoidal closed categories and precomposition with left whiskering. These may not be
definitional equalities but may have to be phrased using `eqToIso`.

-/

@[expose] public section

universe v u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open CategoryTheory.Functor Cat

namespace Cat

variable (C : Type u) [Category.{v} C]

/-- A category `C` induces a functor from `Cat` to itself defined
by forming the category of functors out of `C`. -/
@[simps]
/--
Definition of `exp` / `exp` 的定义

English:
definition exp
  signature: : Cat ⥤ Cat where
  body: Cat.of (C ⥤ D)
  map F := ((whiskeringRight _ _ _).obj F.toFunctor).toCatHom

中文:
定义 exp
  签名: : Cat ⥤ Cat where
  定义体: Cat.of (C ⥤ D)
  map F := ((whiskeringRight _ _ _).obj F.toFunctor).toCatHom

Depends on / 依赖: Cat.of
-/
def exp : Cat ⥤ Cat where
  obj D := Cat.of (C ⥤ D)
  map F := ((whiskeringRight _ _ _).obj F.toFunctor).toCatHom

end Cat

section

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
  [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism of categories of bifunctors given by currying. -/
@[simps!]
/--
Definition of `curryingIso` / `curryingIso` 的定义

English:
definition curryingIso
  signature: : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (C × D ⥤ E)
  body: isoOfEquiv currying Functor.curry_obj_uncurry_obj Functor.uncurry_obj_curry_obj

中文:
定义 curryingIso
  签名: : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (C × D ⥤ E)
  定义体: isoOfEquiv currying Functor.curry_obj_uncurry_obj Functor.uncurry_obj_curry_obj

Depends on / 依赖: Functor, Functor.curry_obj_uncurry_obj, Functor.uncurry_obj_curry_obj, curry_obj_uncurry_obj, currying, isoOfEquiv, uncurry_obj_curry_obj
-/
def curryingIso : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (C × D ⥤ E) :=
  isoOfEquiv currying Functor.curry_obj_uncurry_obj Functor.uncurry_obj_curry_obj

/-- The isomorphism of categories of bifunctors given by flipping the arguments. -/
@[simps!]
/--
Definition of `flippingIso` / `flippingIso` 的定义

English:
definition flippingIso
  signature: : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (D ⥤ C ⥤ E)
  body: isoOfEquiv flipping Functor.flip_flip Functor.flip_flip

中文:
定义 flippingIso
  签名: : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (D ⥤ C ⥤ E)
  定义体: isoOfEquiv flipping Functor.flip_flip Functor.flip_flip

Depends on / 依赖: Functor, Functor.flip_flip, flip_flip, flipping, isoOfEquiv
-/
def flippingIso : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (D ⥤ C ⥤ E) :=
  isoOfEquiv flipping Functor.flip_flip Functor.flip_flip

end

namespace Cat

section
variable (C : Type u) [Category.{u} C]

/--
Instance `closed` / 实例 `closed`

English:
instance closed
  signature: : Closed (Cat.of C) where
  body: exp C
  adj := Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Equiv.trans (Cat.Hom.equivFunctor _ _) (curryingFlipEquiv.symm.trans
        (Functor.equivCatHom _ _))
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

中文:
实例 closed
  签名: : Closed (Cat.of C) where
  定义体: exp C
  adj := Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Equiv.trans (Cat.Hom.equivFunctor _ _) (curryingFlipEquiv.symm.trans
        (Functor.equivCatHom _ _))
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }
-/
instance closed : Closed (Cat.of C) where
  rightAdj := exp C
  adj := Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Equiv.trans (Cat.Hom.equivFunctor _ _) (curryingFlipEquiv.symm.trans
        (Functor.equivCatHom _ _))
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

/--
Instance `cartesianClosed` / 实例 `cartesianClosed`

English:
instance cartesianClosed
  signature: : MonoidalClosed Cat.{u, u} where
  body: closed C

@[simp]

中文:
实例 cartesianClosed
  签名: : MonoidalClosed Cat.{u, u} where
  定义体: closed C

@[simp]

Depends on / 依赖: closed
-/
instance cartesianClosed : MonoidalClosed Cat.{u, u} where
  closed C := closed C

@[simp]
/--
lemma `ihom_obj` / 引理 `ihom_obj`

English:
lemma ihom_obj
  given: (D : Type u) [Category.{u} D]
  proof: rfl

@[simp]

中文:
引理 ihom_obj
  条件: (D : 类型u) [Category.{u} D]
  证明: rfl

@[simp]
-/
lemma ihom_obj (D : Type u) [Category.{u} D] :
    (ihom (Cat.of C)).obj (Cat.of D) = Cat.of (C ⥤ D) := rfl

@[simp]
/--
lemma `ihom_map` / 引理 `ihom_map`

English:
lemma ihom_map
  given: {D E : Type u} [Category.{u} D] [Category.{u} E] (F : D ⥤ E)
  proof: rfl

中文:
引理 ihom_map
  条件: {D E : 类型u} [Category.{u} D] [Category.{u} E] (F : D ⥤ E)
  证明: rfl
-/
lemma ihom_map {D E : Type u} [Category.{u} D] [Category.{u} E] (F : D ⥤ E) :
    (ihom (Cat.of C)).map F.toCatHom = ((whiskeringRight _ _ _).obj F).toCatHom := rfl

end

end Cat

end CategoryTheory
