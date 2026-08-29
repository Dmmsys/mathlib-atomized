/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Algebras for the coproduct monad

The functor `Y ↦ X ⨿ Y` forms a monad, whose category of monads is equivalent to the under category
of `X`. Similarly, `Y ↦ X ⨯ Y` forms a comonad, whose category of coalgebras is equivalent to the
over category of `X`.

## TODO

Show that `Over.forget X : Over X ⥤ C` is a comonadic left adjoint and `Under.forget : Under X ⥤ C`
is a monadic right adjoint.
-/

@[expose] public section


noncomputable section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] (X : C)

section

open Comonad

variable [HasBinaryProducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `X ⨯ -` has a comonad structure. This is sometimes called the writer comonad. -/
@[simps!]
/--
Definition of `prodComonad` / `prodComonad` 的定义

English:
definition prodComonad
  signature: : Comonad C where
  body: prod.functor.obj X
  ε := { app := fun _ => Limits.prod.snd }
  δ := { app := fun _ => prod.lift Limits.prod.fst (𝟙 _) }

中文:
定义 prodComonad
  签名: : 余单子 C where
  定义体: prod.functor.obj X
  ε := { app := fun _ => Limits.prod.snd }
  δ := { app := fun _ => prod.lift Limits.prod.fst (𝟙 _) }

Depends on / 依赖: functor, prod.functor.obj
-/
def prodComonad : Comonad C where
  toFunctor := prod.functor.obj X
  ε := { app := fun _ => Limits.prod.snd }
  δ := { app := fun _ => prod.lift Limits.prod.fst (𝟙 _) }

set_option backward.defeqAttrib.useBackward true in
/-- The forward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
/--
Definition of `coalgebraToOver` / `coalgebraToOver` 的定义

English:
definition coalgebraToOver
  signature: : Coalgebra (prodComonad X) ⥤ Over X where
  body: Over.mk (A.a ≫ Limits.prod.fst)
  map f := Over.homMk f.f (by simp [← dsimp% f.h_assoc])

中文:
定义 coalgebraToOver
  签名: : 余algebra (prodComonad X) ⥤ Over X where
  定义体: Over.mk (A.a ≫ Limits.prod.fst)
  map f := Over.homMk f.f (by simp [← dsimp% f.h_assoc])

Depends on / 依赖: Limits, Limits.prod.fst, Over.mk
-/
def coalgebraToOver : Coalgebra (prodComonad X) ⥤ Over X where
  obj A := Over.mk (A.a ≫ Limits.prod.fst)
  map f := Over.homMk f.f (by simp [← dsimp% f.h_assoc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The backward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
/--
Definition of `overToCoalgebra` / `overToCoalgebra` 的定义

English:
definition overToCoalgebra
  signature: : Over X ⥤ Coalgebra (prodComonad X) where
  body: { A := f.left
      a := prod.lift f.hom (𝟙 _) }
  map g := { f := g.left }

中文:
定义 overToCoalgebra
  签名: : Over X ⥤ 余algebra (prodComonad X) where
  定义体: { A := f.left
      a := prod.lift f.hom (𝟙 _) }
  map g := { f := g.left }

Depends on / 依赖: f.hom, f.left, g.left, prod.lift
-/
def overToCoalgebra : Over X ⥤ Coalgebra (prodComonad X) where
  obj f :=
    { A := f.left
      a := prod.lift f.hom (𝟙 _) }
  map g := { f := g.left }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The equivalence from coalgebras for the product comonad to the over category. -/
@[simps]
/--
Definition of `coalgebraEquivOver` / `coalgebraEquivOver` 的定义

English:
definition coalgebraEquivOver
  signature: : Coalgebra (prodComonad X) ≌ Over X where
  body: coalgebraToOver X
  inverse := overToCoalgebra X
  unitIso := NatIso.ofComponents fun A =>
    Coalgebra.isoMk (Iso.refl _) (Limits.prod.hom_ext (by simp) (by simpa using A.counit))
  counitIso := NatIso.ofComponents fun f => Over.isoMk (Iso.refl _)

中文:
定义 coalgebraEquivOver
  签名: : 余algebra (prodComonad X) ≌ Over X where
  定义体: coalgebraToOver X
  inverse := overToCoalgebra X
  unitIso := NatIso.ofComponents fun A =>
    Coalgebra.isoMk (Iso.refl _) (Limits.prod.hom_ext (by simp) (by simpa using A.counit))
  counitIso := NatIso.ofComponents fun f => Over.isoMk (Iso.refl _)

Depends on / 依赖: coalgebraToOver
-/
def coalgebraEquivOver : Coalgebra (prodComonad X) ≌ Over X where
  functor := coalgebraToOver X
  inverse := overToCoalgebra X
  unitIso := NatIso.ofComponents fun A =>
    Coalgebra.isoMk (Iso.refl _) (Limits.prod.hom_ext (by simp) (by simpa using A.counit))
  counitIso := NatIso.ofComponents fun f => Over.isoMk (Iso.refl _)

end

section


variable [HasBinaryCoproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- `X ⨿ -` has a monad structure. This is sometimes called the either monad. -/
@[simps!]
/--
Definition of `coprodMonad` / `coprodMonad` 的定义

English:
definition coprodMonad
  signature: : Monad C where
  body: coprod.functor.obj X
  η := { app := fun _ => coprod.inr }
  μ := { app := fun _ => coprod.desc coprod.inl (𝟙 _) }

中文:
定义 coprodMonad
  签名: : 单子 C where
  定义体: coprod.functor.obj X
  η := { app := fun _ => coprod.inr }
  μ := { app := fun _ => coprod.desc coprod.inl (𝟙 _) }

Depends on / 依赖: coprod, coprod.functor.obj, functor
-/
def coprodMonad : Monad C where
  toFunctor := coprod.functor.obj X
  η := { app := fun _ => coprod.inr }
  μ := { app := fun _ => coprod.desc coprod.inl (𝟙 _) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The forward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
/--
Definition of `algebraToUnder` / `algebraToUnder` 的定义

English:
definition algebraToUnder
  signature: : Monad.Algebra (coprodMonad X) ⥤ Under X where
  body: Under.mk (coprod.inl ≫ A.a)
  map f := Under.homMk f.f (by simp [← dsimp% f.h])

中文:
定义 algebraToUnder
  签名: : 单子.代数 (coprodMonad X) ⥤ Under X where
  定义体: Under.mk (coprod.inl ≫ A.a)
  map f := Under.homMk f.f (by simp [← dsimp% f.h])

Depends on / 依赖: Under.mk, coprod, coprod.inl
-/
def algebraToUnder : Monad.Algebra (coprodMonad X) ⥤ Under X where
  obj A := Under.mk (coprod.inl ≫ A.a)
  map f := Under.homMk f.f (by simp [← dsimp% f.h])

set_option backward.isDefEq.respectTransparency false in
/-- The backward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
/--
Definition of `underToAlgebra` / `underToAlgebra` 的定义

English:
definition underToAlgebra
  signature: : Under X ⥤ Monad.Algebra (coprodMonad X) where
  body: { A := f.right
      a := coprod.desc f.hom (𝟙 _) }
  map g := { f := g.right }

中文:
定义 underToAlgebra
  签名: : Under X ⥤ 单子.代数 (coprodMonad X) where
  定义体: { A := f.right
      a := coprod.desc f.hom (𝟙 _) }
  map g := { f := g.right }

Depends on / 依赖: coprod, coprod.desc, f.hom, f.right, g.right
-/
def underToAlgebra : Under X ⥤ Monad.Algebra (coprodMonad X) where
  obj f :=
    { A := f.right
      a := coprod.desc f.hom (𝟙 _) }
  map g := { f := g.right }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The equivalence from algebras for the coproduct monad to the under category.
-/
@[simps]
/--
Definition of `algebraEquivUnder` / `algebraEquivUnder` 的定义

English:
definition algebraEquivUnder
  signature: : Monad.Algebra (coprodMonad X) ≌ Under X where
  body: algebraToUnder X
  inverse := underToAlgebra X
  unitIso := NatIso.ofComponents fun A =>
    Monad.Algebra.isoMk (Iso.refl _) (coprod.hom_ext (by simp) (by simpa using A.unit.symm))
  counitIso :=
    NatIso.ofComponents fun f => Under.isoMk (Iso.refl _)

中文:
定义 algebraEquivUnder
  签名: : 单子.代数 (coprodMonad X) ≌ Under X where
  定义体: algebraToUnder X
  inverse := underToAlgebra X
  unitIso := NatIso.ofComponents fun A =>
    Monad.Algebra.isoMk (Iso.refl _) (coprod.hom_ext (by simp) (by simpa using A.unit.symm))
  counitIso :=
    NatIso.ofComponents fun f => Under.isoMk (Iso.refl _)

Depends on / 依赖: algebraToUnder
-/
def algebraEquivUnder : Monad.Algebra (coprodMonad X) ≌ Under X where
  functor := algebraToUnder X
  inverse := underToAlgebra X
  unitIso := NatIso.ofComponents fun A =>
    Monad.Algebra.isoMk (Iso.refl _) (coprod.hom_ext (by simp) (by simpa using A.unit.symm))
  counitIso :=
    NatIso.ofComponents fun f => Under.isoMk (Iso.refl _)

end

end CategoryTheory
