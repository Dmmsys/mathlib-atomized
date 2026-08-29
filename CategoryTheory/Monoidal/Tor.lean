/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tor, the left-derived functor of tensor product

We define `Tor C n : C ⥤ C ⥤ C`, by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`.

For now we have almost nothing to say about it!

It would be good to show that this is naturally isomorphic to the functor obtained
by left-deriving in the first factor, instead.
For now we define `Tor'` by left-deriving in the first factor,
but showing `Tor C n ≅ Tor' C n` will require a bit more theory!
Possibly it's best to axiomatize delta functors, and obtain a unique characterisation?

-/

@[expose] public section


assert_not_exists ModuleCat.abelian

noncomputable section

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable (C : Type*) [Category* C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [HasProjectiveResolutions C]

/-- We define `Tor C n : C ⥤ C ⥤ C` by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`. -/
@[simps]
/--
Definition of `Tor` / `Tor` 的定义

English:
definition Tor
  signature: (n : Nat)
  body: Functor.leftDerived ((tensoringLeft C).obj X) n
  map f := NatTrans.leftDerived ((tensoringLeft C).map f) n

中文:
定义 Tor
  签名: (n : 自然数)
  定义体: Functor.leftDerived ((tensoringLeft C).obj X) n
  map f := NatTrans.leftDerived ((tensoringLeft C).map f) n

Depends on / 依赖: Functor, Functor.leftDerived, leftDerived, tensoringLeft
-/
def Tor (n : Nat) : C ⥤ C ⥤ C where
  obj X := Functor.leftDerived ((tensoringLeft C).obj X) n
  map f := NatTrans.leftDerived ((tensoringLeft C).map f) n

/-- An alternative definition of `Tor`, where we left-derive in the first factor instead. -/
@[simps! obj_obj map_app obj_map]
/--
Definition of `Tor'` / `Tor'` 的定义

English:
definition Tor'
  signature: (n : Nat)
  body: Functor.flip
    { obj := fun X => Functor.leftDerived ((tensoringRight C).obj X) n
      map := fun f => NatTrans.leftDerived ((tensoringRight C).map f) n }

中文:
定义 Tor'
  签名: (n : 自然数)
  定义体: Functor.flip
    { obj := fun X => Functor.leftDerived ((tensoringRight C).obj X) n
      map := fun f => NatTrans.leftDerived ((tensoringRight C).map f) n }

Depends on / 依赖: Functor, Functor.flip, Functor.leftDerived, NatTrans, NatTrans.leftDerived, leftDerived, tensoringRight
-/
def Tor' (n : Nat) : C ⥤ C ⥤ C :=
  Functor.flip
    { obj := fun X => Functor.leftDerived ((tensoringRight C).obj X) n
      map := fun f => NatTrans.leftDerived ((tensoringRight C).map f) n }

/--
lemma `isZero_Tor_succ_of_projective` / 引理 `isZero_Tor_succ_of_projective`

English:
lemma isZero_Tor_succ_of_projective
  given: (X Y : C) [Projective Y] (n : Nat)
  proof: by
  apply Functor.isZero_leftDerived_obj_projective_succ

中文:
引理 isZero_Tor_succ_of_projective
  条件: (X Y : C) [投射 Y] (n : 自然数)
  证明: by
  apply Functor.isZero_leftDerived_obj_projective_succ

Depends on / 依赖: Functor, Functor.isZero_leftDerived_obj_projective_succ, isZero_leftDerived_obj_projective_succ
-/
lemma isZero_Tor_succ_of_projective (X Y : C) [Projective Y] (n : Nat) :
    IsZero (((Tor C (n + 1)).obj X).obj Y) := by
  apply Functor.isZero_leftDerived_obj_projective_succ

/--
lemma `isZero_Tor'_succ_of_projective` / 引理 `isZero_Tor'_succ_of_projective`

English:
lemma isZero_Tor'_succ_of_projective
  given: (X Y : C) [Projective X] (n : Nat)
  proof: by
  apply Functor.isZero_leftDerived_obj_projective_succ

中文:
引理 isZero_Tor'_succ_of_projective
  条件: (X Y : C) [投射 X] (n : 自然数)
  证明: by
  apply Functor.isZero_leftDerived_obj_projective_succ

Depends on / 依赖: Functor, Functor.isZero_leftDerived_obj_projective_succ, isZero_leftDerived_obj_projective_succ
-/
lemma isZero_Tor'_succ_of_projective (X Y : C) [Projective X] (n : Nat) :
    IsZero (((Tor' C (n + 1)).obj X).obj Y) := by
  apply Functor.isZero_leftDerived_obj_projective_succ

end CategoryTheory
