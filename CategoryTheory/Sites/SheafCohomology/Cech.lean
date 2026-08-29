/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech

/-!
# Cech cohomology

Given a family of objects `U : ι → C` in a category `C` that has finite products,
we define a Cech complex functor
`cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` which sends a presheaf
`P : Cᵒᵖ ⥤ A` in a preadditive category (where products exist) to the cochain
complex which in degree `n` consists of the product, indexed by `i : Fin (n + 1) → ι`,
of the value of `P` on the product of the objects `U (i a)` for `a : Fin (n + 1)`.

-/

@[expose] public section

universe w t v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]

namespace Limits.FormalCoproduct

open Opposite

variable (E : SimplicialObject (FormalCoproduct.{w} C))

/-- Given a simplicial object `E` in the category `FormalCoproduct C`, this is the
functor `(Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A` which sends `P : Cᵒᵖ ⥤ A` to the
cosimplicial object which sends `⦋n⦌` to the "evaluation" of `P` on `E _⦋n⦌`. -/
@[simps!]
/--
Definition of `cosimplicialObjectFunctor` / `cosimplicialObjectFunctor` 的定义

English:
definition cosimplicialObjectFunctor
  signature: :
  body: evalOp.{w} C A ⋙ (Functor.whiskeringLeft _ _ _).obj E.rightOp

中文:
定义 cosimplicialObjectFunctor
  签名: :
  定义体: evalOp.{w} C A ⋙ (Functor.whiskeringLeft _ _ _).obj E.rightOp

Depends on / 依赖: E.rightOp, Functor, Functor.whiskeringLeft, evalOp, rightOp, whiskeringLeft
-/
noncomputable def cosimplicialObjectFunctor :
    (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  evalOp.{w} C A ⋙ (Functor.whiskeringLeft _ _ _).obj E.rightOp

variable [Preadditive A]

/-- Given a simplicial object `E` in the category `FormalCoproduct C`, this is the
functor `(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` which sends `P : Cᵒᵖ ⥤ A` to the
cochain complex which in degree `n` consists of the "evaluation" of `P` on `E _⦋n⦌`. -/
@[simps!]
/--
Definition of `cochainComplexFunctor` / `cochainComplexFunctor` 的定义

English:
definition cochainComplexFunctor
  signature: : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A Nat
  body: cosimplicialObjectFunctor E ⋙ AlgebraicTopology.alternatingCofaceMapComplex A

中文:
定义 cochainComplexFunctor
  签名: : (Cᵒᵖ ⥤ A) ⥤ 上链复形 A 自然数
  定义体: cosimplicialObjectFunctor E ⋙ AlgebraicTopology.alternatingCofaceMapComplex A

Depends on / 依赖: AlgebraicTopology, AlgebraicTopology.alternatingCofaceMapComplex, alternatingCofaceMapComplex, cosimplicialObjectFunctor
-/
noncomputable def cochainComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A Nat :=
  cosimplicialObjectFunctor E ⋙ AlgebraicTopology.alternatingCofaceMapComplex A

end Limits.FormalCoproduct

variable [HasFiniteProducts C] [Preadditive A] {ι : Type w} (U : ι -> C)

/--
Definition of `cechComplexFunctor` / `cechComplexFunctor` 的定义

English:
definition cechComplexFunctor
  signature: : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A Nat
  body: FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech

中文:
定义 cechComplexFunctor
  签名: : (Cᵒᵖ ⥤ A) ⥤ 上链复形 A 自然数
  定义体: FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech

Depends on / 依赖: FormalCoproduct, FormalCoproduct.cochainComplexFunctor, FormalCoproduct.mk, cochainComplexFunctor
-/
noncomputable def cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A Nat :=
  FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech

end CategoryTheory
