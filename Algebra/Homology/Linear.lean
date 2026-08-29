/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The category of homological complexes is linear

In this file, we define the instance `Linear R (HomologicalComplex C c)` when the
category `C` is `R`-linear.

## TODO

- show lemmas like `HomologicalComplex.homologyMap_smul` (after doing the same
  for short complexes in `Mathlib/Algebra/Homology/ShortComplex/Linear.lean`)

-/

public section

open CategoryTheory

variable {R : Type*} [Semiring R] {C D : Type*} [Category* C] [Preadditive C]
  [Category* D] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  {ι : Type*} {c : ComplexShape ι}

namespace HomologicalComplex

variable {X Y : HomologicalComplex C c}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (X ⟶ Y)
  body: { f := fun n => r • f.f n }

@[simp]

中文:
实例 :
  签名: SMul R (X ⟶ Y)
  定义体: { f := fun n => r • f.f n }

@[simp]
-/
instance : SMul R (X ⟶ Y) where
  smul r f := { f := fun n => r • f.f n }

@[simp]
/--
lemma `smul_f_apply` / 引理 `smul_f_apply`

English:
lemma smul_f_apply
  given: (r : R) (f : X ⟶ Y) (n : ι)
  statement: (r • f).f n = r • f.f n
  proof: rfl

@[simp]

中文:
引理 smul_f_apply
  条件: (r : R) (f : X ⟶ Y) (n : ι)
  结论: (r • f).f n = r • f.f n
  证明: rfl

@[simp]
-/
lemma smul_f_apply (r : R) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n := rfl

@[simp]
/--
lemma `units_smul_f_apply` / 引理 `units_smul_f_apply`

English:
lemma units_smul_f_apply
  given: (r : Rˣ) (f : X ⟶ Y) (n : ι)
  statement: (r • f).f n = r • f.f n
  proof: rfl

中文:
引理 units_smul_f_apply
  条件: (r : Rˣ) (f : X ⟶ Y) (n : ι)
  结论: (r • f).f n = r • f.f n
  证明: rfl
-/
lemma units_smul_f_apply (r : Rˣ) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n := rfl

instance (X Y : HomologicalComplex C c) : Module R (X ⟶ Y) where
  one_smul a := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  zero_smul := by cat_disch
  add_smul _ _ _ := by ext; apply add_smul
  mul_smul _ _ _ := by ext; apply mul_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear R (HomologicalComplex C c)

中文:
实例 :
  签名: Linear R (HomologicalComplex C c)
-/
instance : Linear R (HomologicalComplex C c) where

end HomologicalComplex

/--
Instance `CategoryTheory.Functor.mapHomologicalComplex_linear` / 实例 `CategoryTheory.Functor.mapHomologicalComplex_linear`

English:
instance CategoryTheory.Functor.mapHomologicalComplex_linear

中文:
实例 CategoryTheory.Functor.mapHomologicalComplex_linear
-/
instance CategoryTheory.Functor.mapHomologicalComplex_linear
    (F : C ⥤ D) [F.Additive] [Functor.Linear R F] (c : ComplexShape ι) :
    Functor.Linear R (F.mapHomologicalComplex c) where
