/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The monoidal structure on `QuadraticModuleCat` is symmetric.

In this file we show:

* `QuadraticModuleCat.instSymmetricCategory : SymmetricCategory (QuadraticModuleCat.{u} R)`

## Implementation notes

This file essentially mirrors `Mathlib/Algebra/Category/AlgCat/Symmetric.lean`.
-/

public section

open CategoryTheory

universe v u

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace QuadraticModuleCat

open QuadraticForm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory (QuadraticModuleCat.{u} R)
  body: .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))
fun X Y => ofIso tensorComm X.form Y.form

中文:
实例 :
  签名: 辫范畴 (二次模范畴.{u} R)
  定义体: .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))
fun X Y => ofIso tensorComm X.form Y.form

Depends on / 依赖: ModuleCat, QuadraticModuleCat, X.form, Y.form, ofFaithful, tensorComm
-/
instance : BraidedCategory (QuadraticModuleCat.{u} R) :=
  .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))
fun X Y => ofIso tensorComm X.form Y.form

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (QuadraticModuleCat R) (ModuleCat R)).Braided

中文:
实例 :
  签名: (forget₂ (二次模范畴 R) (模范畴 R)).辫
-/
instance : (forget₂ (QuadraticModuleCat R) (ModuleCat R)).Braided where

/--
Instance `instSymmetricCategory` / 实例 `instSymmetricCategory`

English:
instance instSymmetricCategory
  signature: : SymmetricCategory (QuadraticModuleCat.{u} R)
  body: .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))

中文:
实例 instSymmetricCategory
  签名: : 对称范畴 (二次模范畴.{u} R)
  定义体: .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))

Depends on / 依赖: ModuleCat, QuadraticModuleCat, ofFaithful
-/
instance instSymmetricCategory : SymmetricCategory (QuadraticModuleCat.{u} R) :=
  .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))

end QuadraticModuleCat
