/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Category.AlgCat.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The monoidal structure on `AlgCat` is symmetric.

In this file we show:

* `AlgCat.instSymmetricCategory : SymmetricCategory (AlgCat.{u} R)`
-/

public section
open CategoryTheory


noncomputable section

universe v u

variable {R : Type u} [CommRing R]

namespace AlgCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory (AlgCat.{u} R)
  body: .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))
    fun X Y => (Algebra.TensorProduct.comm R X Y).toAlgebraIso

中文:
实例 :
  签名: 辫范畴 (Alg范畴.{u} R)
  定义体: .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))
    fun X Y => (Algebra.TensorProduct.comm R X Y).toAlgebraIso

Depends on / 依赖: AlgCat, Algebra, Algebra.TensorProduct.comm, ModuleCat, TensorProduct, ofFaithful, toAlgebraIso
-/
instance : BraidedCategory (AlgCat.{u} R) :=
  .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))
    fun X Y => (Algebra.TensorProduct.comm R X Y).toAlgebraIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (AlgCat R) (ModuleCat R)).Braided

中文:
实例 :
  签名: (forget₂ (Alg范畴 R) (模范畴 R)).辫
-/
instance : (forget₂ (AlgCat R) (ModuleCat R)).Braided where

/--
Instance `instSymmetricCategory` / 实例 `instSymmetricCategory`

English:
instance instSymmetricCategory
  signature: : SymmetricCategory (AlgCat.{u} R)
  body: .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))

中文:
实例 instSymmetricCategory
  签名: : 对称范畴 (Alg范畴.{u} R)
  定义体: .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))

Depends on / 依赖: AlgCat, ModuleCat, ofFaithful
-/
instance instSymmetricCategory : SymmetricCategory (AlgCat.{u} R) :=
  .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))

end AlgCat
