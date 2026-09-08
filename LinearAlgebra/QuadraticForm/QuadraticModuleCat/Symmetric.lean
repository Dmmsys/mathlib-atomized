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

/-
**QuadraticModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory (QuadraticModuleCat.{u} R) :=
  .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))
    fun X Y ↦ ofIso <| tensorComm X.form Y.form

/-- `forget₂ (QuadraticModuleCat R) (ModuleCat R)` is a braided functor. -/
/-
**QuadraticModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`forget₂ (QuadraticModuleCat R) (ModuleCat R)` is a braided functor.
-/
instance : (forget₂ (QuadraticModuleCat R) (ModuleCat R)).Braided where
/-
**QuadraticModuleCat.instSymmetricCategory** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticM
oduleCat`。
形式化陈述：instSymmetricCategory : SymmetricCategory (QuadraticModuleCat.{u} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSymmetricCategory : SymmetricCategory (QuadraticModuleCat.{u} R) :=
  .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))

end QuadraticModuleCat

