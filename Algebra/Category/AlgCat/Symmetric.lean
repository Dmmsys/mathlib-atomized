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

/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory (AlgCat.{u} R) :=
  .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))
    fun X Y ↦ (Algebra.TensorProduct.comm R X Y).toAlgebraIso
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (AlgCat R) (ModuleCat R)).Braided where
/-
**AlgCat.instSymmetricCategory** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：instSymmetricCategory : SymmetricCategory (AlgCat.{u} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSymmetricCategory : SymmetricCategory (AlgCat.{u} R) :=
  .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))

end AlgCat

