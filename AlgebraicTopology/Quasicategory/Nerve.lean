/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Emily Riehl, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal

/-!
# The nerve of a category is a quasicategory

In `AlgebraicTopology.Quasicategory.StrictSegal`, we show that any
strict Segal simplicial set is a quasicategory.
In `AlgebraicTopology.SimplicialSet.StrictSegal`, we show that the nerve of a
category satisfies the strict Segal condition.

In this file, we prove as a direct consequence that the nerve of a category is
a quasicategory.
-/

public section

universe v u

open SSet

namespace CategoryTheory.Nerve

/-- By virtue of satisfying the `StrictSegal` condition, the nerve of a
category is a `Quasicategory`. -/
/-
**CategoryTheory.Nerve.quasicategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.N
erve`。
形式化陈述：quasicategory {C : Type u} [Category.{v} C] : Quasicategory (nerve C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By virtue of satisfying the `StrictSegal` condition, the nerve of a
category is a `Quasicategory`.
-/
instance quasicategory {C : Type u} [Category.{v} C] : Quasicategory (nerve C) := inferInstance

end CategoryTheory.Nerve

