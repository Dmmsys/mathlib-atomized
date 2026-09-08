/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyFiber
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject

/-!
# Precylinder and pre-path objects in the category of homological complexes

In this file, we upgrade the definitions `HomologicalComplex.cylinder` and
`HomologicalComplex.pathObject` to pre-cylinder objects and pre-path
objects in the sense of homotopical algebra.

-/

@[expose] public section

open CategoryTheory Limits HomotopicalAlgebra

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {ι : Type*} {c : ComplexShape ι} [DecidableRel c.Rel]
  (K : HomologicalComplex C c)
  [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]

/-- The precylinder object of a homological complex that is given by
`HomologicalComplex.cylinder`. -/
@[simps]
/-
**HomologicalComplex.precylinder** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：precylinder [K.HasCylinder] : Precylinder K where I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precylinder object of a homological complex that is given by
`HomologicalComplex.cylinder`.
-/
noncomputable def precylinder [K.HasCylinder] : Precylinder K where
  I := K.cylinder
  i₀ := cylinder.ι₀ _
  i₁ := cylinder.ι₁ _
  π := cylinder.π _

/-- The pre-path object of a homological complex that is given by
`HomologicalComplex.pathObject`. -/
@[simps]
/-
**HomologicalComplex.prepathObject** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：prepathObject [K.HasPathObject] : PrepathObject K where P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-path object of a homological complex that is given by
`HomologicalComplex.pathObject`.
-/
noncomputable def prepathObject [K.HasPathObject] : PrepathObject K where
  P := K.pathObject
  p₀ := pathObject.π₀ _
  p₁ := pathObject.π₁ _
  ι := pathObject.ι _

end HomologicalComplex

