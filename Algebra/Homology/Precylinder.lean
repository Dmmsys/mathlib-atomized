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
  [forall i, HasBinaryBiproduct (K.X i) (K.X i)]

/-- The precylinder object of a homological complex that is given by
`HomologicalComplex.cylinder`. -/
@[simps]
/--
Definition of `precylinder` / `precylinder` 的定义

English:
definition precylinder
  signature: [K.HasCylinder]
  body: K.cylinder
  i₀ := cylinder.ι₀ _
  i₁ := cylinder.ι₁ _
  π := cylinder.π _

中文:
定义 precylinder
  签名: [K.HasCylinder]
  定义体: K.cylinder
  i₀ := cylinder.ι₀ _
  i₁ := cylinder.ι₁ _
  π := cylinder.π _

Depends on / 依赖: K.cylinder, cylinder
-/
noncomputable def precylinder [K.HasCylinder] : Precylinder K where
  I := K.cylinder
  i₀ := cylinder.ι₀ _
  i₁ := cylinder.ι₁ _
  π := cylinder.π _

/-- The pre-path object of a homological complex that is given by
`HomologicalComplex.pathObject`. -/
@[simps]
/--
Definition of `prepathObject` / `prepathObject` 的定义

English:
definition prepathObject
  signature: [K.HasPathObject]
  body: K.pathObject
  p₀ := pathObject.π₀ _
  p₁ := pathObject.π₁ _
  ι := pathObject.ι _

中文:
定义 prepathObject
  签名: [K.HasPathObject]
  定义体: K.pathObject
  p₀ := pathObject.π₀ _
  p₁ := pathObject.π₁ _
  ι := pathObject.ι _

Depends on / 依赖: K.pathObject, pathObject
-/
noncomputable def prepathObject [K.HasPathObject] : PrepathObject K where
  P := K.pathObject
  p₀ := pathObject.π₀ _
  p₁ := pathObject.π₁ _
  ι := pathObject.ι _

end HomologicalComplex
