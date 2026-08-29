/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions regarding the category of topological spaces

This file shows that the forgetful functor from topological spaces to types has a left and right
adjoint, given by `TopCat.discrete`, resp. `TopCat.trivial`, the functors which equip a type with
the discrete, resp. trivial, topology.
-/

@[expose] public section


universe u

open CategoryTheory

open TopCat

namespace TopCat

/-- Equipping a type with the discrete topology is left adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps! unit counit]
/--
Definition of `adj₁` / `adj₁` 的定义

English:
definition adj₁
  signature: : discrete ⊣ forget TopCat.{u} where
  body: 𝟙 _
  counit := { app := fun X => TopCat.ofHom (X := discrete.obj X) ⟨id, continuous_bot⟩ }

中文:
定义 adj₁
  签名: : discrete ⊣ forget TopCat.{u} where
  定义体: 𝟙 _
  counit := { app := fun X => TopCat.ofHom (X := discrete.obj X) ⟨id, continuous_bot⟩ }
-/
def adj₁ : discrete ⊣ forget TopCat.{u} where
  unit := 𝟙 _
  counit := { app := fun X => TopCat.ofHom (X := discrete.obj X) ⟨id, continuous_bot⟩ }

/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps! unit counit]
/--
Definition of `adj₂` / `adj₂` 的定义

English:
definition adj₂
  signature: : forget TopCat.{u} ⊣ trivial where
  body: { app := fun X => TopCat.ofHom (Y := trivial.obj X) ⟨id, continuous_top⟩ }
  counit := 𝟙 _

中文:
定义 adj₂
  签名: : forget TopCat.{u} ⊣ trivial where
  定义体: { app := fun X => TopCat.ofHom (Y := trivial.obj X) ⟨id, continuous_top⟩ }
  counit := 𝟙 _

Depends on / 依赖: TopCat, TopCat.ofHom, continuous_top, trivial.obj
-/
def adj₂ : forget TopCat.{u} ⊣ trivial where
  unit := { app := fun X => TopCat.ofHom (Y := trivial.obj X) ⟨id, continuous_top⟩ }
  counit := 𝟙 _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget TopCat.{u}).IsRightAdjoint
  body: ⟨_, ⟨adj₁⟩⟩

中文:
实例 :
  签名: (forget TopCat.{u}).IsRightAdjoint
  定义体: ⟨_, ⟨adj₁⟩⟩
-/
instance : (forget TopCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj₁⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget TopCat.{u}).IsLeftAdjoint
  body: ⟨_, ⟨adj₂⟩⟩

中文:
实例 :
  签名: (forget TopCat.{u}).IsLeftAdjoint
  定义体: ⟨_, ⟨adj₂⟩⟩
-/
instance : (forget TopCat.{u}).IsLeftAdjoint :=
  ⟨_, ⟨adj₂⟩⟩

end TopCat
