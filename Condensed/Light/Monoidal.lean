/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.Light.Basic
public import Mathlib.Condensed.Light.Instances
public import Mathlib.Condensed.Light.Module

/-!

# Closed symmetric monoidal structure on light condensed modules

We define a symmetric monoidal structure on light condensed modules by localizing the symmetric
monoidal structure on the presheaf category. By Day's reflection theorem, we obtain a closed
structure.
-/

public section

universe u

noncomputable section

open CategoryTheory Monoidal Sheaf MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory

namespace LightCondensed

variable (R : Type u) [CommRing R]

.IsMonoidal := instance : (coherentTopology LightProfinite.{u}).W (A := ModuleCat.{u} R)
  GrothendieckTopology.W.transport_isMonoidal _ _
    ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u}))
    (equivSmallModel.{u} LightProfinite.{u}).inverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory (LightCondMod.{u} R)
  body: monoidalCategory _ _

中文:
实例 :
  签名: MonoidalCategory (LightCondMod.{u} R)
  定义体: monoidalCategory _ _

Depends on / 依赖: monoidalCategory
-/
instance : MonoidalCategory (LightCondMod.{u} R) :=
  monoidalCategory _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R))
  body: inferInstanceAs (MonoidalCategory (LightCondMod _))

中文:
实例 :
  签名: MonoidalCategory (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R))
  定义体: inferInstanceAs (MonoidalCategory (LightCondMod _))

Depends on / 依赖: LightCondMod, MonoidalCategory
-/
instance : MonoidalCategory (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)) :=
  inferInstanceAs (MonoidalCategory (LightCondMod _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SymmetricCategory (LightCondMod.{u} R)
  body: symmetricCategory _ _

中文:
实例 :
  签名: SymmetricCategory (LightCondMod.{u} R)
  定义体: symmetricCategory _ _

Depends on / 依赖: symmetricCategory
-/
instance : SymmetricCategory (LightCondMod.{u} R) :=
  symmetricCategory _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalClosed (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R)
  body: .ofEquiv _ (equivSmallModel LightProfinite).op.congrLeft.toAdjunction

中文:
实例 :
  签名: MonoidalClosed (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R)
  定义体: .ofEquiv _ (equivSmallModel LightProfinite).op.congrLeft.toAdjunction

Depends on / 依赖: LightProfinite, congrLeft, equivSmallModel, ofEquiv, op.congrLeft.toAdjunction, toAdjunction
-/
instance : MonoidalClosed (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R) :=
  .ofEquiv _ (equivSmallModel LightProfinite).op.congrLeft.toAdjunction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalClosed (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R))
  body: Reflective.monoidalClosed (sheafificationAdjunction _ _)

中文:
实例 :
  签名: MonoidalClosed (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R))
  定义体: Reflective.monoidalClosed (sheafificationAdjunction _ _)

Depends on / 依赖: Reflective, Reflective.monoidalClosed, monoidalClosed, sheafificationAdjunction
-/
instance : MonoidalClosed (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalClosed (LightCondMod.{u} R)
  body: inferInstanceAs (MonoidalClosed (Sheaf _ _))

中文:
实例 :
  签名: MonoidalClosed (LightCondMod.{u} R)
  定义体: inferInstanceAs (MonoidalClosed (Sheaf _ _))

Depends on / 依赖: MonoidalClosed
-/
instance : MonoidalClosed (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Sheaf _ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (presheafToSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Monoidal
  body: inferInstance

中文:
实例 :
  签名: (presheafToSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Monoidal
  定义体: inferInstance
-/
instance : (presheafToSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Monoidal :=
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (free R).Monoidal
  body: inferInstanceAs (composeAndSheafify _ _).Monoidal

中文:
实例 :
  签名: (free R).Monoidal
  定义体: inferInstanceAs (composeAndSheafify _ _).Monoidal

Depends on / 依赖: Monoidal, composeAndSheafify
-/
instance : (free R).Monoidal := inferInstanceAs (composeAndSheafify _ _).Monoidal

end LightCondensed
