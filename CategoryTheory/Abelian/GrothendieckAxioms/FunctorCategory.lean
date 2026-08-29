/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
/-!

# AB axioms in functor categories

This file proves that, when the relevant limits and colimits exist, exactness of limits and
colimits carries over from `A` to the functor category `C ⥤ A`.
-/

public section

namespace CategoryTheory

open CategoryTheory Limits Opposite

variable {A C J : Type*} [Category* A] [Category* C] [Category* J]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: J A] [HasExactColimitsOfShape J A] [HasFiniteLimits A] :
  body: { preservesFiniteLimits _ := inferInstance }

中文:
实例 [HasColimitsOfShape
  签名: J A] [HasExactColimitsOfShape J A] [HasFiniteLimits A] :
  定义体: { preservesFiniteLimits _ := inferInstance }

Depends on / 依赖: preservesFiniteLimits
-/
instance [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] [HasFiniteLimits A] :
    HasExactColimitsOfShape J (C ⥤ A) where
  preservesFiniteLimits := { preservesFiniteLimits _ := inferInstance }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J A] [HasExactLimitsOfShape J A] [HasFiniteColimits A] :
  body: { preservesFiniteColimits _ := inferInstance }

中文:
实例 [HasLimitsOfShape
  签名: J A] [HasExactLimitsOfShape J A] [HasFiniteColimits A] :
  定义体: { preservesFiniteColimits _ := inferInstance }

Depends on / 依赖: preservesFiniteColimits
-/
instance [HasLimitsOfShape J A] [HasExactLimitsOfShape J A] [HasFiniteColimits A] :
    HasExactLimitsOfShape J (C ⥤ A) where
  preservesFiniteColimits := { preservesFiniteColimits _ := inferInstance }

end CategoryTheory
