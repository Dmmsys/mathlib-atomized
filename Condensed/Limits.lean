/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Module

/-!

# Limits in categories of condensed objects

This file adds some instances for limits in condensed sets and condensed modules.
-/

public section

universe u

open CategoryTheory Limits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimits CondensedSet.{u}
  body: by
  change HasLimits (Sheaf _ _)
  infer_instance

中文:
实例 :
  签名: 有极限 CondensedSet.{u}
  定义体: by
  change HasLimits (Sheaf _ _)
  infer_instance

Depends on / 依赖: HasLimits, infer_instance
-/
instance : HasLimits CondensedSet.{u} := by
  change HasLimits (Sheaf _ _)
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimitsOfSize.{u, u + 1} CondensedSet.{u}
  body: hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

中文:
实例 :
  签名: 有LimitsOfSize.{u, u + 1} CondensedSet.{u}
  定义体: hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

Depends on / 依赖: hasLimitsOfSizeShrink
-/
instance : HasLimitsOfSize.{u, u + 1} CondensedSet.{u} :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

variable (R : Type (u + 1)) [Ring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimits (CondensedMod.{u} R)
  body: inferInstanceAs (HasLimits (Sheaf _ _))

中文:
实例 :
  签名: 有极限 (CondensedMod.{u} R)
  定义体: inferInstanceAs (HasLimits (Sheaf _ _))

Depends on / 依赖: HasLimits
-/
instance : HasLimits (CondensedMod.{u} R) :=
  inferInstanceAs (HasLimits (Sheaf _ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimits (CondensedMod.{u} R)
  body: inferInstanceAs (HasColimits (Sheaf _ _))

中文:
实例 :
  签名: 有余极限 (CondensedMod.{u} R)
  定义体: inferInstanceAs (HasColimits (Sheaf _ _))

Depends on / 依赖: HasColimits
-/
instance : HasColimits (CondensedMod.{u} R) :=
  inferInstanceAs (HasColimits (Sheaf _ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimitsOfSize.{u, u + 1} (CondensedMod.{u} R)
  body: hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

中文:
实例 :
  签名: 有LimitsOfSize.{u, u + 1} (CondensedMod.{u} R)
  定义体: hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

Depends on / 依赖: hasLimitsOfSizeShrink
-/
instance : HasLimitsOfSize.{u, u + 1} (CondensedMod.{u} R) :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

instance {A J : Type*} [Category* A] [Category* J] [HasColimitsOfShape J A]
    [HasWeakSheafify (coherentTopology CompHaus.{u}) A] :
    HasColimitsOfShape J (Condensed.{u} A) :=
  inferInstanceAs (HasColimitsOfShape J (Sheaf _ _))

instance {A J : Type*} [Category* A] [Category* J] [HasLimitsOfShape J A] :
    HasLimitsOfShape J (Condensed.{u} A) :=
  inferInstanceAs (HasLimitsOfShape J (Sheaf _ _))

instance {A : Type*} [Category* A] [HasFiniteLimits A] : HasFiniteLimits (Condensed.{u} A) :=
  inferInstanceAs (HasFiniteLimits (Sheaf _ _))

instance {A : Type*} [Category* A] [HasFiniteColimits A]
    [HasWeakSheafify (coherentTopology CompHaus.{u}) A] : HasFiniteColimits (Condensed.{u} A) :=
  inferInstanceAs (HasFiniteColimits (Sheaf _ _))
