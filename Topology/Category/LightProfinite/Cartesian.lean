/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.CompHausLike.Cartesian
public import Mathlib.Topology.Category.LightProfinite.Basic

/-!
# Cartesian monoidal structure on `LightProfinite`

This file defines the cartesian monoidal structure on `LightProfinite` given by the type-theoretic
product.

-/

public section

universe u

open CategoryTheory Limits CompHausLike

namespace LightProfinite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CartesianMonoidalCategory LightProfinite.{u}
  body: cartesianMonoidalCategory

中文:
实例 :
  签名: CartesianMonoidalCategory LightProfinite.{u}
  定义体: cartesianMonoidalCategory

Depends on / 依赖: cartesianMonoidalCategory
-/
instance : CartesianMonoidalCategory LightProfinite.{u} :=
  cartesianMonoidalCategory

end LightProfinite
