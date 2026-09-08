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

/-
**LightProfinite.** 是 Mathlib 中的一个实例，位于命名空间 `LightProfinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CartesianMonoidalCategory LightProfinite.{u} :=
  cartesianMonoidalCategory

end LightProfinite

