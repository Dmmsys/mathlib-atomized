/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic

/-!
# Metrizability of `C(X, Y)`

If `X` is a weakly locally compact σ-compact space and `Y` is a (pseudo)metrizable space,
then `C(X, Y)` is a (pseudo)metrizable space.
-/

public section

open TopologicalSpace

namespace ContinuousMap

variable {X Y : Type*}
  [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
  [TopologicalSpace Y]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoMetrizableSpace
  signature: Y] : PseudoMetrizableSpace C(X, Y)
  body: let := pseudoMetrizableSpaceUniformity Y
  have := pseudoMetrizableSpaceUniformity_countably_generated Y
  inferInstance

中文:
实例 [PseudoMetrizableSpace
  签名: Y] : PseudoMetrizableSpace C(X, Y)
  定义体: let := pseudoMetrizableSpaceUniformity Y
  have := pseudoMetrizableSpaceUniformity_countably_generated Y
  inferInstance

Depends on / 依赖: pseudoMetrizableSpaceUniformity, pseudoMetrizableSpaceUniformity_countably_generated
-/
instance [PseudoMetrizableSpace Y] : PseudoMetrizableSpace C(X, Y) :=
  let := pseudoMetrizableSpaceUniformity Y
  have := pseudoMetrizableSpaceUniformity_countably_generated Y
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MetrizableSpace
  signature: Y] : MetrizableSpace C(X, Y) where

中文:
实例 [MetrizableSpace
  签名: Y] : MetrizableSpace C(X, Y) where
-/
instance [MetrizableSpace Y] : MetrizableSpace C(X, Y) where

end ContinuousMap
