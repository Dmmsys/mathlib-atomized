/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.Order
public import Mathlib.Data.ZMod.Defs

/-!
# Topology on `ZMod N`

We equip `ZMod N` with the discrete topology.
-/

public section

namespace ZMod

variable {N : Nat}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (ZMod N)
  body: ⊥

中文:
实例 :
  签名: TopologicalSpace (ZMod N)
  定义体: ⊥
-/
instance : TopologicalSpace (ZMod N) := ⊥

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology (ZMod N)
  body: ⟨rfl⟩

中文:
实例 :
  签名: DiscreteTopology (ZMod N)
  定义体: ⟨rfl⟩
-/
instance : DiscreteTopology (ZMod N) := ⟨rfl⟩

end ZMod
