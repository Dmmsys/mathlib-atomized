/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.TotallyDisconnected
/-!

# Separation and (dis)connectedness properties of topological spaces.

This file provides an instance `T2Space X` given `TotallySeparatedSpace X`.

## TODO
* Move the last part of `Topology/Separation` to this file.
-/

public section


variable {X : Type*} [TopologicalSpace X]

section TotallySeparated

/--
Instance `TotallySeparatedSpace.t2Space` / 实例 `TotallySeparatedSpace.t2Space`

English:
instance TotallySeparatedSpace.t2Space
  signature: [TotallySeparatedSpace X]
  body: by
    obtain ⟨u, v, h₁, h₂, h₃, h₄, _, h₅⟩ := isTotallySeparated_univ trivial trivial h
    exact ⟨u, v, h₁, h₂, h₃, h₄, h₅⟩

中文:
实例 TotallySeparatedSpace.t2Space
  签名: [TotallySeparatedSpace X]
  定义体: by
    obtain ⟨u, v, h₁, h₂, h₃, h₄, _, h₅⟩ := isTotallySeparated_univ trivial trivial h
    exact ⟨u, v, h₁, h₂, h₃, h₄, h₅⟩

Depends on / 依赖: isTotallySeparated_univ
-/
instance TotallySeparatedSpace.t2Space [TotallySeparatedSpace X] : T2Space X where
  t2 x y h := by
    obtain ⟨u, v, h₁, h₂, h₃, h₄, _, h₅⟩ := isTotallySeparated_univ trivial trivial h
    exact ⟨u, v, h₁, h₂, h₃, h₄, h₅⟩

end TotallySeparated
