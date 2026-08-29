/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Logic.Small.Defs
public import Mathlib.Topology.Homeomorph.TransferInstance

/-!
# Topological space structure on `Shrink X`
-/

@[expose] public section

universe v u

namespace Shrink

noncomputable instance (X : Type u) [TopologicalSpace X] [Small.{v} X] :
    TopologicalSpace (Shrink.{v} X) :=
  (equivShrink X).symm.topologicalSpace

/-- `equivShrink` as a homeomorphism. -/
@[simps! toEquiv]
/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: (X : Type u) [TopologicalSpace X] [Small.{v} X]
  body: (equivShrink X).symm.homeomorph.symm

中文:
定义 homeomorph
  签名: (X : 类型u) [TopologicalSpace X] [Small.{v} X]
  定义体: (equivShrink X).symm.homeomorph.symm

Depends on / 依赖: equivShrink, homeomorph, symm.homeomorph.symm
-/
noncomputable def homeomorph (X : Type u) [TopologicalSpace X] [Small.{v} X] :
    X ≃ₜ Shrink.{v} X :=
  (equivShrink X).symm.homeomorph.symm

end Shrink
