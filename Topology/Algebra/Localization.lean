/-
Copyright (c) 2021 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.Topology.Algebra.Ring.Basic

/-!

# Localization of topological rings

The topological localization of a topological commutative ring `R` at a submonoid `M` is the ring
`Localization M` endowed with the final ring topology of the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)` in the localization of `R` at an `M`.

## Main Results

- `Localization.ringTopology`: The localization of a topological commutative ring at a submonoid
  is a topological ring.

-/

@[expose] public section


variable {R : Type*} [CommRing R] [TopologicalSpace R] {M : Submonoid R}

/--
Definition of `Localization.ringTopology` / `Localization.ringTopology` 的定义

English:
definition Localization.ringTopology
  signature: : RingTopology (Localization M)
  body: RingTopology.coinduced (Localization.monoidOf M).toFun

中文:
定义 Localization.ringTopology
  签名: : 环拓扑 (Localization M)
  定义体: RingTopology.coinduced (Localization.monoidOf M).toFun

Depends on / 依赖: Localization, Localization.monoidOf, RingTopology, RingTopology.coinduced, coinduced, monoidOf
-/
def Localization.ringTopology : RingTopology (Localization M) :=
  RingTopology.coinduced (Localization.monoidOf M).toFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (Localization M)
  body: Localization.ringTopology.toTopologicalSpace

中文:
实例 :
  签名: 拓扑空间 (Localization M)
  定义体: Localization.ringTopology.toTopologicalSpace

Depends on / 依赖: Localization, Localization.ringTopology.toTopologicalSpace, ringTopology, toTopologicalSpace
-/
instance : TopologicalSpace (Localization M) :=
  Localization.ringTopology.toTopologicalSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalRing (Localization M)
  body: Localization.ringTopology.toIsTopologicalRing

中文:
实例 :
  签名: 是拓扑环 (Localization M)
  定义体: Localization.ringTopology.toIsTopologicalRing

Depends on / 依赖: Localization, Localization.ringTopology.toIsTopologicalRing, ringTopology, toIsTopologicalRing
-/
instance : IsTopologicalRing (Localization M) :=
  Localization.ringTopology.toIsTopologicalRing
