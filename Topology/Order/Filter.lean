/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Filter
public import Mathlib.Topology.Order.Basic

/-!
# Topology on filters of a space with order topology

In this file we prove that `𝓝 (f x)` tends to `𝓝 Filter.atTop` provided that `f` tends to
`Filter.atTop`, and similarly for `Filter.atBot`.
-/

public section


open Topology

namespace Filter

variable {α X : Type*} [TopologicalSpace X] [PartialOrder X] [OrderTopology X]

/--
theorem `tendsto_nhds_atTop` / 定理 `tendsto_nhds_atTop`

English:
theorem tendsto_nhds_atTop
  given: [NoMaxOrder X]
  statement: Tendsto 𝓝 (atTop : Filter X) (𝓝 atTop)
  proof: Filter.tendsto_nhds_atTop_iff.2 fun x => (eventually_gt_atTop x).mono fun _ => le_mem_nhds

中文:
定理 tendsto_nhds_atTop
  条件: [NoMaxOrder X]
  结论: Tendsto 𝓝 (atTop : Filter X) (𝓝 atTop)
  证明: Filter.tendsto_nhds_atTop_iff.2 fun x => (eventually_gt_atTop x).mono fun _ => le_mem_nhds
-/
protected theorem tendsto_nhds_atTop [NoMaxOrder X] : Tendsto 𝓝 (atTop : Filter X) (𝓝 atTop) :=
  Filter.tendsto_nhds_atTop_iff.2 fun x => (eventually_gt_atTop x).mono fun _ => le_mem_nhds

/--
theorem `tendsto_nhds_atBot` / 定理 `tendsto_nhds_atBot`

English:
theorem tendsto_nhds_atBot
  given: [NoMinOrder X]
  statement: Tendsto 𝓝 (atBot : Filter X) (𝓝 atBot)
  proof: @Filter.tendsto_nhds_atTop Xᵒᵈ _ _ _ _

中文:
定理 tendsto_nhds_atBot
  条件: [NoMinOrder X]
  结论: Tendsto 𝓝 (atBot : Filter X) (𝓝 atBot)
  证明: @Filter.tendsto_nhds_atTop Xᵒᵈ _ _ _ _
-/
protected theorem tendsto_nhds_atBot [NoMinOrder X] : Tendsto 𝓝 (atBot : Filter X) (𝓝 atBot) :=
  @Filter.tendsto_nhds_atTop Xᵒᵈ _ _ _ _

/--
theorem `Tendsto.nhds_atTop` / 定理 `Tendsto.nhds_atTop`

English:
theorem Tendsto.nhds_atTop
  given: [NoMaxOrder X] {f : α -> X} {l : Filter α} (h : Tendsto f l atTop)
  proof: Filter.tendsto_nhds_atTop.comp h

中文:
定理 Tendsto.nhds_atTop
  条件: [NoMaxOrder X] {f : α -> X} {l : Filter α} (h : Tendsto f l atTop)
  证明: Filter.tendsto_nhds_atTop.comp h

Depends on / 依赖: Filter, Filter.tendsto_nhds_atTop.comp, tendsto_nhds_atTop
-/
theorem Tendsto.nhds_atTop [NoMaxOrder X] {f : α -> X} {l : Filter α} (h : Tendsto f l atTop) :
    Tendsto (𝓝 ∘ f) l (𝓝 atTop) :=
  Filter.tendsto_nhds_atTop.comp h

/--
theorem `Tendsto.nhds_atBot` / 定理 `Tendsto.nhds_atBot`

English:
theorem Tendsto.nhds_atBot
  given: [NoMinOrder X] {f : α -> X} {l : Filter α} (h : Tendsto f l atBot)
  proof: @Tendsto.nhds_atTop α Xᵒᵈ _ _ _ _ _ _ h

中文:
定理 Tendsto.nhds_atBot
  条件: [NoMinOrder X] {f : α -> X} {l : Filter α} (h : Tendsto f l atBot)
  证明: @Tendsto.nhds_atTop α Xᵒᵈ _ _ _ _ _ _ h

Depends on / 依赖: Tendsto, Tendsto.nhds_atTop, nhds_atTop
-/
theorem Tendsto.nhds_atBot [NoMinOrder X] {f : α -> X} {l : Filter α} (h : Tendsto f l atBot) :
    Tendsto (𝓝 ∘ f) l (𝓝 atBot) :=
  @Tendsto.nhds_atTop α Xᵒᵈ _ _ _ _ _ _ h

end Filter
