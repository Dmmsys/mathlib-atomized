/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Conversion lemmas

The main procedure of the `compute_asymptotics` tactic is able to compute limits of functions at
`atTop` filter. This file contains lemmas we use to reduce other asymptotic goals to
the case `Tendsto f atTop l`.

## Main theorems

This file contains the following lemmas:
* `tendsto_nhdsGT_of_tendsto_atTop` for `Tendsto f (𝓝[>] c) l`
* `tendsto_nhdsLT_of_tendsto_atTop` for `Tendsto f (𝓝[<] c) l`
* `tendsto_nhdsNE_of_tendsto_atTop` for `Tendsto f (𝓝[≠] c) l`
* `isBigO_of_div_tendsto_atTop` and `isBigO_of_div_tendsto_atBot` for `f =O[l] g`

We also use lemmas from other files:
* `tendsto_comp_neg_atTop_iff` for `Tendsto f atBot l`
* `IsLittleO.of_tendsto_div_atBot` and `IsLittleO.of_tendsto_div_atTop` for `f =o[l] g`
* `isEquivalent_of_tendsto_one` for `f ∼ g`
-/

public section

open Filter Topology Asymptotics

namespace Tactic.ComputeAsymptotics

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] {l : Filter α} (f : 𝕜 -> α) (c : 𝕜)

/--
theorem `tendsto_nhdsGT_of_tendsto_atTop` / 定理 `tendsto_nhdsGT_of_tendsto_atTop`

English:
theorem tendsto_nhdsGT_of_tendsto_atTop
  given: (h : Tendsto (fun x => f (c + x⁻¹)) atTop l)
  proof: by
  simpa [← Function.comp_def, Tendsto, ← Filter.map_map] using h

中文:
定理 tendsto_nhdsGT_of_tendsto_atTop
  条件: (h : 收敛 (fun x => f (c + x⁻¹)) atTop l)
  证明: by
  simpa [← Function.comp_def, Tendsto, ← Filter.map_map] using h

Depends on / 依赖: Filter, Filter.map_map, Function, Function.comp_def, Tendsto, comp_def, map_map
-/
theorem tendsto_nhdsGT_of_tendsto_atTop (h : Tendsto (fun x => f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[>] c) l := by
  simpa [← Function.comp_def, Tendsto, ← Filter.map_map] using h

/--
theorem `tendsto_nhdsLT_of_tendsto_atTop` / 定理 `tendsto_nhdsLT_of_tendsto_atTop`

English:
theorem tendsto_nhdsLT_of_tendsto_atTop
  given: (h : Tendsto (fun x => f (c - x⁻¹)) atTop l)
  proof: by
  convert_to Tendsto (f ∘ (fun x => c + x) ∘ Neg.neg ∘ Inv.inv) atTop l at h
  · ext
    simp [AddGroupWithOne.sub_eq_add_neg]
  simpa [Tendsto, ← Filter.map_map] using h

中文:
定理 tendsto_nhdsLT_of_tendsto_atTop
  条件: (h : 收敛 (fun x => f (c - x⁻¹)) atTop l)
  证明: by
  convert_to Tendsto (f ∘ (fun x => c + x) ∘ Neg.neg ∘ Inv.inv) atTop l at h
  · ext
    simp [AddGroupWithOne.sub_eq_add_neg]
  simpa [Tendsto, ← Filter.map_map] using h

Depends on / 依赖: AddGroupWithOne, AddGroupWithOne.sub_eq_add_neg, Filter, Filter.map_map, Inv.inv, Neg.neg, Tendsto, convert_to, map_map, sub_eq_add_neg
-/
theorem tendsto_nhdsLT_of_tendsto_atTop (h : Tendsto (fun x => f (c - x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] c) l := by
  convert_to Tendsto (f ∘ (fun x => c + x) ∘ Neg.neg ∘ Inv.inv) atTop l at h
  · ext
    simp [AddGroupWithOne.sub_eq_add_neg]
  simpa [Tendsto, ← Filter.map_map] using h

/--
theorem `tendsto_nhdsNE_of_tendsto_atTop` / 定理 `tendsto_nhdsNE_of_tendsto_atTop`

English:
theorem tendsto_nhdsNE_of_tendsto_atTop
  statement: (h_neg : Tendsto (fun x => f (c - x⁻¹)) atTop l)
  proof: by
  simpa [Tendsto, ← nhdsLT_sup_nhdsGT] using
    ⟨tendsto_nhdsLT_of_tendsto_atTop _ _ h_neg, tendsto_nhdsGT_of_tendsto_atTop _ _ h_pos⟩

中文:
定理 tendsto_nhdsNE_of_tendsto_atTop
  结论: (h_neg : 收敛 (fun x => f (c - x⁻¹)) atTop l)
  证明: by
  simpa [Tendsto, ← nhdsLT_sup_nhdsGT] using
    ⟨tendsto_nhdsLT_of_tendsto_atTop _ _ h_neg, tendsto_nhdsGT_of_tendsto_atTop _ _ h_pos⟩

Depends on / 依赖: PreconnectedSpace, Tendsto, h_neg, h_pos, nhdsLT_sup_nhdsGT, ordered_connected_space, tendsto_nhdsGT_of_tendsto_atTop, tendsto_nhdsLT_of_tendsto_atTop
-/
theorem tendsto_nhdsNE_of_tendsto_atTop (h_neg : Tendsto (fun x => f (c - x⁻¹)) atTop l)
    (h_pos : Tendsto (fun x => f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[!=] c) l := by
  simpa [Tendsto, ← nhdsLT_sup_nhdsGT] using
    ⟨tendsto_nhdsLT_of_tendsto_atTop _ _ h_neg, tendsto_nhdsGT_of_tendsto_atTop _ _ h_pos⟩

/--
theorem `tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq` / 定理 `tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq`

English:
theorem tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq
  statement: [TopologicalSpace α] {a b : α}
  proof: by
  apply tendsto_nhdsNE_of_tendsto_atTop _ _ h_neg
  convert! h_pos

中文:
定理 tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq
  结论: [拓扑空间 α] {a b : α}
  证明: by
  apply tendsto_nhdsNE_of_tendsto_atTop _ _ h_neg
  convert! h_pos

Depends on / 依赖: convert, h_neg, h_pos, tendsto_nhdsNE_of_tendsto_atTop
-/
theorem tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq [TopologicalSpace α] {a b : α}
    (h_neg : Tendsto (fun x => f (c - x⁻¹)) atTop (𝓝 a))
    (h_pos : Tendsto (fun x => f (c + x⁻¹)) atTop (𝓝 b)) (h_eq : a = b) :
    Tendsto f (𝓝[!=] c) (𝓝 a) := by
  apply tendsto_nhdsNE_of_tendsto_atTop _ _ h_neg
  convert! h_pos

/--
theorem `isBigOWith_of_tendsto_top` / 定理 `isBigOWith_of_tendsto_top`

English:
theorem isBigOWith_of_tendsto_top
  statement: {C : Real} {f g : Real -> Real} {l : Filter Real}
  proof: Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atTop h) hC

中文:
定理 isBigOWith_of_tendsto_top
  结论: {C : 实数} {f g : 实数 -> 实数} {l : 滤子 实数}
  证明: Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atTop h) hC

Depends on / 依赖: Asymptotics, Asymptotics.IsLittleO.forall_isBigOWith, IsLittleO, forall_isBigOWith, of_tendsto_div_atTop
-/
theorem isBigOWith_of_tendsto_top {C : Real} {f g : Real -> Real} {l : Filter Real}
    (h : Tendsto (fun x => g x / f x) l atTop) (hC : 0 < C) :
    IsBigOWith C l f g :=
  Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atTop h) hC

/--
theorem `isBigOWith_of_tendsto_bot` / 定理 `isBigOWith_of_tendsto_bot`

English:
theorem isBigOWith_of_tendsto_bot
  statement: {C : Real} {f g : Real -> Real} {l : Filter Real}
  proof: Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atBot h) hC

中文:
定理 isBigOWith_of_tendsto_bot
  结论: {C : 实数} {f g : 实数 -> 实数} {l : 滤子 实数}
  证明: Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atBot h) hC

Depends on / 依赖: Asymptotics, Asymptotics.IsLittleO.forall_isBigOWith, IsLittleO, forall_isBigOWith, of_tendsto_div_atBot
-/
theorem isBigOWith_of_tendsto_bot {C : Real} {f g : Real -> Real} {l : Filter Real}
    (h : Tendsto (fun x => g x / f x) l atBot) (hC : 0 < C) :
    IsBigOWith C l f g :=
  Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atBot h) hC

/--
theorem `isBigO_of_div_tendsto_atTop` / 定理 `isBigO_of_div_tendsto_atTop`

English:
theorem isBigO_of_div_tendsto_atTop
  statement: {f g : Real -> Real} {l : Filter Real}
  proof: Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atTop h)

中文:
定理 isBigO_of_div_tendsto_atTop
  结论: {f g : 实数 -> 实数} {l : 滤子 实数}
  证明: Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atTop h)

Depends on / 依赖: Asymptotics, Asymptotics.IsLittleO.isBigO, IsLittleO, isBigO, of_tendsto_div_atTop
-/
theorem isBigO_of_div_tendsto_atTop {f g : Real -> Real} {l : Filter Real}
    (h : Tendsto (fun x => g x / f x) l atTop) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atTop h)

/--
theorem `isBigO_of_div_tendsto_atBot` / 定理 `isBigO_of_div_tendsto_atBot`

English:
theorem isBigO_of_div_tendsto_atBot
  statement: {f g : Real -> Real} {l : Filter Real}
  proof: Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atBot h)

中文:
定理 isBigO_of_div_tendsto_atBot
  结论: {f g : 实数 -> 实数} {l : 滤子 实数}
  证明: Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atBot h)

Depends on / 依赖: Asymptotics, Asymptotics.IsLittleO.isBigO, IsLittleO, isBigO, of_tendsto_div_atBot
-/
theorem isBigO_of_div_tendsto_atBot {f g : Real -> Real} {l : Filter Real}
    (h : Tendsto (fun x => g x / f x) l atBot) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atBot h)

end Tactic.ComputeAsymptotics
