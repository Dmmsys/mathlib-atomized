/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Module.Convex
/-!
# "Gauge rescale" homeomorphism between convex sets

Given two convex von Neumann bounded neighbourhoods of the origin
in a real topological vector space,
we construct a homeomorphism `gaugeRescaleHomeomorph`
that sends the interior, the closure, and the frontier of one set
to the interior, the closure, and the frontier of the other set.
-/

@[expose] public section

open Metric Bornology Filter Set
open scoped NNReal Topology Pointwise

noncomputable section

section Module

variable {E : Type*} [AddCommGroup E] [Module Real E]

/--
Definition of `gaugeRescale` / `gaugeRescale` 的定义

English:
definition gaugeRescale
  signature: (s t : Set E) (x : E)
  body: (gauge s x / gauge t x) • x

中文:
定义 gaugeRescale
  签名: (s t : 集合 E) (x : E)
  定义体: (gauge s x / gauge t x) • x
-/
def gaugeRescale (s t : Set E) (x : E) : E := (gauge s x / gauge t x) • x

/--
theorem `gaugeRescale_def` / 定理 `gaugeRescale_def`

English:
theorem gaugeRescale_def
  given: (s t : Set E) (x : E)
  proof: rfl

中文:
定理 gaugeRescale_def
  条件: (s t : 集合 E) (x : E)
  证明: rfl
-/
theorem gaugeRescale_def (s t : Set E) (x : E) :
    gaugeRescale s t x = (gauge s x / gauge t x) • x :=
  rfl

/--
theorem `gaugeRescale_zero` / 定理 `gaugeRescale_zero`

English:
theorem gaugeRescale_zero
  given: (s t : Set E)
  statement: gaugeRescale s t 0 = 0
  proof: smul_zero _

中文:
定理 gaugeRescale_zero
  条件: (s t : 集合 E)
  结论: gaugeRescale s t 0 = 0
  证明: smul_zero _
-/
@[simp] theorem gaugeRescale_zero (s t : Set E) : gaugeRescale s t 0 = 0 := smul_zero _

/--
theorem `gaugeRescale_smul` / 定理 `gaugeRescale_smul`

English:
theorem gaugeRescale_smul
  given: (s t : Set E) {c : Real} (hc : 0 <= c) (x : E)
  proof: by
  simp only [gaugeRescale, gauge_smul_of_nonneg hc, smul_smul, smul_eq_mul]
  rw [mul_div_mul_comm]; rw [mul_right_comm]; rw [div_self_mul_self]

中文:
定理 gaugeRescale_smul
  条件: (s t : 集合 E) {c : 实数} (hc : 0 <= c) (x : E)
  证明: by
  simp only [gaugeRescale, gauge_smul_of_nonneg hc, smul_smul, smul_eq_mul]
  rw [mul_div_mul_comm]; rw [mul_right_comm]; rw [div_self_mul_self]

Depends on / 依赖: div_self_mul_self, gaugeRescale, gauge_smul_of_nonneg, mul_div_mul_comm, mul_right_comm, smul_eq_mul, smul_smul
-/
theorem gaugeRescale_smul (s t : Set E) {c : Real} (hc : 0 <= c) (x : E) :
    gaugeRescale s t (c • x) = c • gaugeRescale s t x := by
  simp only [gaugeRescale, gauge_smul_of_nonneg hc, smul_smul, smul_eq_mul]
  rw [mul_div_mul_comm]; rw [mul_right_comm]; rw [div_self_mul_self]

/--
theorem `gauge_gaugeRescale'` / 定理 `gauge_gaugeRescale'`

English:
theorem gauge_gaugeRescale'
  given: (s : Set E) {t : Set E} {x : E} (hx : gauge t x != 0)
  proof: by
  rw [gaugeRescale]; rw [gauge_smul_of_nonneg (div_nonneg (gauge_nonneg _) (gauge_nonneg _))]; rw [smul_eq_mul]; rw [div_mul_cancel₀ _ hx]

中文:
定理 gauge_gaugeRescale'
  条件: (s : 集合 E) {t : 集合 E} {x : E} (hx : gauge t x != 0)
  证明: by
  rw [gaugeRescale]; rw [gauge_smul_of_nonneg (div_nonneg (gauge_nonneg _) (gauge_nonneg _))]; rw [smul_eq_mul]; rw [div_mul_cancel₀ _ hx]

Depends on / 依赖: div_nonneg, gaugeRescale, gauge_nonneg, gauge_smul_of_nonneg, smul_eq_mul
-/
theorem gauge_gaugeRescale' (s : Set E) {t : Set E} {x : E} (hx : gauge t x != 0) :
    gauge t (gaugeRescale s t x) = gauge s x := by
  rw [gaugeRescale]; rw [gauge_smul_of_nonneg (div_nonneg (gauge_nonneg _) (gauge_nonneg _))]; rw [smul_eq_mul]; rw [div_mul_cancel₀ _ hx]

/--
theorem `gauge_gaugeRescale_le` / 定理 `gauge_gaugeRescale_le`

English:
theorem gauge_gaugeRescale_le
  given: (s t : Set E) (x : E)
  proof: by
  by_cases hx : gauge t x = 0
  · simp [gaugeRescale, hx, gauge_nonneg]
  · exact (gauge_gaugeRescale' s hx).le

中文:
定理 gauge_gaugeRescale_le
  条件: (s t : 集合 E) (x : E)
  证明: by
  by_cases hx : gauge t x = 0
  · simp [gaugeRescale, hx, gauge_nonneg]
  · exact (gauge_gaugeRescale' s hx).le

Depends on / 依赖: gaugeRescale, gauge_gaugeRescale, gauge_nonneg
-/
theorem gauge_gaugeRescale_le (s t : Set E) (x : E) :
    gauge t (gaugeRescale s t x) <= gauge s x := by
  by_cases hx : gauge t x = 0
  · simp [gaugeRescale, hx, gauge_nonneg]
  · exact (gauge_gaugeRescale' s hx).le

variable [TopologicalSpace E]

section
variable [T1Space E]

/--
theorem `gaugeRescale_self_apply` / 定理 `gaugeRescale_self_apply`

English:
theorem gaugeRescale_self_apply
  statement: {s : Set E} (hsa : Absorbent Real s) (hsb : IsVonNBounded Real s)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale]; rw [div_self]; rw [one_smul]
  exact ((gauge_pos hsa hsb).2 hx).ne'

中文:
定理 gaugeRescale_self_apply
  结论: {s : 集合 E} (hsa : Absorbent 实数 s) (hsb : IsVonNBounded 实数 s)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale]; rw [div_self]; rw [one_smul]
  exact ((gauge_pos hsa hsb).2 hx).ne'

Depends on / 依赖: div_self, eq_or_ne, gaugeRescale, gauge_pos, one_smul
-/
theorem gaugeRescale_self_apply {s : Set E} (hsa : Absorbent Real s) (hsb : IsVonNBounded Real s)
    (x : E) : gaugeRescale s s x = x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale]; rw [div_self]; rw [one_smul]
  exact ((gauge_pos hsa hsb).2 hx).ne'

/--
theorem `gaugeRescale_self` / 定理 `gaugeRescale_self`

English:
theorem gaugeRescale_self
  given: {s : Set E} (hsa : Absorbent Real s) (hsb : IsVonNBounded Real s)
  proof: funext gaugeRescale_self_apply hsa hsb

中文:
定理 gaugeRescale_self
  条件: {s : 集合 E} (hsa : Absorbent 实数 s) (hsb : IsVonNBounded 实数 s)
  证明: funext gaugeRescale_self_apply hsa hsb

Depends on / 依赖: gaugeRescale_self_apply
-/
theorem gaugeRescale_self {s : Set E} (hsa : Absorbent Real s) (hsb : IsVonNBounded Real s) :
    gaugeRescale s s = id :=
funext gaugeRescale_self_apply hsa hsb

/--
theorem `gauge_gaugeRescale` / 定理 `gauge_gaugeRescale`

English:
theorem gauge_gaugeRescale
  statement: (s : Set E) {t : Set E} (hta : Absorbent Real t) (htb : IsVonNBounded Real t)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact gauge_gaugeRescale' s ((gauge_pos hta htb).2 hx).ne'

中文:
定理 gauge_gaugeRescale
  结论: (s : 集合 E) {t : 集合 E} (hta : Absorbent 实数 t) (htb : IsVonNBounded 实数 t)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact gauge_gaugeRescale' s ((gauge_pos hta htb).2 hx).ne'

Depends on / 依赖: eq_or_ne, gauge_gaugeRescale, gauge_pos
-/
theorem gauge_gaugeRescale (s : Set E) {t : Set E} (hta : Absorbent Real t) (htb : IsVonNBounded Real t)
    (x : E) : gauge t (gaugeRescale s t x) = gauge s x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact gauge_gaugeRescale' s ((gauge_pos hta htb).2 hx).ne'

/--
theorem `gaugeRescale_gaugeRescale` / 定理 `gaugeRescale_gaugeRescale`

English:
theorem gaugeRescale_gaugeRescale
  statement: {s t u : Set E} (hta : Absorbent Real t) (htb : IsVonNBounded Real t)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale_def s t x]; rw [gaugeRescale_smul]; rw [gaugeRescale]; rw [gaugeRescale]; rw [smul_smul]; rw [div_mul_div_cancel₀]
  exacts [((gauge_pos hta htb).2 hx).ne', div_nonneg (gauge_nonneg _) (gauge_nonneg _)]

中文:
定理 gaugeRescale_gaugeRescale
  结论: {s t u : 集合 E} (hta : Absorbent 实数 t) (htb : IsVonNBounded 实数 t)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale_def s t x]; rw [gaugeRescale_smul]; rw [gaugeRescale]; rw [gaugeRescale]; rw [smul_smul]; rw [div_mul_div_cancel₀]
  exacts [((gauge_pos hta htb).2 hx).ne', div_nonneg (gauge_nonneg _) (gauge_nonneg _)]

Depends on / 依赖: div_nonneg, eq_or_ne, exacts, gaugeRescale, gaugeRescale_def, gaugeRescale_smul, gauge_nonneg, gauge_pos, smul_smul
-/
theorem gaugeRescale_gaugeRescale {s t u : Set E} (hta : Absorbent Real t) (htb : IsVonNBounded Real t)
    (x : E) : gaugeRescale t u (gaugeRescale s t x) = gaugeRescale s u x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale_def s t x]; rw [gaugeRescale_smul]; rw [gaugeRescale]; rw [gaugeRescale]; rw [smul_smul]; rw [div_mul_div_cancel₀]
  exacts [((gauge_pos hta htb).2 hx).ne', div_nonneg (gauge_nonneg _) (gauge_nonneg _)]

/--
Definition of `gaugeRescaleEquiv` / `gaugeRescaleEquiv` 的定义

English:
definition gaugeRescaleEquiv
  signature: (s t : Set E) (hsa : Absorbent Real s) (hsb : IsVonNBounded Real s)
  body: gaugeRescale s t
  invFun := gaugeRescale t s
  left_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption
  right_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption

中文:
定义 gaugeRescaleEquiv
  签名: (s t : 集合 E) (hsa : Absorbent 实数 s) (hsb : IsVonNBounded 实数 s)
  定义体: gaugeRescale s t
  invFun := gaugeRescale t s
  left_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption
  right_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption

Depends on / 依赖: gaugeRescale
-/
def gaugeRescaleEquiv (s t : Set E) (hsa : Absorbent Real s) (hsb : IsVonNBounded Real s)
    (hta : Absorbent Real t) (htb : IsVonNBounded Real t) : E ≃ E where
  toFun := gaugeRescale s t
  invFun := gaugeRescale t s
  left_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption
  right_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption

end

variable [IsTopologicalAddGroup E] [ContinuousSMul Real E] {s t : Set E}

/--
theorem `mapsTo_gaugeRescale_interior` / 定理 `mapsTo_gaugeRescale_interior`

English:
theorem mapsTo_gaugeRescale_interior
  given: (h₀ : t in 𝓝 0) (hc : Convex Real t)
  proof: fun x hx => by
  rw [← gauge_lt_one_iff_mem_interior] <;> try assumption
  exact (gauge_gaugeRescale_le _ _ _).trans_lt (interior_subset_gauge_lt_one _ hx)

中文:
定理 mapsTo_gaugeRescale_interior
  条件: (h₀ : t in 𝓝 0) (hc : 凸 实数 t)
  证明: fun x hx => by
  rw [← gauge_lt_one_iff_mem_interior] <;> try assumption
  exact (gauge_gaugeRescale_le _ _ _).trans_lt (interior_subset_gauge_lt_one _ hx)

Depends on / 依赖: gauge_gaugeRescale_le, gauge_lt_one_iff_mem_interior, interior_subset_gauge_lt_one, trans_lt
-/
theorem mapsTo_gaugeRescale_interior (h₀ : t in 𝓝 0) (hc : Convex Real t) :
    MapsTo (gaugeRescale s t) (interior s) (interior t) := fun x hx => by
  rw [← gauge_lt_one_iff_mem_interior] <;> try assumption
  exact (gauge_gaugeRescale_le _ _ _).trans_lt (interior_subset_gauge_lt_one _ hx)

/--
theorem `mapsTo_gaugeRescale_closure` / 定理 `mapsTo_gaugeRescale_closure`

English:
theorem mapsTo_gaugeRescale_closure
  statement: {s t : Set E} (hsc : Convex Real s) (hs₀ : s in 𝓝 0)
  proof: fun _x hx =>
mem_closure_of_gauge_le_one htc ht₀ hta (gauge_gaugeRescale_le _ _ _).trans
    (gauge_le_one_iff_mem_closure hsc hs₀).2 hx

中文:
定理 mapsTo_gaugeRescale_closure
  结论: {s t : 集合 E} (hsc : 凸 实数 s) (hs₀ : s in 𝓝 0)
  证明: fun _x hx =>
mem_closure_of_gauge_le_one htc ht₀ hta (gauge_gaugeRescale_le _ _ _).trans
    (gauge_le_one_iff_mem_closure hsc hs₀).2 hx
-/
theorem mapsTo_gaugeRescale_closure {s t : Set E} (hsc : Convex Real s) (hs₀ : s in 𝓝 0)
    (htc : Convex Real t) (ht₀ : 0 in t) (hta : Absorbent Real t) :
    MapsTo (gaugeRescale s t) (closure s) (closure t) := fun _x hx =>
mem_closure_of_gauge_le_one htc ht₀ hta (gauge_gaugeRescale_le _ _ _).trans
    (gauge_le_one_iff_mem_closure hsc hs₀).2 hx

variable [T1Space E]

/--
theorem `continuous_gaugeRescale` / 定理 `continuous_gaugeRescale`

English:
theorem continuous_gaugeRescale
  statement: {s t : Set E} (hs : Convex Real s) (hs₀ : s in 𝓝 0)
  proof: by
  have hta : Absorbent Real t := absorbent_nhds_zero ht₀
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, gaugeRescale_zero]
    nth_rewrite 2 [← comap_gauge_nhds_zero htb ht₀]
    simp only [tendsto_comap_iff, Function.comp_def, gauge_gaugeRescale _ hta htb]
    exact tendsto_gauge_nhds_zero hs₀
  · exact ((continuousAt_gauge hs hs₀).div (continuousAt_gauge ht ht₀)
      ((gauge_pos hta htb).2 hx).ne').smul continuousAt_id

中文:
定理 continuous_gaugeRescale
  结论: {s t : 集合 E} (hs : 凸 实数 s) (hs₀ : s in 𝓝 0)
  证明: by
  have hta : Absorbent Real t := absorbent_nhds_zero ht₀
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, gaugeRescale_zero]
    nth_rewrite 2 [← comap_gauge_nhds_zero htb ht₀]
    simp only [tendsto_comap_iff, Function.comp_def, gauge_gaugeRescale _ hta htb]
    exact tendsto_gauge_nhds_zero hs₀
  · exact ((continuousAt_gauge hs hs₀).div (continuousAt_gauge ht ht₀)
      ((gauge_pos hta htb).2 hx).ne').smul continuousAt_id

Depends on / 依赖: Absorbent, ContinuousAt, Function, Function.comp_def, absorbent_nhds_zero, comap_gauge_nhds_zero, comp_def, continuousAt_gauge, continuousAt_id, continuous_iff_continuousAt, eq_or_ne, gaugeRescale_zero, gauge_gaugeRescale, gauge_pos, nth_rewrite, tendsto_comap_iff, tendsto_gauge_nhds_zero
-/
theorem continuous_gaugeRescale {s t : Set E} (hs : Convex Real s) (hs₀ : s in 𝓝 0)
    (ht : Convex Real t) (ht₀ : t in 𝓝 0) (htb : IsVonNBounded Real t) :
    Continuous (gaugeRescale s t) := by
  have hta : Absorbent Real t := absorbent_nhds_zero ht₀
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, gaugeRescale_zero]
    nth_rewrite 2 [← comap_gauge_nhds_zero htb ht₀]
    simp only [tendsto_comap_iff, Function.comp_def, gauge_gaugeRescale _ hta htb]
    exact tendsto_gauge_nhds_zero hs₀
  · exact ((continuousAt_gauge hs hs₀).div (continuousAt_gauge ht ht₀)
      ((gauge_pos hta htb).2 hx).ne').smul continuousAt_id

/--
Definition of `gaugeRescaleHomeomorph` / `gaugeRescaleHomeomorph` 的定义

English:
definition gaugeRescaleHomeomorph
  signature: (s t : Set E)
  body: gaugeRescaleEquiv s t (absorbent_nhds_zero hs₀) hsb (absorbent_nhds_zero ht₀) htb
  continuous_toFun := by apply continuous_gaugeRescale <;> assumption
  continuous_invFun := by apply continuous_gaugeRescale <;> assumption

中文:
定义 gaugeRescaleHomeomorph
  签名: (s t : 集合 E)
  定义体: gaugeRescaleEquiv s t (absorbent_nhds_zero hs₀) hsb (absorbent_nhds_zero ht₀) htb
  continuous_toFun := by apply continuous_gaugeRescale <;> assumption
  continuous_invFun := by apply continuous_gaugeRescale <;> assumption

Depends on / 依赖: absorbent_nhds_zero, gaugeRescaleEquiv
-/
def gaugeRescaleHomeomorph (s t : Set E)
    (hsc : Convex Real s) (hs₀ : s in 𝓝 0) (hsb : IsVonNBounded Real s)
    (htc : Convex Real t) (ht₀ : t in 𝓝 0) (htb : IsVonNBounded Real t) : E ≃ₜ E where
  toEquiv := gaugeRescaleEquiv s t (absorbent_nhds_zero hs₀) hsb (absorbent_nhds_zero ht₀) htb
  continuous_toFun := by apply continuous_gaugeRescale <;> assumption
  continuous_invFun := by apply continuous_gaugeRescale <;> assumption

/--
theorem `image_gaugeRescaleHomeomorph_interior` / 定理 `image_gaugeRescaleHomeomorph_interior`

English:
theorem image_gaugeRescaleHomeomorph_interior
  statement: {s t : Set E}
  proof: Subset.antisymm (mapsTo_gaugeRescale_interior ht₀ htc).image_subset by
    rw [← Homeomorph.preimage_symm]; rw [← image_subset_iff]
    exact (mapsTo_gaugeRescale_interior hs₀ hsc).image_subset

中文:
定理 image_gaugeRescaleHomeomorph_interior
  结论: {s t : 集合 E}
  证明: Subset.antisymm (mapsTo_gaugeRescale_interior ht₀ htc).image_subset by
    rw [← Homeomorph.preimage_symm]; rw [← image_subset_iff]
    exact (mapsTo_gaugeRescale_interior hs₀ hsc).image_subset

Depends on / 依赖: Homeomorph, Homeomorph.preimage_symm, Subset, Subset.antisymm, antisymm, image_subset, image_subset_iff, mapsTo_gaugeRescale_interior, preimage_symm
-/
theorem image_gaugeRescaleHomeomorph_interior {s t : Set E}
    (hsc : Convex Real s) (hs₀ : s in 𝓝 0) (hsb : IsVonNBounded Real s)
    (htc : Convex Real t) (ht₀ : t in 𝓝 0) (htb : IsVonNBounded Real t) :
    gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht₀ htb '' interior s = interior t :=
Subset.antisymm (mapsTo_gaugeRescale_interior ht₀ htc).image_subset by
    rw [← Homeomorph.preimage_symm]; rw [← image_subset_iff]
    exact (mapsTo_gaugeRescale_interior hs₀ hsc).image_subset

/--
theorem `image_gaugeRescaleHomeomorph_closure` / 定理 `image_gaugeRescaleHomeomorph_closure`

English:
theorem image_gaugeRescaleHomeomorph_closure
  statement: {s t : Set E}
  proof: by
  refine Subset.antisymm (mapsTo_gaugeRescale_closure hsc hs₀ htc
    (mem_of_mem_nhds ht₀) (absorbent_nhds_zero ht₀)).image_subset ?_
  rw [← Homeomorph.preimage_symm]; rw [← image_subset_iff]
  exact (mapsTo_gaugeRescale_closure htc ht₀ hsc
    (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀)).image_subset

中文:
定理 image_gaugeRescaleHomeomorph_closure
  结论: {s t : 集合 E}
  证明: by
  refine Subset.antisymm (mapsTo_gaugeRescale_closure hsc hs₀ htc
    (mem_of_mem_nhds ht₀) (absorbent_nhds_zero ht₀)).image_subset ?_
  rw [← Homeomorph.preimage_symm]; rw [← image_subset_iff]
  exact (mapsTo_gaugeRescale_closure htc ht₀ hsc
    (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀)).image_subset

Depends on / 依赖: Homeomorph, Homeomorph.preimage_symm, Subset, Subset.antisymm, absorbent_nhds_zero, antisymm, image_subset, image_subset_iff, mapsTo_gaugeRescale_closure, mem_of_mem_nhds, preimage_symm
-/
theorem image_gaugeRescaleHomeomorph_closure {s t : Set E}
    (hsc : Convex Real s) (hs₀ : s in 𝓝 0) (hsb : IsVonNBounded Real s)
    (htc : Convex Real t) (ht₀ : t in 𝓝 0) (htb : IsVonNBounded Real t) :
    gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht₀ htb '' closure s = closure t := by
  refine Subset.antisymm (mapsTo_gaugeRescale_closure hsc hs₀ htc
    (mem_of_mem_nhds ht₀) (absorbent_nhds_zero ht₀)).image_subset ?_
  rw [← Homeomorph.preimage_symm]; rw [← image_subset_iff]
  exact (mapsTo_gaugeRescale_closure htc ht₀ hsc
    (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀)).image_subset

/--
theorem `exists_homeomorph_image_eq` / 定理 `exists_homeomorph_image_eq`

English:
theorem exists_homeomorph_image_eq
  statement: {s t : Set E}
  proof: by
  rsuffices ⟨e, h₁, h₂⟩ : exists e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t
  · refine ⟨e, h₁, h₂, ?_⟩
    simp_rw [← closure_sdiff_interior, image_sdiff e.injective, h₁, h₂]
  rcases hsne with ⟨x, hx⟩
  rcases htne with ⟨y, hy⟩
  set h : E ≃ₜ E := by
    apply gaugeRescaleHomeomorph (-x +ᵥ s) (-y +ᵥ t) <;>
      simp [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem, *]
refine ⟨.trans (.addLeft (-x)) h.trans .addLeft y, ?_, ?_⟩
  · calc
      (fun a => y + h (-x + a)) '' interior s = y +ᵥ h '' interior (-x +ᵥ s) := by
        simp_rw [interior_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_interior, interior_vadd, vadd_neg_vadd]
  · calc
      (fun a => y + h (-x + a)) '' closure s = y +ᵥ h '' closure (-x +ᵥ s) := by
        simp_rw [closure_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_closure, closure_vadd, vadd_neg_vadd]

中文:
定理 存在_homeomorph_image_eq
  结论: {s t : 集合 E}
  证明: by
  rsuffices ⟨e, h₁, h₂⟩ : exists e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t
  · refine ⟨e, h₁, h₂, ?_⟩
    simp_rw [← closure_sdiff_interior, image_sdiff e.injective, h₁, h₂]
  rcases hsne with ⟨x, hx⟩
  rcases htne with ⟨y, hy⟩
  set h : E ≃ₜ E := by
    apply gaugeRescaleHomeomorph (-x +ᵥ s) (-y +ᵥ t) <;>
      simp [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem, *]
refine ⟨.trans (.addLeft (-x)) h.trans .addLeft y, ?_, ?_⟩
  · calc
      (fun a => y + h (-x + a)) '' interior s = y +ᵥ h '' interior (-x +ᵥ s) := by
        simp_rw [interior_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_interior, interior_vadd, vadd_neg_vadd]
  · calc
      (fun a => y + h (-x + a)) '' closure s = y +ᵥ h '' closure (-x +ᵥ s) := by
        simp_rw [closure_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_closure, closure_vadd, vadd_neg_vadd]

Depends on / 依赖: addLeft, closure, closure_sdiff_interior, e.injective, gaugeRescaleHomeomorph, h.trans, image_sdiff, injective, interior, interior_vadd, mem_interior_iff_mem_nhds, mem_vadd_set_iff_neg_vadd_mem, rsuffices, simp_rw
-/
theorem exists_homeomorph_image_eq {s t : Set E}
    (hsc : Convex Real s) (hsne : (interior s).Nonempty) (hsb : IsVonNBounded Real s)
    (hst : Convex Real t) (htne : (interior t).Nonempty) (htb : IsVonNBounded Real t) :
    exists e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t ∧
      e '' frontier s = frontier t := by
  rsuffices ⟨e, h₁, h₂⟩ : exists e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t
  · refine ⟨e, h₁, h₂, ?_⟩
    simp_rw [← closure_sdiff_interior, image_sdiff e.injective, h₁, h₂]
  rcases hsne with ⟨x, hx⟩
  rcases htne with ⟨y, hy⟩
  set h : E ≃ₜ E := by
    apply gaugeRescaleHomeomorph (-x +ᵥ s) (-y +ᵥ t) <;>
      simp [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem, *]
refine ⟨.trans (.addLeft (-x)) h.trans .addLeft y, ?_, ?_⟩
  · calc
      (fun a => y + h (-x + a)) '' interior s = y +ᵥ h '' interior (-x +ᵥ s) := by
        simp_rw [interior_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_interior, interior_vadd, vadd_neg_vadd]
  · calc
      (fun a => y + h (-x + a)) '' closure s = y +ᵥ h '' closure (-x +ᵥ s) := by
        simp_rw [closure_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_closure, closure_vadd, vadd_neg_vadd]

end Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
theorem `exists_homeomorph_image_interior_closure_frontier_eq_unitBall` / 定理 `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`

English:
theorem exists_homeomorph_image_interior_closure_frontier_eq_unitBall
  statement: {s : Set E}
  proof: by
  simpa [isOpen_ball.interior_eq, closure_ball, frontier_ball]
    using exists_homeomorph_image_eq hc hne (NormedSpace.isVonNBounded_of_isBounded _ hb)
    (convex_ball 0 1) (by simp [isOpen_ball.interior_eq]) (NormedSpace.isVonNBounded_ball _ _ _)

中文:
定理 存在_homeomorph_image_interior_closure_frontier_eq_unitBall
  结论: {s : 集合 E}
  证明: by
  simpa [isOpen_ball.interior_eq, closure_ball, frontier_ball]
    using exists_homeomorph_image_eq hc hne (NormedSpace.isVonNBounded_of_isBounded _ hb)
    (convex_ball 0 1) (by simp [isOpen_ball.interior_eq]) (NormedSpace.isVonNBounded_ball _ _ _)

Depends on / 依赖: NormedSpace, NormedSpace.isVonNBounded_ball, NormedSpace.isVonNBounded_of_isBounded, closure_ball, convex_ball, exists_homeomorph_image_eq, frontier_ball, interior_eq, isOpen_ball, isOpen_ball.interior_eq, isVonNBounded_ball, isVonNBounded_of_isBounded
-/
theorem exists_homeomorph_image_interior_closure_frontier_eq_unitBall {s : Set E}
    (hc : Convex Real s) (hne : (interior s).Nonempty) (hb : IsBounded s) :
    exists h : E ≃ₜ E, h '' interior s = ball 0 1 ∧ h '' closure s = closedBall 0 1 ∧
      h '' frontier s = sphere 0 1 := by
  simpa [isOpen_ball.interior_eq, closure_ball, frontier_ball]
    using exists_homeomorph_image_eq hc hne (NormedSpace.isVonNBounded_of_isBounded _ hb)
    (convex_ball 0 1) (by simp [isOpen_ball.interior_eq]) (NormedSpace.isVonNBounded_ball _ _ _)
