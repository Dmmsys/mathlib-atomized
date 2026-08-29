/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# L'Hôpital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hôpital's rule" for computing 0/0
indeterminate forms. The proof of `HasDerivAt.lhopital_zero_right_on_Ioo`
is based on the one given in the corresponding
[Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule)
chapter, and all other statements are derived from this one by composing by
carefully chosen functions.

Note that the filter `f'/g'` tends to isn't required to be one of `𝓝 a`,
`atTop` or `atBot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `ℝ`.

Each statement is available in a `HasDerivAt` form and a `deriv` form, which
is denoted by each statement being in either the `HasDerivAt` or the `deriv`
namespace.

## Tags

L'Hôpital's rule, L'Hopital's rule
-/

public section


open Filter Set

open scoped Filter Topology Pointwise

variable {a b : Real} {l : Filter Real} {f f' g g' : Real -> Real}

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' ≠ 0`) have
to be satisfied on an explicitly-provided interval.
-/


namespace HasDerivAt

/--
theorem `lhopital_zero_right_on_Ioo` / 定理 `lhopital_zero_right_on_Ioo`

English:
theorem lhopital_zero_right_on_Ioo
  statement: (hab : a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x)
  proof: by
  have sub : forall x in Ioo a b, Ioo a x subseteq Ioo a b := fun x hx =>
    Ioo_subset_Ioo (le_refl a) (le_of_lt hx.2)
  have hg : forall x in Ioo a b, g x != 0 := by
    intro x hx h
    have : Tendsto g (𝓝[<] x) (𝓝 0) := by
      rw [← h]; rw [← nhdsWithin_Ioo_eq_nhdsLT hx.1]
      exact ((hg

中文:
定理 lhopital_zero_right_on_Ioo
  结论: (hab : a < b) (hff' : 对任意 x in Ioo a b, HasDerivAt f (f' x) x)
  证明: by
  have sub : forall x in Ioo a b, Ioo a x subseteq Ioo a b := fun x hx =>
    Ioo_subset_Ioo (le_refl a) (le_of_lt hx.2)
  have hg : forall x in Ioo a b, g x != 0 := by
    intro x hx h
    have : Tendsto g (𝓝[<] x) (𝓝 0) := by
      rw [← h]; rw [← nhdsWithin_Ioo_eq_nhdsLT hx.1]
      exact ((hg

Depends on / 依赖: Ioo_subset_Ioo, Tendsto, continuousAt, continuousAt.continuousWithinAt.mono, continuousWithinAt, exists_hasDerivAt_eq_zero, le_of_lt, le_refl, nhdsWithin_Ioo_eq_nhdsLT, subseteq, tendsto
-/
theorem lhopital_zero_right_on_Ioo (hab : a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x) (hg' : forall x in Ioo a b, g' x != 0)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  have sub : forall x in Ioo a b, Ioo a x subseteq Ioo a b := fun x hx =>
    Ioo_subset_Ioo (le_refl a) (le_of_lt hx.2)
  have hg : forall x in Ioo a b, g x != 0 := by
    intro x hx h
    have : Tendsto g (𝓝[<] x) (𝓝 0) := by
      rw [← h]; rw [← nhdsWithin_Ioo_eq_nhdsLT hx.1]
      exact ((hgg' x hx).continuousAt.continuousWithinAt.mono <| sub x hx).tendsto
    obtain ⟨y, hyx, hy⟩ : exists c in Ioo a x, g' c = 0 :=
exists_hasDerivAt_eq_zero' hx.1 hga this fun y hy => hgg' y sub x hx hy
    exact hg' y (sub x hx hyx) hy
  have : forall x in Ioo a b, exists c in Ioo a x, f x * g' c = g x * f' c := by
    intro x hx
    rw [← sub_zero (f x)]; rw [← sub_zero (g x)]
    exact exists_ratio_hasDerivAt_eq_ratio_slope' g g' hx.1 f f' (fun y hy => hgg' y <| sub x hx hy)
      (fun y hy => hff' y <| sub x hx hy) hga hfa
      (tendsto_nhdsWithin_of_tendsto_nhds (hgg' x hx).continuousAt.tendsto)
      (tendsto_nhdsWithin_of_tendsto_nhds (hff' x hx).continuousAt.tendsto)
  choose! c hc using this
  have : forall x in Ioo a b, ((fun x' => f' x' / g' x') ∘ c) x = f x / g x := by grind
  have cmp : forall x in Ioo a b, a < c x ∧ c x < x := fun x hx => (hc x hx).1
  rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
  apply tendsto_nhdsWithin_congr this
  apply hdiv.comp
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ?_ ?_) ?_
  all_goals
    apply eventually_nhdsWithin_of_forall
    intro x hx
    have := cmp x hx
    simp
    linarith [this]

/--
theorem `lhopital_zero_right_on_Ico` / 定理 `lhopital_zero_right_on_Ico`

English:
theorem lhopital_zero_right_on_Ico
  statement: (hab : a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x)
  proof: by
  refine lhopital_zero_right_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ic

中文:
定理 lhopital_zero_right_on_Ico
  结论: (hab : a < b) (hff' : 对任意 x in Ioo a b, HasDerivAt f (f' x) x)
  证明: by
  refine lhopital_zero_right_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ic

Depends on / 依赖: Ioo_subset_Ico_self, left_mem_Ico, left_mem_Ico.mpr, lhopital_zero_right_on_Ioo, nhdsWithin_Ioo_eq_nhdsGT, tendsto
-/
theorem lhopital_zero_right_on_Ico (hab : a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ico a b))
    (hcg : ContinuousOn g (Ico a b)) (hg' : forall x in Ioo a b, g' x != 0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  refine lhopital_zero_right_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto

/--
theorem `lhopital_zero_left_on_Ioo` / 定理 `lhopital_zero_left_on_Ioo`

English:
theorem lhopital_zero_left_on_Ioo
  statement: (hab : a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x)
  proof: by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : forall x in -Ioo a b, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : forall x in -Ioo a b, HasDerivAt (g ∘ Neg.neg) (g' (-x

中文:
定理 lhopital_zero_left_on_Ioo
  结论: (hab : a < b) (hff' : 对任意 x in Ioo a b, HasDerivAt f (f' x) x)
  证明: by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : forall x in -Ioo a b, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : forall x in -Ioo a b, HasDerivAt (g ∘ Neg.neg) (g' (-x
-/
theorem lhopital_zero_left_on_Ioo (hab : a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x) (hg' : forall x in Ioo a b, g' x != 0)
    (hfb : Tendsto f (𝓝[<] b) (𝓝 0)) (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : forall x in -Ioo a b, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : forall x in -Ioo a b, HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (hasDerivAt_neg x)
  rw [neg_Ioo] at hdnf hdng
  have := lhopital_zero_right_on_Ioo (neg_lt_neg hab) hdnf hdng (by grind)
    (hfb.comp tendsto_neg_nhdsGT_neg) (hgb.comp tendsto_neg_nhdsGT_neg)
    (by
      simp only [neg_div_neg_eq, mul_one, mul_neg]
      exact hdiv.comp tendsto_neg_nhdsGT_neg)
  have := this.comp tendsto_neg_nhdsLT
  unfold Function.comp at this
  simpa only [neg_neg]

/--
theorem `lhopital_zero_left_on_Ioc` / 定理 `lhopital_zero_left_on_Ioc`

English:
theorem lhopital_zero_left_on_Ioc
  statement: (hab : a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x)
  proof: by
  refine lhopital_zero_left_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcf b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto
  · rw [← hgb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcg b <| right_mem_Ioc.mpr hab).mono Ioo_subset_I

中文:
定理 lhopital_zero_left_on_Ioc
  结论: (hab : a < b) (hff' : 对任意 x in Ioo a b, HasDerivAt f (f' x) x)
  证明: by
  refine lhopital_zero_left_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcf b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto
  · rw [← hgb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcg b <| right_mem_Ioc.mpr hab).mono Ioo_subset_I

Depends on / 依赖: Ioo_subset_Ioc_self, lhopital_zero_left_on_Ioo, nhdsWithin_Ioo_eq_nhdsLT, right_mem_Ioc, right_mem_Ioc.mpr, tendsto
-/
theorem lhopital_zero_left_on_Ioc (hab : a < b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ioc a b))
    (hcg : ContinuousOn g (Ioc a b)) (hg' : forall x in Ioo a b, g' x != 0) (hfb : f b = 0) (hgb : g b = 0)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  refine lhopital_zero_left_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcf b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto
  · rw [← hgb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcg b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto

/--
theorem `lhopital_zero_atTop_on_Ioi` / 定理 `lhopital_zero_atTop_on_Ioi`

English:
theorem lhopital_zero_atTop_on_Ioi
  statement: (hff' : forall x in Ioi a, HasDerivAt f (f' x) x)
  proof: by
  obtain ⟨a', haa', ha'⟩ : exists a', a < a' ∧ 0 < a' := ⟨1 + max a 0,
    ⟨lt_of_le_of_lt (le_max_left a 0) (lt_one_add _),
      lt_of_le_of_lt (le_max_right a 0) (lt_one_add _)⟩⟩
  have fact1 : forall x : Real, x in Ioo 0 a'⁻¹ -> x != 0 := fun _ hx => (ne_of_lt hx.1).symm
  have fact2 (x) (hx 

中文:
定理 lhopital_zero_atTop_on_Ioi
  结论: (hff' : 对任意 x in Ioi a, HasDerivAt f (f' x) x)
  证明: by
  obtain ⟨a', haa', ha'⟩ : exists a', a < a' ∧ 0 < a' := ⟨1 + max a 0,
    ⟨lt_of_le_of_lt (le_max_left a 0) (lt_one_add _),
      lt_of_le_of_lt (le_max_right a 0) (lt_one_add _)⟩⟩
  have fact1 : forall x : Real, x in Ioo 0 a'⁻¹ -> x != 0 := fun _ hx => (ne_of_lt hx.1).symm
  have fact2 (x) (hx 

Depends on / 依赖: HasDerivAt, Inv.inv, le_max_left, le_max_right, lt_of_le_of_lt, lt_one_add, lt_trans, ne_of_lt
-/
theorem lhopital_zero_atTop_on_Ioi (hff' : forall x in Ioi a, HasDerivAt f (f' x) x)
    (hgg' : forall x in Ioi a, HasDerivAt g (g' x) x) (hg' : forall x in Ioi a, g' x != 0)
    (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atTop l) : Tendsto (fun x => f x / g x) atTop l := by
  obtain ⟨a', haa', ha'⟩ : exists a', a < a' ∧ 0 < a' := ⟨1 + max a 0,
    ⟨lt_of_le_of_lt (le_max_left a 0) (lt_one_add _),
      lt_of_le_of_lt (le_max_right a 0) (lt_one_add _)⟩⟩
  have fact1 : forall x : Real, x in Ioo 0 a'⁻¹ -> x != 0 := fun _ hx => (ne_of_lt hx.1).symm
  have fact2 (x) (hx : x in Ioo 0 a'⁻¹) : a < x⁻¹ := lt_trans haa' ((lt_inv_comm₀ ha' hx.1).mpr hx.2)
  have hdnf : forall x in Ioo 0 a'⁻¹, HasDerivAt (f ∘ Inv.inv) (f' x⁻¹ * -(x ^ 2)⁻¹) x := fun x hx =>
    comp x (hff' x⁻¹ <| fact2 x hx) (hasDerivAt_inv <| fact1 x hx)
  have hdng : forall x in Ioo 0 a'⁻¹, HasDerivAt (g ∘ Inv.inv) (g' x⁻¹ * -(x ^ 2)⁻¹) x := fun x hx =>
    comp x (hgg' x⁻¹ <| fact2 x hx) (hasDerivAt_inv <| fact1 x hx)
  have := lhopital_zero_right_on_Ioo (inv_pos.mpr ha') hdnf hdng
    (by
      intro x hx
      refine mul_ne_zero ?_ (neg_ne_zero.mpr <| inv_ne_zero <| pow_ne_zero _ <| fact1 x hx)
      exact hg' _ (fact2 x hx))
    (hftop.comp tendsto_inv_nhdsGT_zero) (hgtop.comp tendsto_inv_nhdsGT_zero)
    (by
      refine (tendsto_congr' ?_).mp (hdiv.comp tendsto_inv_nhdsGT_zero)
      filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      simp only [Function.comp_def]
      rw [mul_div_mul_right]
      exact neg_ne_zero.mpr (by positivity))
  have := this.comp tendsto_inv_atTop_nhdsGT_zero
  unfold Function.comp at this
  simpa only [inv_inv]

/--
theorem `lhopital_zero_atBot_on_Iio` / 定理 `lhopital_zero_atBot_on_Iio`

English:
theorem lhopital_zero_atBot_on_Iio
  statement: (hff' : forall x in Iio a, HasDerivAt f (f' x) x)
  proof: by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : forall x in -Iio a, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : forall x in -Iio a, HasDerivAt (g ∘ Neg.neg) (g' (-x) * 

中文:
定理 lhopital_zero_atBot_on_Iio
  结论: (hff' : 对任意 x in Iio a, HasDerivAt f (f' x) x)
  证明: by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : forall x in -Iio a, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : forall x in -Iio a, HasDerivAt (g ∘ Neg.neg) (g' (-x) * 
-/
theorem lhopital_zero_atBot_on_Iio (hff' : forall x in Iio a, HasDerivAt f (f' x) x)
    (hgg' : forall x in Iio a, HasDerivAt g (g' x) x) (hg' : forall x in Iio a, g' x != 0)
    (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atBot l) : Tendsto (fun x => f x / g x) atBot l := by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : forall x in -Iio a, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : forall x in -Iio a, HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (hasDerivAt_neg x)
  rw [neg_Iio] at hdnf hdng
  have := lhopital_zero_atTop_on_Ioi hdnf hdng (by grind)
    (hfbot.comp tendsto_neg_atTop_atBot) (hgbot.comp tendsto_neg_atTop_atBot)
    (by simpa using! hdiv.comp tendsto_neg_atTop_atBot)
  have := this.comp tendsto_neg_atBot_atTop
  unfold Function.comp at this
  simpa only [neg_neg]

end HasDerivAt

namespace deriv

/--
theorem `lhopital_zero_right_on_Ioo` / 定理 `lhopital_zero_right_on_Ioo`

English:
theorem lhopital_zero_right_on_Ioo
  statement: (hab : a < b) (hdf : DifferentiableOn Real f (Ioo a b))
  proof: by
  have hdf : forall x in Ioo a b, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : forall x in Ioo a b, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasD

中文:
定理 lhopital_zero_right_on_Ioo
  结论: (hab : a < b) (hdf : DifferentiableOn 实数 f (Ioo a b))
  证明: by
  have hdf : forall x in Ioo a b, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : forall x in Ioo a b, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasD

Depends on / 依赖: DifferentiableAt, HasDerivAt, HasDerivAt.lhopital_zero_right_on_Ioo, Ioo_mem_nhds, by_contradiction, deriv_zero_of_not_differentiableAt, differentiableAt, hasDerivAt, lhopital_zero_right_on_Ioo
-/
theorem lhopital_zero_right_on_Ioo (hab : a < b) (hdf : DifferentiableOn Real f (Ioo a b))
    (hg' : forall x in Ioo a b, deriv g x != 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  have hdf : forall x in Ioo a b, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : forall x in Ioo a b, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_right_on_Ioo hab (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfa hga hdiv

/--
theorem `lhopital_zero_right_on_Ico` / 定理 `lhopital_zero_right_on_Ico`

English:
theorem lhopital_zero_right_on_Ico
  statement: (hab : a < b) (hdf : DifferentiableOn Real f (Ioo a b))
  proof: by
  refine lhopital_zero_right_on_Ioo hab hdf hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self

中文:
定理 lhopital_zero_right_on_Ico
  结论: (hab : a < b) (hdf : DifferentiableOn 实数 f (Ioo a b))
  证明: by
  refine lhopital_zero_right_on_Ioo hab hdf hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self

Depends on / 依赖: Ioo_subset_Ico_self, left_mem_Ico, left_mem_Ico.mpr, lhopital_zero_right_on_Ioo, nhdsWithin_Ioo_eq_nhdsGT, tendsto
-/
theorem lhopital_zero_right_on_Ico (hab : a < b) (hdf : DifferentiableOn Real f (Ioo a b))
    (hcf : ContinuousOn f (Ico a b)) (hcg : ContinuousOn g (Ico a b))
    (hg' : forall x in Ioo a b, (deriv g) x != 0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  refine lhopital_zero_right_on_Ioo hab hdf hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto

/--
theorem `lhopital_zero_left_on_Ioo` / 定理 `lhopital_zero_left_on_Ioo`

English:
theorem lhopital_zero_left_on_Ioo
  statement: (hab : a < b) (hdf : DifferentiableOn Real f (Ioo a b))
  proof: by
  have hdf : forall x in Ioo a b, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : forall x in Ioo a b, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasD

中文:
定理 lhopital_zero_left_on_Ioo
  结论: (hab : a < b) (hdf : DifferentiableOn 实数 f (Ioo a b))
  证明: by
  have hdf : forall x in Ioo a b, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : forall x in Ioo a b, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasD

Depends on / 依赖: DifferentiableAt, HasDerivAt, HasDerivAt.lhopital_zero_left_on_Ioo, Ioo_mem_nhds, by_contradiction, deriv_zero_of_not_differentiableAt, differentiableAt, hasDerivAt, lhopital_zero_left_on_Ioo
-/
theorem lhopital_zero_left_on_Ioo (hab : a < b) (hdf : DifferentiableOn Real f (Ioo a b))
    (hg' : forall x in Ioo a b, (deriv g) x != 0) (hfb : Tendsto f (𝓝[<] b) (𝓝 0))
    (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[<] b) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  have hdf : forall x in Ioo a b, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : forall x in Ioo a b, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_left_on_Ioo hab (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfb hgb hdiv

/--
theorem `lhopital_zero_atTop_on_Ioi` / 定理 `lhopital_zero_atTop_on_Ioi`

English:
theorem lhopital_zero_atTop_on_Ioi
  statement: (hdf : DifferentiableOn Real f (Ioi a))
  proof: by
  have hdf : forall x in Ioi a, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioi_mem_nhds hx)
  have hdg : forall x in Ioi a, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhop

中文:
定理 lhopital_zero_atTop_on_Ioi
  结论: (hdf : DifferentiableOn 实数 f (Ioi a))
  证明: by
  have hdf : forall x in Ioi a, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioi_mem_nhds hx)
  have hdg : forall x in Ioi a, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhop

Depends on / 依赖: DifferentiableAt, HasDerivAt, HasDerivAt.lhopital_zero_atTop_on_Ioi, Ioi_mem_nhds, by_contradiction, deriv_zero_of_not_differentiableAt, differentiableAt, hasDerivAt, lhopital_zero_atTop_on_Ioi
-/
theorem lhopital_zero_atTop_on_Ioi (hdf : DifferentiableOn Real f (Ioi a))
    (hg' : forall x in Ioi a, (deriv g) x != 0) (hftop : Tendsto f atTop (𝓝 0))
    (hgtop : Tendsto g atTop (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop l) :
    Tendsto (fun x => f x / g x) atTop l := by
  have hdf : forall x in Ioi a, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioi_mem_nhds hx)
  have hdg : forall x in Ioi a, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_atTop_on_Ioi (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hftop hgtop hdiv

/--
theorem `lhopital_zero_atBot_on_Iio` / 定理 `lhopital_zero_atBot_on_Iio`

English:
theorem lhopital_zero_atBot_on_Iio
  statement: (hdf : DifferentiableOn Real f (Iio a))
  proof: by
  have hdf : forall x in Iio a, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Iio_mem_nhds hx)
  have hdg : forall x in Iio a, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhop

中文:
定理 lhopital_zero_atBot_on_Iio
  结论: (hdf : DifferentiableOn 实数 f (Iio a))
  证明: by
  have hdf : forall x in Iio a, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Iio_mem_nhds hx)
  have hdg : forall x in Iio a, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhop

Depends on / 依赖: DifferentiableAt, HasDerivAt, HasDerivAt.lhopital_zero_atBot_on_Iio, Iio_mem_nhds, by_contradiction, deriv_zero_of_not_differentiableAt, differentiableAt, hasDerivAt, lhopital_zero_atBot_on_Iio
-/
theorem lhopital_zero_atBot_on_Iio (hdf : DifferentiableOn Real f (Iio a))
    (hg' : forall x in Iio a, (deriv g) x != 0) (hfbot : Tendsto f atBot (𝓝 0))
    (hgbot : Tendsto g atBot (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot l) :
    Tendsto (fun x => f x / g x) atBot l := by
  have hdf : forall x in Iio a, DifferentiableAt Real f x := fun x hx =>
    (hdf x hx).differentiableAt (Iio_mem_nhds hx)
  have hdg : forall x in Iio a, DifferentiableAt Real g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_atBot_on_Iio (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfbot hgbot hdiv

end deriv

/-!
## Generic versions

The following statements no longer any explicit interval, as they only require
conditions holding eventually.
-/


namespace HasDerivAt

/--
theorem `lhopital_zero_nhdsGT` / 定理 `lhopital_zero_nhdsGT`

English:
theorem lhopital_zero_nhdsGT
  statement: (hff' : forallᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x)
  proof: by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in 𝓝[>] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hs
  rcases hs with 

中文:
定理 lhopital_zero_nhdsGT
  结论: (hff' : 对任意ᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x)
  证明: by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in 𝓝[>] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hs
  rcases hs with 

Depends on / 依赖: eventually_iff_exists_mem, inter_mem, lhopital_zero_right_on_Ioo, mem_nhdsGT_iff_exists_Ioo_subset
-/
theorem lhopital_zero_nhdsGT (hff' : forallᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x)
    (hgg' : forallᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x) (hg' : forallᶠ x in 𝓝[>] a, g' x != 0)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in 𝓝[>] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hs
  rcases hs with ⟨u, hau, hu⟩
  refine lhopital_zero_right_on_Ioo hau ?_ ?_ ?_ hfa hga hdiv <;> grind

/--
theorem `lhopital_zero_nhdsLT` / 定理 `lhopital_zero_nhdsLT`

English:
theorem lhopital_zero_nhdsLT
  statement: (hff' : forallᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x)
  proof: by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in 𝓝[<] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsLT_iff_exists_Ioo_subset] at hs
  rcases hs with 

中文:
定理 lhopital_zero_nhdsLT
  结论: (hff' : 对任意ᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x)
  证明: by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in 𝓝[<] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsLT_iff_exists_Ioo_subset] at hs
  rcases hs with 

Depends on / 依赖: eventually_iff_exists_mem, inter_mem, lhopital_zero_left_on_Ioo, mem_nhdsLT_iff_exists_Ioo_subset
-/
theorem lhopital_zero_nhdsLT (hff' : forallᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x)
    (hgg' : forallᶠ x in 𝓝[<] a, HasDerivAt g (g' x) x) (hg' : forallᶠ x in 𝓝[<] a, g' x != 0)
    (hfa : Tendsto f (𝓝[<] a) (𝓝 0)) (hga : Tendsto g (𝓝[<] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] a) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in 𝓝[<] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsLT_iff_exists_Ioo_subset] at hs
  rcases hs with ⟨l, hal, hl⟩
  refine lhopital_zero_left_on_Ioo hal ?_ ?_ ?_ hfa hga hdiv <;> grind

/--
theorem `lhopital_zero_nhdsNE` / 定理 `lhopital_zero_nhdsNE`

English:
theorem lhopital_zero_nhdsNE
  statement: (hff' : forallᶠ x in 𝓝[!=] a, HasDerivAt f (f' x) x)
  proof: by
  simp only [← Iio_union_Ioi, nhdsWithin_union, tendsto_sup, eventually_sup] at *
  exact ⟨lhopital_zero_nhdsLT hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1,
    lhopital_zero_nhdsGT hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2⟩

中文:
定理 lhopital_zero_nhdsNE
  结论: (hff' : 对任意ᶠ x in 𝓝[!=] a, HasDerivAt f (f' x) x)
  证明: by
  simp only [← Iio_union_Ioi, nhdsWithin_union, tendsto_sup, eventually_sup] at *
  exact ⟨lhopital_zero_nhdsLT hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1,
    lhopital_zero_nhdsGT hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2⟩

Depends on / 依赖: Iio_union_Ioi, eventually_sup, lhopital_zero_nhdsGT, lhopital_zero_nhdsLT, nhdsWithin_union, tendsto_sup
-/
theorem lhopital_zero_nhdsNE (hff' : forallᶠ x in 𝓝[!=] a, HasDerivAt f (f' x) x)
    (hgg' : forallᶠ x in 𝓝[!=] a, HasDerivAt g (g' x) x) (hg' : forallᶠ x in 𝓝[!=] a, g' x != 0)
    (hfa : Tendsto f (𝓝[!=] a) (𝓝 0)) (hga : Tendsto g (𝓝[!=] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[!=] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[!=] a) l := by
  simp only [← Iio_union_Ioi, nhdsWithin_union, tendsto_sup, eventually_sup] at *
  exact ⟨lhopital_zero_nhdsLT hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1,
    lhopital_zero_nhdsGT hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2⟩

/--
theorem `_root_.HasDerivWithinAt.lhopital_zero_nhdsWithin_convex` / 定理 `_root_.HasDerivWithinAt.lhopital_zero_nhdsWithin_convex`

English:
theorem _root_.HasDerivWithinAt.lhopital_zero_nhdsWithin_convex
  statement: {s : Set Real} (hs : Convex Real s)
  proof: .of_neBot_imp fun has => by
  replace has := closure_mono sdiff_subset (mem_closure_iff_nhdsWithin_neBot.2 has)
  have h := hs.sdiff_singleton_eventually_mem_nhds a
replace hff' := h.mp hff'.mono fun _ h => h.hasDerivAt
replace hgg' := h.mp hgg'.mono fun _ h => h.hasDerivAt
  rcases eq_empty_or_none

中文:
定理 _root_.HasDerivWithinAt.lhopital_zero_nhdsWithin_convex
  结论: {s : Set 实数} (hs : Convex 实数 s)
  证明: .of_neBot_imp fun has => by
  replace has := closure_mono sdiff_subset (mem_closure_iff_nhdsWithin_neBot.2 has)
  have h := hs.sdiff_singleton_eventually_mem_nhds a
replace hff' := h.mp hff'.mono fun _ h => h.hasDerivAt
replace hgg' := h.mp hgg'.mono fun _ h => h.hasDerivAt
  rcases eq_empty_or_none

Depends on / 依赖: Iio_union_Ioi, closure_mono, eq_empty_or_nonempty, h.hasDerivAt, h.mp, hasDerivAt, hs.nhds, hs.sdiff_singleton_eventually_mem_nhds, hs_Iio, hs_Ioi, inter_union_distrib_left, mem_closure_iff_nhdsWithin_neBot, of_neBot_imp, replace, sdiff_eq, sdiff_singleton_eventually_mem_nhds, sdiff_subset, simp_rw
-/
theorem _root_.HasDerivWithinAt.lhopital_zero_nhdsWithin_convex {s : Set Real} (hs : Convex Real s)
    (hff' : forallᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (f' x) (s \ {a}) x)
    (hgg' : forallᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt g (g' x) (s \ {a}) x)
    (hg' : forallᶠ x in 𝓝[s \ {a}] a, g' x != 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[s \ {a}] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[s \ {a}] a) l := .of_neBot_imp fun has => by
  replace has := closure_mono sdiff_subset (mem_closure_iff_nhdsWithin_neBot.2 has)
  have h := hs.sdiff_singleton_eventually_mem_nhds a
replace hff' := h.mp hff'.mono fun _ h => h.hasDerivAt
replace hgg' := h.mp hgg'.mono fun _ h => h.hasDerivAt
  rcases eq_empty_or_nonempty (s inter Iio a) with hs_Iio | hs_Iio
    <;> rcases eq_empty_or_nonempty (s inter Ioi a) with hs_Ioi | hs_Ioi
  · simp [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left, hs_Iio, hs_Ioi]
  · simp_rw [hs.nhdsWithin_sdiff_eq_nhdsGT has hs_Iio hs_Ioi] at *
    exact lhopital_zero_nhdsGT hff' hgg' hg' hfa hga hdiv
  · simp_rw [hs.nhdsWithin_sdiff_eq_nhdsLT has hs_Iio hs_Ioi] at *
    exact lhopital_zero_nhdsLT hff' hgg' hg' hfa hga hdiv
  · simp_rw [hs.nhdsWithin_sdiff_eq_nhdsNE has hs_Iio hs_Ioi] at *
    exact lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv

/--
theorem `lhopital_zero_nhds` / 定理 `lhopital_zero_nhds`

English:
theorem lhopital_zero_nhds
  statement: (hff' : forallᶠ x in 𝓝 a, HasDerivAt f (f' x) x)
  proof: by
  apply @lhopital_zero_nhdsNE _ _ _ f' _ g' <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

中文:
定理 lhopital_zero_nhds
  结论: (hff' : 对任意ᶠ x in 𝓝 a, HasDerivAt f (f' x) x)
  证明: by
  apply @lhopital_zero_nhdsNE _ _ _ f' _ g' <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

Depends on / 依赖: eventually_nhdsWithin_of_eventually_nhds, lhopital_zero_nhdsNE, tendsto_nhdsWithin_of_tendsto_nhds
-/
theorem lhopital_zero_nhds (hff' : forallᶠ x in 𝓝 a, HasDerivAt f (f' x) x)
    (hgg' : forallᶠ x in 𝓝 a, HasDerivAt g (g' x) x) (hg' : forallᶠ x in 𝓝 a, g' x != 0)
    (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝 a) l) : Tendsto (fun x => f x / g x) (𝓝[!=] a) l := by
  apply @lhopital_zero_nhdsNE _ _ _ f' _ g' <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

/--
theorem `lhopital_zero_atTop` / 定理 `lhopital_zero_atTop`

English:
theorem lhopital_zero_atTop
  statement: (hff' : forallᶠ x in atTop, HasDerivAt f (f' x) x)
  proof: by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in atTop := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atTop_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' 

中文:
定理 lhopital_zero_atTop
  结论: (hff' : 对任意ᶠ x in atTop, HasDerivAt f (f' x) x)
  证明: by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in atTop := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atTop_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' 

Depends on / 依赖: eventually_iff_exists_mem, inter_mem, le_of_lt, lhopital_zero_atTop_on_Ioi, mem_atTop_sets, subseteq
-/
theorem lhopital_zero_atTop (hff' : forallᶠ x in atTop, HasDerivAt f (f' x) x)
    (hgg' : forallᶠ x in atTop, HasDerivAt g (g' x) x) (hg' : forallᶠ x in atTop, g' x != 0)
    (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atTop l) : Tendsto (fun x => f x / g x) atTop l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in atTop := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atTop_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' : Ioi l subseteq s := fun x hx => hl x (le_of_lt hx)
  refine lhopital_zero_atTop_on_Ioi ?_ ?_ (fun x hx => hg' x (hl' hx).2) hftop hgtop hdiv <;> grind

/--
theorem `lhopital_zero_atBot` / 定理 `lhopital_zero_atBot`

English:
theorem lhopital_zero_atBot
  statement: (hff' : forallᶠ x in atBot, HasDerivAt f (f' x) x)
  proof: by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in atBot := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atBot_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' 

中文:
定理 lhopital_zero_atBot
  结论: (hff' : 对任意ᶠ x in atBot, HasDerivAt f (f' x) x)
  证明: by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in atBot := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atBot_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' 

Depends on / 依赖: eventually_iff_exists_mem, inter_mem, le_of_lt, lhopital_zero_atBot_on_Iio, mem_atBot_sets, subseteq
-/
theorem lhopital_zero_atBot (hff' : forallᶠ x in atBot, HasDerivAt f (f' x) x)
    (hgg' : forallᶠ x in atBot, HasDerivAt g (g' x) x) (hg' : forallᶠ x in atBot, g' x != 0)
    (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atBot l) : Tendsto (fun x => f x / g x) atBot l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ inter s₂ inter s₃
  have hs : s in atBot := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atBot_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' : Iio l subseteq s := fun x hx => hl x (le_of_lt hx)
  refine lhopital_zero_atBot_on_Iio ?_ ?_ (fun x hx => hg' x (hl' hx).2) hfbot hgbot hdiv <;> grind

end HasDerivAt

namespace derivWithin

/--
theorem `lhopital_zero_nhdsWithin_convex` / 定理 `lhopital_zero_nhdsWithin_convex`

English:
theorem lhopital_zero_nhdsWithin_convex
  statement: {s : Set Real} (hs : Convex Real s)
  proof: by
  have hdg : forallᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt Real g (s \ {a}) x :=
    hg'.mp (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (derivWithin_zero_of_not_differentiableWithinAt h))
  have hdf' : forallᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (derivWithin f (s 

中文:
定理 lhopital_zero_nhdsWithin_convex
  结论: {s : Set 实数} (hs : Convex 实数 s)
  证明: by
  have hdg : forallᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt Real g (s \ {a}) x :=
    hg'.mp (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (derivWithin_zero_of_not_differentiableWithinAt h))
  have hdf' : forallᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (derivWithin f (s 

Depends on / 依赖: DifferentiableWithinAt, Eventually, Eventually.of_forall, HasDerivWithinAt, by_contradiction, derivWithin, derivWithin_zero_of_not_differentiableWithinAt, h.hasDerivWithinAt, hasDerivWithinAt, hdf.mp, hdg.mp, of_forall
-/
theorem lhopital_zero_nhdsWithin_convex {s : Set Real} (hs : Convex Real s)
    (hdf : forallᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt Real f (s \ {a}) x)
    (hg' : forallᶠ x in 𝓝[s \ {a}] a, derivWithin g (s \ {a}) x != 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x => derivWithin f (s \ {a}) x / derivWithin g (s \ {a}) x)
      (𝓝[s \ {a}] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[s \ {a}] a) l := by
  have hdg : forallᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt Real g (s \ {a}) x :=
    hg'.mp (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (derivWithin_zero_of_not_differentiableWithinAt h))
  have hdf' : forallᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (derivWithin f (s \ {a}) x) (s \ {a}) x :=
    hdf.mp (Eventually.of_forall fun _ h => h.hasDerivWithinAt)
  have hdg' : forallᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt g (derivWithin g (s \ {a}) x) (s \ {a}) x :=
    hdg.mp (Eventually.of_forall fun _ h => h.hasDerivWithinAt)
  exact HasDerivWithinAt.lhopital_zero_nhdsWithin_convex hs hdf' hdg' hg' hfa hga hdiv

end derivWithin

namespace deriv

/--
theorem `lhopital_zero_nhdsWithin_convex` / 定理 `lhopital_zero_nhdsWithin_convex`

English:
theorem lhopital_zero_nhdsWithin_convex
  statement: {s : Set Real} (hs : Convex Real s)
  proof: by
  refine derivWithin.lhopital_zero_nhdsWithin_convex hs
    (hdf.mono fun _ h => h.differentiableWithinAt) (hg'.mp ?_) hfa hga
    (hdiv.congr' ?_)
  all_goals
    apply (hs.sdiff_singleton_eventually_mem_nhds a).mono
    intros
  · rwa [derivWithin_of_mem_nhds ‹_›]
  · simp only
    iterate 2 rw

中文:
定理 lhopital_zero_nhdsWithin_convex
  结论: {s : Set 实数} (hs : Convex 实数 s)
  证明: by
  refine derivWithin.lhopital_zero_nhdsWithin_convex hs
    (hdf.mono fun _ h => h.differentiableWithinAt) (hg'.mp ?_) hfa hga
    (hdiv.congr' ?_)
  all_goals
    apply (hs.sdiff_singleton_eventually_mem_nhds a).mono
    intros
  · rwa [derivWithin_of_mem_nhds ‹_›]
  · simp only
    iterate 2 rw

Depends on / 依赖: all_goals, derivWithin, derivWithin.lhopital_zero_nhdsWithin_convex, derivWithin_of_mem_nhds, differentiableWithinAt, h.differentiableWithinAt, hdf.mono, hdiv.congr, hs.sdiff_singleton_eventually_mem_nhds, intros, iterate, lhopital_zero_nhdsWithin_convex, sdiff_singleton_eventually_mem_nhds
-/
theorem lhopital_zero_nhdsWithin_convex {s : Set Real} (hs : Convex Real s)
    (hdf : forallᶠ x in 𝓝[s \ {a}] a, DifferentiableAt Real f x) (hg' : forallᶠ x in 𝓝[s \ {a}] a, deriv g x != 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝[s \ {a}] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[s \ {a}] a) l := by
  refine derivWithin.lhopital_zero_nhdsWithin_convex hs
    (hdf.mono fun _ h => h.differentiableWithinAt) (hg'.mp ?_) hfa hga
    (hdiv.congr' ?_)
  all_goals
    apply (hs.sdiff_singleton_eventually_mem_nhds a).mono
    intros
  · rwa [derivWithin_of_mem_nhds ‹_›]
  · simp only
    iterate 2 rw [derivWithin_of_mem_nhds ‹_›]

/--
theorem `lhopital_zero_nhdsGT` / 定理 `lhopital_zero_nhdsGT`

English:
theorem lhopital_zero_nhdsGT
  statement: (hdf : forallᶠ x in 𝓝[>] a, DifferentiableAt Real f x)
  proof: by
  rw [← Ici_sdiff_left] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Ici a) hdf hg' hfa hga hdiv

中文:
定理 lhopital_zero_nhdsGT
  结论: (hdf : 对任意ᶠ x in 𝓝[>] a, DifferentiableAt 实数 f x)
  证明: by
  rw [← Ici_sdiff_left] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Ici a) hdf hg' hfa hga hdiv

Depends on / 依赖: Ici_sdiff_left, convex_Ici, lhopital_zero_nhdsWithin_convex
-/
theorem lhopital_zero_nhdsGT (hdf : forallᶠ x in 𝓝[>] a, DifferentiableAt Real f x)
    (hg' : forallᶠ x in 𝓝[>] a, deriv g x != 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[>] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  rw [← Ici_sdiff_left] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Ici a) hdf hg' hfa hga hdiv

/--
theorem `lhopital_zero_nhdsLT` / 定理 `lhopital_zero_nhdsLT`

English:
theorem lhopital_zero_nhdsLT
  statement: (hdf : forallᶠ x in 𝓝[<] a, DifferentiableAt Real f x)
  proof: by
  rw [← Iic_sdiff_right] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Iic a) hdf hg' hfa hga hdiv

中文:
定理 lhopital_zero_nhdsLT
  结论: (hdf : 对任意ᶠ x in 𝓝[<] a, DifferentiableAt 实数 f x)
  证明: by
  rw [← Iic_sdiff_right] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Iic a) hdf hg' hfa hga hdiv

Depends on / 依赖: Iic_sdiff_right, convex_Iic, lhopital_zero_nhdsWithin_convex
-/
theorem lhopital_zero_nhdsLT (hdf : forallᶠ x in 𝓝[<] a, DifferentiableAt Real f x)
    (hg' : forallᶠ x in 𝓝[<] a, deriv g x != 0) (hfa : Tendsto f (𝓝[<] a) (𝓝 0))
    (hga : Tendsto g (𝓝[<] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[<] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] a) l := by
  rw [← Iic_sdiff_right] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Iic a) hdf hg' hfa hga hdiv

/--
theorem `lhopital_zero_nhdsNE` / 定理 `lhopital_zero_nhdsNE`

English:
theorem lhopital_zero_nhdsNE
  statement: (hdf : forallᶠ x in 𝓝[!=] a, DifferentiableAt Real f x)
  proof: by
  rw [compl_eq_univ_sdiff] at *
  exact lhopital_zero_nhdsWithin_convex convex_univ hdf hg' hfa hga hdiv

中文:
定理 lhopital_zero_nhdsNE
  结论: (hdf : 对任意ᶠ x in 𝓝[!=] a, DifferentiableAt 实数 f x)
  证明: by
  rw [compl_eq_univ_sdiff] at *
  exact lhopital_zero_nhdsWithin_convex convex_univ hdf hg' hfa hga hdiv

Depends on / 依赖: compl_eq_univ_sdiff, convex_univ, lhopital_zero_nhdsWithin_convex
-/
theorem lhopital_zero_nhdsNE (hdf : forallᶠ x in 𝓝[!=] a, DifferentiableAt Real f x)
    (hg' : forallᶠ x in 𝓝[!=] a, deriv g x != 0) (hfa : Tendsto f (𝓝[!=] a) (𝓝 0))
    (hga : Tendsto g (𝓝[!=] a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[!=] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[!=] a) l := by
  rw [compl_eq_univ_sdiff] at *
  exact lhopital_zero_nhdsWithin_convex convex_univ hdf hg' hfa hga hdiv

/--
theorem `lhopital_zero_nhds` / 定理 `lhopital_zero_nhds`

English:
theorem lhopital_zero_nhds
  statement: (hdf : forallᶠ x in 𝓝 a, DifferentiableAt Real f x)
  proof: by
  apply lhopital_zero_nhdsNE <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

中文:
定理 lhopital_zero_nhds
  结论: (hdf : 对任意ᶠ x in 𝓝 a, DifferentiableAt 实数 f x)
  证明: by
  apply lhopital_zero_nhdsNE <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

Depends on / 依赖: eventually_nhdsWithin_of_eventually_nhds, lhopital_zero_nhdsNE, tendsto_nhdsWithin_of_tendsto_nhds
-/
theorem lhopital_zero_nhds (hdf : forallᶠ x in 𝓝 a, DifferentiableAt Real f x)
    (hg' : forallᶠ x in 𝓝 a, deriv g x != 0) (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝 a) l) :
    Tendsto (fun x => f x / g x) (𝓝[!=] a) l := by
  apply lhopital_zero_nhdsNE <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds) <;> assumption

/--
theorem `lhopital_zero_atTop` / 定理 `lhopital_zero_atTop`

English:
theorem lhopital_zero_atTop
  statement: (hdf : forallᶠ x : Real in atTop, DifferentiableAt Real f x)
  proof: by
  have hdg : forallᶠ x in atTop, DifferentiableAt Real g x := hg'.mp
    (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h))
  have hdf' : forallᶠ x in atTop, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt

中文:
定理 lhopital_zero_atTop
  结论: (hdf : 对任意ᶠ x : 实数 in atTop, DifferentiableAt 实数 f x)
  证明: by
  have hdg : forallᶠ x in atTop, DifferentiableAt Real g x := hg'.mp
    (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h))
  have hdf' : forallᶠ x in atTop, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt

Depends on / 依赖: DifferentiableAt, DifferentiableAt.hasDerivAt, Eventually, Eventually.of_forall, HasDerivAt, HasDerivAt.lhopital_zero_atTop, by_contradiction, deriv_zero_of_not_differentiableAt, hasDerivAt, hdf.mono, hdg.mono, lhopital_zero_atTop, of_forall
-/
theorem lhopital_zero_atTop (hdf : forallᶠ x : Real in atTop, DifferentiableAt Real f x)
    (hg' : forallᶠ x : Real in atTop, deriv g x != 0) (hftop : Tendsto f atTop (𝓝 0))
    (hgtop : Tendsto g atTop (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atTop l) :
    Tendsto (fun x => f x / g x) atTop l := by
  have hdg : forallᶠ x in atTop, DifferentiableAt Real g x := hg'.mp
    (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h))
  have hdf' : forallᶠ x in atTop, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt
  have hdg' : forallᶠ x in atTop, HasDerivAt g (deriv g x) x :=
    hdg.mono fun _ => DifferentiableAt.hasDerivAt
  exact HasDerivAt.lhopital_zero_atTop hdf' hdg' hg' hftop hgtop hdiv

/--
theorem `lhopital_zero_atBot` / 定理 `lhopital_zero_atBot`

English:
theorem lhopital_zero_atBot
  statement: (hdf : forallᶠ x : Real in atBot, DifferentiableAt Real f x)
  proof: by
  have hdg : forallᶠ x in atBot, DifferentiableAt Real g x :=
    hg'.mono fun _ hg' => by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h)
  have hdf' : forallᶠ x in atBot, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt
  have hdg' : forallᶠ x in

中文:
定理 lhopital_zero_atBot
  结论: (hdf : 对任意ᶠ x : 实数 in atBot, DifferentiableAt 实数 f x)
  证明: by
  have hdg : forallᶠ x in atBot, DifferentiableAt Real g x :=
    hg'.mono fun _ hg' => by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h)
  have hdf' : forallᶠ x in atBot, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt
  have hdg' : forallᶠ x in

Depends on / 依赖: DifferentiableAt, DifferentiableAt.hasDerivAt, HasDerivAt, HasDerivAt.lhopital_zero_atBot, by_contradiction, deriv_zero_of_not_differentiableAt, hasDerivAt, hdf.mono, hdg.mono, lhopital_zero_atBot
-/
theorem lhopital_zero_atBot (hdf : forallᶠ x : Real in atBot, DifferentiableAt Real f x)
    (hg' : forallᶠ x : Real in atBot, deriv g x != 0) (hfbot : Tendsto f atBot (𝓝 0))
    (hgbot : Tendsto g atBot (𝓝 0)) (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) atBot l) :
    Tendsto (fun x => f x / g x) atBot l := by
  have hdg : forallᶠ x in atBot, DifferentiableAt Real g x :=
    hg'.mono fun _ hg' => by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h)
  have hdf' : forallᶠ x in atBot, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt
  have hdg' : forallᶠ x in atBot, HasDerivAt g (deriv g x) x :=
    hdg.mono fun _ => DifferentiableAt.hasDerivAt
  exact HasDerivAt.lhopital_zero_atBot hdf' hdg' hg' hfbot hgbot hdiv

end deriv
