/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.RCLike.Basic
/-!
# Mean value theorem

In this file we prove Cauchy's and Lagrange's mean value theorems, and deduce some corollaries.

Cauchy's mean value theorem says that for two functions `f` and `g`
that are continuous on `[a, b]` and are differentiable on `(a, b)`,
there exists a point `c ∈ (a, b)` such that `f' c / g' c = (f b - f a) / (g b - g a)`.
We formulate this theorem with both sides multiplied by the denominators,
see `exists_ratio_hasDerivAt_eq_ratio_slope`,
in order to avoid auxiliary conditions like `g' c ≠ 0`.

Lagrange's mean value theorem, see `exists_hasDerivAt_eq_slope`,
says that for a function `f` that is continuous on `[a, b]` and is differentiable on `(a, b)`,
there exists a point `c ∈ (a, b)` such that `f' c = (f b - f a) / (b - a)`.

Lagrange's MVT implies that `(f b - f a) / (b - a) > C`
provided that `f' c > C` for all `c ∈ (a, b)`, see `mul_sub_lt_image_sub_of_lt_deriv`,
and other theorems for `>` / `≥` / `<` / `≤`.

In case `C = 0`, we deduce that a function with a positive derivative is strictly monotone,
see `strictMonoOn_of_deriv_pos` and nearby theorems for other types of monotonicity.

We also prove that a real function whose derivative tends to infinity from the right at a point
is not differentiable on the right at that point, and similarly differentiability on the left.

## Main results


* `exists_ratio_hasDerivAt_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_hasDerivAt_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `domain_mvt` : Lagrange's Mean Value Theorem, applied to a segment in a convex domain.

* `Convex.image_sub_lt_mul_sub_of_deriv_lt`, `Convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `Convex.image_sub_le_mul_sub_of_deriv_le`, `Convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`,
  `strictMono_of_deriv_pos`, `strictAnti_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/antitone/strictly monotone/strictly monotonically
  decreasing.

* `convexOn_of_deriv`, `convexOn_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

-/

public section

open Set Function Filter
open scoped Topology

/-! ### Functions `[a, b] → ℝ`. -/

section Interval

-- Declare all variables here to make sure they come in a correct order
variable (f f' : Real -> Real) {a b : Real} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
  (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (hfd : DifferentiableOn Real f (Ioo a b))
  (g g' : Real -> Real) (hgc : ContinuousOn g (Icc a b)) (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x)
  (hgd : DifferentiableOn Real g (Ioo a b))

include hab hfc hff' hgc hgg' in
/--
theorem `exists_ratio_hasDerivAt_eq_ratio_slope` / 定理 `exists_ratio_hasDerivAt_eq_ratio_slope`

English:
theorem exists_ratio_hasDerivAt_eq_ratio_slope
  proof: by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by simp only [h]; ring
  let h' x := (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : forall x in Ioo a b, HasDerivAt h (h' x) x := fun x hx =>
    ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b 

中文:
定理 存在_ratio_hasDerivAt_eq_ratio_slope
  证明: by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by simp only [h]; ring
  let h' x := (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : forall x in Ioo a b, HasDerivAt h (h' x) x := fun x hx =>
    ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b 

Depends on / 依赖: ContinuousOn, HasDerivAt, const_mul, continuousOn_const, continuousOn_const.mul, exists_hasDerivAt_eq_zero, sub_eq_zero
-/
theorem exists_ratio_hasDerivAt_eq_ratio_slope :
    exists c in Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by simp only [h]; ring
  let h' x := (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : forall x in Ioo a b, HasDerivAt h (h' x) x := fun x hx =>
    ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b - f a))
  have hhc : ContinuousOn h (Icc a b) :=
    (continuousOn_const.mul hfc).sub (continuousOn_const.mul hgc)
  rcases exists_hasDerivAt_eq_zero hab hhc hI hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩

include hab in
/--
theorem `exists_ratio_hasDerivAt_eq_ratio_slope'` / 定理 `exists_ratio_hasDerivAt_eq_ratio_slope'`

English:
theorem exists_ratio_hasDerivAt_eq_ratio_slope'
  statement: {lfa lga lfb lgb : Real}
  proof: by
  let h x := (lgb - lga) * f x - (lfb - lfa) * g x
  have hha : Tendsto h (𝓝[>] a) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[>] a) (𝓝 <| (lgb - lga) * lfa - (lfb - lfa) * lga) :=
      (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga)
    convert! this using 2
    rin

中文:
定理 存在_ratio_hasDerivAt_eq_ratio_slope'
  结论: {lfa lga lfb lgb : 实数}
  证明: by
  let h x := (lgb - lga) * f x - (lfb - lfa) * g x
  have hha : Tendsto h (𝓝[>] a) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[>] a) (𝓝 <| (lgb - lga) * lfa - (lfb - lfa) * lga) :=
      (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga)
    convert! this using 2
    rin

Depends on / 依赖: Tendsto, convert, tendsto_const_nhds, tendsto_const_nhds.mul
-/
theorem exists_ratio_hasDerivAt_eq_ratio_slope' {lfa lga lfb lgb : Real}
    (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) (hgg' : forall x in Ioo a b, HasDerivAt g (g' x) x)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    exists c in Ioo a b, (lgb - lga) * f' c = (lfb - lfa) * g' c := by
  let h x := (lgb - lga) * f x - (lfb - lfa) * g x
  have hha : Tendsto h (𝓝[>] a) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[>] a) (𝓝 <| (lgb - lga) * lfa - (lfb - lfa) * lga) :=
      (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga)
    convert! this using 2
    ring
  have hhb : Tendsto h (𝓝[<] b) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[<] b) (𝓝 <| (lgb - lga) * lfb - (lfb - lfa) * lgb) :=
      (tendsto_const_nhds.mul hfb).sub (tendsto_const_nhds.mul hgb)
    convert! this using 2
    ring
  let h' x := (lgb - lga) * f' x - (lfb - lfa) * g' x
  have hhh' : forall x in Ioo a b, HasDerivAt h (h' x) x := by
    intro x hx
    exact ((hff' x hx).const_mul _).sub ((hgg' x hx).const_mul _)
  rcases exists_hasDerivAt_eq_zero' hab hha hhb hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩

include hab hfc hff' in
/--
theorem `exists_hasDerivAt_eq_slope` / 定理 `exists_hasDerivAt_eq_slope`

English:
theorem exists_hasDerivAt_eq_slope
  statement: exists c in Ioo a b, f' c = (f b - f a) / (b - a)
  proof: by
  obtain ⟨c, cmem, hc⟩ : exists c in Ioo a b, (b - a) * f' c = (f b - f a) * 1 :=
    exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' id 1 continuousOn_id
      fun x _ => hasDerivAt_id x
  use c, cmem
  rwa [mul_one, mul_comm, ← eq_div_iff (sub_ne_zero.2 hab.ne')] at hc

include hab hfc

中文:
定理 存在_hasDerivAt_eq_slope
  结论: 存在 c in 开区间 a b, f' c = (f b - f a) / (b - a)
  证明: by
  obtain ⟨c, cmem, hc⟩ : exists c in Ioo a b, (b - a) * f' c = (f b - f a) * 1 :=
    exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' id 1 continuousOn_id
      fun x _ => hasDerivAt_id x
  use c, cmem
  rwa [mul_one, mul_comm, ← eq_div_iff (sub_ne_zero.2 hab.ne')] at hc

include hab hfc

Depends on / 依赖: continuousOn_id, eq_div_iff, exists_ratio_hasDerivAt_eq_ratio_slope, hab.ne, hasDerivAt_id, mul_comm, mul_one, sub_ne_zero
-/
theorem exists_hasDerivAt_eq_slope : exists c in Ioo a b, f' c = (f b - f a) / (b - a) := by
  obtain ⟨c, cmem, hc⟩ : exists c in Ioo a b, (b - a) * f' c = (f b - f a) * 1 :=
    exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' id 1 continuousOn_id
      fun x _ => hasDerivAt_id x
  use c, cmem
  rwa [mul_one, mul_comm, ← eq_div_iff (sub_ne_zero.2 hab.ne')] at hc

include hab hfc hgc hgd hfd in
/-- Cauchy's Mean Value Theorem, `deriv` version. -/
@[wikidata Q189136]
/--
theorem `exists_ratio_deriv_eq_ratio_slope` / 定理 `exists_ratio_deriv_eq_ratio_slope`

English:
theorem exists_ratio_deriv_eq_ratio_slope
  proof: exists_ratio_hasDerivAt_eq_ratio_slope f (deriv f) hab hfc
    (fun x hx => ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt) g
    (deriv g) hgc fun x hx =>
    ((hgd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab in

中文:
定理 存在_ratio_deriv_eq_ratio_slope
  证明: exists_ratio_hasDerivAt_eq_ratio_slope f (deriv f) hab hfc
    (fun x hx => ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt) g
    (deriv g) hgc fun x hx =>
    ((hgd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab in

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, differentiableAt, exists_ratio_hasDerivAt_eq_ratio_slope, hasDerivAt, isOpen_Ioo, mem_nhds
-/
theorem exists_ratio_deriv_eq_ratio_slope :
    exists c in Ioo a b, (g b - g a) * deriv f c = (f b - f a) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope f (deriv f) hab hfc
    (fun x hx => ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt) g
    (deriv g) hgc fun x hx =>
    ((hgd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab in
/--
theorem `exists_ratio_deriv_eq_ratio_slope'` / 定理 `exists_ratio_deriv_eq_ratio_slope'`

English:
theorem exists_ratio_deriv_eq_ratio_slope'
  statement: {lfa lga lfb lgb : Real}
  proof: exists_ratio_hasDerivAt_eq_ratio_slope' _ _ hab _ _
    (fun x hx => ((hdf x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt)
    (fun x hx => ((hdg x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt) hfa hga hfb hgb

include hab hfc hfd in

中文:
定理 存在_ratio_deriv_eq_ratio_slope'
  结论: {lfa lga lfb lgb : 实数}
  证明: exists_ratio_hasDerivAt_eq_ratio_slope' _ _ hab _ _
    (fun x hx => ((hdf x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt)
    (fun x hx => ((hdg x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt) hfa hga hfb hgb

include hab hfc hfd in

Depends on / 依赖: Ioo_mem_nhds, differentiableAt, exists_ratio_hasDerivAt_eq_ratio_slope, hasDerivAt
-/
theorem exists_ratio_deriv_eq_ratio_slope' {lfa lga lfb lgb : Real}
    (hdf : DifferentiableOn Real f <| Ioo a b) (hdg : DifferentiableOn Real g <| Ioo a b)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    exists c in Ioo a b, (lgb - lga) * deriv f c = (lfb - lfa) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope' _ _ hab _ _
    (fun x hx => ((hdf x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt)
    (fun x hx => ((hdg x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt) hfa hga hfb hgb

include hab hfc hfd in
/--
theorem `exists_deriv_eq_slope` / 定理 `exists_deriv_eq_slope`

English:
theorem exists_deriv_eq_slope
  statement: exists c in Ioo a b, deriv f c = (f b - f a) / (b - a)
  proof: exists_hasDerivAt_eq_slope f (deriv f) hab hfc fun x hx =>
    ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab hfc hfd in

中文:
定理 存在_deriv_eq_slope
  结论: 存在 c in 开区间 a b, deriv f c = (f b - f a) / (b - a)
  证明: exists_hasDerivAt_eq_slope f (deriv f) hab hfc fun x hx =>
    ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab hfc hfd in

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, differentiableAt, exists_hasDerivAt_eq_slope, hasDerivAt, isOpen_Ioo, mem_nhds
-/
theorem exists_deriv_eq_slope : exists c in Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f (deriv f) hab hfc fun x hx =>
    ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab hfc hfd in
/--
theorem `exists_deriv_eq_slope'` / 定理 `exists_deriv_eq_slope'`

English:
theorem exists_deriv_eq_slope'
  statement: exists c in Ioo a b, deriv f c = slope f a b
  proof: by
  rw [slope_def_field]
  exact exists_deriv_eq_slope f hab hfc hfd

中文:
定理 存在_deriv_eq_slope'
  结论: 存在 c in 开区间 a b, deriv f c = slope f a b
  证明: by
  rw [slope_def_field]
  exact exists_deriv_eq_slope f hab hfc hfd

Depends on / 依赖: exists_deriv_eq_slope, slope_def_field
-/
theorem exists_deriv_eq_slope' : exists c in Ioo a b, deriv f c = slope f a b := by
  rw [slope_def_field]
  exact exists_deriv_eq_slope f hab hfc hfd

/--
theorem `not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi` / 定理 `not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi`

English:
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi
  statement: (f : Real -> Real) {a : Real}
  proof: by
  replace hf : Tendsto (derivWithin f (Ioi a)) (𝓝[>] a) atTop := by
    refine hf.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have : Ioi a in 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx]
    exact (derivWithin_of_mem_nhds this).symm
  by_cases hcont_at_a : Continuou

中文:
定理 not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi
  结论: (f : 实数 -> 实数) {a : 实数}
  证明: by
  replace hf : Tendsto (derivWithin f (Ioi a)) (𝓝[>] a) atTop := by
    refine hf.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have : Ioi a in 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx]
    exact (derivWithin_of_mem_nhds this).symm
  by_cases hcont_at_a : Continuou

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.sdiff_iff, Tendsto, continuousWithinAt, derivWithin, derivWithin_of_mem_nhds, eventually_mem_nhdsWithin, filter_upwards, hasDerivWithinAt, hcont_at_a, hcontra, hcontra.continuousWithinAt, hdiff.hasDerivWithinAt, hf.congr, mem_interior_iff_mem_nhds, replace, sdiff_iff
-/
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (f : Real -> Real) {a : Real}
    (hf : Tendsto (deriv f) (𝓝[>] a) atTop) : ¬ DifferentiableWithinAt Real f (Ioi a) a := by
  replace hf : Tendsto (derivWithin f (Ioi a)) (𝓝[>] a) atTop := by
    refine hf.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have : Ioi a in 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx]
    exact (derivWithin_of_mem_nhds this).symm
  by_cases hcont_at_a : ContinuousWithinAt f (Ici a) a
  case neg =>
    intro hcontra
    have := hcontra.continuousWithinAt
    rw [← ContinuousWithinAt.sdiff_iff this] at hcont_at_a
    simp at hcont_at_a
  case pos =>
    intro hdiff
    replace hdiff := hdiff.hasDerivWithinAt
    rw [hasDerivWithinAt_iff_tendsto_slope]; rw [Set.sdiff_singleton_eq_self self_notMem_Ioi] at hdiff
    have h₀ : forallᶠ b in 𝓝[>] a,
        forall x in Ioc a b, max (derivWithin f (Ioi a) a + 1) 0 < derivWithin f (Ioi a) x := by
      rw [(nhdsGT_basis a).eventually_iff]
      rw [(nhdsGT_basis a).tendsto_left_iff] at hf
      obtain ⟨b, hab, hb⟩ := hf (Ioi (max (derivWithin f (Ioi a) a + 1) 0)) (Ioi_mem_atTop _)
      refine ⟨b, hab, fun x hx z hz => ?_⟩
      simp only [MapsTo, mem_Ioo, mem_Ioi, and_imp] at hb
exact hb hz.1 hz.2.trans_lt hx.2
    have h₁ : forallᶠ b in 𝓝[>] a, slope f a b < derivWithin f (Ioi a) a + 1 := by
      rw [(nhds_basis_Ioo _).tendsto_right_iff] at hdiff
specialize hdiff ⟨derivWithin f (Ioi a) a - 1, derivWithin f (Ioi a) a + 1⟩ by simp
      filter_upwards [hdiff] with z hz using hz.2
    have hcontra : forallᶠ _ in 𝓝[>] a, False := by
      filter_upwards [h₀, h₁, eventually_mem_nhdsWithin] with b hb hslope (hab : a < b)
      have hdiff' : DifferentiableOn Real f (Ioc a b) := fun z hz => by
        refine DifferentiableWithinAt.mono (t := Ioi a) ?_ Ioc_subset_Ioi_self
have : derivWithin f (Ioi a) z != 0 := ne_of_gt by
          simp_all only [and_imp, mem_Ioc, max_lt_iff]
        exact differentiableWithinAt_of_derivWithin_ne_zero this
      have hcont_Ioc : forall z in Ioc a b, ContinuousWithinAt f (Icc a b) z := by
        intro z hz''
        refine (hdiff'.continuousOn z hz'').mono_of_mem_nhdsWithin ?_
        have hfinal : 𝓝[Ioc a b] z = 𝓝[Icc a b] z := by
          refine nhdsWithin_eq_nhdsWithin' (s := Ioi a) (Ioi_mem_nhds hz''.1) ?_
          simp only [Ioc_inter_Ioi, le_refl, sup_of_le_left]
          ext y
          exact ⟨fun h => ⟨mem_Icc_of_Ioc h, mem_of_mem_inter_left h⟩, fun ⟨H1, H2⟩ => ⟨H2, H1.2⟩⟩
        rw [← hfinal]
        exact self_mem_nhdsWithin
      have hcont : ContinuousOn f (Icc a b) := by
        intro z hz
        by_cases hz' : z = a
        · rw [hz']
          exact hcont_at_a.mono Icc_subset_Ici_self
        · exact hcont_Ioc z ⟨lt_of_le_of_ne hz.1 (Ne.symm hz'), hz.2⟩
      obtain ⟨x, hx₁, hx₂⟩ :=
        exists_deriv_eq_slope' f hab hcont (hdiff'.mono (Ioo_subset_Ioc_self))
      specialize hb x ⟨hx₁.1, le_of_lt hx₁.2⟩
      replace hx₂ : derivWithin f (Ioi a) x = slope f a b := by
        have : Ioi a in 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx₁.1]
        rwa [derivWithin_of_mem_nhds this]
      rw [hx₂]; rw [max_lt_iff] at hb
      linarith
    simp [Filter.eventually_false_iff_eq_bot, ← notMem_closure_iff_nhdsWithin_eq_bot] at hcontra

/--
theorem `not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi` / 定理 `not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi`

English:
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi
  statement: (f : Real -> Real) {a : Real}
  proof: by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[>] a) atTop := by
    rw [deriv.neg']
    exact tendsto_neg_atBot_atTop.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (-f) hf' h.neg

中文:
定理 not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi
  结论: (f : 实数 -> 实数) {a : 实数}
  证明: by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[>] a) atTop := by
    rw [deriv.neg']
    exact tendsto_neg_atBot_atTop.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (-f) hf' h.neg

Depends on / 依赖: Tendsto, deriv.neg, h.neg, not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi, tendsto_neg_atBot_atTop, tendsto_neg_atBot_atTop.comp
-/
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi (f : Real -> Real) {a : Real}
    (hf : Tendsto (deriv f) (𝓝[>] a) atBot) : ¬ DifferentiableWithinAt Real f (Ioi a) a := by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[>] a) atTop := by
    rw [deriv.neg']
    exact tendsto_neg_atBot_atTop.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (-f) hf' h.neg

/--
theorem `not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio` / 定理 `not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio`

English:
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio
  statement: (f : Real -> Real) {a : Real}
  proof: by
  let f' := f ∘ Neg.neg
  have hderiv : deriv f' =ᶠ[𝓝[>] (-a)] -(deriv f ∘ Neg.neg) := by
    rw [atBot_basis.tendsto_right_iff] at hf
    specialize hf (-1) trivial
    rw [(nhdsLT_basis a).eventually_iff] at hf
    rw [EventuallyEq]; rw [(nhdsGT_basis (-a)).eventually_iff]
    obtain ⟨b, hb₁, h

中文:
定理 not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio
  结论: (f : 实数 -> 实数) {a : 实数}
  证明: by
  let f' := f ∘ Neg.neg
  have hderiv : deriv f' =ᶠ[𝓝[>] (-a)] -(deriv f ∘ Neg.neg) := by
    rw [atBot_basis.tendsto_right_iff] at hf
    specialize hf (-1) trivial
    rw [(nhdsLT_basis a).eventually_iff] at hf
    rw [EventuallyEq]; rw [(nhdsGT_basis (-a)).eventually_iff]
    obtain ⟨b, hb₁, h

Depends on / 依赖: EventuallyEq, Function, Function.comp_apply, Neg.neg, Pi.neg_apply, atBot_basis, atBot_basis.tendsto_right_iff, comp_apply, deriv_comp, differentiableAt, eventually_iff, hderiv, neg_apply, nhdsGT_basis, nhdsLT_basis, specialize, tendsto_right_iff
-/
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (f : Real -> Real) {a : Real}
    (hf : Tendsto (deriv f) (𝓝[<] a) atBot) : ¬ DifferentiableWithinAt Real f (Iio a) a := by
  let f' := f ∘ Neg.neg
  have hderiv : deriv f' =ᶠ[𝓝[>] (-a)] -(deriv f ∘ Neg.neg) := by
    rw [atBot_basis.tendsto_right_iff] at hf
    specialize hf (-1) trivial
    rw [(nhdsLT_basis a).eventually_iff] at hf
    rw [EventuallyEq]; rw [(nhdsGT_basis (-a)).eventually_iff]
    obtain ⟨b, hb₁, hb₂⟩ := hf
    refine ⟨-b, by linarith, fun x hx => ?_⟩
    simp only [Pi.neg_apply, Function.comp_apply]
    suffices deriv f' x = deriv f (-x) * deriv (Neg.neg : Real -> Real) x by simpa using this
    refine deriv_comp x (differentiableAt_of_deriv_ne_zero ?_) (by fun_prop)
    rw [mem_Ioo] at hx
    have h₁ : -x in Ioo b a := ⟨by linarith, by linarith⟩
    have h₂ : deriv f (-x) <= -1 := hb₂ h₁
    exact ne_of_lt (by linarith)
  have hmain : ¬ DifferentiableWithinAt Real f' (Ioi (-a)) (-a) := by
refine not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi f' Tendsto.congr' hderiv.symm ?_
    refine Tendsto.comp (g := -deriv f) ?_ tendsto_neg_nhdsGT_neg
    exact Tendsto.comp (g := Neg.neg) tendsto_neg_atBot_atTop hf
  intro h
  have : DifferentiableWithinAt Real f' (Ioi (-a)) (-a) := by
    refine DifferentiableWithinAt.comp (g := f) (f := Neg.neg) (t := Iio a) (-a) ?_ ?_ ?_
    · simp [h]
    · fun_prop
    · intro x
      simp [neg_lt]
  exact hmain this

/--
theorem `not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio` / 定理 `not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio`

English:
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio
  statement: (f : Real -> Real) {a : Real}
  proof: by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[<] a) atBot := by
    rw [deriv.neg']
    exact tendsto_neg_atTop_atBot.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (-f) hf' h.neg

中文:
定理 not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio
  结论: (f : 实数 -> 实数) {a : 实数}
  证明: by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[<] a) atBot := by
    rw [deriv.neg']
    exact tendsto_neg_atTop_atBot.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (-f) hf' h.neg

Depends on / 依赖: Tendsto, deriv.neg, h.neg, not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.comp
-/
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio (f : Real -> Real) {a : Real}
    (hf : Tendsto (deriv f) (𝓝[<] a) atTop) : ¬ DifferentiableWithinAt Real f (Iio a) a := by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[<] a) atBot := by
    rw [deriv.neg']
    exact tendsto_neg_atTop_atBot.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (-f) hf' h.neg

end Interval

/--
theorem `Convex.mul_sub_lt_image_sub_of_lt_deriv` / 定理 `Convex.mul_sub_lt_image_sub_of_lt_deriv`

English:
theorem Convex.mul_sub_lt_image_sub_of_lt_deriv
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: by
  intro x hx y hy hxy
  have hxyD : Icc x y subseteq D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y subseteq interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_de

中文:
定理 凸.mul_sub_lt_image_sub_of_lt_deriv
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: by
  intro x hx y hy hxy
  have hxyD : Icc x y subseteq D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y subseteq interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_de

Depends on / 依赖: Ioo_subset_Icc_self, Ioo_subset_Icc_self.trans, a_mem, exists_deriv_eq_slope, hD.ordConnected.out, hf.mono, interior, isOpen_Ioo, ordConnected, sub_pos, subset_sUnion_of_mem, subseteq
-/
theorem Convex.mul_sub_lt_image_sub_of_lt_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) {C}
    (hf'_gt : forall x in interior D, C < deriv f x) :
    forallᵉ (x in D) (y in D), x < y -> C * (y - x) < f y - f x := by
  intro x hx y hy hxy
  have hxyD : Icc x y subseteq D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y subseteq interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
  have : C < (f y - f x) / (y - x) := ha ▸ hf'_gt _ (hxyD' a_mem)
  exact (lt_div_iff₀ (sub_pos.2 hxy)).1 this

/--
theorem `mul_sub_lt_image_sub_of_lt_deriv` / 定理 `mul_sub_lt_image_sub_of_lt_deriv`

English:
theorem mul_sub_lt_image_sub_of_lt_deriv
  statement: {f : Real -> Real} (hf : Differentiable Real f) {C}
  proof: convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_gt x) x trivial y trivial hxy

中文:
定理 mul_sub_lt_image_sub_of_lt_deriv
  结论: {f : 实数 -> 实数} (hf : 可微 实数 f) {C}
  证明: convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_gt x) x trivial y trivial hxy

Depends on / 依赖: continuous, continuousOn, convex_univ, convex_univ.mul_sub_lt_image_sub_of_lt_deriv, differentiableOn, hf.continuous.continuousOn, hf.differentiableOn, mul_sub_lt_image_sub_of_lt_deriv
-/
theorem mul_sub_lt_image_sub_of_lt_deriv {f : Real -> Real} (hf : Differentiable Real f) {C}
    (hf'_gt : forall x, C < deriv f x) ⦃x y⦄ (hxy : x < y) : C * (y - x) < f y - f x :=
  convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_gt x) x trivial y trivial hxy

/--
theorem `Convex.mul_sub_le_image_sub_of_le_deriv` / 定理 `Convex.mul_sub_le_image_sub_of_le_deriv`

English:
theorem Convex.mul_sub_le_image_sub_of_le_deriv
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with hxy' | hxy'
  · rw [hxy', sub_self, sub_self, mul_zero]
  have hxyD : Icc x y subseteq D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y subseteq interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain

中文:
定理 凸.mul_sub_le_image_sub_of_le_deriv
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with hxy' | hxy'
  · rw [hxy', sub_self, sub_self, mul_zero]
  have hxyD : Icc x y subseteq D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y subseteq interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain

Depends on / 依赖: Ioo_subset_Icc_self, Ioo_subset_Icc_self.trans, a_mem, eq_or_lt_of_le, exists_deriv_eq_slope, hD.ordConnected.out, hf.mono, interior, isOpen_Ioo, le_div_, mul_zero, ordConnected, sub_self, subset_sUnion_of_mem, subseteq
-/
theorem Convex.mul_sub_le_image_sub_of_le_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) {C}
    (hf'_ge : forall x in interior D, C <= deriv f x) :
    forallᵉ (x in D) (y in D), x <= y -> C * (y - x) <= f y - f x := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with hxy' | hxy'
  · rw [hxy', sub_self, sub_self, mul_zero]
  have hxyD : Icc x y subseteq D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y subseteq interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD')
  have : C <= (f y - f x) / (y - x) := ha ▸ hf'_ge _ (hxyD' a_mem)
  exact (le_div_iff₀ (sub_pos.2 hxy')).1 this

/--
theorem `mul_sub_le_image_sub_of_le_deriv` / 定理 `mul_sub_le_image_sub_of_le_deriv`

English:
theorem mul_sub_le_image_sub_of_le_deriv
  statement: {f : Real -> Real} (hf : Differentiable Real f) {C}
  proof: convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_ge x) x trivial y trivial hxy

中文:
定理 mul_sub_le_image_sub_of_le_deriv
  结论: {f : 实数 -> 实数} (hf : 可微 实数 f) {C}
  证明: convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_ge x) x trivial y trivial hxy

Depends on / 依赖: continuous, continuousOn, convex_univ, convex_univ.mul_sub_le_image_sub_of_le_deriv, differentiableOn, hf.continuous.continuousOn, hf.differentiableOn, mul_sub_le_image_sub_of_le_deriv
-/
theorem mul_sub_le_image_sub_of_le_deriv {f : Real -> Real} (hf : Differentiable Real f) {C}
    (hf'_ge : forall x, C <= deriv f x) ⦃x y⦄ (hxy : x <= y) : C * (y - x) <= f y - f x :=
  convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_ge x) x trivial y trivial hxy

/--
theorem `Convex.image_sub_lt_mul_sub_of_deriv_lt` / 定理 `Convex.image_sub_lt_mul_sub_of_deriv_lt`

English:
theorem Convex.image_sub_lt_mul_sub_of_deriv_lt
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: by
  have hf'_gt : forall x in interior D, -C < deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.fun_neg]; rw [neg_lt_neg_iff]
    exact lt_hf' x hx
  linarith [hD.mul_sub_lt_image_sub_of_lt_deriv hf.fun_neg hf'.neg hf'_gt x hx y hy hxy]

中文:
定理 凸.image_sub_lt_mul_sub_of_deriv_lt
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: by
  have hf'_gt : forall x in interior D, -C < deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.fun_neg]; rw [neg_lt_neg_iff]
    exact lt_hf' x hx
  linarith [hD.mul_sub_lt_image_sub_of_lt_deriv hf.fun_neg hf'.neg hf'_gt x hx y hy hxy]

Depends on / 依赖: deriv.fun_neg, fun_neg, hD.mul_sub_lt_image_sub_of_lt_deriv, hf.fun_neg, interior, lt_hf, mul_sub_lt_image_sub_of_lt_deriv, neg_lt_neg_iff
-/
theorem Convex.image_sub_lt_mul_sub_of_deriv_lt {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) {C}
    (lt_hf' : forall x in interior D, deriv f x < C) (x : Real) (hx : x in D) (y : Real) (hy : y in D)
    (hxy : x < y) : f y - f x < C * (y - x) := by
  have hf'_gt : forall x in interior D, -C < deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.fun_neg]; rw [neg_lt_neg_iff]
    exact lt_hf' x hx
  linarith [hD.mul_sub_lt_image_sub_of_lt_deriv hf.fun_neg hf'.neg hf'_gt x hx y hy hxy]

/--
theorem `image_sub_lt_mul_sub_of_deriv_lt` / 定理 `image_sub_lt_mul_sub_of_deriv_lt`

English:
theorem image_sub_lt_mul_sub_of_deriv_lt
  statement: {f : Real -> Real} (hf : Differentiable Real f) {C}
  proof: convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => lt_hf' x) x trivial y trivial hxy

中文:
定理 image_sub_lt_mul_sub_of_deriv_lt
  结论: {f : 实数 -> 实数} (hf : 可微 实数 f) {C}
  证明: convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => lt_hf' x) x trivial y trivial hxy

Depends on / 依赖: continuous, continuousOn, convex_univ, convex_univ.image_sub_lt_mul_sub_of_deriv_lt, differentiableOn, hf.continuous.continuousOn, hf.differentiableOn, image_sub_lt_mul_sub_of_deriv_lt, lt_hf
-/
theorem image_sub_lt_mul_sub_of_deriv_lt {f : Real -> Real} (hf : Differentiable Real f) {C}
    (lt_hf' : forall x, deriv f x < C) ⦃x y⦄ (hxy : x < y) : f y - f x < C * (y - x) :=
  convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => lt_hf' x) x trivial y trivial hxy

/--
theorem `Convex.image_sub_le_mul_sub_of_deriv_le` / 定理 `Convex.image_sub_le_mul_sub_of_deriv_le`

English:
theorem Convex.image_sub_le_mul_sub_of_deriv_le
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: by
  have hf'_ge : forall x in interior D, -C <= deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.fun_neg]; rw [neg_le_neg_iff]
    exact le_hf' x hx
  linarith [hD.mul_sub_le_image_sub_of_le_deriv hf.fun_neg hf'.neg hf'_ge x hx y hy hxy]

中文:
定理 凸.image_sub_le_mul_sub_of_deriv_le
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: by
  have hf'_ge : forall x in interior D, -C <= deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.fun_neg]; rw [neg_le_neg_iff]
    exact le_hf' x hx
  linarith [hD.mul_sub_le_image_sub_of_le_deriv hf.fun_neg hf'.neg hf'_ge x hx y hy hxy]

Depends on / 依赖: deriv.fun_neg, fun_neg, hD.mul_sub_le_image_sub_of_le_deriv, hf.fun_neg, interior, le_hf, mul_sub_le_image_sub_of_le_deriv, neg_le_neg_iff
-/
theorem Convex.image_sub_le_mul_sub_of_deriv_le {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) {C}
    (le_hf' : forall x in interior D, deriv f x <= C) (x : Real) (hx : x in D) (y : Real) (hy : y in D)
    (hxy : x <= y) : f y - f x <= C * (y - x) := by
  have hf'_ge : forall x in interior D, -C <= deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.fun_neg]; rw [neg_le_neg_iff]
    exact le_hf' x hx
  linarith [hD.mul_sub_le_image_sub_of_le_deriv hf.fun_neg hf'.neg hf'_ge x hx y hy hxy]

/--
theorem `image_sub_le_mul_sub_of_deriv_le` / 定理 `image_sub_le_mul_sub_of_deriv_le`

English:
theorem image_sub_le_mul_sub_of_deriv_le
  statement: {f : Real -> Real} (hf : Differentiable Real f) {C}
  proof: convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => le_hf' x) x trivial y trivial hxy

中文:
定理 image_sub_le_mul_sub_of_deriv_le
  结论: {f : 实数 -> 实数} (hf : 可微 实数 f) {C}
  证明: convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => le_hf' x) x trivial y trivial hxy

Depends on / 依赖: continuous, continuousOn, convex_univ, convex_univ.image_sub_le_mul_sub_of_deriv_le, differentiableOn, hf.continuous.continuousOn, hf.differentiableOn, image_sub_le_mul_sub_of_deriv_le, le_hf
-/
theorem image_sub_le_mul_sub_of_deriv_le {f : Real -> Real} (hf : Differentiable Real f) {C}
    (le_hf' : forall x, deriv f x <= C) ⦃x y⦄ (hxy : x <= y) : f y - f x <= C * (y - x) :=
  convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => le_hf' x) x trivial y trivial hxy

/--
theorem `strictMonoOn_of_deriv_pos` / 定理 `strictMonoOn_of_deriv_pos`

English:
theorem strictMonoOn_of_deriv_pos
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: by
  intro x hx y hy
  have : DifferentiableOn Real f (interior D) := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hf' z hz).ne').differentiableWithinAt
  simpa only [zero_mul, sub_pos] using
    hD.mul_sub_lt_image_sub_of_lt_deriv hf this hf' x hx y hy

中文:
定理 strictMonoOn_of_deriv_pos
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: by
  intro x hx y hy
  have : DifferentiableOn Real f (interior D) := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hf' z hz).ne').differentiableWithinAt
  simpa only [zero_mul, sub_pos] using
    hD.mul_sub_lt_image_sub_of_lt_deriv hf this hf' x hx y hy

Depends on / 依赖: DifferentiableOn, differentiableAt_of_deriv_ne_zero, differentiableWithinAt, hD.mul_sub_lt_image_sub_of_lt_deriv, interior, mul_sub_lt_image_sub_of_lt_deriv, sub_pos, zero_mul
-/
theorem strictMonoOn_of_deriv_pos {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : forall x in interior D, 0 < deriv f x) : StrictMonoOn f D := by
  intro x hx y hy
  have : DifferentiableOn Real f (interior D) := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hf' z hz).ne').differentiableWithinAt
  simpa only [zero_mul, sub_pos] using
    hD.mul_sub_lt_image_sub_of_lt_deriv hf this hf' x hx y hy

/--
theorem `strictMono_of_deriv_pos` / 定理 `strictMono_of_deriv_pos`

English:
theorem strictMono_of_deriv_pos
  given: {f : Real -> Real} (hf' : forall x, 0 < deriv f x)
  statement: StrictMono f
  proof: strictMonoOn_univ.1 strictMonoOn_of_deriv_pos convex_univ (fun z _ =>
    (differentiableAt_of_deriv_ne_zero (hf' z).ne').differentiableWithinAt.continuousWithinAt)
    fun x _ => hf' x

中文:
定理 strictMono_of_deriv_pos
  条件: {f : 实数 -> 实数} (hf' : 对任意 x, 0 < deriv f x)
  结论: 严格递增 f
  证明: strictMonoOn_univ.1 strictMonoOn_of_deriv_pos convex_univ (fun z _ =>
    (differentiableAt_of_deriv_ne_zero (hf' z).ne').differentiableWithinAt.continuousWithinAt)
    fun x _ => hf' x

Depends on / 依赖: continuousWithinAt, convex_univ, differentiableAt_of_deriv_ne_zero, differentiableWithinAt, differentiableWithinAt.continuousWithinAt, strictMonoOn_of_deriv_pos, strictMonoOn_univ
-/
theorem strictMono_of_deriv_pos {f : Real -> Real} (hf' : forall x, 0 < deriv f x) : StrictMono f :=
strictMonoOn_univ.1 strictMonoOn_of_deriv_pos convex_univ (fun z _ =>
    (differentiableAt_of_deriv_ne_zero (hf' z).ne').differentiableWithinAt.continuousWithinAt)
    fun x _ => hf' x

/--
lemma `strictMonoOn_of_hasDerivWithinAt_pos` / 引理 `strictMonoOn_of_hasDerivWithinAt_pos`

English:
lemma strictMonoOn_of_hasDerivWithinAt_pos
  statement: {D : Set Real} (hD : Convex Real D) {f f' : Real -> Real}
  proof: strictMonoOn_of_deriv_pos hD hf fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

中文:
引理 strictMonoOn_of_hasDerivWithinAt_pos
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f f' : 实数 -> 实数}
  证明: strictMonoOn_of_deriv_pos hD hf fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

Depends on / 依赖: deriv_eqOn, isOpen_interior, strictMonoOn_of_deriv_pos
-/
lemma strictMonoOn_of_hasDerivWithinAt_pos {D : Set Real} (hD : Convex Real D) {f f' : Real -> Real}
    (hf : ContinuousOn f D) (hf' : forall x in interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : forall x in interior D, 0 < f' x) : StrictMonoOn f D :=
  strictMonoOn_of_deriv_pos hD hf fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/--
lemma `strictMono_of_hasDerivAt_pos` / 引理 `strictMono_of_hasDerivAt_pos`

English:
lemma strictMono_of_hasDerivAt_pos
  statement: {f f' : Real -> Real} (hf : forall x, HasDerivAt f (f' x) x)
  proof: strictMono_of_deriv_pos fun x => by rw [(hf _).deriv]; exact hf' _

中文:
引理 strictMono_of_hasDerivAt_pos
  结论: {f f' : 实数 -> 实数} (hf : 对任意 x, 在点处可导 f (f' x) x)
  证明: strictMono_of_deriv_pos fun x => by rw [(hf _).deriv]; exact hf' _

Depends on / 依赖: strictMono_of_deriv_pos
-/
lemma strictMono_of_hasDerivAt_pos {f f' : Real -> Real} (hf : forall x, HasDerivAt f (f' x) x)
    (hf' : forall x, 0 < f' x) : StrictMono f :=
  strictMono_of_deriv_pos fun x => by rw [(hf _).deriv]; exact hf' _

/--
theorem `monotoneOn_of_deriv_nonneg` / 定理 `monotoneOn_of_deriv_nonneg`

English:
theorem monotoneOn_of_deriv_nonneg
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonneg] using
    hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg x hx y hy hxy

中文:
定理 monotoneOn_of_deriv_nonneg
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonneg] using
    hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg x hx y hy hxy

Depends on / 依赖: _nonneg, hD.mul_sub_le_image_sub_of_le_deriv, mul_sub_le_image_sub_of_le_deriv, sub_nonneg, zero_mul
-/
theorem monotoneOn_of_deriv_nonneg {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D))
    (hf'_nonneg : forall x in interior D, 0 <= deriv f x) : MonotoneOn f D := fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonneg] using
    hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg x hx y hy hxy

/--
theorem `monotone_of_deriv_nonneg` / 定理 `monotone_of_deriv_nonneg`

English:
theorem monotone_of_deriv_nonneg
  given: {f : Real -> Real} (hf : Differentiable Real f) (hf' : forall x, 0 <= deriv f x)
  proof: monotoneOn_univ.1
    monotoneOn_of_deriv_nonneg convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x

中文:
定理 monotone_of_deriv_nonneg
  条件: {f : 实数 -> 实数} (hf : 可微 实数 f) (hf' : 对任意 x, 0 <= deriv f x)
  证明: monotoneOn_univ.1
    monotoneOn_of_deriv_nonneg convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x

Depends on / 依赖: continuous, continuousOn, convex_univ, differentiableOn, hf.continuous.continuousOn, hf.differentiableOn, monotoneOn_of_deriv_nonneg, monotoneOn_univ
-/
theorem monotone_of_deriv_nonneg {f : Real -> Real} (hf : Differentiable Real f) (hf' : forall x, 0 <= deriv f x) :
    Monotone f :=
monotoneOn_univ.1
    monotoneOn_of_deriv_nonneg convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x

/--
lemma `monotoneOn_of_hasDerivWithinAt_nonneg` / 引理 `monotoneOn_of_hasDerivWithinAt_nonneg`

English:
lemma monotoneOn_of_hasDerivWithinAt_nonneg
  statement: {D : Set Real} (hD : Convex Real D) {f f' : Real -> Real}
  proof: monotoneOn_of_deriv_nonneg hD hf (fun _ hx => (hf' _ hx).differentiableWithinAt) fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

中文:
引理 monotoneOn_of_hasDerivWithinAt_nonneg
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f f' : 实数 -> 实数}
  证明: monotoneOn_of_deriv_nonneg hD hf (fun _ hx => (hf' _ hx).differentiableWithinAt) fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

Depends on / 依赖: deriv_eqOn, differentiableWithinAt, isOpen_interior, monotoneOn_of_deriv_nonneg
-/
lemma monotoneOn_of_hasDerivWithinAt_nonneg {D : Set Real} (hD : Convex Real D) {f f' : Real -> Real}
    (hf : ContinuousOn f D) (hf' : forall x in interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : forall x in interior D, 0 <= f' x) : MonotoneOn f D :=
  monotoneOn_of_deriv_nonneg hD hf (fun _ hx => (hf' _ hx).differentiableWithinAt) fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/--
lemma `monotone_of_hasDerivAt_nonneg` / 引理 `monotone_of_hasDerivAt_nonneg`

English:
lemma monotone_of_hasDerivAt_nonneg
  statement: {f f' : Real -> Real} (hf : forall x, HasDerivAt f (f' x) x)
  proof: monotone_of_deriv_nonneg (fun _ => (hf _).differentiableAt) fun x => by
    rw [(hf _).deriv]; exact hf' _

中文:
引理 monotone_of_hasDerivAt_nonneg
  结论: {f f' : 实数 -> 实数} (hf : 对任意 x, 在点处可导 f (f' x) x)
  证明: monotone_of_deriv_nonneg (fun _ => (hf _).differentiableAt) fun x => by
    rw [(hf _).deriv]; exact hf' _

Depends on / 依赖: differentiableAt, monotone_of_deriv_nonneg
-/
lemma monotone_of_hasDerivAt_nonneg {f f' : Real -> Real} (hf : forall x, HasDerivAt f (f' x) x)
    (hf' : 0 <= f') : Monotone f :=
  monotone_of_deriv_nonneg (fun _ => (hf _).differentiableAt) fun x => by
    rw [(hf _).deriv]; exact hf' _

/--
theorem `strictAntiOn_of_deriv_neg` / 定理 `strictAntiOn_of_deriv_neg`

English:
theorem strictAntiOn_of_deriv_neg
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: fun x hx y => by
  simpa only [zero_mul, sub_lt_zero] using
    hD.image_sub_lt_mul_sub_of_deriv_lt hf
      (fun z hz => (differentiableAt_of_deriv_ne_zero (hf' z hz).ne).differentiableWithinAt) hf' x
      hx y

中文:
定理 strictAntiOn_of_deriv_neg
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: fun x hx y => by
  simpa only [zero_mul, sub_lt_zero] using
    hD.image_sub_lt_mul_sub_of_deriv_lt hf
      (fun z hz => (differentiableAt_of_deriv_ne_zero (hf' z hz).ne).differentiableWithinAt) hf' x
      hx y

Depends on / 依赖: differentiableAt_of_deriv_ne_zero, differentiableWithinAt, hD.image_sub_lt_mul_sub_of_deriv_lt, image_sub_lt_mul_sub_of_deriv_lt, sub_lt_zero, zero_mul
-/
theorem strictAntiOn_of_deriv_neg {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : forall x in interior D, deriv f x < 0) : StrictAntiOn f D :=
  fun x hx y => by
  simpa only [zero_mul, sub_lt_zero] using
    hD.image_sub_lt_mul_sub_of_deriv_lt hf
      (fun z hz => (differentiableAt_of_deriv_ne_zero (hf' z hz).ne).differentiableWithinAt) hf' x
      hx y

/--
theorem `strictAnti_of_deriv_neg` / 定理 `strictAnti_of_deriv_neg`

English:
theorem strictAnti_of_deriv_neg
  given: {f : Real -> Real} (hf' : forall x, deriv f x < 0)
  statement: StrictAnti f
  proof: strictAntiOn_univ.1 strictAntiOn_of_deriv_neg convex_univ
      (fun z _ =>
        (differentiableAt_of_deriv_ne_zero (hf' z).ne).differentiableWithinAt.continuousWithinAt)
      fun x _ => hf' x

中文:
定理 strictAnti_of_deriv_neg
  条件: {f : 实数 -> 实数} (hf' : 对任意 x, deriv f x < 0)
  结论: 严格递减 f
  证明: strictAntiOn_univ.1 strictAntiOn_of_deriv_neg convex_univ
      (fun z _ =>
        (differentiableAt_of_deriv_ne_zero (hf' z).ne).differentiableWithinAt.continuousWithinAt)
      fun x _ => hf' x

Depends on / 依赖: continuousWithinAt, convex_univ, differentiableAt_of_deriv_ne_zero, differentiableWithinAt, differentiableWithinAt.continuousWithinAt, strictAntiOn_of_deriv_neg, strictAntiOn_univ
-/
theorem strictAnti_of_deriv_neg {f : Real -> Real} (hf' : forall x, deriv f x < 0) : StrictAnti f :=
strictAntiOn_univ.1 strictAntiOn_of_deriv_neg convex_univ
      (fun z _ =>
        (differentiableAt_of_deriv_ne_zero (hf' z).ne).differentiableWithinAt.continuousWithinAt)
      fun x _ => hf' x

/--
lemma `strictAntiOn_of_hasDerivWithinAt_neg` / 引理 `strictAntiOn_of_hasDerivWithinAt_neg`

English:
lemma strictAntiOn_of_hasDerivWithinAt_neg
  statement: {D : Set Real} (hD : Convex Real D) {f f' : Real -> Real}
  proof: strictAntiOn_of_deriv_neg hD hf fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

中文:
引理 strictAntiOn_of_hasDerivWithinAt_neg
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f f' : 实数 -> 实数}
  证明: strictAntiOn_of_deriv_neg hD hf fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

Depends on / 依赖: deriv_eqOn, isOpen_interior, strictAntiOn_of_deriv_neg
-/
lemma strictAntiOn_of_hasDerivWithinAt_neg {D : Set Real} (hD : Convex Real D) {f f' : Real -> Real}
    (hf : ContinuousOn f D) (hf' : forall x in interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : forall x in interior D, f' x < 0) : StrictAntiOn f D :=
  strictAntiOn_of_deriv_neg hD hf fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/--
lemma `strictAnti_of_hasDerivAt_neg` / 引理 `strictAnti_of_hasDerivAt_neg`

English:
lemma strictAnti_of_hasDerivAt_neg
  statement: {f f' : Real -> Real} (hf : forall x, HasDerivAt f (f' x) x)
  proof: strictAnti_of_deriv_neg fun x => by rw [(hf _).deriv]; exact hf' _

中文:
引理 strictAnti_of_hasDerivAt_neg
  结论: {f f' : 实数 -> 实数} (hf : 对任意 x, 在点处可导 f (f' x) x)
  证明: strictAnti_of_deriv_neg fun x => by rw [(hf _).deriv]; exact hf' _

Depends on / 依赖: strictAnti_of_deriv_neg
-/
lemma strictAnti_of_hasDerivAt_neg {f f' : Real -> Real} (hf : forall x, HasDerivAt f (f' x) x)
    (hf' : forall x, f' x < 0) : StrictAnti f :=
  strictAnti_of_deriv_neg fun x => by rw [(hf _).deriv]; exact hf' _

/--
theorem `antitoneOn_of_deriv_nonpos` / 定理 `antitoneOn_of_deriv_nonpos`

English:
theorem antitoneOn_of_deriv_nonpos
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonpos] using
    hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos x hx y hy hxy

中文:
定理 antitoneOn_of_deriv_nonpos
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonpos] using
    hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos x hx y hy hxy

Depends on / 依赖: _nonpos, hD.image_sub_le_mul_sub_of_deriv_le, image_sub_le_mul_sub_of_deriv_le, sub_nonpos, zero_mul
-/
theorem antitoneOn_of_deriv_nonpos {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D))
    (hf'_nonpos : forall x in interior D, deriv f x <= 0) : AntitoneOn f D := fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonpos] using
    hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos x hx y hy hxy

/--
theorem `antitone_of_deriv_nonpos` / 定理 `antitone_of_deriv_nonpos`

English:
theorem antitone_of_deriv_nonpos
  given: {f : Real -> Real} (hf : Differentiable Real f) (hf' : forall x, deriv f x <= 0)
  proof: antitoneOn_univ.1
    antitoneOn_of_deriv_nonpos convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x

中文:
定理 antitone_of_deriv_nonpos
  条件: {f : 实数 -> 实数} (hf : 可微 实数 f) (hf' : 对任意 x, deriv f x <= 0)
  证明: antitoneOn_univ.1
    antitoneOn_of_deriv_nonpos convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x

Depends on / 依赖: antitoneOn_of_deriv_nonpos, antitoneOn_univ, continuous, continuousOn, convex_univ, differentiableOn, hf.continuous.continuousOn, hf.differentiableOn
-/
theorem antitone_of_deriv_nonpos {f : Real -> Real} (hf : Differentiable Real f) (hf' : forall x, deriv f x <= 0) :
    Antitone f :=
antitoneOn_univ.1
    antitoneOn_of_deriv_nonpos convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x

/--
lemma `antitoneOn_of_hasDerivWithinAt_nonpos` / 引理 `antitoneOn_of_hasDerivWithinAt_nonpos`

English:
lemma antitoneOn_of_hasDerivWithinAt_nonpos
  statement: {D : Set Real} (hD : Convex Real D) {f f' : Real -> Real}
  proof: antitoneOn_of_deriv_nonpos hD hf (fun _ hx => (hf' _ hx).differentiableWithinAt) fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

中文:
引理 antitoneOn_of_hasDerivWithinAt_nonpos
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f f' : 实数 -> 实数}
  证明: antitoneOn_of_deriv_nonpos hD hf (fun _ hx => (hf' _ hx).differentiableWithinAt) fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

Depends on / 依赖: antitoneOn_of_deriv_nonpos, deriv_eqOn, differentiableWithinAt, isOpen_interior
-/
lemma antitoneOn_of_hasDerivWithinAt_nonpos {D : Set Real} (hD : Convex Real D) {f f' : Real -> Real}
    (hf : ContinuousOn f D) (hf' : forall x in interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : forall x in interior D, f' x <= 0) : AntitoneOn f D :=
  antitoneOn_of_deriv_nonpos hD hf (fun _ hx => (hf' _ hx).differentiableWithinAt) fun x hx => by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/--
lemma `antitone_of_hasDerivAt_nonpos` / 引理 `antitone_of_hasDerivAt_nonpos`

English:
lemma antitone_of_hasDerivAt_nonpos
  statement: {f f' : Real -> Real} (hf : forall x, HasDerivAt f (f' x) x)
  proof: antitone_of_deriv_nonpos (fun _ => (hf _).differentiableAt) fun x => by
    rw [(hf _).deriv]; exact hf' _

中文:
引理 antitone_of_hasDerivAt_nonpos
  结论: {f f' : 实数 -> 实数} (hf : 对任意 x, 在点处可导 f (f' x) x)
  证明: antitone_of_deriv_nonpos (fun _ => (hf _).differentiableAt) fun x => by
    rw [(hf _).deriv]; exact hf' _

Depends on / 依赖: antitone_of_deriv_nonpos, differentiableAt
-/
lemma antitone_of_hasDerivAt_nonpos {f f' : Real -> Real} (hf : forall x, HasDerivAt f (f' x) x)
    (hf' : f' <= 0) : Antitone f :=
  antitone_of_deriv_nonpos (fun _ => (hf _).differentiableAt) fun x => by
    rw [(hf _).deriv]; exact hf' _

/-! ### Functions `f : E → ℝ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `domain_mvt` / 定理 `domain_mvt`

English:
theorem domain_mvt
  statement: {f : E -> Real} {s : Set E} {x y : E} {f' : E -> StrongDual Real E}
  proof: by
  -- Use `g = AffineMap.lineMap x y` to parametrize the segment
  set g : Real -> E := fun t => AffineMap.lineMap x y t
  set I := Icc (0 : Real) 1
  have hsub : Ioo (0 : Real) 1 subseteq I := Ioo_subset_Icc_self
  have hmaps : MapsTo g I s := hs.mapsTo_lineMap xs ys
  -- The one-variable functio

中文:
定理 domain_mvt
  结论: {f : E -> 实数} {s : 集合 E} {x y : E} {f' : E -> StrongDual 实数 E}
  证明: by
  -- Use `g = AffineMap.lineMap x y` to parametrize the segment
  set g : Real -> E := fun t => AffineMap.lineMap x y t
  set I := Icc (0 : Real) 1
  have hsub : Ioo (0 : Real) 1 subseteq I := Ioo_subset_Icc_self
  have hmaps : MapsTo g I s := hs.mapsTo_lineMap xs ys
  -- The one-variable functio
-/
theorem domain_mvt {f : E -> Real} {s : Set E} {x y : E} {f' : E -> StrongDual Real E}
    (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (hs : Convex Real s) (xs : x in s) (ys : y in s) :
    exists z in segment Real x y, f y - f x = f' z (y - x) := by
  -- Use `g = AffineMap.lineMap x y` to parametrize the segment
  set g : Real -> E := fun t => AffineMap.lineMap x y t
  set I := Icc (0 : Real) 1
  have hsub : Ioo (0 : Real) 1 subseteq I := Ioo_subset_Icc_self
  have hmaps : MapsTo g I s := hs.mapsTo_lineMap xs ys
  -- The one-variable function `f ∘ g` has derivative `f' (g t) (y - x)` at each `t ∈ I`
  have hfg : forall t in I, HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) I t := fun t ht =>
    (hf _ (hmaps ht)).comp_hasDerivWithinAt t AffineMap.hasDerivWithinAt_lineMap hmaps
  -- apply 1-variable mean value theorem to pullback
  have hMVT : exists t in Ioo (0 : Real) 1, f' (g t) (y - x) = (f (g 1) - f (g 0)) / (1 - 0) := by
    refine exists_hasDerivAt_eq_slope (f ∘ g) _ (by simp) ?_ ?_
    · exact fun t Ht => (hfg t Ht).continuousWithinAt
    · exact fun t Ht => (hfg t <| hsub Ht).hasDerivAt (Icc_mem_nhds Ht.1 Ht.2)
  -- reinterpret on domain
  rcases hMVT with ⟨t, Ht, hMVT'⟩
  rw [segment_eq_image_lineMap]; rw [exists_mem_image]
  refine ⟨t, hsub Ht, ?_⟩
  simpa [g] using hMVT'.symm
