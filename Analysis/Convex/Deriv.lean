/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov, David Loeffler
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Convexity of functions and derivatives

Here we relate convexity of functions `ℝ → ℝ` to properties of their derivatives.

## Main results

* `MonotoneOn.convexOn_of_deriv`, `convexOn_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.
* `ConvexOn.monotoneOn_deriv`: if a function is convex and differentiable, then its derivative is
  monotone.
-/

public section

open Metric Set Asymptotics ContinuousLinearMap Filter
open scoped Topology NNReal

/-!
## Monotonicity of `f'` implies convexity of `f`
-/

/--
theorem `MonotoneOn.convexOn_of_deriv` / 定理 `MonotoneOn.convexOn_of_deriv`

English:
theorem MonotoneOn.convexOn_of_deriv
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: convexOn_of_slope_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      -- First we prove some trivial inclusions
      have hxzD : Icc x z subseteq D := hD.ordConnected.out hx hz
      have hxyD : Icc x y subseteq D := (Icc_subset_Icc_right hyz.le).trans hxzD
      have hxyD' : Ioo x y sub

中文:
定理 MonotoneOn.convexOn_of_deriv
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: convexOn_of_slope_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      -- First we prove some trivial inclusions
      have hxzD : Icc x z subseteq D := hD.ordConnected.out hx hz
      have hxyD : Icc x y subseteq D := (Icc_subset_Icc_right hyz.le).trans hxzD
      have hxyD' : Ioo x y sub

Depends on / 依赖: convexOn_of_slope_mono_adjacent
-/
theorem MonotoneOn.convexOn_of_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D))
    (hf'_mono : MonotoneOn (deriv f) (interior D)) : ConvexOn Real D f :=
  convexOn_of_slope_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      -- First we prove some trivial inclusions
      have hxzD : Icc x z subseteq D := hD.ordConnected.out hx hz
      have hxyD : Icc x y subseteq D := (Icc_subset_Icc_right hyz.le).trans hxzD
      have hxyD' : Ioo x y subseteq interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
      have hyzD : Icc y z subseteq D := (Icc_subset_Icc_left hxy.le).trans hxzD
      have hyzD' : Ioo y z subseteq interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
      -- Then we apply MVT to both `[x, y]` and `[y, z]`
      obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
        exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
      obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : exists b in Ioo y z, deriv f b = (f z - f y) / (z - y) :=
        exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD')
      rw [← ha]; rw [← hb]
      exact hf'_mono (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb).le)

/--
theorem `AntitoneOn.concaveOn_of_deriv` / 定理 `AntitoneOn.concaveOn_of_deriv`

English:
theorem AntitoneOn.concaveOn_of_deriv
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: haveI : MonotoneOn (deriv (-f)) (interior D) := by
    simpa only [← deriv.neg] using h_anti.neg
  neg_convexOn_iff.mp (this.convexOn_of_deriv hD hf.neg hf'.neg)

中文:
定理 AntitoneOn.concaveOn_of_deriv
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: haveI : MonotoneOn (deriv (-f)) (interior D) := by
    simpa only [← deriv.neg] using h_anti.neg
  neg_convexOn_iff.mp (this.convexOn_of_deriv hD hf.neg hf'.neg)

Depends on / 依赖: MonotoneOn, convexOn_of_deriv, deriv.neg, h_anti, h_anti.neg, hf.neg, interior, neg_convexOn_iff, neg_convexOn_iff.mp, this.convexOn_of_deriv
-/
theorem AntitoneOn.concaveOn_of_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D))
    (h_anti : AntitoneOn (deriv f) (interior D)) : ConcaveOn Real D f :=
  haveI : MonotoneOn (deriv (-f)) (interior D) := by
    simpa only [← deriv.neg] using h_anti.neg
  neg_convexOn_iff.mp (this.convexOn_of_deriv hD hf.neg hf'.neg)

/--
theorem `StrictMonoOn.exists_slope_lt_deriv_aux` / 定理 `StrictMonoOn.exists_slope_lt_deriv_aux`

English:
theorem StrictMonoOn.exists_slope_lt_deriv_aux
  statement: {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y))
  proof: by
  have A : DifferentiableOn Real f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b

中文:
定理 StrictMonoOn.存在_slope_lt_deriv_aux
  结论: {x y : 实数} {f : 实数 -> 实数} (hf : ContinuousOn f (闭区间 x y))
  证明: by
  have A : DifferentiableOn Real f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b

Depends on / 依赖: DifferentiableOn, _mono, differentiableAt_of_deriv_ne_zero, differentiableWithinAt, exists_deriv_eq_slope, hxa.trans, nonempty_Ioo
-/
theorem StrictMonoOn.exists_slope_lt_deriv_aux {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : forall w in Ioo x y, deriv f w != 0) :
    exists a in Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  have A : DifferentiableOn Real f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b, ⟨hab, hby⟩⟩
  refine ⟨b, ⟨hxa.trans hab, hby⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxa, hay⟩ ⟨hxa.trans hab, hby⟩ hab

/--
theorem `StrictMonoOn.exists_slope_lt_deriv` / 定理 `StrictMonoOn.exists_slope_lt_deriv`

English:
theorem StrictMonoOn.exists_slope_lt_deriv
  statement: {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y))
  proof: by
  by_cases! h : forall w in Ioo x y, deriv f w != 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : exists a in Ioo x w, (f w - f x) / (w - x) < deriv f a := by
      apply StrictMonoOn.exists_slope_lt_deriv

中文:
定理 StrictMonoOn.存在_slope_lt_deriv
  结论: {x y : 实数} {f : 实数 -> 实数} (hf : ContinuousOn f (闭区间 x y))
  证明: by
  by_cases! h : forall w in Ioo x y, deriv f w != 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : exists a in Ioo x w, (f w - f x) / (w - x) < deriv f a := by
      apply StrictMonoOn.exists_slope_lt_deriv

Depends on / 依赖: Icc_subset_Icc, Ioo_subset_Ioo, StrictMonoOn, StrictMonoOn.exists_slope_lt_deriv_aux, _mono, _mono.mono, exists_slope_lt_deriv_aux, hf.mono, hwy.le, le_rfl, ne_of_lt
-/
theorem StrictMonoOn.exists_slope_lt_deriv {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    exists a in Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  by_cases! h : forall w in Ioo x y, deriv f w != 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : exists a in Ioo x w, (f w - f x) / (w - x) < deriv f a := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : exists b in Ioo w y, (f y - f w) / (y - w) < deriv f b := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hwy _ _
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨b, ⟨hxw.trans hwb, hby⟩, ?_⟩
    simp only [div_lt_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (w - x) < deriv f b * (w - x) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hxw) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith

/--
theorem `StrictMonoOn.exists_deriv_lt_slope_aux` / 定理 `StrictMonoOn.exists_deriv_lt_slope_aux`

English:
theorem StrictMonoOn.exists_deriv_lt_slope_aux
  statement: {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y))
  proof: by
  have A : DifferentiableOn Real f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b

中文:
定理 StrictMonoOn.存在_deriv_lt_slope_aux
  结论: {x y : 实数} {f : 实数 -> 实数} (hf : ContinuousOn f (闭区间 x y))
  证明: by
  have A : DifferentiableOn Real f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b

Depends on / 依赖: DifferentiableOn, _mono, differentiableAt_of_deriv_ne_zero, differentiableWithinAt, exists_deriv_eq_slope, hba.trans, nonempty_Ioo
-/
theorem StrictMonoOn.exists_deriv_lt_slope_aux {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : forall w in Ioo x y, deriv f w != 0) :
    exists a in Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  have A : DifferentiableOn Real f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : exists a in Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b, ⟨hxb, hba⟩⟩
  refine ⟨b, ⟨hxb, hba.trans hay⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxb, hba.trans hay⟩ ⟨hxa, hay⟩ hba

/--
theorem `StrictMonoOn.exists_deriv_lt_slope` / 定理 `StrictMonoOn.exists_deriv_lt_slope`

English:
theorem StrictMonoOn.exists_deriv_lt_slope
  statement: {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y))
  proof: by
  by_cases! h : forall w in Ioo x y, deriv f w != 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : exists a in Ioo x w, deriv f a < (f w - f x) / (w - x) := by
      apply StrictMonoOn.exists_deriv_lt_slope

中文:
定理 StrictMonoOn.存在_deriv_lt_slope
  结论: {x y : 实数} {f : 实数 -> 实数} (hf : ContinuousOn f (闭区间 x y))
  证明: by
  by_cases! h : forall w in Ioo x y, deriv f w != 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : exists a in Ioo x w, deriv f a < (f w - f x) / (w - x) := by
      apply StrictMonoOn.exists_deriv_lt_slope

Depends on / 依赖: Icc_subset_Icc, Ioo_subset_Ioo, StrictMonoOn, StrictMonoOn.exists_deriv_lt_slope_aux, _mono, _mono.mono, exists_deriv_lt_slope_aux, hf.mono, hwy.le, le_rfl, ne_of_lt
-/
theorem StrictMonoOn.exists_deriv_lt_slope {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    exists a in Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  by_cases! h : forall w in Ioo x y, deriv f w != 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : exists a in Ioo x w, deriv f a < (f w - f x) / (w - x) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : exists b in Ioo w y, deriv f b < (f y - f w) / (y - w) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hwy _ _
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨a, ⟨hxa, haw.trans hwy⟩, ?_⟩
    simp only [lt_div_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (y - w) < deriv f b * (y - w) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hwy) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith

/--
theorem `StrictMonoOn.strictConvexOn_of_deriv` / 定理 `StrictMonoOn.strictConvexOn_of_deriv`

English:
theorem StrictMonoOn.strictConvexOn_of_deriv
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: strictConvexOn_of_slope_strict_mono_adjacent hD fun {x y z} hx hz hxy hyz => by
    -- First we prove some trivial inclusions
    have hxzD : Icc x z subseteq D := hD.ordConnected.out hx hz
    have hxyD : Icc x y subseteq D := (Icc_subset_Icc_right hyz.le).trans hxzD
    have hxyD' : Ioo x y subset

中文:
定理 StrictMonoOn.strictConvexOn_of_deriv
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: strictConvexOn_of_slope_strict_mono_adjacent hD fun {x y z} hx hz hxy hyz => by
    -- First we prove some trivial inclusions
    have hxzD : Icc x z subseteq D := hD.ordConnected.out hx hz
    have hxyD : Icc x y subseteq D := (Icc_subset_Icc_right hyz.le).trans hxzD
    have hxyD' : Ioo x y subset

Depends on / 依赖: strictConvexOn_of_slope_strict_mono_adjacent
-/
theorem StrictMonoOn.strictConvexOn_of_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf' : StrictMonoOn (deriv f) (interior D)) : StrictConvexOn Real D f :=
  strictConvexOn_of_slope_strict_mono_adjacent hD fun {x y z} hx hz hxy hyz => by
    -- First we prove some trivial inclusions
    have hxzD : Icc x z subseteq D := hD.ordConnected.out hx hz
    have hxyD : Icc x y subseteq D := (Icc_subset_Icc_right hyz.le).trans hxzD
    have hxyD' : Ioo x y subseteq interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
    have hyzD : Icc y z subseteq D := (Icc_subset_Icc_left hxy.le).trans hxzD
    have hyzD' : Ioo y z subseteq interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
    -- Then we get points `a` and `b` in each interval `[x, y]` and `[y, z]` where the derivatives
    -- can be compared to the slopes between `x, y` and `y, z` respectively.
    obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : exists a in Ioo x y, (f y - f x) / (y - x) < deriv f a :=
      StrictMonoOn.exists_slope_lt_deriv (hf.mono hxyD) hxy (hf'.mono hxyD')
    obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : exists b in Ioo y z, deriv f b < (f z - f y) / (z - y) :=
      StrictMonoOn.exists_deriv_lt_slope (hf.mono hyzD) hyz (hf'.mono hyzD')
    apply ha.trans (lt_trans _ hb)
    exact hf' (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb)

/--
theorem `StrictAntiOn.strictConcaveOn_of_deriv` / 定理 `StrictAntiOn.strictConcaveOn_of_deriv`

English:
theorem StrictAntiOn.strictConcaveOn_of_deriv
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: have : StrictMonoOn (deriv (-f)) (interior D) := by simpa only [← deriv.neg] using h_anti.neg
  neg_neg f ▸ (this.strictConvexOn_of_deriv hD hf.neg).neg

中文:
定理 StrictAntiOn.strictConcaveOn_of_deriv
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: have : StrictMonoOn (deriv (-f)) (interior D) := by simpa only [← deriv.neg] using h_anti.neg
  neg_neg f ▸ (this.strictConvexOn_of_deriv hD hf.neg).neg

Depends on / 依赖: StrictMonoOn, deriv.neg, h_anti, h_anti.neg, hf.neg, interior, neg_neg, strictConvexOn_of_deriv, this.strictConvexOn_of_deriv
-/
theorem StrictAntiOn.strictConcaveOn_of_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (h_anti : StrictAntiOn (deriv f) (interior D)) :
    StrictConcaveOn Real D f :=
  have : StrictMonoOn (deriv (-f)) (interior D) := by simpa only [← deriv.neg] using h_anti.neg
  neg_neg f ▸ (this.strictConvexOn_of_deriv hD hf.neg).neg

/--
theorem `Monotone.convexOn_univ_of_deriv` / 定理 `Monotone.convexOn_univ_of_deriv`

English:
theorem Monotone.convexOn_univ_of_deriv
  statement: {f : Real -> Real} (hf : Differentiable Real f)
  proof: (hf'_mono.monotoneOn _).convexOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

中文:
定理 递增.convexOn_univ_of_deriv
  结论: {f : 实数 -> 实数} (hf : 可微 实数 f)
  证明: (hf'_mono.monotoneOn _).convexOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

Depends on / 依赖: _mono, _mono.monotoneOn, continuous, continuousOn, convexOn_of_deriv, convex_univ, differentiableOn, hf.continuous.continuousOn, hf.differentiableOn, monotoneOn
-/
theorem Monotone.convexOn_univ_of_deriv {f : Real -> Real} (hf : Differentiable Real f)
    (hf'_mono : Monotone (deriv f)) : ConvexOn Real univ f :=
  (hf'_mono.monotoneOn _).convexOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

/--
theorem `Antitone.concaveOn_univ_of_deriv` / 定理 `Antitone.concaveOn_univ_of_deriv`

English:
theorem Antitone.concaveOn_univ_of_deriv
  statement: {f : Real -> Real} (hf : Differentiable Real f)
  proof: (hf'_anti.antitoneOn _).concaveOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

中文:
定理 递减.concaveOn_univ_of_deriv
  结论: {f : 实数 -> 实数} (hf : 可微 实数 f)
  证明: (hf'_anti.antitoneOn _).concaveOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

Depends on / 依赖: _anti, _anti.antitoneOn, antitoneOn, concaveOn_of_deriv, continuous, continuousOn, convex_univ, differentiableOn, hf.continuous.continuousOn, hf.differentiableOn
-/
theorem Antitone.concaveOn_univ_of_deriv {f : Real -> Real} (hf : Differentiable Real f)
    (hf'_anti : Antitone (deriv f)) : ConcaveOn Real univ f :=
  (hf'_anti.antitoneOn _).concaveOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

/--
theorem `StrictMono.strictConvexOn_univ_of_deriv` / 定理 `StrictMono.strictConvexOn_univ_of_deriv`

English:
theorem StrictMono.strictConvexOn_univ_of_deriv
  statement: {f : Real -> Real} (hf : Continuous f)
  proof: (hf'_mono.strictMonoOn _).strictConvexOn_of_deriv convex_univ hf.continuousOn

中文:
定理 严格递增.strictConvexOn_univ_of_deriv
  结论: {f : 实数 -> 实数} (hf : 连续 f)
  证明: (hf'_mono.strictMonoOn _).strictConvexOn_of_deriv convex_univ hf.continuousOn

Depends on / 依赖: _mono, _mono.strictMonoOn, continuousOn, convex_univ, hf.continuousOn, strictConvexOn_of_deriv, strictMonoOn
-/
theorem StrictMono.strictConvexOn_univ_of_deriv {f : Real -> Real} (hf : Continuous f)
    (hf'_mono : StrictMono (deriv f)) : StrictConvexOn Real univ f :=
  (hf'_mono.strictMonoOn _).strictConvexOn_of_deriv convex_univ hf.continuousOn

/--
theorem `StrictAnti.strictConcaveOn_univ_of_deriv` / 定理 `StrictAnti.strictConcaveOn_univ_of_deriv`

English:
theorem StrictAnti.strictConcaveOn_univ_of_deriv
  statement: {f : Real -> Real} (hf : Continuous f)
  proof: (hf'_anti.strictAntiOn _).strictConcaveOn_of_deriv convex_univ hf.continuousOn

中文:
定理 严格递减.strictConcaveOn_univ_of_deriv
  结论: {f : 实数 -> 实数} (hf : 连续 f)
  证明: (hf'_anti.strictAntiOn _).strictConcaveOn_of_deriv convex_univ hf.continuousOn

Depends on / 依赖: _anti, _anti.strictAntiOn, continuousOn, convex_univ, hf.continuousOn, strictAntiOn, strictConcaveOn_of_deriv
-/
theorem StrictAnti.strictConcaveOn_univ_of_deriv {f : Real -> Real} (hf : Continuous f)
    (hf'_anti : StrictAnti (deriv f)) : StrictConcaveOn Real univ f :=
  (hf'_anti.strictAntiOn _).strictConcaveOn_of_deriv convex_univ hf.continuousOn

/--
theorem `convexOn_of_deriv2_nonneg` / 定理 `convexOn_of_deriv2_nonneg`

English:
theorem convexOn_of_deriv2_nonneg
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D)
  proof: (monotoneOn_of_deriv_nonneg hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).convexOn_of_deriv
    hD hf hf'

中文:
定理 convexOn_of_deriv2_nonneg
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数} (hf : ContinuousOn f D)
  证明: (monotoneOn_of_deriv_nonneg hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).convexOn_of_deriv
    hD hf hf'

Depends on / 依赖: continuousOn, convexOn_of_deriv, hD.interior, interior, interior_interior, monotoneOn_of_deriv_nonneg
-/
theorem convexOn_of_deriv2_nonneg {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn Real f (interior D)) (hf'' : DifferentiableOn Real (deriv f) (interior D))
    (hf''_nonneg : forall x in interior D, 0 <= deriv^[2] f x) : ConvexOn Real D f :=
  (monotoneOn_of_deriv_nonneg hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).convexOn_of_deriv
    hD hf hf'

/--
theorem `concaveOn_of_deriv2_nonpos` / 定理 `concaveOn_of_deriv2_nonpos`

English:
theorem concaveOn_of_deriv2_nonpos
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D)
  proof: (antitoneOn_of_deriv_nonpos hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).concaveOn_of_deriv
    hD hf hf'

中文:
定理 concaveOn_of_deriv2_nonpos
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数} (hf : ContinuousOn f D)
  证明: (antitoneOn_of_deriv_nonpos hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).concaveOn_of_deriv
    hD hf hf'

Depends on / 依赖: antitoneOn_of_deriv_nonpos, concaveOn_of_deriv, continuousOn, hD.interior, interior, interior_interior
-/
theorem concaveOn_of_deriv2_nonpos {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn Real f (interior D)) (hf'' : DifferentiableOn Real (deriv f) (interior D))
    (hf''_nonpos : forall x in interior D, deriv^[2] f x <= 0) : ConcaveOn Real D f :=
  (antitoneOn_of_deriv_nonpos hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).concaveOn_of_deriv
    hD hf hf'

/--
lemma `convexOn_of_hasDerivWithinAt2_nonneg` / 引理 `convexOn_of_hasDerivWithinAt2_nonneg`

English:
lemma convexOn_of_hasDerivWithinAt2_nonneg
  statement: {D : Set Real} (hD : Convex Real D) {f f' f'' : Real -> Real}
  proof: by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine convexOn_of_deriv2_nonneg hD hf (fun x hx => (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx => (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ 

中文:
引理 convexOn_of_hasDerivWithinAt2_nonneg
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f f' f'' : 实数 -> 实数}
  证明: by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine convexOn_of_deriv2_nonneg hD hf (fun x hx => (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx => (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ 

Depends on / 依赖: convert, convexOn_of_deriv2_nonneg, deriv_eqOn, differentiableOn_congr, differentiableWithinAt, interior, isOpen_interior
-/
lemma convexOn_of_hasDerivWithinAt2_nonneg {D : Set Real} (hD : Convex Real D) {f f' f'' : Real -> Real}
    (hf : ContinuousOn f D) (hf' : forall x in interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : forall x in interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : forall x in interior D, 0 <= f'' x) : ConvexOn Real D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine convexOn_of_deriv2_nonneg hD hf (fun x hx => (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx => (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy => ?_) hx]
exact (hf'' _ hy).congr this by rw [this hy]

/--
lemma `concaveOn_of_hasDerivWithinAt2_nonpos` / 引理 `concaveOn_of_hasDerivWithinAt2_nonpos`

English:
lemma concaveOn_of_hasDerivWithinAt2_nonpos
  statement: {D : Set Real} (hD : Convex Real D) {f f' f'' : Real -> Real}
  proof: by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine concaveOn_of_deriv2_nonpos hD hf (fun x hx => (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx => (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀

中文:
引理 concaveOn_of_hasDerivWithinAt2_nonpos
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f f' f'' : 实数 -> 实数}
  证明: by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine concaveOn_of_deriv2_nonpos hD hf (fun x hx => (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx => (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀

Depends on / 依赖: concaveOn_of_deriv2_nonpos, convert, deriv_eqOn, differentiableOn_congr, differentiableWithinAt, interior, isOpen_interior
-/
lemma concaveOn_of_hasDerivWithinAt2_nonpos {D : Set Real} (hD : Convex Real D) {f f' f'' : Real -> Real}
    (hf : ContinuousOn f D) (hf' : forall x in interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : forall x in interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : forall x in interior D, f'' x <= 0) : ConcaveOn Real D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine concaveOn_of_deriv2_nonpos hD hf (fun x hx => (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx => (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy => ?_) hx]
exact (hf'' _ hy).congr this by rw [this hy]

/--
theorem `strictConvexOn_of_deriv2_pos` / 定理 `strictConvexOn_of_deriv2_pos`

English:
theorem strictConvexOn_of_deriv2_pos
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: ((strictMonoOn_of_deriv_pos hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne').differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConvexOn_of_deriv
    hD hf

中文:
定理 strictConvexOn_of_deriv2_pos
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: ((strictMonoOn_of_deriv_pos hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne').differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConvexOn_of_deriv
    hD hf

Depends on / 依赖: continuousWithinAt, differentiableAt_of_deriv_ne_zero, differentiableWithinAt, differentiableWithinAt.continuousWithinAt, hD.interior, interior, interior_interior, strictConvexOn_of_deriv, strictMonoOn_of_deriv_pos
-/
theorem strictConvexOn_of_deriv2_pos {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf'' : forall x in interior D, 0 < (deriv^[2] f) x) :
    StrictConvexOn Real D f :=
  ((strictMonoOn_of_deriv_pos hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne').differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConvexOn_of_deriv
    hD hf

/--
theorem `strictConcaveOn_of_deriv2_neg` / 定理 `strictConcaveOn_of_deriv2_neg`

English:
theorem strictConcaveOn_of_deriv2_neg
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: ((strictAntiOn_of_deriv_neg hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne).differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConcaveOn_of_deriv
    hD hf

中文:
定理 strictConcaveOn_of_deriv2_neg
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: ((strictAntiOn_of_deriv_neg hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne).differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConcaveOn_of_deriv
    hD hf

Depends on / 依赖: continuousWithinAt, differentiableAt_of_deriv_ne_zero, differentiableWithinAt, differentiableWithinAt.continuousWithinAt, hD.interior, interior, interior_interior, strictAntiOn_of_deriv_neg, strictConcaveOn_of_deriv
-/
theorem strictConcaveOn_of_deriv2_neg {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf'' : forall x in interior D, deriv^[2] f x < 0) :
    StrictConcaveOn Real D f :=
  ((strictAntiOn_of_deriv_neg hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne).differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConcaveOn_of_deriv
    hD hf

/--
theorem `convexOn_of_deriv2_nonneg'` / 定理 `convexOn_of_deriv2_nonneg'`

English:
theorem convexOn_of_deriv2_nonneg'
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: convexOn_of_deriv2_nonneg hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonneg x (interior_subset hx)

中文:
定理 convexOn_of_deriv2_nonneg'
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: convexOn_of_deriv2_nonneg hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonneg x (interior_subset hx)

Depends on / 依赖: _nonneg, continuousOn, convexOn_of_deriv2_nonneg, interior_subset
-/
theorem convexOn_of_deriv2_nonneg' {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf' : DifferentiableOn Real f D) (hf'' : DifferentiableOn Real (deriv f) D)
    (hf''_nonneg : forall x in D, 0 <= (deriv^[2] f) x) : ConvexOn Real D f :=
  convexOn_of_deriv2_nonneg hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonneg x (interior_subset hx)

/--
theorem `concaveOn_of_deriv2_nonpos'` / 定理 `concaveOn_of_deriv2_nonpos'`

English:
theorem concaveOn_of_deriv2_nonpos'
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: concaveOn_of_deriv2_nonpos hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonpos x (interior_subset hx)

中文:
定理 concaveOn_of_deriv2_nonpos'
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: concaveOn_of_deriv2_nonpos hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonpos x (interior_subset hx)

Depends on / 依赖: _nonpos, concaveOn_of_deriv2_nonpos, continuousOn, interior_subset
-/
theorem concaveOn_of_deriv2_nonpos' {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf' : DifferentiableOn Real f D) (hf'' : DifferentiableOn Real (deriv f) D)
    (hf''_nonpos : forall x in D, deriv^[2] f x <= 0) : ConcaveOn Real D f :=
  concaveOn_of_deriv2_nonpos hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonpos x (interior_subset hx)

/--
theorem `strictConvexOn_of_deriv2_pos'` / 定理 `strictConvexOn_of_deriv2_pos'`

English:
theorem strictConvexOn_of_deriv2_pos'
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: strictConvexOn_of_deriv2_pos hD hf fun x hx => hf'' x (interior_subset hx)

中文:
定理 strictConvexOn_of_deriv2_pos'
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: strictConvexOn_of_deriv2_pos hD hf fun x hx => hf'' x (interior_subset hx)

Depends on / 依赖: interior_subset, strictConvexOn_of_deriv2_pos
-/
theorem strictConvexOn_of_deriv2_pos' {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf'' : forall x in D, 0 < (deriv^[2] f) x) : StrictConvexOn Real D f :=
  strictConvexOn_of_deriv2_pos hD hf fun x hx => hf'' x (interior_subset hx)

/--
theorem `strictConcaveOn_of_deriv2_neg'` / 定理 `strictConcaveOn_of_deriv2_neg'`

English:
theorem strictConcaveOn_of_deriv2_neg'
  statement: {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
  proof: strictConcaveOn_of_deriv2_neg hD hf fun x hx => hf'' x (interior_subset hx)

中文:
定理 strictConcaveOn_of_deriv2_neg'
  结论: {D : 集合 实数} (hD : 凸 实数 D) {f : 实数 -> 实数}
  证明: strictConcaveOn_of_deriv2_neg hD hf fun x hx => hf'' x (interior_subset hx)

Depends on / 依赖: interior_subset, strictConcaveOn_of_deriv2_neg
-/
theorem strictConcaveOn_of_deriv2_neg' {D : Set Real} (hD : Convex Real D) {f : Real -> Real}
    (hf : ContinuousOn f D) (hf'' : forall x in D, deriv^[2] f x < 0) : StrictConcaveOn Real D f :=
  strictConcaveOn_of_deriv2_neg hD hf fun x hx => hf'' x (interior_subset hx)

/--
theorem `convexOn_univ_of_deriv2_nonneg` / 定理 `convexOn_univ_of_deriv2_nonneg`

English:
theorem convexOn_univ_of_deriv2_nonneg
  statement: {f : Real -> Real} (hf' : Differentiable Real f)
  proof: convexOn_of_deriv2_nonneg' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonneg x

中文:
定理 convexOn_univ_of_deriv2_nonneg
  结论: {f : 实数 -> 实数} (hf' : 可微 实数 f)
  证明: convexOn_of_deriv2_nonneg' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonneg x

Depends on / 依赖: _nonneg, convexOn_of_deriv2_nonneg, convex_univ, differentiableOn
-/
theorem convexOn_univ_of_deriv2_nonneg {f : Real -> Real} (hf' : Differentiable Real f)
    (hf'' : Differentiable Real (deriv f)) (hf''_nonneg : forall x, 0 <= (deriv^[2] f) x) :
    ConvexOn Real univ f :=
  convexOn_of_deriv2_nonneg' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonneg x

/--
theorem `concaveOn_univ_of_deriv2_nonpos` / 定理 `concaveOn_univ_of_deriv2_nonpos`

English:
theorem concaveOn_univ_of_deriv2_nonpos
  statement: {f : Real -> Real} (hf' : Differentiable Real f)
  proof: concaveOn_of_deriv2_nonpos' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonpos x

中文:
定理 concaveOn_univ_of_deriv2_nonpos
  结论: {f : 实数 -> 实数} (hf' : 可微 实数 f)
  证明: concaveOn_of_deriv2_nonpos' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonpos x

Depends on / 依赖: _nonpos, concaveOn_of_deriv2_nonpos, convex_univ, differentiableOn
-/
theorem concaveOn_univ_of_deriv2_nonpos {f : Real -> Real} (hf' : Differentiable Real f)
    (hf'' : Differentiable Real (deriv f)) (hf''_nonpos : forall x, deriv^[2] f x <= 0) :
    ConcaveOn Real univ f :=
  concaveOn_of_deriv2_nonpos' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonpos x

/--
theorem `strictConvexOn_univ_of_deriv2_pos` / 定理 `strictConvexOn_univ_of_deriv2_pos`

English:
theorem strictConvexOn_univ_of_deriv2_pos
  statement: {f : Real -> Real} (hf : Continuous f)
  proof: strictConvexOn_of_deriv2_pos' convex_univ hf.continuousOn fun x _ => hf'' x

中文:
定理 strictConvexOn_univ_of_deriv2_pos
  结论: {f : 实数 -> 实数} (hf : 连续 f)
  证明: strictConvexOn_of_deriv2_pos' convex_univ hf.continuousOn fun x _ => hf'' x

Depends on / 依赖: continuousOn, convex_univ, hf.continuousOn, strictConvexOn_of_deriv2_pos
-/
theorem strictConvexOn_univ_of_deriv2_pos {f : Real -> Real} (hf : Continuous f)
    (hf'' : forall x, 0 < (deriv^[2] f) x) : StrictConvexOn Real univ f :=
  strictConvexOn_of_deriv2_pos' convex_univ hf.continuousOn fun x _ => hf'' x

/--
theorem `strictConcaveOn_univ_of_deriv2_neg` / 定理 `strictConcaveOn_univ_of_deriv2_neg`

English:
theorem strictConcaveOn_univ_of_deriv2_neg
  statement: {f : Real -> Real} (hf : Continuous f)
  proof: strictConcaveOn_of_deriv2_neg' convex_univ hf.continuousOn fun x _ => hf'' x

中文:
定理 strictConcaveOn_univ_of_deriv2_neg
  结论: {f : 实数 -> 实数} (hf : 连续 f)
  证明: strictConcaveOn_of_deriv2_neg' convex_univ hf.continuousOn fun x _ => hf'' x

Depends on / 依赖: continuousOn, convex_univ, hf.continuousOn, strictConcaveOn_of_deriv2_neg
-/
theorem strictConcaveOn_univ_of_deriv2_neg {f : Real -> Real} (hf : Continuous f)
    (hf'' : forall x, deriv^[2] f x < 0) : StrictConcaveOn Real univ f :=
  strictConcaveOn_of_deriv2_neg' convex_univ hf.continuousOn fun x _ => hf'' x

/-!
## Convexity of `f` implies monotonicity of `f'`

In this section we prove inequalities relating derivatives of convex functions to slopes of secant
lines, and deduce that if `f` is convex then its derivative is monotone (and similarly for strict
convexity / strict monotonicity).
-/

section slope

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {s : Set 𝕜} {f : 𝕜 -> 𝕜} {x : 𝕜}

/--
lemma `ConvexOn.slope_mono` / 引理 `ConvexOn.slope_mono`

English:
lemma ConvexOn.slope_mono
  given: (hfc : ConvexOn 𝕜 s f) (hx : x in s)
  statement: MonotoneOn (slope f x) (s \ {x})
  proof: (slope_fun_def_field f _).symm ▸ fun _ hy _ hz hz' => hfc.secant_mono hx (mem_of_mem_sdiff hy)
    (mem_of_mem_sdiff hz) (notMem_of_mem_sdiff hy :) (notMem_of_mem_sdiff hz :) hz'

中文:
引理 ConvexOn.slope_mono
  条件: (hfc : ConvexOn 𝕜 s f) (hx : x in s)
  结论: MonotoneOn (slope f x) (s \ {x})
  证明: (slope_fun_def_field f _).symm ▸ fun _ hy _ hz hz' => hfc.secant_mono hx (mem_of_mem_sdiff hy)
    (mem_of_mem_sdiff hz) (notMem_of_mem_sdiff hy :) (notMem_of_mem_sdiff hz :) hz'

Depends on / 依赖: hfc.secant_mono, mem_of_mem_sdiff, notMem_of_mem_sdiff, secant_mono, slope_fun_def_field
-/
lemma ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x in s) : MonotoneOn (slope f x) (s \ {x}) :=
  (slope_fun_def_field f _).symm ▸ fun _ hy _ hz hz' => hfc.secant_mono hx (mem_of_mem_sdiff hy)
    (mem_of_mem_sdiff hz) (notMem_of_mem_sdiff hy :) (notMem_of_mem_sdiff hz :) hz'

/--
lemma `ConvexOn.monotoneOn_slope_gt` / 引理 `ConvexOn.monotoneOn_slope_gt`

English:
lemma ConvexOn.monotoneOn_slope_gt
  given: (hfc : ConvexOn 𝕜 s f) (hxs : x in s)
  proof: (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne'⟩

中文:
引理 ConvexOn.monotoneOn_slope_gt
  条件: (hfc : ConvexOn 𝕜 s f) (hxs : x in s)
  证明: (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne'⟩

Depends on / 依赖: h2.ne, hfc.slope_mono, slope_mono
-/
lemma ConvexOn.monotoneOn_slope_gt (hfc : ConvexOn 𝕜 s f) (hxs : x in s) :
    MonotoneOn (slope f x) {y in s | x < y} :=
  (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne'⟩

/--
lemma `ConvexOn.monotoneOn_slope_lt` / 引理 `ConvexOn.monotoneOn_slope_lt`

English:
lemma ConvexOn.monotoneOn_slope_lt
  given: (hfc : ConvexOn 𝕜 s f) (hxs : x in s)
  proof: (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne⟩

中文:
引理 ConvexOn.monotoneOn_slope_lt
  条件: (hfc : ConvexOn 𝕜 s f) (hxs : x in s)
  证明: (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne⟩

Depends on / 依赖: h2.ne, hfc.slope_mono, slope_mono
-/
lemma ConvexOn.monotoneOn_slope_lt (hfc : ConvexOn 𝕜 s f) (hxs : x in s) :
    MonotoneOn (slope f x) {y in s | y < x} :=
  (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne⟩

/--
lemma `ConcaveOn.slope_anti` / 引理 `ConcaveOn.slope_anti`

English:
lemma ConcaveOn.slope_anti
  given: (hfc : ConcaveOn 𝕜 s f) (hx : x in s)
  proof: by
  rw [← neg_neg f]; rw [slope_neg_fun]
  exact (ConvexOn.slope_mono hfc.neg hx).neg

中文:
引理 ConcaveOn.slope_anti
  条件: (hfc : ConcaveOn 𝕜 s f) (hx : x in s)
  证明: by
  rw [← neg_neg f]; rw [slope_neg_fun]
  exact (ConvexOn.slope_mono hfc.neg hx).neg

Depends on / 依赖: ConvexOn, ConvexOn.slope_mono, hfc.neg, neg_neg, slope_mono, slope_neg_fun
-/
lemma ConcaveOn.slope_anti (hfc : ConcaveOn 𝕜 s f) (hx : x in s) :
    AntitoneOn (slope f x) (s \ {x}) := by
  rw [← neg_neg f]; rw [slope_neg_fun]
  exact (ConvexOn.slope_mono hfc.neg hx).neg

/--
lemma `ConcaveOn.antitoneOn_slope_gt` / 引理 `ConcaveOn.antitoneOn_slope_gt`

English:
lemma ConcaveOn.antitoneOn_slope_gt
  given: (hfc : ConcaveOn 𝕜 s f) (hxs : x in s)
  proof: (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne'⟩

中文:
引理 ConcaveOn.antitoneOn_slope_gt
  条件: (hfc : ConcaveOn 𝕜 s f) (hxs : x in s)
  证明: (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne'⟩

Depends on / 依赖: h2.ne, hfc.slope_anti, slope_anti
-/
lemma ConcaveOn.antitoneOn_slope_gt (hfc : ConcaveOn 𝕜 s f) (hxs : x in s) :
    AntitoneOn (slope f x) {y in s | x < y} :=
  (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne'⟩

/--
lemma `ConcaveOn.antitoneOn_slope_lt` / 引理 `ConcaveOn.antitoneOn_slope_lt`

English:
lemma ConcaveOn.antitoneOn_slope_lt
  given: (hfc : ConcaveOn 𝕜 s f) (hxs : x in s)
  proof: (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne⟩

中文:
引理 ConcaveOn.antitoneOn_slope_lt
  条件: (hfc : ConcaveOn 𝕜 s f) (hxs : x in s)
  证明: (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne⟩

Depends on / 依赖: h2.ne, hfc.slope_anti, slope_anti
-/
lemma ConcaveOn.antitoneOn_slope_lt (hfc : ConcaveOn 𝕜 s f) (hxs : x in s) :
    AntitoneOn (slope f x) {y in s | y < x} :=
  (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ => ⟨h1, h2.ne⟩

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/--
lemma `bddBelow_slope_lt_of_mem_interior` / 引理 `bddBelow_slope_lt_of_mem_interior`

English:
lemma bddBelow_slope_lt_of_mem_interior
  given: (hfc : ConvexOn 𝕜 s f) (hxs : x in interior s)
  proof: by
  obtain ⟨y, hyx, hys⟩ : exists y, y < x ∧ y in s :=
    Eventually.exists_lt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddBelow_iff_subset_Ici.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ => ?_⟩
  simp_rw [mem_Ici, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hyx.trans hz.2).le
  · sim

中文:
引理 bddBelow_slope_lt_of_mem_interior
  条件: (hfc : ConvexOn 𝕜 s f) (hxs : x in interior s)
  证明: by
  obtain ⟨y, hyx, hys⟩ : exists y, y < x ∧ y in s :=
    Eventually.exists_lt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddBelow_iff_subset_Ici.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ => ?_⟩
  simp_rw [mem_Ici, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hyx.trans hz.2).le
  · sim

Depends on / 依赖: Eventually, Eventually.exists_lt, bddBelow_iff_subset_Ici, bddBelow_iff_subset_Ici.mpr, exists_lt, hfc.slope_mono, hyx.ne, hyx.trans, interior_subset, mem_Ici, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.mp, simp_rw, slope_mono
-/
lemma bddBelow_slope_lt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x in interior s) :
    BddBelow (slope f x '' {y in s | x < y}) := by
  obtain ⟨y, hyx, hys⟩ : exists y, y < x ∧ y in s :=
    Eventually.exists_lt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddBelow_iff_subset_Ici.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ => ?_⟩
  simp_rw [mem_Ici, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hyx.trans hz.2).le
  · simp [hys, hyx.ne]
  · simp [hz.2.ne', hz.1]

/--
lemma `bddAbove_slope_gt_of_mem_interior` / 引理 `bddAbove_slope_gt_of_mem_interior`

English:
lemma bddAbove_slope_gt_of_mem_interior
  given: (hfc : ConvexOn 𝕜 s f) (hxs : x in interior s)
  proof: by
  obtain ⟨y, hyx, hys⟩ : exists y, x < y ∧ y in s :=
    Eventually.exists_gt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddAbove_iff_subset_Iic.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ => ?_⟩
  simp_rw [mem_Iic, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hz.2.trans hyx).le
  · sim

中文:
引理 bddAbove_slope_gt_of_mem_interior
  条件: (hfc : ConvexOn 𝕜 s f) (hxs : x in interior s)
  证明: by
  obtain ⟨y, hyx, hys⟩ : exists y, x < y ∧ y in s :=
    Eventually.exists_gt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddAbove_iff_subset_Iic.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ => ?_⟩
  simp_rw [mem_Iic, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hz.2.trans hyx).le
  · sim

Depends on / 依赖: Eventually, Eventually.exists_gt, bddAbove_iff_subset_Iic, bddAbove_iff_subset_Iic.mpr, exists_gt, hfc.slope_mono, hyx.ne, interior_subset, mem_Iic, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.mp, simp_rw, slope_mono
-/
lemma bddAbove_slope_gt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x in interior s) :
    BddAbove (slope f x '' {y in s | y < x}) := by
  obtain ⟨y, hyx, hys⟩ : exists y, x < y ∧ y in s :=
    Eventually.exists_gt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddAbove_iff_subset_Iic.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ => ?_⟩
  simp_rw [mem_Iic, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hz.2.trans hyx).le
  · simp [hz.2.ne, hz.1]
  · simp [hys, hyx.ne']

end slope

namespace ConvexOn

variable {S : Set Real} {f : Real -> Real} {x y f' : Real}

section Interior


/--
lemma `hasDerivWithinAt_sInf_slope_of_mem_interior` / 引理 `hasDerivWithinAt_sInf_slope_of_mem_interior`

English:
lemma hasDerivWithinAt_sInf_slope_of_mem_interior
  given: (hfc : ConvexOn Real S f) (hxs : x in interior S)
  proof: by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h : Ioo x b subseteq {y |

中文:
引理 hasDerivWithinAt_sInf_slope_of_mem_interior
  条件: (hfc : ConvexOn 实数 S f) (hxs : x in interior S)
  证明: by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h : Ioo x b subseteq {y |

Depends on / 依赖: Tendsto, h_Ioo, hasDerivWithinAt_iff_tendsto_slope, lt_self_iff_false, mem_Ioi, mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset, monotoneOn_slope_gt, not_false_eq_true, sdiff_singleton_eq_self, simp_rw, subseteq, tendsto_nhdsWit
-/
lemma hasDerivWithinAt_sInf_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) :
    HasDerivWithinAt f (sInf (slope f x '' {y in S | x < y})) (Ioi x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h : Ioo x b subseteq {y | y in S ∧ x < y} := fun z hz => ⟨habs ⟨hxab.1.trans hz.1, hz.2⟩, hz.1⟩
  have h_Ioo : Tendsto (slope f x) (𝓝[>] x) (𝓝 (sInf (slope f x '' Ioo x b))) :=
    ((monotoneOn_slope_gt hfc (habs hxab)).mono h).tendsto_nhdsWithin_Ioo_right
      (by simpa using hxab.2) ((bddBelow_slope_lt_of_mem_interior hfc hxs).mono (image_mono h))
  suffices sInf (slope f x '' Ioo x b) = sInf (slope f x '' {y in S | x < y}) by rwa [← this]
  apply (monotoneOn_slope_gt hfc (habs hxab)).csInf_eq_of_subset_of_forall_exists_le
    (bddBelow_slope_lt_of_mem_interior hfc hxs) h ?_
  rintro y ⟨hyS, hxy⟩
  obtain ⟨z, hxz, hzy⟩ := exists_between (lt_min hxab.2 hxy)
  exact ⟨z, ⟨hxz, hzy.trans_le (min_le_left _ _)⟩, hzy.le.trans (min_le_right _ _)⟩

/--
lemma `hasDerivWithinAt_sSup_slope_of_mem_interior` / 引理 `hasDerivWithinAt_sSup_slope_of_mem_interior`

English:
lemma hasDerivWithinAt_sSup_slope_of_mem_interior
  given: (hfc : ConvexOn Real S f) (hxs : x in interior S)
  proof: by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h : Ioo a x subseteq {y |

中文:
引理 hasDerivWithinAt_sSup_slope_of_mem_interior
  条件: (hfc : ConvexOn 实数 S f) (hxs : x in interior S)
  证明: by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h : Ioo a x subseteq {y |

Depends on / 依赖: Tendsto, h_Ioo, hasDerivWithinAt_iff_tendsto_slope, lt_self_iff_false, mem_Iio, mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset, monotoneOn_slope_lt, not_false_eq_true, sdiff_singleton_eq_self, simp_rw, subseteq, tendsto_nhdsWit
-/
lemma hasDerivWithinAt_sSup_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) :
    HasDerivWithinAt f (sSup (slope f x '' {y in S | y < x})) (Iio x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h : Ioo a x subseteq {y | y in S ∧ y < x} := fun z hz => ⟨habs ⟨hz.1, hz.2.trans hxab.2⟩, hz.2⟩
  have h_Ioo : Tendsto (slope f x) (𝓝[<] x) (𝓝 (sSup (slope f x '' Ioo a x))) :=
    ((monotoneOn_slope_lt hfc (habs hxab)).mono h).tendsto_nhdsWithin_Ioo_left
      (by simpa using hxab.1) ((bddAbove_slope_gt_of_mem_interior hfc hxs).mono (image_mono h))
  suffices sSup (slope f x '' Ioo a x) = sSup (slope f x '' {y in S | y < x}) by rwa [← this]
  apply (monotoneOn_slope_lt hfc (habs hxab)).csSup_eq_of_subset_of_forall_exists_le
    (bddAbove_slope_gt_of_mem_interior hfc hxs) h ?_
  rintro y ⟨hyS, hyx⟩
  obtain ⟨z, hyz, hzx⟩ := exists_between (max_lt hxab.1 hyx)
  exact ⟨z, ⟨(le_max_left _ _).trans_lt hyz, hzx⟩, (le_max_right _ _).trans hyz.le⟩

/--
lemma `differentiableWithinAt_Ioi_of_mem_interior` / 引理 `differentiableWithinAt_Ioi_of_mem_interior`

English:
lemma differentiableWithinAt_Ioi_of_mem_interior
  given: (hfc : ConvexOn Real S f) (hxs : x in interior S)
  proof: (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).differentiableWithinAt

中文:
引理 differentiableWithinAt_Ioi_of_mem_interior
  条件: (hfc : ConvexOn 实数 S f) (hxs : x in interior S)
  证明: (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, hasDerivWithinAt_sInf_slope_of_mem_interior, hfc.hasDerivWithinAt_sInf_slope_of_mem_interior
-/
lemma differentiableWithinAt_Ioi_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) :
    DifferentiableWithinAt Real f (Ioi x) x :=
  (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).differentiableWithinAt

/--
lemma `differentiableWithinAt_Iio_of_mem_interior` / 引理 `differentiableWithinAt_Iio_of_mem_interior`

English:
lemma differentiableWithinAt_Iio_of_mem_interior
  given: (hfc : ConvexOn Real S f) (hxs : x in interior S)
  proof: (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).differentiableWithinAt

中文:
引理 differentiableWithinAt_Iio_of_mem_interior
  条件: (hfc : ConvexOn 实数 S f) (hxs : x in interior S)
  证明: (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, hasDerivWithinAt_sSup_slope_of_mem_interior, hfc.hasDerivWithinAt_sSup_slope_of_mem_interior
-/
lemma differentiableWithinAt_Iio_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) :
    DifferentiableWithinAt Real f (Iio x) x :=
  (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).differentiableWithinAt

/--
lemma `hasDerivWithinAt_rightDeriv_of_mem_interior` / 引理 `hasDerivWithinAt_rightDeriv_of_mem_interior`

English:
lemma hasDerivWithinAt_rightDeriv_of_mem_interior
  given: (hfc : ConvexOn Real S f) (hxs : x in interior S)
  proof: (hfc.differentiableWithinAt_Ioi_of_mem_interior hxs).hasDerivWithinAt

中文:
引理 hasDerivWithinAt_rightDeriv_of_mem_interior
  条件: (hfc : ConvexOn 实数 S f) (hxs : x in interior S)
  证明: (hfc.differentiableWithinAt_Ioi_of_mem_interior hxs).hasDerivWithinAt

Depends on / 依赖: differentiableWithinAt_Ioi_of_mem_interior, hasDerivWithinAt, hfc.differentiableWithinAt_Ioi_of_mem_interior
-/
lemma hasDerivWithinAt_rightDeriv_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) :
    HasDerivWithinAt f (derivWithin f (Ioi x) x) (Ioi x) x :=
  (hfc.differentiableWithinAt_Ioi_of_mem_interior hxs).hasDerivWithinAt

/--
lemma `hasDerivWithinAt_leftDeriv_of_mem_interior` / 引理 `hasDerivWithinAt_leftDeriv_of_mem_interior`

English:
lemma hasDerivWithinAt_leftDeriv_of_mem_interior
  given: (hfc : ConvexOn Real S f) (hxs : x in interior S)
  proof: (hfc.differentiableWithinAt_Iio_of_mem_interior hxs).hasDerivWithinAt

中文:
引理 hasDerivWithinAt_leftDeriv_of_mem_interior
  条件: (hfc : ConvexOn 实数 S f) (hxs : x in interior S)
  证明: (hfc.differentiableWithinAt_Iio_of_mem_interior hxs).hasDerivWithinAt

Depends on / 依赖: differentiableWithinAt_Iio_of_mem_interior, hasDerivWithinAt, hfc.differentiableWithinAt_Iio_of_mem_interior
-/
lemma hasDerivWithinAt_leftDeriv_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) :
    HasDerivWithinAt f (derivWithin f (Iio x) x) (Iio x) x :=
  (hfc.differentiableWithinAt_Iio_of_mem_interior hxs).hasDerivWithinAt

/--
lemma `rightDeriv_eq_sInf_slope_of_mem_interior` / 引理 `rightDeriv_eq_sInf_slope_of_mem_interior`

English:
lemma rightDeriv_eq_sInf_slope_of_mem_interior
  given: (hfc : ConvexOn Real S f) (hxs : x in interior S)
  proof: (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Ioi x)

中文:
引理 rightDeriv_eq_sInf_slope_of_mem_interior
  条件: (hfc : ConvexOn 实数 S f) (hxs : x in interior S)
  证明: (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Ioi x)

Depends on / 依赖: derivWithin, hasDerivWithinAt_sInf_slope_of_mem_interior, hfc.hasDerivWithinAt_sInf_slope_of_mem_interior, uniqueDiffWithinAt_Ioi
-/
lemma rightDeriv_eq_sInf_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) :
    derivWithin f (Ioi x) x = sInf (slope f x '' {y | y in S ∧ x < y}) :=
  (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Ioi x)

/--
lemma `leftDeriv_eq_sSup_slope_of_mem_interior` / 引理 `leftDeriv_eq_sSup_slope_of_mem_interior`

English:
lemma leftDeriv_eq_sSup_slope_of_mem_interior
  given: (hfc : ConvexOn Real S f) (hxs : x in interior S)
  proof: (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Iio x)

中文:
引理 leftDeriv_eq_sSup_slope_of_mem_interior
  条件: (hfc : ConvexOn 实数 S f) (hxs : x in interior S)
  证明: (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Iio x)

Depends on / 依赖: derivWithin, hasDerivWithinAt_sSup_slope_of_mem_interior, hfc.hasDerivWithinAt_sSup_slope_of_mem_interior, uniqueDiffWithinAt_Iio
-/
lemma leftDeriv_eq_sSup_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) :
    derivWithin f (Iio x) x = sSup (slope f x '' {y | y in S ∧ y < x}) :=
  (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Iio x)

/--
lemma `monotoneOn_rightDeriv` / 引理 `monotoneOn_rightDeriv`

English:
lemma monotoneOn_rightDeriv
  given: (hfc : ConvexOn Real S f)
  proof: by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.rightDeriv_eq_sInf_slope_of_mem_interior hys]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_lt_of_mem_interior hfc hxs)
    ⟨y, by simp only 

中文:
引理 monotoneOn_rightDeriv
  条件: (hfc : ConvexOn 实数 S f)
  证明: by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.rightDeriv_eq_sInf_slope_of_mem_interior hys]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_lt_of_mem_interior hfc hxs)
    ⟨y, by simp only 

Depends on / 依赖: and_true, bddBelow_slope_lt_of_mem_interior, csInf_le_of_le, eq_or_lt_of_le, hfc.rightDeriv_eq_sInf_slope_of_mem_interior, image_n, interior_subset, le_csInf, mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset, mem_ofPred_eq, rightDeriv_eq_sInf_slope_of_mem_interior, simp_rw
-/
lemma monotoneOn_rightDeriv (hfc : ConvexOn Real S f) :
    MonotoneOn (fun x => derivWithin f (Ioi x) x) (interior S) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.rightDeriv_eq_sInf_slope_of_mem_interior hys]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_lt_of_mem_interior hfc hxs)
    ⟨y, by simp only [mem_ofPred_eq, hxy, and_true]; exact interior_subset hys⟩
    (le_csInf ?_ ?_)
  · have hys' := hys
    rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hys'
    obtain ⟨a, b, hxab, habs⟩ := hys'
    rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.2
    exact ⟨z, habs ⟨hxab.1.trans hxz, hzb⟩, hxz⟩
  · rintro _ ⟨z, ⟨hzs, hyz : y < z⟩, rfl⟩
    rw [slope_comm]
    exact slope_mono hfc (interior_subset hys) ⟨interior_subset hxs, hxy.ne⟩ ⟨hzs, hyz.ne'⟩
      (hxy.trans hyz).le

/--
lemma `monotoneOn_leftDeriv` / 引理 `monotoneOn_leftDeriv`

English:
lemma monotoneOn_leftDeriv
  given: (hfc : ConvexOn Real S f)
  proof: by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hys]
  refine le_csSup_of_le (b := slope f x y) (bddAbove_slope_gt_of_mem_interior hfc hys)
    ⟨x, by simp only [s

中文:
引理 monotoneOn_leftDeriv
  条件: (hfc : ConvexOn 实数 S f)
  证明: by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hys]
  refine le_csSup_of_le (b := slope f x y) (bddAbove_slope_gt_of_mem_interior hfc hys)
    ⟨x, by simp only [s

Depends on / 依赖: and_true, bddAbove_slope_gt_of_mem_interior, csSup_le, eq_or_lt_of_le, hfc.leftDeriv_eq_sSup_slope_of_mem_interior, interior_subset, le_csSup_of_le, leftDeriv_eq_sSup_slope_of_mem_interior, mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset, mem_ofPred_eq, simp_rw, slope_comm
-/
lemma monotoneOn_leftDeriv (hfc : ConvexOn Real S f) :
    MonotoneOn (fun x => derivWithin f (Iio x) x) (interior S) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hys]
  refine le_csSup_of_le (b := slope f x y) (bddAbove_slope_gt_of_mem_interior hfc hys)
    ⟨x, by simp only [slope_comm, mem_ofPred_eq, hxy, and_true]; exact interior_subset hxs⟩
    (csSup_le ?_ ?_)
  · have hxs' := hxs
    rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
    obtain ⟨a, b, hxab, habs⟩ := hxs'
    rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.1
    exact ⟨z, habs ⟨hxz, hzb.trans hxab.2⟩, hzb⟩
  · rintro _ ⟨z, ⟨hzs, hyz : z < x⟩, rfl⟩
    exact slope_mono hfc (interior_subset hxs) ⟨hzs, hyz.ne⟩ ⟨interior_subset hys, hxy.ne'⟩
      (hyz.trans hxy).le

/--
lemma `leftDeriv_le_rightDeriv_of_mem_interior` / 引理 `leftDeriv_le_rightDeriv_of_mem_interior`

English:
lemma leftDeriv_le_rightDeriv_of_mem_interior
  given: (hfc : ConvexOn Real S f) (hxs : x in interior S)
  proof: by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs]; rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs]
  refine csSup_le ?_ ?_
  · rw [image_nonempty]
    ob

中文:
引理 leftDeriv_le_rightDeriv_of_mem_interior
  条件: (hfc : ConvexOn 实数 S f) (hxs : x in interior S)
  证明: by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs]; rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs]
  refine csSup_le ?_ ?_
  · rw [image_nonempty]
    ob

Depends on / 依赖: csSup_le, exists_between, hfc.leftDeriv_eq_sSup_slope_of_mem_interior, hfc.rightDeriv_eq_sInf_slope_of_mem_interior, hzx.trans, image_nonempty, le_csInf, leftDeriv_eq_sSup_slope_of_mem_interior, mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset, rightDeriv_eq_sInf_slope_of_mem_interior
-/
lemma leftDeriv_le_rightDeriv_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) :
    derivWithin f (Iio x) x <= derivWithin f (Ioi x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs]; rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs]
  refine csSup_le ?_ ?_
  · rw [image_nonempty]
    obtain ⟨z, haz, hzx⟩ := exists_between hxab.1
    exact ⟨z, habs ⟨haz, hzx.trans hxab.2⟩, hzx⟩
  rintro _ ⟨z, ⟨hzs, hzx⟩, rfl⟩
  refine le_csInf ?_ ?_
  · rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.2
    exact ⟨z, habs ⟨hxab.1.trans hxz, hzb⟩, hxz⟩
  rintro _ ⟨y, ⟨hys, hxy⟩, rfl⟩
  exact slope_mono hfc (interior_subset hxs) ⟨hzs, hzx.ne⟩ ⟨hys, hxy.ne'⟩ (hzx.trans hxy).le

end Interior

section left
/-!
### Convex functions, derivative at left endpoint of secant
-/

/--
lemma `le_slope_of_hasDerivWithinAt_Ioi` / 引理 `le_slope_of_hasDerivWithinAt_Ioi`

English:
lemma le_slope_of_hasDerivWithinAt_Ioi
  statement: (hfc : ConvexOn Real S f)
  proof: by
apply le_of_tendsto (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_def_field]
  filter_upwards [eventually_lt_nhds hxy] with t ht (ht' : x < t)
  refine hfc.secant_mono hx (?_ : t in S) hy ht'.ne' hxy.ne' ht.le
  exact hfc.1.ordConnected.o

中文:
引理 le_slope_of_hasDerivWithinAt_Ioi
  结论: (hfc : ConvexOn 实数 S f)
  证明: by
apply le_of_tendsto (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_def_field]
  filter_upwards [eventually_lt_nhds hxy] with t ht (ht' : x < t)
  refine hfc.secant_mono hx (?_ : t in S) hy ht'.ne' hxy.ne' ht.le
  exact hfc.1.ordConnected.o

Depends on / 依赖: eventually_lt_nhds, eventually_nhdsWithin_iff, filter_upwards, hasDerivWithinAt_iff_tendsto_slope, hfc.secant_mono, ht.le, hxy.ne, le_of_tendsto, ordConnected, ordConnected.out, secant_mono, self_notMem_Ioi, simp_rw, slope_def_field
-/
lemma le_slope_of_hasDerivWithinAt_Ioi (hfc : ConvexOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' <= slope f x y := by
apply le_of_tendsto (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_def_field]
  filter_upwards [eventually_lt_nhds hxy] with t ht (ht' : x < t)
  refine hfc.secant_mono hx (?_ : t in S) hy ht'.ne' hxy.ne' ht.le
  exact hfc.1.ordConnected.out hx hy ⟨ht'.le, ht.le⟩

/--
lemma `rightDeriv_le_slope` / 引理 `rightDeriv_le_slope`

English:
lemma rightDeriv_le_slope
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: le_slope_of_hasDerivWithinAt_Ioi hfc hx hy hxy hfd.hasDerivWithinAt

中文:
引理 rightDeriv_le_slope
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: le_slope_of_hasDerivWithinAt_Ioi hfc hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfd.hasDerivWithinAt, le_slope_of_hasDerivWithinAt_Ioi
-/
lemma rightDeriv_le_slope (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f (Ioi x) x) :
    derivWithin f (Ioi x) x <= slope f x y :=
  le_slope_of_hasDerivWithinAt_Ioi hfc hx hy hxy hfd.hasDerivWithinAt

/--
lemma `rightDeriv_le_slope_of_mem_interior` / 引理 `rightDeriv_le_slope_of_mem_interior`

English:
lemma rightDeriv_le_slope_of_mem_interior
  statement: (hfc : ConvexOn Real S f)
  proof: rightDeriv_le_slope hfc (interior_subset hxs) hys hxy
    (differentiableWithinAt_Ioi_of_mem_interior hfc hxs)

中文:
引理 rightDeriv_le_slope_of_mem_interior
  结论: (hfc : ConvexOn 实数 S f)
  证明: rightDeriv_le_slope hfc (interior_subset hxs) hys hxy
    (differentiableWithinAt_Ioi_of_mem_interior hfc hxs)

Depends on / 依赖: differentiableWithinAt_Ioi_of_mem_interior, interior_subset, rightDeriv_le_slope
-/
lemma rightDeriv_le_slope_of_mem_interior (hfc : ConvexOn Real S f)
    {y : Real} (hxs : x in interior S) (hys : y in S) (hxy : x < y) :
    derivWithin f (Ioi x) x <= slope f x y :=
  rightDeriv_le_slope hfc (interior_subset hxs) hys hxy
    (differentiableWithinAt_Ioi_of_mem_interior hfc hxs)

/--
lemma `le_slope_of_hasDerivWithinAt` / 引理 `le_slope_of_hasDerivWithinAt`

English:
lemma le_slope_of_hasDerivWithinAt
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsGT hx hy hxy

中文:
引理 le_slope_of_hasDerivWithinAt
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsGT hx hy hxy

Depends on / 依赖: hfc.le_slope_of_hasDerivWithinAt_Ioi, le_slope_of_hasDerivWithinAt_Ioi, mem_nhdsGT, mono_of_mem_nhdsWithin, ordConnected, ordConnected.mem_nhdsGT
-/
lemma le_slope_of_hasDerivWithinAt (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S x) :
    f' <= slope f x y :=
hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsGT hx hy hxy

/--
lemma `derivWithin_le_slope` / 引理 `derivWithin_le_slope`

English:
lemma derivWithin_le_slope
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: le_slope_of_hasDerivWithinAt hfc hx hy hxy hfd.hasDerivWithinAt

中文:
引理 derivWithin_le_slope
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: le_slope_of_hasDerivWithinAt hfc hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfd.hasDerivWithinAt, le_slope_of_hasDerivWithinAt
-/
lemma derivWithin_le_slope (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f S x) :
    derivWithin f S x <= slope f x y :=
  le_slope_of_hasDerivWithinAt hfc hx hy hxy hfd.hasDerivWithinAt

/--
lemma `le_slope_of_hasDerivAt` / 引理 `le_slope_of_hasDerivAt`

English:
lemma le_slope_of_hasDerivAt
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy ha.hasDerivWithinAt

中文:
引理 le_slope_of_hasDerivAt
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy ha.hasDerivWithinAt

Depends on / 依赖: ha.hasDerivWithinAt, hasDerivWithinAt, hfc.le_slope_of_hasDerivWithinAt_Ioi, le_slope_of_hasDerivWithinAt_Ioi
-/
lemma le_slope_of_hasDerivAt (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (ha : HasDerivAt f f' x) :
    f' <= slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy ha.hasDerivWithinAt

/--
lemma `deriv_le_slope` / 引理 `deriv_le_slope`

English:
lemma deriv_le_slope
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: le_slope_of_hasDerivAt hfc hx hy hxy hfd.hasDerivAt

中文:
引理 deriv_le_slope
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: le_slope_of_hasDerivAt hfc hx hy hxy hfd.hasDerivAt

Depends on / 依赖: hasDerivAt, hfd.hasDerivAt, le_slope_of_hasDerivAt
-/
lemma deriv_le_slope (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableAt Real f x) :
    deriv f x <= slope f x y :=
  le_slope_of_hasDerivAt hfc hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Convex functions, derivative at right endpoint of secant
-/

/--
lemma `slope_le_of_hasDerivWithinAt_Iio` / 引理 `slope_le_of_hasDerivWithinAt_Iio`

English:
lemma slope_le_of_hasDerivWithinAt_Iio
  statement: (hfc : ConvexOn Real S f)
  proof: by
apply ge_of_tendsto (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_comm f x y, slope_def_field]
  filter_upwards [eventually_gt_nhds hxy] with t ht (ht' : t < y)
  refine hfc.secant_mono hy hx (?_ : t in S) hxy.ne ht'.ne ht.le
  exact hfc.

中文:
引理 slope_le_of_hasDerivWithinAt_Iio
  结论: (hfc : ConvexOn 实数 S f)
  证明: by
apply ge_of_tendsto (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_comm f x y, slope_def_field]
  filter_upwards [eventually_gt_nhds hxy] with t ht (ht' : t < y)
  refine hfc.secant_mono hy hx (?_ : t in S) hxy.ne ht'.ne ht.le
  exact hfc.

Depends on / 依赖: eventually_gt_nhds, eventually_nhdsWithin_iff, filter_upwards, ge_of_tendsto, hasDerivWithinAt_iff_tendsto_slope, hfc.secant_mono, ht.le, hxy.ne, ordConnected, ordConnected.out, secant_mono, self_notMem_Iio, simp_rw, slope_comm, slope_def_field
-/
lemma slope_le_of_hasDerivWithinAt_Iio (hfc : ConvexOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    slope f x y <= f' := by
apply ge_of_tendsto (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_comm f x y, slope_def_field]
  filter_upwards [eventually_gt_nhds hxy] with t ht (ht' : t < y)
  refine hfc.secant_mono hy hx (?_ : t in S) hxy.ne ht'.ne ht.le
  exact hfc.1.ordConnected.out hx hy ⟨ht.le, ht'.le⟩

/--
lemma `slope_le_leftDeriv` / 引理 `slope_le_leftDeriv`

English:
lemma slope_le_leftDeriv
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

中文:
引理 slope_le_leftDeriv
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_le_of_hasDerivWithinAt_Iio, hfd.hasDerivWithinAt, slope_le_of_hasDerivWithinAt_Iio
-/
lemma slope_le_leftDeriv (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f (Iio y) y) :
    slope f x y <= derivWithin f (Iio y) y :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

/--
lemma `slope_le_leftDeriv_of_mem_interior` / 引理 `slope_le_leftDeriv_of_mem_interior`

English:
lemma slope_le_leftDeriv_of_mem_interior
  statement: (hfc : ConvexOn Real S f)
  proof: slope_le_leftDeriv hfc hys (interior_subset hxs) hxy
    (differentiableWithinAt_Iio_of_mem_interior hfc hxs)

中文:
引理 slope_le_leftDeriv_of_mem_interior
  结论: (hfc : ConvexOn 实数 S f)
  证明: slope_le_leftDeriv hfc hys (interior_subset hxs) hxy
    (differentiableWithinAt_Iio_of_mem_interior hfc hxs)

Depends on / 依赖: differentiableWithinAt_Iio_of_mem_interior, interior_subset, slope_le_leftDeriv
-/
lemma slope_le_leftDeriv_of_mem_interior (hfc : ConvexOn Real S f)
    (hys : x in S) (hxs : y in interior S) (hxy : x < y) :
    slope f x y <= derivWithin f (Iio y) y :=
  slope_le_leftDeriv hfc hys (interior_subset hxs) hxy
    (differentiableWithinAt_Iio_of_mem_interior hfc hxs)

/--
lemma `slope_le_of_hasDerivWithinAt` / 引理 `slope_le_of_hasDerivWithinAt`

English:
lemma slope_le_of_hasDerivWithinAt
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsLT hx hy hxy

中文:
引理 slope_le_of_hasDerivWithinAt
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsLT hx hy hxy

Depends on / 依赖: hfc.slope_le_of_hasDerivWithinAt_Iio, mem_nhdsLT, mono_of_mem_nhdsWithin, ordConnected, ordConnected.mem_nhdsLT, slope_le_of_hasDerivWithinAt_Iio
-/
lemma slope_le_of_hasDerivWithinAt (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    slope f x y <= f' :=
hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsLT hx hy hxy

/--
lemma `slope_le_derivWithin` / 引理 `slope_le_derivWithin`

English:
lemma slope_le_derivWithin
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

中文:
引理 slope_le_derivWithin
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_le_of_hasDerivWithinAt, hfd.hasDerivWithinAt, slope_le_of_hasDerivWithinAt
-/
lemma slope_le_derivWithin (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f S y) :
    slope f x y <= derivWithin f S y :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/--
lemma `slope_le_of_hasDerivAt` / 引理 `slope_le_of_hasDerivAt`

English:
lemma slope_le_of_hasDerivAt
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

中文:
引理 slope_le_of_hasDerivAt
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_le_of_hasDerivWithinAt_Iio, slope_le_of_hasDerivWithinAt_Iio
-/
lemma slope_le_of_hasDerivAt (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y <= f' :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

/--
lemma `slope_le_deriv` / 引理 `slope_le_deriv`

English:
lemma slope_le_deriv
  statement: (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

中文:
引理 slope_le_deriv
  结论: (hfc : ConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

Depends on / 依赖: hasDerivAt, hfc.slope_le_of_hasDerivAt, hfd.hasDerivAt, slope_le_of_hasDerivAt
-/
lemma slope_le_deriv (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableAt Real f y) :
    slope f x y <= deriv f y :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Convex functions, monotonicity of derivative
-/

/--
lemma `monotoneOn_derivWithin` / 引理 `monotoneOn_derivWithin`

English:
lemma monotoneOn_derivWithin
  given: (hfc : ConvexOn Real S f) (hfd : DifferentiableOn Real f S)
  proof: by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd x hx)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd y hy))

中文:
引理 monotoneOn_derivWithin
  条件: (hfc : ConvexOn 实数 S f) (hfd : DifferentiableOn 实数 f S)
  证明: by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd x hx)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd y hy))

Depends on / 依赖: derivWithin_le_slope, eq_or_lt_of_le, hfc.derivWithin_le_slope, hfc.slope_le_derivWithin, slope_le_derivWithin
-/
lemma monotoneOn_derivWithin (hfc : ConvexOn Real S f) (hfd : DifferentiableOn Real f S) :
    MonotoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd x hx)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd y hy))

/--
theorem `monotoneOn_deriv` / 定理 `monotoneOn_deriv`

English:
theorem monotoneOn_deriv
  given: (hfc : ConvexOn Real S f) (hfd : forall x in S, DifferentiableAt Real f x)
  proof: by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.deriv_le_slope hx hy hxy' (hfd x hx)).trans (hfc.slope_le_deriv hx hy hxy' (hfd y hy))

中文:
定理 monotoneOn_deriv
  条件: (hfc : ConvexOn 实数 S f) (hfd : 对任意 x in S, DifferentiableAt 实数 f x)
  证明: by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.deriv_le_slope hx hy hxy' (hfd x hx)).trans (hfc.slope_le_deriv hx hy hxy' (hfd y hy))

Depends on / 依赖: deriv_le_slope, eq_or_lt_of_le, hfc.deriv_le_slope, hfc.slope_le_deriv, slope_le_deriv
-/
theorem monotoneOn_deriv (hfc : ConvexOn Real S f) (hfd : forall x in S, DifferentiableAt Real f x) :
    MonotoneOn (deriv f) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.deriv_le_slope hx hy hxy' (hfd x hx)).trans (hfc.slope_le_deriv hx hy hxy' (hfd y hy))

/--
lemma `isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg` / 引理 `isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg`

English:
lemma isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg
  statement: (hf : ConvexOn Real S f) (hx : x in interior S)
  proof: by
  intro y hy
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · suffices 0 <= slope f x y by
      simp only [slope_def_field, div_nonneg_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hxy, and_false, or_false] at this
      exact this.1
exact hf_rd.trans rightDeriv_le_slope_o

中文:
引理 isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg
  结论: (hf : ConvexOn 实数 S f) (hx : x in interior S)
  证明: by
  intro y hy
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · suffices 0 <= slope f x y by
      simp only [slope_def_field, div_nonneg_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hxy, and_false, or_false] at this
      exact this.1
exact hf_rd.trans rightDeriv_le_slope_o

Depends on / 依赖: and_false, div_nonneg_iff, div_nonpos_iff, h_eq, hf_rd, hf_rd.trans, lt_trichotomy, not_le, not_le.mpr, or_false, rightDeriv_le_slope_of_mem_interior, slope_, slope_def_field, sub_nonneg, tsub_le_iff_right, zero_add
-/
lemma isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg (hf : ConvexOn Real S f) (hx : x in interior S)
    (hf_ld : derivWithin f (Iio x) x <= 0) (hf_rd : 0 <= derivWithin f (Ioi x) x) :
    IsMinOn f S x := by
  intro y hy
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · suffices 0 <= slope f x y by
      simp only [slope_def_field, div_nonneg_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hxy, and_false, or_false] at this
      exact this.1
exact hf_rd.trans rightDeriv_le_slope_of_mem_interior hf hx hy hxy
  · simp [h_eq]
  · suffices slope f x y <= 0 by
      simp only [slope_def_field, div_nonpos_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hyx, and_false, or_false] at this
      exact this.1
    rw [slope_comm]
    exact (slope_le_leftDeriv_of_mem_interior hf hy hx hyx).trans hf_ld

/--
lemma `isMinOn_of_rightDeriv_eq_zero` / 引理 `isMinOn_of_rightDeriv_eq_zero`

English:
lemma isMinOn_of_rightDeriv_eq_zero
  statement: (hf : ConvexOn Real S f) (hx : x in interior S)
  proof: by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx ?_ hf_rd.symm.le
  exact (hf.leftDeriv_le_rightDeriv_of_mem_interior hx).trans_eq hf_rd

中文:
引理 isMinOn_of_rightDeriv_eq_zero
  结论: (hf : ConvexOn 实数 S f) (hx : x in interior S)
  证明: by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx ?_ hf_rd.symm.le
  exact (hf.leftDeriv_le_rightDeriv_of_mem_interior hx).trans_eq hf_rd

Depends on / 依赖: hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg, hf.leftDeriv_le_rightDeriv_of_mem_interior, hf_rd, hf_rd.symm.le, isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg, leftDeriv_le_rightDeriv_of_mem_interior, trans_eq
-/
lemma isMinOn_of_rightDeriv_eq_zero (hf : ConvexOn Real S f) (hx : x in interior S)
    (hf_rd : derivWithin f (Ioi x) x = 0) :
    IsMinOn f S x := by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx ?_ hf_rd.symm.le
  exact (hf.leftDeriv_le_rightDeriv_of_mem_interior hx).trans_eq hf_rd

/--
lemma `isMinOn_of_leftDeriv_eq_zero` / 引理 `isMinOn_of_leftDeriv_eq_zero`

English:
lemma isMinOn_of_leftDeriv_eq_zero
  statement: (hf : ConvexOn Real S f) (hx : x in interior S)
  proof: by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx hf_ld.le ?_
  exact hf_ld.symm.le.trans (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)

中文:
引理 isMinOn_of_leftDeriv_eq_zero
  结论: (hf : ConvexOn 实数 S f) (hx : x in interior S)
  证明: by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx hf_ld.le ?_
  exact hf_ld.symm.le.trans (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)

Depends on / 依赖: hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg, hf.leftDeriv_le_rightDeriv_of_mem_interior, hf_ld, hf_ld.le, hf_ld.symm.le.trans, isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg, leftDeriv_le_rightDeriv_of_mem_interior
-/
lemma isMinOn_of_leftDeriv_eq_zero (hf : ConvexOn Real S f) (hx : x in interior S)
    (hf_ld : derivWithin f (Iio x) x = 0) :
    IsMinOn f S x := by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx hf_ld.le ?_
  exact hf_ld.symm.le.trans (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)

end ConvexOn

namespace StrictConvexOn

variable {S : Set Real} {f : Real -> Real} {x y f' : Real}

section left
/-!
### Strict convex functions, derivative at left endpoint of secant
-/

/--
lemma `lt_slope_of_hasDerivWithinAt_Ioi` / 引理 `lt_slope_of_hasDerivWithinAt_Ioi`

English:
lemma lt_slope_of_hasDerivWithinAt_Ioi
  statement: (hfc : StrictConvexOn Real S f)
  proof: by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u in S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hx hu hy hxu.ne' hxy.ne' huy
  simp only [← slope_def_field] at this
  exact (hfc.convexOn.le_slope_of_hasDerivWithinAt_Ioi hx hu hxu hf').trans_lt thi

中文:
引理 lt_slope_of_hasDerivWithinAt_Ioi
  结论: (hfc : StrictConvexOn 实数 S f)
  证明: by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u in S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hx hu hy hxu.ne' hxy.ne' huy
  simp only [← slope_def_field] at this
  exact (hfc.convexOn.le_slope_of_hasDerivWithinAt_Ioi hx hu hxu hf').trans_lt thi

Depends on / 依赖: convexOn, exists_between, hfc.convexOn.le_slope_of_hasDerivWithinAt_Ioi, hfc.secant_strict_mono, huy.le, hxu.le, hxu.ne, hxy.ne, le_slope_of_hasDerivWithinAt_Ioi, ordConnected, ordConnected.out, secant_strict_mono, slope_def_field, trans_lt
-/
lemma lt_slope_of_hasDerivWithinAt_Ioi (hfc : StrictConvexOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' < slope f x y := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u in S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hx hu hy hxu.ne' hxy.ne' huy
  simp only [← slope_def_field] at this
  exact (hfc.convexOn.le_slope_of_hasDerivWithinAt_Ioi hx hu hxu hf').trans_lt this

/--
lemma `rightDeriv_lt_slope` / 引理 `rightDeriv_lt_slope`

English:
lemma rightDeriv_lt_slope
  statement: (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

中文:
引理 rightDeriv_lt_slope
  结论: (hfc : StrictConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.lt_slope_of_hasDerivWithinAt_Ioi, hfd.hasDerivWithinAt, lt_slope_of_hasDerivWithinAt_Ioi
-/
lemma rightDeriv_lt_slope (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f (Ioi x) x) :
    derivWithin f (Ioi x) x < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

/--
lemma `lt_slope_of_hasDerivWithinAt` / 引理 `lt_slope_of_hasDerivWithinAt`

English:
lemma lt_slope_of_hasDerivWithinAt
  statement: (hfc : StrictConvexOn Real S f)
  proof: hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsGT hx hy hxy

中文:
引理 lt_slope_of_hasDerivWithinAt
  结论: (hfc : StrictConvexOn 实数 S f)
  证明: hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsGT hx hy hxy

Depends on / 依赖: hfc.lt_slope_of_hasDerivWithinAt_Ioi, lt_slope_of_hasDerivWithinAt_Ioi, mem_nhdsGT, mono_of_mem_nhdsWithin, ordConnected, ordConnected.mem_nhdsGT
-/
lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConvexOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S x) :
    f' < slope f x y :=
hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsGT hx hy hxy

/--
lemma `derivWithin_lt_slope` / 引理 `derivWithin_lt_slope`

English:
lemma derivWithin_lt_slope
  statement: (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

中文:
引理 derivWithin_lt_slope
  结论: (hfc : StrictConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.lt_slope_of_hasDerivWithinAt, hfd.hasDerivWithinAt, lt_slope_of_hasDerivWithinAt
-/
lemma derivWithin_lt_slope (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f S x) :
    derivWithin f S x < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/--
lemma `lt_slope_of_hasDerivAt` / 引理 `lt_slope_of_hasDerivAt`

English:
lemma lt_slope_of_hasDerivAt
  statement: (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

中文:
引理 lt_slope_of_hasDerivAt
  结论: (hfc : StrictConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.lt_slope_of_hasDerivWithinAt_Ioi, lt_slope_of_hasDerivWithinAt_Ioi
-/
lemma lt_slope_of_hasDerivAt (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hf' : HasDerivAt f f' x) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

/--
lemma `deriv_lt_slope` / 引理 `deriv_lt_slope`

English:
lemma deriv_lt_slope
  statement: (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

中文:
引理 deriv_lt_slope
  结论: (hfc : StrictConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

Depends on / 依赖: hasDerivAt, hfc.lt_slope_of_hasDerivAt, hfd.hasDerivAt, lt_slope_of_hasDerivAt
-/
lemma deriv_lt_slope (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableAt Real f x) :
    deriv f x < slope f x y :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Strict convex functions, derivative at right endpoint of secant
-/

/--
lemma `slope_lt_of_hasDerivWithinAt_Iio` / 引理 `slope_lt_of_hasDerivWithinAt_Iio`

English:
lemma slope_lt_of_hasDerivWithinAt_Iio
  statement: (hfc : StrictConvexOn Real S f)
  proof: by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u in S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hy hx hu hxy.ne huy.ne hxu
  simp_rw [← slope_def_field, slope_comm _ y] at this
exact this.trans_le hfc.convexOn.slope_le_of_hasDerivWithinAt_Iio hu h

中文:
引理 slope_lt_of_hasDerivWithinAt_Iio
  结论: (hfc : StrictConvexOn 实数 S f)
  证明: by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u in S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hy hx hu hxy.ne huy.ne hxu
  simp_rw [← slope_def_field, slope_comm _ y] at this
exact this.trans_le hfc.convexOn.slope_le_of_hasDerivWithinAt_Iio hu h

Depends on / 依赖: convexOn, exists_between, hfc.convexOn.slope_le_of_hasDerivWithinAt_Iio, hfc.secant_strict_mono, huy.le, huy.ne, hxu.le, hxy.ne, ordConnected, ordConnected.out, secant_strict_mono, simp_rw, slope_comm, slope_def_field, slope_le_of_hasDerivWithinAt_Iio, this.trans_le, trans_le
-/
lemma slope_lt_of_hasDerivWithinAt_Iio (hfc : StrictConvexOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    slope f x y < f' := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u in S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hy hx hu hxy.ne huy.ne hxu
  simp_rw [← slope_def_field, slope_comm _ y] at this
exact this.trans_le hfc.convexOn.slope_le_of_hasDerivWithinAt_Iio hu hy huy hf'

/--
lemma `slope_lt_leftDeriv` / 引理 `slope_lt_leftDeriv`

English:
lemma slope_lt_leftDeriv
  statement: (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

中文:
引理 slope_lt_leftDeriv
  结论: (hfc : StrictConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_lt_of_hasDerivWithinAt_Iio, hfd.hasDerivWithinAt, slope_lt_of_hasDerivWithinAt_Iio
-/
lemma slope_lt_leftDeriv (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f (Iio y) y) :
    slope f x y < derivWithin f (Iio y) y :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

/--
lemma `slope_lt_of_hasDerivWithinAt` / 引理 `slope_lt_of_hasDerivWithinAt`

English:
lemma slope_lt_of_hasDerivWithinAt
  statement: (hfc : StrictConvexOn Real S f)
  proof: hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsLT hx hy hxy

中文:
引理 slope_lt_of_hasDerivWithinAt
  结论: (hfc : StrictConvexOn 实数 S f)
  证明: hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsLT hx hy hxy

Depends on / 依赖: hfc.slope_lt_of_hasDerivWithinAt_Iio, mem_nhdsLT, mono_of_mem_nhdsWithin, ordConnected, ordConnected.mem_nhdsLT, slope_lt_of_hasDerivWithinAt_Iio
-/
lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConvexOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    slope f x y < f' :=
hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsLT hx hy hxy

/--
lemma `slope_lt_derivWithin` / 引理 `slope_lt_derivWithin`

English:
lemma slope_lt_derivWithin
  statement: (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

中文:
引理 slope_lt_derivWithin
  结论: (hfc : StrictConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_lt_of_hasDerivWithinAt, hfd.hasDerivWithinAt, slope_lt_of_hasDerivWithinAt
-/
lemma slope_lt_derivWithin (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f S y) :
    slope f x y < derivWithin f S y :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/--
lemma `slope_lt_of_hasDerivAt` / 引理 `slope_lt_of_hasDerivAt`

English:
lemma slope_lt_of_hasDerivAt
  statement: (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

中文:
引理 slope_lt_of_hasDerivAt
  结论: (hfc : StrictConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_lt_of_hasDerivWithinAt_Iio, slope_lt_of_hasDerivWithinAt_Iio
-/
lemma slope_lt_of_hasDerivAt (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y < f' :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

/--
lemma `slope_lt_deriv` / 引理 `slope_lt_deriv`

English:
lemma slope_lt_deriv
  statement: (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

中文:
引理 slope_lt_deriv
  结论: (hfc : StrictConvexOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

Depends on / 依赖: hasDerivAt, hfc.slope_lt_of_hasDerivAt, hfd.hasDerivAt, slope_lt_of_hasDerivAt
-/
lemma slope_lt_deriv (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableAt Real f y) :
    slope f x y < deriv f y :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right

/-!
### Strict convex functions, strict monotonicity of derivative
-/

/--
lemma `strictMonoOn_derivWithin` / 引理 `strictMonoOn_derivWithin`

English:
lemma strictMonoOn_derivWithin
  given: (hfc : StrictConvexOn Real S f) (hfd : DifferentiableOn Real f S)
  proof: by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd x hx)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd y hy))

中文:
引理 strictMonoOn_derivWithin
  条件: (hfc : StrictConvexOn 实数 S f) (hfd : DifferentiableOn 实数 f S)
  证明: by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd x hx)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd y hy))

Depends on / 依赖: derivWithin_lt_slope, hfc.derivWithin_lt_slope, hfc.slope_lt_derivWithin, slope_lt_derivWithin
-/
lemma strictMonoOn_derivWithin (hfc : StrictConvexOn Real S f) (hfd : DifferentiableOn Real f S) :
    StrictMonoOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd x hx)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd y hy))

/--
lemma `strictMonoOn_deriv` / 引理 `strictMonoOn_deriv`

English:
lemma strictMonoOn_deriv
  given: (hfc : StrictConvexOn Real S f) (hfd : forall x in S, DifferentiableAt Real f x)
  proof: by
  intro x hx y hy hxy
  exact (hfc.deriv_lt_slope hx hy hxy (hfd x hx)).trans (hfc.slope_lt_deriv hx hy hxy (hfd y hy))

中文:
引理 strictMonoOn_deriv
  条件: (hfc : StrictConvexOn 实数 S f) (hfd : 对任意 x in S, DifferentiableAt 实数 f x)
  证明: by
  intro x hx y hy hxy
  exact (hfc.deriv_lt_slope hx hy hxy (hfd x hx)).trans (hfc.slope_lt_deriv hx hy hxy (hfd y hy))

Depends on / 依赖: deriv_lt_slope, hfc.deriv_lt_slope, hfc.slope_lt_deriv, slope_lt_deriv
-/
lemma strictMonoOn_deriv (hfc : StrictConvexOn Real S f) (hfd : forall x in S, DifferentiableAt Real f x) :
    StrictMonoOn (deriv f) S := by
  intro x hx y hy hxy
  exact (hfc.deriv_lt_slope hx hy hxy (hfd x hx)).trans (hfc.slope_lt_deriv hx hy hxy (hfd y hy))

end StrictConvexOn

section MirrorImage

variable {S : Set Real} {f : Real -> Real} {x y f' : Real}

namespace ConcaveOn

section left

/--
lemma `slope_le_of_hasDerivWithinAt_Ioi` / 引理 `slope_le_of_hasDerivWithinAt_Ioi`

English:
lemma slope_le_of_hasDerivWithinAt_Ioi
  statement: (hfc : ConcaveOn Real S f)
  proof: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_le_neg (hfc.neg.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

中文:
引理 slope_le_of_hasDerivWithinAt_Ioi
  结论: (hfc : ConcaveOn 实数 S f)
  证明: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_le_neg (hfc.neg.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

Depends on / 依赖: Pi.neg_def, hfc.neg.le_slope_of_hasDerivWithinAt_Ioi, le_slope_of_hasDerivWithinAt_Ioi, neg_def, neg_le_neg, neg_neg, slope_neg
-/
lemma slope_le_of_hasDerivWithinAt_Ioi (hfc : ConcaveOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y <= f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_le_neg (hfc.neg.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

/--
lemma `slope_le_rightDeriv` / 引理 `slope_le_rightDeriv`

English:
lemma slope_le_rightDeriv
  statement: (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

中文:
引理 slope_le_rightDeriv
  结论: (hfc : ConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_le_of_hasDerivWithinAt_Ioi, hfd.hasDerivWithinAt, slope_le_of_hasDerivWithinAt_Ioi
-/
lemma slope_le_rightDeriv (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f (Ioi x) x) :
    slope f x y <= derivWithin f (Ioi x) x :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

/--
lemma `slope_le_of_hasDerivWithinAt` / 引理 `slope_le_of_hasDerivWithinAt`

English:
lemma slope_le_of_hasDerivWithinAt
  statement: (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy
hfd.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsGT hx hy hxy

中文:
引理 slope_le_of_hasDerivWithinAt
  结论: (hfc : ConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy
hfd.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsGT hx hy hxy

Depends on / 依赖: hfc.slope_le_of_hasDerivWithinAt_Ioi, hfd.mono_of_mem_nhdsWithin, mem_nhdsGT, mono_of_mem_nhdsWithin, ordConnected, ordConnected.mem_nhdsGT, slope_le_of_hasDerivWithinAt_Ioi
-/
lemma slope_le_of_hasDerivWithinAt (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : HasDerivWithinAt f f' S x) :
    slope f x y <= f' :=
hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy
hfd.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsGT hx hy hxy

/--
lemma `slope_le_derivWithin` / 引理 `slope_le_derivWithin`

English:
lemma slope_le_derivWithin
  statement: (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

中文:
引理 slope_le_derivWithin
  结论: (hfc : ConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_le_of_hasDerivWithinAt, hfd.hasDerivWithinAt, slope_le_of_hasDerivWithinAt
-/
lemma slope_le_derivWithin (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f S x) :
    slope f x y <= derivWithin f S x :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/--
lemma `slope_le_of_hasDerivAt` / 引理 `slope_le_of_hasDerivAt`

English:
lemma slope_le_of_hasDerivAt
  statement: (hfc : ConcaveOn Real S f)
  proof: hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

中文:
引理 slope_le_of_hasDerivAt
  结论: (hfc : ConcaveOn 实数 S f)
  证明: hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_le_of_hasDerivWithinAt_Ioi, slope_le_of_hasDerivWithinAt_Ioi
-/
lemma slope_le_of_hasDerivAt (hfc : ConcaveOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivAt f f' x) :
    slope f x y <= f' :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

/--
lemma `slope_le_deriv` / 引理 `slope_le_deriv`

English:
lemma slope_le_deriv
  statement: (hfc : ConcaveOn Real S f)
  proof: hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

中文:
引理 slope_le_deriv
  结论: (hfc : ConcaveOn 实数 S f)
  证明: hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

Depends on / 依赖: hasDerivAt, hfc.slope_le_of_hasDerivAt, hfd.hasDerivAt, slope_le_of_hasDerivAt
-/
lemma slope_le_deriv (hfc : ConcaveOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableAt Real f x) :
    slope f x y <= deriv f x :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right

/--
lemma `le_slope_of_hasDerivWithinAt_Iio` / 引理 `le_slope_of_hasDerivWithinAt_Iio`

English:
lemma le_slope_of_hasDerivWithinAt_Iio
  statement: (hfc : ConcaveOn Real S f)
  proof: by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_le_neg (hfc.neg.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

中文:
引理 le_slope_of_hasDerivWithinAt_Iio
  结论: (hfc : ConcaveOn 实数 S f)
  证明: by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_le_neg (hfc.neg.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

Depends on / 依赖: Pi.neg_def, hfc.neg.slope_le_of_hasDerivWithinAt_Iio, neg_def, neg_le_neg, neg_neg, slope_le_of_hasDerivWithinAt_Iio, slope_neg
-/
lemma le_slope_of_hasDerivWithinAt_Iio (hfc : ConcaveOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' <= slope f x y := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_le_neg (hfc.neg.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

/--
lemma `leftDeriv_le_slope` / 引理 `leftDeriv_le_slope`

English:
lemma leftDeriv_le_slope
  statement: (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

中文:
引理 leftDeriv_le_slope
  结论: (hfc : ConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.le_slope_of_hasDerivWithinAt_Iio, hfd.hasDerivWithinAt, le_slope_of_hasDerivWithinAt_Iio
-/
lemma leftDeriv_le_slope (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f (Iio y) y) :
    derivWithin f (Iio y) y <= slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

/--
lemma `le_slope_of_hasDerivWithinAt` / 引理 `le_slope_of_hasDerivWithinAt`

English:
lemma le_slope_of_hasDerivWithinAt
  statement: (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsLT hx hy hxy

中文:
引理 le_slope_of_hasDerivWithinAt
  结论: (hfc : ConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsLT hx hy hxy

Depends on / 依赖: hfc.le_slope_of_hasDerivWithinAt_Iio, le_slope_of_hasDerivWithinAt_Iio, mem_nhdsLT, mono_of_mem_nhdsWithin, ordConnected, ordConnected.mem_nhdsLT
-/
lemma le_slope_of_hasDerivWithinAt (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    f' <= slope f x y :=
hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy
hf'.mono_of_mem_nhdsWithin hfc.1.ordConnected.mem_nhdsLT hx hy hxy

/--
lemma `derivWithin_le_slope` / 引理 `derivWithin_le_slope`

English:
lemma derivWithin_le_slope
  statement: (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.le_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

中文:
引理 derivWithin_le_slope
  结论: (hfc : ConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.le_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.le_slope_of_hasDerivWithinAt, hfd.hasDerivWithinAt, le_slope_of_hasDerivWithinAt
-/
lemma derivWithin_le_slope (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f S y) :
    derivWithin f S y <= slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/--
lemma `le_slope_of_hasDerivAt` / 引理 `le_slope_of_hasDerivAt`

English:
lemma le_slope_of_hasDerivAt
  statement: (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

中文:
引理 le_slope_of_hasDerivAt
  结论: (hfc : ConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.le_slope_of_hasDerivWithinAt_Iio, le_slope_of_hasDerivWithinAt_Iio
-/
lemma le_slope_of_hasDerivAt (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' <= slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

/--
lemma `deriv_le_slope` / 引理 `deriv_le_slope`

English:
lemma deriv_le_slope
  statement: (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.le_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

中文:
引理 deriv_le_slope
  结论: (hfc : ConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.le_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

Depends on / 依赖: hasDerivAt, hfc.le_slope_of_hasDerivAt, hfd.hasDerivAt, le_slope_of_hasDerivAt
-/
lemma deriv_le_slope (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableAt Real f y) :
    deriv f y <= slope f x y :=
  hfc.le_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right

/--
lemma `antitoneOn_derivWithin` / 引理 `antitoneOn_derivWithin`

English:
lemma antitoneOn_derivWithin
  given: (hfc : ConcaveOn Real S f) (hfd : DifferentiableOn Real f S)
  proof: by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd y hy)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd x hx))

中文:
引理 antitoneOn_derivWithin
  条件: (hfc : ConcaveOn 实数 S f) (hfd : DifferentiableOn 实数 f S)
  证明: by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd y hy)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd x hx))

Depends on / 依赖: derivWithin_le_slope, eq_or_lt_of_le, hfc.derivWithin_le_slope, hfc.slope_le_derivWithin, slope_le_derivWithin
-/
lemma antitoneOn_derivWithin (hfc : ConcaveOn Real S f) (hfd : DifferentiableOn Real f S) :
    AntitoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd y hy)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd x hx))

/--
theorem `antitoneOn_deriv` / 定理 `antitoneOn_deriv`

English:
theorem antitoneOn_deriv
  given: (hfc : ConcaveOn Real S f) (hfd : forall x in S, DifferentiableAt Real f x)
  proof: by
  simpa using (hfc.neg.monotoneOn_deriv (fun x hx => (hfd x hx).neg)).neg

中文:
定理 antitoneOn_deriv
  条件: (hfc : ConcaveOn 实数 S f) (hfd : 对任意 x in S, DifferentiableAt 实数 f x)
  证明: by
  simpa using (hfc.neg.monotoneOn_deriv (fun x hx => (hfd x hx).neg)).neg

Depends on / 依赖: hfc.neg.monotoneOn_deriv, monotoneOn_deriv
-/
theorem antitoneOn_deriv (hfc : ConcaveOn Real S f) (hfd : forall x in S, DifferentiableAt Real f x) :
    AntitoneOn (deriv f) S := by
  simpa using (hfc.neg.monotoneOn_deriv (fun x hx => (hfd x hx).neg)).neg

end ConcaveOn

namespace StrictConcaveOn

section left

/--
lemma `slope_lt_of_hasDerivWithinAt_Ioi` / 引理 `slope_lt_of_hasDerivWithinAt_Ioi`

English:
lemma slope_lt_of_hasDerivWithinAt_Ioi
  statement: (hfc : StrictConcaveOn Real S f)
  proof: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

中文:
引理 slope_lt_of_hasDerivWithinAt_Ioi
  结论: (hfc : StrictConcaveOn 实数 S f)
  证明: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

Depends on / 依赖: Pi.neg_def, hfc.neg.lt_slope_of_hasDerivWithinAt_Ioi, lt_slope_of_hasDerivWithinAt_Ioi, neg_def, neg_lt_neg, neg_neg, slope_neg
-/
lemma slope_lt_of_hasDerivWithinAt_Ioi (hfc : StrictConcaveOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

/--
lemma `slope_lt_rightDeriv` / 引理 `slope_lt_rightDeriv`

English:
lemma slope_lt_rightDeriv
  statement: (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_lt_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

中文:
引理 slope_lt_rightDeriv
  结论: (hfc : StrictConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_lt_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_lt_of_hasDerivWithinAt_Ioi, hfd.hasDerivWithinAt, slope_lt_of_hasDerivWithinAt_Ioi
-/
lemma slope_lt_rightDeriv (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f (Ioi x) x) :
    slope f x y < derivWithin f (Ioi x) x :=
  hfc.slope_lt_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

/--
lemma `slope_lt_of_hasDerivWithinAt` / 引理 `slope_lt_of_hasDerivWithinAt`

English:
lemma slope_lt_of_hasDerivWithinAt
  statement: (hfc : StrictConcaveOn Real S f)
  proof: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.neg)

中文:
引理 slope_lt_of_hasDerivWithinAt
  结论: (hfc : StrictConcaveOn 实数 S f)
  证明: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.neg)

Depends on / 依赖: Pi.neg_def, hfc.neg.lt_slope_of_hasDerivWithinAt, hfd.neg, lt_slope_of_hasDerivWithinAt, neg_def, neg_lt_neg, neg_neg, slope_neg
-/
lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConcaveOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : HasDerivWithinAt f f' S x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.neg)

/--
lemma `slope_lt_derivWithin` / 引理 `slope_lt_derivWithin`

English:
lemma slope_lt_derivWithin
  statement: (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

中文:
引理 slope_lt_derivWithin
  结论: (hfc : StrictConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.slope_lt_of_hasDerivWithinAt, hfd.hasDerivWithinAt, slope_lt_of_hasDerivWithinAt
-/
lemma slope_lt_derivWithin (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f S x) :
    slope f x y < derivWithin f S x :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/--
lemma `slope_lt_of_hasDerivAt` / 引理 `slope_lt_of_hasDerivAt`

English:
lemma slope_lt_of_hasDerivAt
  statement: (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivAt hx hy hxy hfd.neg)

中文:
引理 slope_lt_of_hasDerivAt
  结论: (hfc : StrictConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivAt hx hy hxy hfd.neg)

Depends on / 依赖: Pi.neg_def, hfc.neg.lt_slope_of_hasDerivAt, hfd.neg, lt_slope_of_hasDerivAt, neg_def, neg_lt_neg, neg_neg, slope_neg
-/
lemma slope_lt_of_hasDerivAt (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : HasDerivAt f f' x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivAt hx hy hxy hfd.neg)

/--
lemma `slope_lt_deriv` / 引理 `slope_lt_deriv`

English:
lemma slope_lt_deriv
  statement: (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

中文:
引理 slope_lt_deriv
  结论: (hfc : StrictConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

Depends on / 依赖: hasDerivAt, hfc.slope_lt_of_hasDerivAt, hfd.hasDerivAt, slope_lt_of_hasDerivAt
-/
lemma slope_lt_deriv (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableAt Real f x) :
    slope f x y < deriv f x :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right

/--
lemma `lt_slope_of_hasDerivWithinAt_Iio` / 引理 `lt_slope_of_hasDerivWithinAt_Iio`

English:
lemma lt_slope_of_hasDerivWithinAt_Iio
  statement: (hfc : StrictConcaveOn Real S f)
  proof: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

中文:
引理 lt_slope_of_hasDerivWithinAt_Iio
  结论: (hfc : StrictConcaveOn 实数 S f)
  证明: by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

Depends on / 依赖: Pi.neg_def, hfc.neg.slope_lt_of_hasDerivWithinAt_Iio, neg_def, neg_lt_neg, neg_neg, slope_lt_of_hasDerivWithinAt_Iio, slope_neg
-/
lemma lt_slope_of_hasDerivWithinAt_Iio (hfc : StrictConcaveOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' < slope f x y := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

/--
lemma `leftDeriv_lt_slope` / 引理 `leftDeriv_lt_slope`

English:
lemma leftDeriv_lt_slope
  statement: (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

中文:
引理 leftDeriv_lt_slope
  结论: (hfc : StrictConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.lt_slope_of_hasDerivWithinAt_Iio, hfd.hasDerivWithinAt, lt_slope_of_hasDerivWithinAt_Iio
-/
lemma leftDeriv_lt_slope (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f (Iio y) y) :
    derivWithin f (Iio y) y < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

/--
lemma `lt_slope_of_hasDerivWithinAt` / 引理 `lt_slope_of_hasDerivWithinAt`

English:
lemma lt_slope_of_hasDerivWithinAt
  statement: (hfc : StrictConcaveOn Real S f)
  proof: by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt hx hy hxy hf'.neg)

中文:
引理 lt_slope_of_hasDerivWithinAt
  结论: (hfc : StrictConcaveOn 实数 S f)
  证明: by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt hx hy hxy hf'.neg)

Depends on / 依赖: Pi.neg_def, hfc.neg.slope_lt_of_hasDerivWithinAt, neg_def, neg_lt_neg, neg_neg, slope_lt_of_hasDerivWithinAt, slope_neg
-/
lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConcaveOn Real S f)
    (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    f' < slope f x y := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt hx hy hxy hf'.neg)

/--
lemma `derivWithin_lt_slope` / 引理 `derivWithin_lt_slope`

English:
lemma derivWithin_lt_slope
  statement: (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

中文:
引理 derivWithin_lt_slope
  结论: (hfc : StrictConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.lt_slope_of_hasDerivWithinAt, hfd.hasDerivWithinAt, lt_slope_of_hasDerivWithinAt
-/
lemma derivWithin_lt_slope (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableWithinAt Real f S y) :
    derivWithin f S y < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/--
lemma `lt_slope_of_hasDerivAt` / 引理 `lt_slope_of_hasDerivAt`

English:
lemma lt_slope_of_hasDerivAt
  statement: (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

中文:
引理 lt_slope_of_hasDerivAt
  结论: (hfc : StrictConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hfc.lt_slope_of_hasDerivWithinAt_Iio, lt_slope_of_hasDerivWithinAt_Iio
-/
lemma lt_slope_of_hasDerivAt (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

/--
lemma `deriv_lt_slope` / 引理 `deriv_lt_slope`

English:
lemma deriv_lt_slope
  statement: (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  proof: hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

中文:
引理 deriv_lt_slope
  结论: (hfc : StrictConcaveOn 实数 S f) (hx : x in S) (hy : y in S) (hxy : x < y)
  证明: hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

Depends on / 依赖: hasDerivAt, hfc.lt_slope_of_hasDerivAt, hfd.hasDerivAt, lt_slope_of_hasDerivAt
-/
lemma deriv_lt_slope (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y)
    (hfd : DifferentiableAt Real f y) :
    deriv f y < slope f x y :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right

/--
lemma `strictAntiOn_derivWithin` / 引理 `strictAntiOn_derivWithin`

English:
lemma strictAntiOn_derivWithin
  given: (hfc : StrictConcaveOn Real S f) (hfd : DifferentiableOn Real f S)
  proof: by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd y hy)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd x hx))

中文:
引理 strictAntiOn_derivWithin
  条件: (hfc : StrictConcaveOn 实数 S f) (hfd : DifferentiableOn 实数 f S)
  证明: by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd y hy)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd x hx))

Depends on / 依赖: derivWithin_lt_slope, hfc.derivWithin_lt_slope, hfc.slope_lt_derivWithin, slope_lt_derivWithin
-/
lemma strictAntiOn_derivWithin (hfc : StrictConcaveOn Real S f) (hfd : DifferentiableOn Real f S) :
    StrictAntiOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd y hy)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd x hx))

/--
theorem `strictAntiOn_deriv` / 定理 `strictAntiOn_deriv`

English:
theorem strictAntiOn_deriv
  given: (hfc : StrictConcaveOn Real S f) (hfd : forall x in S, DifferentiableAt Real f x)
  proof: by
  simpa using (hfc.neg.strictMonoOn_deriv (fun x hx => (hfd x hx).neg)).neg

中文:
定理 strictAntiOn_deriv
  条件: (hfc : StrictConcaveOn 实数 S f) (hfd : 对任意 x in S, DifferentiableAt 实数 f x)
  证明: by
  simpa using (hfc.neg.strictMonoOn_deriv (fun x hx => (hfd x hx).neg)).neg

Depends on / 依赖: hfc.neg.strictMonoOn_deriv, strictMonoOn_deriv
-/
theorem strictAntiOn_deriv (hfc : StrictConcaveOn Real S f) (hfd : forall x in S, DifferentiableAt Real f x) :
    StrictAntiOn (deriv f) S := by
  simpa using (hfc.neg.strictMonoOn_deriv (fun x hx => (hfd x hx).neg)).neg

end StrictConcaveOn

end MirrorImage
