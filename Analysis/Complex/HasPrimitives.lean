/-
Copyright (c) 2024 Ian Jauslin and Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Jauslin, Alex Kontorovich, Oliver Nash
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex

/-!
# Primitives of Holomorphic Functions

In this file, we give conditions under which holomorphic functions have primitives. The main goal
is to prove that holomorphic functions on simply connected domains have primitives. As a first step,
we prove that holomorphic functions on disks have primitives. The approach is based on Morera's
theorem, that a continuous function (on a disk) whose integral round a rectangle vanishes on all
rectangles contained in the disk has a primitive. (Coupled with the fact that holomorphic functions
satisfy this property.) To prove Morera's theorem, we first define the `Complex.wedgeIntegral`,
which is the integral of a function over a "wedge" (a horizontal segment followed by a vertical
segment in the disk), and compute its derivative.

## Main results

* `Complex.IsConservativeOn.isExactOn_ball`: **Morera's Theorem**: On a disk, a continuous function
  whose integrals on rectangles vanish, has primitives.
* `DifferentiableOn.isExactOn_ball`: On a disk, a holomorphic function has primitives.

TODO: Extend to holomorphic functions on simply connected domains.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Interval

namespace Complex

section AuxiliaryLemmata

variable {c z : Complex} {r x y : Real}

/--
lemma `re_add_im_mul_mem_ball` / 引理 `re_add_im_mul_mem_ball`

English:
lemma re_add_im_mul_mem_ball
  given: (hz : z in ball c r)
  proof: by
  suffices dist (z.re + c.im * I) c <= dist z c from lt_of_le_of_lt this hz
  rw [dist_eq_re_im]; rw [dist_eq_re_im]; rw [Real.le_sqrt (by positivity) (by positivity)]; rw [Real.sq_sqrt (by positivity)]
  simp [sq_nonneg _]

中文:
引理 re_add_im_mul_mem_ball
  条件: (hz : z in ball c r)
  证明: by
  suffices dist (z.re + c.im * I) c <= dist z c from lt_of_le_of_lt this hz
  rw [dist_eq_re_im]; rw [dist_eq_re_im]; rw [Real.le_sqrt (by positivity) (by positivity)]; rw [Real.sq_sqrt (by positivity)]
  simp [sq_nonneg _]
-/
private lemma re_add_im_mul_mem_ball (hz : z in ball c r) :
    z.re + c.im * I in ball c r := by
  suffices dist (z.re + c.im * I) c <= dist z c from lt_of_le_of_lt this hz
  rw [dist_eq_re_im]; rw [dist_eq_re_im]; rw [Real.le_sqrt (by positivity) (by positivity)]; rw [Real.sq_sqrt (by positivity)]
  simp [sq_nonneg _]

/--
lemma `mem_ball_re_aux` / 引理 `mem_ball_re_aux`

English:
lemma mem_ball_re_aux
  given: (hx : x in Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c)))
  proof: by
  set r₁ := r - dist z c
  set s := Ioo (z.re - r₁) (z.re + r₁)
  have s_ball₁ : s ×Complex {z.im} subseteq ball z r₁ := by
    rintro y ⟨yRe : y.re in s, yIm : y.im = z.im⟩
    rw [mem_ball]; rw [dist_eq_re_im]; rw [yIm]; rw [sub_self]; rw [zero_pow two_ne_zero]; rw [add_zero]; rw [Real.sqrt_sq_

中文:
引理 mem_ball_re_aux
  条件: (hx : x in Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c)))
  证明: by
  set r₁ := r - dist z c
  set s := Ioo (z.re - r₁) (z.re + r₁)
  have s_ball₁ : s ×Complex {z.im} subseteq ball z r₁ := by
    rintro y ⟨yRe : y.re in s, yIm : y.im = z.im⟩
    rw [mem_ball]; rw [dist_eq_re_im]; rw [yIm]; rw [sub_self]; rw [zero_pow two_ne_zero]; rw [add_zero]; rw [Real.sqrt_sq_
-/
private lemma mem_ball_re_aux (hx : x in Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) :
    x + z.im * I in ball c r := by
  set r₁ := r - dist z c
  set s := Ioo (z.re - r₁) (z.re + r₁)
  have s_ball₁ : s ×Complex {z.im} subseteq ball z r₁ := by
    rintro y ⟨yRe : y.re in s, yIm : y.im = z.im⟩
    rw [mem_ball]; rw [dist_eq_re_im]; rw [yIm]; rw [sub_self]; rw [zero_pow two_ne_zero]; rw [add_zero]; rw [Real.sqrt_sq_eq_abs]
    grind [abs_lt]
suffices s ×Complex {z.im} subseteq ball c r from this by simp [mem_reProdIm, hx]
exact s_ball₁.trans ball_subset_ball' by simp [r₁]

/--
lemma `mem_closedBall_aux` / 引理 `mem_closedBall_aux`

English:
lemma mem_closedBall_aux
  given: (z_in_ball : z in closedBall c r) (y_in_I : y in Ι c.im z.im)
  proof: by
  refine le_trans ?_ (mem_closedBall.mp z_in_ball)
  rw [dist_eq_re_im]; rw [dist_eq_re_im]; rw [Real.le_sqrt (by positivity) (by positivity)]; rw [Real.sq_sqrt (by positivity)]
  suffices (y - c.im) ^ 2 <= (z.im - c.im) ^ 2 by simpa
  cases mem_uIoc.mp y_in_I <;> nlinarith

中文:
引理 mem_closedBall_aux
  条件: (z_in_ball : z in closedBall c r) (y_in_I : y in Ι c.im z.im)
  证明: by
  refine le_trans ?_ (mem_closedBall.mp z_in_ball)
  rw [dist_eq_re_im]; rw [dist_eq_re_im]; rw [Real.le_sqrt (by positivity) (by positivity)]; rw [Real.sq_sqrt (by positivity)]
  suffices (y - c.im) ^ 2 <= (z.im - c.im) ^ 2 by simpa
  cases mem_uIoc.mp y_in_I <;> nlinarith
-/
private lemma mem_closedBall_aux (z_in_ball : z in closedBall c r) (y_in_I : y in Ι c.im z.im) :
    z.re + y * I in closedBall c r := by
  refine le_trans ?_ (mem_closedBall.mp z_in_ball)
  rw [dist_eq_re_im]; rw [dist_eq_re_im]; rw [Real.le_sqrt (by positivity) (by positivity)]; rw [Real.sq_sqrt (by positivity)]
  suffices (y - c.im) ^ 2 <= (z.im - c.im) ^ 2 by simpa
  cases mem_uIoc.mp y_in_I <;> nlinarith

/--
lemma `mem_ball_of_map_re_aux` / 引理 `mem_ball_of_map_re_aux`

English:
lemma mem_ball_of_map_re_aux
  statement: {a₁ a₂ b : Real} (ha₁ : a₁ + b * I in ball c r)
  proof: by
  convert Convex.rectangle_subset (convex_ball c r) ha₁ ha₂ ?_ ?_ <;>
  simp [horizontalSegment_eq a₁ a₂ b, ha₁, ha₂, Rectangle]

中文:
引理 mem_ball_of_map_re_aux
  结论: {a₁ a₂ b : 实数} (ha₁ : a₁ + b * I in ball c r)
  证明: by
  convert Convex.rectangle_subset (convex_ball c r) ha₁ ha₂ ?_ ?_ <;>
  simp [horizontalSegment_eq a₁ a₂ b, ha₁, ha₂, Rectangle]
-/
private lemma mem_ball_of_map_re_aux {a₁ a₂ b : Real} (ha₁ : a₁ + b * I in ball c r)
    (ha₂ : a₂ + b * I in ball c r) : (fun (x : Real) => x + b * I) '' [[a₁, a₂]] subseteq ball c r := by
  convert Convex.rectangle_subset (convex_ball c r) ha₁ ha₂ ?_ ?_ <;>
  simp [horizontalSegment_eq a₁ a₂ b, ha₁, ha₂, Rectangle]

/--
lemma `mem_ball_of_map_im_aux₁` / 引理 `mem_ball_of_map_im_aux₁`

English:
lemma mem_ball_of_map_im_aux₁
  statement: {a b₁ b₂ : Real} (hb₁ : a + b₁ * I in ball c r)
  proof: by
  convert Convex.rectangle_subset (convex_ball c r) hb₁ hb₂ ?_ ?_ <;>
  simp [verticalSegment_eq a b₁ b₂, hb₁, hb₂, Rectangle]

中文:
引理 mem_ball_of_map_im_aux₁
  结论: {a b₁ b₂ : 实数} (hb₁ : a + b₁ * I in ball c r)
  证明: by
  convert Convex.rectangle_subset (convex_ball c r) hb₁ hb₂ ?_ ?_ <;>
  simp [verticalSegment_eq a b₁ b₂, hb₁, hb₂, Rectangle]
-/
private lemma mem_ball_of_map_im_aux₁ {a b₁ b₂ : Real} (hb₁ : a + b₁ * I in ball c r)
    (hb₂ : a + b₂ * I in ball c r) : (fun (y : Real) => a + y * I) '' [[b₁, b₂]] subseteq ball c r := by
  convert Convex.rectangle_subset (convex_ball c r) hb₁ hb₂ ?_ ?_ <;>
  simp [verticalSegment_eq a b₁ b₂, hb₁, hb₂, Rectangle]

/--
lemma `mem_ball_of_map_im_aux₂` / 引理 `mem_ball_of_map_im_aux₂`

English:
lemma mem_ball_of_map_im_aux₂
  given: {w : Complex} (hw : w in ball z (r - dist z c))
  proof: by
  apply mem_ball_of_map_im_aux₁ <;>
  apply mem_of_subset_of_mem (ball_subset_ball' (by simp) : ball z (r - dist z c) subseteq ball c r)
  · exact re_add_im_mul_mem_ball hw
  · simpa using hw

中文:
引理 mem_ball_of_map_im_aux₂
  条件: {w : Complex} (hw : w in ball z (r - dist z c))
  证明: by
  apply mem_ball_of_map_im_aux₁ <;>
  apply mem_of_subset_of_mem (ball_subset_ball' (by simp) : ball z (r - dist z c) subseteq ball c r)
  · exact re_add_im_mul_mem_ball hw
  · simpa using hw
-/
private lemma mem_ball_of_map_im_aux₂ {w : Complex} (hw : w in ball z (r - dist z c)) :
    (fun (y : Real) => w.re + y * I) '' [[z.im, w.im]] subseteq ball c r := by
  apply mem_ball_of_map_im_aux₁ <;>
  apply mem_of_subset_of_mem (ball_subset_ball' (by simp) : ball z (r - dist z c) subseteq ball c r)
  · exact re_add_im_mul_mem_ball hw
  · simpa using hw

end AuxiliaryLemmata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

/--
Definition of `wedgeIntegral` / `wedgeIntegral` 的定义

English:
definition wedgeIntegral
  signature: (z w : Complex) (f : Complex -> E)
  body: (∫ x : Real in z.re..w.re, f (x + z.im * I)) + I • (∫ y : Real in z.im..w.im, f (w.re + y * I))

中文:
定义 wedgeIntegral
  签名: (z w : Complex) (f : Complex -> E)
  定义体: (∫ x : Real in z.re..w.re, f (x + z.im * I)) + I • (∫ y : Real in z.im..w.im, f (w.re + y * I))

Depends on / 依赖: w.im, w.re, z.im, z.re
-/
def wedgeIntegral (z w : Complex) (f : Complex -> E) : E :=
  (∫ x : Real in z.re..w.re, f (x + z.im * I)) + I • (∫ y : Real in z.im..w.im, f (w.re + y * I))

/--
lemma `wedgeIntegral_add_wedgeIntegral_eq` / 引理 `wedgeIntegral_add_wedgeIntegral_eq`

English:
lemma wedgeIntegral_add_wedgeIntegral_eq
  given: (z w : Complex) (f : Complex -> E)
  proof: by
  simp only [wedgeIntegral, intervalIntegral.integral_symm z.re w.re,
    intervalIntegral.integral_symm z.im w.im, smul_neg]
  abel

中文:
引理 wedgeIntegral_add_wedgeIntegral_eq
  条件: (z w : Complex) (f : Complex -> E)
  证明: by
  simp only [wedgeIntegral, intervalIntegral.integral_symm z.re w.re,
    intervalIntegral.integral_symm z.im w.im, smul_neg]
  abel

Depends on / 依赖: integral_symm, intervalIntegral, intervalIntegral.integral_symm, smul_neg, w.im, w.re, wedgeIntegral, z.im, z.re
-/
lemma wedgeIntegral_add_wedgeIntegral_eq (z w : Complex) (f : Complex -> E) :
    wedgeIntegral z w f + wedgeIntegral w z f =
      (∫ x : Real in z.re..w.re, f (x + z.im * I)) -
      (∫ x : Real in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : Real in z.im..w.im, f (w.re + y * I)) -
      I • (∫ y : Real in z.im..w.im, f (z.re + y * I)) := by
  simp only [wedgeIntegral, intervalIntegral.integral_symm z.re w.re,
    intervalIntegral.integral_symm z.im w.im, smul_neg]
  abel

/--
Definition of `IsConservativeOn` / `IsConservativeOn` 的定义

English:
definition IsConservativeOn
  signature: (f : Complex -> E) (U : Set Complex)
  body: forall z w, Rectangle z w subseteq U -> wedgeIntegral z w f = - wedgeIntegral w z f

中文:
定义 IsConservativeOn
  签名: (f : Complex -> E) (U : Set Complex)
  定义体: forall z w, Rectangle z w subseteq U -> wedgeIntegral z w f = - wedgeIntegral w z f

Depends on / 依赖: Rectangle, subseteq, wedgeIntegral
-/
def IsConservativeOn (f : Complex -> E) (U : Set Complex) : Prop :=
  forall z w, Rectangle z w subseteq U -> wedgeIntegral z w f = - wedgeIntegral w z f

/--
Definition of `IsExactOn` / `IsExactOn` 的定义

English:
definition IsExactOn
  signature: (f : Complex -> E) (U : Set Complex)
  body: exists g, forall z in U, HasDerivAt g (f z) z

中文:
定义 IsExactOn
  签名: (f : Complex -> E) (U : Set Complex)
  定义体: exists g, forall z in U, HasDerivAt g (f z) z

Depends on / 依赖: HasDerivAt
-/
def IsExactOn (f : Complex -> E) (U : Set Complex) : Prop :=
  exists g, forall z in U, HasDerivAt g (f z) z

/--
lemma `IsExactOn.with_val_at` / 引理 `IsExactOn.with_val_at`

English:
lemma IsExactOn.with_val_at
  given: {f : Complex -> E} {s : Set Complex} (h : IsExactOn f s) (x₀ : Complex) (y : E)
  proof: by
  obtain ⟨η, hη⟩ := h
  use fun z => η z - η x₀ + y, by simp, by simpa using hη

中文:
引理 IsExactOn.with_val_at
  条件: {f : Complex -> E} {s : Set Complex} (h : IsExactOn f s) (x₀ : Complex) (y : E)
  证明: by
  obtain ⟨η, hη⟩ := h
  use fun z => η z - η x₀ + y, by simp, by simpa using hη
-/
lemma IsExactOn.with_val_at {f : Complex -> E} {s : Set Complex} (h : IsExactOn f s) (x₀ : Complex) (y : E) :
    exists g, g x₀ = y ∧ forall x in s, HasDerivAt g (f x) x := by
  obtain ⟨η, hη⟩ := h
  use fun z => η z - η x₀ + y, by simp, by simpa using hη

variable {c : Complex} {r : Real} {f : Complex -> E}

/--
lemma `IsConservativeOn.mono` / 引理 `IsConservativeOn.mono`

English:
lemma IsConservativeOn.mono
  given: {U V : Set Complex} (h : U subseteq V) (hf : IsConservativeOn f V)
  proof: fun z w hzw => hf z w (hzw.trans h)

中文:
引理 IsConservativeOn.mono
  条件: {U V : Set Complex} (h : U subseteq V) (hf : IsConservativeOn f V)
  证明: fun z w hzw => hf z w (hzw.trans h)

Depends on / 依赖: hzw.trans
-/
lemma IsConservativeOn.mono {U V : Set Complex} (h : U subseteq V) (hf : IsConservativeOn f V) :
    IsConservativeOn f U :=
  fun z w hzw => hf z w (hzw.trans h)

/--
theorem `_root_.DifferentiableOn.isConservativeOn` / 定理 `_root_.DifferentiableOn.isConservativeOn`

English:
theorem _root_.DifferentiableOn.isConservativeOn
  given: {U : Set Complex} (hf : DifferentiableOn Complex f U)
  proof: by
  rintro z w hzw
  rw [← add_eq_zero_iff_eq_neg]; rw [wedgeIntegral_add_wedgeIntegral_eq]
exact integral_boundary_rect_eq_zero_of_differentiableOn f z w hf.mono hzw

中文:
定理 _root_.DifferentiableOn.isConservativeOn
  条件: {U : Set Complex} (hf : DifferentiableOn Complex f U)
  证明: by
  rintro z w hzw
  rw [← add_eq_zero_iff_eq_neg]; rw [wedgeIntegral_add_wedgeIntegral_eq]
exact integral_boundary_rect_eq_zero_of_differentiableOn f z w hf.mono hzw

Depends on / 依赖: add_eq_zero_iff_eq_neg, hf.mono, integral_boundary_rect_eq_zero_of_differentiableOn, wedgeIntegral_add_wedgeIntegral_eq
-/
theorem _root_.DifferentiableOn.isConservativeOn {U : Set Complex} (hf : DifferentiableOn Complex f U) :
    IsConservativeOn f U := by
  rintro z w hzw
  rw [← add_eq_zero_iff_eq_neg]; rw [wedgeIntegral_add_wedgeIntegral_eq]
exact integral_boundary_rect_eq_zero_of_differentiableOn f z w hf.mono hzw

variable [CompleteSpace E]

/--
lemma `IsExactOn.differentiableOn` / 引理 `IsExactOn.differentiableOn`

English:
lemma IsExactOn.differentiableOn
  given: {U : Set Complex} (hU : IsOpen U) (hf : IsExactOn f U)
  proof: by
  obtain ⟨g, hg⟩ := hf
  have hg' : DifferentiableOn Complex g U := fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
exact (differentiableOn_congr <| fun z hz => (hg z hz).deriv).mp hg'.deriv hU

中文:
引理 IsExactOn.differentiableOn
  条件: {U : Set Complex} (hU : IsOpen U) (hf : IsExactOn f U)
  证明: by
  obtain ⟨g, hg⟩ := hf
  have hg' : DifferentiableOn Complex g U := fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
exact (differentiableOn_congr <| fun z hz => (hg z hz).deriv).mp hg'.deriv hU

Depends on / 依赖: DifferentiableOn, differentiableAt, differentiableAt.differentiableWithinAt, differentiableOn_congr, differentiableWithinAt
-/
lemma IsExactOn.differentiableOn {U : Set Complex} (hU : IsOpen U) (hf : IsExactOn f U) :
    DifferentiableOn Complex f U := by
  obtain ⟨g, hg⟩ := hf
  have hg' : DifferentiableOn Complex g U := fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
exact (differentiableOn_congr <| fun z hz => (hg z hz).deriv).mp hg'.deriv hU

section ContinuousOnBall

variable (f_cont : ContinuousOn f (ball c r)) {z : Complex} (hz : z in ball c r)
include f_cont hz

set_option linter.style.whitespace false in -- manual alignment is not recognised
omit [CompleteSpace E] in
/--
lemma `IsConservativeOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral` / 引理 `IsConservativeOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral`

English:
lemma IsConservativeOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral
  proof: by
  refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w w_in_z_ball => ?_⟩
  set I₁ := ∫ x in c.re..w.re, f (x + c.im * I)
  set I₂ := I • ∫ y in c.im..w.im, f (w.re + y * I)
  set I₃ := ∫ x in c.re..z.re, f (x + c.im * I)
  set I₄ := I • ∫ y in c.im..z.im, f (z.re + y * I)


中文:
引理 IsConservativeOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral
  证明: by
  refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w w_in_z_ball => ?_⟩
  set I₁ := ∫ x in c.re..w.re, f (x + c.im * I)
  set I₂ := I • ∫ y in c.im..w.im, f (w.re + y * I)
  set I₃ := ∫ x in c.re..z.re, f (x + c.im * I)
  set I₄ := I • ∫ y in c.im..z.im, f (z.re + y * I)


Depends on / 依赖: c.im, c.re, eventually_nhds_iff_ball, eventually_nhds_iff_ball.mpr, w.im, w.re, w_in_z_ball, z.im, z.re, z_ball
-/
lemma IsConservativeOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral
    (hf : IsConservativeOn f (ball c r)) :
    forallᶠ w in 𝓝 z, wedgeIntegral c w f - wedgeIntegral c z f = wedgeIntegral z w f := by
  refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w w_in_z_ball => ?_⟩
  set I₁ := ∫ x in c.re..w.re, f (x + c.im * I)
  set I₂ := I • ∫ y in c.im..w.im, f (w.re + y * I)
  set I₃ := ∫ x in c.re..z.re, f (x + c.im * I)
  set I₄ := I • ∫ y in c.im..z.im, f (z.re + y * I)
  set I₅ := ∫ x in z.re..w.re, f (x + z.im * I)
  set I₆ := I • ∫ y in z.im..w.im, f (w.re + y * I)
  set I₇ := ∫ x in z.re..w.re, f (x + c.im * I)
  set I₈ := I • ∫ y in c.im..z.im, f (w.re + y * I)
  have z_ball : ball z (r - dist z c) subseteq ball c r := ball_subset_ball' (by simp)
  have w_mem : w in ball c r := mem_of_subset_of_mem z_ball w_in_z_ball
  have integrableHoriz (a₁ a₂ b : Real) (ha₁ : a₁ + b * I in ball c r) (ha₂ : a₂ + b * I in ball c r) :
      IntervalIntegrable (fun x => f (x + b * I)) volume a₁ a₂ :=
    ((f_cont.mono (mem_ball_of_map_re_aux ha₁ ha₂)).comp (by fun_prop)
      (mapsTo_image _ _)).intervalIntegrable
  have integrableVert (a b₁ b₂ : Real) (hb₁ : a + b₁ * I in ball c r) (hb₂ : a + b₂ * I in ball c r) :
      IntervalIntegrable (fun y => f (a + y * I)) volume b₁ b₂ :=
    ((f_cont.mono (mem_ball_of_map_im_aux₁ hb₁ hb₂)).comp (by fun_prop)
      (mapsTo_image _ _)).intervalIntegrable
  have hI₁ : I₁ = I₃ + I₇ := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableHoriz
· exact re_add_im_mul_mem_ball mem_ball_self (pos_of_mem_ball hz)
    · exact re_add_im_mul_mem_ball hz
    · exact re_add_im_mul_mem_ball hz
    · exact re_add_im_mul_mem_ball w_mem
  have hI₂ : I₂ = I₈ + I₆ := by
    rw [← smul_add]; rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableVert
    · exact re_add_im_mul_mem_ball w_mem
    · exact mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    · exact mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    · simpa using w_mem
  have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
    have wzInBall : w.re + z.im * I in ball c r :=
      mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    have wcInBall : w.re + c.im * I in ball c r := re_add_im_mul_mem_ball w_mem
    have hU : Rectangle (z.re + c.im * I) (w.re + z.im * I) subseteq ball c r :=
      (convex_ball c r).rectangle_subset (re_add_im_mul_mem_ball hz) wzInBall
        (by simpa using hz) (by simpa using wcInBall)
    simpa [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] using
      hf (z.re + c.im * I) (w.re + z.im * I) hU
  grind [wedgeIntegral]

/--
lemma `hasDerivAt_wedgeIntegral_re_aux` / 引理 `hasDerivAt_wedgeIntegral_re_aux`

English:
lemma hasDerivAt_wedgeIntegral_re_aux
  proof: by
  suffices (fun x => (∫ t in z.re..x, f (t + z.im * I)) - (x - z.re) • f z) =o[𝓝 z.re]
      fun x => x - z.re from
.trans_isBigO isBigO_re_sub_re this.comp_tendsto (continuous_re.tendsto z)
  let r₁ := r - dist z c
  have r₁_pos : 0 < r₁ := by simpa only [mem_ball, sub_pos, r₁] using hz
  let s 

中文:
引理 hasDerivAt_wedgeIntegral_re_aux
  证明: by
  suffices (fun x => (∫ t in z.re..x, f (t + z.im * I)) - (x - z.re) • f z) =o[𝓝 z.re]
      fun x => x - z.re from
.trans_isBigO isBigO_re_sub_re this.comp_tendsto (continuous_re.tendsto z)
  let r₁ := r - dist z c
  have r₁_pos : 0 < r₁ := by simpa only [mem_ball, sub_pos, r₁] using hz
  let s 
-/
private lemma hasDerivAt_wedgeIntegral_re_aux :
    (fun w => (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z) =o[𝓝 z] fun w => w - z := by
  suffices (fun x => (∫ t in z.re..x, f (t + z.im * I)) - (x - z.re) • f z) =o[𝓝 z.re]
      fun x => x - z.re from
.trans_isBigO isBigO_re_sub_re this.comp_tendsto (continuous_re.tendsto z)
  let r₁ := r - dist z c
  have r₁_pos : 0 < r₁ := by simpa only [mem_ball, sub_pos, r₁] using hz
  let s : Set Real := Ioo (z.re - r₁) (z.re + r₁)
  have zRe_mem_s : z.re in s := by simp [s, r₁_pos]
  have f_contOn : ContinuousOn (fun (x : Real) => f (x + z.im * I)) s :=
f_cont.comp ((continuous_add_const _).comp continuous_ofReal).continuousOn
      fun _ => mem_ball_re_aux
  have int1 : IntervalIntegrable (fun (x : Real) => f (x + z.im * I)) volume z.re z.re :=
ContinuousOn.intervalIntegrable f_contOn.mono by simpa
  have int2 : StronglyMeasurableAtFilter (fun (x : Real) => f (x + z.im * I)) (𝓝 z.re) :=
    f_contOn.stronglyMeasurableAtFilter isOpen_Ioo _ zRe_mem_s
  have int3 : ContinuousAt (fun (x : Real) => f (x + z.im * I)) z.re :=
    isOpen_Ioo.continuousOn_iff.mp f_contOn zRe_mem_s
.isLittleO simpa using intervalIntegral.integral_hasDerivAt_right int1 int2 int3

/--
lemma `hasDerivAt_wedgeIntegral_im_aux` / 引理 `hasDerivAt_wedgeIntegral_im_aux`

English:
lemma hasDerivAt_wedgeIntegral_im_aux
  proof: by
  suffices (fun w => ∫ y in z.im..w.im, f (w.re + y * I) - f z) =o[𝓝 z] fun w => w - z by
    calc
      _ = fun w => (∫ y in z.im..w.im, f (w.re + y * I)) - (∫ _ in z.im..w.im, f z) := by simp
      _ =ᶠ[𝓝 z] fun w => ∫ y in z.im..w.im, f (w.re + y * I) - f z := ?_
      _ =o[𝓝 z] fun w => w - z

中文:
引理 hasDerivAt_wedgeIntegral_im_aux
  证明: by
  suffices (fun w => ∫ y in z.im..w.im, f (w.re + y * I) - f z) =o[𝓝 z] fun w => w - z by
    calc
      _ = fun w => (∫ y in z.im..w.im, f (w.re + y * I)) - (∫ _ in z.im..w.im, f z) := by simp
      _ =ᶠ[𝓝 z] fun w => ∫ y in z.im..w.im, f (w.re + y * I) - f z := ?_
      _ =o[𝓝 z] fun w => w - z
-/
private lemma hasDerivAt_wedgeIntegral_im_aux :
    (fun w => (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) =o[𝓝 z] fun w => w - z := by
  suffices (fun w => ∫ y in z.im..w.im, f (w.re + y * I) - f z) =o[𝓝 z] fun w => w - z by
    calc
      _ = fun w => (∫ y in z.im..w.im, f (w.re + y * I)) - (∫ _ in z.im..w.im, f z) := by simp
      _ =ᶠ[𝓝 z] fun w => ∫ y in z.im..w.im, f (w.re + y * I) - f z := ?_
      _ =o[𝓝 z] fun w => w - z := this
    refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w hw => ?_⟩
    exact (intervalIntegral.integral_sub
      ((f_cont.mono (mem_ball_of_map_im_aux₂ hw)).comp (by fun_prop)
        (mapsTo_image _ _)).intervalIntegrable intervalIntegrable_const).symm
  have : (fun w => f w - f z) =o[𝓝 z] fun _ => (1 : Real) := by
    rw [Asymptotics.isLittleO_one_iff]; rw [tendsto_sub_nhds_zero_iff]
exact f_cont.continuousAt _root_.mem_nhds_iff.mpr ⟨ball c r, le_refl _, isOpen_ball, hz⟩
  rw [Asymptotics.IsLittleO] at this ⊢
  intro ε ε_pos
  replace := this ε_pos
  simp only [Asymptotics.isBigOWith_iff, norm_one, mul_one] at this ⊢
  replace this : forallᶠ w in 𝓝 z, forall y in Ι z.im w.im, ‖f (w.re + y * I) - f z‖ <= ε := by
    rw [Metric.nhds_basis_closedBall.eventually_iff] at this ⊢
    obtain ⟨i, i_pos, hi⟩ := this
    exact ⟨i, i_pos, fun w w_in_ball y y_in_I => hi (mem_closedBall_aux w_in_ball y_in_I)⟩
  filter_upwards [this] with w hw
  calc
    _ <= ε * ‖w.im - z.im‖ := intervalIntegral.norm_integral_le_of_norm_le_const hw
    _ = ε * ‖(w - z).im‖ := by simp
    _ <= ε * ‖w - z‖ := (mul_le_mul_iff_of_pos_left ε_pos).mpr (abs_im_le_norm _)

/--
theorem `IsConservativeOn.hasDerivAt_wedgeIntegral` / 定理 `IsConservativeOn.hasDerivAt_wedgeIntegral`

English:
theorem IsConservativeOn.hasDerivAt_wedgeIntegral
  given: (h : IsConservativeOn f (ball c r))
  proof: by
  rw [hasDerivAt_iff_isLittleO]
  calc
    _ =ᶠ[𝓝 z] (fun w => wedgeIntegral z w f - (w - z) • f z) := ?_
    _ = (fun w => (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z)
        + I • (fun w => (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) := ?_
    _ =o[𝓝 z] fun w => w - 

中文:
定理 IsConservativeOn.hasDerivAt_wedgeIntegral
  条件: (h : IsConservativeOn f (ball c r))
  证明: by
  rw [hasDerivAt_iff_isLittleO]
  calc
    _ =ᶠ[𝓝 z] (fun w => wedgeIntegral z w f - (w - z) • f z) := ?_
    _ = (fun w => (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z)
        + I • (fun w => (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) := ?_
    _ =o[𝓝 z] fun w => w - 

Depends on / 依赖: const_smul_left, eventually_nhds_wedgeIntegral_sub_wedgeIntegral, f_cont, h.eventually_nhds_wedgeIntegral_sub_wedgeIntegral, hasDerivAt_iff_isLittleO, hasDerivAt_wedgeIntegral_im_aux, hasDerivAt_wedgeIntegral_re_aux, w.im, w.re, wedgeIntegral, z.im, z.re
-/
theorem IsConservativeOn.hasDerivAt_wedgeIntegral (h : IsConservativeOn f (ball c r)) :
    HasDerivAt (fun w => wedgeIntegral c w f) (f z) z := by
  rw [hasDerivAt_iff_isLittleO]
  calc
    _ =ᶠ[𝓝 z] (fun w => wedgeIntegral z w f - (w - z) • f z) := ?_
    _ = (fun w => (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z)
        + I • (fun w => (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) := ?_
    _ =o[𝓝 z] fun w => w - z := (hasDerivAt_wedgeIntegral_re_aux f_cont hz).add
        ((hasDerivAt_wedgeIntegral_im_aux f_cont hz).const_smul_left I)
· exact (h.eventually_nhds_wedgeIntegral_sub_wedgeIntegral f_cont hz).mono by simp
  ext w
  set I₁ := ∫ x in z.re..w.re, f (x + z.im * I)
  set I₂ := ∫ y in z.im..w.im, f (w.re + y * I)
  calc
    _ = I₁ + I • I₂ - ((w - z).re + (w - z).im * I) • f z := by congr; rw [re_add_im]
    _ = I₁ + I • I₂ - ((w.re - z.re : Complex) + (w.im - z.im) * I) • f z := by simp
    _ = I₁ - (w.re - z.re : Complex) • f z + I • (I₂ - (w.im - z.im : Complex) • f z) := ?_
  · rw [add_smul, smul_sub, smul_smul, mul_comm I]; abel
  · congr <;> simp

end ContinuousOnBall

/--
theorem `IsConservativeOn.isExactOn_ball` / 定理 `IsConservativeOn.isExactOn_ball`

English:
theorem IsConservativeOn.isExactOn_ball
  statement: (hf' : ContinuousOn f (ball c r))
  proof: ⟨fun z => wedgeIntegral c z f, fun _ => hf.hasDerivAt_wedgeIntegral hf'⟩

中文:
定理 IsConservativeOn.isExactOn_ball
  结论: (hf' : ContinuousOn f (ball c r))
  证明: ⟨fun z => wedgeIntegral c z f, fun _ => hf.hasDerivAt_wedgeIntegral hf'⟩

Depends on / 依赖: hasDerivAt_wedgeIntegral, hf.hasDerivAt_wedgeIntegral, wedgeIntegral
-/
theorem IsConservativeOn.isExactOn_ball (hf' : ContinuousOn f (ball c r))
    (hf : IsConservativeOn f (ball c r)) :
    IsExactOn f (ball c r) :=
  ⟨fun z => wedgeIntegral c z f, fun _ => hf.hasDerivAt_wedgeIntegral hf'⟩

/--
theorem `isConservativeOn_and_continuousOn_iff_isDifferentiableOn` / 定理 `isConservativeOn_and_continuousOn_iff_isDifferentiableOn`

English:
theorem isConservativeOn_and_continuousOn_iff_isDifferentiableOn
  proof: by
  refine ⟨fun ⟨hf, hf'⟩ z hz => ?_, fun hf => ⟨hf.isConservativeOn, hf.continuousOn⟩⟩
  obtain ⟨r, h₀, h₁⟩ : exists r > 0, ball z r subseteq U := Metric.isOpen_iff.mp hU z hz
  have : DifferentiableOn Complex f (ball z r) :=
    (IsConservativeOn.isExactOn_ball (hf'.mono h₁) (hf.mono h₁)).differe

中文:
定理 isConservativeOn_and_continuousOn_iff_isDifferentiableOn
  证明: by
  refine ⟨fun ⟨hf, hf'⟩ z hz => ?_, fun hf => ⟨hf.isConservativeOn, hf.continuousOn⟩⟩
  obtain ⟨r, h₀, h₁⟩ : exists r > 0, ball z r subseteq U := Metric.isOpen_iff.mp hU z hz
  have : DifferentiableOn Complex f (ball z r) :=
    (IsConservativeOn.isExactOn_ball (hf'.mono h₁) (hf.mono h₁)).differe

Depends on / 依赖: DifferentiableOn, IsConservativeOn, IsConservativeOn.isExactOn_ball, Metric, Metric.isOpen_iff.mp, continuousOn, differentiableOn, hf.continuousOn, hf.isConservativeOn, hf.mono, inter_subset_left, isConservativeOn, isExactOn_ball, isOpen_ball, isOpen_iff, mem_ball_self, mem_nhdsWithin, mem_nhdsWithin.mpr, mono_of_mem_nhdsWithin, subseteq
-/
theorem isConservativeOn_and_continuousOn_iff_isDifferentiableOn
    {U : Set Complex} (hU : IsOpen U) :
    IsConservativeOn f U ∧ ContinuousOn f U ↔ DifferentiableOn Complex f U := by
  refine ⟨fun ⟨hf, hf'⟩ z hz => ?_, fun hf => ⟨hf.isConservativeOn, hf.continuousOn⟩⟩
  obtain ⟨r, h₀, h₁⟩ : exists r > 0, ball z r subseteq U := Metric.isOpen_iff.mp hU z hz
  have : DifferentiableOn Complex f (ball z r) :=
    (IsConservativeOn.isExactOn_ball (hf'.mono h₁) (hf.mono h₁)).differentiableOn isOpen_ball
  apply (this z (mem_ball_self h₀)).mono_of_mem_nhdsWithin
  exact mem_nhdsWithin.mpr ⟨ball z r, isOpen_ball, mem_ball_self h₀, inter_subset_left⟩

/--
theorem `_root_.DifferentiableOn.isExactOn_ball` / 定理 `_root_.DifferentiableOn.isExactOn_ball`

English:
theorem _root_.DifferentiableOn.isExactOn_ball
  given: (hf : DifferentiableOn Complex f (ball c r))
  proof: hf.isConservativeOn.isExactOn_ball hf.continuousOn

中文:
定理 _root_.DifferentiableOn.isExactOn_ball
  条件: (hf : DifferentiableOn Complex f (ball c r))
  证明: hf.isConservativeOn.isExactOn_ball hf.continuousOn

Depends on / 依赖: continuousOn, hf.continuousOn, hf.isConservativeOn.isExactOn_ball, isConservativeOn, isExactOn_ball
-/
theorem _root_.DifferentiableOn.isExactOn_ball (hf : DifferentiableOn Complex f (ball c r)) :
    IsExactOn f (ball c r) :=
  hf.isConservativeOn.isExactOn_ball hf.continuousOn

/--
theorem `IsConservativeOn.isExactOn_univ` / 定理 `IsConservativeOn.isExactOn_univ`

English:
theorem IsConservativeOn.isExactOn_univ
  given: (h₁ : Continuous f) (h₂ : IsConservativeOn f univ)
  proof: by
  use (wedgeIntegral 0 · f)
  intro z _
  have h₃ : IsConservativeOn f (ball 0 (‖z‖ + 1)) := h₂.mono (subset_univ _)
  exact h₃.hasDerivAt_wedgeIntegral (by fun_prop) (by aesop)

中文:
定理 IsConservativeOn.isExactOn_univ
  条件: (h₁ : Continuous f) (h₂ : IsConservativeOn f univ)
  证明: by
  use (wedgeIntegral 0 · f)
  intro z _
  have h₃ : IsConservativeOn f (ball 0 (‖z‖ + 1)) := h₂.mono (subset_univ _)
  exact h₃.hasDerivAt_wedgeIntegral (by fun_prop) (by aesop)

Depends on / 依赖: IsConservativeOn, fun_prop, hasDerivAt_wedgeIntegral, subset_univ, wedgeIntegral
-/
theorem IsConservativeOn.isExactOn_univ (h₁ : Continuous f) (h₂ : IsConservativeOn f univ) :
    IsExactOn f univ := by
  use (wedgeIntegral 0 · f)
  intro z _
  have h₃ : IsConservativeOn f (ball 0 (‖z‖ + 1)) := h₂.mono (subset_univ _)
  exact h₃.hasDerivAt_wedgeIntegral (by fun_prop) (by aesop)

/--
theorem `_root_.Differentiable.isExactOn_univ` / 定理 `_root_.Differentiable.isExactOn_univ`

English:
theorem _root_.Differentiable.isExactOn_univ
  given: (hf : Differentiable Complex f)
  statement: IsExactOn f univ
  proof: by
  apply IsConservativeOn.isExactOn_univ hf.continuous
    ((isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).2 hf.differentiableOn).1

中文:
定理 _root_.Differentiable.isExactOn_univ
  条件: (hf : Differentiable Complex f)
  结论: IsExactOn f univ
  证明: by
  apply IsConservativeOn.isExactOn_univ hf.continuous
    ((isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).2 hf.differentiableOn).1

Depends on / 依赖: IsConservativeOn, IsConservativeOn.isExactOn_univ, continuous, differentiableOn, hf.continuous, hf.differentiableOn, isConservativeOn_and_continuousOn_iff_isDifferentiableOn, isExactOn_univ, isOpen_univ
-/
theorem _root_.Differentiable.isExactOn_univ (hf : Differentiable Complex f) : IsExactOn f univ := by
  apply IsConservativeOn.isExactOn_univ hf.continuous
    ((isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).2 hf.differentiableOn).1

end Complex
