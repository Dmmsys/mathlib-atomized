/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.CPolynomialDef

/-!
# Linear functions are analytic

In this file we prove that a `ContinuousLinearMap` defines an analytic function with
the formal power series `f x = f a + f (x - a)`. We also prove similar results for bilinear maps.

We deduce this fact from the stronger result that continuous linear maps are continuously
polynomial, i.e., they admit a finite power series.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology NNReal ENNReal
open Set Filter Asymptotics

noncomputable section

namespace ContinuousLinearMap

@[simp]
/--
theorem `fpowerSeries_radius` / 定理 `fpowerSeries_radius`

English:
theorem fpowerSeries_radius
  given: (f : E ->L[𝕜] F) (x : E)
  statement: (f.fpowerSeries x).radius = ∞
  proof: (f.fpowerSeries x).radius_eq_top_of_forall_image_add_eq_zero 2 fun _ => rfl

中文:
定理 fpowerSeries_radius
  条件: (f : E ->L[𝕜] F) (x : E)
  结论: (f.fpowerSeries x).radius = ∞
  证明: (f.fpowerSeries x).radius_eq_top_of_forall_image_add_eq_zero 2 fun _ => rfl

Depends on / 依赖: f.fpowerSeries, fpowerSeries, radius_eq_top_of_forall_image_add_eq_zero
-/
theorem fpowerSeries_radius (f : E ->L[𝕜] F) (x : E) : (f.fpowerSeries x).radius = ∞ :=
  (f.fpowerSeries x).radius_eq_top_of_forall_image_add_eq_zero 2 fun _ => rfl

/--
theorem `hasFiniteFPowerSeriesOnBall` / 定理 `hasFiniteFPowerSeriesOnBall`

English:
theorem hasFiniteFPowerSeriesOnBall
  given: (f : E ->L[𝕜] F) (x : E)
  proof: by simp
  r_pos := ENNReal.coe_lt_top
hasSum := fun _ => (hasSum_nat_add_iff' 2).1 by
    simp [Finset.sum_range_succ, hasSum_zero, fpowerSeries]
  finite := by
    intro m hm
    match m with
    | 0 | 1 => linarith
    | n + 2 => simp [fpowerSeries]

中文:
定理 hasFiniteFPowerSeriesOnBall
  条件: (f : E ->L[𝕜] F) (x : E)
  证明: by simp
  r_pos := ENNReal.coe_lt_top
hasSum := fun _ => (hasSum_nat_add_iff' 2).1 by
    simp [Finset.sum_range_succ, hasSum_zero, fpowerSeries]
  finite := by
    intro m hm
    match m with
    | 0 | 1 => linarith
    | n + 2 => simp [fpowerSeries]
-/
protected theorem hasFiniteFPowerSeriesOnBall (f : E ->L[𝕜] F) (x : E) :
    HasFiniteFPowerSeriesOnBall f (f.fpowerSeries x) x 2 ∞ where
  r_le := by simp
  r_pos := ENNReal.coe_lt_top
hasSum := fun _ => (hasSum_nat_add_iff' 2).1 by
    simp [Finset.sum_range_succ, hasSum_zero, fpowerSeries]
  finite := by
    intro m hm
    match m with
    | 0 | 1 => linarith
    | n + 2 => simp [fpowerSeries]

/--
theorem `hasFPowerSeriesOnBall` / 定理 `hasFPowerSeriesOnBall`

English:
theorem hasFPowerSeriesOnBall
  given: (f : E ->L[𝕜] F) (x : E)
  proof: (f.hasFiniteFPowerSeriesOnBall x).toHasFPowerSeriesOnBall

中文:
定理 hasFPowerSeriesOnBall
  条件: (f : E ->L[𝕜] F) (x : E)
  证明: (f.hasFiniteFPowerSeriesOnBall x).toHasFPowerSeriesOnBall
-/
protected theorem hasFPowerSeriesOnBall (f : E ->L[𝕜] F) (x : E) :
    HasFPowerSeriesOnBall f (f.fpowerSeries x) x ∞ :=
  (f.hasFiniteFPowerSeriesOnBall x).toHasFPowerSeriesOnBall

/--
theorem `hasFPowerSeriesAt` / 定理 `hasFPowerSeriesAt`

English:
theorem hasFPowerSeriesAt
  given: (f : E ->L[𝕜] F) (x : E)
  proof: ⟨∞, f.hasFPowerSeriesOnBall x⟩

中文:
定理 hasFPowerSeriesAt
  条件: (f : E ->L[𝕜] F) (x : E)
  证明: ⟨∞, f.hasFPowerSeriesOnBall x⟩
-/
protected theorem hasFPowerSeriesAt (f : E ->L[𝕜] F) (x : E) :
    HasFPowerSeriesAt f (f.fpowerSeries x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall x⟩

/--
theorem `cpolynomialAt` / 定理 `cpolynomialAt`

English:
theorem cpolynomialAt
  given: (f : E ->L[𝕜] F) (x : E)
  statement: CPolynomialAt 𝕜 f x
  proof: (f.hasFiniteFPowerSeriesOnBall x).cpolynomialAt

中文:
定理 cpolynomialAt
  条件: (f : E ->L[𝕜] F) (x : E)
  结论: CPolynomialAt 𝕜 f x
  证明: (f.hasFiniteFPowerSeriesOnBall x).cpolynomialAt
-/
protected theorem cpolynomialAt (f : E ->L[𝕜] F) (x : E) : CPolynomialAt 𝕜 f x :=
  (f.hasFiniteFPowerSeriesOnBall x).cpolynomialAt

/--
theorem `analyticAt` / 定理 `analyticAt`

English:
theorem analyticAt
  given: (f : E ->L[𝕜] F) (x : E)
  statement: AnalyticAt 𝕜 f x
  proof: (f.hasFPowerSeriesAt x).analyticAt

中文:
定理 analyticAt
  条件: (f : E ->L[𝕜] F) (x : E)
  结论: AnalyticAt 𝕜 f x
  证明: (f.hasFPowerSeriesAt x).analyticAt
-/
protected theorem analyticAt (f : E ->L[𝕜] F) (x : E) : AnalyticAt 𝕜 f x :=
  (f.hasFPowerSeriesAt x).analyticAt

/--
theorem `cpolynomialOn` / 定理 `cpolynomialOn`

English:
theorem cpolynomialOn
  given: (f : E ->L[𝕜] F) (s : Set E)
  statement: CPolynomialOn 𝕜 f s
  proof: fun x _ => f.cpolynomialAt x

中文:
定理 cpolynomialOn
  条件: (f : E ->L[𝕜] F) (s : Set E)
  结论: CPolynomialOn 𝕜 f s
  证明: fun x _ => f.cpolynomialAt x
-/
protected theorem cpolynomialOn (f : E ->L[𝕜] F) (s : Set E) : CPolynomialOn 𝕜 f s :=
  fun x _ => f.cpolynomialAt x

/--
theorem `analyticOnNhd` / 定理 `analyticOnNhd`

English:
theorem analyticOnNhd
  given: (f : E ->L[𝕜] F) (s : Set E)
  statement: AnalyticOnNhd 𝕜 f s
  proof: fun x _ => f.analyticAt x

中文:
定理 analyticOnNhd
  条件: (f : E ->L[𝕜] F) (s : Set E)
  结论: AnalyticOnNhd 𝕜 f s
  证明: fun x _ => f.analyticAt x
-/
protected theorem analyticOnNhd (f : E ->L[𝕜] F) (s : Set E) : AnalyticOnNhd 𝕜 f s :=
  fun x _ => f.analyticAt x

/--
theorem `analyticWithinAt` / 定理 `analyticWithinAt`

English:
theorem analyticWithinAt
  given: (f : E ->L[𝕜] F) (s : Set E) (x : E)
  statement: AnalyticWithinAt 𝕜 f s x
  proof: (f.analyticAt x).analyticWithinAt

中文:
定理 analyticWithinAt
  条件: (f : E ->L[𝕜] F) (s : Set E) (x : E)
  结论: AnalyticWithinAt 𝕜 f s x
  证明: (f.analyticAt x).analyticWithinAt
-/
protected theorem analyticWithinAt (f : E ->L[𝕜] F) (s : Set E) (x : E) : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt

/--
theorem `analyticOn` / 定理 `analyticOn`

English:
theorem analyticOn
  given: (f : E ->L[𝕜] F) (s : Set E)
  statement: AnalyticOn 𝕜 f s
  proof: fun x _ => f.analyticWithinAt _ x

中文:
定理 analyticOn
  条件: (f : E ->L[𝕜] F) (s : Set E)
  结论: AnalyticOn 𝕜 f s
  证明: fun x _ => f.analyticWithinAt _ x
-/
protected theorem analyticOn (f : E ->L[𝕜] F) (s : Set E) : AnalyticOn 𝕜 f s :=
  fun x _ => f.analyticWithinAt _ x

/--
Definition of `uncurryBilinear` / `uncurryBilinear` 的定义

English:
definition uncurryBilinear
  signature: (f : E ->L[𝕜] F ->L[𝕜] G)
  body: @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _
(↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F ->L[𝕜] G) ->L[𝕜] _).comp
      f.bilinearComp (fst _ _ _) (snd _ _ _)

@[simp]

中文:
定义 uncurryBilinear
  签名: (f : E ->L[𝕜] F ->L[𝕜] G)
  定义体: @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _
(↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F ->L[𝕜] G) ->L[𝕜] _).comp
      f.bilinearComp (fst _ _ _) (snd _ _ _)

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.uncurryLeft, bilinearComp, continuousMultilinearCurryFin1, f.bilinearComp, uncurryLeft
-/
def uncurryBilinear (f : E ->L[𝕜] F ->L[𝕜] G) : E × F [×2]->L[𝕜] G :=
@ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _
(↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F ->L[𝕜] G) ->L[𝕜] _).comp
      f.bilinearComp (fst _ _ _) (snd _ _ _)

@[simp]
/--
theorem `uncurryBilinear_apply` / 定理 `uncurryBilinear_apply`

English:
theorem uncurryBilinear_apply
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (m : Fin 2 -> E × F)
  proof: rfl

中文:
定理 uncurryBilinear_apply
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (m : Fin 2 -> E × F)
  证明: rfl
-/
theorem uncurryBilinear_apply (f : E ->L[𝕜] F ->L[𝕜] G) (m : Fin 2 -> E × F) :
    f.uncurryBilinear m = f (m 0).1 (m 1).2 :=
  rfl

/--
Definition of `fpowerSeriesBilinear` / `fpowerSeriesBilinear` 的定义

English:
definition fpowerSeriesBilinear
  signature: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)

中文:
定义 fpowerSeriesBilinear
  签名: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
-/
def fpowerSeriesBilinear (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) : FormalMultilinearSeries 𝕜 (E × F) G
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ (f x.1 x.2)
  | 1 => (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
  | 2 => f.uncurryBilinear
  | _ => 0

@[simp]
/--
theorem `fpowerSeriesBilinear_apply_zero` / 定理 `fpowerSeriesBilinear_apply_zero`

English:
theorem fpowerSeriesBilinear_apply_zero
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  proof: rfl

@[simp]

中文:
定理 fpowerSeriesBilinear_apply_zero
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  证明: rfl

@[simp]
-/
theorem fpowerSeriesBilinear_apply_zero (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ (f x.1 x.2) :=
  rfl

@[simp]
/--
theorem `fpowerSeriesBilinear_apply_one` / 定理 `fpowerSeriesBilinear_apply_one`

English:
theorem fpowerSeriesBilinear_apply_one
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  proof: rfl

@[simp]

中文:
定理 fpowerSeriesBilinear_apply_one
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  证明: rfl

@[simp]
-/
theorem fpowerSeriesBilinear_apply_one (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 1 = (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x) :=
  rfl

@[simp]
/--
theorem `fpowerSeriesBilinear_apply_two` / 定理 `fpowerSeriesBilinear_apply_two`

English:
theorem fpowerSeriesBilinear_apply_two
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  proof: rfl

@[simp]

中文:
定理 fpowerSeriesBilinear_apply_two
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  证明: rfl

@[simp]
-/
theorem fpowerSeriesBilinear_apply_two (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 2 = f.uncurryBilinear :=
  rfl

@[simp]
/--
theorem `fpowerSeriesBilinear_apply_add_three` / 定理 `fpowerSeriesBilinear_apply_add_three`

English:
theorem fpowerSeriesBilinear_apply_add_three
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) (n)
  proof: rfl

@[simp]

中文:
定理 fpowerSeriesBilinear_apply_add_three
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) (n)
  证明: rfl

@[simp]
-/
theorem fpowerSeriesBilinear_apply_add_three (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) (n) :
    fpowerSeriesBilinear f x (n + 3) = 0 :=
  rfl

@[simp]
/--
theorem `fpowerSeriesBilinear_radius` / 定理 `fpowerSeriesBilinear_radius`

English:
theorem fpowerSeriesBilinear_radius
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  proof: (f.fpowerSeriesBilinear x).radius_eq_top_of_forall_image_add_eq_zero 3 fun _ => rfl

中文:
定理 fpowerSeriesBilinear_radius
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  证明: (f.fpowerSeriesBilinear x).radius_eq_top_of_forall_image_add_eq_zero 3 fun _ => rfl

Depends on / 依赖: f.fpowerSeriesBilinear, fpowerSeriesBilinear, radius_eq_top_of_forall_image_add_eq_zero
-/
theorem fpowerSeriesBilinear_radius (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) :
    (f.fpowerSeriesBilinear x).radius = ∞ :=
  (f.fpowerSeriesBilinear x).radius_eq_top_of_forall_image_add_eq_zero 3 fun _ => rfl

/--
theorem `hasFPowerSeriesOnBall_bilinear` / 定理 `hasFPowerSeriesOnBall_bilinear`

English:
theorem hasFPowerSeriesOnBall_bilinear
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  proof: { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    hasSum := fun _ =>
(hasSum_nat_add_iff' 3).1 by
        simp only [Finset.sum_range_succ, Prod.fst_add, Prod.snd_add, f.map_add_add]
        simp [fpowerSeriesBilinear, hasSum_zero] }

中文:
定理 hasFPowerSeriesOnBall_bilinear
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  证明: { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    hasSum := fun _ =>
(hasSum_nat_add_iff' 3).1 by
        simp only [Finset.sum_range_succ, Prod.fst_add, Prod.snd_add, f.map_add_add]
        simp [fpowerSeriesBilinear, hasSum_zero] }
-/
protected theorem hasFPowerSeriesOnBall_bilinear (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) :
    HasFPowerSeriesOnBall (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x ∞ :=
  { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    hasSum := fun _ =>
(hasSum_nat_add_iff' 3).1 by
        simp only [Finset.sum_range_succ, Prod.fst_add, Prod.snd_add, f.map_add_add]
        simp [fpowerSeriesBilinear, hasSum_zero] }

/--
theorem `hasFPowerSeriesAt_bilinear` / 定理 `hasFPowerSeriesAt_bilinear`

English:
theorem hasFPowerSeriesAt_bilinear
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  proof: ⟨∞, f.hasFPowerSeriesOnBall_bilinear x⟩

中文:
定理 hasFPowerSeriesAt_bilinear
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  证明: ⟨∞, f.hasFPowerSeriesOnBall_bilinear x⟩
-/
protected theorem hasFPowerSeriesAt_bilinear (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) :
    HasFPowerSeriesAt (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall_bilinear x⟩

/--
theorem `analyticAt_bilinear` / 定理 `analyticAt_bilinear`

English:
theorem analyticAt_bilinear
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  proof: (f.hasFPowerSeriesAt_bilinear x).analyticAt

中文:
定理 analyticAt_bilinear
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
  证明: (f.hasFPowerSeriesAt_bilinear x).analyticAt
-/
protected theorem analyticAt_bilinear (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) :
    AnalyticAt 𝕜 (fun x : E × F => f x.1 x.2) x :=
  (f.hasFPowerSeriesAt_bilinear x).analyticAt

/--
theorem `analyticWithinAt_bilinear` / 定理 `analyticWithinAt_bilinear`

English:
theorem analyticWithinAt_bilinear
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (s : Set (E × F)) (x : E × F)
  proof: (f.analyticAt_bilinear x).analyticWithinAt

中文:
定理 analyticWithinAt_bilinear
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (s : Set (E × F)) (x : E × F)
  证明: (f.analyticAt_bilinear x).analyticWithinAt
-/
protected theorem analyticWithinAt_bilinear (f : E ->L[𝕜] F ->L[𝕜] G) (s : Set (E × F)) (x : E × F) :
    AnalyticWithinAt 𝕜 (fun x : E × F => f x.1 x.2) s x :=
  (f.analyticAt_bilinear x).analyticWithinAt

/--
theorem `analyticOnNhd_bilinear` / 定理 `analyticOnNhd_bilinear`

English:
theorem analyticOnNhd_bilinear
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (s : Set (E × F))
  proof: fun x _ => f.analyticAt_bilinear x

中文:
定理 analyticOnNhd_bilinear
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (s : Set (E × F))
  证明: fun x _ => f.analyticAt_bilinear x
-/
protected theorem analyticOnNhd_bilinear (f : E ->L[𝕜] F ->L[𝕜] G) (s : Set (E × F)) :
    AnalyticOnNhd 𝕜 (fun x : E × F => f x.1 x.2) s :=
  fun x _ => f.analyticAt_bilinear x

/--
theorem `analyticOn_bilinear` / 定理 `analyticOn_bilinear`

English:
theorem analyticOn_bilinear
  given: (f : E ->L[𝕜] F ->L[𝕜] G) (s : Set (E × F))
  proof: (f.analyticOnNhd_bilinear s).analyticOn

中文:
定理 analyticOn_bilinear
  条件: (f : E ->L[𝕜] F ->L[𝕜] G) (s : Set (E × F))
  证明: (f.analyticOnNhd_bilinear s).analyticOn
-/
protected theorem analyticOn_bilinear (f : E ->L[𝕜] F ->L[𝕜] G) (s : Set (E × F)) :
    AnalyticOn 𝕜 (fun x : E × F => f x.1 x.2) s :=
  (f.analyticOnNhd_bilinear s).analyticOn

end ContinuousLinearMap

variable {s : Set E} {z : E} {t : Set (E × F)} {p : E × F}

@[fun_prop]
/--
lemma `analyticAt_id` / 引理 `analyticAt_id`

English:
lemma analyticAt_id
  statement: AnalyticAt 𝕜 (id : E -> E) z
  proof: (ContinuousLinearMap.id 𝕜 E).analyticAt z

中文:
引理 analyticAt_id
  结论: AnalyticAt 𝕜 (id : E -> E) z
  证明: (ContinuousLinearMap.id 𝕜 E).analyticAt z

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, analyticAt
-/
lemma analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z :=
  (ContinuousLinearMap.id 𝕜 E).analyticAt z

/--
lemma `analyticWithinAt_id` / 引理 `analyticWithinAt_id`

English:
lemma analyticWithinAt_id
  statement: AnalyticWithinAt 𝕜 (id : E -> E) s z
  proof: analyticAt_id.analyticWithinAt

中文:
引理 analyticWithinAt_id
  结论: AnalyticWithinAt 𝕜 (id : E -> E) s z
  证明: analyticAt_id.analyticWithinAt

Depends on / 依赖: analyticAt_id, analyticAt_id.analyticWithinAt, analyticWithinAt
-/
lemma analyticWithinAt_id : AnalyticWithinAt 𝕜 (id : E -> E) s z :=
  analyticAt_id.analyticWithinAt

/--
theorem `analyticOnNhd_id` / 定理 `analyticOnNhd_id`

English:
theorem analyticOnNhd_id
  statement: AnalyticOnNhd 𝕜 (fun x : E => x) s
  proof: fun _ _ => analyticAt_id

中文:
定理 analyticOnNhd_id
  结论: AnalyticOnNhd 𝕜 (fun x : E => x) s
  证明: fun _ _ => analyticAt_id

Depends on / 依赖: analyticAt_id
-/
theorem analyticOnNhd_id : AnalyticOnNhd 𝕜 (fun x : E => x) s :=
  fun _ _ => analyticAt_id

/--
theorem `analyticOn_id` / 定理 `analyticOn_id`

English:
theorem analyticOn_id
  statement: AnalyticOn 𝕜 (fun x : E => x) s
  proof: fun _ _ => analyticWithinAt_id

中文:
定理 analyticOn_id
  结论: AnalyticOn 𝕜 (fun x : E => x) s
  证明: fun _ _ => analyticWithinAt_id

Depends on / 依赖: analyticWithinAt_id
-/
theorem analyticOn_id : AnalyticOn 𝕜 (fun x : E => x) s :=
  fun _ _ => analyticWithinAt_id

/--
theorem `analyticAt_fst` / 定理 `analyticAt_fst`

English:
theorem analyticAt_fst
  statement: AnalyticAt 𝕜 (fun p : E × F => p.fst) p
  proof: (ContinuousLinearMap.fst 𝕜 E F).analyticAt p

中文:
定理 analyticAt_fst
  结论: AnalyticAt 𝕜 (fun p : E × F => p.fst) p
  证明: (ContinuousLinearMap.fst 𝕜 E F).analyticAt p

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fst, analyticAt
-/
theorem analyticAt_fst : AnalyticAt 𝕜 (fun p : E × F => p.fst) p :=
  (ContinuousLinearMap.fst 𝕜 E F).analyticAt p

/--
theorem `analyticWithinAt_fst` / 定理 `analyticWithinAt_fst`

English:
theorem analyticWithinAt_fst
  statement: AnalyticWithinAt 𝕜 (fun p : E × F => p.fst) t p
  proof: analyticAt_fst.analyticWithinAt

中文:
定理 analyticWithinAt_fst
  结论: AnalyticWithinAt 𝕜 (fun p : E × F => p.fst) t p
  证明: analyticAt_fst.analyticWithinAt

Depends on / 依赖: analyticAt_fst, analyticAt_fst.analyticWithinAt, analyticWithinAt
-/
theorem analyticWithinAt_fst : AnalyticWithinAt 𝕜 (fun p : E × F => p.fst) t p :=
  analyticAt_fst.analyticWithinAt

/--
theorem `analyticAt_snd` / 定理 `analyticAt_snd`

English:
theorem analyticAt_snd
  statement: AnalyticAt 𝕜 (fun p : E × F => p.snd) p
  proof: (ContinuousLinearMap.snd 𝕜 E F).analyticAt p

中文:
定理 analyticAt_snd
  结论: AnalyticAt 𝕜 (fun p : E × F => p.snd) p
  证明: (ContinuousLinearMap.snd 𝕜 E F).analyticAt p

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.snd, analyticAt
-/
theorem analyticAt_snd : AnalyticAt 𝕜 (fun p : E × F => p.snd) p :=
  (ContinuousLinearMap.snd 𝕜 E F).analyticAt p

/--
theorem `analyticWithinAt_snd` / 定理 `analyticWithinAt_snd`

English:
theorem analyticWithinAt_snd
  statement: AnalyticWithinAt 𝕜 (fun p : E × F => p.snd) t p
  proof: analyticAt_snd.analyticWithinAt

中文:
定理 analyticWithinAt_snd
  结论: AnalyticWithinAt 𝕜 (fun p : E × F => p.snd) t p
  证明: analyticAt_snd.analyticWithinAt

Depends on / 依赖: analyticAt_snd, analyticAt_snd.analyticWithinAt, analyticWithinAt
-/
theorem analyticWithinAt_snd : AnalyticWithinAt 𝕜 (fun p : E × F => p.snd) t p :=
  analyticAt_snd.analyticWithinAt

/--
theorem `analyticOnNhd_fst` / 定理 `analyticOnNhd_fst`

English:
theorem analyticOnNhd_fst
  statement: AnalyticOnNhd 𝕜 (fun p : E × F => p.fst) t
  proof: fun _ _ => analyticAt_fst

中文:
定理 analyticOnNhd_fst
  结论: AnalyticOnNhd 𝕜 (fun p : E × F => p.fst) t
  证明: fun _ _ => analyticAt_fst

Depends on / 依赖: analyticAt_fst
-/
theorem analyticOnNhd_fst : AnalyticOnNhd 𝕜 (fun p : E × F => p.fst) t :=
  fun _ _ => analyticAt_fst

/--
theorem `analyticOn_fst` / 定理 `analyticOn_fst`

English:
theorem analyticOn_fst
  statement: AnalyticOn 𝕜 (fun p : E × F => p.fst) t
  proof: fun _ _ => analyticWithinAt_fst

中文:
定理 analyticOn_fst
  结论: AnalyticOn 𝕜 (fun p : E × F => p.fst) t
  证明: fun _ _ => analyticWithinAt_fst

Depends on / 依赖: analyticWithinAt_fst
-/
theorem analyticOn_fst : AnalyticOn 𝕜 (fun p : E × F => p.fst) t :=
  fun _ _ => analyticWithinAt_fst

/--
theorem `analyticOnNhd_snd` / 定理 `analyticOnNhd_snd`

English:
theorem analyticOnNhd_snd
  statement: AnalyticOnNhd 𝕜 (fun p : E × F => p.snd) t
  proof: fun _ _ => analyticAt_snd

中文:
定理 analyticOnNhd_snd
  结论: AnalyticOnNhd 𝕜 (fun p : E × F => p.snd) t
  证明: fun _ _ => analyticAt_snd

Depends on / 依赖: analyticAt_snd
-/
theorem analyticOnNhd_snd : AnalyticOnNhd 𝕜 (fun p : E × F => p.snd) t :=
  fun _ _ => analyticAt_snd

/--
theorem `analyticOn_snd` / 定理 `analyticOn_snd`

English:
theorem analyticOn_snd
  statement: AnalyticOn 𝕜 (fun p : E × F => p.snd) t
  proof: fun _ _ => analyticWithinAt_snd

中文:
定理 analyticOn_snd
  结论: AnalyticOn 𝕜 (fun p : E × F => p.snd) t
  证明: fun _ _ => analyticWithinAt_snd

Depends on / 依赖: analyticWithinAt_snd
-/
theorem analyticOn_snd : AnalyticOn 𝕜 (fun p : E × F => p.snd) t :=
  fun _ _ => analyticWithinAt_snd

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] F) (s : Set E) (x : E)

/--
theorem `analyticAt` / 定理 `analyticAt`

English:
theorem analyticAt
  statement: AnalyticAt 𝕜 f x
  proof: ((f : E ->L[𝕜] F).hasFPowerSeriesAt x).analyticAt

中文:
定理 analyticAt
  结论: AnalyticAt 𝕜 f x
  证明: ((f : E ->L[𝕜] F).hasFPowerSeriesAt x).analyticAt
-/
protected theorem analyticAt : AnalyticAt 𝕜 f x :=
  ((f : E ->L[𝕜] F).hasFPowerSeriesAt x).analyticAt

/--
theorem `analyticOnNhd` / 定理 `analyticOnNhd`

English:
theorem analyticOnNhd
  statement: AnalyticOnNhd 𝕜 f s
  proof: fun x _ => f.analyticAt x

中文:
定理 analyticOnNhd
  结论: AnalyticOnNhd 𝕜 f s
  证明: fun x _ => f.analyticAt x
-/
protected theorem analyticOnNhd : AnalyticOnNhd 𝕜 f s :=
  fun x _ => f.analyticAt x

/--
theorem `analyticWithinAt` / 定理 `analyticWithinAt`

English:
theorem analyticWithinAt
  statement: AnalyticWithinAt 𝕜 f s x
  proof: (f.analyticAt x).analyticWithinAt

中文:
定理 analyticWithinAt
  结论: AnalyticWithinAt 𝕜 f s x
  证明: (f.analyticAt x).analyticWithinAt
-/
protected theorem analyticWithinAt : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt

/--
theorem `analyticOn` / 定理 `analyticOn`

English:
theorem analyticOn
  statement: AnalyticOn 𝕜 f s
  proof: fun x _ => f.analyticWithinAt _ x

中文:
定理 analyticOn
  结论: AnalyticOn 𝕜 f s
  证明: fun x _ => f.analyticWithinAt _ x
-/
protected theorem analyticOn : AnalyticOn 𝕜 f s :=
  fun x _ => f.analyticWithinAt _ x

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable (f : E ≃ₗᵢ[𝕜] F) (s : Set E) (x : E)

/--
theorem `analyticAt` / 定理 `analyticAt`

English:
theorem analyticAt
  statement: AnalyticAt 𝕜 f x
  proof: ((f : E ->L[𝕜] F).hasFPowerSeriesAt x).analyticAt

中文:
定理 analyticAt
  结论: AnalyticAt 𝕜 f x
  证明: ((f : E ->L[𝕜] F).hasFPowerSeriesAt x).analyticAt
-/
protected theorem analyticAt : AnalyticAt 𝕜 f x :=
  ((f : E ->L[𝕜] F).hasFPowerSeriesAt x).analyticAt

/--
theorem `analyticOnNhd` / 定理 `analyticOnNhd`

English:
theorem analyticOnNhd
  statement: AnalyticOnNhd 𝕜 f s
  proof: fun x _ => f.analyticAt x

中文:
定理 analyticOnNhd
  结论: AnalyticOnNhd 𝕜 f s
  证明: fun x _ => f.analyticAt x
-/
protected theorem analyticOnNhd : AnalyticOnNhd 𝕜 f s :=
  fun x _ => f.analyticAt x

/--
theorem `analyticWithinAt` / 定理 `analyticWithinAt`

English:
theorem analyticWithinAt
  statement: AnalyticWithinAt 𝕜 f s x
  proof: (f.analyticAt x).analyticWithinAt

中文:
定理 analyticWithinAt
  结论: AnalyticWithinAt 𝕜 f s x
  证明: (f.analyticAt x).analyticWithinAt
-/
protected theorem analyticWithinAt : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt

/--
theorem `analyticOn` / 定理 `analyticOn`

English:
theorem analyticOn
  statement: AnalyticOn 𝕜 f s
  proof: fun x _ => f.analyticWithinAt _ x

中文:
定理 analyticOn
  结论: AnalyticOn 𝕜 f s
  证明: fun x _ => f.analyticWithinAt _ x
-/
protected theorem analyticOn : AnalyticOn 𝕜 f s :=
  fun x _ => f.analyticWithinAt _ x

end LinearIsometryEquiv
