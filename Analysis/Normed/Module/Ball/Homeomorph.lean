/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Oliver Nash
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Module

/-!
# (Local) homeomorphism between a normed space and a ball

In this file we show that a real (semi)normed vector space is homeomorphic to the unit ball.

We formalize it in two ways:

- as a `Homeomorph`, see `Homeomorph.unitBall`;
- as an `OpenPartialHomeomorph` with `source = Set.univ` and `target = Metric.ball (0 : E) 1`.

While the former approach is more natural, the latter approach provides us
with a globally defined inverse function which makes it easier to say
that this homeomorphism is in fact a diffeomorphism.

We also show that the unit ball `Metric.ball (0 : E) 1` is homeomorphic
to a ball of positive radius in an affine space over `E`, see `OpenPartialHomeomorph.unitBallBall`.

## Tags

homeomorphism, ball
-/

@[expose] public section

open Set Metric Pointwise
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace Real E]

noncomputable section

/-- Local homeomorphism between a real (semi)normed space and the unit ball.
See also `Homeomorph.unitBall`. -/
@[simps -isSimp]
/--
Definition of `OpenPartialHomeomorph.univUnitBall` / `OpenPartialHomeomorph.univUnitBall` 的定义

English:
definition OpenPartialHomeomorph.univUnitBall
  signature: : OpenPartialHomeomorph E E where
  body: (√(1 + ‖x‖ ^ 2))⁻¹ • x
  invFun y := (√(1 - ‖(y : E)‖ ^ 2))⁻¹ • (y : E)
  source := univ
  target := ball 0 1
  map_source' x _ := by
    have : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [mem_ball_zero_iff]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_inv]; rw [← _root_.div_eq_inv_mul]; rw [div_lt_

中文:
定义 OpenPartialHomeomorph.univUnitBall
  签名: : OpenPartialHomeomorph E E where
  定义体: (√(1 + ‖x‖ ^ 2))⁻¹ • x
  invFun y := (√(1 - ‖(y : E)‖ ^ 2))⁻¹ • (y : E)
  source := univ
  target := ball 0 1
  map_source' x _ := by
    have : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [mem_ball_zero_iff]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_inv]; rw [← _root_.div_eq_inv_mul]; rw [div_lt_
-/
def OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E where
  toFun x := (√(1 + ‖x‖ ^ 2))⁻¹ • x
  invFun y := (√(1 - ‖(y : E)‖ ^ 2))⁻¹ • (y : E)
  source := univ
  target := ball 0 1
  map_source' x _ := by
    have : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [mem_ball_zero_iff]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_inv]; rw [← _root_.div_eq_inv_mul]; rw [div_lt_one (abs_pos.mpr <| Real.sqrt_ne_zero'.mpr this)]; rw [← abs_norm x]; rw [← sq_lt_sq]; rw [abs_norm]; rw [Real.sq_sqrt this.le]
    exact lt_one_add _
  map_target' _ _ := trivial
  left_inv' x _ := by
    match_scalars
    simp [norm_smul]
    field_simp
    simp [sq_abs, Real.sq_sqrt (zero_lt_one_add_norm_sq x).le]
  right_inv' y hy := by
    have : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y, mem_ball_zero_iff.1 hy]
    match_scalars
    simp [norm_smul]
    field_simp
    simp [field, sq_abs, Real.sq_sqrt this.le]
  open_source := isOpen_univ
  open_target := isOpen_ball
  continuousOn_toFun := by
    suffices Continuous fun (x : E) => (√(1 + ‖x‖ ^ 2))⁻¹ by fun_prop
    exact Continuous.inv₀ (by fun_prop) fun x => Real.sqrt_ne_zero'.mpr (by positivity)
  continuousOn_invFun := by
    have : forall y in ball (0 : E) 1, √(1 - ‖(y : E)‖ ^ 2) != 0 := fun y hy => by
      rw [Real.sqrt_ne_zero']
      nlinarith [norm_nonneg y, mem_ball_zero_iff.1 hy]
    exact ContinuousOn.smul (ContinuousOn.inv₀
      (continuousOn_const.sub (continuous_norm.continuousOn.pow _)).sqrt this) continuousOn_id

@[simp]
/--
theorem `OpenPartialHomeomorph.univUnitBall_apply_zero` / 定理 `OpenPartialHomeomorph.univUnitBall_apply_zero`

English:
theorem OpenPartialHomeomorph.univUnitBall_apply_zero
  statement: univUnitBall (0 : E) = 0
  proof: by
  simp [OpenPartialHomeomorph.univUnitBall_apply]

@[simp]

中文:
定理 OpenPartialHomeomorph.univUnitBall_apply_zero
  结论: univUnitBall (0 : E) = 0
  证明: by
  simp [OpenPartialHomeomorph.univUnitBall_apply]

@[simp]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.univUnitBall_apply, univUnitBall_apply
-/
theorem OpenPartialHomeomorph.univUnitBall_apply_zero : univUnitBall (0 : E) = 0 := by
  simp [OpenPartialHomeomorph.univUnitBall_apply]

@[simp]
/--
theorem `OpenPartialHomeomorph.univUnitBall_symm_apply_zero` / 定理 `OpenPartialHomeomorph.univUnitBall_symm_apply_zero`

English:
theorem OpenPartialHomeomorph.univUnitBall_symm_apply_zero
  statement: univUnitBall.symm (0 : E) = 0
  proof: by
  simp [OpenPartialHomeomorph.univUnitBall_symm_apply]

中文:
定理 OpenPartialHomeomorph.univUnitBall_symm_apply_zero
  结论: univUnitBall.symm (0 : E) = 0
  证明: by
  simp [OpenPartialHomeomorph.univUnitBall_symm_apply]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.univUnitBall_symm_apply, univUnitBall_symm_apply
-/
theorem OpenPartialHomeomorph.univUnitBall_symm_apply_zero : univUnitBall.symm (0 : E) = 0 := by
  simp [OpenPartialHomeomorph.univUnitBall_symm_apply]

/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ‖x‖²)^(- ½) • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`Homeomorph.unitBall_apply_coe` and `Homeomorph.unitBall_symm_apply` as `@[simp]`.

See also `Homeomorph.contDiff_unitBall` and `OpenPartialHomeomorph.contDiffOn_unitBall_symm`
for smoothness properties that hold when `E` is an inner-product space. -/
@[simps! -isSimp]
/--
Definition of `Homeomorph.unitBall` / `Homeomorph.unitBall` 的定义

English:
definition Homeomorph.unitBall
  signature: : E ≃ₜ ball (0 : E) 1
  body: (Homeomorph.Set.univ _).symm.trans OpenPartialHomeomorph.univUnitBall.toHomeomorphSourceTarget

@[simp]

中文:
定义 同胚.unitBall
  签名: : E ≃ₜ ball (0 : E) 1
  定义体: (Homeomorph.Set.univ _).symm.trans OpenPartialHomeomorph.univUnitBall.toHomeomorphSourceTarget

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.Set.univ, OpenPartialHomeomorph, OpenPartialHomeomorph.univUnitBall.toHomeomorphSourceTarget, symm.trans, toHomeomorphSourceTarget, univUnitBall
-/
def Homeomorph.unitBall : E ≃ₜ ball (0 : E) 1 :=
  (Homeomorph.Set.univ _).symm.trans OpenPartialHomeomorph.univUnitBall.toHomeomorphSourceTarget

@[simp]
/--
theorem `Homeomorph.coe_unitBall_apply_zero` / 定理 `Homeomorph.coe_unitBall_apply_zero`

English:
theorem Homeomorph.coe_unitBall_apply_zero
  proof: OpenPartialHomeomorph.univUnitBall_apply_zero

中文:
定理 同胚.coe_unitBall_apply_zero
  证明: OpenPartialHomeomorph.univUnitBall_apply_zero

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.univUnitBall_apply_zero, univUnitBall_apply_zero
-/
theorem Homeomorph.coe_unitBall_apply_zero :
    (Homeomorph.unitBall (0 : E) : E) = 0 :=
  OpenPartialHomeomorph.univUnitBall_apply_zero

variable {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]

namespace OpenPartialHomeomorph

/-- Affine homeomorphism `(r • · +ᵥ c)` between a normed space and an add torsor over this space,
interpreted as an `OpenPartialHomeomorph` between `Metric.ball 0 1` and `Metric.ball c r`. -/
@[simps!]
/--
Definition of `unitBallBall` / `unitBallBall` 的定义

English:
definition unitBallBall
  signature: (c : P) (r : Real) (hr : 0 < r)
  body: ((Homeomorph.smulOfNeZero r hr.ne').trans
      (IsometryEquiv.vaddConst c).toHomeomorph).toOpenPartialHomeomorphOfImageEq
(ball 0 1) isOpen_ball (ball c r) by
    change (IsometryEquiv.vaddConst c) ∘ (r • ·) '' ball (0 : E) 1 = ball c r
    rw [image_comp]; rw [image_smul]; rw [smul_unitBall hr.ne'

中文:
定义 unitBallBall
  签名: (c : P) (r : 实数) (hr : 0 < r)
  定义体: ((Homeomorph.smulOfNeZero r hr.ne').trans
      (IsometryEquiv.vaddConst c).toHomeomorph).toOpenPartialHomeomorphOfImageEq
(ball 0 1) isOpen_ball (ball c r) by
    change (IsometryEquiv.vaddConst c) ∘ (r • ·) '' ball (0 : E) 1 = ball c r
    rw [image_comp]; rw [image_smul]; rw [smul_unitBall hr.ne'

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, IsometryEquiv, IsometryEquiv.image_ball, IsometryEquiv.vaddConst, abs_of_pos, hr.ne, image_ball, image_comp, image_smul, isOpen_ball, smulOfNeZero, smul_unitBall, toHomeomorph, toOpenPartialHomeomorphOfImageEq, vaddConst
-/
def unitBallBall (c : P) (r : Real) (hr : 0 < r) : OpenPartialHomeomorph E P :=
  ((Homeomorph.smulOfNeZero r hr.ne').trans
      (IsometryEquiv.vaddConst c).toHomeomorph).toOpenPartialHomeomorphOfImageEq
(ball 0 1) isOpen_ball (ball c r) by
    change (IsometryEquiv.vaddConst c) ∘ (r • ·) '' ball (0 : E) 1 = ball c r
    rw [image_comp]; rw [image_smul]; rw [smul_unitBall hr.ne']; rw [IsometryEquiv.image_ball]
    simp [abs_of_pos hr]

/--
Definition of `univBall` / `univBall` 的定义

English:
definition univBall
  signature: (c : P) (r : Real)
  body: if h : 0 < r then univUnitBall.trans' (unitBallBall c r h) rfl
  else (IsometryEquiv.vaddConst c).toHomeomorph.toOpenPartialHomeomorph

@[simp]

中文:
定义 univBall
  签名: (c : P) (r : 实数)
  定义体: if h : 0 < r then univUnitBall.trans' (unitBallBall c r h) rfl
  else (IsometryEquiv.vaddConst c).toHomeomorph.toOpenPartialHomeomorph

@[simp]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.vaddConst, toHomeomorph, toHomeomorph.toOpenPartialHomeomorph, toOpenPartialHomeomorph, unitBallBall, univUnitBall, univUnitBall.trans, vaddConst
-/
def univBall (c : P) (r : Real) : OpenPartialHomeomorph E P :=
  if h : 0 < r then univUnitBall.trans' (unitBallBall c r h) rfl
  else (IsometryEquiv.vaddConst c).toHomeomorph.toOpenPartialHomeomorph

@[simp]
/--
theorem `univBall_source` / 定理 `univBall_source`

English:
theorem univBall_source
  given: (c : P) (r : Real)
  statement: (univBall c r).source = univ
  proof: by
  unfold univBall; split_ifs <;> rfl

中文:
定理 univBall_source
  条件: (c : P) (r : 实数)
  结论: (univBall c r).source = univ
  证明: by
  unfold univBall; split_ifs <;> rfl

Depends on / 依赖: split_ifs, univBall
-/
theorem univBall_source (c : P) (r : Real) : (univBall c r).source = univ := by
  unfold univBall; split_ifs <;> rfl

/--
theorem `univBall_target` / 定理 `univBall_target`

English:
theorem univBall_target
  given: (c : P) {r : Real} (hr : 0 < r)
  statement: (univBall c r).target = ball c r
  proof: by
  rw [univBall]; rw [dif_pos hr]; rfl

中文:
定理 univBall_target
  条件: (c : P) {r : 实数} (hr : 0 < r)
  结论: (univBall c r).target = ball c r
  证明: by
  rw [univBall]; rw [dif_pos hr]; rfl

Depends on / 依赖: dif_pos, univBall
-/
theorem univBall_target (c : P) {r : Real} (hr : 0 < r) : (univBall c r).target = ball c r := by
  rw [univBall]; rw [dif_pos hr]; rfl

/--
theorem `ball_subset_univBall_target` / 定理 `ball_subset_univBall_target`

English:
theorem ball_subset_univBall_target
  given: (c : P) (r : Real)
  statement: ball c r subseteq (univBall c r).target
  proof: by
  by_cases hr : 0 < r
  · rw [univBall_target c hr]
  · rw [univBall, dif_neg hr]
    exact subset_univ _

中文:
定理 ball_subset_univBall_target
  条件: (c : P) (r : 实数)
  结论: ball c r subseteq (univBall c r).target
  证明: by
  by_cases hr : 0 < r
  · rw [univBall_target c hr]
  · rw [univBall, dif_neg hr]
    exact subset_univ _

Depends on / 依赖: dif_neg, subset_univ, univBall, univBall_target
-/
theorem ball_subset_univBall_target (c : P) (r : Real) : ball c r subseteq (univBall c r).target := by
  by_cases hr : 0 < r
  · rw [univBall_target c hr]
  · rw [univBall, dif_neg hr]
    exact subset_univ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `univBall_apply_zero` / 定理 `univBall_apply_zero`

English:
theorem univBall_apply_zero
  given: (c : P) (r : Real)
  statement: univBall c r 0 = c
  proof: by
  unfold univBall; split_ifs <;> simp

@[simp]

中文:
定理 univBall_apply_zero
  条件: (c : P) (r : 实数)
  结论: univBall c r 0 = c
  证明: by
  unfold univBall; split_ifs <;> simp

@[simp]

Depends on / 依赖: split_ifs, univBall
-/
theorem univBall_apply_zero (c : P) (r : Real) : univBall c r 0 = c := by
  unfold univBall; split_ifs <;> simp

@[simp]
/--
theorem `univBall_symm_apply_center` / 定理 `univBall_symm_apply_center`

English:
theorem univBall_symm_apply_center
  given: (c : P) (r : Real)
  statement: (univBall c r).symm c = 0
  proof: by
  have : 0 in (univBall c r).source := by simp
  simpa only [univBall_apply_zero] using (univBall c r).left_inv this

@[continuity]

中文:
定理 univBall_symm_apply_center
  条件: (c : P) (r : 实数)
  结论: (univBall c r).symm c = 0
  证明: by
  have : 0 in (univBall c r).source := by simp
  simpa only [univBall_apply_zero] using (univBall c r).left_inv this

@[continuity]

Depends on / 依赖: left_inv, source, univBall, univBall_apply_zero
-/
theorem univBall_symm_apply_center (c : P) (r : Real) : (univBall c r).symm c = 0 := by
  have : 0 in (univBall c r).source := by simp
  simpa only [univBall_apply_zero] using (univBall c r).left_inv this

@[continuity]
/--
theorem `continuous_univBall` / 定理 `continuous_univBall`

English:
theorem continuous_univBall
  given: (c : P) (r : Real)
  statement: Continuous (univBall c r)
  proof: by
  simpa [continuousOn_univ] using (univBall c r).continuousOn

中文:
定理 continuous_univBall
  条件: (c : P) (r : 实数)
  结论: 连续 (univBall c r)
  证明: by
  simpa [continuousOn_univ] using (univBall c r).continuousOn

Depends on / 依赖: continuousOn, continuousOn_univ, univBall
-/
theorem continuous_univBall (c : P) (r : Real) : Continuous (univBall c r) := by
  simpa [continuousOn_univ] using (univBall c r).continuousOn

/--
theorem `continuousOn_univBall_symm` / 定理 `continuousOn_univBall_symm`

English:
theorem continuousOn_univBall_symm
  given: (c : P) (r : Real)
  statement: ContinuousOn (univBall c r).symm (ball c r)
  proof: (univBall c r).symm.continuousOn.mono ball_subset_univBall_target c r

中文:
定理 continuousOn_univBall_symm
  条件: (c : P) (r : 实数)
  结论: ContinuousOn (univBall c r).symm (ball c r)
  证明: (univBall c r).symm.continuousOn.mono ball_subset_univBall_target c r

Depends on / 依赖: ball_subset_univBall_target, continuousOn, symm.continuousOn.mono, univBall
-/
theorem continuousOn_univBall_symm (c : P) (r : Real) : ContinuousOn (univBall c r).symm (ball c r) :=
(univBall c r).symm.continuousOn.mono ball_subset_univBall_target c r

end OpenPartialHomeomorph
