/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Angles between vectors

This file defines unoriented angles in real inner product spaces.

## Main definitions

* `InnerProductGeometry.angle` is the undirected angle between two vectors.
-/

@[expose] public section


assert_not_exists HasFDerivAt ConformalAt

noncomputable section

open Real Set

open RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] {x y : V}

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. See `Orientation.oangle` for the corresponding oriented angle
definition. -/
@[wikidata Q11352]
/--
Definition of `angle` / `angle` 的定义

English:
definition angle
  signature: (x y : V)
  body: Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))

中文:
定义 angle
  签名: (x y : V)
  定义体: Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))

Depends on / 依赖: Real.arccos, arccos
-/
def angle (x y : V) : Real :=
  Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))

/--
theorem `continuousAt_angle` / 定理 `continuousAt_angle`

English:
theorem continuousAt_angle
  given: {x : V × V} (hx1 : x.1 != 0) (hx2 : x.2 != 0)
  proof: by
  unfold angle
  fun_prop (disch := simp [*])

中文:
定理 continuousAt_angle
  条件: {x : V × V} (hx1 : x.1 != 0) (hx2 : x.2 != 0)
  证明: by
  unfold angle
  fun_prop (disch := simp [*])

Depends on / 依赖: fun_prop
-/
theorem continuousAt_angle {x : V × V} (hx1 : x.1 != 0) (hx2 : x.2 != 0) :
    ContinuousAt (fun y : V × V => angle y.1 y.2) x := by
  unfold angle
  fun_prop (disch := simp [*])

/--
theorem `angle_smul_smul` / 定理 `angle_smul_smul`

English:
theorem angle_smul_smul
  given: {c : Real} (hc : c != 0) (x y : V)
  statement: angle (c • x) (c • y) = angle x y
  proof: by
  have : c * c != 0 := mul_ne_zero hc hc
  rw [angle]; rw [angle]; rw [real_inner_smul_left]; rw [inner_smul_right]; rw [norm_smul]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [mul_mul_mul_comm _ ‖x‖]; rw [abs_mul_abs_self]; rw [← mul_assoc c c]; rw [mul_div_mul_left _ _ this]

@[simp]

中文:
定理 angle_smul_smul
  条件: {c : 实数} (hc : c != 0) (x y : V)
  结论: angle (c • x) (c • y) = angle x y
  证明: by
  have : c * c != 0 := mul_ne_zero hc hc
  rw [angle]; rw [angle]; rw [real_inner_smul_left]; rw [inner_smul_right]; rw [norm_smul]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [mul_mul_mul_comm _ ‖x‖]; rw [abs_mul_abs_self]; rw [← mul_assoc c c]; rw [mul_div_mul_left _ _ this]

@[simp]

Depends on / 依赖: Real.norm_eq_abs, abs_mul_abs_self, inner_smul_right, mul_assoc, mul_div_mul_left, mul_mul_mul_comm, mul_ne_zero, norm_eq_abs, norm_smul, real_inner_smul_left
-/
theorem angle_smul_smul {c : Real} (hc : c != 0) (x y : V) : angle (c • x) (c • y) = angle x y := by
  have : c * c != 0 := mul_ne_zero hc hc
  rw [angle]; rw [angle]; rw [real_inner_smul_left]; rw [inner_smul_right]; rw [norm_smul]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [mul_mul_mul_comm _ ‖x‖]; rw [abs_mul_abs_self]; rw [← mul_assoc c c]; rw [mul_div_mul_left _ _ this]

@[simp]
/--
theorem `_root_.LinearIsometry.angle_map` / 定理 `_root_.LinearIsometry.angle_map`

English:
theorem _root_.LinearIsometry.angle_map
  statement: {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  proof: by
  rw [angle]; rw [angle]; rw [f.inner_map_map]; rw [f.norm_map]; rw [f.norm_map]

@[simp, norm_cast]

中文:
定理 _root_.线性等距.angle_map
  结论: {E F : 类型} [赋范交换加群 E] [赋范交换加群 F]
  证明: by
  rw [angle]; rw [angle]; rw [f.inner_map_map]; rw [f.norm_map]; rw [f.norm_map]

@[simp, norm_cast]

Depends on / 依赖: f.inner_map_map, f.norm_map, inner_map_map, norm_map
-/
theorem _root_.LinearIsometry.angle_map {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace Real E] [InnerProductSpace Real F] (f : E ->ₗᵢ[Real] F) (u v : E) :
    angle (f u) (f v) = angle u v := by
  rw [angle]; rw [angle]; rw [f.inner_map_map]; rw [f.norm_map]; rw [f.norm_map]

@[simp, norm_cast]
/--
theorem `_root_.Submodule.angle_coe` / 定理 `_root_.Submodule.angle_coe`

English:
theorem _root_.Submodule.angle_coe
  given: {s : Submodule Real V} (x y : s)
  proof: s.subtypeₗᵢ.angle_map x y

中文:
定理 _root_.子模.angle_coe
  条件: {s : 子模 实数 V} (x y : s)
  证明: s.subtypeₗᵢ.angle_map x y

Depends on / 依赖: angle_map, s.subtype
-/
theorem _root_.Submodule.angle_coe {s : Submodule Real V} (x y : s) :
    angle (x : V) (y : V) = angle x y :=
  s.subtypeₗᵢ.angle_map x y

/--
theorem `cos_angle` / 定理 `cos_angle`

English:
theorem cos_angle
  given: (x y : V)
  statement: Real.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖)
  proof: Real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

中文:
定理 cos_angle
  条件: (x y : V)
  结论: 实数.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖)
  证明: Real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

Depends on / 依赖: Real.cos_arccos, abs_le, abs_le.mp, abs_real_inner_div_norm_mul_norm_le_one, cos_arccos
-/
theorem cos_angle (x y : V) : Real.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) :=
  Real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

/--
theorem `angle_comm` / 定理 `angle_comm`

English:
theorem angle_comm
  given: (x y : V)
  statement: angle x y = angle y x
  proof: by
  unfold angle
  rw [real_inner_comm]; rw [mul_comm]

中文:
定理 angle_comm
  条件: (x y : V)
  结论: angle x y = angle y x
  证明: by
  unfold angle
  rw [real_inner_comm]; rw [mul_comm]

Depends on / 依赖: mul_comm, real_inner_comm
-/
theorem angle_comm (x y : V) : angle x y = angle y x := by
  unfold angle
  rw [real_inner_comm]; rw [mul_comm]

/-- The angle between the negation of two vectors. -/
@[simp]
/--
theorem `angle_neg_neg` / 定理 `angle_neg_neg`

English:
theorem angle_neg_neg
  given: (x y : V)
  statement: angle (-x) (-y) = angle x y
  proof: by
  unfold angle
  rw [inner_neg_neg]; rw [norm_neg]; rw [norm_neg]

中文:
定理 angle_neg_neg
  条件: (x y : V)
  结论: angle (-x) (-y) = angle x y
  证明: by
  unfold angle
  rw [inner_neg_neg]; rw [norm_neg]; rw [norm_neg]

Depends on / 依赖: inner_neg_neg, norm_neg
-/
theorem angle_neg_neg (x y : V) : angle (-x) (-y) = angle x y := by
  unfold angle
  rw [inner_neg_neg]; rw [norm_neg]; rw [norm_neg]

/--
theorem `angle_nonneg` / 定理 `angle_nonneg`

English:
theorem angle_nonneg
  given: (x y : V)
  statement: 0 <= angle x y
  proof: Real.arccos_nonneg _

中文:
定理 angle_nonneg
  条件: (x y : V)
  结论: 0 <= angle x y
  证明: Real.arccos_nonneg _

Depends on / 依赖: Real.arccos_nonneg, arccos_nonneg
-/
theorem angle_nonneg (x y : V) : 0 <= angle x y :=
  Real.arccos_nonneg _

/--
theorem `angle_le_pi` / 定理 `angle_le_pi`

English:
theorem angle_le_pi
  given: (x y : V)
  statement: angle x y <= π
  proof: Real.arccos_le_pi _

中文:
定理 angle_le_pi
  条件: (x y : V)
  结论: angle x y <= π
  证明: Real.arccos_le_pi _

Depends on / 依赖: Real.arccos_le_pi, arccos_le_pi
-/
theorem angle_le_pi (x y : V) : angle x y <= π :=
  Real.arccos_le_pi _

/--
theorem `sin_angle_nonneg` / 定理 `sin_angle_nonneg`

English:
theorem sin_angle_nonneg
  given: (x y : V)
  statement: 0 <= sin (angle x y)
  proof: sin_nonneg_of_nonneg_of_le_pi (angle_nonneg x y) (angle_le_pi x y)

中文:
定理 sin_angle_nonneg
  条件: (x y : V)
  结论: 0 <= sin (angle x y)
  证明: sin_nonneg_of_nonneg_of_le_pi (angle_nonneg x y) (angle_le_pi x y)

Depends on / 依赖: angle_le_pi, angle_nonneg, sin_nonneg_of_nonneg_of_le_pi
-/
theorem sin_angle_nonneg (x y : V) : 0 <= sin (angle x y) :=
  sin_nonneg_of_nonneg_of_le_pi (angle_nonneg x y) (angle_le_pi x y)

/--
theorem `angle_neg_right` / 定理 `angle_neg_right`

English:
theorem angle_neg_right
  given: (x y : V)
  statement: angle x (-y) = π - angle x y
  proof: by
  unfold angle
  rw [← Real.arccos_neg]; rw [norm_neg]; rw [inner_neg_right]; rw [neg_div]

中文:
定理 angle_neg_right
  条件: (x y : V)
  结论: angle x (-y) = π - angle x y
  证明: by
  unfold angle
  rw [← Real.arccos_neg]; rw [norm_neg]; rw [inner_neg_right]; rw [neg_div]

Depends on / 依赖: Real.arccos_neg, arccos_neg, inner_neg_right, neg_div, norm_neg
-/
theorem angle_neg_right (x y : V) : angle x (-y) = π - angle x y := by
  unfold angle
  rw [← Real.arccos_neg]; rw [norm_neg]; rw [inner_neg_right]; rw [neg_div]

/--
theorem `angle_neg_left` / 定理 `angle_neg_left`

English:
theorem angle_neg_left
  given: (x y : V)
  statement: angle (-x) y = π - angle x y
  proof: by
  rw [← angle_neg_neg]; rw [neg_neg]; rw [angle_neg_right]

中文:
定理 angle_neg_left
  条件: (x y : V)
  结论: angle (-x) y = π - angle x y
  证明: by
  rw [← angle_neg_neg]; rw [neg_neg]; rw [angle_neg_right]

Depends on / 依赖: angle_neg_neg, angle_neg_right, neg_neg
-/
theorem angle_neg_left (x y : V) : angle (-x) y = π - angle x y := by
  rw [← angle_neg_neg]; rw [neg_neg]; rw [angle_neg_right]

/-- The angle between the zero vector and a vector. -/
@[simp]
/--
theorem `angle_zero_left` / 定理 `angle_zero_left`

English:
theorem angle_zero_left
  given: (x : V)
  statement: angle 0 x = π / 2
  proof: by
  unfold angle
  rw [inner_zero_left]; rw [zero_div]; rw [Real.arccos_zero]

中文:
定理 angle_zero_left
  条件: (x : V)
  结论: angle 0 x = π / 2
  证明: by
  unfold angle
  rw [inner_zero_left]; rw [zero_div]; rw [Real.arccos_zero]

Depends on / 依赖: Real.arccos_zero, arccos_zero, inner_zero_left, zero_div
-/
theorem angle_zero_left (x : V) : angle 0 x = π / 2 := by
  unfold angle
  rw [inner_zero_left]; rw [zero_div]; rw [Real.arccos_zero]

/-- The angle between a vector and the zero vector. -/
@[simp]
/--
theorem `angle_zero_right` / 定理 `angle_zero_right`

English:
theorem angle_zero_right
  given: (x : V)
  statement: angle x 0 = π / 2
  proof: by
  unfold angle
  rw [inner_zero_right]; rw [zero_div]; rw [Real.arccos_zero]

中文:
定理 angle_zero_right
  条件: (x : V)
  结论: angle x 0 = π / 2
  证明: by
  unfold angle
  rw [inner_zero_right]; rw [zero_div]; rw [Real.arccos_zero]

Depends on / 依赖: Real.arccos_zero, arccos_zero, inner_zero_right, zero_div
-/
theorem angle_zero_right (x : V) : angle x 0 = π / 2 := by
  unfold angle
  rw [inner_zero_right]; rw [zero_div]; rw [Real.arccos_zero]

/-- The angle between a nonzero vector and itself. -/
@[simp]
/--
theorem `angle_self` / 定理 `angle_self`

English:
theorem angle_self
  given: {x : V} (hx : x != 0)
  statement: angle x x = 0
  proof: by
  unfold angle
  rw [← real_inner_self_eq_norm_mul_norm]; rw [div_self (inner_self_ne_zero.2 hx : ⟪x]; rw [x⟫ != 0)]; rw [Real.arccos_one]

中文:
定理 angle_self
  条件: {x : V} (hx : x != 0)
  结论: angle x x = 0
  证明: by
  unfold angle
  rw [← real_inner_self_eq_norm_mul_norm]; rw [div_self (inner_self_ne_zero.2 hx : ⟪x]; rw [x⟫ != 0)]; rw [Real.arccos_one]

Depends on / 依赖: Real.arccos_one, arccos_one, div_self, inner_self_ne_zero, real_inner_self_eq_norm_mul_norm
-/
theorem angle_self {x : V} (hx : x != 0) : angle x x = 0 := by
  unfold angle
  rw [← real_inner_self_eq_norm_mul_norm]; rw [div_self (inner_self_ne_zero.2 hx : ⟪x]; rw [x⟫ != 0)]; rw [Real.arccos_one]

/-- The angle between a nonzero vector and its negation. -/
@[simp]
/--
theorem `angle_self_neg_of_nonzero` / 定理 `angle_self_neg_of_nonzero`

English:
theorem angle_self_neg_of_nonzero
  given: {x : V} (hx : x != 0)
  statement: angle x (-x) = π
  proof: by
  rw [angle_neg_right]; rw [angle_self hx]; rw [sub_zero]

中文:
定理 angle_self_neg_of_nonzero
  条件: {x : V} (hx : x != 0)
  结论: angle x (-x) = π
  证明: by
  rw [angle_neg_right]; rw [angle_self hx]; rw [sub_zero]

Depends on / 依赖: angle_neg_right, angle_self, sub_zero
-/
theorem angle_self_neg_of_nonzero {x : V} (hx : x != 0) : angle x (-x) = π := by
  rw [angle_neg_right]; rw [angle_self hx]; rw [sub_zero]

/-- The angle between the negation of a nonzero vector and that
vector. -/
@[simp]
/--
theorem `angle_neg_self_of_nonzero` / 定理 `angle_neg_self_of_nonzero`

English:
theorem angle_neg_self_of_nonzero
  given: {x : V} (hx : x != 0)
  statement: angle (-x) x = π
  proof: by
  rw [angle_comm]; rw [angle_self_neg_of_nonzero hx]

中文:
定理 angle_neg_self_of_nonzero
  条件: {x : V} (hx : x != 0)
  结论: angle (-x) x = π
  证明: by
  rw [angle_comm]; rw [angle_self_neg_of_nonzero hx]

Depends on / 依赖: angle_comm, angle_self_neg_of_nonzero
-/
theorem angle_neg_self_of_nonzero {x : V} (hx : x != 0) : angle (-x) x = π := by
  rw [angle_comm]; rw [angle_self_neg_of_nonzero hx]

/-- The angle between a vector and a positive multiple of a vector. -/
@[simp]
/--
theorem `angle_smul_right_of_pos` / 定理 `angle_smul_right_of_pos`

English:
theorem angle_smul_right_of_pos
  given: (x y : V) {r : Real} (hr : 0 < r)
  statement: angle x (r • y) = angle x y
  proof: by
  unfold angle
  rw [inner_smul_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg (le_of_lt hr)]; rw [← mul_assoc]; rw [mul_comm _ r]; rw [mul_assoc]; rw [mul_div_mul_left _ _ (ne_of_gt hr)]

中文:
定理 angle_smul_right_of_pos
  条件: (x y : V) {r : 实数} (hr : 0 < r)
  结论: angle x (r • y) = angle x y
  证明: by
  unfold angle
  rw [inner_smul_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg (le_of_lt hr)]; rw [← mul_assoc]; rw [mul_comm _ r]; rw [mul_assoc]; rw [mul_div_mul_left _ _ (ne_of_gt hr)]

Depends on / 依赖: Real.norm_eq_abs, abs_of_nonneg, inner_smul_right, le_of_lt, mul_assoc, mul_comm, mul_div_mul_left, ne_of_gt, norm_eq_abs, norm_smul
-/
theorem angle_smul_right_of_pos (x y : V) {r : Real} (hr : 0 < r) : angle x (r • y) = angle x y := by
  unfold angle
  rw [inner_smul_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg (le_of_lt hr)]; rw [← mul_assoc]; rw [mul_comm _ r]; rw [mul_assoc]; rw [mul_div_mul_left _ _ (ne_of_gt hr)]

/-- The angle between a positive multiple of a vector and a vector. -/
@[simp]
/--
theorem `angle_smul_left_of_pos` / 定理 `angle_smul_left_of_pos`

English:
theorem angle_smul_left_of_pos
  given: (x y : V) {r : Real} (hr : 0 < r)
  statement: angle (r • x) y = angle x y
  proof: by
  rw [angle_comm]; rw [angle_smul_right_of_pos y x hr]; rw [angle_comm]

中文:
定理 angle_smul_left_of_pos
  条件: (x y : V) {r : 实数} (hr : 0 < r)
  结论: angle (r • x) y = angle x y
  证明: by
  rw [angle_comm]; rw [angle_smul_right_of_pos y x hr]; rw [angle_comm]

Depends on / 依赖: angle_comm, angle_smul_right_of_pos
-/
theorem angle_smul_left_of_pos (x y : V) {r : Real} (hr : 0 < r) : angle (r • x) y = angle x y := by
  rw [angle_comm]; rw [angle_smul_right_of_pos y x hr]; rw [angle_comm]

/-- The angle between a vector and a negative multiple of a vector. -/
@[simp]
/--
theorem `angle_smul_right_of_neg` / 定理 `angle_smul_right_of_neg`

English:
theorem angle_smul_right_of_neg
  given: (x y : V) {r : Real} (hr : r < 0)
  proof: by
  rw [← neg_neg r]; rw [neg_smul]; rw [angle_neg_right]; rw [angle_smul_right_of_pos x y (neg_pos_of_neg hr)]; rw [angle_neg_right]

中文:
定理 angle_smul_right_of_neg
  条件: (x y : V) {r : 实数} (hr : r < 0)
  证明: by
  rw [← neg_neg r]; rw [neg_smul]; rw [angle_neg_right]; rw [angle_smul_right_of_pos x y (neg_pos_of_neg hr)]; rw [angle_neg_right]

Depends on / 依赖: angle_neg_right, angle_smul_right_of_pos, neg_neg, neg_pos_of_neg, neg_smul
-/
theorem angle_smul_right_of_neg (x y : V) {r : Real} (hr : r < 0) :
    angle x (r • y) = angle x (-y) := by
  rw [← neg_neg r]; rw [neg_smul]; rw [angle_neg_right]; rw [angle_smul_right_of_pos x y (neg_pos_of_neg hr)]; rw [angle_neg_right]

/-- The angle between a negative multiple of a vector and a vector. -/
@[simp]
/--
theorem `angle_smul_left_of_neg` / 定理 `angle_smul_left_of_neg`

English:
theorem angle_smul_left_of_neg
  given: (x y : V) {r : Real} (hr : r < 0)
  statement: angle (r • x) y = angle (-x) y
  proof: by
  rw [angle_comm]; rw [angle_smul_right_of_neg y x hr]; rw [angle_comm]

中文:
定理 angle_smul_left_of_neg
  条件: (x y : V) {r : 实数} (hr : r < 0)
  结论: angle (r • x) y = angle (-x) y
  证明: by
  rw [angle_comm]; rw [angle_smul_right_of_neg y x hr]; rw [angle_comm]

Depends on / 依赖: angle_comm, angle_smul_right_of_neg
-/
theorem angle_smul_left_of_neg (x y : V) {r : Real} (hr : r < 0) : angle (r • x) y = angle (-x) y := by
  rw [angle_comm]; rw [angle_smul_right_of_neg y x hr]; rw [angle_comm]

/--
theorem `cos_angle_mul_norm_mul_norm` / 定理 `cos_angle_mul_norm_mul_norm`

English:
theorem cos_angle_mul_norm_mul_norm
  given: (x y : V)
  statement: Real.cos (angle x y) * (‖x‖ * ‖y‖) = ⟪x, y⟫
  proof: by
  rw [cos_angle]; rw [div_mul_cancel_of_imp]
  simp +contextual [or_imp]

中文:
定理 cos_angle_mul_norm_mul_norm
  条件: (x y : V)
  结论: 实数.cos (angle x y) * (‖x‖ * ‖y‖) = ⟪x, y⟫
  证明: by
  rw [cos_angle]; rw [div_mul_cancel_of_imp]
  simp +contextual [or_imp]

Depends on / 依赖: contextual, cos_angle, div_mul_cancel_of_imp, or_imp
-/
theorem cos_angle_mul_norm_mul_norm (x y : V) : Real.cos (angle x y) * (‖x‖ * ‖y‖) = ⟪x, y⟫ := by
  rw [cos_angle]; rw [div_mul_cancel_of_imp]
  simp +contextual [or_imp]

/--
theorem `sin_angle_mul_norm_mul_norm` / 定理 `sin_angle_mul_norm_mul_norm`

English:
theorem sin_angle_mul_norm_mul_norm
  given: (x y : V)
  proof: by
  unfold angle
  rw [Real.sin_arccos]
  nth_rw 2 [← Real.sqrt_sq (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
  rw [← Real.sqrt_mul' _ (by positivity)]; rw [sq]
  rcases eq_or_ne x 0 with (rfl | hx); · simp
  rcases eq_or_ne y 0 with (rfl | hy); · simp
  simp only [real_inner_self_eq_norm_mul_no

中文:
定理 sin_angle_mul_norm_mul_norm
  条件: (x y : V)
  证明: by
  unfold angle
  rw [Real.sin_arccos]
  nth_rw 2 [← Real.sqrt_sq (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
  rw [← Real.sqrt_mul' _ (by positivity)]; rw [sq]
  rcases eq_or_ne x 0 with (rfl | hx); · simp
  rcases eq_or_ne y 0 with (rfl | hy); · simp
  simp only [real_inner_self_eq_norm_mul_no

Depends on / 依赖: Real.sin_arccos, Real.sqrt_mul, Real.sqrt_sq, eq_or_ne, mul_nonneg, norm_nonneg, nth_rw, real_inner_self_eq_norm_mul_norm, sin_arccos, sqrt_mul, sqrt_sq
-/
theorem sin_angle_mul_norm_mul_norm (x y : V) :
    Real.sin (angle x y) * (‖x‖ * ‖y‖) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) := by
  unfold angle
  rw [Real.sin_arccos]
  nth_rw 2 [← Real.sqrt_sq (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
  rw [← Real.sqrt_mul' _ (by positivity)]; rw [sq]
  rcases eq_or_ne x 0 with (rfl | hx); · simp
  rcases eq_or_ne y 0 with (rfl | hy); · simp
  simp only [real_inner_self_eq_norm_mul_norm]
  field_simp

/--
theorem `sin_angle` / 定理 `sin_angle`

English:
theorem sin_angle
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  rw [← sin_angle_mul_norm_mul_norm]
  field

中文:
定理 sin_angle
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  rw [← sin_angle_mul_norm_mul_norm]
  field

Depends on / 依赖: sin_angle_mul_norm_mul_norm
-/
theorem sin_angle {x y : V} (hx : x != 0) (hy : y != 0) :
    Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) / (‖x‖ * ‖y‖) := by
  rw [← sin_angle_mul_norm_mul_norm]
  field

/--
theorem `sin_angle_add` / 定理 `sin_angle_add`

English:
theorem sin_angle_add
  given: {x y : V} (hx : x != 0) (hy : x + y != 0)
  proof: by
  rw [sin_angle hx hy]
  field_simp
  simp only [inner_add_left, inner_add_right, real_inner_comm]
  ring_nf

中文:
定理 sin_angle_add
  条件: {x y : V} (hx : x != 0) (hy : x + y != 0)
  证明: by
  rw [sin_angle hx hy]
  field_simp
  simp only [inner_add_left, inner_add_right, real_inner_comm]
  ring_nf

Depends on / 依赖: inner_add_left, inner_add_right, real_inner_comm, ring_nf, sin_angle
-/
theorem sin_angle_add {x y : V} (hx : x != 0) (hy : x + y != 0) :
    Real.sin (angle x (x + y)) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) / (‖x‖ * ‖x + y‖) := by
  rw [sin_angle hx hy]
  field_simp
  simp only [inner_add_left, inner_add_right, real_inner_comm]
  ring_nf

/--
theorem `angle_eq_zero_iff` / 定理 `angle_eq_zero_iff`

English:
theorem angle_eq_zero_iff
  given: {x y : V}
  statement: angle x y = 0 ↔ x != 0 ∧ exists r : Real, 0 < r ∧ y = r • x
  proof: by
  rw [angle]; rw [← real_inner_div_norm_mul_norm_eq_one_iff]; rw [Real.arccos_eq_zero]; rw [LE.le.ge_iff_eq']; rw [eq_comm]
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

中文:
定理 angle_eq_zero_iff
  条件: {x y : V}
  结论: angle x y = 0 ↔ x != 0 ∧ 存在 r : 实数, 0 < r ∧ y = r • x
  证明: by
  rw [angle]; rw [← real_inner_div_norm_mul_norm_eq_one_iff]; rw [Real.arccos_eq_zero]; rw [LE.le.ge_iff_eq']; rw [eq_comm]
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

Depends on / 依赖: LE.le.ge_iff_eq, Real.arccos_eq_zero, abs_le, abs_le.mp, abs_real_inner_div_norm_mul_norm_le_one, arccos_eq_zero, eq_comm, ge_iff_eq, real_inner_div_norm_mul_norm_eq_one_iff
-/
theorem angle_eq_zero_iff {x y : V} : angle x y = 0 ↔ x != 0 ∧ exists r : Real, 0 < r ∧ y = r • x := by
  rw [angle]; rw [← real_inner_div_norm_mul_norm_eq_one_iff]; rw [Real.arccos_eq_zero]; rw [LE.le.ge_iff_eq']; rw [eq_comm]
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

/--
theorem `angle_eq_pi_iff` / 定理 `angle_eq_pi_iff`

English:
theorem angle_eq_pi_iff
  given: {x y : V}
  statement: angle x y = π ↔ x != 0 ∧ exists r : Real, r < 0 ∧ y = r • x
  proof: by
  rw [angle]; rw [← real_inner_div_norm_mul_norm_eq_neg_one_iff]; rw [Real.arccos_eq_pi]; rw [LE.le.ge_iff_eq']
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1

中文:
定理 angle_eq_pi_iff
  条件: {x y : V}
  结论: angle x y = π ↔ x != 0 ∧ 存在 r : 实数, r < 0 ∧ y = r • x
  证明: by
  rw [angle]; rw [← real_inner_div_norm_mul_norm_eq_neg_one_iff]; rw [Real.arccos_eq_pi]; rw [LE.le.ge_iff_eq']
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1

Depends on / 依赖: LE.le.ge_iff_eq, Real.arccos_eq_pi, abs_le, abs_le.mp, abs_real_inner_div_norm_mul_norm_le_one, arccos_eq_pi, ge_iff_eq, real_inner_div_norm_mul_norm_eq_neg_one_iff
-/
theorem angle_eq_pi_iff {x y : V} : angle x y = π ↔ x != 0 ∧ exists r : Real, r < 0 ∧ y = r • x := by
  rw [angle]; rw [← real_inner_div_norm_mul_norm_eq_neg_one_iff]; rw [Real.arccos_eq_pi]; rw [LE.le.ge_iff_eq']
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1

/--
theorem `angle_add_angle_eq_pi_of_angle_eq_pi` / 定理 `angle_add_angle_eq_pi_of_angle_eq_pi`

English:
theorem angle_add_angle_eq_pi_of_angle_eq_pi
  given: {x y : V} (z : V) (h : angle x y = π)
  proof: by
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩
  rw [angle_smul_left_of_neg x z hr]; rw [angle_neg_left]; rw [add_sub_cancel]

中文:
定理 angle_add_angle_eq_pi_of_angle_eq_pi
  条件: {x y : V} (z : V) (h : angle x y = π)
  证明: by
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩
  rw [angle_smul_left_of_neg x z hr]; rw [angle_neg_left]; rw [add_sub_cancel]

Depends on / 依赖: add_sub_cancel, angle_eq_pi_iff, angle_neg_left, angle_smul_left_of_neg
-/
theorem angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} (z : V) (h : angle x y = π) :
    angle x z + angle y z = π := by
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩
  rw [angle_smul_left_of_neg x z hr]; rw [angle_neg_left]; rw [add_sub_cancel]

/--
theorem `inner_eq_zero_iff_angle_eq_pi_div_two` / 定理 `inner_eq_zero_iff_angle_eq_pi_div_two`

English:
theorem inner_eq_zero_iff_angle_eq_pi_div_two
  given: (x y : V)
  statement: ⟪x, y⟫ = 0 ↔ angle x y = π / 2
  proof: Iff.symm by simp +contextual [angle, or_imp]

中文:
定理 inner_eq_zero_iff_angle_eq_pi_div_two
  条件: (x y : V)
  结论: ⟪x, y⟫ = 0 ↔ angle x y = π / 2
  证明: Iff.symm by simp +contextual [angle, or_imp]

Depends on / 依赖: Iff.symm, contextual, or_imp
-/
theorem inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2 :=
Iff.symm by simp +contextual [angle, or_imp]

/--
theorem `inner_eq_neg_mul_norm_of_angle_eq_pi` / 定理 `inner_eq_neg_mul_norm_of_angle_eq_pi`

English:
theorem inner_eq_neg_mul_norm_of_angle_eq_pi
  given: {x y : V} (h : angle x y = π)
  proof: by
  simp [← cos_angle_mul_norm_mul_norm, h]

中文:
定理 inner_eq_neg_mul_norm_of_angle_eq_pi
  条件: {x y : V} (h : angle x y = π)
  证明: by
  simp [← cos_angle_mul_norm_mul_norm, h]

Depends on / 依赖: cos_angle_mul_norm_mul_norm
-/
theorem inner_eq_neg_mul_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) :
    ⟪x, y⟫ = -(‖x‖ * ‖y‖) := by
  simp [← cos_angle_mul_norm_mul_norm, h]

/--
theorem `inner_eq_mul_norm_of_angle_eq_zero` / 定理 `inner_eq_mul_norm_of_angle_eq_zero`

English:
theorem inner_eq_mul_norm_of_angle_eq_zero
  given: {x y : V} (h : angle x y = 0)
  statement: ⟪x, y⟫ = ‖x‖ * ‖y‖
  proof: by
  simp [← cos_angle_mul_norm_mul_norm, h]

中文:
定理 inner_eq_mul_norm_of_angle_eq_zero
  条件: {x y : V} (h : angle x y = 0)
  结论: ⟪x, y⟫ = ‖x‖ * ‖y‖
  证明: by
  simp [← cos_angle_mul_norm_mul_norm, h]

Depends on / 依赖: cos_angle_mul_norm_mul_norm
-/
theorem inner_eq_mul_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ⟪x, y⟫ = ‖x‖ * ‖y‖ := by
  simp [← cos_angle_mul_norm_mul_norm, h]

/--
theorem `inner_eq_neg_mul_norm_iff_angle_eq_pi` / 定理 `inner_eq_neg_mul_norm_iff_angle_eq_pi`

English:
theorem inner_eq_neg_mul_norm_iff_angle_eq_pi
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  refine ⟨fun h => ?_, inner_eq_neg_mul_norm_of_angle_eq_pi⟩
  have h₁ : ‖x‖ * ‖y‖ != 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle]; rw [h]; rw [neg_div]; rw [div_self h₁]; rw [Real.arccos_neg_one]

中文:
定理 inner_eq_neg_mul_norm_iff_angle_eq_pi
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  refine ⟨fun h => ?_, inner_eq_neg_mul_norm_of_angle_eq_pi⟩
  have h₁ : ‖x‖ * ‖y‖ != 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle]; rw [h]; rw [neg_div]; rw [div_self h₁]; rw [Real.arccos_neg_one]

Depends on / 依赖: Real.arccos_neg_one, arccos_neg_one, div_self, inner_eq_neg_mul_norm_of_angle_eq_pi, mul_pos, neg_div, norm_pos_iff, norm_pos_iff.mpr
-/
theorem inner_eq_neg_mul_norm_iff_angle_eq_pi {x y : V} (hx : x != 0) (hy : y != 0) :
    ⟪x, y⟫ = -(‖x‖ * ‖y‖) ↔ angle x y = π := by
  refine ⟨fun h => ?_, inner_eq_neg_mul_norm_of_angle_eq_pi⟩
  have h₁ : ‖x‖ * ‖y‖ != 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle]; rw [h]; rw [neg_div]; rw [div_self h₁]; rw [Real.arccos_neg_one]

/--
theorem `inner_eq_mul_norm_iff_angle_eq_zero` / 定理 `inner_eq_mul_norm_iff_angle_eq_zero`

English:
theorem inner_eq_mul_norm_iff_angle_eq_zero
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  refine ⟨fun h => ?_, inner_eq_mul_norm_of_angle_eq_zero⟩
  have h₁ : ‖x‖ * ‖y‖ != 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle]; rw [h]; rw [div_self h₁]; rw [Real.arccos_one]

中文:
定理 inner_eq_mul_norm_iff_angle_eq_zero
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  refine ⟨fun h => ?_, inner_eq_mul_norm_of_angle_eq_zero⟩
  have h₁ : ‖x‖ * ‖y‖ != 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle]; rw [h]; rw [div_self h₁]; rw [Real.arccos_one]

Depends on / 依赖: Real.arccos_one, arccos_one, div_self, inner_eq_mul_norm_of_angle_eq_zero, mul_pos, norm_pos_iff, norm_pos_iff.mpr
-/
theorem inner_eq_mul_norm_iff_angle_eq_zero {x y : V} (hx : x != 0) (hy : y != 0) :
    ⟪x, y⟫ = ‖x‖ * ‖y‖ ↔ angle x y = 0 := by
  refine ⟨fun h => ?_, inner_eq_mul_norm_of_angle_eq_zero⟩
  have h₁ : ‖x‖ * ‖y‖ != 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle]; rw [h]; rw [div_self h₁]; rw [Real.arccos_one]

/--
theorem `norm_sub_eq_add_norm_of_angle_eq_pi` / 定理 `norm_sub_eq_add_norm_of_angle_eq_pi`

English:
theorem norm_sub_eq_add_norm_of_angle_eq_pi
  given: {x y : V} (h : angle x y = π)
  proof: by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]; rw [norm_sub_pow_two_real]; rw [inner_eq_neg_mul_norm_of_angle_eq_pi h]
  ring

中文:
定理 norm_sub_eq_add_norm_of_angle_eq_pi
  条件: {x y : V} (h : angle x y = π)
  证明: by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]; rw [norm_sub_pow_two_real]; rw [inner_eq_neg_mul_norm_of_angle_eq_pi h]
  ring

Depends on / 依赖: add_nonneg, inner_eq_neg_mul_norm_of_angle_eq_pi, norm_nonneg, norm_sub_pow_two_real
-/
theorem norm_sub_eq_add_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) :
    ‖x - y‖ = ‖x‖ + ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]; rw [norm_sub_pow_two_real]; rw [inner_eq_neg_mul_norm_of_angle_eq_pi h]
  ring

/--
theorem `norm_add_eq_add_norm_of_angle_eq_zero` / 定理 `norm_add_eq_add_norm_of_angle_eq_zero`

English:
theorem norm_add_eq_add_norm_of_angle_eq_zero
  given: {x y : V} (h : angle x y = 0)
  proof: by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]; rw [norm_add_pow_two_real]; rw [inner_eq_mul_norm_of_angle_eq_zero h]
  ring

中文:
定理 norm_add_eq_add_norm_of_angle_eq_zero
  条件: {x y : V} (h : angle x y = 0)
  证明: by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]; rw [norm_add_pow_two_real]; rw [inner_eq_mul_norm_of_angle_eq_zero h]
  ring

Depends on / 依赖: add_nonneg, inner_eq_mul_norm_of_angle_eq_zero, norm_add_pow_two_real, norm_nonneg
-/
theorem norm_add_eq_add_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) :
    ‖x + y‖ = ‖x‖ + ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]; rw [norm_add_pow_two_real]; rw [inner_eq_mul_norm_of_angle_eq_zero h]
  ring

/--
theorem `norm_sub_eq_abs_sub_norm_of_angle_eq_zero` / 定理 `norm_sub_eq_abs_sub_norm_of_angle_eq_zero`

English:
theorem norm_sub_eq_abs_sub_norm_of_angle_eq_zero
  given: {x y : V} (h : angle x y = 0)
  proof: by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (abs_nonneg (‖x‖ - ‖y‖))]; rw [norm_sub_pow_two_real]; rw [inner_eq_mul_norm_of_angle_eq_zero h]; rw [sq_abs (‖x‖ - ‖y‖)]
  ring

中文:
定理 norm_sub_eq_abs_sub_norm_of_angle_eq_zero
  条件: {x y : V} (h : angle x y = 0)
  证明: by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (abs_nonneg (‖x‖ - ‖y‖))]; rw [norm_sub_pow_two_real]; rw [inner_eq_mul_norm_of_angle_eq_zero h]; rw [sq_abs (‖x‖ - ‖y‖)]
  ring

Depends on / 依赖: abs_nonneg, inner_eq_mul_norm_of_angle_eq_zero, norm_nonneg, norm_sub_pow_two_real, sq_abs
-/
theorem norm_sub_eq_abs_sub_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) :
    ‖x - y‖ = |‖x‖ - ‖y‖| := by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (abs_nonneg (‖x‖ - ‖y‖))]; rw [norm_sub_pow_two_real]; rw [inner_eq_mul_norm_of_angle_eq_zero h]; rw [sq_abs (‖x‖ - ‖y‖)]
  ring

/--
theorem `norm_sub_eq_add_norm_iff_angle_eq_pi` / 定理 `norm_sub_eq_add_norm_iff_angle_eq_pi`

English:
theorem norm_sub_eq_add_norm_iff_angle_eq_pi
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  refine ⟨fun h => ?_, norm_sub_eq_add_norm_of_angle_eq_pi⟩
  rw [← inner_eq_neg_mul_norm_iff_angle_eq_pi hx hy]
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x - y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  rw [← sq_eq_sq₀ hxy₁ hxy₂]; rw [norm_sub_pow_two_real] at h
  calc
    ⟪x, y⟫ = (‖x‖ ^ 2 + ‖y

中文:
定理 norm_sub_eq_add_norm_iff_angle_eq_pi
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  refine ⟨fun h => ?_, norm_sub_eq_add_norm_of_angle_eq_pi⟩
  rw [← inner_eq_neg_mul_norm_iff_angle_eq_pi hx hy]
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x - y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  rw [← sq_eq_sq₀ hxy₁ hxy₂]; rw [norm_sub_pow_two_real] at h
  calc
    ⟪x, y⟫ = (‖x‖ ^ 2 + ‖y

Depends on / 依赖: add_nonneg, inner_eq_neg_mul_norm_iff_angle_eq_pi, norm_nonneg, norm_sub_eq_add_norm_of_angle_eq_pi, norm_sub_pow_two_real
-/
theorem norm_sub_eq_add_norm_iff_angle_eq_pi {x y : V} (hx : x != 0) (hy : y != 0) :
    ‖x - y‖ = ‖x‖ + ‖y‖ ↔ angle x y = π := by
  refine ⟨fun h => ?_, norm_sub_eq_add_norm_of_angle_eq_pi⟩
  rw [← inner_eq_neg_mul_norm_iff_angle_eq_pi hx hy]
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x - y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  rw [← sq_eq_sq₀ hxy₁ hxy₂]; rw [norm_sub_pow_two_real] at h
  calc
    ⟪x, y⟫ = (‖x‖ ^ 2 + ‖y‖ ^ 2 - (‖x‖ + ‖y‖) ^ 2) / 2 := by linarith
    _ = -(‖x‖ * ‖y‖) := by ring

/--
theorem `norm_add_eq_add_norm_iff_angle_eq_zero` / 定理 `norm_add_eq_add_norm_iff_angle_eq_zero`

English:
theorem norm_add_eq_add_norm_iff_angle_eq_zero
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  refine ⟨?_, norm_add_eq_add_norm_of_angle_eq_zero⟩
  grind [inner_eq_mul_norm_iff_angle_eq_zero hx hy, norm_add_pow_two_real]

中文:
定理 norm_add_eq_add_norm_iff_angle_eq_zero
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  refine ⟨?_, norm_add_eq_add_norm_of_angle_eq_zero⟩
  grind [inner_eq_mul_norm_iff_angle_eq_zero hx hy, norm_add_pow_two_real]

Depends on / 依赖: inner_eq_mul_norm_iff_angle_eq_zero, norm_add_eq_add_norm_of_angle_eq_zero, norm_add_pow_two_real
-/
theorem norm_add_eq_add_norm_iff_angle_eq_zero {x y : V} (hx : x != 0) (hy : y != 0) :
    ‖x + y‖ = ‖x‖ + ‖y‖ ↔ angle x y = 0 := by
  refine ⟨?_, norm_add_eq_add_norm_of_angle_eq_zero⟩
  grind [inner_eq_mul_norm_iff_angle_eq_zero hx hy, norm_add_pow_two_real]

/--
theorem `norm_sub_eq_abs_sub_norm_iff_angle_eq_zero` / 定理 `norm_sub_eq_abs_sub_norm_iff_angle_eq_zero`

English:
theorem norm_sub_eq_abs_sub_norm_iff_angle_eq_zero
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  refine ⟨fun h => ?_, norm_sub_eq_abs_sub_norm_of_angle_eq_zero⟩
  rw [← inner_eq_mul_norm_iff_angle_eq_zero hx hy]
  have h1 : ‖x - y‖ ^ 2 = (‖x‖ - ‖y‖) ^ 2 := by
    rw [h]
    exact sq_abs (‖x‖ - ‖y‖)
  rw [norm_sub_pow_two_real] at h1
  calc
    ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2)

中文:
定理 norm_sub_eq_abs_sub_norm_iff_angle_eq_zero
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  refine ⟨fun h => ?_, norm_sub_eq_abs_sub_norm_of_angle_eq_zero⟩
  rw [← inner_eq_mul_norm_iff_angle_eq_zero hx hy]
  have h1 : ‖x - y‖ ^ 2 = (‖x‖ - ‖y‖) ^ 2 := by
    rw [h]
    exact sq_abs (‖x‖ - ‖y‖)
  rw [norm_sub_pow_two_real] at h1
  calc
    ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2)

Depends on / 依赖: inner_eq_mul_norm_iff_angle_eq_zero, norm_sub_eq_abs_sub_norm_of_angle_eq_zero, norm_sub_pow_two_real, sq_abs
-/
theorem norm_sub_eq_abs_sub_norm_iff_angle_eq_zero {x y : V} (hx : x != 0) (hy : y != 0) :
    ‖x - y‖ = |‖x‖ - ‖y‖| ↔ angle x y = 0 := by
  refine ⟨fun h => ?_, norm_sub_eq_abs_sub_norm_of_angle_eq_zero⟩
  rw [← inner_eq_mul_norm_iff_angle_eq_zero hx hy]
  have h1 : ‖x - y‖ ^ 2 = (‖x‖ - ‖y‖) ^ 2 := by
    rw [h]
    exact sq_abs (‖x‖ - ‖y‖)
  rw [norm_sub_pow_two_real] at h1
  calc
    ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by linarith
    _ = ‖x‖ * ‖y‖ := by ring

/--
theorem `norm_add_eq_norm_sub_iff_angle_eq_pi_div_two` / 定理 `norm_add_eq_norm_sub_iff_angle_eq_pi_div_two`

English:
theorem norm_add_eq_norm_sub_iff_angle_eq_pi_div_two
  given: (x y : V)
  proof: by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (norm_nonneg (x - y))]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two x y]; rw [norm_add_pow_two_real]; rw [norm_sub_pow_two_real]
  constructor <;> intro h <;> linarith

中文:
定理 norm_add_eq_norm_sub_iff_angle_eq_pi_div_two
  条件: (x y : V)
  证明: by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (norm_nonneg (x - y))]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two x y]; rw [norm_add_pow_two_real]; rw [norm_sub_pow_two_real]
  constructor <;> intro h <;> linarith

Depends on / 依赖: inner_eq_zero_iff_angle_eq_pi_div_two, norm_add_pow_two_real, norm_nonneg, norm_sub_pow_two_real
-/
theorem norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (x y : V) :
    ‖x + y‖ = ‖x - y‖ ↔ angle x y = π / 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (norm_nonneg (x - y))]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two x y]; rw [norm_add_pow_two_real]; rw [norm_sub_pow_two_real]
  constructor <;> intro h <;> linarith

/--
theorem `cos_eq_one_iff_angle_eq_zero` / 定理 `cos_eq_one_iff_angle_eq_zero`

English:
theorem cos_eq_one_iff_angle_eq_zero
  statement: cos (angle x y) = 1 ↔ angle x y = 0
  proof: by
  rw [← cos_zero]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (left_mem_Icc.2 pi_pos.le)

中文:
定理 cos_eq_one_iff_angle_eq_zero
  结论: cos (angle x y) = 1 ↔ angle x y = 0
  证明: by
  rw [← cos_zero]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (left_mem_Icc.2 pi_pos.le)

Depends on / 依赖: angle_le_pi, angle_nonneg, cos_zero, eq_iff, injOn_cos, injOn_cos.eq_iff, left_mem_Icc, pi_pos, pi_pos.le
-/
theorem cos_eq_one_iff_angle_eq_zero : cos (angle x y) = 1 ↔ angle x y = 0 := by
  rw [← cos_zero]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (left_mem_Icc.2 pi_pos.le)

/--
theorem `cos_eq_zero_iff_angle_eq_pi_div_two` / 定理 `cos_eq_zero_iff_angle_eq_pi_div_two`

English:
theorem cos_eq_zero_iff_angle_eq_pi_div_two
  statement: cos (angle x y) = 0 ↔ angle x y = π / 2
  proof: by
  rw [← cos_pi_div_two]
  apply injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩
  constructor <;> linarith [pi_pos]

中文:
定理 cos_eq_zero_iff_angle_eq_pi_div_two
  结论: cos (angle x y) = 0 ↔ angle x y = π / 2
  证明: by
  rw [← cos_pi_div_two]
  apply injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩
  constructor <;> linarith [pi_pos]

Depends on / 依赖: angle_le_pi, angle_nonneg, cos_pi_div_two, eq_iff, injOn_cos, injOn_cos.eq_iff, pi_pos
-/
theorem cos_eq_zero_iff_angle_eq_pi_div_two : cos (angle x y) = 0 ↔ angle x y = π / 2 := by
  rw [← cos_pi_div_two]
  apply injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩
  constructor <;> linarith [pi_pos]

/--
theorem `cos_eq_neg_one_iff_angle_eq_pi` / 定理 `cos_eq_neg_one_iff_angle_eq_pi`

English:
theorem cos_eq_neg_one_iff_angle_eq_pi
  statement: cos (angle x y) = -1 ↔ angle x y = π
  proof: by
  rw [← cos_pi]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (right_mem_Icc.2 pi_pos.le)

中文:
定理 cos_eq_neg_one_iff_angle_eq_pi
  结论: cos (angle x y) = -1 ↔ angle x y = π
  证明: by
  rw [← cos_pi]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (right_mem_Icc.2 pi_pos.le)

Depends on / 依赖: angle_le_pi, angle_nonneg, cos_pi, eq_iff, injOn_cos, injOn_cos.eq_iff, pi_pos, pi_pos.le, right_mem_Icc
-/
theorem cos_eq_neg_one_iff_angle_eq_pi : cos (angle x y) = -1 ↔ angle x y = π := by
  rw [← cos_pi]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (right_mem_Icc.2 pi_pos.le)

/--
theorem `sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi` / 定理 `sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi`

English:
theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi
  proof: by
  rw [sin_eq_zero_iff_cos_eq]; rw [cos_eq_one_iff_angle_eq_zero]; rw [cos_eq_neg_one_iff_angle_eq_pi]

中文:
定理 sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi
  证明: by
  rw [sin_eq_zero_iff_cos_eq]; rw [cos_eq_one_iff_angle_eq_zero]; rw [cos_eq_neg_one_iff_angle_eq_pi]

Depends on / 依赖: cos_eq_neg_one_iff_angle_eq_pi, cos_eq_one_iff_angle_eq_zero, sin_eq_zero_iff_cos_eq
-/
theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi :
    sin (angle x y) = 0 ↔ angle x y = 0 ∨ angle x y = π := by
  rw [sin_eq_zero_iff_cos_eq]; rw [cos_eq_one_iff_angle_eq_zero]; rw [cos_eq_neg_one_iff_angle_eq_pi]

/--
theorem `sin_eq_one_iff_angle_eq_pi_div_two` / 定理 `sin_eq_one_iff_angle_eq_pi_div_two`

English:
theorem sin_eq_one_iff_angle_eq_pi_div_two
  statement: sin (angle x y) = 1 ↔ angle x y = π / 2
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [h, sin_pi_div_two]⟩
  rw [← cos_eq_zero_iff_angle_eq_pi_div_two]; rw [← abs_eq_zero]; rw [abs_cos_eq_sqrt_one_sub_sin_sq]; rw [h]
  simp

中文:
定理 sin_eq_one_iff_angle_eq_pi_div_two
  结论: sin (angle x y) = 1 ↔ angle x y = π / 2
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [h, sin_pi_div_two]⟩
  rw [← cos_eq_zero_iff_angle_eq_pi_div_two]; rw [← abs_eq_zero]; rw [abs_cos_eq_sqrt_one_sub_sin_sq]; rw [h]
  simp

Depends on / 依赖: abs_cos_eq_sqrt_one_sub_sin_sq, abs_eq_zero, cos_eq_zero_iff_angle_eq_pi_div_two, sin_pi_div_two
-/
theorem sin_eq_one_iff_angle_eq_pi_div_two : sin (angle x y) = 1 ↔ angle x y = π / 2 := by
  refine ⟨fun h => ?_, fun h => by rw [h, sin_pi_div_two]⟩
  rw [← cos_eq_zero_iff_angle_eq_pi_div_two]; rw [← abs_eq_zero]; rw [abs_cos_eq_sqrt_one_sub_sin_sq]; rw [h]
  simp

/--
lemma `eq_of_angle_eq_zero_of_norm_eq` / 引理 `eq_of_angle_eq_zero_of_norm_eq`

English:
lemma eq_of_angle_eq_zero_of_norm_eq
  given: {x y : V} (hxy : angle x y = 0) (h : ‖x‖ = ‖y‖)
  statement: x = y
  proof: by
  grind [angle_eq_zero_iff, norm_smul, Real.norm_eq_abs, norm_ne_zero_iff, abs, one_smul]

中文:
引理 eq_of_angle_eq_zero_of_norm_eq
  条件: {x y : V} (hxy : angle x y = 0) (h : ‖x‖ = ‖y‖)
  结论: x = y
  证明: by
  grind [angle_eq_zero_iff, norm_smul, Real.norm_eq_abs, norm_ne_zero_iff, abs, one_smul]

Depends on / 依赖: Real.norm_eq_abs, angle_eq_zero_iff, norm_eq_abs, norm_ne_zero_iff, norm_smul, one_smul
-/
lemma eq_of_angle_eq_zero_of_norm_eq {x y : V} (hxy : angle x y = 0) (h : ‖x‖ = ‖y‖) : x = y := by
  grind [angle_eq_zero_iff, norm_smul, Real.norm_eq_abs, norm_ne_zero_iff, abs, one_smul]

/-- The angle between a normalized vector and another vector is equal to the angle
between the original vectors. -/
@[simp]
/--
lemma `angle_normalize_left` / 引理 `angle_normalize_left`

English:
lemma angle_normalize_left
  given: (x y : V)
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  · rw [NormedSpace.normalize, angle_smul_left_of_pos _ _ (by positivity)]

中文:
引理 angle_normalize_left
  条件: (x y : V)
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  · rw [NormedSpace.normalize, angle_smul_left_of_pos _ _ (by positivity)]

Depends on / 依赖: NormedSpace, NormedSpace.normalize, angle_smul_left_of_pos, normalize
-/
lemma angle_normalize_left (x y : V) :
    angle (NormedSpace.normalize x) y = angle x y := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [NormedSpace.normalize, angle_smul_left_of_pos _ _ (by positivity)]

/-- The angle between a vector and another normalized vector is equal to the angle
between the original vectors. -/
@[simp]
/--
lemma `angle_normalize_right` / 引理 `angle_normalize_right`

English:
lemma angle_normalize_right
  given: (x y : V)
  proof: by
  rw [angle_comm]; rw [angle_normalize_left]; rw [angle_comm]

中文:
引理 angle_normalize_right
  条件: (x y : V)
  证明: by
  rw [angle_comm]; rw [angle_normalize_left]; rw [angle_comm]

Depends on / 依赖: angle_comm, angle_normalize_left
-/
lemma angle_normalize_right (x y : V) :
    angle x (NormedSpace.normalize y) = angle x y := by
  rw [angle_comm]; rw [angle_normalize_left]; rw [angle_comm]

/--
lemma `inner_eq_cos_angle_of_norm_eq_one` / 引理 `inner_eq_cos_angle_of_norm_eq_one`

English:
lemma inner_eq_cos_angle_of_norm_eq_one
  given: {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  proof: by
  simp [cos_angle, hx, hy]

中文:
引理 inner_eq_cos_angle_of_norm_eq_one
  条件: {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  证明: by
  simp [cos_angle, hx, hy]

Depends on / 依赖: cos_angle
-/
lemma inner_eq_cos_angle_of_norm_eq_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = Real.cos (angle x y) := by
  simp [cos_angle, hx, hy]

end InnerProductGeometry
