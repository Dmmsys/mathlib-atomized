/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/

public section


open Metric Set Pointwise Topology

variable {E : Type*}

section SeminormedGroup

variable [SeminormedGroup E] {s t : Set E}

-- note: we can't use `LipschitzOnWith.isBounded_image2` here without adding `[IsIsometricSMul E E]`
@[to_additive]
/--
theorem `Bornology.IsBounded.mul` / 定理 `Bornology.IsBounded.mul`

English:
theorem Bornology.IsBounded.mul
  given: (hs : IsBounded s) (ht : IsBounded t)
  statement: IsBounded (s * t)
  proof: by
  obtain ⟨Rs, hRs⟩ : exists R, forall x in s, ‖x‖ <= R := hs.exists_norm_le'
  obtain ⟨Rt, hRt⟩ : exists R, forall x in t, ‖x‖ <= R := ht.exists_norm_le'
  refine isBounded_iff_forall_norm_le'.2 ⟨Rs + Rt, ?_⟩
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact norm_mul_le_of_le' (hRs x hx) (hRt y hy)

@[to_ad

中文:
定理 有界结构.IsBounded.mul
  条件: (hs : IsBounded s) (ht : IsBounded t)
  结论: IsBounded (s * t)
  证明: by
  obtain ⟨Rs, hRs⟩ : exists R, forall x in s, ‖x‖ <= R := hs.exists_norm_le'
  obtain ⟨Rt, hRt⟩ : exists R, forall x in t, ‖x‖ <= R := ht.exists_norm_le'
  refine isBounded_iff_forall_norm_le'.2 ⟨Rs + Rt, ?_⟩
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact norm_mul_le_of_le' (hRs x hx) (hRt y hy)

@[to_ad

Depends on / 依赖: exists_norm_le, hs.exists_norm_le, ht.exists_norm_le, isBounded_iff_forall_norm_le, norm_mul_le_of_le
-/
theorem Bornology.IsBounded.mul (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s * t) := by
  obtain ⟨Rs, hRs⟩ : exists R, forall x in s, ‖x‖ <= R := hs.exists_norm_le'
  obtain ⟨Rt, hRt⟩ : exists R, forall x in t, ‖x‖ <= R := ht.exists_norm_le'
  refine isBounded_iff_forall_norm_le'.2 ⟨Rs + Rt, ?_⟩
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact norm_mul_le_of_le' (hRs x hx) (hRt y hy)

@[to_additive]
/--
theorem `Bornology.IsBounded.of_mul` / 定理 `Bornology.IsBounded.of_mul`

English:
theorem Bornology.IsBounded.of_mul
  given: (hst : IsBounded (s * t))
  statement: IsBounded s ∨ IsBounded t
  proof: by
  symm
  exact AntilipschitzWith.isBounded_of_image2_left _ (fun x => (isometry_mul_left x).antilipschitz)
    (by rwa [image2_swap])

@[to_additive]

中文:
定理 有界结构.IsBounded.of_mul
  条件: (hst : IsBounded (s * t))
  结论: IsBounded s ∨ IsBounded t
  证明: by
  symm
  exact AntilipschitzWith.isBounded_of_image2_left _ (fun x => (isometry_mul_left x).antilipschitz)
    (by rwa [image2_swap])

@[to_additive]

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.isBounded_of_image2_left, antilipschitz, image2_swap, isBounded_of_image2_left, isometry_mul_left
-/
theorem Bornology.IsBounded.of_mul (hst : IsBounded (s * t)) : IsBounded s ∨ IsBounded t := by
  symm
  exact AntilipschitzWith.isBounded_of_image2_left _ (fun x => (isometry_mul_left x).antilipschitz)
    (by rwa [image2_swap])

@[to_additive]
/--
theorem `Bornology.IsBounded.inv` / 定理 `Bornology.IsBounded.inv`

English:
theorem Bornology.IsBounded.inv
  statement: IsBounded s -> IsBounded s⁻¹
  proof: by
  simp_rw [isBounded_iff_forall_norm_le', ← image_inv_eq_inv, forall_mem_image, norm_inv']
  exact id

@[to_additive]

中文:
定理 有界结构.IsBounded.inv
  结论: IsBounded s -> IsBounded s⁻¹
  证明: by
  simp_rw [isBounded_iff_forall_norm_le', ← image_inv_eq_inv, forall_mem_image, norm_inv']
  exact id

@[to_additive]

Depends on / 依赖: forall_mem_image, image_inv_eq_inv, isBounded_iff_forall_norm_le, norm_inv, simp_rw
-/
theorem Bornology.IsBounded.inv : IsBounded s -> IsBounded s⁻¹ := by
  simp_rw [isBounded_iff_forall_norm_le', ← image_inv_eq_inv, forall_mem_image, norm_inv']
  exact id

@[to_additive]
/--
theorem `Bornology.IsBounded.div` / 定理 `Bornology.IsBounded.div`

English:
theorem Bornology.IsBounded.div
  given: (hs : IsBounded s) (ht : IsBounded t)
  statement: IsBounded (s / t)
  proof: div_eq_mul_inv s t ▸ hs.mul ht.inv

中文:
定理 有界结构.IsBounded.div
  条件: (hs : IsBounded s) (ht : IsBounded t)
  结论: IsBounded (s / t)
  证明: div_eq_mul_inv s t ▸ hs.mul ht.inv

Depends on / 依赖: div_eq_mul_inv, hs.mul, ht.inv
-/
theorem Bornology.IsBounded.div (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s / t) :=
  div_eq_mul_inv s t ▸ hs.mul ht.inv

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] {δ : Real} {s : Set E} {x y : E}

section EMetric

open EMetric

@[to_additive (attr := simp)]
/--
theorem `infEDist_inv_inv` / 定理 `infEDist_inv_inv`

English:
theorem infEDist_inv_inv
  given: (x : E) (s : Set E)
  statement: infEDist x⁻¹ s⁻¹ = infEDist x s
  proof: by
  rw [← image_inv_eq_inv]; rw [infEDist_image isometry_inv]

@[deprecated (since := "2026-01-08")]
alias infEdist_neg_neg := infEDist_neg_neg

@[to_additive existing, deprecated (since := "2026-01-08")]
alias infEdist_inv_inv := infEDist_inv_inv


@[to_additive]

中文:
定理 infEDist_inv_inv
  条件: (x : E) (s : 集合 E)
  结论: infEDist x⁻¹ s⁻¹ = infEDist x s
  证明: by
  rw [← image_inv_eq_inv]; rw [infEDist_image isometry_inv]

@[deprecated (since := "2026-01-08")]
alias infEdist_neg_neg := infEDist_neg_neg

@[to_additive existing, deprecated (since := "2026-01-08")]
alias infEdist_inv_inv := infEDist_inv_inv


@[to_additive]

Depends on / 依赖: image_inv_eq_inv, infEDist_image, isometry_inv
-/
theorem infEDist_inv_inv (x : E) (s : Set E) : infEDist x⁻¹ s⁻¹ = infEDist x s := by
  rw [← image_inv_eq_inv]; rw [infEDist_image isometry_inv]

@[deprecated (since := "2026-01-08")]
alias infEdist_neg_neg := infEDist_neg_neg

@[to_additive existing, deprecated (since := "2026-01-08")]
alias infEdist_inv_inv := infEDist_inv_inv


@[to_additive]
/--
theorem `infEDist_inv` / 定理 `infEDist_inv`

English:
theorem infEDist_inv
  given: (x : E) (s : Set E)
  statement: infEDist x⁻¹ s = infEDist x s⁻¹
  proof: by
  rw [← infEDist_inv_inv]; rw [inv_inv]

@[deprecated (since := "2026-01-08")]
alias infEdist_neg := infEDist_neg

@[to_additive existing, deprecated (since := "2026-01-08")]
alias infEdist_inv := infEDist_inv

@[to_additive]

中文:
定理 infEDist_inv
  条件: (x : E) (s : 集合 E)
  结论: infEDist x⁻¹ s = infEDist x s⁻¹
  证明: by
  rw [← infEDist_inv_inv]; rw [inv_inv]

@[deprecated (since := "2026-01-08")]
alias infEdist_neg := infEDist_neg

@[to_additive existing, deprecated (since := "2026-01-08")]
alias infEdist_inv := infEDist_inv

@[to_additive]

Depends on / 依赖: infEDist_inv_inv, inv_inv
-/
theorem infEDist_inv (x : E) (s : Set E) : infEDist x⁻¹ s = infEDist x s⁻¹ := by
  rw [← infEDist_inv_inv]; rw [inv_inv]

@[deprecated (since := "2026-01-08")]
alias infEdist_neg := infEDist_neg

@[to_additive existing, deprecated (since := "2026-01-08")]
alias infEdist_inv := infEDist_inv

@[to_additive]
/--
theorem `ediam_mul_le` / 定理 `ediam_mul_le`

English:
theorem ediam_mul_le
  given: (x y : Set E)
  statement: ediam (x * y) <= ediam x + ediam y
  proof: (LipschitzOnWith.ediam_image2_le (· * ·) _ _
        (fun _ _ => (isometry_mul_right _).lipschitz.lipschitzOnWith) fun _ _ =>
        (isometry_mul_left _).lipschitz.lipschitzOnWith).trans_eq <|
    by simp only [ENNReal.coe_one, one_mul]

中文:
定理 ediam_mul_le
  条件: (x y : 集合 E)
  结论: ediam (x * y) <= ediam x + ediam y
  证明: (LipschitzOnWith.ediam_image2_le (· * ·) _ _
        (fun _ _ => (isometry_mul_right _).lipschitz.lipschitzOnWith) fun _ _ =>
        (isometry_mul_left _).lipschitz.lipschitzOnWith).trans_eq <|
    by simp only [ENNReal.coe_one, one_mul]

Depends on / 依赖: ENNReal, ENNReal.coe_one, LipschitzOnWith, LipschitzOnWith.ediam_image2_le, coe_one, ediam_image2_le, isometry_mul_left, isometry_mul_right, lipschitz, lipschitz.lipschitzOnWith, lipschitzOnWith, one_mul, trans_eq
-/
theorem ediam_mul_le (x y : Set E) : ediam (x * y) <= ediam x + ediam y :=
  (LipschitzOnWith.ediam_image2_le (· * ·) _ _
        (fun _ _ => (isometry_mul_right _).lipschitz.lipschitzOnWith) fun _ _ =>
        (isometry_mul_left _).lipschitz.lipschitzOnWith).trans_eq <|
    by simp only [ENNReal.coe_one, one_mul]

end EMetric

variable (δ s x y)

@[to_additive (attr := simp)]
/--
theorem `inv_thickening` / 定理 `inv_thickening`

English:
theorem inv_thickening
  statement: (thickening δ s)⁻¹ = thickening δ s⁻¹
  proof: by
  simp_rw [thickening, ← infEDist_inv]
  rfl

@[to_additive (attr := simp)]

中文:
定理 inv_thickening
  结论: (thickening δ s)⁻¹ = thickening δ s⁻¹
  证明: by
  simp_rw [thickening, ← infEDist_inv]
  rfl

@[to_additive (attr := simp)]

Depends on / 依赖: infEDist_inv, simp_rw, thickening
-/
theorem inv_thickening : (thickening δ s)⁻¹ = thickening δ s⁻¹ := by
  simp_rw [thickening, ← infEDist_inv]
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_cthickening` / 定理 `inv_cthickening`

English:
theorem inv_cthickening
  statement: (cthickening δ s)⁻¹ = cthickening δ s⁻¹
  proof: by
  simp_rw [cthickening, ← infEDist_inv]
  rfl

@[to_additive (attr := simp)]

中文:
定理 inv_cthickening
  结论: (cthickening δ s)⁻¹ = cthickening δ s⁻¹
  证明: by
  simp_rw [cthickening, ← infEDist_inv]
  rfl

@[to_additive (attr := simp)]

Depends on / 依赖: cthickening, infEDist_inv, simp_rw
-/
theorem inv_cthickening : (cthickening δ s)⁻¹ = cthickening δ s⁻¹ := by
  simp_rw [cthickening, ← infEDist_inv]
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_ball` / 定理 `inv_ball`

English:
theorem inv_ball
  statement: (ball x δ)⁻¹ = ball x⁻¹ δ
  proof: (IsometryEquiv.inv E).preimage_ball x δ

@[to_additive (attr := simp)]

中文:
定理 inv_ball
  结论: (ball x δ)⁻¹ = ball x⁻¹ δ
  证明: (IsometryEquiv.inv E).preimage_ball x δ

@[to_additive (attr := simp)]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.inv, preimage_ball
-/
theorem inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ := (IsometryEquiv.inv E).preimage_ball x δ

@[to_additive (attr := simp)]
/--
theorem `inv_closedBall` / 定理 `inv_closedBall`

English:
theorem inv_closedBall
  statement: (closedBall x δ)⁻¹ = closedBall x⁻¹ δ
  proof: (IsometryEquiv.inv E).preimage_closedBall x δ

@[to_additive (attr := simp)]

中文:
定理 inv_closedBall
  结论: (closedBall x δ)⁻¹ = closedBall x⁻¹ δ
  证明: (IsometryEquiv.inv E).preimage_closedBall x δ

@[to_additive (attr := simp)]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.inv, preimage_closedBall
-/
theorem inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ :=
  (IsometryEquiv.inv E).preimage_closedBall x δ

@[to_additive (attr := simp)]
/--
theorem `inv_sphere` / 定理 `inv_sphere`

English:
theorem inv_sphere
  statement: (sphere x δ)⁻¹ = sphere x⁻¹ δ
  proof: (IsometryEquiv.inv E).preimage_sphere x δ

@[to_additive]

中文:
定理 inv_sphere
  结论: (sphere x δ)⁻¹ = sphere x⁻¹ δ
  证明: (IsometryEquiv.inv E).preimage_sphere x δ

@[to_additive]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.inv, preimage_sphere
-/
theorem inv_sphere : (sphere x δ)⁻¹ = sphere x⁻¹ δ :=
  (IsometryEquiv.inv E).preimage_sphere x δ

@[to_additive]
/--
theorem `singleton_mul_ball` / 定理 `singleton_mul_ball`

English:
theorem singleton_mul_ball
  statement: {x} * ball y δ = ball (x * y) δ
  proof: by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]

@[to_additive]

中文:
定理 singleton_mul_ball
  结论: {x} * ball y δ = ball (x * y) δ
  证明: by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]

@[to_additive]

Depends on / 依赖: div_inv_eq_mul, image_mul_left, mul_comm, preimage_mul_ball, singleton_mul
-/
theorem singleton_mul_ball : {x} * ball y δ = ball (x * y) δ := by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]

@[to_additive]
/--
theorem `singleton_div_ball` / 定理 `singleton_div_ball`

English:
theorem singleton_div_ball
  statement: {x} / ball y δ = ball (x / y) δ
  proof: by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]

@[to_additive]

中文:
定理 singleton_div_ball
  结论: {x} / ball y δ = ball (x / y) δ
  证明: by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, inv_ball, simp_rw, singleton_mul_ball
-/
theorem singleton_div_ball : {x} / ball y δ = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]

@[to_additive]
/--
theorem `ball_mul_singleton` / 定理 `ball_mul_singleton`

English:
theorem ball_mul_singleton
  statement: ball x δ * {y} = ball (x * y) δ
  proof: by
  rw [mul_comm]; rw [singleton_mul_ball]; rw [mul_comm y]

@[to_additive]

中文:
定理 ball_mul_singleton
  结论: ball x δ * {y} = ball (x * y) δ
  证明: by
  rw [mul_comm]; rw [singleton_mul_ball]; rw [mul_comm y]

@[to_additive]

Depends on / 依赖: mul_comm, singleton_mul_ball
-/
theorem ball_mul_singleton : ball x δ * {y} = ball (x * y) δ := by
  rw [mul_comm]; rw [singleton_mul_ball]; rw [mul_comm y]

@[to_additive]
/--
theorem `ball_div_singleton` / 定理 `ball_div_singleton`

English:
theorem ball_div_singleton
  statement: ball x δ / {y} = ball (x / y) δ
  proof: by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]

@[to_additive]

中文:
定理 ball_div_singleton
  结论: ball x δ / {y} = ball (x / y) δ
  证明: by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]

@[to_additive]

Depends on / 依赖: ball_mul_singleton, div_eq_mul_inv, inv_singleton, simp_rw
-/
theorem ball_div_singleton : ball x δ / {y} = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]

@[to_additive]
/--
theorem `singleton_mul_ball_one` / 定理 `singleton_mul_ball_one`

English:
theorem singleton_mul_ball_one
  statement: {x} * ball 1 δ = ball x δ
  proof: by simp

@[to_additive]

中文:
定理 singleton_mul_ball_one
  结论: {x} * ball 1 δ = ball x δ
  证明: by simp

@[to_additive]
-/
theorem singleton_mul_ball_one : {x} * ball 1 δ = ball x δ := by simp

@[to_additive]
/--
theorem `singleton_div_ball_one` / 定理 `singleton_div_ball_one`

English:
theorem singleton_div_ball_one
  statement: {x} / ball 1 δ = ball x δ
  proof: by
  rw [singleton_div_ball]; rw [div_one]

@[to_additive]

中文:
定理 singleton_div_ball_one
  结论: {x} / ball 1 δ = ball x δ
  证明: by
  rw [singleton_div_ball]; rw [div_one]

@[to_additive]

Depends on / 依赖: div_one, singleton_div_ball
-/
theorem singleton_div_ball_one : {x} / ball 1 δ = ball x δ := by
  rw [singleton_div_ball]; rw [div_one]

@[to_additive]
/--
theorem `ball_one_mul_singleton` / 定理 `ball_one_mul_singleton`

English:
theorem ball_one_mul_singleton
  statement: ball 1 δ * {x} = ball x δ
  proof: by simp

@[to_additive]

中文:
定理 ball_one_mul_singleton
  结论: ball 1 δ * {x} = ball x δ
  证明: by simp

@[to_additive]
-/
theorem ball_one_mul_singleton : ball 1 δ * {x} = ball x δ := by simp

@[to_additive]
/--
theorem `ball_one_div_singleton` / 定理 `ball_one_div_singleton`

English:
theorem ball_one_div_singleton
  statement: ball 1 δ / {x} = ball x⁻¹ δ
  proof: by
  rw [ball_div_singleton]; rw [one_div]

@[to_additive]

中文:
定理 ball_one_div_singleton
  结论: ball 1 δ / {x} = ball x⁻¹ δ
  证明: by
  rw [ball_div_singleton]; rw [one_div]

@[to_additive]

Depends on / 依赖: ball_div_singleton, one_div
-/
theorem ball_one_div_singleton : ball 1 δ / {x} = ball x⁻¹ δ := by
  rw [ball_div_singleton]; rw [one_div]

@[to_additive]
/--
theorem `smul_ball_one` / 定理 `smul_ball_one`

English:
theorem smul_ball_one
  statement: x • ball (1 : E) δ = ball x δ
  proof: by
  rw [smul_ball]; rw [smul_eq_mul]; rw [mul_one]

@[to_additive (attr := simp 1100)]

中文:
定理 smul_ball_one
  结论: x • ball (1 : E) δ = ball x δ
  证明: by
  rw [smul_ball]; rw [smul_eq_mul]; rw [mul_one]

@[to_additive (attr := simp 1100)]

Depends on / 依赖: mul_one, smul_ball, smul_eq_mul
-/
theorem smul_ball_one : x • ball (1 : E) δ = ball x δ := by
  rw [smul_ball]; rw [smul_eq_mul]; rw [mul_one]

@[to_additive (attr := simp 1100)]
/--
theorem `singleton_mul_closedBall` / 定理 `singleton_mul_closedBall`

English:
theorem singleton_mul_closedBall
  statement: {x} * closedBall y δ = closedBall (x * y) δ
  proof: by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_closedBall]

@[to_additive (attr := simp 1100)]

中文:
定理 singleton_mul_closedBall
  结论: {x} * closedBall y δ = closedBall (x * y) δ
  证明: by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_closedBall]

@[to_additive (attr := simp 1100)]

Depends on / 依赖: image_smul, simp_rw, singleton_mul, smul_closedBall, smul_eq_mul
-/
theorem singleton_mul_closedBall : {x} * closedBall y δ = closedBall (x * y) δ := by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_closedBall]

@[to_additive (attr := simp 1100)]
/--
theorem `singleton_div_closedBall` / 定理 `singleton_div_closedBall`

English:
theorem singleton_div_closedBall
  statement: {x} / closedBall y δ = closedBall (x / y) δ
  proof: by
  simp_rw [div_eq_mul_inv, inv_closedBall, singleton_mul_closedBall]

@[to_additive (attr := simp 1100)]

中文:
定理 singleton_div_closedBall
  结论: {x} / closedBall y δ = closedBall (x / y) δ
  证明: by
  simp_rw [div_eq_mul_inv, inv_closedBall, singleton_mul_closedBall]

@[to_additive (attr := simp 1100)]

Depends on / 依赖: div_eq_mul_inv, inv_closedBall, simp_rw, singleton_mul_closedBall
-/
theorem singleton_div_closedBall : {x} / closedBall y δ = closedBall (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_closedBall, singleton_mul_closedBall]

@[to_additive (attr := simp 1100)]
/--
theorem `closedBall_mul_singleton` / 定理 `closedBall_mul_singleton`

English:
theorem closedBall_mul_singleton
  statement: closedBall x δ * {y} = closedBall (x * y) δ
  proof: by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]

中文:
定理 closedBall_mul_singleton
  结论: closedBall x δ * {y} = closedBall (x * y) δ
  证明: by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]

Depends on / 依赖: mul_comm
-/
theorem closedBall_mul_singleton : closedBall x δ * {y} = closedBall (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]
/--
theorem `closedBall_div_singleton` / 定理 `closedBall_div_singleton`

English:
theorem closedBall_div_singleton
  statement: closedBall x δ / {y} = closedBall (x / y) δ
  proof: by
  simp [div_eq_mul_inv]

@[to_additive]

中文:
定理 closedBall_div_singleton
  结论: closedBall x δ / {y} = closedBall (x / y) δ
  证明: by
  simp [div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv
-/
theorem closedBall_div_singleton : closedBall x δ / {y} = closedBall (x / y) δ := by
  simp [div_eq_mul_inv]

@[to_additive]
/--
theorem `singleton_mul_closedBall_one` / 定理 `singleton_mul_closedBall_one`

English:
theorem singleton_mul_closedBall_one
  statement: {x} * closedBall 1 δ = closedBall x δ
  proof: by simp

@[to_additive]

中文:
定理 singleton_mul_closedBall_one
  结论: {x} * closedBall 1 δ = closedBall x δ
  证明: by simp

@[to_additive]
-/
theorem singleton_mul_closedBall_one : {x} * closedBall 1 δ = closedBall x δ := by simp

@[to_additive]
/--
theorem `singleton_div_closedBall_one` / 定理 `singleton_div_closedBall_one`

English:
theorem singleton_div_closedBall_one
  statement: {x} / closedBall 1 δ = closedBall x δ
  proof: by
  rw [singleton_div_closedBall]; rw [div_one]

@[to_additive]

中文:
定理 singleton_div_closedBall_one
  结论: {x} / closedBall 1 δ = closedBall x δ
  证明: by
  rw [singleton_div_closedBall]; rw [div_one]

@[to_additive]

Depends on / 依赖: div_one, singleton_div_closedBall
-/
theorem singleton_div_closedBall_one : {x} / closedBall 1 δ = closedBall x δ := by
  rw [singleton_div_closedBall]; rw [div_one]

@[to_additive]
/--
theorem `closedBall_one_mul_singleton` / 定理 `closedBall_one_mul_singleton`

English:
theorem closedBall_one_mul_singleton
  statement: closedBall 1 δ * {x} = closedBall x δ
  proof: by simp

@[to_additive]

中文:
定理 closedBall_one_mul_singleton
  结论: closedBall 1 δ * {x} = closedBall x δ
  证明: by simp

@[to_additive]
-/
theorem closedBall_one_mul_singleton : closedBall 1 δ * {x} = closedBall x δ := by simp

@[to_additive]
/--
theorem `closedBall_one_div_singleton` / 定理 `closedBall_one_div_singleton`

English:
theorem closedBall_one_div_singleton
  statement: closedBall 1 δ / {x} = closedBall x⁻¹ δ
  proof: by simp

@[to_additive (attr := simp 1100)]

中文:
定理 closedBall_one_div_singleton
  结论: closedBall 1 δ / {x} = closedBall x⁻¹ δ
  证明: by simp

@[to_additive (attr := simp 1100)]
-/
theorem closedBall_one_div_singleton : closedBall 1 δ / {x} = closedBall x⁻¹ δ := by simp

@[to_additive (attr := simp 1100)]
/--
theorem `smul_closedBall_one` / 定理 `smul_closedBall_one`

English:
theorem smul_closedBall_one
  statement: x • closedBall (1 : E) δ = closedBall x δ
  proof: by simp

@[to_additive (attr := simp 1100)]

中文:
定理 smul_closedBall_one
  结论: x • closedBall (1 : E) δ = closedBall x δ
  证明: by simp

@[to_additive (attr := simp 1100)]
-/
theorem smul_closedBall_one : x • closedBall (1 : E) δ = closedBall x δ := by simp

@[to_additive (attr := simp 1100)]
/--
theorem `singleton_mul_sphere` / 定理 `singleton_mul_sphere`

English:
theorem singleton_mul_sphere
  statement: {x} * sphere y δ = sphere (x * y) δ
  proof: by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_sphere]

@[to_additive (attr := simp 1100)]

中文:
定理 singleton_mul_sphere
  结论: {x} * sphere y δ = sphere (x * y) δ
  证明: by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_sphere]

@[to_additive (attr := simp 1100)]

Depends on / 依赖: image_smul, simp_rw, singleton_mul, smul_eq_mul, smul_sphere
-/
theorem singleton_mul_sphere : {x} * sphere y δ = sphere (x * y) δ := by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_sphere]

@[to_additive (attr := simp 1100)]
/--
theorem `singleton_div_sphere` / 定理 `singleton_div_sphere`

English:
theorem singleton_div_sphere
  statement: {x} / sphere y δ = sphere (x / y) δ
  proof: by
  simp_rw [div_eq_mul_inv, inv_sphere, singleton_mul_sphere]

@[to_additive (attr := simp 1100)]

中文:
定理 singleton_div_sphere
  结论: {x} / sphere y δ = sphere (x / y) δ
  证明: by
  simp_rw [div_eq_mul_inv, inv_sphere, singleton_mul_sphere]

@[to_additive (attr := simp 1100)]

Depends on / 依赖: div_eq_mul_inv, inv_sphere, simp_rw, singleton_mul_sphere
-/
theorem singleton_div_sphere : {x} / sphere y δ = sphere (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_sphere, singleton_mul_sphere]

@[to_additive (attr := simp 1100)]
/--
theorem `sphere_mul_singleton` / 定理 `sphere_mul_singleton`

English:
theorem sphere_mul_singleton
  statement: sphere x δ * {y} = sphere (x * y) δ
  proof: by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]

中文:
定理 sphere_mul_singleton
  结论: sphere x δ * {y} = sphere (x * y) δ
  证明: by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]

Depends on / 依赖: mul_comm
-/
theorem sphere_mul_singleton : sphere x δ * {y} = sphere (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]
/--
theorem `sphere_div_singleton` / 定理 `sphere_div_singleton`

English:
theorem sphere_div_singleton
  statement: sphere x δ / {y} = sphere (x / y) δ
  proof: by
  simp [div_eq_mul_inv]

@[to_additive]

中文:
定理 sphere_div_singleton
  结论: sphere x δ / {y} = sphere (x / y) δ
  证明: by
  simp [div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv
-/
theorem sphere_div_singleton : sphere x δ / {y} = sphere (x / y) δ := by
  simp [div_eq_mul_inv]

@[to_additive]
/--
theorem `singleton_mul_sphere_one` / 定理 `singleton_mul_sphere_one`

English:
theorem singleton_mul_sphere_one
  statement: {x} * sphere 1 δ = sphere x δ
  proof: by simp

@[to_additive]

中文:
定理 singleton_mul_sphere_one
  结论: {x} * sphere 1 δ = sphere x δ
  证明: by simp

@[to_additive]
-/
theorem singleton_mul_sphere_one : {x} * sphere 1 δ = sphere x δ := by simp

@[to_additive]
/--
theorem `singleton_div_sphere_one` / 定理 `singleton_div_sphere_one`

English:
theorem singleton_div_sphere_one
  statement: {x} / sphere 1 δ = sphere x δ
  proof: by
  rw [singleton_div_sphere]; rw [div_one]

@[to_additive]

中文:
定理 singleton_div_sphere_one
  结论: {x} / sphere 1 δ = sphere x δ
  证明: by
  rw [singleton_div_sphere]; rw [div_one]

@[to_additive]

Depends on / 依赖: div_one, singleton_div_sphere
-/
theorem singleton_div_sphere_one : {x} / sphere 1 δ = sphere x δ := by
  rw [singleton_div_sphere]; rw [div_one]

@[to_additive]
/--
theorem `sphere_one_mul_singleton` / 定理 `sphere_one_mul_singleton`

English:
theorem sphere_one_mul_singleton
  statement: sphere 1 δ * {x} = sphere x δ
  proof: by simp

@[to_additive]

中文:
定理 sphere_one_mul_singleton
  结论: sphere 1 δ * {x} = sphere x δ
  证明: by simp

@[to_additive]
-/
theorem sphere_one_mul_singleton : sphere 1 δ * {x} = sphere x δ := by simp

@[to_additive]
/--
theorem `sphere_one_div_singleton` / 定理 `sphere_one_div_singleton`

English:
theorem sphere_one_div_singleton
  statement: sphere 1 δ / {x} = sphere x⁻¹ δ
  proof: by simp

@[to_additive (attr := simp 1100)]

中文:
定理 sphere_one_div_singleton
  结论: sphere 1 δ / {x} = sphere x⁻¹ δ
  证明: by simp

@[to_additive (attr := simp 1100)]
-/
theorem sphere_one_div_singleton : sphere 1 δ / {x} = sphere x⁻¹ δ := by simp

@[to_additive (attr := simp 1100)]
/--
theorem `smul_sphere_one` / 定理 `smul_sphere_one`

English:
theorem smul_sphere_one
  statement: x • sphere (1 : E) δ = sphere x δ
  proof: by simp

@[to_additive]

中文:
定理 smul_sphere_one
  结论: x • sphere (1 : E) δ = sphere x δ
  证明: by simp

@[to_additive]
-/
theorem smul_sphere_one : x • sphere (1 : E) δ = sphere x δ := by simp

@[to_additive]
/--
theorem `mul_ball_one` / 定理 `mul_ball_one`

English:
theorem mul_ball_one
  statement: s * ball 1 δ = thickening δ s
  proof: by
  rw [thickening_eq_biUnion_ball]
  convert! iUnion₂_mul (fun x (_ : x in s) => { x }) (ball (1 : E) δ)
  · exact s.biUnion_of_singleton.symm
  ext x
  simp_rw [singleton_mul_ball, mul_one]

@[to_additive]

中文:
定理 mul_ball_one
  结论: s * ball 1 δ = thickening δ s
  证明: by
  rw [thickening_eq_biUnion_ball]
  convert! iUnion₂_mul (fun x (_ : x in s) => { x }) (ball (1 : E) δ)
  · exact s.biUnion_of_singleton.symm
  ext x
  simp_rw [singleton_mul_ball, mul_one]

@[to_additive]

Depends on / 依赖: biUnion_of_singleton, convert, mul_one, s.biUnion_of_singleton.symm, simp_rw, singleton_mul_ball, thickening_eq_biUnion_ball
-/
theorem mul_ball_one : s * ball 1 δ = thickening δ s := by
  rw [thickening_eq_biUnion_ball]
  convert! iUnion₂_mul (fun x (_ : x in s) => { x }) (ball (1 : E) δ)
  · exact s.biUnion_of_singleton.symm
  ext x
  simp_rw [singleton_mul_ball, mul_one]

@[to_additive]
/--
theorem `div_ball_one` / 定理 `div_ball_one`

English:
theorem div_ball_one
  statement: s / ball 1 δ = thickening δ s
  proof: by simp [div_eq_mul_inv, mul_ball_one]

@[to_additive]

中文:
定理 div_ball_one
  结论: s / ball 1 δ = thickening δ s
  证明: by simp [div_eq_mul_inv, mul_ball_one]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mul_ball_one
-/
theorem div_ball_one : s / ball 1 δ = thickening δ s := by simp [div_eq_mul_inv, mul_ball_one]

@[to_additive]
/--
theorem `ball_mul_one` / 定理 `ball_mul_one`

English:
theorem ball_mul_one
  statement: ball 1 δ * s = thickening δ s
  proof: by rw [mul_comm, mul_ball_one]

@[to_additive]

中文:
定理 ball_mul_one
  结论: ball 1 δ * s = thickening δ s
  证明: by rw [mul_comm, mul_ball_one]

@[to_additive]

Depends on / 依赖: mul_ball_one, mul_comm
-/
theorem ball_mul_one : ball 1 δ * s = thickening δ s := by rw [mul_comm, mul_ball_one]

@[to_additive]
/--
theorem `ball_div_one` / 定理 `ball_div_one`

English:
theorem ball_div_one
  statement: ball 1 δ / s = thickening δ s⁻¹
  proof: by simp [div_eq_mul_inv, ball_mul_one]

@[to_additive (attr := simp)]

中文:
定理 ball_div_one
  结论: ball 1 δ / s = thickening δ s⁻¹
  证明: by simp [div_eq_mul_inv, ball_mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: ball_mul_one, div_eq_mul_inv
-/
theorem ball_div_one : ball 1 δ / s = thickening δ s⁻¹ := by simp [div_eq_mul_inv, ball_mul_one]

@[to_additive (attr := simp)]
/--
theorem `mul_ball` / 定理 `mul_ball`

English:
theorem mul_ball
  statement: s * ball x δ = x • thickening δ s
  proof: by
  rw [← smul_ball_one]; rw [mul_smul_comm]; rw [mul_ball_one]

@[to_additive (attr := simp)]

中文:
定理 mul_ball
  结论: s * ball x δ = x • thickening δ s
  证明: by
  rw [← smul_ball_one]; rw [mul_smul_comm]; rw [mul_ball_one]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_ball_one, mul_smul_comm, smul_ball_one
-/
theorem mul_ball : s * ball x δ = x • thickening δ s := by
  rw [← smul_ball_one]; rw [mul_smul_comm]; rw [mul_ball_one]

@[to_additive (attr := simp)]
/--
theorem `div_ball` / 定理 `div_ball`

English:
theorem div_ball
  statement: s / ball x δ = x⁻¹ • thickening δ s
  proof: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 div_ball
  结论: s / ball x δ = x⁻¹ • thickening δ s
  证明: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem div_ball : s / ball x δ = x⁻¹ • thickening δ s := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `ball_mul` / 定理 `ball_mul`

English:
theorem ball_mul
  statement: ball x δ * s = x • thickening δ s
  proof: by rw [mul_comm, mul_ball]

@[to_additive (attr := simp)]

中文:
定理 ball_mul
  结论: ball x δ * s = x • thickening δ s
  证明: by rw [mul_comm, mul_ball]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_ball, mul_comm
-/
theorem ball_mul : ball x δ * s = x • thickening δ s := by rw [mul_comm, mul_ball]

@[to_additive (attr := simp)]
/--
theorem `ball_div` / 定理 `ball_div`

English:
theorem ball_div
  statement: ball x δ / s = x • thickening δ s⁻¹
  proof: by simp [div_eq_mul_inv]

中文:
定理 ball_div
  结论: ball x δ / s = x • thickening δ s⁻¹
  证明: by simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
theorem ball_div : ball x δ / s = x • thickening δ s⁻¹ := by simp [div_eq_mul_inv]

variable {δ s x y}

@[to_additive]
/--
theorem `IsCompact.mul_closedBall_one` / 定理 `IsCompact.mul_closedBall_one`

English:
theorem IsCompact.mul_closedBall_one
  given: (hs : IsCompact s) (hδ : 0 <= δ)
  proof: by
  rw [hs.cthickening_eq_biUnion_closedBall hδ]
  ext x
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_iUnion, mem_closedBall,
    ← eq_div_iff_mul_eq'', div_one, exists_eq_right]

@[to_additive]

中文:
定理 是紧集.mul_closedBall_one
  条件: (hs : 是紧集 s) (hδ : 0 <= δ)
  证明: by
  rw [hs.cthickening_eq_biUnion_closedBall hδ]
  ext x
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_iUnion, mem_closedBall,
    ← eq_div_iff_mul_eq'', div_one, exists_eq_right]

@[to_additive]

Depends on / 依赖: cthickening_eq_biUnion_closedBall, dist_eq_norm_div, div_one, eq_div_iff_mul_eq, exists_eq_right, exists_prop, hs.cthickening_eq_biUnion_closedBall, mem_closedBall, mem_iUnion, mem_mul
-/
theorem IsCompact.mul_closedBall_one (hs : IsCompact s) (hδ : 0 <= δ) :
    s * closedBall (1 : E) δ = cthickening δ s := by
  rw [hs.cthickening_eq_biUnion_closedBall hδ]
  ext x
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_iUnion, mem_closedBall,
    ← eq_div_iff_mul_eq'', div_one, exists_eq_right]

@[to_additive]
/--
theorem `IsCompact.div_closedBall_one` / 定理 `IsCompact.div_closedBall_one`

English:
theorem IsCompact.div_closedBall_one
  given: (hs : IsCompact s) (hδ : 0 <= δ)
  proof: by simp [div_eq_mul_inv, hs.mul_closedBall_one hδ]

@[to_additive]

中文:
定理 是紧集.div_closedBall_one
  条件: (hs : 是紧集 s) (hδ : 0 <= δ)
  证明: by simp [div_eq_mul_inv, hs.mul_closedBall_one hδ]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hs.mul_closedBall_one, mul_closedBall_one
-/
theorem IsCompact.div_closedBall_one (hs : IsCompact s) (hδ : 0 <= δ) :
    s / closedBall 1 δ = cthickening δ s := by simp [div_eq_mul_inv, hs.mul_closedBall_one hδ]

@[to_additive]
/--
theorem `IsCompact.closedBall_one_mul` / 定理 `IsCompact.closedBall_one_mul`

English:
theorem IsCompact.closedBall_one_mul
  given: (hs : IsCompact s) (hδ : 0 <= δ)
  proof: by rw [mul_comm, hs.mul_closedBall_one hδ]

@[to_additive]

中文:
定理 是紧集.closedBall_one_mul
  条件: (hs : 是紧集 s) (hδ : 0 <= δ)
  证明: by rw [mul_comm, hs.mul_closedBall_one hδ]

@[to_additive]

Depends on / 依赖: hs.mul_closedBall_one, mul_closedBall_one, mul_comm
-/
theorem IsCompact.closedBall_one_mul (hs : IsCompact s) (hδ : 0 <= δ) :
    closedBall 1 δ * s = cthickening δ s := by rw [mul_comm, hs.mul_closedBall_one hδ]

@[to_additive]
/--
theorem `IsCompact.closedBall_one_div` / 定理 `IsCompact.closedBall_one_div`

English:
theorem IsCompact.closedBall_one_div
  given: (hs : IsCompact s) (hδ : 0 <= δ)
  proof: by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closedBall_one hδ]

@[to_additive]

中文:
定理 是紧集.closedBall_one_div
  条件: (hs : 是紧集 s) (hδ : 0 <= δ)
  证明: by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closedBall_one hδ]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hs.inv.mul_closedBall_one, mul_closedBall_one, mul_comm
-/
theorem IsCompact.closedBall_one_div (hs : IsCompact s) (hδ : 0 <= δ) :
    closedBall 1 δ / s = cthickening δ s⁻¹ := by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closedBall_one hδ]

@[to_additive]
/--
theorem `IsCompact.mul_closedBall` / 定理 `IsCompact.mul_closedBall`

English:
theorem IsCompact.mul_closedBall
  given: (hs : IsCompact s) (hδ : 0 <= δ) (x : E)
  proof: by
  rw [← smul_closedBall_one]; rw [mul_smul_comm]; rw [hs.mul_closedBall_one hδ]

@[to_additive]

中文:
定理 是紧集.mul_closedBall
  条件: (hs : 是紧集 s) (hδ : 0 <= δ) (x : E)
  证明: by
  rw [← smul_closedBall_one]; rw [mul_smul_comm]; rw [hs.mul_closedBall_one hδ]

@[to_additive]

Depends on / 依赖: hs.mul_closedBall_one, mul_closedBall_one, mul_smul_comm, smul_closedBall_one
-/
theorem IsCompact.mul_closedBall (hs : IsCompact s) (hδ : 0 <= δ) (x : E) :
    s * closedBall x δ = x • cthickening δ s := by
  rw [← smul_closedBall_one]; rw [mul_smul_comm]; rw [hs.mul_closedBall_one hδ]

@[to_additive]
/--
theorem `IsCompact.div_closedBall` / 定理 `IsCompact.div_closedBall`

English:
theorem IsCompact.div_closedBall
  given: (hs : IsCompact s) (hδ : 0 <= δ) (x : E)
  proof: by
  simp [div_eq_mul_inv, hs.mul_closedBall hδ]

@[to_additive]

中文:
定理 是紧集.div_closedBall
  条件: (hs : 是紧集 s) (hδ : 0 <= δ) (x : E)
  证明: by
  simp [div_eq_mul_inv, hs.mul_closedBall hδ]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hs.mul_closedBall, mul_closedBall
-/
theorem IsCompact.div_closedBall (hs : IsCompact s) (hδ : 0 <= δ) (x : E) :
    s / closedBall x δ = x⁻¹ • cthickening δ s := by
  simp [div_eq_mul_inv, hs.mul_closedBall hδ]

@[to_additive]
/--
theorem `IsCompact.closedBall_mul` / 定理 `IsCompact.closedBall_mul`

English:
theorem IsCompact.closedBall_mul
  given: (hs : IsCompact s) (hδ : 0 <= δ) (x : E)
  proof: by rw [mul_comm, hs.mul_closedBall hδ]

@[to_additive]

中文:
定理 是紧集.closedBall_mul
  条件: (hs : 是紧集 s) (hδ : 0 <= δ) (x : E)
  证明: by rw [mul_comm, hs.mul_closedBall hδ]

@[to_additive]

Depends on / 依赖: hs.mul_closedBall, mul_closedBall, mul_comm
-/
theorem IsCompact.closedBall_mul (hs : IsCompact s) (hδ : 0 <= δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by rw [mul_comm, hs.mul_closedBall hδ]

@[to_additive]
/--
theorem `IsCompact.closedBall_div` / 定理 `IsCompact.closedBall_div`

English:
theorem IsCompact.closedBall_div
  given: (hs : IsCompact s) (hδ : 0 <= δ) (x : E)
  proof: by
  simp [hs.closedBall_mul hδ]

中文:
定理 是紧集.closedBall_div
  条件: (hs : 是紧集 s) (hδ : 0 <= δ) (x : E)
  证明: by
  simp [hs.closedBall_mul hδ]

Depends on / 依赖: closedBall_mul, hs.closedBall_mul
-/
theorem IsCompact.closedBall_div (hs : IsCompact s) (hδ : 0 <= δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by
  simp [hs.closedBall_mul hδ]

end SeminormedCommGroup
