/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Normed groups are uniform groups

This file proves lipschitzness of normed group operations and shows that normed groups are uniform
groups.
-/

public section

variable {𝓕 E F : Type*}

open Filter Function Metric Bornology
open scoped ENNReal NNReal Uniformity Pointwise Topology

section SeminormedGroup
variable [SeminormedGroup E] [SeminormedGroup F] {s : Set E} {a b : E} {r : Real}

@[to_additive]
/--
Instance `NormedGroup.to_isIsometricSMul` / 实例 `NormedGroup.to_isIsometricSMul`

English:
instance NormedGroup.to_isIsometricSMul
  signature: : IsIsometricSMul E E
  body: ⟨fun a => Isometry.of_dist_eq fun b c => by simp [dist_eq_norm_inv_mul]⟩

@[to_additive]

中文:
实例 赋范群.to_isIsometricSMul
  签名: : 是是ometricSMul E E
  定义体: ⟨fun a => Isometry.of_dist_eq fun b c => by simp [dist_eq_norm_inv_mul]⟩

@[to_additive]

Depends on / 依赖: Isometry, Isometry.of_dist_eq, dist_eq_norm_inv_mul, of_dist_eq
-/
instance NormedGroup.to_isIsometricSMul : IsIsometricSMul E E :=
  ⟨fun a => Isometry.of_dist_eq fun b c => by simp [dist_eq_norm_inv_mul]⟩

@[to_additive]
/--
theorem `Isometry.norm_map_of_map_one` / 定理 `Isometry.norm_map_of_map_one`

English:
theorem Isometry.norm_map_of_map_one
  given: {f : E -> F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E)
  proof: by rw [← dist_one_right, ← h₁, hi.dist_eq, dist_one_right]

@[to_additive (attr := simp) norm_map]

中文:
定理 等距.norm_map_of_map_one
  条件: {f : E -> F} (hi : 等距 f) (h₁ : f 1 = 1) (x : E)
  证明: by rw [← dist_one_right, ← h₁, hi.dist_eq, dist_one_right]

@[to_additive (attr := simp) norm_map]

Depends on / 依赖: dist_eq, dist_one_right, hi.dist_eq
-/
theorem Isometry.norm_map_of_map_one {f : E -> F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖ = ‖x‖ := by rw [← dist_one_right, ← h₁, hi.dist_eq, dist_one_right]

@[to_additive (attr := simp) norm_map]
/--
theorem `norm_map'` / 定理 `norm_map'`

English:
theorem norm_map'
  given: [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E)
  proof: (IsometryClass.isometry f).norm_map_of_map_one (map_one f) x

@[to_additive (attr := simp) nnnorm_map]

中文:
定理 norm_map'
  条件: [函数状 𝓕 E F] [等距类 𝓕 E F] [幺态射类 𝓕 E F] (f : 𝓕) (x : E)
  证明: (IsometryClass.isometry f).norm_map_of_map_one (map_one f) x

@[to_additive (attr := simp) nnnorm_map]

Depends on / 依赖: IsometryClass, IsometryClass.isometry, isometry, map_one, norm_map_of_map_one
-/
theorem norm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E) :
    ‖f x‖ = ‖x‖ :=
  (IsometryClass.isometry f).norm_map_of_map_one (map_one f) x

@[to_additive (attr := simp) nnnorm_map]
/--
theorem `nnnorm_map'` / 定理 `nnnorm_map'`

English:
theorem nnnorm_map'
  given: [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E)
  proof: NNReal.eq norm_map' f x

@[to_additive (attr := simp) enorm_map]

中文:
定理 nnnorm_map'
  条件: [函数状 𝓕 E F] [等距类 𝓕 E F] [幺态射类 𝓕 E F] (f : 𝓕) (x : E)
  证明: NNReal.eq norm_map' f x

@[to_additive (attr := simp) enorm_map]

Depends on / 依赖: NNReal, NNReal.eq, norm_map
-/
theorem nnnorm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E) :
    ‖f x‖₊ = ‖x‖₊ :=
NNReal.eq norm_map' f x

@[to_additive (attr := simp) enorm_map]
/--
lemma `enorm_map'` / 引理 `enorm_map'`

English:
lemma enorm_map'
  given: [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E)
  proof: by simp [enorm]

@[to_additive (attr := simp)]

中文:
引理 enorm_map'
  条件: [函数状 𝓕 E F] [等距类 𝓕 E F] [幺态射类 𝓕 E F] (f : 𝓕) (x : E)
  证明: by simp [enorm]

@[to_additive (attr := simp)]
-/
lemma enorm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E) :
    ‖f x‖ₑ = ‖x‖ₑ := by simp [enorm]

@[to_additive (attr := simp)]
/--
theorem `dist_self_mul_right` / 定理 `dist_self_mul_right`

English:
theorem dist_self_mul_right
  given: (a b : E)
  statement: dist b (b * a) = ‖a‖
  proof: by
  rw [← dist_one_left]; rw [← dist_mul_left b 1 a]; rw [mul_one]

@[to_additive (attr := simp)]

中文:
定理 dist_self_mul_right
  条件: (a b : E)
  结论: dist b (b * a) = ‖a‖
  证明: by
  rw [← dist_one_left]; rw [← dist_mul_left b 1 a]; rw [mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: dist_mul_left, dist_one_left, mul_one
-/
theorem dist_self_mul_right (a b : E) : dist b (b * a) = ‖a‖ := by
  rw [← dist_one_left]; rw [← dist_mul_left b 1 a]; rw [mul_one]

@[to_additive (attr := simp)]
/--
theorem `dist_self_mul_left` / 定理 `dist_self_mul_left`

English:
theorem dist_self_mul_left
  given: (a b : E)
  statement: dist (b * a) b = ‖a‖
  proof: by
  rw [dist_comm]; rw [dist_self_mul_right]

中文:
定理 dist_self_mul_left
  条件: (a b : E)
  结论: dist (b * a) b = ‖a‖
  证明: by
  rw [dist_comm]; rw [dist_self_mul_right]

Depends on / 依赖: dist_comm, dist_self_mul_right
-/
theorem dist_self_mul_left (a b : E) : dist (b * a) b = ‖a‖ := by
  rw [dist_comm]; rw [dist_self_mul_right]

open Finset

variable [FunLike 𝓕 E F]

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/Normed/Operator/Basic.lean`. -/
@[to_additive /-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant
`C` such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/Normed/Operator/Basic.lean`. -/]
/--
theorem `MonoidHomClass.lipschitz_of_bound` / 定理 `MonoidHomClass.lipschitz_of_bound`

English:
theorem MonoidHomClass.lipschitz_of_bound
  statement: [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Real)
  proof: LipschitzWith.of_dist_le' fun x y => by
    simpa only [dist_eq_norm_inv_mul, map_mul, map_inv] using h (x⁻¹ * y)

@[to_additive]

中文:
定理 幺半群态射类.lipschitz_of_bound
  结论: [幺半群态射类 𝓕 E F] (f : 𝓕) (C : 实数)
  证明: LipschitzWith.of_dist_le' fun x y => by
    simpa only [dist_eq_norm_inv_mul, map_mul, map_inv] using h (x⁻¹ * y)

@[to_additive]

Depends on / 依赖: LipschitzWith, LipschitzWith.of_dist_le, dist_eq_norm_inv_mul, map_inv, map_mul, of_dist_le
-/
theorem MonoidHomClass.lipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Real)
    (h : forall x, ‖f x‖ <= C * ‖x‖) : LipschitzWith (Real.toNNReal C) f :=
  LipschitzWith.of_dist_le' fun x y => by
    simpa only [dist_eq_norm_inv_mul, map_mul, map_inv] using h (x⁻¹ * y)

@[to_additive]
/--
theorem `lipschitzOnWith_iff_norm_inv_mul_le` / 定理 `lipschitzOnWith_iff_norm_inv_mul_le`

English:
theorem lipschitzOnWith_iff_norm_inv_mul_le
  given: {f : E -> F} {C : Real>=0}
  proof: by
  simp only [lipschitzOnWith_iff_dist_le_mul, dist_eq_norm_inv_mul]

alias ⟨LipschitzOnWith.norm_inv_mul_le, _⟩ := lipschitzOnWith_iff_norm_inv_mul_le

中文:
定理 lipschitzOnWith_iff_norm_inv_mul_le
  条件: {f : E -> F} {C : 实数>=0}
  证明: by
  simp only [lipschitzOnWith_iff_dist_le_mul, dist_eq_norm_inv_mul]

alias ⟨LipschitzOnWith.norm_inv_mul_le, _⟩ := lipschitzOnWith_iff_norm_inv_mul_le

Depends on / 依赖: dist_eq_norm_inv_mul, lipschitzOnWith_iff_dist_le_mul
-/
theorem lipschitzOnWith_iff_norm_inv_mul_le {f : E -> F} {C : Real>=0} :
    LipschitzOnWith C f s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> ‖(f x)⁻¹ * f y‖ <= C * ‖x⁻¹ * y‖ := by
  simp only [lipschitzOnWith_iff_dist_le_mul, dist_eq_norm_inv_mul]

alias ⟨LipschitzOnWith.norm_inv_mul_le, _⟩ := lipschitzOnWith_iff_norm_inv_mul_le

attribute [to_additive] LipschitzOnWith.norm_inv_mul_le

@[to_additive]
/--
theorem `LipschitzOnWith.norm_inv_mul_le_of_le` / 定理 `LipschitzOnWith.norm_inv_mul_le_of_le`

English:
theorem LipschitzOnWith.norm_inv_mul_le_of_le
  statement: {f : E -> F} {C : Real>=0} (h : LipschitzOnWith C f s)
  proof: (h.norm_inv_mul_le ha hb).trans by gcongr

@[to_additive]

中文:
定理 LipschitzOnWith.norm_inv_mul_le_of_le
  结论: {f : E -> F} {C : 实数>=0} (h : LipschitzOnWith C f s)
  证明: (h.norm_inv_mul_le ha hb).trans by gcongr

@[to_additive]

Depends on / 依赖: h.norm_inv_mul_le, norm_inv_mul_le
-/
theorem LipschitzOnWith.norm_inv_mul_le_of_le {f : E -> F} {C : Real>=0} (h : LipschitzOnWith C f s)
    (ha : a in s) (hb : b in s) (hr : ‖a⁻¹ * b‖ <= r) : ‖(f a)⁻¹ * f b‖ <= C * r :=
(h.norm_inv_mul_le ha hb).trans by gcongr

@[to_additive]
/--
theorem `lipschitzWith_iff_norm_inv_mul_le` / 定理 `lipschitzWith_iff_norm_inv_mul_le`

English:
theorem lipschitzWith_iff_norm_inv_mul_le
  given: {f : E -> F} {C : Real>=0}
  proof: by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_inv_mul]

alias ⟨LipschitzWith.norm_inv_mul_le, _⟩ := lipschitzWith_iff_norm_inv_mul_le

中文:
定理 lipschitzWith_iff_norm_inv_mul_le
  条件: {f : E -> F} {C : 实数>=0}
  证明: by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_inv_mul]

alias ⟨LipschitzWith.norm_inv_mul_le, _⟩ := lipschitzWith_iff_norm_inv_mul_le

Depends on / 依赖: dist_eq_norm_inv_mul, lipschitzWith_iff_dist_le_mul
-/
theorem lipschitzWith_iff_norm_inv_mul_le {f : E -> F} {C : Real>=0} :
    LipschitzWith C f ↔ forall x y, ‖(f x)⁻¹ * f y‖ <= C * ‖x⁻¹ * y‖ := by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_inv_mul]

alias ⟨LipschitzWith.norm_inv_mul_le, _⟩ := lipschitzWith_iff_norm_inv_mul_le

attribute [to_additive] LipschitzWith.norm_inv_mul_le

@[to_additive]
/--
theorem `LipschitzWith.norm_inv_mul_le_of_le` / 定理 `LipschitzWith.norm_inv_mul_le_of_le`

English:
theorem LipschitzWith.norm_inv_mul_le_of_le
  statement: {f : E -> F} {C : Real>=0} (h : LipschitzWith C f)
  proof: (h.norm_inv_mul_le _ _).trans by gcongr

中文:
定理 LipschitzWith.norm_inv_mul_le_of_le
  结论: {f : E -> F} {C : 实数>=0} (h : LipschitzWith C f)
  证明: (h.norm_inv_mul_le _ _).trans by gcongr

Depends on / 依赖: h.norm_inv_mul_le, norm_inv_mul_le
-/
theorem LipschitzWith.norm_inv_mul_le_of_le {f : E -> F} {C : Real>=0} (h : LipschitzWith C f)
    (hr : ‖a⁻¹ * b‖ <= r) : ‖(f a)⁻¹ * f b‖ <= C * r :=
(h.norm_inv_mul_le _ _).trans by gcongr

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. -/
@[to_additive /-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant
`C` such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. -/]
/--
theorem `MonoidHomClass.continuous_of_bound` / 定理 `MonoidHomClass.continuous_of_bound`

English:
theorem MonoidHomClass.continuous_of_bound
  statement: [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Real)
  proof: (MonoidHomClass.lipschitz_of_bound f C h).continuous

@[to_additive]

中文:
定理 幺半群态射类.continuous_of_bound
  结论: [幺半群态射类 𝓕 E F] (f : 𝓕) (C : 实数)
  证明: (MonoidHomClass.lipschitz_of_bound f C h).continuous

@[to_additive]

Depends on / 依赖: MonoidHomClass, MonoidHomClass.lipschitz_of_bound, continuous, lipschitz_of_bound
-/
theorem MonoidHomClass.continuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Real)
    (h : forall x, ‖f x‖ <= C * ‖x‖) : Continuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).continuous

@[to_additive]
/--
theorem `MonoidHomClass.uniformContinuous_of_bound` / 定理 `MonoidHomClass.uniformContinuous_of_bound`

English:
theorem MonoidHomClass.uniformContinuous_of_bound
  statement: [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Real)
  proof: (MonoidHomClass.lipschitz_of_bound f C h).uniformContinuous

@[to_additive]

中文:
定理 幺半群态射类.uniformContinuous_of_bound
  结论: [幺半群态射类 𝓕 E F] (f : 𝓕) (C : 实数)
  证明: (MonoidHomClass.lipschitz_of_bound f C h).uniformContinuous

@[to_additive]

Depends on / 依赖: MonoidHomClass, MonoidHomClass.lipschitz_of_bound, lipschitz_of_bound, uniformContinuous
-/
theorem MonoidHomClass.uniformContinuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Real)
    (h : forall x, ‖f x‖ <= C * ‖x‖) : UniformContinuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).uniformContinuous

@[to_additive]
/--
theorem `MonoidHomClass.isometry_iff_norm` / 定理 `MonoidHomClass.isometry_iff_norm`

English:
theorem MonoidHomClass.isometry_iff_norm
  given: [MonoidHomClass 𝓕 E F] (f : 𝓕)
  proof: by
  simp only [isometry_iff_dist_eq, dist_eq_norm_inv_mul, ← map_inv, ← map_mul]
  refine ⟨fun h x => ?_, fun h x y => h _⟩
  simpa using h x 1

alias ⟨_, MonoidHomClass.isometry_of_norm⟩ := MonoidHomClass.isometry_iff_norm

中文:
定理 幺半群态射类.isometry_iff_norm
  条件: [幺半群态射类 𝓕 E F] (f : 𝓕)
  证明: by
  simp only [isometry_iff_dist_eq, dist_eq_norm_inv_mul, ← map_inv, ← map_mul]
  refine ⟨fun h x => ?_, fun h x y => h _⟩
  simpa using h x 1

alias ⟨_, MonoidHomClass.isometry_of_norm⟩ := MonoidHomClass.isometry_iff_norm

Depends on / 依赖: dist_eq_norm_inv_mul, isometry_iff_dist_eq, map_inv, map_mul
-/
theorem MonoidHomClass.isometry_iff_norm [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    Isometry f ↔ forall x, ‖f x‖ = ‖x‖ := by
  simp only [isometry_iff_dist_eq, dist_eq_norm_inv_mul, ← map_inv, ← map_mul]
  refine ⟨fun h x => ?_, fun h x y => h _⟩
  simpa using h x 1

alias ⟨_, MonoidHomClass.isometry_of_norm⟩ := MonoidHomClass.isometry_iff_norm

attribute [to_additive] MonoidHomClass.isometry_of_norm

section NNNorm

@[to_additive]
/--
theorem `MonoidHomClass.lipschitz_of_bound_nnnorm` / 定理 `MonoidHomClass.lipschitz_of_bound_nnnorm`

English:
theorem MonoidHomClass.lipschitz_of_bound_nnnorm
  statement: [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Real>=0)
  proof: @Real.toNNReal_coe C ▸ MonoidHomClass.lipschitz_of_bound f C h

@[to_additive]

中文:
定理 幺半群态射类.lipschitz_of_bound_nnnorm
  结论: [幺半群态射类 𝓕 E F] (f : 𝓕) (C : 实数>=0)
  证明: @Real.toNNReal_coe C ▸ MonoidHomClass.lipschitz_of_bound f C h

@[to_additive]

Depends on / 依赖: MonoidHomClass, MonoidHomClass.lipschitz_of_bound, Real.toNNReal_coe, lipschitz_of_bound, toNNReal_coe
-/
theorem MonoidHomClass.lipschitz_of_bound_nnnorm [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Real>=0)
    (h : forall x, ‖f x‖₊ <= C * ‖x‖₊) : LipschitzWith C f :=
  @Real.toNNReal_coe C ▸ MonoidHomClass.lipschitz_of_bound f C h

@[to_additive]
/--
theorem `MonoidHomClass.antilipschitz_of_bound` / 定理 `MonoidHomClass.antilipschitz_of_bound`

English:
theorem MonoidHomClass.antilipschitz_of_bound
  statement: [MonoidHomClass 𝓕 E F] (f : 𝓕) {K : Real>=0}
  proof: AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [dist_eq_norm_inv_mul, map_inv, map_mul] using h (x⁻¹ * y)

@[to_additive LipschitzWith.norm_le_mul]

中文:
定理 幺半群态射类.antilipschitz_of_bound
  结论: [幺半群态射类 𝓕 E F] (f : 𝓕) {K : 实数>=0}
  证明: AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [dist_eq_norm_inv_mul, map_inv, map_mul] using h (x⁻¹ * y)

@[to_additive LipschitzWith.norm_le_mul]

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, dist_eq_norm_inv_mul, map_inv, map_mul, of_le_mul_dist
-/
theorem MonoidHomClass.antilipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) {K : Real>=0}
    (h : forall x, ‖x‖ <= K * ‖f x‖) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [dist_eq_norm_inv_mul, map_inv, map_mul] using h (x⁻¹ * y)

@[to_additive LipschitzWith.norm_le_mul]
/--
theorem `LipschitzWith.norm_le_mul'` / 定理 `LipschitzWith.norm_le_mul'`

English:
theorem LipschitzWith.norm_le_mul'
  statement: {f : E -> F} {K : Real>=0} (h : LipschitzWith K f) (hf : f 1 = 1)
  proof: by simpa only [dist_one_right, hf] using h.dist_le_mul x 1

@[to_additive LipschitzWith.nnorm_le_mul]

中文:
定理 LipschitzWith.norm_le_mul'
  结论: {f : E -> F} {K : 实数>=0} (h : LipschitzWith K f) (hf : f 1 = 1)
  证明: by simpa only [dist_one_right, hf] using h.dist_le_mul x 1

@[to_additive LipschitzWith.nnorm_le_mul]

Depends on / 依赖: dist_le_mul, dist_one_right, h.dist_le_mul
-/
theorem LipschitzWith.norm_le_mul' {f : E -> F} {K : Real>=0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖ <= K * ‖x‖ := by simpa only [dist_one_right, hf] using h.dist_le_mul x 1

@[to_additive LipschitzWith.nnorm_le_mul]
/--
theorem `LipschitzWith.nnorm_le_mul'` / 定理 `LipschitzWith.nnorm_le_mul'`

English:
theorem LipschitzWith.nnorm_le_mul'
  statement: {f : E -> F} {K : Real>=0} (h : LipschitzWith K f) (hf : f 1 = 1)
  proof: h.norm_le_mul' hf x

@[to_additive AntilipschitzWith.le_mul_norm]

中文:
定理 LipschitzWith.nnorm_le_mul'
  结论: {f : E -> F} {K : 实数>=0} (h : LipschitzWith K f) (hf : f 1 = 1)
  证明: h.norm_le_mul' hf x

@[to_additive AntilipschitzWith.le_mul_norm]

Depends on / 依赖: h.norm_le_mul, norm_le_mul
-/
theorem LipschitzWith.nnorm_le_mul' {f : E -> F} {K : Real>=0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖₊ <= K * ‖x‖₊ :=
  h.norm_le_mul' hf x

@[to_additive AntilipschitzWith.le_mul_norm]
/--
theorem `AntilipschitzWith.le_mul_norm'` / 定理 `AntilipschitzWith.le_mul_norm'`

English:
theorem AntilipschitzWith.le_mul_norm'
  statement: {f : E -> F} {K : Real>=0} (h : AntilipschitzWith K f)
  proof: by
  simpa only [dist_one_right, hf] using h.le_mul_dist x 1

@[to_additive antilipschitzWith_iff_exists_mul_le_norm]

中文:
定理 AntilipschitzWith.le_mul_norm'
  结论: {f : E -> F} {K : 实数>=0} (h : AntilipschitzWith K f)
  证明: by
  simpa only [dist_one_right, hf] using h.le_mul_dist x 1

@[to_additive antilipschitzWith_iff_exists_mul_le_norm]

Depends on / 依赖: dist_one_right, h.le_mul_dist, le_mul_dist
-/
theorem AntilipschitzWith.le_mul_norm' {f : E -> F} {K : Real>=0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖ <= K * ‖f x‖ := by
  simpa only [dist_one_right, hf] using h.le_mul_dist x 1

@[to_additive antilipschitzWith_iff_exists_mul_le_norm]
/--
theorem `antilipschitzWith_iff_exists_mul_le_norm'` / 定理 `antilipschitzWith_iff_exists_mul_le_norm'`

English:
theorem antilipschitzWith_iff_exists_mul_le_norm'
  given: [MonoidHomClass 𝓕 E F] {f : 𝓕}
  proof: by
  refine ⟨fun ⟨K, hK⟩ => ⟨(K + 1)⁻¹, by positivity, fun x => ?_⟩, fun ⟨c, hc0, hc⟩ =>
    ⟨.mk c⁻¹ (by positivity), MonoidHomClass.antilipschitz_of_bound f fun x => ?_⟩⟩
  · grw [hK.le_mul_norm' (map_one f), ← mul_assoc]
    exact mul_le_of_le_one_left (norm_nonneg' (f x)) (by simp [field])
  · grw [← hc, NNReal.coe_mk, inv_mul_cancel_left₀ hc0.ne']

@[to_additive AntilipschitzWith.le_mul_nnnorm]

中文:
定理 antilipschitzWith_iff_存在_mul_le_norm'
  条件: [幺半群态射类 𝓕 E F] {f : 𝓕}
  证明: by
  refine ⟨fun ⟨K, hK⟩ => ⟨(K + 1)⁻¹, by positivity, fun x => ?_⟩, fun ⟨c, hc0, hc⟩ =>
    ⟨.mk c⁻¹ (by positivity), MonoidHomClass.antilipschitz_of_bound f fun x => ?_⟩⟩
  · grw [hK.le_mul_norm' (map_one f), ← mul_assoc]
    exact mul_le_of_le_one_left (norm_nonneg' (f x)) (by simp [field])
  · grw [← hc, NNReal.coe_mk, inv_mul_cancel_left₀ hc0.ne']

@[to_additive AntilipschitzWith.le_mul_nnnorm]

Depends on / 依赖: MonoidHomClass, MonoidHomClass.antilipschitz_of_bound, NNReal, NNReal.coe_mk, antilipschitz_of_bound, coe_mk, hK.le_mul_norm, hc0.ne, le_mul_norm, map_one, mul_assoc, mul_le_of_le_one_left, norm_nonneg
-/
theorem antilipschitzWith_iff_exists_mul_le_norm' [MonoidHomClass 𝓕 E F] {f : 𝓕} :
    (exists K, AntilipschitzWith K f) ↔ exists c > 0, forall x, c * ‖x‖ <= ‖f x‖ := by
  refine ⟨fun ⟨K, hK⟩ => ⟨(K + 1)⁻¹, by positivity, fun x => ?_⟩, fun ⟨c, hc0, hc⟩ =>
    ⟨.mk c⁻¹ (by positivity), MonoidHomClass.antilipschitz_of_bound f fun x => ?_⟩⟩
  · grw [hK.le_mul_norm' (map_one f), ← mul_assoc]
    exact mul_le_of_le_one_left (norm_nonneg' (f x)) (by simp [field])
  · grw [← hc, NNReal.coe_mk, inv_mul_cancel_left₀ hc0.ne']

@[to_additive AntilipschitzWith.le_mul_nnnorm]
/--
theorem `AntilipschitzWith.le_mul_nnnorm'` / 定理 `AntilipschitzWith.le_mul_nnnorm'`

English:
theorem AntilipschitzWith.le_mul_nnnorm'
  statement: {f : E -> F} {K : Real>=0} (h : AntilipschitzWith K f)
  proof: h.le_mul_norm' hf x

@[to_additive]

中文:
定理 AntilipschitzWith.le_mul_nnnorm'
  结论: {f : E -> F} {K : 实数>=0} (h : AntilipschitzWith K f)
  证明: h.le_mul_norm' hf x

@[to_additive]

Depends on / 依赖: h.le_mul_norm, le_mul_norm
-/
theorem AntilipschitzWith.le_mul_nnnorm' {f : E -> F} {K : Real>=0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖₊ <= K * ‖f x‖₊ :=
  h.le_mul_norm' hf x

@[to_additive]
/--
theorem `OneHomClass.bound_of_antilipschitz` / 定理 `OneHomClass.bound_of_antilipschitz`

English:
theorem OneHomClass.bound_of_antilipschitz
  statement: [OneHomClass 𝓕 E F] (f : 𝓕) {K : Real>=0}
  proof: h.le_mul_nnnorm' (map_one f) x

@[to_additive]

中文:
定理 幺态射类.bound_of_antilipschitz
  结论: [幺态射类 𝓕 E F] (f : 𝓕) {K : 实数>=0}
  证明: h.le_mul_nnnorm' (map_one f) x

@[to_additive]

Depends on / 依赖: h.le_mul_nnnorm, le_mul_nnnorm, map_one
-/
theorem OneHomClass.bound_of_antilipschitz [OneHomClass 𝓕 E F] (f : 𝓕) {K : Real>=0}
    (h : AntilipschitzWith K f) (x) : ‖x‖ <= K * ‖f x‖ :=
  h.le_mul_nnnorm' (map_one f) x

@[to_additive]
/--
theorem `Isometry.nnnorm_map_of_map_one` / 定理 `Isometry.nnnorm_map_of_map_one`

English:
theorem Isometry.nnnorm_map_of_map_one
  given: {f : E -> F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E)
  proof: Subtype.ext hi.norm_map_of_map_one h₁ x

中文:
定理 等距.nnnorm_map_of_map_one
  条件: {f : E -> F} (hi : 等距 f) (h₁ : f 1 = 1) (x : E)
  证明: Subtype.ext hi.norm_map_of_map_one h₁ x

Depends on / 依赖: Subtype, Subtype.ext, hi.norm_map_of_map_one, norm_map_of_map_one
-/
theorem Isometry.nnnorm_map_of_map_one {f : E -> F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖₊ = ‖x‖₊ :=
Subtype.ext hi.norm_map_of_map_one h₁ x

end NNNorm

@[to_additive lipschitzWith_one_norm]
/--
theorem `lipschitzWith_one_norm'` / 定理 `lipschitzWith_one_norm'`

English:
theorem lipschitzWith_one_norm'
  statement: LipschitzWith 1 (norm : E -> Real)
  proof: by
  simpa using LipschitzWith.dist_right (1 : E)

@[to_additive lipschitzWith_one_nnnorm]

中文:
定理 lipschitzWith_one_norm'
  结论: LipschitzWith 1 (norm : E -> 实数)
  证明: by
  simpa using LipschitzWith.dist_right (1 : E)

@[to_additive lipschitzWith_one_nnnorm]

Depends on / 依赖: LipschitzWith, LipschitzWith.dist_right, dist_right
-/
theorem lipschitzWith_one_norm' : LipschitzWith 1 (norm : E -> Real) := by
  simpa using LipschitzWith.dist_right (1 : E)

@[to_additive lipschitzWith_one_nnnorm]
/--
theorem `lipschitzWith_one_nnnorm'` / 定理 `lipschitzWith_one_nnnorm'`

English:
theorem lipschitzWith_one_nnnorm'
  statement: LipschitzWith 1 (NNNorm.nnnorm : E -> Real>=0)
  proof: lipschitzWith_one_norm'

@[to_additive (attr := fun_prop) uniformContinuous_norm]

中文:
定理 lipschitzWith_one_nnnorm'
  结论: LipschitzWith 1 (NN范数.nnnorm : E -> 实数>=0)
  证明: lipschitzWith_one_norm'

@[to_additive (attr := fun_prop) uniformContinuous_norm]

Depends on / 依赖: lipschitzWith_one_norm
-/
theorem lipschitzWith_one_nnnorm' : LipschitzWith 1 (NNNorm.nnnorm : E -> Real>=0) :=
  lipschitzWith_one_norm'

@[to_additive (attr := fun_prop) uniformContinuous_norm]
/--
theorem `uniformContinuous_norm'` / 定理 `uniformContinuous_norm'`

English:
theorem uniformContinuous_norm'
  statement: UniformContinuous (norm : E -> Real)
  proof: lipschitzWith_one_norm'.uniformContinuous

@[to_additive (attr := fun_prop) uniformContinuous_nnnorm]

中文:
定理 uniformContinuous_norm'
  结论: 一致连续 (norm : E -> 实数)
  证明: lipschitzWith_one_norm'.uniformContinuous

@[to_additive (attr := fun_prop) uniformContinuous_nnnorm]

Depends on / 依赖: lipschitzWith_one_norm, uniformContinuous
-/
theorem uniformContinuous_norm' : UniformContinuous (norm : E -> Real) :=
  lipschitzWith_one_norm'.uniformContinuous

@[to_additive (attr := fun_prop) uniformContinuous_nnnorm]
/--
theorem `uniformContinuous_nnnorm'` / 定理 `uniformContinuous_nnnorm'`

English:
theorem uniformContinuous_nnnorm'
  statement: UniformContinuous fun a : E => ‖a‖₊
  proof: uniformContinuous_norm'.subtype_mk _

中文:
定理 uniformContinuous_nnnorm'
  结论: 一致连续 fun a : E => ‖a‖₊
  证明: uniformContinuous_norm'.subtype_mk _

Depends on / 依赖: subtype_mk, uniformContinuous_norm
-/
theorem uniformContinuous_nnnorm' : UniformContinuous fun a : E => ‖a‖₊ :=
  uniformContinuous_norm'.subtype_mk _

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a₁ a₂ b₁ b₂ : E} {r₁ r₂ : Real}

@[to_additive]
/--
Instance `NormedGroup.to_isIsometricSMul_right` / 实例 `NormedGroup.to_isIsometricSMul_right`

English:
instance NormedGroup.to_isIsometricSMul_right
  signature: : IsIsometricSMul Eᵐᵒᵖ E
  body: ⟨fun a => Isometry.of_dist_eq fun b c => by simp⟩

@[to_additive (attr := simp)]

中文:
实例 赋范群.to_isIsometricSMul_right
  签名: : 是是ometricSMul Eᵐᵒᵖ E
  定义体: ⟨fun a => Isometry.of_dist_eq fun b c => by simp⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Isometry, Isometry.of_dist_eq, of_dist_eq
-/
instance NormedGroup.to_isIsometricSMul_right : IsIsometricSMul Eᵐᵒᵖ E :=
  ⟨fun a => Isometry.of_dist_eq fun b c => by simp⟩

@[to_additive (attr := simp)]
/--
theorem `dist_mul_self_right` / 定理 `dist_mul_self_right`

English:
theorem dist_mul_self_right
  given: (a b : E)
  statement: dist a (b * a) = ‖b‖
  proof: by
  rw [← dist_one_left]; rw [← dist_mul_left a 1 b]; rw [mul_one]; rw [mul_comm]

@[to_additive (attr := simp)]

中文:
定理 dist_mul_self_right
  条件: (a b : E)
  结论: dist a (b * a) = ‖b‖
  证明: by
  rw [← dist_one_left]; rw [← dist_mul_left a 1 b]; rw [mul_one]; rw [mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: dist_mul_left, dist_one_left, mul_comm, mul_one
-/
theorem dist_mul_self_right (a b : E) : dist a (b * a) = ‖b‖ := by
  rw [← dist_one_left]; rw [← dist_mul_left a 1 b]; rw [mul_one]; rw [mul_comm]

@[to_additive (attr := simp)]
/--
theorem `dist_mul_self_left` / 定理 `dist_mul_self_left`

English:
theorem dist_mul_self_left
  given: (a b : E)
  statement: dist (b * a) a = ‖b‖
  proof: by
  rw [dist_comm]; rw [dist_mul_self_right]

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this

中文:
定理 dist_mul_self_left
  条件: (a b : E)
  结论: dist (b * a) a = ‖b‖
  证明: by
  rw [dist_comm]; rw [dist_mul_self_right]

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this

Depends on / 依赖: dist_comm, dist_mul_self_right
-/
theorem dist_mul_self_left (a b : E) : dist (b * a) a = ‖b‖ := by
  rw [dist_comm]; rw [dist_mul_self_right]

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this
/--
theorem `dist_self_div_right` / 定理 `dist_self_div_right`

English:
theorem dist_self_div_right
  given: (a b : E)
  statement: dist a (a / b) = ‖b‖
  proof: by
  rw [div_eq_mul_inv]; rw [dist_self_mul_right]; rw [norm_inv']

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this

中文:
定理 dist_self_div_right
  条件: (a b : E)
  结论: dist a (a / b) = ‖b‖
  证明: by
  rw [div_eq_mul_inv]; rw [dist_self_mul_right]; rw [norm_inv']

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this

Depends on / 依赖: dist_self_mul_right, div_eq_mul_inv, norm_inv
-/
theorem dist_self_div_right (a b : E) : dist a (a / b) = ‖b‖ := by
  rw [div_eq_mul_inv]; rw [dist_self_mul_right]; rw [norm_inv']

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this
/--
theorem `dist_self_div_left` / 定理 `dist_self_div_left`

English:
theorem dist_self_div_left
  given: (a b : E)
  statement: dist (a / b) a = ‖b‖
  proof: by
  rw [dist_comm]; rw [dist_self_div_right]

@[to_additive (attr := simp)]

中文:
定理 dist_self_div_left
  条件: (a b : E)
  结论: dist (a / b) a = ‖b‖
  证明: by
  rw [dist_comm]; rw [dist_self_div_right]

@[to_additive (attr := simp)]

Depends on / 依赖: dist_comm, dist_self_div_right
-/
theorem dist_self_div_left (a b : E) : dist (a / b) a = ‖b‖ := by
  rw [dist_comm]; rw [dist_self_div_right]

@[to_additive (attr := simp)]
/--
theorem `dist_div_eq_dist_mul_left` / 定理 `dist_div_eq_dist_mul_left`

English:
theorem dist_div_eq_dist_mul_left
  given: (a b c : E)
  statement: dist (a / b) c = dist a (c * b)
  proof: by
  rw [← dist_mul_right _ _ b]; rw [div_mul_cancel]

@[to_additive (attr := simp)]

中文:
定理 dist_div_eq_dist_mul_left
  条件: (a b c : E)
  结论: dist (a / b) c = dist a (c * b)
  证明: by
  rw [← dist_mul_right _ _ b]; rw [div_mul_cancel]

@[to_additive (attr := simp)]

Depends on / 依赖: dist_mul_right, div_mul_cancel
-/
theorem dist_div_eq_dist_mul_left (a b c : E) : dist (a / b) c = dist a (c * b) := by
  rw [← dist_mul_right _ _ b]; rw [div_mul_cancel]

@[to_additive (attr := simp)]
/--
theorem `dist_div_eq_dist_mul_right` / 定理 `dist_div_eq_dist_mul_right`

English:
theorem dist_div_eq_dist_mul_right
  given: (a b c : E)
  statement: dist a (b / c) = dist (a * c) b
  proof: by
  rw [← dist_mul_right _ _ c]; rw [div_mul_cancel]

@[to_additive]

中文:
定理 dist_div_eq_dist_mul_right
  条件: (a b c : E)
  结论: dist a (b / c) = dist (a * c) b
  证明: by
  rw [← dist_mul_right _ _ c]; rw [div_mul_cancel]

@[to_additive]

Depends on / 依赖: dist_mul_right, div_mul_cancel
-/
theorem dist_div_eq_dist_mul_right (a b c : E) : dist a (b / c) = dist (a * c) b := by
  rw [← dist_mul_right _ _ c]; rw [div_mul_cancel]

@[to_additive]
/--
theorem `dist_mul_mul_le` / 定理 `dist_mul_mul_le`

English:
theorem dist_mul_mul_le
  given: (a₁ a₂ b₁ b₂ : E)
  statement: dist (a₁ * a₂) (b₁ * b₂) <= dist a₁ b₁ + dist a₂ b₂
  proof: by
  simpa only [dist_mul_left, dist_mul_right] using dist_triangle (a₁ * a₂) (b₁ * a₂) (b₁ * b₂)

@[to_additive]

中文:
定理 dist_mul_mul_le
  条件: (a₁ a₂ b₁ b₂ : E)
  结论: dist (a₁ * a₂) (b₁ * b₂) <= dist a₁ b₁ + dist a₂ b₂
  证明: by
  simpa only [dist_mul_left, dist_mul_right] using dist_triangle (a₁ * a₂) (b₁ * a₂) (b₁ * b₂)

@[to_additive]

Depends on / 依赖: dist_mul_left, dist_mul_right, dist_triangle
-/
theorem dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ * b₂) <= dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [dist_mul_left, dist_mul_right] using dist_triangle (a₁ * a₂) (b₁ * a₂) (b₁ * b₂)

@[to_additive]
/--
theorem `dist_mul_mul_le_of_le` / 定理 `dist_mul_mul_le_of_le`

English:
theorem dist_mul_mul_le_of_le
  given: (h₁ : dist a₁ b₁ <= r₁) (h₂ : dist a₂ b₂ <= r₂)
  proof: (dist_mul_mul_le a₁ a₂ b₁ b₂).trans add_le_add h₁ h₂

@[to_additive]

中文:
定理 dist_mul_mul_le_of_le
  条件: (h₁ : dist a₁ b₁ <= r₁) (h₂ : dist a₂ b₂ <= r₂)
  证明: (dist_mul_mul_le a₁ a₂ b₁ b₂).trans add_le_add h₁ h₂

@[to_additive]

Depends on / 依赖: add_le_add, dist_mul_mul_le
-/
theorem dist_mul_mul_le_of_le (h₁ : dist a₁ b₁ <= r₁) (h₂ : dist a₂ b₂ <= r₂) :
    dist (a₁ * a₂) (b₁ * b₂) <= r₁ + r₂ :=
(dist_mul_mul_le a₁ a₂ b₁ b₂).trans add_le_add h₁ h₂

@[to_additive]
/--
theorem `dist_div_div_le` / 定理 `dist_div_div_le`

English:
theorem dist_div_div_le
  given: (a₁ a₂ b₁ b₂ : E)
  statement: dist (a₁ / a₂) (b₁ / b₂) <= dist a₁ b₁ + dist a₂ b₂
  proof: by
  simpa only [div_eq_mul_inv, dist_inv_inv] using dist_mul_mul_le a₁ a₂⁻¹ b₁ b₂⁻¹

@[to_additive]

中文:
定理 dist_div_div_le
  条件: (a₁ a₂ b₁ b₂ : E)
  结论: dist (a₁ / a₂) (b₁ / b₂) <= dist a₁ b₁ + dist a₂ b₂
  证明: by
  simpa only [div_eq_mul_inv, dist_inv_inv] using dist_mul_mul_le a₁ a₂⁻¹ b₁ b₂⁻¹

@[to_additive]

Depends on / 依赖: dist_inv_inv, dist_mul_mul_le, div_eq_mul_inv
-/
theorem dist_div_div_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ / a₂) (b₁ / b₂) <= dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [div_eq_mul_inv, dist_inv_inv] using dist_mul_mul_le a₁ a₂⁻¹ b₁ b₂⁻¹

@[to_additive]
/--
theorem `dist_div_div_le_of_le` / 定理 `dist_div_div_le_of_le`

English:
theorem dist_div_div_le_of_le
  given: (h₁ : dist a₁ b₁ <= r₁) (h₂ : dist a₂ b₂ <= r₂)
  proof: (dist_div_div_le a₁ a₂ b₁ b₂).trans add_le_add h₁ h₂

@[to_additive]

中文:
定理 dist_div_div_le_of_le
  条件: (h₁ : dist a₁ b₁ <= r₁) (h₂ : dist a₂ b₂ <= r₂)
  证明: (dist_div_div_le a₁ a₂ b₁ b₂).trans add_le_add h₁ h₂

@[to_additive]

Depends on / 依赖: add_le_add, dist_div_div_le
-/
theorem dist_div_div_le_of_le (h₁ : dist a₁ b₁ <= r₁) (h₂ : dist a₂ b₂ <= r₂) :
    dist (a₁ / a₂) (b₁ / b₂) <= r₁ + r₂ :=
(dist_div_div_le a₁ a₂ b₁ b₂).trans add_le_add h₁ h₂

@[to_additive]
/--
theorem `abs_dist_sub_le_dist_mul_mul` / 定理 `abs_dist_sub_le_dist_mul_mul`

English:
theorem abs_dist_sub_le_dist_mul_mul
  given: (a₁ a₂ b₁ b₂ : E)
  proof: by
  simpa only [dist_mul_left, dist_mul_right, dist_comm b₂] using
    abs_dist_sub_le (a₁ * a₂) (b₁ * b₂) (b₁ * a₂)

中文:
定理 abs_dist_sub_le_dist_mul_mul
  条件: (a₁ a₂ b₁ b₂ : E)
  证明: by
  simpa only [dist_mul_left, dist_mul_right, dist_comm b₂] using
    abs_dist_sub_le (a₁ * a₂) (b₁ * b₂) (b₁ * a₂)

Depends on / 依赖: abs_dist_sub_le, dist_comm, dist_mul_left, dist_mul_right
-/
theorem abs_dist_sub_le_dist_mul_mul (a₁ a₂ b₁ b₂ : E) :
    |dist a₁ b₁ - dist a₂ b₂| <= dist (a₁ * a₂) (b₁ * b₂) := by
  simpa only [dist_mul_left, dist_mul_right, dist_comm b₂] using
    abs_dist_sub_le (a₁ * a₂) (b₁ * b₂) (b₁ * a₂)

open Finset

@[to_additive]
/--
theorem `nndist_mul_mul_le` / 定理 `nndist_mul_mul_le`

English:
theorem nndist_mul_mul_le
  given: (a₁ a₂ b₁ b₂ : E)
  proof: NNReal.coe_le_coe.1 dist_mul_mul_le a₁ a₂ b₁ b₂

@[to_additive]

中文:
定理 nndist_mul_mul_le
  条件: (a₁ a₂ b₁ b₂ : E)
  证明: NNReal.coe_le_coe.1 dist_mul_mul_le a₁ a₂ b₁ b₂

@[to_additive]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, dist_mul_mul_le
-/
theorem nndist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    nndist (a₁ * a₂) (b₁ * b₂) <= nndist a₁ b₁ + nndist a₂ b₂ :=
NNReal.coe_le_coe.1 dist_mul_mul_le a₁ a₂ b₁ b₂

@[to_additive]
/--
theorem `edist_mul_mul_le` / 定理 `edist_mul_mul_le`

English:
theorem edist_mul_mul_le
  given: (a₁ a₂ b₁ b₂ : E)
  proof: by
  simp only [edist_nndist]
  norm_cast
  apply nndist_mul_mul_le

中文:
定理 edist_mul_mul_le
  条件: (a₁ a₂ b₁ b₂ : E)
  证明: by
  simp only [edist_nndist]
  norm_cast
  apply nndist_mul_mul_le

Depends on / 依赖: edist_nndist, nndist_mul_mul_le
-/
theorem edist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    edist (a₁ * a₂) (b₁ * b₂) <= edist a₁ b₁ + edist a₂ b₂ := by
  simp only [edist_nndist]
  norm_cast
  apply nndist_mul_mul_le

section PseudoEMetricSpace
variable {α E : Type*} [SeminormedCommGroup E] [PseudoEMetricSpace α] {K Kf Kg : Real>=0}
  {f g : α -> E} {s : Set α}

@[to_additive (attr := simp)]
/--
lemma `lipschitzWith_inv_iff` / 引理 `lipschitzWith_inv_iff`

English:
lemma lipschitzWith_inv_iff
  statement: LipschitzWith K f⁻¹ ↔ LipschitzWith K f
  proof: by simp [LipschitzWith]

@[to_additive (attr := simp)]

中文:
引理 lipschitzWith_inv_iff
  结论: LipschitzWith K f⁻¹ ↔ LipschitzWith K f
  证明: by simp [LipschitzWith]

@[to_additive (attr := simp)]

Depends on / 依赖: LipschitzWith
-/
lemma lipschitzWith_inv_iff : LipschitzWith K f⁻¹ ↔ LipschitzWith K f := by simp [LipschitzWith]

@[to_additive (attr := simp)]
/--
lemma `antilipschitzWith_inv_iff` / 引理 `antilipschitzWith_inv_iff`

English:
lemma antilipschitzWith_inv_iff
  statement: AntilipschitzWith K f⁻¹ ↔ AntilipschitzWith K f
  proof: by
  simp [AntilipschitzWith]

@[to_additive (attr := simp)]

中文:
引理 antilipschitzWith_inv_iff
  结论: AntilipschitzWith K f⁻¹ ↔ AntilipschitzWith K f
  证明: by
  simp [AntilipschitzWith]

@[to_additive (attr := simp)]

Depends on / 依赖: AntilipschitzWith
-/
lemma antilipschitzWith_inv_iff : AntilipschitzWith K f⁻¹ ↔ AntilipschitzWith K f := by
  simp [AntilipschitzWith]

@[to_additive (attr := simp)]
/--
lemma `lipschitzOnWith_inv_iff` / 引理 `lipschitzOnWith_inv_iff`

English:
lemma lipschitzOnWith_inv_iff
  statement: LipschitzOnWith K f⁻¹ s ↔ LipschitzOnWith K f s
  proof: by
  simp [LipschitzOnWith]

@[to_additive (attr := simp)]

中文:
引理 lipschitzOnWith_inv_iff
  结论: LipschitzOnWith K f⁻¹ s ↔ LipschitzOnWith K f s
  证明: by
  simp [LipschitzOnWith]

@[to_additive (attr := simp)]

Depends on / 依赖: LipschitzOnWith
-/
lemma lipschitzOnWith_inv_iff : LipschitzOnWith K f⁻¹ s ↔ LipschitzOnWith K f s := by
  simp [LipschitzOnWith]

@[to_additive (attr := simp)]
/--
lemma `locallyLipschitz_inv_iff` / 引理 `locallyLipschitz_inv_iff`

English:
lemma locallyLipschitz_inv_iff
  statement: LocallyLipschitz f⁻¹ ↔ LocallyLipschitz f
  proof: by
  simp [LocallyLipschitz]

@[to_additive (attr := simp)]

中文:
引理 locallyLipschitz_inv_iff
  结论: LocallyLipschitz f⁻¹ ↔ LocallyLipschitz f
  证明: by
  simp [LocallyLipschitz]

@[to_additive (attr := simp)]

Depends on / 依赖: LocallyLipschitz
-/
lemma locallyLipschitz_inv_iff : LocallyLipschitz f⁻¹ ↔ LocallyLipschitz f := by
  simp [LocallyLipschitz]

@[to_additive (attr := simp)]
/--
lemma `locallyLipschitzOn_inv_iff` / 引理 `locallyLipschitzOn_inv_iff`

English:
lemma locallyLipschitzOn_inv_iff
  statement: LocallyLipschitzOn s f⁻¹ ↔ LocallyLipschitzOn s f
  proof: by
  simp [LocallyLipschitzOn]

@[to_additive] alias ⟨LipschitzWith.of_inv, LipschitzWith.inv⟩ := lipschitzWith_inv_iff
@[to_additive] alias ⟨AntilipschitzWith.of_inv, AntilipschitzWith.inv⟩ := antilipschitzWith_inv_iff
@[to_additive] alias ⟨LipschitzOnWith.of_inv, LipschitzOnWith.inv⟩ := lipschitzOnWith_inv_iff
@[to_additive] alias ⟨LocallyLipschitz.of_inv, LocallyLipschitz.inv⟩ := locallyLipschitz_inv_iff
@[to_additive]
alias ⟨LocallyLipschitzOn.of_inv, LocallyLipschitzOn.inv⟩ := locallyLipschitzOn_inv_iff

@[to_additive]

中文:
引理 locallyLipschitzOn_inv_iff
  结论: LocallyLipschitzOn s f⁻¹ ↔ LocallyLipschitzOn s f
  证明: by
  simp [LocallyLipschitzOn]

@[to_additive] alias ⟨LipschitzWith.of_inv, LipschitzWith.inv⟩ := lipschitzWith_inv_iff
@[to_additive] alias ⟨AntilipschitzWith.of_inv, AntilipschitzWith.inv⟩ := antilipschitzWith_inv_iff
@[to_additive] alias ⟨LipschitzOnWith.of_inv, LipschitzOnWith.inv⟩ := lipschitzOnWith_inv_iff
@[to_additive] alias ⟨LocallyLipschitz.of_inv, LocallyLipschitz.inv⟩ := locallyLipschitz_inv_iff
@[to_additive]
alias ⟨LocallyLipschitzOn.of_inv, LocallyLipschitzOn.inv⟩ := locallyLipschitzOn_inv_iff

@[to_additive]

Depends on / 依赖: LocallyLipschitzOn
-/
lemma locallyLipschitzOn_inv_iff : LocallyLipschitzOn s f⁻¹ ↔ LocallyLipschitzOn s f := by
  simp [LocallyLipschitzOn]

@[to_additive] alias ⟨LipschitzWith.of_inv, LipschitzWith.inv⟩ := lipschitzWith_inv_iff
@[to_additive] alias ⟨AntilipschitzWith.of_inv, AntilipschitzWith.inv⟩ := antilipschitzWith_inv_iff
@[to_additive] alias ⟨LipschitzOnWith.of_inv, LipschitzOnWith.inv⟩ := lipschitzOnWith_inv_iff
@[to_additive] alias ⟨LocallyLipschitz.of_inv, LocallyLipschitz.inv⟩ := locallyLipschitz_inv_iff
@[to_additive]
alias ⟨LocallyLipschitzOn.of_inv, LocallyLipschitzOn.inv⟩ := locallyLipschitzOn_inv_iff

@[to_additive]
/--
lemma `LipschitzOnWith.mul` / 引理 `LipschitzOnWith.mul`

English:
lemma LipschitzOnWith.mul
  given: (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
  proof: fun x hx y hy =>
  calc
    edist (f x * g x) (f y * g y) <= edist (f x) (f y) + edist (g x) (g y) :=
      edist_mul_mul_le _ _ _ _
    _ <= Kf * edist x y + Kg * edist x y := add_le_add (hf hx hy) (hg hx hy)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[to_additive]

中文:
引理 LipschitzOnWith.mul
  条件: (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
  证明: fun x hx y hy =>
  calc
    edist (f x * g x) (f y * g y) <= edist (f x) (f y) + edist (g x) (g y) :=
      edist_mul_mul_le _ _ _ _
    _ <= Kf * edist x y + Kg * edist x y := add_le_add (hf hx hy) (hg hx hy)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[to_additive]
-/
lemma LipschitzOnWith.mul (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf + Kg) (fun x => f x * g x) s := fun x hx y hy =>
  calc
    edist (f x * g x) (f y * g y) <= edist (f x) (f y) + edist (g x) (g y) :=
      edist_mul_mul_le _ _ _ _
    _ <= Kf * edist x y + Kg * edist x y := add_le_add (hf hx hy) (hg hx hy)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[to_additive]
/--
lemma `LipschitzWith.mul` / 引理 `LipschitzWith.mul`

English:
lemma LipschitzWith.mul
  given: (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
  proof: by
  simpa [← lipschitzOnWith_univ] using hf.lipschitzOnWith.mul hg.lipschitzOnWith

@[to_additive]

中文:
引理 LipschitzWith.mul
  条件: (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
  证明: by
  simpa [← lipschitzOnWith_univ] using hf.lipschitzOnWith.mul hg.lipschitzOnWith

@[to_additive]

Depends on / 依赖: hf.lipschitzOnWith.mul, hg.lipschitzOnWith, lipschitzOnWith, lipschitzOnWith_univ
-/
lemma LipschitzWith.mul (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x => f x * g x := by
  simpa [← lipschitzOnWith_univ] using hf.lipschitzOnWith.mul hg.lipschitzOnWith

@[to_additive]
/--
lemma `LocallyLipschitzOn.mul` / 引理 `LocallyLipschitzOn.mul`

English:
lemma LocallyLipschitzOn.mul
  given: (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g)
  proof: fun x hx => by
  obtain ⟨Kf, t, ht, hKf⟩ := hf hx
  obtain ⟨Kg, u, hu, hKg⟩ := hg hx
  exact ⟨Kf + Kg, t inter u, inter_mem ht hu,
    (hKf.mono Set.inter_subset_left).mul (hKg.mono Set.inter_subset_right)⟩

@[to_additive]

中文:
引理 LocallyLipschitzOn.mul
  条件: (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g)
  证明: fun x hx => by
  obtain ⟨Kf, t, ht, hKf⟩ := hf hx
  obtain ⟨Kg, u, hu, hKg⟩ := hg hx
  exact ⟨Kf + Kg, t inter u, inter_mem ht hu,
    (hKf.mono Set.inter_subset_left).mul (hKg.mono Set.inter_subset_right)⟩

@[to_additive]

Depends on / 依赖: Set.inter_subset_left, Set.inter_subset_right, hKf.mono, hKg.mono, inter_mem, inter_subset_left, inter_subset_right
-/
lemma LocallyLipschitzOn.mul (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s fun x => f x * g x := fun x hx => by
  obtain ⟨Kf, t, ht, hKf⟩ := hf hx
  obtain ⟨Kg, u, hu, hKg⟩ := hg hx
  exact ⟨Kf + Kg, t inter u, inter_mem ht hu,
    (hKf.mono Set.inter_subset_left).mul (hKg.mono Set.inter_subset_right)⟩

@[to_additive]
/--
lemma `LocallyLipschitz.mul` / 引理 `LocallyLipschitz.mul`

English:
lemma LocallyLipschitz.mul
  given: (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
  proof: by
  simpa [← locallyLipschitzOn_univ] using hf.locallyLipschitzOn.mul hg.locallyLipschitzOn

@[to_additive]

中文:
引理 LocallyLipschitz.mul
  条件: (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
  证明: by
  simpa [← locallyLipschitzOn_univ] using hf.locallyLipschitzOn.mul hg.locallyLipschitzOn

@[to_additive]

Depends on / 依赖: hf.locallyLipschitzOn.mul, hg.locallyLipschitzOn, locallyLipschitzOn, locallyLipschitzOn_univ
-/
lemma LocallyLipschitz.mul (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => f x * g x := by
  simpa [← locallyLipschitzOn_univ] using hf.locallyLipschitzOn.mul hg.locallyLipschitzOn

@[to_additive]
/--
lemma `LipschitzOnWith.div` / 引理 `LipschitzOnWith.div`

English:
lemma LipschitzOnWith.div
  given: (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
  proof: by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]

中文:
引理 LipschitzOnWith.div
  条件: (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
  证明: by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
lemma LipschitzOnWith.div (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf + Kg) (fun x => f x / g x) s := by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]
/--
theorem `LipschitzWith.div` / 定理 `LipschitzWith.div`

English:
theorem LipschitzWith.div
  given: (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
  proof: by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]

中文:
定理 LipschitzWith.div
  条件: (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
  证明: by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem LipschitzWith.div (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x => f x / g x := by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]
/--
lemma `LocallyLipschitzOn.div` / 引理 `LocallyLipschitzOn.div`

English:
lemma LocallyLipschitzOn.div
  given: (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g)
  proof: by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]

中文:
引理 LocallyLipschitzOn.div
  条件: (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g)
  证明: by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
lemma LocallyLipschitzOn.div (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s fun x => f x / g x := by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]
/--
lemma `LocallyLipschitz.div` / 引理 `LocallyLipschitz.div`

English:
lemma LocallyLipschitz.div
  given: (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
  proof: by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

中文:
引理 LocallyLipschitz.div
  条件: (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
  证明: by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
lemma LocallyLipschitz.div (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => f x / g x := by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

namespace AntilipschitzWith

@[to_additive]
/--
theorem `mul_lipschitzWith` / 定理 `mul_lipschitzWith`

English:
theorem mul_lipschitzWith
  given: (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹)
  proof: by
  let : PseudoMetricSpace α := PseudoEMetricSpace.toPseudoMetricSpace hf.edist_ne_top
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [NNReal.coe_inv]; rw [← _root_.div_eq_inv_mul]
  rw [le_div_iff₀ (NNReal.coe_pos.2 <| tsub_pos_iff_lt.2 hK)]
  rw [mul_comm]; rw [NNReal.coe_sub hK.le]; rw [sub_mul]
  calc
    ↑Kf⁻¹ * dist x y - Kg * dist x y <= dist (f x) (f y) - dist (g x) (g y) :=
      sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
    _ <= _ := le_trans (le_abs_self _) (abs_dist_sub_le_dist_mul_mul _ _ _ _)

@[to_additive]

中文:
定理 mul_lipschitzWith
  条件: (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹)
  证明: by
  let : PseudoMetricSpace α := PseudoEMetricSpace.toPseudoMetricSpace hf.edist_ne_top
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [NNReal.coe_inv]; rw [← _root_.div_eq_inv_mul]
  rw [le_div_iff₀ (NNReal.coe_pos.2 <| tsub_pos_iff_lt.2 hK)]
  rw [mul_comm]; rw [NNReal.coe_sub hK.le]; rw [sub_mul]
  calc
    ↑Kf⁻¹ * dist x y - Kg * dist x y <= dist (f x) (f y) - dist (g x) (g y) :=
      sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
    _ <= _ := le_trans (le_abs_self _) (abs_dist_sub_le_dist_mul_mul _ _ _ _)

@[to_additive]

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, NNReal, NNReal.coe_inv, NNReal.coe_pos, NNReal.coe_sub, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpace, PseudoMetricSpace, _root_, _root_.div_eq_inv_mul, abs_dist_sub_le_dist_mul_, coe_inv, coe_pos, coe_sub, dist_le_mul, div_eq_inv_mul, edist_ne_top, hK.le, hf.edist_ne_top
-/
theorem mul_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹) :
    AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ fun x => f x * g x := by
  let : PseudoMetricSpace α := PseudoEMetricSpace.toPseudoMetricSpace hf.edist_ne_top
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [NNReal.coe_inv]; rw [← _root_.div_eq_inv_mul]
  rw [le_div_iff₀ (NNReal.coe_pos.2 <| tsub_pos_iff_lt.2 hK)]
  rw [mul_comm]; rw [NNReal.coe_sub hK.le]; rw [sub_mul]
  calc
    ↑Kf⁻¹ * dist x y - Kg * dist x y <= dist (f x) (f y) - dist (g x) (g y) :=
      sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
    _ <= _ := le_trans (le_abs_self _) (abs_dist_sub_le_dist_mul_mul _ _ _ _)

@[to_additive]
/--
theorem `mul_div_lipschitzWith` / 定理 `mul_div_lipschitzWith`

English:
theorem mul_div_lipschitzWith
  statement: (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g / f))
  proof: by
  simpa only [Pi.div_apply, mul_div_cancel] using hf.mul_lipschitzWith hg hK

@[to_additive le_mul_norm_sub]

中文:
定理 mul_div_lipschitzWith
  结论: (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g / f))
  证明: by
  simpa only [Pi.div_apply, mul_div_cancel] using hf.mul_lipschitzWith hg hK

@[to_additive le_mul_norm_sub]

Depends on / 依赖: Pi.div_apply, div_apply, hf.mul_lipschitzWith, mul_div_cancel, mul_lipschitzWith
-/
theorem mul_div_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g / f))
    (hK : Kg < Kf⁻¹) : AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ g := by
  simpa only [Pi.div_apply, mul_div_cancel] using hf.mul_lipschitzWith hg hK

@[to_additive le_mul_norm_sub]
/--
theorem `le_mul_norm_div` / 定理 `le_mul_norm_div`

English:
theorem le_mul_norm_div
  given: {f : E -> F} (hf : AntilipschitzWith K f) (x y : E)
  proof: by simp [← dist_eq_norm_inv_mul, hf.le_mul_dist x y]

中文:
定理 le_mul_norm_div
  条件: {f : E -> F} (hf : AntilipschitzWith K f) (x y : E)
  证明: by simp [← dist_eq_norm_inv_mul, hf.le_mul_dist x y]

Depends on / 依赖: dist_eq_norm_inv_mul, hf.le_mul_dist, le_mul_dist
-/
theorem le_mul_norm_div {f : E -> F} (hf : AntilipschitzWith K f) (x y : E) :
    ‖x⁻¹ * y‖ <= K * ‖(f x)⁻¹ * f y‖ := by simp [← dist_eq_norm_inv_mul, hf.le_mul_dist x y]

end AntilipschitzWith
end PseudoEMetricSpace

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.to_lipschitzMul : LipschitzMul E :=
  ⟨⟨1 + 1, LipschitzWith.prod_fst.mul LipschitzWith.prod_snd⟩⟩

-- See note [lower instance priority]
/-- A seminormed group is a uniform group, i.e., multiplication and division are uniformly
continuous. -/
@[to_additive /-- A seminormed group is a uniform additive group, i.e., addition and subtraction are
uniformly continuous. -/]
instance (priority := 100) SeminormedCommGroup.to_isUniformGroup : IsUniformGroup E :=
  ⟨(LipschitzWith.prod_fst.div LipschitzWith.prod_snd).uniformContinuous⟩

-- short-circuit type class inference
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.toIsTopologicalGroup : IsTopologicalGroup E :=
  inferInstance

/-! ### SeparationQuotient -/

namespace SeparationQuotient

@[to_additive instNorm]
/--
Instance `instMulNorm` / 实例 `instMulNorm`

English:
instance instMulNorm
  signature: : Norm (SeparationQuotient E) where
  body: lift Norm.norm fun _ _ h => h.norm_eq_norm'

中文:
实例 instMulNorm
  签名: : 范数 (SeparationQuotient E) where
  定义体: lift Norm.norm fun _ _ h => h.norm_eq_norm'

Depends on / 依赖: Norm.norm, h.norm_eq_norm, norm_eq_norm
-/
instance instMulNorm : Norm (SeparationQuotient E) where
  norm := lift Norm.norm fun _ _ h => h.norm_eq_norm'

set_option linter.docPrime false in
@[to_additive (attr := simp) norm_mk]
/--
theorem `norm_mk'` / 定理 `norm_mk'`

English:
theorem norm_mk'
  given: (p : E)
  statement: ‖mk p‖ = ‖p‖
  proof: rfl

@[to_additive]

中文:
定理 norm_mk'
  条件: (p : E)
  结论: ‖mk p‖ = ‖p‖
  证明: rfl

@[to_additive]
-/
theorem norm_mk' (p : E) : ‖mk p‖ = ‖p‖ := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedCommGroup (SeparationQuotient E)
  body: instCommGroup
  dist_eq := Quotient.ind₂ dist_eq_norm_inv_mul

@[to_additive]

中文:
实例 :
  签名: NormedComm群 (SeparationQuotient E)
  定义体: instCommGroup
  dist_eq := Quotient.ind₂ dist_eq_norm_inv_mul

@[to_additive]

Depends on / 依赖: instCommGroup
-/
instance : NormedCommGroup (SeparationQuotient E) where
  __ : CommGroup (SeparationQuotient E) := instCommGroup
  dist_eq := Quotient.ind₂ dist_eq_norm_inv_mul

@[to_additive]
/--
theorem `mk_eq_one_iff` / 定理 `mk_eq_one_iff`

English:
theorem mk_eq_one_iff
  given: {p : E}
  statement: mk p = 1 ↔ ‖p‖ = 0
  proof: by
  rw [← norm_mk']; rw [norm_eq_zero']

中文:
定理 mk_eq_one_iff
  条件: {p : E}
  结论: mk p = 1 ↔ ‖p‖ = 0
  证明: by
  rw [← norm_mk']; rw [norm_eq_zero']

Depends on / 依赖: norm_eq_zero, norm_mk
-/
theorem mk_eq_one_iff {p : E} : mk p = 1 ↔ ‖p‖ = 0 := by
  rw [← norm_mk']; rw [norm_eq_zero']

set_option linter.docPrime false in
@[to_additive (attr := simp) nnnorm_mk]
/--
theorem `nnnorm_mk'` / 定理 `nnnorm_mk'`

English:
theorem nnnorm_mk'
  given: (p : E)
  statement: ‖mk p‖₊ = ‖p‖₊
  proof: rfl

中文:
定理 nnnorm_mk'
  条件: (p : E)
  结论: ‖mk p‖₊ = ‖p‖₊
  证明: rfl
-/
theorem nnnorm_mk' (p : E) : ‖mk p‖₊ = ‖p‖₊ := rfl

end SeparationQuotient

@[to_additive]
/--
theorem `cauchySeq_prod_of_eventually_eq` / 定理 `cauchySeq_prod_of_eventually_eq`

English:
theorem cauchySeq_prod_of_eventually_eq
  statement: {u v : Nat -> E} {N : Nat} (huv : forall n >= N, u n = v n)
  proof: by
  let d : Nat -> E := fun n => ∏ k in range (n + 1), u k / v k
  rw [show (fun n => ∏ k in range (n + 1)]; rw [u k) = d * fun n => ∏ k in range (n + 1)]; rw [v k
      by ext n; simp [d]]
  suffices forall n >= N, d n = d N from (tendsto_atTop_of_eventually_const this).cauchySeq.mul hv
  intro n hn
  dsimp [d]
  rw [eventually_constant_prod (N := N + 1) _ (by gcongr)]
  intro m hm
  simp [huv m (le_of_lt hm)]

@[to_additive CauchySeq.norm_bddAbove]

中文:
定理 cauchySeq_prod_of_eventually_eq
  结论: {u v : 自然数 -> E} {N : 自然数} (huv : 对任意 n >= N, u n = v n)
  证明: by
  let d : Nat -> E := fun n => ∏ k in range (n + 1), u k / v k
  rw [show (fun n => ∏ k in range (n + 1)]; rw [u k) = d * fun n => ∏ k in range (n + 1)]; rw [v k
      by ext n; simp [d]]
  suffices forall n >= N, d n = d N from (tendsto_atTop_of_eventually_const this).cauchySeq.mul hv
  intro n hn
  dsimp [d]
  rw [eventually_constant_prod (N := N + 1) _ (by gcongr)]
  intro m hm
  simp [huv m (le_of_lt hm)]

@[to_additive CauchySeq.norm_bddAbove]

Depends on / 依赖: cauchySeq, cauchySeq.mul, eventually_constant_prod, le_of_lt, tendsto_atTop_of_eventually_const
-/
theorem cauchySeq_prod_of_eventually_eq {u v : Nat -> E} {N : Nat} (huv : forall n >= N, u n = v n)
    (hv : CauchySeq fun n => ∏ k in range (n + 1), v k) :
    CauchySeq fun n => ∏ k in range (n + 1), u k := by
  let d : Nat -> E := fun n => ∏ k in range (n + 1), u k / v k
  rw [show (fun n => ∏ k in range (n + 1)]; rw [u k) = d * fun n => ∏ k in range (n + 1)]; rw [v k
      by ext n; simp [d]]
  suffices forall n >= N, d n = d N from (tendsto_atTop_of_eventually_const this).cauchySeq.mul hv
  intro n hn
  dsimp [d]
  rw [eventually_constant_prod (N := N + 1) _ (by gcongr)]
  intro m hm
  simp [huv m (le_of_lt hm)]

@[to_additive CauchySeq.norm_bddAbove]
/--
lemma `CauchySeq.mul_norm_bddAbove` / 引理 `CauchySeq.mul_norm_bddAbove`

English:
lemma CauchySeq.mul_norm_bddAbove
  statement: {G : Type*} [SeminormedGroup G] {u : Nat -> G}
  proof: by
  obtain ⟨C, -, hC⟩ := cauchySeq_bdd hu
  simp_rw [SeminormedGroup.dist_eq] at hC
  have : forall n, ‖u n‖ <= C + ‖u 0‖ := by
    intro n
    rw [add_comm]
    refine (norm_le_norm_add_norm_inv_mul (u n) (u 0)).trans ?_
    simp [(hC _ _).le]
  rw [bddAbove_def]
  exact ⟨C + ‖u 0‖, by simpa using this⟩

@[to_additive]

中文:
引理 CauchySeq.mul_norm_bddAbove
  结论: {G : 类型} [半赋范群 G] {u : 自然数 -> G}
  证明: by
  obtain ⟨C, -, hC⟩ := cauchySeq_bdd hu
  simp_rw [SeminormedGroup.dist_eq] at hC
  have : forall n, ‖u n‖ <= C + ‖u 0‖ := by
    intro n
    rw [add_comm]
    refine (norm_le_norm_add_norm_inv_mul (u n) (u 0)).trans ?_
    simp [(hC _ _).le]
  rw [bddAbove_def]
  exact ⟨C + ‖u 0‖, by simpa using this⟩

@[to_additive]

Depends on / 依赖: SeminormedGroup, SeminormedGroup.dist_eq, add_comm, bddAbove_def, cauchySeq_bdd, dist_eq, norm_le_norm_add_norm_inv_mul, simp_rw
-/
lemma CauchySeq.mul_norm_bddAbove {G : Type*} [SeminormedGroup G] {u : Nat -> G}
    (hu : CauchySeq u) : BddAbove (Set.range (fun n => ‖u n‖)) := by
  obtain ⟨C, -, hC⟩ := cauchySeq_bdd hu
  simp_rw [SeminormedGroup.dist_eq] at hC
  have : forall n, ‖u n‖ <= C + ‖u 0‖ := by
    intro n
    rw [add_comm]
    refine (norm_le_norm_add_norm_inv_mul (u n) (u 0)).trans ?_
    simp [(hC _ _).le]
  rw [bddAbove_def]
  exact ⟨C + ‖u 0‖, by simpa using this⟩

@[to_additive]
/--
theorem `lipschitzOnWith_iff_norm_div_le` / 定理 `lipschitzOnWith_iff_norm_div_le`

English:
theorem lipschitzOnWith_iff_norm_div_le
  given: {f : E -> F} {C : Real>=0} {s : Set E}
  proof: by
  simpa [← norm_inv_mul] using lipschitzOnWith_iff_norm_inv_mul_le

alias ⟨LipschitzOnWith.norm_div_le, _⟩ := lipschitzOnWith_iff_norm_div_le

中文:
定理 lipschitzOnWith_iff_norm_div_le
  条件: {f : E -> F} {C : 实数>=0} {s : 集合 E}
  证明: by
  simpa [← norm_inv_mul] using lipschitzOnWith_iff_norm_inv_mul_le

alias ⟨LipschitzOnWith.norm_div_le, _⟩ := lipschitzOnWith_iff_norm_div_le

Depends on / 依赖: lipschitzOnWith_iff_norm_inv_mul_le, norm_inv_mul
-/
theorem lipschitzOnWith_iff_norm_div_le {f : E -> F} {C : Real>=0} {s : Set E} :
    LipschitzOnWith C f s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> ‖f x / f y‖ <= C * ‖x / y‖ := by
  simpa [← norm_inv_mul] using lipschitzOnWith_iff_norm_inv_mul_le

alias ⟨LipschitzOnWith.norm_div_le, _⟩ := lipschitzOnWith_iff_norm_div_le

attribute [to_additive] LipschitzOnWith.norm_div_le

@[to_additive]
/--
theorem `LipschitzOnWith.norm_div_le_of_le` / 定理 `LipschitzOnWith.norm_div_le_of_le`

English:
theorem LipschitzOnWith.norm_div_le_of_le
  statement: {f : E -> F} {C : Real>=0} {s : Set E} {a b : E} {r : Real}
  proof: (h.norm_div_le ha hb).trans by gcongr

@[to_additive]

中文:
定理 LipschitzOnWith.norm_div_le_of_le
  结论: {f : E -> F} {C : 实数>=0} {s : 集合 E} {a b : E} {r : 实数}
  证明: (h.norm_div_le ha hb).trans by gcongr

@[to_additive]

Depends on / 依赖: h.norm_div_le, norm_div_le
-/
theorem LipschitzOnWith.norm_div_le_of_le {f : E -> F} {C : Real>=0} {s : Set E} {a b : E} {r : Real}
    (h : LipschitzOnWith C f s) (ha : a in s) (hb : b in s) (hr : ‖a / b‖ <= r) :
    ‖f a / f b‖ <= C * r :=
(h.norm_div_le ha hb).trans by gcongr

@[to_additive]
/--
theorem `lipschitzWith_iff_norm_div_le` / 定理 `lipschitzWith_iff_norm_div_le`

English:
theorem lipschitzWith_iff_norm_div_le
  given: {f : E -> F} {C : Real>=0}
  proof: by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_div]

alias ⟨LipschitzWith.norm_div_le, _⟩ := lipschitzWith_iff_norm_div_le

中文:
定理 lipschitzWith_iff_norm_div_le
  条件: {f : E -> F} {C : 实数>=0}
  证明: by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_div]

alias ⟨LipschitzWith.norm_div_le, _⟩ := lipschitzWith_iff_norm_div_le

Depends on / 依赖: dist_eq_norm_div, lipschitzWith_iff_dist_le_mul
-/
theorem lipschitzWith_iff_norm_div_le {f : E -> F} {C : Real>=0} :
    LipschitzWith C f ↔ forall x y, ‖f x / f y‖ <= C * ‖x / y‖ := by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_div]

alias ⟨LipschitzWith.norm_div_le, _⟩ := lipschitzWith_iff_norm_div_le

attribute [to_additive] LipschitzWith.norm_div_le

@[to_additive]
/--
theorem `LipschitzWith.norm_div_le_of_le` / 定理 `LipschitzWith.norm_div_le_of_le`

English:
theorem LipschitzWith.norm_div_le_of_le
  statement: {f : E -> F} {C : Real>=0} {a b : E} {r : Real}
  proof: (h.norm_div_le _ _).trans by gcongr

中文:
定理 LipschitzWith.norm_div_le_of_le
  结论: {f : E -> F} {C : 实数>=0} {a b : E} {r : 实数}
  证明: (h.norm_div_le _ _).trans by gcongr

Depends on / 依赖: h.norm_div_le, norm_div_le
-/
theorem LipschitzWith.norm_div_le_of_le {f : E -> F} {C : Real>=0} {a b : E} {r : Real}
    (h : LipschitzWith C f) (hr : ‖a / b‖ <= r) : ‖f a / f b‖ <= C * r :=
(h.norm_div_le _ _).trans by gcongr

end SeminormedCommGroup

namespace Real
open Topology

/--
theorem `isometry_intCast` / 定理 `isometry_intCast`

English:
theorem isometry_intCast
  statement: Isometry ((↑) : Int -> Real)
  proof: Isometry.of_dist_eq by tauto

中文:
定理 isometry_intCast
  结论: 等距 ((↑) : 整数 -> 实数)
  证明: Isometry.of_dist_eq by tauto

Depends on / 依赖: Isometry, Isometry.of_dist_eq, of_dist_eq
-/
theorem isometry_intCast : Isometry ((↑) : Int -> Real) :=
Isometry.of_dist_eq by tauto

/--
theorem `isClosedEmbedding_intCast` / 定理 `isClosedEmbedding_intCast`

English:
theorem isClosedEmbedding_intCast
  statement: IsClosedEmbedding ((↑) : Int -> Real)
  proof: isometry_intCast.isClosedEmbedding

中文:
定理 isClosedEmbedding_intCast
  结论: 是闭嵌入 ((↑) : 整数 -> 实数)
  证明: isometry_intCast.isClosedEmbedding

Depends on / 依赖: isClosedEmbedding, isometry_intCast, isometry_intCast.isClosedEmbedding
-/
theorem isClosedEmbedding_intCast : IsClosedEmbedding ((↑) : Int -> Real) :=
  isometry_intCast.isClosedEmbedding

/--
lemma `isClosed_range_intCast` / 引理 `isClosed_range_intCast`

English:
lemma isClosed_range_intCast
  statement: IsClosed (Set.range ((↑) : Int -> Real))
  proof: isClosedEmbedding_intCast.isClosed_range

中文:
引理 isClosed_range_intCast
  结论: 是闭集 (集合.range ((↑) : 整数 -> 实数))
  证明: isClosedEmbedding_intCast.isClosed_range

Depends on / 依赖: isClosedEmbedding_intCast, isClosedEmbedding_intCast.isClosed_range, isClosed_range
-/
lemma isClosed_range_intCast : IsClosed (Set.range ((↑) : Int -> Real)) :=
  isClosedEmbedding_intCast.isClosed_range

/--
lemma `isOpen_compl_range_intCast` / 引理 `isOpen_compl_range_intCast`

English:
lemma isOpen_compl_range_intCast
  statement: IsOpen (Set.range ((↑) : Int -> Real))ᶜ
  proof: Real.isClosed_range_intCast.isOpen_compl

中文:
引理 isOpen_compl_range_intCast
  结论: 是开集 (集合.range ((↑) : 整数 -> 实数))ᶜ
  证明: Real.isClosed_range_intCast.isOpen_compl

Depends on / 依赖: Real.isClosed_range_intCast.isOpen_compl, isClosed_range_intCast, isOpen_compl
-/
lemma isOpen_compl_range_intCast : IsOpen (Set.range ((↑) : Int -> Real))ᶜ :=
  Real.isClosed_range_intCast.isOpen_compl

end Real
