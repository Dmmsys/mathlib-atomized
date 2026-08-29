/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Topology.Instances.RealVectorSpace


/-!
# Torsors of normed space actions.

This file contains lemmas about normed additive torsors over normed spaces.
-/

@[expose] public section


noncomputable section

open NNReal Topology

open Filter

variable {V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

section NormedSpace

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]

open AffineMap

@[simp]
/--
theorem `dist_center_homothety` / 定理 `dist_center_homothety`

English:
theorem dist_center_homothety
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: by
  simp [homothety_def, norm_smul, ← dist_eq_norm_vsub, dist_comm]

@[simp]

中文:
定理 dist_center_homothety
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: by
  simp [homothety_def, norm_smul, ← dist_eq_norm_vsub, dist_comm]

@[simp]

Depends on / 依赖: dist_comm, dist_eq_norm_vsub, homothety_def, norm_smul
-/
theorem dist_center_homothety (p₁ p₂ : P) (c : 𝕜) :
    dist p₁ (homothety p₁ c p₂) = ‖c‖ * dist p₁ p₂ := by
  simp [homothety_def, norm_smul, ← dist_eq_norm_vsub, dist_comm]

@[simp]
/--
theorem `nndist_center_homothety` / 定理 `nndist_center_homothety`

English:
theorem nndist_center_homothety
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: NNReal.eq dist_center_homothety _ _ _

@[simp]

中文:
定理 nndist_center_homothety
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: NNReal.eq dist_center_homothety _ _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, dist_center_homothety
-/
theorem nndist_center_homothety (p₁ p₂ : P) (c : 𝕜) :
    nndist p₁ (homothety p₁ c p₂) = ‖c‖₊ * nndist p₁ p₂ :=
NNReal.eq dist_center_homothety _ _ _

@[simp]
/--
theorem `dist_homothety_center` / 定理 `dist_homothety_center`

English:
theorem dist_homothety_center
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: by rw [dist_comm, dist_center_homothety]

@[simp]

中文:
定理 dist_homothety_center
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: by rw [dist_comm, dist_center_homothety]

@[simp]

Depends on / 依赖: dist_center_homothety, dist_comm
-/
theorem dist_homothety_center (p₁ p₂ : P) (c : 𝕜) :
    dist (homothety p₁ c p₂) p₁ = ‖c‖ * dist p₁ p₂ := by rw [dist_comm, dist_center_homothety]

@[simp]
/--
theorem `nndist_homothety_center` / 定理 `nndist_homothety_center`

English:
theorem nndist_homothety_center
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: NNReal.eq dist_homothety_center _ _ _

中文:
定理 nndist_homothety_center
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: NNReal.eq dist_homothety_center _ _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_homothety_center
-/
theorem nndist_homothety_center (p₁ p₂ : P) (c : 𝕜) :
    nndist (homothety p₁ c p₂) p₁ = ‖c‖₊ * nndist p₁ p₂ :=
NNReal.eq dist_homothety_center _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `dist_lineMap_lineMap` / 定理 `dist_lineMap_lineMap`

English:
theorem dist_lineMap_lineMap
  given: (p₁ p₂ : P) (c₁ c₂ : 𝕜)
  proof: by
  rw [dist_comm p₁ p₂]
  simp only [lineMap_apply, dist_eq_norm_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul, norm_smul, vsub_eq_sub]

中文:
定理 dist_lineMap_lineMap
  条件: (p₁ p₂ : P) (c₁ c₂ : 𝕜)
  证明: by
  rw [dist_comm p₁ p₂]
  simp only [lineMap_apply, dist_eq_norm_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul, norm_smul, vsub_eq_sub]

Depends on / 依赖: dist_comm, dist_eq_norm_vsub, lineMap_apply, norm_smul, sub_smul, vadd_vsub_vadd_cancel_right, vsub_eq_sub
-/
theorem dist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) :
    dist (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂ := by
  rw [dist_comm p₁ p₂]
  simp only [lineMap_apply, dist_eq_norm_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul, norm_smul, vsub_eq_sub]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `nndist_lineMap_lineMap` / 定理 `nndist_lineMap_lineMap`

English:
theorem nndist_lineMap_lineMap
  given: (p₁ p₂ : P) (c₁ c₂ : 𝕜)
  proof: NNReal.eq dist_lineMap_lineMap _ _ _ _

中文:
定理 nndist_lineMap_lineMap
  条件: (p₁ p₂ : P) (c₁ c₂ : 𝕜)
  证明: NNReal.eq dist_lineMap_lineMap _ _ _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_lineMap_lineMap
-/
theorem nndist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) :
    nndist (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = nndist c₁ c₂ * nndist p₁ p₂ :=
NNReal.eq dist_lineMap_lineMap _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lipschitzWith_lineMap` / 定理 `lipschitzWith_lineMap`

English:
theorem lipschitzWith_lineMap
  given: (p₁ p₂ : P)
  statement: LipschitzWith (nndist p₁ p₂) (lineMap p₁ p₂ : 𝕜 -> P)
  proof: LipschitzWith.of_dist_le_mul fun c₁ c₂ =>
    ((dist_lineMap_lineMap p₁ p₂ c₁ c₂).trans (mul_comm _ _)).le

中文:
定理 lipschitzWith_lineMap
  条件: (p₁ p₂ : P)
  结论: LipschitzWith (nndist p₁ p₂) (lineMap p₁ p₂ : 𝕜 -> P)
  证明: LipschitzWith.of_dist_le_mul fun c₁ c₂ =>
    ((dist_lineMap_lineMap p₁ p₂ c₁ c₂).trans (mul_comm _ _)).le

Depends on / 依赖: LipschitzWith, LipschitzWith.of_dist_le_mul, dist_lineMap_lineMap, mul_comm, of_dist_le_mul
-/
theorem lipschitzWith_lineMap (p₁ p₂ : P) : LipschitzWith (nndist p₁ p₂) (lineMap p₁ p₂ : 𝕜 -> P) :=
  LipschitzWith.of_dist_le_mul fun c₁ c₂ =>
    ((dist_lineMap_lineMap p₁ p₂ c₁ c₂).trans (mul_comm _ _)).le

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `dist_lineMap_left` / 定理 `dist_lineMap_left`

English:
theorem dist_lineMap_left
  given: (p₁ p₂ : P) (c : 𝕜)
  statement: dist (lineMap p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂
  proof: by
  simpa only [lineMap_apply_zero, dist_zero_right] using dist_lineMap_lineMap p₁ p₂ c 0

中文:
定理 dist_lineMap_left
  条件: (p₁ p₂ : P) (c : 𝕜)
  结论: dist (lineMap p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂
  证明: by
  simpa only [lineMap_apply_zero, dist_zero_right] using dist_lineMap_lineMap p₁ p₂ c 0

Depends on / 依赖: dist_lineMap_lineMap, dist_zero_right, lineMap_apply_zero
-/
theorem dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂ := by
  simpa only [lineMap_apply_zero, dist_zero_right] using dist_lineMap_lineMap p₁ p₂ c 0

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `nndist_lineMap_left` / 定理 `nndist_lineMap_left`

English:
theorem nndist_lineMap_left
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: NNReal.eq dist_lineMap_left _ _ _

中文:
定理 nndist_lineMap_left
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: NNReal.eq dist_lineMap_left _ _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_lineMap_left
-/
theorem nndist_lineMap_left (p₁ p₂ : P) (c : 𝕜) :
    nndist (lineMap p₁ p₂ c) p₁ = ‖c‖₊ * nndist p₁ p₂ :=
NNReal.eq dist_lineMap_left _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `dist_left_lineMap` / 定理 `dist_left_lineMap`

English:
theorem dist_left_lineMap
  given: (p₁ p₂ : P) (c : 𝕜)
  statement: dist p₁ (lineMap p₁ p₂ c) = ‖c‖ * dist p₁ p₂
  proof: (dist_comm _ _).trans (dist_lineMap_left _ _ _)

中文:
定理 dist_left_lineMap
  条件: (p₁ p₂ : P) (c : 𝕜)
  结论: dist p₁ (lineMap p₁ p₂ c) = ‖c‖ * dist p₁ p₂
  证明: (dist_comm _ _).trans (dist_lineMap_left _ _ _)

Depends on / 依赖: dist_comm, dist_lineMap_left
-/
theorem dist_left_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₁ (lineMap p₁ p₂ c) = ‖c‖ * dist p₁ p₂ :=
  (dist_comm _ _).trans (dist_lineMap_left _ _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `nndist_left_lineMap` / 定理 `nndist_left_lineMap`

English:
theorem nndist_left_lineMap
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: NNReal.eq dist_left_lineMap _ _ _

中文:
定理 nndist_left_lineMap
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: NNReal.eq dist_left_lineMap _ _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_left_lineMap
-/
theorem nndist_left_lineMap (p₁ p₂ : P) (c : 𝕜) :
    nndist p₁ (lineMap p₁ p₂ c) = ‖c‖₊ * nndist p₁ p₂ :=
NNReal.eq dist_left_lineMap _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `dist_lineMap_right` / 定理 `dist_lineMap_right`

English:
theorem dist_lineMap_right
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: by
  simpa only [lineMap_apply_one, dist_eq_norm'] using dist_lineMap_lineMap p₁ p₂ c 1

中文:
定理 dist_lineMap_right
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: by
  simpa only [lineMap_apply_one, dist_eq_norm'] using dist_lineMap_lineMap p₁ p₂ c 1

Depends on / 依赖: dist_eq_norm, dist_lineMap_lineMap, lineMap_apply_one
-/
theorem dist_lineMap_right (p₁ p₂ : P) (c : 𝕜) :
    dist (lineMap p₁ p₂ c) p₂ = ‖1 - c‖ * dist p₁ p₂ := by
  simpa only [lineMap_apply_one, dist_eq_norm'] using dist_lineMap_lineMap p₁ p₂ c 1

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `nndist_lineMap_right` / 定理 `nndist_lineMap_right`

English:
theorem nndist_lineMap_right
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: NNReal.eq dist_lineMap_right _ _ _

中文:
定理 nndist_lineMap_right
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: NNReal.eq dist_lineMap_right _ _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_lineMap_right
-/
theorem nndist_lineMap_right (p₁ p₂ : P) (c : 𝕜) :
    nndist (lineMap p₁ p₂ c) p₂ = ‖1 - c‖₊ * nndist p₁ p₂ :=
NNReal.eq dist_lineMap_right _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `dist_right_lineMap` / 定理 `dist_right_lineMap`

English:
theorem dist_right_lineMap
  given: (p₁ p₂ : P) (c : 𝕜)
  statement: dist p₂ (lineMap p₁ p₂ c) = ‖1 - c‖ * dist p₁ p₂
  proof: (dist_comm _ _).trans (dist_lineMap_right _ _ _)

中文:
定理 dist_right_lineMap
  条件: (p₁ p₂ : P) (c : 𝕜)
  结论: dist p₂ (lineMap p₁ p₂ c) = ‖1 - c‖ * dist p₁ p₂
  证明: (dist_comm _ _).trans (dist_lineMap_right _ _ _)

Depends on / 依赖: dist_comm, dist_lineMap_right
-/
theorem dist_right_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₂ (lineMap p₁ p₂ c) = ‖1 - c‖ * dist p₁ p₂ :=
  (dist_comm _ _).trans (dist_lineMap_right _ _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `nndist_right_lineMap` / 定理 `nndist_right_lineMap`

English:
theorem nndist_right_lineMap
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: NNReal.eq dist_right_lineMap _ _ _

@[simp]

中文:
定理 nndist_right_lineMap
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: NNReal.eq dist_right_lineMap _ _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, dist_right_lineMap
-/
theorem nndist_right_lineMap (p₁ p₂ : P) (c : 𝕜) :
    nndist p₂ (lineMap p₁ p₂ c) = ‖1 - c‖₊ * nndist p₁ p₂ :=
NNReal.eq dist_right_lineMap _ _ _

@[simp]
/--
theorem `dist_homothety_self` / 定理 `dist_homothety_self`

English:
theorem dist_homothety_self
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: by
  rw [homothety_eq_lineMap]; rw [dist_lineMap_right]

@[simp]

中文:
定理 dist_homothety_self
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: by
  rw [homothety_eq_lineMap]; rw [dist_lineMap_right]

@[simp]

Depends on / 依赖: dist_lineMap_right, homothety_eq_lineMap
-/
theorem dist_homothety_self (p₁ p₂ : P) (c : 𝕜) :
    dist (homothety p₁ c p₂) p₂ = ‖1 - c‖ * dist p₁ p₂ := by
  rw [homothety_eq_lineMap]; rw [dist_lineMap_right]

@[simp]
/--
theorem `nndist_homothety_self` / 定理 `nndist_homothety_self`

English:
theorem nndist_homothety_self
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: NNReal.eq dist_homothety_self _ _ _

@[simp]

中文:
定理 nndist_homothety_self
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: NNReal.eq dist_homothety_self _ _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, dist_homothety_self
-/
theorem nndist_homothety_self (p₁ p₂ : P) (c : 𝕜) :
    nndist (homothety p₁ c p₂) p₂ = ‖1 - c‖₊ * nndist p₁ p₂ :=
NNReal.eq dist_homothety_self _ _ _

@[simp]
/--
theorem `dist_self_homothety` / 定理 `dist_self_homothety`

English:
theorem dist_self_homothety
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: by rw [dist_comm, dist_homothety_self]

@[simp]

中文:
定理 dist_self_homothety
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: by rw [dist_comm, dist_homothety_self]

@[simp]

Depends on / 依赖: dist_comm, dist_homothety_self
-/
theorem dist_self_homothety (p₁ p₂ : P) (c : 𝕜) :
    dist p₂ (homothety p₁ c p₂) = ‖1 - c‖ * dist p₁ p₂ := by rw [dist_comm, dist_homothety_self]

@[simp]
/--
theorem `nndist_self_homothety` / 定理 `nndist_self_homothety`

English:
theorem nndist_self_homothety
  given: (p₁ p₂ : P) (c : 𝕜)
  proof: NNReal.eq dist_self_homothety _ _ _

中文:
定理 nndist_self_homothety
  条件: (p₁ p₂ : P) (c : 𝕜)
  证明: NNReal.eq dist_self_homothety _ _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_self_homothety
-/
theorem nndist_self_homothety (p₁ p₂ : P) (c : 𝕜) :
    nndist p₂ (homothety p₁ c p₂) = ‖1 - c‖₊ * nndist p₁ p₂ :=
NNReal.eq dist_self_homothety _ _ _

section invertibleTwo

variable [Invertible (2 : 𝕜)]

@[simp]
/--
theorem `dist_left_midpoint` / 定理 `dist_left_midpoint`

English:
theorem dist_left_midpoint
  given: (p₁ p₂ : P)
  statement: dist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
  proof: by
  rw [midpoint]; rw [dist_comm]; rw [dist_lineMap_left]; rw [invOf_eq_inv]; rw [← norm_inv]

@[simp]

中文:
定理 dist_left_midpoint
  条件: (p₁ p₂ : P)
  结论: dist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
  证明: by
  rw [midpoint]; rw [dist_comm]; rw [dist_lineMap_left]; rw [invOf_eq_inv]; rw [← norm_inv]

@[simp]

Depends on / 依赖: dist_comm, dist_lineMap_left, invOf_eq_inv, midpoint, norm_inv
-/
theorem dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [midpoint]; rw [dist_comm]; rw [dist_lineMap_left]; rw [invOf_eq_inv]; rw [← norm_inv]

@[simp]
/--
theorem `nndist_left_midpoint` / 定理 `nndist_left_midpoint`

English:
theorem nndist_left_midpoint
  given: (p₁ p₂ : P)
  proof: NNReal.eq dist_left_midpoint _ _

@[simp]

中文:
定理 nndist_left_midpoint
  条件: (p₁ p₂ : P)
  证明: NNReal.eq dist_left_midpoint _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, dist_left_midpoint
-/
theorem nndist_left_midpoint (p₁ p₂ : P) :
    nndist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
NNReal.eq dist_left_midpoint _ _

@[simp]
/--
theorem `dist_midpoint_left` / 定理 `dist_midpoint_left`

English:
theorem dist_midpoint_left
  given: (p₁ p₂ : P)
  statement: dist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
  proof: by
  rw [dist_comm]; rw [dist_left_midpoint]

@[simp]

中文:
定理 dist_midpoint_left
  条件: (p₁ p₂ : P)
  结论: dist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
  证明: by
  rw [dist_comm]; rw [dist_left_midpoint]

@[simp]

Depends on / 依赖: dist_comm, dist_left_midpoint
-/
theorem dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [dist_comm]; rw [dist_left_midpoint]

@[simp]
/--
theorem `nndist_midpoint_left` / 定理 `nndist_midpoint_left`

English:
theorem nndist_midpoint_left
  given: (p₁ p₂ : P)
  proof: NNReal.eq dist_midpoint_left _ _

@[simp]

中文:
定理 nndist_midpoint_left
  条件: (p₁ p₂ : P)
  证明: NNReal.eq dist_midpoint_left _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, dist_midpoint_left
-/
theorem nndist_midpoint_left (p₁ p₂ : P) :
    nndist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
NNReal.eq dist_midpoint_left _ _

@[simp]
/--
theorem `dist_midpoint_right` / 定理 `dist_midpoint_right`

English:
theorem dist_midpoint_right
  given: (p₁ p₂ : P)
  proof: by
  rw [midpoint_comm]; rw [dist_midpoint_left]; rw [dist_comm]

@[simp]

中文:
定理 dist_midpoint_right
  条件: (p₁ p₂ : P)
  证明: by
  rw [midpoint_comm]; rw [dist_midpoint_left]; rw [dist_comm]

@[simp]

Depends on / 依赖: dist_comm, dist_midpoint_left, midpoint_comm
-/
theorem dist_midpoint_right (p₁ p₂ : P) :
    dist (midpoint 𝕜 p₁ p₂) p₂ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [midpoint_comm]; rw [dist_midpoint_left]; rw [dist_comm]

@[simp]
/--
theorem `nndist_midpoint_right` / 定理 `nndist_midpoint_right`

English:
theorem nndist_midpoint_right
  given: (p₁ p₂ : P)
  proof: NNReal.eq dist_midpoint_right _ _

@[simp]

中文:
定理 nndist_midpoint_right
  条件: (p₁ p₂ : P)
  证明: NNReal.eq dist_midpoint_right _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, dist_midpoint_right
-/
theorem nndist_midpoint_right (p₁ p₂ : P) :
    nndist (midpoint 𝕜 p₁ p₂) p₂ = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
NNReal.eq dist_midpoint_right _ _

@[simp]
/--
theorem `dist_right_midpoint` / 定理 `dist_right_midpoint`

English:
theorem dist_right_midpoint
  given: (p₁ p₂ : P)
  proof: by
  rw [dist_comm]; rw [dist_midpoint_right]

@[simp]

中文:
定理 dist_right_midpoint
  条件: (p₁ p₂ : P)
  证明: by
  rw [dist_comm]; rw [dist_midpoint_right]

@[simp]

Depends on / 依赖: dist_comm, dist_midpoint_right
-/
theorem dist_right_midpoint (p₁ p₂ : P) :
    dist p₂ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [dist_comm]; rw [dist_midpoint_right]

@[simp]
/--
theorem `nndist_right_midpoint` / 定理 `nndist_right_midpoint`

English:
theorem nndist_right_midpoint
  given: (p₁ p₂ : P)
  proof: NNReal.eq dist_right_midpoint _ _

中文:
定理 nndist_right_midpoint
  条件: (p₁ p₂ : P)
  证明: NNReal.eq dist_right_midpoint _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_right_midpoint
-/
theorem nndist_right_midpoint (p₁ p₂ : P) :
    nndist p₂ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
NNReal.eq dist_right_midpoint _ _

/--
theorem `dist_left_midpoint_eq_dist_right_midpoint` / 定理 `dist_left_midpoint_eq_dist_right_midpoint`

English:
theorem dist_left_midpoint_eq_dist_right_midpoint
  given: (p₁ p₂ : P)
  proof: by
  rw [dist_left_midpoint p₁ p₂]; rw [dist_right_midpoint p₁ p₂]

中文:
定理 dist_left_midpoint_eq_dist_right_midpoint
  条件: (p₁ p₂ : P)
  证明: by
  rw [dist_left_midpoint p₁ p₂]; rw [dist_right_midpoint p₁ p₂]

Depends on / 依赖: dist_left_midpoint, dist_right_midpoint
-/
theorem dist_left_midpoint_eq_dist_right_midpoint (p₁ p₂ : P) :
    dist p₁ (midpoint 𝕜 p₁ p₂) = dist p₂ (midpoint 𝕜 p₁ p₂) := by
  rw [dist_left_midpoint p₁ p₂]; rw [dist_right_midpoint p₁ p₂]

/--
theorem `dist_midpoint_midpoint_le'` / 定理 `dist_midpoint_midpoint_le'`

English:
theorem dist_midpoint_midpoint_le'
  given: (p₁ p₂ p₃ p₄ : P)
  proof: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [midpoint_vsub_midpoint]
  rw [midpoint_eq_smul_add]; rw [norm_smul]; rw [invOf_eq_inv]; rw [norm_inv]; rw [← div_eq_inv_mul]
  grw [norm_add_le]

中文:
定理 dist_midpoint_midpoint_le'
  条件: (p₁ p₂ p₃ p₄ : P)
  证明: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [midpoint_vsub_midpoint]
  rw [midpoint_eq_smul_add]; rw [norm_smul]; rw [invOf_eq_inv]; rw [norm_inv]; rw [← div_eq_inv_mul]
  grw [norm_add_le]

Depends on / 依赖: dist_eq_norm_vsub, div_eq_inv_mul, invOf_eq_inv, midpoint_eq_smul_add, midpoint_vsub_midpoint, norm_add_le, norm_inv, norm_smul
-/
theorem dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
    dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) <= (dist p₁ p₃ + dist p₂ p₄) / ‖(2 : 𝕜)‖ := by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [midpoint_vsub_midpoint]
  rw [midpoint_eq_smul_add]; rw [norm_smul]; rw [invOf_eq_inv]; rw [norm_inv]; rw [← div_eq_inv_mul]
  grw [norm_add_le]

/--
theorem `nndist_midpoint_midpoint_le'` / 定理 `nndist_midpoint_midpoint_le'`

English:
theorem nndist_midpoint_midpoint_le'
  given: (p₁ p₂ p₃ p₄ : P)
  proof: dist_midpoint_midpoint_le' _ _ _ _

中文:
定理 nndist_midpoint_midpoint_le'
  条件: (p₁ p₂ p₃ p₄ : P)
  证明: dist_midpoint_midpoint_le' _ _ _ _

Depends on / 依赖: dist_midpoint_midpoint_le
-/
theorem nndist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
    nndist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) <= (nndist p₁ p₃ + nndist p₂ p₄) / ‖(2 : 𝕜)‖₊ :=
  dist_midpoint_midpoint_le' _ _ _ _

end invertibleTwo

/--
theorem `dist_pointReflection_left` / 定理 `dist_pointReflection_left`

English:
theorem dist_pointReflection_left
  given: (p q : P)
  proof: by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_left (G := V)]

中文:
定理 dist_pointReflection_left
  条件: (p q : P)
  证明: by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_left (G := V)]
-/
@[simp] theorem dist_pointReflection_left (p q : P) :
    dist (Equiv.pointReflection p q) p = dist p q := by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_left (G := V)]

/--
theorem `dist_left_pointReflection` / 定理 `dist_left_pointReflection`

English:
theorem dist_left_pointReflection
  given: (p q : P)
  proof: (dist_comm _ _).trans (dist_pointReflection_left _ _)

中文:
定理 dist_left_pointReflection
  条件: (p q : P)
  证明: (dist_comm _ _).trans (dist_pointReflection_left _ _)
-/
@[simp] theorem dist_left_pointReflection (p q : P) :
    dist p (Equiv.pointReflection p q) = dist p q :=
  (dist_comm _ _).trans (dist_pointReflection_left _ _)

variable (𝕜) in
/--
theorem `dist_pointReflection_right` / 定理 `dist_pointReflection_right`

English:
theorem dist_pointReflection_right
  given: (p q : P)
  proof: by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_right (G := V), ← Nat.cast_smul_eq_nsmul 𝕜,
    norm_smul]

中文:
定理 dist_pointReflection_right
  条件: (p q : P)
  证明: by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_right (G := V), ← Nat.cast_smul_eq_nsmul 𝕜,
    norm_smul]

Depends on / 依赖: Equiv.pointReflection_vsub_right, Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, dist_eq_norm_vsub, norm_smul, pointReflection_vsub_right
-/
theorem dist_pointReflection_right (p q : P) :
    dist (Equiv.pointReflection p q) q = ‖(2 : 𝕜)‖ * dist p q := by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_right (G := V), ← Nat.cast_smul_eq_nsmul 𝕜,
    norm_smul]

variable (𝕜) in
/--
theorem `dist_right_pointReflection` / 定理 `dist_right_pointReflection`

English:
theorem dist_right_pointReflection
  given: (p q : P)
  proof: (dist_comm _ _).trans (dist_pointReflection_right 𝕜 _ _)

中文:
定理 dist_right_pointReflection
  条件: (p q : P)
  证明: (dist_comm _ _).trans (dist_pointReflection_right 𝕜 _ _)

Depends on / 依赖: dist_comm, dist_pointReflection_right
-/
theorem dist_right_pointReflection (p q : P) :
    dist q (Equiv.pointReflection p q) = ‖(2 : 𝕜)‖ * dist p q :=
  (dist_comm _ _).trans (dist_pointReflection_right 𝕜 _ _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `antilipschitzWith_lineMap` / 定理 `antilipschitzWith_lineMap`

English:
theorem antilipschitzWith_lineMap
  given: {p₁ p₂ : Q} (h : p₁ != p₂)
  proof: AntilipschitzWith.of_le_mul_dist fun c₁ c₂ => by
    rw [dist_lineMap_lineMap]; rw [NNReal.coe_inv]; rw [← dist_nndist]; rw [mul_left_comm]; rw [inv_mul_cancel₀ (dist_ne_zero.2 h)]; rw [mul_one]

中文:
定理 antilipschitzWith_lineMap
  条件: {p₁ p₂ : Q} (h : p₁ != p₂)
  证明: AntilipschitzWith.of_le_mul_dist fun c₁ c₂ => by
    rw [dist_lineMap_lineMap]; rw [NNReal.coe_inv]; rw [← dist_nndist]; rw [mul_left_comm]; rw [inv_mul_cancel₀ (dist_ne_zero.2 h)]; rw [mul_one]

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, NNReal, NNReal.coe_inv, coe_inv, dist_lineMap_lineMap, dist_ne_zero, dist_nndist, mul_left_comm, mul_one, of_le_mul_dist
-/
theorem antilipschitzWith_lineMap {p₁ p₂ : Q} (h : p₁ != p₂) :
    AntilipschitzWith (nndist p₁ p₂)⁻¹ (lineMap p₁ p₂ : 𝕜 -> Q) :=
  AntilipschitzWith.of_le_mul_dist fun c₁ c₂ => by
    rw [dist_lineMap_lineMap]; rw [NNReal.coe_inv]; rw [← dist_nndist]; rw [mul_left_comm]; rw [inv_mul_cancel₀ (dist_ne_zero.2 h)]; rw [mul_one]

end NormedSpace

variable [NormedSpace Real V] [NormedSpace Real W]

/--
theorem `dist_midpoint_midpoint_le` / 定理 `dist_midpoint_midpoint_le`

English:
theorem dist_midpoint_midpoint_le
  given: (p₁ p₂ p₃ p₄ : V)
  proof: by
  simpa using dist_midpoint_midpoint_le' (𝕜 := Real) p₁ p₂ p₃ p₄

中文:
定理 dist_midpoint_midpoint_le
  条件: (p₁ p₂ p₃ p₄ : V)
  证明: by
  simpa using dist_midpoint_midpoint_le' (𝕜 := Real) p₁ p₂ p₃ p₄

Depends on / 依赖: dist_midpoint_midpoint_le
-/
theorem dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
    dist (midpoint Real p₁ p₂) (midpoint Real p₃ p₄) <= (dist p₁ p₃ + dist p₂ p₄) / 2 := by
  simpa using dist_midpoint_midpoint_le' (𝕜 := Real) p₁ p₂ p₃ p₄

/--
theorem `nndist_midpoint_midpoint_le` / 定理 `nndist_midpoint_midpoint_le`

English:
theorem nndist_midpoint_midpoint_le
  given: (p₁ p₂ p₃ p₄ : V)
  proof: dist_midpoint_midpoint_le _ _ _ _

中文:
定理 nndist_midpoint_midpoint_le
  条件: (p₁ p₂ p₃ p₄ : V)
  证明: dist_midpoint_midpoint_le _ _ _ _

Depends on / 依赖: dist_midpoint_midpoint_le
-/
theorem nndist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
    nndist (midpoint Real p₁ p₂) (midpoint Real p₃ p₄) <= (nndist p₁ p₃ + nndist p₂ p₄) / 2 :=
  dist_midpoint_midpoint_le _ _ _ _

/--
Definition of `AffineMap.ofMapMidpoint` / `AffineMap.ofMapMidpoint` 的定义

English:
definition AffineMap.ofMapMidpoint
  signature: (f : P -> Q) (h : forall x y, f (midpoint Real x y) = midpoint Real (f x) (f y))
  body: let c := Classical.arbitrary P
  AffineMap.mk' f (↑((AddMonoidHom.ofMapMidpoint Real Real
    ((AffineEquiv.vaddConst Real (f <| c)).symm ∘ f ∘ AffineEquiv.vaddConst Real c) (by simp)
    fun x y => by simp [h]).toRealLinearMap <| by
        apply_rules [Continuous.vadd, Continuous.vsub, continuous_

中文:
定义 AffineMap.ofMapMidpoint
  签名: (f : P -> Q) (h : 对任意 x y, f (midpoint 实数 x y) = midpoint 实数 (f x) (f y))
  定义体: let c := Classical.arbitrary P
  AffineMap.mk' f (↑((AddMonoidHom.ofMapMidpoint Real Real
    ((AffineEquiv.vaddConst Real (f <| c)).symm ∘ f ∘ AffineEquiv.vaddConst Real c) (by simp)
    fun x y => by simp [h]).toRealLinearMap <| by
        apply_rules [Continuous.vadd, Continuous.vsub, continuous_

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ofMapMidpoint, AffineEquiv, AffineEquiv.vaddConst, AffineMap, AffineMap.mk, Classical, Classical.arbitrary, Continuous, Continuous.vadd, Continuous.vsub, apply_rules, arbitrary, continuous_const, continuous_id, hfc.comp, ofMapMidpoint, toRealLinearMap, vaddConst
-/
def AffineMap.ofMapMidpoint (f : P -> Q) (h : forall x y, f (midpoint Real x y) = midpoint Real (f x) (f y))
    (hfc : Continuous f) : P ->ᵃ[Real] Q :=
  let c := Classical.arbitrary P
  AffineMap.mk' f (↑((AddMonoidHom.ofMapMidpoint Real Real
    ((AffineEquiv.vaddConst Real (f <| c)).symm ∘ f ∘ AffineEquiv.vaddConst Real c) (by simp)
    fun x y => by simp [h]).toRealLinearMap <| by
        apply_rules [Continuous.vadd, Continuous.vsub, continuous_const, hfc.comp, continuous_id]))
    c fun p => by simp

end

section

open Dilation

variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]
variable [Module 𝕜 E] [NormSMulClass 𝕜 E] {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]

-- TODO: reimplement this as a `ContinuousAffineEquiv`.
/-- Scaling by an element `k` of the scalar ring as a `DilationEquiv` with ratio `‖k‖₊`, mapping
from a normed space to a normed torsor over that space sending `0` to `c`. -/
@[simps]
/--
Definition of `DilationEquiv.smulTorsor` / `DilationEquiv.smulTorsor` 的定义

English:
definition DilationEquiv.smulTorsor
  signature: (c : P) {k : 𝕜} (hk : k != 0)
  body: (k • · +ᵥ c)
  invFun := k⁻¹ • (· -ᵥ c)
  left_inv x := by simp [inv_smul_smul₀ hk]
  right_inv p := by simp [smul_inv_smul₀ hk]
  edist_eq' := ⟨‖k‖₊, nnnorm_ne_zero_iff.mpr hk, fun x y => by
    rw [show edist (k • x +ᵥ c) (k • y +ᵥ c) = _ from (IsometryEquiv.vaddConst c).isometry ..]
    exact edi

中文:
定义 DilationEquiv.smulTorsor
  签名: (c : P) {k : 𝕜} (hk : k != 0)
  定义体: (k • · +ᵥ c)
  invFun := k⁻¹ • (· -ᵥ c)
  left_inv x := by simp [inv_smul_smul₀ hk]
  right_inv p := by simp [smul_inv_smul₀ hk]
  edist_eq' := ⟨‖k‖₊, nnnorm_ne_zero_iff.mpr hk, fun x y => by
    rw [show edist (k • x +ᵥ c) (k • y +ᵥ c) = _ from (IsometryEquiv.vaddConst c).isometry ..]
    exact edi
-/
def DilationEquiv.smulTorsor (c : P) {k : 𝕜} (hk : k != 0) : E ≃ᵈ P where
  toFun := (k • · +ᵥ c)
  invFun := k⁻¹ • (· -ᵥ c)
  left_inv x := by simp [inv_smul_smul₀ hk]
  right_inv p := by simp [smul_inv_smul₀ hk]
  edist_eq' := ⟨‖k‖₊, nnnorm_ne_zero_iff.mpr hk, fun x y => by
    rw [show edist (k • x +ᵥ c) (k • y +ᵥ c) = _ from (IsometryEquiv.vaddConst c).isometry ..]
    exact edist_smul₀ ..⟩

-- Cannot be @[simp] because `x` and `y` cannot be inferred by `simp`.
/--
lemma `DilationEquiv.smulTorsor_ratio` / 引理 `DilationEquiv.smulTorsor_ratio`

English:
lemma DilationEquiv.smulTorsor_ratio
  statement: {c : P} {k : 𝕜} (hk : k != 0) {x y : E}
  proof: Eq.symm ratio_unique_of_dist_ne_zero h by simp [dist_eq_norm, ← smul_sub, norm_smul]

@[simp]

中文:
引理 DilationEquiv.smulTorsor_ratio
  结论: {c : P} {k : 𝕜} (hk : k != 0) {x y : E}
  证明: Eq.symm ratio_unique_of_dist_ne_zero h by simp [dist_eq_norm, ← smul_sub, norm_smul]

@[simp]

Depends on / 依赖: Eq.symm, dist_eq_norm, norm_smul, ratio_unique_of_dist_ne_zero, smul_sub
-/
lemma DilationEquiv.smulTorsor_ratio {c : P} {k : 𝕜} (hk : k != 0) {x y : E}
    (h : dist x y != 0) : ratio (smulTorsor c hk) = ‖k‖₊ :=
Eq.symm ratio_unique_of_dist_ne_zero h by simp [dist_eq_norm, ← smul_sub, norm_smul]

@[simp]
/--
lemma `DilationEquiv.smulTorsor_preimage_ball` / 引理 `DilationEquiv.smulTorsor_preimage_ball`

English:
lemma DilationEquiv.smulTorsor_preimage_ball
  given: {c : P} {k : 𝕜} (hk : k != 0)
  proof: by
  aesop (add simp norm_smul)

中文:
引理 DilationEquiv.smulTorsor_preimage_ball
  条件: {c : P} {k : 𝕜} (hk : k != 0)
  证明: by
  aesop (add simp norm_smul)

Depends on / 依赖: norm_smul
-/
lemma DilationEquiv.smulTorsor_preimage_ball {c : P} {k : 𝕜} (hk : k != 0) :
    smulTorsor c hk ⁻¹' (Metric.ball c ‖k‖) = Metric.ball (0 : E) 1 := by
  aesop (add simp norm_smul)

end
