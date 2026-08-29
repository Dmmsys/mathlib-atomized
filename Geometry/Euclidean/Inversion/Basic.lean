/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Tactic.AdaptationNote

/-!
# Inversion in an affine space

In this file we define inversion in a sphere in an affine space. This map sends each point `x` to
the point `y` such that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center
and the radius of the sphere.

In many applications, it is convenient to assume that the inversion swaps the center and the point
at infinity. In order to stay in the original affine space, we define the map so that it sends
center to itself.

Currently, we prove only a few basic lemmas needed to prove Ptolemy's inequality, see
`EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`.
-/

@[expose] public section

noncomputable section

open Metric Function AffineMap Set AffineSubspace
open scoped Topology

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace EuclideanGeometry

variable {c x y : P} {R : Real}

/--
Definition of `inversion` / `inversion` 的定义

English:
definition inversion
  signature: (c : P) (R : Real) (x : P)
  body: (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c

中文:
定义 inversion
  签名: (c : P) (R : 实数) (x : P)
  定义体: (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c
-/
def inversion (c : P) (R : Real) (x : P) : P :=
  (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c

/--
theorem `inversion_def` / 定理 `inversion_def`

English:
theorem inversion_def
  proof: rfl

中文:
定理 inversion_def
  证明: rfl
-/
theorem inversion_def :
    inversion = fun (c : P) (R : Real) (x : P) => (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c :=
  rfl

/-!
### Basic properties

In this section we prove that `EuclideanGeometry.inversion c R` is involutive and preserves the
sphere `Metric.sphere c R`. We also prove that the distance to the center of the image of `x` under
this inversion is given by `R ^ 2 / dist x c`.
-/

set_option backward.isDefEq.respectTransparency false in
/--
theorem `inversion_eq_lineMap` / 定理 `inversion_eq_lineMap`

English:
theorem inversion_eq_lineMap
  given: (c : P) (R : Real) (x : P)
  proof: rfl

中文:
定理 inversion_eq_lineMap
  条件: (c : P) (R : 实数) (x : P)
  证明: rfl
-/
theorem inversion_eq_lineMap (c : P) (R : Real) (x : P) :
    inversion c R x = lineMap c x ((R / dist x c) ^ 2) :=
  rfl

/--
theorem `inversion_vsub_center` / 定理 `inversion_vsub_center`

English:
theorem inversion_vsub_center
  given: (c : P) (R : Real) (x : P)
  proof: vadd_vsub _ _

@[simp]

中文:
定理 inversion_vsub_center
  条件: (c : P) (R : 实数) (x : P)
  证明: vadd_vsub _ _

@[simp]

Depends on / 依赖: vadd_vsub
-/
theorem inversion_vsub_center (c : P) (R : Real) (x : P) :
    inversion c R x -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c) :=
  vadd_vsub _ _

@[simp]
/--
theorem `inversion_self` / 定理 `inversion_self`

English:
theorem inversion_self
  given: (c : P) (R : Real)
  statement: inversion c R c = c
  proof: by simp [inversion]

@[simp]

中文:
定理 inversion_self
  条件: (c : P) (R : 实数)
  结论: inversion c R c = c
  证明: by simp [inversion]

@[simp]

Depends on / 依赖: inversion
-/
theorem inversion_self (c : P) (R : Real) : inversion c R c = c := by simp [inversion]

@[simp]
/--
theorem `inversion_zero_radius` / 定理 `inversion_zero_radius`

English:
theorem inversion_zero_radius
  given: (c x : P)
  statement: inversion c 0 x = c
  proof: by simp [inversion]

中文:
定理 inversion_zero_radius
  条件: (c x : P)
  结论: inversion c 0 x = c
  证明: by simp [inversion]

Depends on / 依赖: inversion
-/
theorem inversion_zero_radius (c x : P) : inversion c 0 x = c := by simp [inversion]

/--
theorem `inversion_mul` / 定理 `inversion_mul`

English:
theorem inversion_mul
  given: (c : P) (a R : Real) (x : P)
  proof: by
  simp only [inversion_eq_lineMap, ← homothety_eq_lineMap, ← homothety_mul_apply, mul_div_assoc,
    mul_pow]

@[simp]

中文:
定理 inversion_mul
  条件: (c : P) (a R : 实数) (x : P)
  证明: by
  simp only [inversion_eq_lineMap, ← homothety_eq_lineMap, ← homothety_mul_apply, mul_div_assoc,
    mul_pow]

@[simp]

Depends on / 依赖: homothety_eq_lineMap, homothety_mul_apply, inversion_eq_lineMap, mul_div_assoc, mul_pow
-/
theorem inversion_mul (c : P) (a R : Real) (x : P) :
    inversion c (a * R) x = homothety c (a ^ 2) (inversion c R x) := by
  simp only [inversion_eq_lineMap, ← homothety_eq_lineMap, ← homothety_mul_apply, mul_div_assoc,
    mul_pow]

@[simp]
/--
theorem `inversion_dist_center` / 定理 `inversion_dist_center`

English:
theorem inversion_dist_center
  given: (c x : P)
  statement: inversion c (dist x c) x = x
  proof: by
  rcases eq_or_ne x c with (rfl | hne)
  · apply inversion_self
  · rw [inversion, div_self, one_pow, one_smul, vsub_vadd]
    rwa [dist_ne_zero]

@[simp]

中文:
定理 inversion_dist_center
  条件: (c x : P)
  结论: inversion c (dist x c) x = x
  证明: by
  rcases eq_or_ne x c with (rfl | hne)
  · apply inversion_self
  · rw [inversion, div_self, one_pow, one_smul, vsub_vadd]
    rwa [dist_ne_zero]

@[simp]

Depends on / 依赖: dist_ne_zero, div_self, eq_or_ne, inversion, inversion_self, one_pow, one_smul, vsub_vadd
-/
theorem inversion_dist_center (c x : P) : inversion c (dist x c) x = x := by
  rcases eq_or_ne x c with (rfl | hne)
  · apply inversion_self
  · rw [inversion, div_self, one_pow, one_smul, vsub_vadd]
    rwa [dist_ne_zero]

@[simp]
/--
theorem `inversion_dist_center'` / 定理 `inversion_dist_center'`

English:
theorem inversion_dist_center'
  given: (c x : P)
  statement: inversion c (dist c x) x = x
  proof: by
  rw [dist_comm]; rw [inversion_dist_center]

中文:
定理 inversion_dist_center'
  条件: (c x : P)
  结论: inversion c (dist c x) x = x
  证明: by
  rw [dist_comm]; rw [inversion_dist_center]

Depends on / 依赖: dist_comm, inversion_dist_center
-/
theorem inversion_dist_center' (c x : P) : inversion c (dist c x) x = x := by
  rw [dist_comm]; rw [inversion_dist_center]

/--
theorem `inversion_of_mem_sphere` / 定理 `inversion_of_mem_sphere`

English:
theorem inversion_of_mem_sphere
  given: (h : x in Metric.sphere c R)
  statement: inversion c R x = x
  proof: h.out ▸ inversion_dist_center c x

中文:
定理 inversion_of_mem_sphere
  条件: (h : x in Metric.sphere c R)
  结论: inversion c R x = x
  证明: h.out ▸ inversion_dist_center c x

Depends on / 依赖: h.out, inversion_dist_center
-/
theorem inversion_of_mem_sphere (h : x in Metric.sphere c R) : inversion c R x = x :=
  h.out ▸ inversion_dist_center c x

/--
theorem `dist_inversion_center` / 定理 `dist_inversion_center`

English:
theorem dist_inversion_center
  given: (c x : P) (R : Real)
  statement: dist (inversion c R x) c = R ^ 2 / dist x c
  proof: by
  rcases eq_or_ne x c with (rfl | hx)
  · simp
  have : dist x c != 0 := dist_ne_zero.2 hx
  simp only [inversion]
  field_simp
  simp only [sq, dist_vadd_left, norm_smul, norm_div, norm_mul, Real.norm_eq_abs, abs_mul_abs_self,
    abs_dist, ← dist_eq_norm_vsub]
  field

中文:
定理 dist_inversion_center
  条件: (c x : P) (R : 实数)
  结论: dist (inversion c R x) c = R ^ 2 / dist x c
  证明: by
  rcases eq_or_ne x c with (rfl | hx)
  · simp
  have : dist x c != 0 := dist_ne_zero.2 hx
  simp only [inversion]
  field_simp
  simp only [sq, dist_vadd_left, norm_smul, norm_div, norm_mul, Real.norm_eq_abs, abs_mul_abs_self,
    abs_dist, ← dist_eq_norm_vsub]
  field

Depends on / 依赖: Real.norm_eq_abs, abs_dist, abs_mul_abs_self, dist_eq_norm_vsub, dist_ne_zero, dist_vadd_left, eq_or_ne, inversion, norm_div, norm_eq_abs, norm_mul, norm_smul
-/
theorem dist_inversion_center (c x : P) (R : Real) : dist (inversion c R x) c = R ^ 2 / dist x c := by
  rcases eq_or_ne x c with (rfl | hx)
  · simp
  have : dist x c != 0 := dist_ne_zero.2 hx
  simp only [inversion]
  field_simp
  simp only [sq, dist_vadd_left, norm_smul, norm_div, norm_mul, Real.norm_eq_abs, abs_mul_abs_self,
    abs_dist, ← dist_eq_norm_vsub]
  field

/--
theorem `dist_center_inversion` / 定理 `dist_center_inversion`

English:
theorem dist_center_inversion
  given: (c x : P) (R : Real)
  statement: dist c (inversion c R x) = R ^ 2 / dist c x
  proof: by
  rw [dist_comm c]; rw [dist_comm c]; rw [dist_inversion_center]

@[simp]

中文:
定理 dist_center_inversion
  条件: (c x : P) (R : 实数)
  结论: dist c (inversion c R x) = R ^ 2 / dist c x
  证明: by
  rw [dist_comm c]; rw [dist_comm c]; rw [dist_inversion_center]

@[simp]

Depends on / 依赖: dist_comm, dist_inversion_center
-/
theorem dist_center_inversion (c x : P) (R : Real) : dist c (inversion c R x) = R ^ 2 / dist c x := by
  rw [dist_comm c]; rw [dist_comm c]; rw [dist_inversion_center]

@[simp]
/--
theorem `inversion_inversion` / 定理 `inversion_inversion`

English:
theorem inversion_inversion
  given: (c : P) {R : Real} (hR : R != 0) (x : P)
  proof: by
  rcases eq_or_ne x c with (rfl | hne)
  · rw [inversion_self, inversion_self]
  · rw [inversion, dist_inversion_center, inversion_vsub_center, smul_smul, ← mul_pow,
      div_mul_div_comm, div_mul_cancel₀ _ (dist_ne_zero.2 hne), ← sq, div_self, one_pow, one_smul,
      vsub_vadd]
    exact pow_n

中文:
定理 inversion_inversion
  条件: (c : P) {R : 实数} (hR : R != 0) (x : P)
  证明: by
  rcases eq_or_ne x c with (rfl | hne)
  · rw [inversion_self, inversion_self]
  · rw [inversion, dist_inversion_center, inversion_vsub_center, smul_smul, ← mul_pow,
      div_mul_div_comm, div_mul_cancel₀ _ (dist_ne_zero.2 hne), ← sq, div_self, one_pow, one_smul,
      vsub_vadd]
    exact pow_n

Depends on / 依赖: dist_inversion_center, dist_ne_zero, div_mul_div_comm, div_self, eq_or_ne, inversion, inversion_self, inversion_vsub_center, mul_pow, one_pow, one_smul, pow_ne_zero, smul_smul, vsub_vadd
-/
theorem inversion_inversion (c : P) {R : Real} (hR : R != 0) (x : P) :
    inversion c R (inversion c R x) = x := by
  rcases eq_or_ne x c with (rfl | hne)
  · rw [inversion_self, inversion_self]
  · rw [inversion, dist_inversion_center, inversion_vsub_center, smul_smul, ← mul_pow,
      div_mul_div_comm, div_mul_cancel₀ _ (dist_ne_zero.2 hne), ← sq, div_self, one_pow, one_smul,
      vsub_vadd]
    exact pow_ne_zero _ hR

/--
theorem `inversion_involutive` / 定理 `inversion_involutive`

English:
theorem inversion_involutive
  given: (c : P) {R : Real} (hR : R != 0)
  statement: Involutive (inversion c R)
  proof: inversion_inversion c hR

中文:
定理 inversion_involutive
  条件: (c : P) {R : 实数} (hR : R != 0)
  结论: 对合 (inversion c R)
  证明: inversion_inversion c hR

Depends on / 依赖: inversion_inversion
-/
theorem inversion_involutive (c : P) {R : Real} (hR : R != 0) : Involutive (inversion c R) :=
  inversion_inversion c hR

/--
theorem `inversion_surjective` / 定理 `inversion_surjective`

English:
theorem inversion_surjective
  given: (c : P) {R : Real} (hR : R != 0)
  statement: Surjective (inversion c R)
  proof: (inversion_involutive c hR).surjective

中文:
定理 inversion_surjective
  条件: (c : P) {R : 实数} (hR : R != 0)
  结论: 满射 (inversion c R)
  证明: (inversion_involutive c hR).surjective

Depends on / 依赖: inversion_involutive, surjective
-/
theorem inversion_surjective (c : P) {R : Real} (hR : R != 0) : Surjective (inversion c R) :=
  (inversion_involutive c hR).surjective

/--
theorem `inversion_injective` / 定理 `inversion_injective`

English:
theorem inversion_injective
  given: (c : P) {R : Real} (hR : R != 0)
  statement: Injective (inversion c R)
  proof: (inversion_involutive c hR).injective

中文:
定理 inversion_injective
  条件: (c : P) {R : 实数} (hR : R != 0)
  结论: 单射 (inversion c R)
  证明: (inversion_involutive c hR).injective

Depends on / 依赖: injective, inversion_involutive
-/
theorem inversion_injective (c : P) {R : Real} (hR : R != 0) : Injective (inversion c R) :=
  (inversion_involutive c hR).injective

/--
theorem `inversion_bijective` / 定理 `inversion_bijective`

English:
theorem inversion_bijective
  given: (c : P) {R : Real} (hR : R != 0)
  statement: Bijective (inversion c R)
  proof: (inversion_involutive c hR).bijective

中文:
定理 inversion_bijective
  条件: (c : P) {R : 实数} (hR : R != 0)
  结论: 双射 (inversion c R)
  证明: (inversion_involutive c hR).bijective

Depends on / 依赖: bijective, inversion_involutive
-/
theorem inversion_bijective (c : P) {R : Real} (hR : R != 0) : Bijective (inversion c R) :=
  (inversion_involutive c hR).bijective

/--
theorem `inversion_eq_center` / 定理 `inversion_eq_center`

English:
theorem inversion_eq_center
  given: (hR : R != 0)
  statement: inversion c R x = c ↔ x = c
  proof: (inversion_injective c hR).eq_iff' inversion_self _ _

@[simp]

中文:
定理 inversion_eq_center
  条件: (hR : R != 0)
  结论: inversion c R x = c ↔ x = c
  证明: (inversion_injective c hR).eq_iff' inversion_self _ _

@[simp]

Depends on / 依赖: eq_iff, inversion_injective, inversion_self
-/
theorem inversion_eq_center (hR : R != 0) : inversion c R x = c ↔ x = c :=
(inversion_injective c hR).eq_iff' inversion_self _ _

@[simp]
/--
theorem `inversion_eq_center'` / 定理 `inversion_eq_center'`

English:
theorem inversion_eq_center'
  statement: inversion c R x = c ↔ x = c ∨ R = 0
  proof: by
  by_cases hR : R = 0 <;> simp [inversion_eq_center, hR]

中文:
定理 inversion_eq_center'
  结论: inversion c R x = c ↔ x = c ∨ R = 0
  证明: by
  by_cases hR : R = 0 <;> simp [inversion_eq_center, hR]

Depends on / 依赖: inversion_eq_center
-/
theorem inversion_eq_center' : inversion c R x = c ↔ x = c ∨ R = 0 := by
  by_cases hR : R = 0 <;> simp [inversion_eq_center, hR]

/--
theorem `center_eq_inversion` / 定理 `center_eq_inversion`

English:
theorem center_eq_inversion
  given: (hR : R != 0)
  statement: c = inversion c R x ↔ x = c
  proof: eq_comm.trans (inversion_eq_center hR)

@[simp]

中文:
定理 center_eq_inversion
  条件: (hR : R != 0)
  结论: c = inversion c R x ↔ x = c
  证明: eq_comm.trans (inversion_eq_center hR)

@[simp]

Depends on / 依赖: eq_comm, eq_comm.trans, inversion_eq_center
-/
theorem center_eq_inversion (hR : R != 0) : c = inversion c R x ↔ x = c :=
  eq_comm.trans (inversion_eq_center hR)

@[simp]
/--
theorem `center_eq_inversion'` / 定理 `center_eq_inversion'`

English:
theorem center_eq_inversion'
  statement: c = inversion c R x ↔ x = c ∨ R = 0
  proof: eq_comm.trans inversion_eq_center'

中文:
定理 center_eq_inversion'
  结论: c = inversion c R x ↔ x = c ∨ R = 0
  证明: eq_comm.trans inversion_eq_center'

Depends on / 依赖: eq_comm, eq_comm.trans, inversion_eq_center
-/
theorem center_eq_inversion' : c = inversion c R x ↔ x = c ∨ R = 0 :=
  eq_comm.trans inversion_eq_center'

/-!
### Similarity of triangles

If inversion with center `O` sends `A` to `A'` and `B` to `B'`, then the triangle `OB'A'` is similar
to the triangle `OAB` with coefficient `R ^ 2 / (|OA|*|OB|)` and the triangle `OA'B` is similar to
the triangle `OAB'` with coefficient `|OB|/|OA|`. We formulate these statements in terms of ratios
of the lengths of their sides.
-/

/--
theorem `dist_inversion_inversion` / 定理 `dist_inversion_inversion`

English:
theorem dist_inversion_inversion
  given: (hx : x != c) (hy : y != c) (R : Real)
  proof: by
  dsimp only [inversion]
  simp_rw [dist_vadd_cancel_right, dist_eq_norm_vsub V _ c]
  simpa only [dist_vsub_cancel_right] using
    dist_div_norm_sq_smul (vsub_ne_zero.2 hx) (vsub_ne_zero.2 hy) R

中文:
定理 dist_inversion_inversion
  条件: (hx : x != c) (hy : y != c) (R : 实数)
  证明: by
  dsimp only [inversion]
  simp_rw [dist_vadd_cancel_right, dist_eq_norm_vsub V _ c]
  simpa only [dist_vsub_cancel_right] using
    dist_div_norm_sq_smul (vsub_ne_zero.2 hx) (vsub_ne_zero.2 hy) R

Depends on / 依赖: dist_div_norm_sq_smul, dist_eq_norm_vsub, dist_vadd_cancel_right, dist_vsub_cancel_right, inversion, simp_rw, vsub_ne_zero
-/
theorem dist_inversion_inversion (hx : x != c) (hy : y != c) (R : Real) :
    dist (inversion c R x) (inversion c R y) = R ^ 2 / (dist x c * dist y c) * dist x y := by
  dsimp only [inversion]
  simp_rw [dist_vadd_cancel_right, dist_eq_norm_vsub V _ c]
  simpa only [dist_vsub_cancel_right] using
    dist_div_norm_sq_smul (vsub_ne_zero.2 hx) (vsub_ne_zero.2 hy) R

/--
theorem `dist_inversion_mul_dist_center_eq` / 定理 `dist_inversion_mul_dist_center_eq`

English:
theorem dist_inversion_mul_dist_center_eq
  given: (hx : x != c) (hy : y != c)
  proof: by
  rcases eq_or_ne R 0 with rfl | hR; · simp [dist_comm, mul_comm]
  have hy' : inversion c R y != c := by simp [*]
  conv in dist _ y => rw [← inversion_inversion c hR y]
  rw [dist_inversion_inversion hx hy']; rw [dist_inversion_center]
  field [dist_ne_zero.2 hx]

中文:
定理 dist_inversion_mul_dist_center_eq
  条件: (hx : x != c) (hy : y != c)
  证明: by
  rcases eq_or_ne R 0 with rfl | hR; · simp [dist_comm, mul_comm]
  have hy' : inversion c R y != c := by simp [*]
  conv in dist _ y => rw [← inversion_inversion c hR y]
  rw [dist_inversion_inversion hx hy']; rw [dist_inversion_center]
  field [dist_ne_zero.2 hx]

Depends on / 依赖: dist_comm, dist_inversion_center, dist_inversion_inversion, dist_ne_zero, eq_or_ne, inversion, inversion_inversion, mul_comm
-/
theorem dist_inversion_mul_dist_center_eq (hx : x != c) (hy : y != c) :
    dist (inversion c R x) y * dist x c = dist x (inversion c R y) * dist y c := by
  rcases eq_or_ne R 0 with rfl | hR; · simp [dist_comm, mul_comm]
  have hy' : inversion c R y != c := by simp [*]
  conv in dist _ y => rw [← inversion_inversion c hR y]
  rw [dist_inversion_inversion hx hy']; rw [dist_inversion_center]
  field [dist_ne_zero.2 hx]

/-!
### Ptolemy's inequality
-/

include V in
/--
theorem `mul_dist_le_mul_dist_add_mul_dist` / 定理 `mul_dist_le_mul_dist_add_mul_dist`

English:
theorem mul_dist_le_mul_dist_add_mul_dist
  given: (a b c d : P)
  proof: by
  -- If one of the points `b`, `c`, `d` is equal to `a`, then the inequality is trivial.
  rcases eq_or_ne b a with (rfl | hb)
  · rw [dist_self, zero_mul, zero_add]
  rcases eq_or_ne c a with (rfl | hc)
  · rw [dist_self, zero_mul]
    positivity
  rcases eq_or_ne d a with (rfl | hd)
  · rw [dis

中文:
定理 mul_dist_le_mul_dist_add_mul_dist
  条件: (a b c d : P)
  证明: by
  -- If one of the points `b`, `c`, `d` is equal to `a`, then the inequality is trivial.
  rcases eq_or_ne b a with (rfl | hb)
  · rw [dist_self, zero_mul, zero_add]
  rcases eq_or_ne c a with (rfl | hc)
  · rw [dist_self, zero_mul]
    positivity
  rcases eq_or_ne d a with (rfl | hd)
  · rw [dis
-/
theorem mul_dist_le_mul_dist_add_mul_dist (a b c d : P) :
    dist a c * dist b d <= dist a b * dist c d + dist b c * dist a d := by
  -- If one of the points `b`, `c`, `d` is equal to `a`, then the inequality is trivial.
  rcases eq_or_ne b a with (rfl | hb)
  · rw [dist_self, zero_mul, zero_add]
  rcases eq_or_ne c a with (rfl | hc)
  · rw [dist_self, zero_mul]
    positivity
  rcases eq_or_ne d a with (rfl | hd)
  · rw [dist_self, mul_zero, add_zero, dist_comm d, dist_comm d, mul_comm]
  /- Otherwise, we apply the triangle inequality to `EuclideanGeometry.inversion a 1 b`,
    `EuclideanGeometry.inversion a 1 c`, and `EuclideanGeometry.inversion a 1 d`. -/
  have H := dist_triangle (inversion a 1 b) (inversion a 1 c) (inversion a 1 d)
  rw [dist_inversion_inversion hb hd]; rw [dist_inversion_inversion hb hc]; rw [dist_inversion_inversion hc hd]; rw [one_pow] at H
  rw [← dist_pos] at hb hc hd
  rw [← div_le_div_iff_of_pos_right (mul_pos hb (mul_pos hc hd))]
  convert! H using 1 <;> simp [field, dist_comm a]; ring

end EuclideanGeometry

open EuclideanGeometry


/--
theorem `Filter.Tendsto.inversion` / 定理 `Filter.Tendsto.inversion`

English:
theorem Filter.Tendsto.inversion
  statement: {α : Type*} {x c : P} {R : Real} {l : Filter α}
  proof: (((hR.div (hx.dist hc) <| dist_ne_zero.2 hne).pow 2).smul (hx.vsub hc)).vadd hc

中文:
定理 滤子.收敛.inversion
  结论: {α : 类型} {x c : P} {R : 实数} {l : 滤子 α}
  证明: (((hR.div (hx.dist hc) <| dist_ne_zero.2 hne).pow 2).smul (hx.vsub hc)).vadd hc
-/
protected theorem Filter.Tendsto.inversion {α : Type*} {x c : P} {R : Real} {l : Filter α}
    {fc fx : α -> P} {fR : α -> Real} (hc : Tendsto fc l (𝓝 c)) (hR : Tendsto fR l (𝓝 R))
    (hx : Tendsto fx l (𝓝 x)) (hne : x != c) :
    Tendsto (fun a => inversion (fc a) (fR a) (fx a)) l (𝓝 (inversion c R x)) :=
  (((hR.div (hx.dist hc) <| dist_ne_zero.2 hne).pow 2).smul (hx.vsub hc)).vadd hc

variable {X : Type*} [TopologicalSpace X] {c x : X -> P} {R : X -> Real} {a₀ : X} {s : Set X}

protected nonrec theorem ContinuousWithinAt.inversion (hc : ContinuousWithinAt c s a₀)
    (hR : ContinuousWithinAt R s a₀) (hx : ContinuousWithinAt x s a₀) (hne : x a₀ != c a₀) :
    ContinuousWithinAt (fun a => inversion (c a) (R a) (x a)) s a₀ :=
  hc.inversion hR hx hne

protected nonrec theorem ContinuousAt.inversion (hc : ContinuousAt c a₀) (hR : ContinuousAt R a₀)
    (hx : ContinuousAt x a₀) (hne : x a₀ != c a₀) :
    ContinuousAt (fun a => inversion (c a) (R a) (x a)) a₀ :=
  hc.inversion hR hx hne

/--
theorem `ContinuousOn.inversion` / 定理 `ContinuousOn.inversion`

English:
theorem ContinuousOn.inversion
  statement: (hc : ContinuousOn c s) (hR : ContinuousOn R s)
  proof: fun a ha =>
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

中文:
定理 ContinuousOn.inversion
  结论: (hc : ContinuousOn c s) (hR : ContinuousOn R s)
  证明: fun a ha =>
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)
-/
protected theorem ContinuousOn.inversion (hc : ContinuousOn c s) (hR : ContinuousOn R s)
    (hx : ContinuousOn x s) (hne : forall a in s, x a != c a) :
    ContinuousOn (fun a => inversion (c a) (R a) (x a)) s := fun a ha =>
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

/--
theorem `Continuous.inversion` / 定理 `Continuous.inversion`

English:
theorem Continuous.inversion
  statement: (hc : Continuous c) (hR : Continuous R) (hx : Continuous x)
  proof: continuous_iff_continuousAt.2 fun _ =>
    hc.continuousAt.inversion hR.continuousAt hx.continuousAt (hne _)

中文:
定理 连续.inversion
  结论: (hc : 连续 c) (hR : 连续 R) (hx : 连续 x)
  证明: continuous_iff_continuousAt.2 fun _ =>
    hc.continuousAt.inversion hR.continuousAt hx.continuousAt (hne _)
-/
protected theorem Continuous.inversion (hc : Continuous c) (hR : Continuous R) (hx : Continuous x)
    (hne : forall a, x a != c a) : Continuous (fun a => inversion (c a) (R a) (x a)) :=
  continuous_iff_continuousAt.2 fun _ =>
    hc.continuousAt.inversion hR.continuousAt hx.continuousAt (hne _)

namespace EuclideanGeometry

open Filter in
/--
theorem `tendsto_inversion_nhdsNE_center_cobounded` / 定理 `tendsto_inversion_nhdsNE_center_cobounded`

English:
theorem tendsto_inversion_nhdsNE_center_cobounded
  given: {c : P} {R : Real} (hR : R != 0)
  proof: by
  rw [← tendsto_dist_left_atTop_iff c]
  have hdist : Tendsto (dist c) (𝓝[!=] c) (𝓝[>] (0 : Real)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds ?_, eventually_nhdsWithin_of_forall ?_⟩
    · rw [← dist_self c]
exact ContinuousAt.tendsto by fun_prop
    · aes

中文:
定理 tendsto_inversion_nhdsNE_center_cobounded
  条件: {c : P} {R : 实数} (hR : R != 0)
  证明: by
  rw [← tendsto_dist_left_atTop_iff c]
  have hdist : Tendsto (dist c) (𝓝[!=] c) (𝓝[>] (0 : Real)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds ?_, eventually_nhdsWithin_of_forall ?_⟩
    · rw [← dist_self c]
exact ContinuousAt.tendsto by fun_prop
    · aes

Depends on / 依赖: ContinuousAt, ContinuousAt.tendsto, Tendsto, const_mul_atTop, dist_center_inversion, dist_self, div_eq_mul_inv, eventually_nhdsWithin_of_forall, fun_prop, hdist.inv_tendsto_nhdsGT_zero.const_mul_atTop, hratio, inv_tendsto_nhdsGT_zero, inversion, simp_rw, sq_pos_iff, tendsto, tendsto_dist_left_atTop_iff, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_of_tendsto_nhds
-/
theorem tendsto_inversion_nhdsNE_center_cobounded {c : P} {R : Real} (hR : R != 0) :
    Tendsto (inversion c R) (𝓝[!=] c) (Bornology.cobounded P) := by
  rw [← tendsto_dist_left_atTop_iff c]
  have hdist : Tendsto (dist c) (𝓝[!=] c) (𝓝[>] (0 : Real)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds ?_, eventually_nhdsWithin_of_forall ?_⟩
    · rw [← dist_self c]
exact ContinuousAt.tendsto by fun_prop
    · aesop
  have hratio : Tendsto (fun x : P => dist c (inversion c R x)) (𝓝[!=] c) atTop := by
    simp_rw [dist_center_inversion, div_eq_mul_inv]
exact hdist.inv_tendsto_nhdsGT_zero.const_mul_atTop by rwa [sq_pos_iff]
  simpa using hratio

end EuclideanGeometry
