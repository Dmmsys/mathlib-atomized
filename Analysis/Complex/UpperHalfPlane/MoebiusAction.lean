/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Group action on the upper half-plane

We equip the upper half-plane with the structure of a `GL (Fin 2) ℝ` action by fractional linear
transformations (composing with complex conjugation when needed to extend the action from the
positive-determinant subgroup, so that `!![-1, 0; 0, 1]` acts as `z ↦ -conj z`.)
-/

@[expose] public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace UpperHalfPlane

/--
Definition of `num` / `num` 的定义

English:
definition num
  signature: (g : GL (Fin 2) Real) (z : Complex)
  body: g 0 0 * z + g 0 1

中文:
定义 num
  签名: (g : GL (有限集 2) 实数) (z : 复形)
  定义体: g 0 0 * z + g 0 1
-/
def num (g : GL (Fin 2) Real) (z : Complex) : Complex := g 0 0 * z + g 0 1

/--
Definition of `denom` / `denom` 的定义

English:
definition denom
  signature: (g : GL (Fin 2) Real) (z : Complex)
  body: g 1 0 * z + g 1 1

@[simp]

中文:
定义 denom
  签名: (g : GL (有限集 2) 实数) (z : 复形)
  定义体: g 1 0 * z + g 1 1

@[simp]
-/
def denom (g : GL (Fin 2) Real) (z : Complex) : Complex := g 1 0 * z + g 1 1

@[simp]
/--
lemma `num_neg` / 引理 `num_neg`

English:
lemma num_neg
  given: (g : GL (Fin 2) Real) (z : Complex)
  statement: num (-g) z = -(num g z)
  proof: by
  simp [num]; ring

@[simp]

中文:
引理 num_neg
  条件: (g : GL (有限集 2) 实数) (z : 复形)
  结论: num (-g) z = -(num g z)
  证明: by
  simp [num]; ring

@[simp]
-/
lemma num_neg (g : GL (Fin 2) Real) (z : Complex) : num (-g) z = -(num g z) := by
  simp [num]; ring

@[simp]
/--
lemma `denom_neg` / 引理 `denom_neg`

English:
lemma denom_neg
  given: (g : GL (Fin 2) Real) (z : Complex)
  statement: denom (-g) z = -(denom g z)
  proof: by
  simp [denom]; ring

中文:
引理 denom_neg
  条件: (g : GL (有限集 2) 实数) (z : 复形)
  结论: denom (-g) z = -(denom g z)
  证明: by
  simp [denom]; ring
-/
lemma denom_neg (g : GL (Fin 2) Real) (z : Complex) : denom (-g) z = -(denom g z) := by
  simp [denom]; ring

/--
theorem `linear_ne_zero_of_im` / 定理 `linear_ne_zero_of_im`

English:
theorem linear_ne_zero_of_im
  given: {cd : Fin 2 -> Real} {z : Complex} (hz : z.im != 0) (h : cd != 0)
  proof: by
  contrapose h
  have : cd 0 = 0 := by
    -- we will need this twice
    apply_fun Complex.im at h
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, mul_eq_zero, hz, or_false] using! h
  simp only [this, zero_mul, Complex.ofReal_zero, z

中文:
定理 linear_ne_zero_of_im
  条件: {cd : 有限集 2 -> 实数} {z : 复形} (hz : z.im != 0) (h : cd != 0)
  证明: by
  contrapose h
  have : cd 0 = 0 := by
    -- we will need this twice
    apply_fun Complex.im at h
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, mul_eq_zero, hz, or_false] using! h
  simp only [this, zero_mul, Complex.ofReal_zero, z

Depends on / 依赖: contrapose
-/
theorem linear_ne_zero_of_im {cd : Fin 2 -> Real} {z : Complex} (hz : z.im != 0) (h : cd != 0) :
    (cd 0 : Complex) * z + cd 1 != 0 := by
  contrapose h
  have : cd 0 = 0 := by
    -- we will need this twice
    apply_fun Complex.im at h
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, mul_eq_zero, hz, or_false] using! h
  simp only [this, zero_mul, Complex.ofReal_zero, zero_add, Complex.ofReal_eq_zero] at h
  ext i
  fin_cases i <;> assumption

/--
theorem `linear_ne_zero` / 定理 `linear_ne_zero`

English:
theorem linear_ne_zero
  given: {cd : Fin 2 -> Real} (τ : ℍ) (h : cd != 0)
  proof: linear_ne_zero_of_im τ.im_ne_zero h

中文:
定理 linear_ne_zero
  条件: {cd : 有限集 2 -> 实数} (τ : ℍ) (h : cd != 0)
  证明: linear_ne_zero_of_im τ.im_ne_zero h

Depends on / 依赖: im_ne_zero, linear_ne_zero_of_im
-/
theorem linear_ne_zero {cd : Fin 2 -> Real} (τ : ℍ) (h : cd != 0) :
    (cd 0 : Complex) * τ + cd 1 != 0 :=
  linear_ne_zero_of_im τ.im_ne_zero h

/--
theorem `denom_ne_zero_of_im` / 定理 `denom_ne_zero_of_im`

English:
theorem denom_ne_zero_of_im
  given: (g : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0)
  statement: denom g z != 0
  proof: by
  refine linear_ne_zero_of_im hz fun H => g.det.ne_zero ?_
  simp [Matrix.det_fin_two, H]

@[simp]

中文:
定理 denom_ne_zero_of_im
  条件: (g : GL (有限集 2) 实数) {z : 复形} (hz : z.im != 0)
  结论: denom g z != 0
  证明: by
  refine linear_ne_zero_of_im hz fun H => g.det.ne_zero ?_
  simp [Matrix.det_fin_two, H]

@[simp]

Depends on / 依赖: Matrix, Matrix.det_fin_two, det_fin_two, g.det.ne_zero, linear_ne_zero_of_im, ne_zero
-/
theorem denom_ne_zero_of_im (g : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0) : denom g z != 0 := by
  refine linear_ne_zero_of_im hz fun H => g.det.ne_zero ?_
  simp [Matrix.det_fin_two, H]

@[simp]
/--
theorem `denom_ne_zero` / 定理 `denom_ne_zero`

English:
theorem denom_ne_zero
  given: (g : GL (Fin 2) Real) (z : ℍ)
  statement: denom g z != 0
  proof: denom_ne_zero_of_im g z.im_ne_zero

中文:
定理 denom_ne_zero
  条件: (g : GL (有限集 2) 实数) (z : ℍ)
  结论: denom g z != 0
  证明: denom_ne_zero_of_im g z.im_ne_zero

Depends on / 依赖: denom_ne_zero_of_im, im_ne_zero, z.im_ne_zero
-/
theorem denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ) : denom g z != 0 :=
  denom_ne_zero_of_im g z.im_ne_zero

/--
theorem `normSq_denom_pos` / 定理 `normSq_denom_pos`

English:
theorem normSq_denom_pos
  given: (g : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0)
  proof: Complex.normSq_pos.mpr (denom_ne_zero_of_im g hz)

中文:
定理 normSq_denom_pos
  条件: (g : GL (有限集 2) 实数) {z : 复形} (hz : z.im != 0)
  证明: Complex.normSq_pos.mpr (denom_ne_zero_of_im g hz)

Depends on / 依赖: Complex.normSq_pos.mpr, denom_ne_zero_of_im, normSq_pos
-/
theorem normSq_denom_pos (g : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0) :
    0 < Complex.normSq (denom g z) :=
  Complex.normSq_pos.mpr (denom_ne_zero_of_im g hz)

/--
theorem `normSq_denom_ne_zero` / 定理 `normSq_denom_ne_zero`

English:
theorem normSq_denom_ne_zero
  given: (g : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0)
  proof: ne_of_gt (normSq_denom_pos g hz)

中文:
定理 normSq_denom_ne_zero
  条件: (g : GL (有限集 2) 实数) {z : 复形} (hz : z.im != 0)
  证明: ne_of_gt (normSq_denom_pos g hz)

Depends on / 依赖: ne_of_gt, normSq_denom_pos
-/
theorem normSq_denom_ne_zero (g : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0) :
    Complex.normSq (denom g z) != 0 :=
  ne_of_gt (normSq_denom_pos g hz)

/--
lemma `denom_cocycle` / 引理 `denom_cocycle`

English:
lemma denom_cocycle
  given: (g h : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0)
  proof: by
  change _ = (_ * (_ / _) + _) * _
  field_simp [denom_ne_zero_of_im h hz]
  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one, Complex.ofReal_add,
    Complex.ofReal_mul, num]
  ring

中文:
引理 denom_cocycle
  条件: (g h : GL (有限集 2) 实数) {z : 复形} (hz : z.im != 0)
  证明: by
  change _ = (_ * (_ / _) + _) * _
  field_simp [denom_ne_zero_of_im h hz]
  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one, Complex.ofReal_add,
    Complex.ofReal_mul, num]
  ring

Depends on / 依赖: Complex.ofReal_add, Complex.ofReal_mul, Fin.default_eq_zero, Fin.succ_zero_eq_one, Fin.sum_univ_succ, Finset, Finset.sum_singleton, Finset.univ_unique, Units.val_mul, default_eq_zero, denom_ne_zero_of_im, mul_apply, ofReal_add, ofReal_mul, succ_zero_eq_one, sum_singleton, sum_univ_succ, univ_unique, val_mul
-/
lemma denom_cocycle (g h : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0) :
    denom (g * h) z = denom g (num h z / denom h z) * denom h z := by
  change _ = (_ * (_ / _) + _) * _
  field_simp [denom_ne_zero_of_im h hz]
  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one, Complex.ofReal_add,
    Complex.ofReal_mul, num]
  ring

/--
lemma `moebius_im` / 引理 `moebius_im`

English:
lemma moebius_im
  given: (g : GL (Fin 2) Real) (z : Complex)
  proof: by
  simp only [num, denom, Complex.div_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero, ← sub_div,
    GeneralLinearGroup.val_det_apply, g.1.det_fin_two]
  ring

中文:
引理 moebius_im
  条件: (g : GL (有限集 2) 实数) (z : 复形)
  证明: by
  simp only [num, denom, Complex.div_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero, ← sub_div,
    GeneralLinearGroup.val_det_apply, g.1.det_fin_two]
  ring

Depends on / 依赖: Complex.add_im, Complex.add_re, Complex.div_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, GeneralLinearGroup, GeneralLinearGroup.val_det_apply, add_im, add_re, add_zero, det_fin_two, div_im, mul_im, mul_re, ofReal_im, ofReal_re, sub_div, sub_zero
-/
lemma moebius_im (g : GL (Fin 2) Real) (z : Complex) :
    (num g z / denom g z).im = g.det.val * z.im / Complex.normSq (denom g z) := by
  simp only [num, denom, Complex.div_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero, ← sub_div,
    GeneralLinearGroup.val_det_apply, g.1.det_fin_two]
  ring

/--
Definition of `σ` / `σ` 的定义

English:
definition σ
  signature: (g : GL (Fin 2) Real)
  body: if 0 < g.det.val then .refl Real Complex else Complex.conjCAE

中文:
定义 σ
  签名: (g : GL (有限集 2) 实数)
  定义体: if 0 < g.det.val then .refl Real Complex else Complex.conjCAE

Depends on / 依赖: Complex.conjCAE, conjCAE, g.det.val
-/
noncomputable def σ (g : GL (Fin 2) Real) : Complex ≃A[Real] Complex :=
  if 0 < g.det.val then .refl Real Complex else Complex.conjCAE

/--
lemma `σ_conj` / 引理 `σ_conj`

English:
lemma σ_conj
  given: (g : GL (Fin 2) Real) (z : Complex)
  statement: σ g (conj z) = conj (σ g z)
  proof: by
  simp only [σ]
  split_ifs <;> simp

@[simp]

中文:
引理 σ_conj
  条件: (g : GL (有限集 2) 实数) (z : 复形)
  结论: σ g (conj z) = conj (σ g z)
  证明: by
  simp only [σ]
  split_ifs <;> simp

@[simp]

Depends on / 依赖: split_ifs
-/
lemma σ_conj (g : GL (Fin 2) Real) (z : Complex) : σ g (conj z) = conj (σ g z) := by
  simp only [σ]
  split_ifs <;> simp

@[simp]
/--
lemma `σ_ofReal` / 引理 `σ_ofReal`

English:
lemma σ_ofReal
  given: (g : GL (Fin 2) Real) (y : Real)
  statement: σ g y = y
  proof: by
  simp only [σ]
  split_ifs <;> simp

中文:
引理 σ_of实数
  条件: (g : GL (有限集 2) 实数) (y : 实数)
  结论: σ g y = y
  证明: by
  simp only [σ]
  split_ifs <;> simp

Depends on / 依赖: split_ifs
-/
lemma σ_ofReal (g : GL (Fin 2) Real) (y : Real) : σ g y = y := by
  simp only [σ]
  split_ifs <;> simp

/--
lemma `σ_num` / 引理 `σ_num`

English:
lemma σ_num
  given: (g h : GL (Fin 2) Real) (z : Complex)
  statement: σ g (num h z) = num h (σ g z)
  proof: by
  simp [num]

中文:
引理 σ_num
  条件: (g h : GL (有限集 2) 实数) (z : 复形)
  结论: σ g (num h z) = num h (σ g z)
  证明: by
  simp [num]
-/
lemma σ_num (g h : GL (Fin 2) Real) (z : Complex) : σ g (num h z) = num h (σ g z) := by
  simp [num]

/--
lemma `σ_denom` / 引理 `σ_denom`

English:
lemma σ_denom
  given: (g h : GL (Fin 2) Real) (z : Complex)
  statement: σ g (denom h z) = denom h (σ g z)
  proof: by
  simp [denom]

中文:
引理 σ_denom
  条件: (g h : GL (有限集 2) 实数) (z : 复形)
  结论: σ g (denom h z) = denom h (σ g z)
  证明: by
  simp [denom]
-/
lemma σ_denom (g h : GL (Fin 2) Real) (z : Complex) : σ g (denom h z) = denom h (σ g z) := by
  simp [denom]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `σ_neg` / 引理 `σ_neg`

English:
lemma σ_neg
  given: (g : GL (Fin 2) Real)
  statement: σ (-g) = σ g
  proof: by
  simp [σ, det_neg]

@[simp]

中文:
引理 σ_neg
  条件: (g : GL (有限集 2) 实数)
  结论: σ (-g) = σ g
  证明: by
  simp [σ, det_neg]

@[simp]

Depends on / 依赖: det_neg
-/
lemma σ_neg (g : GL (Fin 2) Real) : σ (-g) = σ g := by
  simp [σ, det_neg]

@[simp]
/--
lemma `σ_sq` / 引理 `σ_sq`

English:
lemma σ_sq
  given: (g : GL (Fin 2) Real) (z : Complex)
  statement: σ g (σ g z) = z
  proof: by
  simp only [σ]
  split_ifs <;> simp

中文:
引理 σ_sq
  条件: (g : GL (有限集 2) 实数) (z : 复形)
  结论: σ g (σ g z) = z
  证明: by
  simp only [σ]
  split_ifs <;> simp

Depends on / 依赖: split_ifs
-/
lemma σ_sq (g : GL (Fin 2) Real) (z : Complex) : σ g (σ g z) = z := by
  simp only [σ]
  split_ifs <;> simp

/--
lemma `σ_im_ne_zero` / 引理 `σ_im_ne_zero`

English:
lemma σ_im_ne_zero
  given: {g z}
  statement: (σ g z).im != 0 ↔ z.im != 0
  proof: by
  simp only [σ]
  split_ifs <;> simp

中文:
引理 σ_im_ne_zero
  条件: {g z}
  结论: (σ g z).im != 0 ↔ z.im != 0
  证明: by
  simp only [σ]
  split_ifs <;> simp

Depends on / 依赖: split_ifs
-/
lemma σ_im_ne_zero {g z} : (σ g z).im != 0 ↔ z.im != 0 := by
  simp only [σ]
  split_ifs <;> simp

/--
lemma `σ_mul` / 引理 `σ_mul`

English:
lemma σ_mul
  given: (g g' : GL (Fin 2) Real) (z : Complex)
  statement: σ (g * g') z = σ g (σ g' z)
  proof: by
  simp only [σ, map_mul, Units.val_mul]
  rcases g.det_ne_zero.lt_or_gt with (h | h) <;>
  rcases g'.det_ne_zero.lt_or_gt with (h' | h')
  · simp [mul_pos_of_neg_of_neg h h', h.not_gt, h'.not_gt]
  · simp [(mul_neg_of_neg_of_pos h h').not_gt, h.not_gt, h']
  · simp [(mul_neg_of_pos_of_neg h h').n

中文:
引理 σ_mul
  条件: (g g' : GL (有限集 2) 实数) (z : 复形)
  结论: σ (g * g') z = σ g (σ g' z)
  证明: by
  simp only [σ, map_mul, Units.val_mul]
  rcases g.det_ne_zero.lt_or_gt with (h | h) <;>
  rcases g'.det_ne_zero.lt_or_gt with (h' | h')
  · simp [mul_pos_of_neg_of_neg h h', h.not_gt, h'.not_gt]
  · simp [(mul_neg_of_neg_of_pos h h').not_gt, h.not_gt, h']
  · simp [(mul_neg_of_pos_of_neg h h').n

Depends on / 依赖: Units.val_mul, det_ne_zero, det_ne_zero.lt_or_gt, g.det_ne_zero.lt_or_gt, h.not_gt, lt_or_gt, map_mul, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg, mul_pos, mul_pos_of_neg_of_neg, not_gt, val_mul
-/
lemma σ_mul (g g' : GL (Fin 2) Real) (z : Complex) : σ (g * g') z = σ g (σ g' z) := by
  simp only [σ, map_mul, Units.val_mul]
  rcases g.det_ne_zero.lt_or_gt with (h | h) <;>
  rcases g'.det_ne_zero.lt_or_gt with (h' | h')
  · simp [mul_pos_of_neg_of_neg h h', h.not_gt, h'.not_gt]
  · simp [(mul_neg_of_neg_of_pos h h').not_gt, h.not_gt, h']
  · simp [(mul_neg_of_pos_of_neg h h').not_gt, h, h'.not_gt]
  · simp [mul_pos h h', h, h']

/--
lemma `σ_mul_comm` / 引理 `σ_mul_comm`

English:
lemma σ_mul_comm
  given: (g h : GL (Fin 2) Real) (z : Complex)
  statement: σ g (σ h z) = σ h (σ g z)
  proof: by
  simp only [σ]
  split_ifs <;> simp

中文:
引理 σ_mul_comm
  条件: (g h : GL (有限集 2) 实数) (z : 复形)
  结论: σ g (σ h z) = σ h (σ g z)
  证明: by
  simp only [σ]
  split_ifs <;> simp

Depends on / 依赖: split_ifs
-/
lemma σ_mul_comm (g h : GL (Fin 2) Real) (z : Complex) : σ g (σ h z) = σ h (σ g z) := by
  simp only [σ]
  split_ifs <;> simp

/--
lemma `norm_σ` / 引理 `norm_σ`

English:
lemma norm_σ
  given: (g : GL (Fin 2) Real) (z : Complex)
  statement: ‖σ g z‖ = ‖z‖
  proof: by
  simp only [σ]
  split_ifs <;> simp

中文:
引理 norm_σ
  条件: (g : GL (有限集 2) 实数) (z : 复形)
  结论: ‖σ g z‖ = ‖z‖
  证明: by
  simp only [σ]
  split_ifs <;> simp
-/
@[simp] lemma norm_σ (g : GL (Fin 2) Real) (z : Complex) : ‖σ g z‖ = ‖z‖ := by
  simp only [σ]
  split_ifs <;> simp

/--
Definition of `smulAux'` / `smulAux'` 的定义

English:
definition smulAux'
  signature: (g : GL (Fin 2) Real) (z : Complex)
  body: σ g (num g z / denom g z)

中文:
定义 smulAux'
  签名: (g : GL (有限集 2) 实数) (z : 复形)
  定义体: σ g (num g z / denom g z)
-/
def smulAux' (g : GL (Fin 2) Real) (z : Complex) : Complex := σ g (num g z / denom g z)

/--
lemma `smulAux'_im` / 引理 `smulAux'_im`

English:
lemma smulAux'_im
  given: (g : GL (Fin 2) Real) (z : Complex)
  proof: by
  simp only [smulAux', σ]
  split_ifs with h <;>
  [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]] <;>
  simpa only [Complex.conjCAE_apply, Complex.star_def, Complex.conj_im,
    neg_mul, neg_div, neg_inj] using! moebius_im g z

中文:
引理 smulAux'_im
  条件: (g : GL (有限集 2) 实数) (z : 复形)
  证明: by
  simp only [smulAux', σ]
  split_ifs with h <;>
  [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]] <;>
  simpa only [Complex.conjCAE_apply, Complex.star_def, Complex.conj_im,
    neg_mul, neg_div, neg_inj] using! moebius_im g z
-/
lemma smulAux'_im (g : GL (Fin 2) Real) (z : Complex) :
    (smulAux' g z).im = |g.det.val| * z.im / Complex.normSq (denom g z) := by
  simp only [smulAux', σ]
  split_ifs with h <;>
  [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]] <;>
  simpa only [Complex.conjCAE_apply, Complex.star_def, Complex.conj_im,
    neg_mul, neg_div, neg_inj] using! moebius_im g z

/--
Definition of `smulAux` / `smulAux` 的定义

English:
definition smulAux
  signature: (g : GL (Fin 2) Real) (z : ℍ)
  body: mk (smulAux' g z) by
    rw [smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) z.im_pos) (normSq_denom_pos _ z.im_ne_zero)

中文:
定义 smulAux
  签名: (g : GL (有限集 2) 实数) (z : ℍ)
  定义体: mk (smulAux' g z) by
    rw [smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) z.im_pos) (normSq_denom_pos _ z.im_ne_zero)

Depends on / 依赖: abs_pos, abs_pos.mpr, div_pos, g.det.ne_zero, im_ne_zero, im_pos, mul_pos, ne_zero, normSq_denom_pos, smulAux, z.im_ne_zero, z.im_pos
-/
def smulAux (g : GL (Fin 2) Real) (z : ℍ) : ℍ :=
mk (smulAux' g z) by
    rw [smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) z.im_pos) (normSq_denom_pos _ z.im_ne_zero)

/--
lemma `denom_cocycle'` / 引理 `denom_cocycle'`

English:
lemma denom_cocycle'
  given: (g h : GL (Fin 2) Real) (z : ℍ)
  proof: by
  simpa [smulAux, smulAux', denom, σ_sq] using denom_cocycle g h z.im_ne_zero

中文:
引理 denom_cocycle'
  条件: (g h : GL (有限集 2) 实数) (z : ℍ)
  证明: by
  simpa [smulAux, smulAux', denom, σ_sq] using denom_cocycle g h z.im_ne_zero

Depends on / 依赖: denom_cocycle, im_ne_zero, smulAux, z.im_ne_zero
-/
lemma denom_cocycle' (g h : GL (Fin 2) Real) (z : ℍ) :
    denom (g * h) z = σ h (denom g (smulAux h z)) * denom h z := by
  simpa [smulAux, smulAux', denom, σ_sq] using denom_cocycle g h z.im_ne_zero

/--
theorem `mul_smul'` / 定理 `mul_smul'`

English:
theorem mul_smul'
  given: (g h : GL (Fin 2) Real) (z : ℍ)
  proof: by
  ext : 1
  simp only [smulAux, coe_mk, smulAux', map_div₀, σ_num, σ_denom, σ_mul]
  generalize hu : σ g (σ h z) = u
  have hu : u.im != 0 := by simpa only [← hu, σ_im_ne_zero] using! z.im_ne_zero
  have hu' : (num h u / denom h u).im != 0 := by
    rw [moebius_im]
    exact div_ne_zero (mul_ne_z

中文:
定理 mul_smul'
  条件: (g h : GL (有限集 2) 实数) (z : ℍ)
  证明: by
  ext : 1
  simp only [smulAux, coe_mk, smulAux', map_div₀, σ_num, σ_denom, σ_mul]
  generalize hu : σ g (σ h z) = u
  have hu : u.im != 0 := by simpa only [← hu, σ_im_ne_zero] using! z.im_ne_zero
  have hu' : (num h u / denom h u).im != 0 := by
    rw [moebius_im]
    exact div_ne_zero (mul_ne_z

Depends on / 依赖: coe_mk, conv_, denom_ne_zero_of_im, det_ne_zero, div_add, div_eq_div_iff, div_ne_zero, generalize, h.det_ne_zero, im_ne_zero, moebius_im, mul_div, mul_ne_zero, normSq_denom_ne_zero, smulAux, u.im, z.im_ne_zero
-/
theorem mul_smul' (g h : GL (Fin 2) Real) (z : ℍ) :
    smulAux (g * h) z = smulAux g (smulAux h z) := by
  ext : 1
  simp only [smulAux, coe_mk, smulAux', map_div₀, σ_num, σ_denom, σ_mul]
  generalize hu : σ g (σ h z) = u
  have hu : u.im != 0 := by simpa only [← hu, σ_im_ne_zero] using! z.im_ne_zero
  have hu' : (num h u / denom h u).im != 0 := by
    rw [moebius_im]
    exact div_ne_zero (mul_ne_zero h.det_ne_zero hu) (normSq_denom_ne_zero _ hu)
  rw [div_eq_div_iff (denom_ne_zero_of_im _ hu) (denom_ne_zero_of_im _ hu')]; rw [denom]; rw [mul_div]; rw [div_add' _ _ _ (denom_ne_zero_of_im _ hu)]; rw [mul_div]
  conv_rhs => rw [num]
  rw [mul_div]; rw [div_add' _ _ _ (denom_ne_zero_of_im _ hu)]; rw [div_mul_eq_mul_div]
  congr 1
  simp only [num, denom, Units.val_mul, mul_apply, Fin.sum_univ_succ,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

/--
Instance `glAction` / 实例 `glAction`

English:
instance glAction
  signature: : MulAction (GL (Fin 2) Real) ℍ where
  body: smulAux
  one_smul z := by
    change smulAux 1 z = z
    simp [smulAux, smulAux', num, denom, σ]
  mul_smul := mul_smul'

中文:
实例 glAction
  签名: : 乘法作用 (GL (有限集 2) 实数) ℍ where
  定义体: smulAux
  one_smul z := by
    change smulAux 1 z = z
    simp [smulAux, smulAux', num, denom, σ]
  mul_smul := mul_smul'

Depends on / 依赖: smulAux
-/
instance glAction : MulAction (GL (Fin 2) Real) ℍ where
  smul := smulAux
  one_smul z := by
    change smulAux 1 z = z
    simp [smulAux, smulAux', num, denom, σ]
  mul_smul := mul_smul'

/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (g : GL (Fin 2) Real) (z : ℍ)
  proof: rfl

中文:
引理 coe_smul
  条件: (g : GL (有限集 2) 实数) (z : ℍ)
  证明: rfl
-/
lemma coe_smul (g : GL (Fin 2) Real) (z : ℍ) :
    ↑(g • z) = σ g (num g z / denom g z) := rfl

/--
lemma `coe_smul_of_det_pos` / 引理 `coe_smul_of_det_pos`

English:
lemma coe_smul_of_det_pos
  given: {g : GL (Fin 2) Real} (hg : 0 < g.det.val) (z : ℍ)
  proof: by
  change smulAux' g z = _
  rw [smulAux']; rw [σ]; rw [if_pos hg]; rw [ContinuousAlgEquiv.refl_apply]; rw [num]; rw [denom]

中文:
引理 coe_smul_of_det_pos
  条件: {g : GL (有限集 2) 实数} (hg : 0 < g.det.val) (z : ℍ)
  证明: by
  change smulAux' g z = _
  rw [smulAux']; rw [σ]; rw [if_pos hg]; rw [ContinuousAlgEquiv.refl_apply]; rw [num]; rw [denom]

Depends on / 依赖: ContinuousAlgEquiv, ContinuousAlgEquiv.refl_apply, if_pos, refl_apply, smulAux
-/
lemma coe_smul_of_det_pos {g : GL (Fin 2) Real} (hg : 0 < g.det.val) (z : ℍ) :
    ↑(g • z) = num g z / denom g z := by
  change smulAux' g z = _
  rw [smulAux']; rw [σ]; rw [if_pos hg]; rw [ContinuousAlgEquiv.refl_apply]; rw [num]; rw [denom]

/--
lemma `denom_cocycle_σ` / 引理 `denom_cocycle_σ`

English:
lemma denom_cocycle_σ
  given: (g h : GL (Fin 2) Real) (z : ℍ)
  proof: denom_cocycle' g h z

中文:
引理 denom_cocycle_σ
  条件: (g h : GL (有限集 2) 实数) (z : ℍ)
  证明: denom_cocycle' g h z

Depends on / 依赖: denom_cocycle
-/
lemma denom_cocycle_σ (g h : GL (Fin 2) Real) (z : ℍ) :
    denom (g * h) z = σ h (denom g ↑(h • z)) * denom h z :=
  denom_cocycle' g h z

/--
lemma `glPos_smul_def` / 引理 `glPos_smul_def`

English:
lemma glPos_smul_def
  given: {g : GL (Fin 2) Real} (hg : 0 < g.det.val) (z : ℍ)
  proof: by
  ext; simp [coe_smul_of_det_pos hg]

中文:
引理 glPos_smul_def
  条件: {g : GL (有限集 2) 实数} (hg : 0 < g.det.val) (z : ℍ)
  证明: by
  ext; simp [coe_smul_of_det_pos hg]

Depends on / 依赖: coe_smul_of_det_pos
-/
lemma glPos_smul_def {g : GL (Fin 2) Real} (hg : 0 < g.det.val) (z : ℍ) :
    g • z = ⟨num g z / denom g z, coe_smul_of_det_pos hg z ▸ (g • z).im_pos⟩ := by
  ext; simp [coe_smul_of_det_pos hg]

section GLAction
variable (g : GL (Fin 2) Real) (z : ℍ)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `re_smul` / 定理 `re_smul`

English:
theorem re_smul
  statement: (g • z).re = (num g z / denom g z).re
  proof: by
  change (smulAux' g z).re = _
  simp +contextual [smulAux', σ, DFunLike.ite_apply, apply_ite, Complex.div_re]

中文:
定理 re_smul
  结论: (g • z).re = (num g z / denom g z).re
  证明: by
  change (smulAux' g z).re = _
  simp +contextual [smulAux', σ, DFunLike.ite_apply, apply_ite, Complex.div_re]

Depends on / 依赖: Complex.div_re, DFunLike, DFunLike.ite_apply, apply_ite, contextual, div_re, ite_apply, smulAux
-/
theorem re_smul : (g • z).re = (num g z / denom g z).re := by
  change (smulAux' g z).re = _
  simp +contextual [smulAux', σ, DFunLike.ite_apply, apply_ite, Complex.div_re]

/--
theorem `im_smul` / 定理 `im_smul`

English:
theorem im_smul
  statement: (g • z).im = |(num g z / denom g z).im|
  proof: by
  change (smulAux' g z).im = _
  simp only [smulAux', σ, DFunLike.ite_apply, ContinuousAlgEquiv.refl_apply, apply_ite, moebius_im,
    Complex.conjCAE_apply, Complex.conj_im, ← neg_div, ← neg_mul, abs_div, abs_mul,
    abs_of_pos (show 0 < (z : Complex).im from z.coe_im ▸ z.im_pos),
abs_of_nonneg

中文:
定理 im_smul
  结论: (g • z).im = |(num g z / denom g z).im|
  证明: by
  change (smulAux' g z).im = _
  simp only [smulAux', σ, DFunLike.ite_apply, ContinuousAlgEquiv.refl_apply, apply_ite, moebius_im,
    Complex.conjCAE_apply, Complex.conj_im, ← neg_div, ← neg_mul, abs_div, abs_mul,
    abs_of_pos (show 0 < (z : Complex).im from z.coe_im ▸ z.im_pos),
abs_of_nonneg

Depends on / 依赖: Complex.conjCAE_apply, Complex.conj_im, Complex.normSq_nonneg, ContinuousAlgEquiv, ContinuousAlgEquiv.refl_apply, DFunLike, DFunLike.ite_apply, abs_div, abs_mul, abs_of_nonneg, abs_of_nonpos, abs_of_pos, apply_ite, coe_im, conjCAE_apply, conj_im, im_pos, ite_apply, moebius_im, neg_div
-/
theorem im_smul : (g • z).im = |(num g z / denom g z).im| := by
  change (smulAux' g z).im = _
  simp only [smulAux', σ, DFunLike.ite_apply, ContinuousAlgEquiv.refl_apply, apply_ite, moebius_im,
    Complex.conjCAE_apply, Complex.conj_im, ← neg_div, ← neg_mul, abs_div, abs_mul,
    abs_of_pos (show 0 < (z : Complex).im from z.coe_im ▸ z.im_pos),
abs_of_nonneg Complex.normSq_nonneg _]
  split_ifs with h <;> [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]]

/--
lemma `im_smul_eq_div_normSq` / 引理 `im_smul_eq_div_normSq`

English:
lemma im_smul_eq_div_normSq
  statement: (g • z).im = |g.det.val| * z.im / Complex.normSq (denom g z)
  proof: smulAux'_im g z

中文:
引理 im_smul_eq_div_normSq
  结论: (g • z).im = |g.det.val| * z.im / 复形.normSq (denom g z)
  证明: smulAux'_im g z

Depends on / 依赖: smulAux
-/
lemma im_smul_eq_div_normSq : (g • z).im = |g.det.val| * z.im / Complex.normSq (denom g z) :=
  smulAux'_im g z

/--
theorem `c_mul_im_sq_le_normSq_denom` / 定理 `c_mul_im_sq_le_normSq_denom`

English:
theorem c_mul_im_sq_le_normSq_denom
  statement: (g 1 0 * z.im) ^ 2 <= Complex.normSq (denom g z)
  proof: by
  set c := g 1 0
  set d := g 1 1
  calc
    (c * z.im) ^ 2 <= (c * z.im) ^ 2 + (c * z.re + d) ^ 2 := by nlinarith
    _ = Complex.normSq (denom g z) := by simp [denom, Complex.normSq]; ring

@[simp]

中文:
定理 c_mul_im_sq_le_normSq_denom
  结论: (g 1 0 * z.im) ^ 2 <= 复形.normSq (denom g z)
  证明: by
  set c := g 1 0
  set d := g 1 1
  calc
    (c * z.im) ^ 2 <= (c * z.im) ^ 2 + (c * z.re + d) ^ 2 := by nlinarith
    _ = Complex.normSq (denom g z) := by simp [denom, Complex.normSq]; ring

@[simp]

Depends on / 依赖: Complex.normSq, normSq, z.im, z.re
-/
theorem c_mul_im_sq_le_normSq_denom : (g 1 0 * z.im) ^ 2 <= Complex.normSq (denom g z) := by
  set c := g 1 0
  set d := g 1 1
  calc
    (c * z.im) ^ 2 <= (c * z.im) ^ 2 + (c * z.re + d) ^ 2 := by nlinarith
    _ = Complex.normSq (denom g z) := by simp [denom, Complex.normSq]; ring

@[simp]
/--
theorem `neg_smul` / 定理 `neg_smul`

English:
theorem neg_smul
  statement: -g • z = g • z
  proof: by
  ext1
  simp [coe_smul]

@[simp]

中文:
定理 neg_smul
  结论: -g • z = g • z
  证明: by
  ext1
  simp [coe_smul]

@[simp]

Depends on / 依赖: coe_smul
-/
theorem neg_smul : -g • z = g • z := by
  ext1
  simp [coe_smul]

@[simp]
/--
lemma `num_one` / 引理 `num_one`

English:
lemma num_one
  statement: num 1 z = z
  proof: by simp [num]

@[simp]

中文:
引理 num_one
  结论: num 1 z = z
  证明: by simp [num]

@[simp]
-/
lemma num_one : num 1 z = z := by simp [num]

@[simp]
/--
lemma `denom_one` / 引理 `denom_one`

English:
lemma denom_one
  statement: denom 1 z = 1
  proof: by
  simp [denom]

@[simp]

中文:
引理 denom_one
  结论: denom 1 z = 1
  证明: by
  simp [denom]

@[simp]
-/
lemma denom_one : denom 1 z = 1 := by
  simp [denom]

@[simp]
/--
theorem `num_scalar` / 定理 `num_scalar`

English:
theorem num_scalar
  given: (u : Realˣ) (z : ℍ)
  statement: num (.scalar (Fin 2) u) z = u * z
  proof: by
  simp [num]

@[simp]

中文:
定理 num_scalar
  条件: (u : 实数ˣ) (z : ℍ)
  结论: num (.scalar (有限集 2) u) z = u * z
  证明: by
  simp [num]

@[simp]
-/
theorem num_scalar (u : Realˣ) (z : ℍ) : num (.scalar (Fin 2) u) z = u * z := by
  simp [num]

@[simp]
/--
theorem `denom_scalar` / 定理 `denom_scalar`

English:
theorem denom_scalar
  given: (u : Realˣ) (z : ℍ)
  statement: denom (.scalar (Fin 2) u) z = u
  proof: by
  simp [denom]

@[simp]

中文:
定理 denom_scalar
  条件: (u : 实数ˣ) (z : ℍ)
  结论: denom (.scalar (有限集 2) u) z = u
  证明: by
  simp [denom]

@[simp]
-/
theorem denom_scalar (u : Realˣ) (z : ℍ) : denom (.scalar (Fin 2) u) z = u := by
  simp [denom]

@[simp]
/--
theorem `glScalar_smul` / 定理 `glScalar_smul`

English:
theorem glScalar_smul
  given: (u : Realˣ) (z : ℍ)
  proof: by
  rw [glPos_smul_def]
  · simp
  · simp [sq_pos_iff]

中文:
定理 glScalar_smul
  条件: (u : 实数ˣ) (z : ℍ)
  证明: by
  rw [glPos_smul_def]
  · simp
  · simp [sq_pos_iff]

Depends on / 依赖: glPos_smul_def, sq_pos_iff
-/
theorem glScalar_smul (u : Realˣ) (z : ℍ) :
    GeneralLinearGroup.scalar (Fin 2) u • z = z := by
  rw [glPos_smul_def]
  · simp
  · simp [sq_pos_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction.IsPretransitive (GL (Fin 2) Real) ℍ
  body: by
    set m : Matrix (Fin 2) (Fin 2) Real := !![w.im, z.im * w.re - w.im * z.re; 0, z.im]
refine ⟨.mkOfDetNeZero m by simp [m, im_ne_zero], ?_⟩
    ext
    simp [coe_smul_of_det_pos, im_pos, num, denom, m, Complex.ext_iff, im_ne_zero]

中文:
实例 :
  签名: 乘法作用.是Pretransitive (GL (有限集 2) 实数) ℍ
  定义体: by
    set m : Matrix (Fin 2) (Fin 2) Real := !![w.im, z.im * w.re - w.im * z.re; 0, z.im]
refine ⟨.mkOfDetNeZero m by simp [m, im_ne_zero], ?_⟩
    ext
    simp [coe_smul_of_det_pos, im_pos, num, denom, m, Complex.ext_iff, im_ne_zero]

Depends on / 依赖: Complex.ext_iff, Matrix, coe_smul_of_det_pos, ext_iff, im_ne_zero, im_pos, mkOfDetNeZero, w.im, w.re, z.im, z.re
-/
instance : MulAction.IsPretransitive (GL (Fin 2) Real) ℍ where
  exists_smul_eq z w := by
    set m : Matrix (Fin 2) (Fin 2) Real := !![w.im, z.im * w.re - w.im * z.re; 0, z.im]
refine ⟨.mkOfDetNeZero m by simp [m, im_ne_zero], ?_⟩
    ext
    simp [coe_smul_of_det_pos, im_pos, num, denom, m, Complex.ext_iff, im_ne_zero]

end GLAction

section PGLAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction PGL(2, Real) ℍ
  body: Matrix.ProjGenLinGroup.mulActionOfGL glScalar_smul

@[simp]

中文:
实例 :
  签名: 乘法作用 PGL(2, 实数) ℍ
  定义体: Matrix.ProjGenLinGroup.mulActionOfGL glScalar_smul

@[simp]

Depends on / 依赖: Matrix, Matrix.ProjGenLinGroup.mulActionOfGL, ProjGenLinGroup, glScalar_smul, mulActionOfGL
-/
instance : MulAction PGL(2, Real) ℍ :=
  Matrix.ProjGenLinGroup.mulActionOfGL glScalar_smul

@[simp]
/--
theorem `pglMk_smul` / 定理 `pglMk_smul`

English:
theorem pglMk_smul
  given: (g : GL (Fin 2) Real) (z : ℍ)
  proof: ProjGenLinGroup.mk_smul ..

中文:
定理 pglMk_smul
  条件: (g : GL (有限集 2) 实数) (z : ℍ)
  证明: ProjGenLinGroup.mk_smul ..

Depends on / 依赖: ProjGenLinGroup, ProjGenLinGroup.mk_smul, mk_smul
-/
theorem pglMk_smul (g : GL (Fin 2) Real) (z : ℍ) :
    ProjGenLinGroup.mk g • z = g • z :=
  ProjGenLinGroup.mk_smul ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction.IsPretransitive PGL(2, Real) ℍ
  body: .of_smul_eq .mk pglMk_smul _ _

中文:
实例 :
  签名: 乘法作用.是Pretransitive PGL(2, 实数) ℍ
  定义体: .of_smul_eq .mk pglMk_smul _ _

Depends on / 依赖: of_smul_eq, pglMk_smul
-/
instance : MulAction.IsPretransitive PGL(2, Real) ℍ :=
.of_smul_eq .mk pglMk_smul _ _

end PGLAction

section SLAction

/--
Instance `SLAction` / 实例 `SLAction`

English:
instance SLAction
  signature: {R : Type*} [CommRing R] [Algebra R Real]
  body: MulAction.compHom ℍ SpecialLinearGroup.mapGL Real

中文:
实例 SLAction
  签名: {R : 类型} [交换环 R] [代数 R 实数]
  定义体: MulAction.compHom ℍ SpecialLinearGroup.mapGL Real

Depends on / 依赖: MulAction, MulAction.compHom, SpecialLinearGroup, SpecialLinearGroup.mapGL, compHom
-/
noncomputable instance SLAction {R : Type*} [CommRing R] [Algebra R Real] : MulAction SL(2, R) ℍ :=
MulAction.compHom ℍ SpecialLinearGroup.mapGL Real

/--
theorem `coe_specialLinearGroup_apply` / 定理 `coe_specialLinearGroup_apply`

English:
theorem coe_specialLinearGroup_apply
  given: {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ)
  proof: by
  rw [MulAction.compHom_smul_def]; rw [coe_smul_of_det_pos (by simp)]
  rfl

中文:
定理 coe_specialLinearGroup_apply
  条件: {R : 类型} [交换环 R] [代数 R 实数] (g : SL(2, R)) (z : ℍ)
  证明: by
  rw [MulAction.compHom_smul_def]; rw [coe_smul_of_det_pos (by simp)]
  rfl

Depends on / 依赖: MulAction, MulAction.compHom_smul_def, coe_smul_of_det_pos, compHom_smul_def
-/
theorem coe_specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) :
    ↑(g • z) =
      (((algebraMap R Real (g 0 0) : Complex) * z + (algebraMap R Real (g 0 1) : Complex)) /
      ((algebraMap R Real (g 1 0) : Complex) * z + (algebraMap R Real (g 1 1) : Complex))) := by
  rw [MulAction.compHom_smul_def]; rw [coe_smul_of_det_pos (by simp)]
  rfl

/--
theorem `specialLinearGroup_apply` / 定理 `specialLinearGroup_apply`

English:
theorem specialLinearGroup_apply
  given: {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ)
  proof: by
  ext; simp [coe_specialLinearGroup_apply]

中文:
定理 specialLinearGroup_apply
  条件: {R : 类型} [交换环 R] [代数 R 实数] (g : SL(2, R)) (z : ℍ)
  证明: by
  ext; simp [coe_specialLinearGroup_apply]

Depends on / 依赖: coe_specialLinearGroup_apply
-/
theorem specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) :
    g • z = mk
      (((algebraMap R Real (g 0 0) : Complex) * z + (algebraMap R Real (g 0 1) : Complex)) /
      ((algebraMap R Real (g 1 0) : Complex) * z + (algebraMap R Real (g 1 1) : Complex)))
      (coe_specialLinearGroup_apply g z ▸ (g • z).im_pos) := by
  ext; simp [coe_specialLinearGroup_apply]


/--
theorem `modular_S_smul` / 定理 `modular_S_smul`

English:
theorem modular_S_smul
  given: (z : ℍ)
  proof: by
  rw [specialLinearGroup_apply]
  simp [ModularGroup.S, neg_div, inv_neg]

中文:
定理 modular_S_smul
  条件: (z : ℍ)
  证明: by
  rw [specialLinearGroup_apply]
  simp [ModularGroup.S, neg_div, inv_neg]

Depends on / 依赖: ModularGroup, ModularGroup.S, inv_neg, neg_div, specialLinearGroup_apply
-/
theorem modular_S_smul (z : ℍ) :
    ModularGroup.S • z = mk (-z : Complex)⁻¹ z.im_inv_neg_coe_pos := by
  rw [specialLinearGroup_apply]
  simp [ModularGroup.S, neg_div, inv_neg]

/--
theorem `modular_T_zpow_smul` / 定理 `modular_T_zpow_smul`

English:
theorem modular_T_zpow_smul
  given: (z : ℍ) (n : Int)
  statement: ModularGroup.T ^ n • z = (n : Real) +ᵥ z
  proof: by
  rw [UpperHalfPlane.ext_iff]; rw [coe_vadd]; rw [add_comm]; rw [coe_specialLinearGroup_apply]
  simp [ModularGroup.coe_T_zpow,
    of_apply, cons_val_zero, Complex.ofReal_one, one_mul, cons_val_one,
    zero_mul, zero_add, div_one]

中文:
定理 modular_T_zpow_smul
  条件: (z : ℍ) (n : 整数)
  结论: ModularGroup.T ^ n • z = (n : 实数) +ᵥ z
  证明: by
  rw [UpperHalfPlane.ext_iff]; rw [coe_vadd]; rw [add_comm]; rw [coe_specialLinearGroup_apply]
  simp [ModularGroup.coe_T_zpow,
    of_apply, cons_val_zero, Complex.ofReal_one, one_mul, cons_val_one,
    zero_mul, zero_add, div_one]

Depends on / 依赖: Complex.ofReal_one, ModularGroup, ModularGroup.coe_T_zpow, UpperHalfPlane, UpperHalfPlane.ext_iff, add_comm, coe_T_zpow, coe_specialLinearGroup_apply, coe_vadd, cons_val_one, cons_val_zero, div_one, ext_iff, ofReal_one, of_apply, one_mul, zero_add, zero_mul
-/
theorem modular_T_zpow_smul (z : ℍ) (n : Int) : ModularGroup.T ^ n • z = (n : Real) +ᵥ z := by
  rw [UpperHalfPlane.ext_iff]; rw [coe_vadd]; rw [add_comm]; rw [coe_specialLinearGroup_apply]
  simp [ModularGroup.coe_T_zpow,
    of_apply, cons_val_zero, Complex.ofReal_one, one_mul, cons_val_one,
    zero_mul, zero_add, div_one]

/--
theorem `modular_T_smul` / 定理 `modular_T_smul`

English:
theorem modular_T_smul
  given: (z : ℍ)
  statement: ModularGroup.T • z = (1 : Real) +ᵥ z
  proof: by
  simpa only [zpow_one, Int.cast_one] using modular_T_zpow_smul z 1

中文:
定理 modular_T_smul
  条件: (z : ℍ)
  结论: ModularGroup.T • z = (1 : 实数) +ᵥ z
  证明: by
  simpa only [zpow_one, Int.cast_one] using modular_T_zpow_smul z 1

Depends on / 依赖: Int.cast_one, cast_one, modular_T_zpow_smul, zpow_one
-/
theorem modular_T_smul (z : ℍ) : ModularGroup.T • z = (1 : Real) +ᵥ z := by
  simpa only [zpow_one, Int.cast_one] using modular_T_zpow_smul z 1

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_SL2_smul_eq_of_apply_zero_one_eq_zero` / 定理 `exists_SL2_smul_eq_of_apply_zero_one_eq_zero`

English:
theorem exists_SL2_smul_eq_of_apply_zero_one_eq_zero
  given: (g : SL(2, Real)) (hc : g 1 0 = 0)
  proof: by
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
  refine ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices ↑a * z * a + b * a = b * a + a * a * z by simpa [specialLinearGroup_apply, add_mul]
  ring

中文:
定理 存在_SL2_smul_eq_of_apply_zero_one_eq_zero
  条件: (g : SL(2, 实数)) (hc : g 1 0 = 0)
  证明: by
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
  refine ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices ↑a * z * a + b * a = b * a + a * a * z by simpa [specialLinearGroup_apply, add_mul]
  ring

Depends on / 依赖: add_mul, fin_two_exists_eq_mk_of_apply_zero_one_eq_zero, g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero, mul_self_pos, mul_self_pos.mpr, specialLinearGroup_apply
-/
theorem exists_SL2_smul_eq_of_apply_zero_one_eq_zero (g : SL(2, Real)) (hc : g 1 0 = 0) :
    exists (u : { x : Real // 0 < x }) (v : Real), (g • · : ℍ -> ℍ) = (v +ᵥ ·) ∘ (u • ·) := by
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
  refine ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices ↑a * z * a + b * a = b * a + a * a * z by simpa [specialLinearGroup_apply, add_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_SL2_smul_eq_of_apply_zero_one_ne_zero` / 定理 `exists_SL2_smul_eq_of_apply_zero_one_ne_zero`

English:
theorem exists_SL2_smul_eq_of_apply_zero_one_ne_zero
  given: (g : SL(2, Real)) (hc : g 1 0 != 0)
  proof: by
  have h_denom (z : ℍ) := denom_ne_zero g z
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | _ a b c d h => ?_
  replace hc : c != 0 := by simpa using! hc
  refine ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices (↑a * z + b) / (↑c * z + d) = a / 

中文:
定理 存在_SL2_smul_eq_of_apply_zero_one_ne_zero
  条件: (g : SL(2, 实数)) (hc : g 1 0 != 0)
  证明: by
  have h_denom (z : ℍ) := denom_ne_zero g z
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | _ a b c d h => ?_
  replace hc : c != 0 := by simpa using! hc
  refine ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices (↑a * z + b) / (↑c * z + d) = a / 

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup.fin_two_induction, SpecialLinearGroup, coe_specialLinearGroup_apply, denom_ne_zero, fin_two_induction, h_denom, modular_S_smul, mul_self_pos, mul_self_pos.mpr, replace
-/
theorem exists_SL2_smul_eq_of_apply_zero_one_ne_zero (g : SL(2, Real)) (hc : g 1 0 != 0) :
    exists (u : { x : Real // 0 < x }) (v w : Real),
      (g • · : ℍ -> ℍ) =
        (w +ᵥ ·) ∘ (ModularGroup.S • · : ℍ -> ℍ) ∘ (v +ᵥ · : ℍ -> ℍ) ∘ (u • · : ℍ -> ℍ) := by
  have h_denom (z : ℍ) := denom_ne_zero g z
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | _ a b c d h => ?_
  replace hc : c != 0 := by simpa using! hc
  refine ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices (↑a * z + b) / (↑c * z + d) = a / c - (c * d + ↑c * ↑c * z)⁻¹ by
    simpa [modular_S_smul, coe_specialLinearGroup_apply]
  replace hc : (c : Complex) != 0 := by norm_cast
  replace h_denom : ↑c * z + d != 0 := by simpa using! h_denom ⟨z, hz⟩
  replace h : (a * d - b * c : Complex) = (1 : Complex) := by norm_cast
  grind

end SLAction

section toSL2R

/--
Definition of `toSL2R` / `toSL2R` 的定义

English:
definition toSL2R
  signature: (z : ℍ)
  body: ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩

中文:
定义 toSL2R
  签名: (z : ℍ)
  定义体: ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩

Depends on / 依赖: Real.sqrt_ne_zero, im_pos, sqrt_ne_zero, z.im, z.im_pos, z.re
-/
noncomputable def toSL2R (z : ℍ) : SL(2, Real) :=
  ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩

/--
lemma `toSL2R_apply` / 引理 `toSL2R_apply`

English:
lemma toSL2R_apply
  given: (z : ℍ)
  statement: z.toSL2R =
  proof: (rfl)

中文:
引理 toSL2R_apply
  条件: (z : ℍ)
  结论: z.toSL2R =
  证明: (rfl)
-/
lemma toSL2R_apply (z : ℍ) : z.toSL2R =
  ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩ := (rfl)

/--
lemma `coe_toSL2R` / 引理 `coe_toSL2R`

English:
lemma coe_toSL2R
  given: (z : ℍ)
  statement: z.toSL2R = !![√z.im, z.re / √z.im; 0, 1 / √z.im]
  proof: (rfl)

中文:
引理 coe_toSL2R
  条件: (z : ℍ)
  结论: z.toSL2R = !![√z.im, z.re / √z.im; 0, 1 / √z.im]
  证明: (rfl)
-/
@[simp] lemma coe_toSL2R (z : ℍ) : z.toSL2R = !![√z.im, z.re / √z.im; 0, 1 / √z.im] := (rfl)

/--
lemma `toSL2R_smul_I` / 引理 `toSL2R_smul_I`

English:
lemma toSL2R_smul_I
  given: (z : ℍ)
  statement: z.toSL2R • I = z
  proof: by
  have : √z.im != (0 : Complex) := by simpa [Real.sqrt_ne_zero'] using z.im_pos
  ext
  suffices z.re / √z.im + √z.im * Complex.I = z * (↑√z.im)⁻¹ by
    rw [coe_specialLinearGroup_apply]; rw [div_eq_iff (mod_cast denom_ne_zero z.toSL2R I)]
    simpa [add_comm]
  rw [div_add' (hc := this)]; rw [m

中文:
引理 toSL2R_smul_I
  条件: (z : ℍ)
  结论: z.toSL2R • I = z
  证明: by
  have : √z.im != (0 : Complex) := by simpa [Real.sqrt_ne_zero'] using z.im_pos
  ext
  suffices z.re / √z.im + √z.im * Complex.I = z * (↑√z.im)⁻¹ by
    rw [coe_specialLinearGroup_apply]; rw [div_eq_iff (mod_cast denom_ne_zero z.toSL2R I)]
    simpa [add_comm]
  rw [div_add' (hc := this)]; rw [m
-/
@[simp] lemma toSL2R_smul_I (z : ℍ) : z.toSL2R • I = z := by
  have : √z.im != (0 : Complex) := by simpa [Real.sqrt_ne_zero'] using z.im_pos
  ext
  suffices z.re / √z.im + √z.im * Complex.I = z * (↑√z.im)⁻¹ by
    rw [coe_specialLinearGroup_apply]; rw [div_eq_iff (mod_cast denom_ne_zero z.toSL2R I)]
    simpa [add_comm]
  rw [div_add' (hc := this)]; rw [mul_right_comm]; rw [← Complex.ofReal_mul]; rw [← Real.sqrt_mul z.im_pos.le]; rw [Real.sqrt_mul_self z.im_pos.le]; rw [re_add_im]; rw [div_eq_mul_inv]

/--
Instance `isPretransitiveSL2R` / 实例 `isPretransitiveSL2R`

English:
instance isPretransitiveSL2R
  signature: : MulAction.IsPretransitive SL(2, Real) ℍ
  body: .of_orbit fun z => ⟨_, toSL2R_smul_I z⟩

中文:
实例 isPretransitiveSL2R
  签名: : 乘法作用.是Pretransitive SL(2, 实数) ℍ
  定义体: .of_orbit fun z => ⟨_, toSL2R_smul_I z⟩

Depends on / 依赖: of_orbit, toSL2R_smul_I
-/
instance isPretransitiveSL2R : MulAction.IsPretransitive SL(2, Real) ℍ :=
  .of_orbit fun z => ⟨_, toSL2R_smul_I z⟩

/--
Instance `isPretransitiveGL2R` / 实例 `isPretransitiveGL2R`

English:
instance isPretransitiveGL2R
  signature: : MulAction.IsPretransitive (GL (Fin 2) Real) ℍ
  body: .of_smul_eq ((↑) : SL(2, Real) -> _) fun {g z} => (MulAction.compHom_smul_def _ g z).symm

中文:
实例 isPretransitiveGL2R
  签名: : 乘法作用.是Pretransitive (GL (有限集 2) 实数) ℍ
  定义体: .of_smul_eq ((↑) : SL(2, Real) -> _) fun {g z} => (MulAction.compHom_smul_def _ g z).symm

Depends on / 依赖: MulAction, MulAction.compHom_smul_def, compHom_smul_def, of_smul_eq
-/
instance isPretransitiveGL2R : MulAction.IsPretransitive (GL (Fin 2) Real) ℍ :=
  .of_smul_eq ((↑) : SL(2, Real) -> _) fun {g z} => (MulAction.compHom_smul_def _ g z).symm

end toSL2R

section J

/--
Definition of `J` / `J` 的定义

English:
definition J
  signature: : GL (Fin 2) Real
  body: .mkOfDetNeZero !![-1, 0; 0, 1] (by simp)

中文:
定义 J
  签名: : GL (有限集 2) 实数
  定义体: .mkOfDetNeZero !![-1, 0; 0, 1] (by simp)

Depends on / 依赖: mkOfDetNeZero
-/
def J : GL (Fin 2) Real := .mkOfDetNeZero !![-1, 0; 0, 1] (by simp)

/--
lemma `coe_J_smul` / 引理 `coe_J_smul`

English:
lemma coe_J_smul
  given: (τ : ℍ)
  statement: (↑(J • τ) : Complex) = -conj ↑τ
  proof: by
  simp [UpperHalfPlane.coe_smul, σ, J, show ¬(1 : Real) < 0 by simp, num, denom]

中文:
引理 coe_J_smul
  条件: (τ : ℍ)
  结论: (↑(J • τ) : 复形) = -conj ↑τ
  证明: by
  simp [UpperHalfPlane.coe_smul, σ, J, show ¬(1 : Real) < 0 by simp, num, denom]

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.coe_smul, coe_smul
-/
lemma coe_J_smul (τ : ℍ) : (↑(J • τ) : Complex) = -conj ↑τ := by
  simp [UpperHalfPlane.coe_smul, σ, J, show ¬(1 : Real) < 0 by simp, num, denom]

/--
lemma `val_J` / 引理 `val_J`

English:
lemma val_J
  statement: J.val = !![-1, 0; 0, 1]
  proof: rfl

中文:
引理 val_J
  结论: J.val = !![-1, 0; 0, 1]
  证明: rfl
-/
@[simp] lemma val_J : J.val = !![-1, 0; 0, 1] := rfl

/--
lemma `J_sq` / 引理 `J_sq`

English:
lemma J_sq
  statement: J ^ 2 = 1
  proof: by ext; simp [J, sq, Matrix.one_fin_two]

中文:
引理 J_sq
  结论: J ^ 2 = 1
  证明: by ext; simp [J, sq, Matrix.one_fin_two]
-/
@[simp] lemma J_sq : J ^ 2 = 1 := by ext; simp [J, sq, Matrix.one_fin_two]

/--
lemma `det_J` / 引理 `det_J`

English:
lemma det_J
  statement: J.det = -1
  proof: by ext; simp [J]

中文:
引理 det_J
  结论: J.det = -1
  证明: by ext; simp [J]
-/
@[simp] lemma det_J : J.det = -1 := by ext; simp [J]

/--
lemma `sigma_J` / 引理 `sigma_J`

English:
lemma sigma_J
  statement: σ J = Complex.conjCAE
  proof: by simp [σ, J]

中文:
引理 sigma_J
  结论: σ J = 复形.conjCAE
  证明: by simp [σ, J]
-/
@[simp] lemma sigma_J : σ J = Complex.conjCAE := by simp [σ, J]

/--
lemma `denom_J` / 引理 `denom_J`

English:
lemma denom_J
  given: (τ : Complex)
  statement: denom J τ = 1
  proof: by simp [J, denom]

@[simp]

中文:
引理 denom_J
  条件: (τ : 复形)
  结论: denom J τ = 1
  证明: by simp [J, denom]

@[simp]
-/
@[simp] lemma denom_J (τ : Complex) : denom J τ = 1 := by simp [J, denom]

@[simp]
/--
lemma `denom_J_mul` / 引理 `denom_J_mul`

English:
lemma denom_J_mul
  given: (g : GL (Fin 2) Real) (τ : Complex)
  statement: denom (J * g) τ = denom g τ
  proof: by
  simp [denom, vecMul, vecHead, vecTail]

中文:
引理 denom_J_mul
  条件: (g : GL (有限集 2) 实数) (τ : 复形)
  结论: denom (J * g) τ = denom g τ
  证明: by
  simp [denom, vecMul, vecHead, vecTail]

Depends on / 依赖: vecHead, vecMul, vecTail
-/
lemma denom_J_mul (g : GL (Fin 2) Real) (τ : Complex) : denom (J * g) τ = denom g τ := by
  simp [denom, vecMul, vecHead, vecTail]

end J

end UpperHalfPlane

namespace ModularGroup -- results specific to `SL(2, ℤ)`
-- TODO: Move these elsewhere, maybe somewhere in the algebra or number theory hierarchies?

section ModularScalarTowers

/-- Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`. -/
@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
Definition of `coe` / `coe` 的定义

English:
definition coe
  signature: (g : SL(2, Int))
  body: ((g : SL(2, Real)) : GL(2, Real)⁺)

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]

中文:
定义 coe
  签名: (g : SL(2, 整数))
  定义体: ((g : SL(2, Real)) : GL(2, Real)⁺)

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
-/
def coe (g : SL(2, Int)) : GL(2, Real)⁺ := ((g : SL(2, Real)) : GL(2, Real)⁺)

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  given: (a b : SL(2, Int))
  statement: coe a = coe b ↔ a = b
  proof: by
  refine ⟨fun h => a.ext b fun i j => ?_, congr_arg _⟩
  simp only [Subtype.ext_iff, GeneralLinearGroup.ext_iff] at h
  simpa [coe] using h i j

中文:
引理 coe_inj
  条件: (a b : SL(2, 整数))
  结论: coe a = coe b ↔ a = b
  证明: by
  refine ⟨fun h => a.ext b fun i j => ?_, congr_arg _⟩
  simp only [Subtype.ext_iff, GeneralLinearGroup.ext_iff] at h
  simpa [coe] using h i j

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.ext_iff, Subtype, Subtype.ext_iff, a.ext, congr_arg, ext_iff
-/
lemma coe_inj (a b : SL(2, Int)) : coe a = coe b ↔ a = b := by
  refine ⟨fun h => a.ext b fun i j => ?_, congr_arg _⟩
  simp only [Subtype.ext_iff, GeneralLinearGroup.ext_iff] at h
  simpa [coe] using h i j

/-- Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`, bundled as a group hom. -/
@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
Definition of `coeHom` / `coeHom` 的定义

English:
definition coeHom
  signature: : SL(2, Int) ->* GL(2, Real)⁺
  body: toGLPos.comp map Int.castRingHom _

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]

中文:
定义 coeHom
  签名: : SL(2, 整数) ->* GL(2, 实数)⁺
  定义体: toGLPos.comp map Int.castRingHom _

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]

Depends on / 依赖: Int.castRingHom, castRingHom, toGLPos, toGLPos.comp
-/
def coeHom : SL(2, Int) ->* GL(2, Real)⁺ := toGLPos.comp map Int.castRingHom _

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
lemma `coeHom_apply` / 引理 `coeHom_apply`

English:
lemma coeHom_apply
  given: (g : SL(2, Int))
  statement: coeHom g = coe g
  proof: rfl

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]

中文:
引理 coeHom_apply
  条件: (g : SL(2, 整数))
  结论: coeHom g = coe g
  证明: rfl

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
-/
lemma coeHom_apply (g : SL(2, Int)) : coeHom g = coe g := rfl

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
theorem `coe_apply_complex` / 定理 `coe_apply_complex`

English:
theorem coe_apply_complex
  given: {g : SL(2, Int)} {i j : Fin 2}
  proof: rfl

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]

中文:
定理 coe_apply_complex
  条件: {g : SL(2, 整数)} {i j : 有限集 2}
  证明: rfl

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
-/
theorem coe_apply_complex {g : SL(2, Int)} {i j : Fin 2} :
    (Units.val <| Subtype.val <| coe g) i j = (Subtype.val g i j : Complex) :=
  rfl

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
theorem `det_coe` / 定理 `det_coe`

English:
theorem det_coe
  given: {g : SL(2, Int)}
  statement: det (Units.val <| Subtype.val <| coe g) = 1
  proof: by
  simp only [SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, SpecialLinearGroup.det_coe, coe]

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]

中文:
定理 det_coe
  条件: {g : SL(2, 整数)}
  结论: det (单位群.val <| 子类型.val <| coe g) = 1
  证明: by
  simp only [SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, SpecialLinearGroup.det_coe, coe]

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]

Depends on / 依赖: SpecialLinearGroup, SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, SpecialLinearGroup.det_coe, coe_GLPos_coe_GL_coe_matrix, det_coe
-/
theorem det_coe {g : SL(2, Int)} : det (Units.val <| Subtype.val <| coe g) = 1 := by
  simp only [SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, SpecialLinearGroup.det_coe, coe]

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: coe 1 = 1
  proof: by
  simp only [coe, map_one]

中文:
引理 coe_one
  结论: coe 1 = 1
  证明: by
  simp only [coe, map_one]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, IsSelfAdjoint, IsSelfAdjoint.star_mul_self, adjoint, ext_iff, h.one_sub, isStarNormal_iff, isStarNormal_iff_norm_eq_adjoint, isStarNormal_iff_norm_eq_adjoint.mp, map_one, norm_eq_zero, one_def, one_sub, simp_rw, star_eq_adjoint, star_mul_self, sub_eq_zero, zero_apply
-/
lemma coe_one : coe 1 = 1 := by
  simp only [coe, map_one]

/-- Multiplication action of `SL(2, ℤ)` on `GL(2, ℝ)⁺`. -/
@[reducible, deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
Definition of `SLOnGLPos` / `SLOnGLPos` 的定义

English:
definition SLOnGLPos
  signature: : SMul SL(2, Int) GL(2, Real)⁺
  body: ⟨fun s g => s * g⟩

中文:
定义 SLOnGLPos
  签名: : 标量乘法 SL(2, 整数) GL(2, 实数)⁺
  定义体: ⟨fun s g => s * g⟩
-/
def SLOnGLPos : SMul SL(2, Int) GL(2, Real)⁺ :=
  ⟨fun s g => s * g⟩

attribute [local instance] SLOnGLPos

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
theorem `SLOnGLPos_smul_apply` / 定理 `SLOnGLPos_smul_apply`

English:
theorem SLOnGLPos_smul_apply
  given: (s : SL(2, Int)) (g : GL(2, Real)⁺) (z : ℍ)
  proof: rfl

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]

中文:
定理 SLOnGLPos_smul_apply
  条件: (s : SL(2, 整数)) (g : GL(2, 实数)⁺) (z : ℍ)
  证明: rfl

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
-/
theorem SLOnGLPos_smul_apply (s : SL(2, Int)) (g : GL(2, Real)⁺) (z : ℍ) :
    (s • g) • z = ((s : GL(2, Real)⁺) * g) • z :=
  rfl

@[deprecated "use GL(2, Real)" (since := "2026-04-29")]
/--
lemma `SL_to_GL_tower` / 引理 `SL_to_GL_tower`

English:
lemma SL_to_GL_tower
  statement: IsScalarTower SL(2, Int) GL(2, Real)⁺ ℍ where
  proof: by
    simp only [SLOnGLPos_smul_apply]
    apply mul_smul'

中文:
引理 SL_to_GL_tower
  结论: 标量塔 SL(2, 整数) GL(2, 实数)⁺ ℍ where
  证明: by
    simp only [SLOnGLPos_smul_apply]
    apply mul_smul'

Depends on / 依赖: SLOnGLPos_smul_apply, mul_smul
-/
lemma SL_to_GL_tower : IsScalarTower SL(2, Int) GL(2, Real)⁺ ℍ where
  smul_assoc s g z := by
    simp only [SLOnGLPos_smul_apply]
    apply mul_smul'

end ModularScalarTowers

section SLModularAction

variable (g : SL(2, Int)) (z : ℍ)

@[simp]
/--
theorem `sl_moeb` / 定理 `sl_moeb`

English:
theorem sl_moeb
  statement: g • z = (g : GL (Fin 2) Real) • z
  proof: rfl

@[simp high]

中文:
定理 sl_moeb
  结论: g • z = (g : GL (有限集 2) 实数) • z
  证明: rfl

@[simp high]
-/
theorem sl_moeb : g • z = (g : GL (Fin 2) Real) • z := rfl

@[simp high]
/--
theorem `SL_neg_smul` / 定理 `SL_neg_smul`

English:
theorem SL_neg_smul
  statement: -g • z = g • z
  proof: by
  rw [sl_moeb]; rw [← z.neg_smul]
  congr 1 with i j
  simp [toGL]

中文:
定理 SL_neg_smul
  结论: -g • z = g • z
  证明: by
  rw [sl_moeb]; rw [← z.neg_smul]
  congr 1 with i j
  simp [toGL]

Depends on / 依赖: neg_smul, sl_moeb, z.neg_smul
-/
theorem SL_neg_smul : -g • z = g • z := by
  rw [sl_moeb]; rw [← z.neg_smul]
  congr 1 with i j
  simp [toGL]

/--
theorem `im_smul_eq_div_normSq` / 定理 `im_smul_eq_div_normSq`

English:
theorem im_smul_eq_div_normSq
  statement: (g • z).im = z.im / Complex.normSq (denom g z)
  proof: by
  simpa using z.im_smul_eq_div_normSq g

中文:
定理 im_smul_eq_div_normSq
  结论: (g • z).im = z.im / 复形.normSq (denom g z)
  证明: by
  simpa using z.im_smul_eq_div_normSq g

Depends on / 依赖: im_smul_eq_div_normSq, z.im_smul_eq_div_normSq
-/
theorem im_smul_eq_div_normSq : (g • z).im = z.im / Complex.normSq (denom g z) := by
  simpa using z.im_smul_eq_div_normSq g

/--
theorem `denom_apply` / 定理 `denom_apply`

English:
theorem denom_apply
  statement: denom g z = g 1 0 * z + g 1 1
  proof: rfl

中文:
定理 denom_apply
  结论: denom g z = g 1 0 * z + g 1 1
  证明: rfl
-/
theorem denom_apply : denom g z = g 1 0 * z + g 1 1 := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `denom_S` / 引理 `denom_S`

English:
lemma denom_S
  statement: denom S z = z
  proof: by simp [S, denom_apply]

中文:
引理 denom_S
  结论: denom S z = z
  证明: by simp [S, denom_apply]
-/
@[simp] lemma denom_S : denom S z = z := by simp [S, denom_apply]

end SLModularAction

end ModularGroup
