/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.PSeries
public import Mathlib.Order.Interval.Finset.Box
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Summability of Eisenstein series

We gather results about the summability of Eisenstein series, particularly
the summability of the Eisenstein series summands, which are used in the proof of the
boundedness of Eisenstein series at infinity.
-/

@[expose] public section
noncomputable section

open Complex UpperHalfPlane Set Finset Topology Filter Asymptotics

open scoped UpperHalfPlane Topology Nat

variable (z : ℍ)

namespace EisensteinSeries

/--
lemma `norm_eq_max_natAbs` / 引理 `norm_eq_max_natAbs`

English:
lemma norm_eq_max_natAbs
  given: (x : Fin 2 -> Int)
  statement: ‖x‖ = max (x 0).natAbs (x 1).natAbs
  proof: by
  rw [← coe_nnnorm]; rw [← NNReal.coe_natCast]; rw [NNReal.coe_inj]; rw [Nat.cast_max]
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [pi_nnnorm_le_iff, Fin.forall_fin_two, max_le_iff, NNReal.natCast_natAbs]

中文:
引理 norm_eq_max_natAbs
  条件: (x : 有限集 2 -> 整数)
  结论: ‖x‖ = 最大值 (x 0).natAbs (x 1).natAbs
  证明: by
  rw [← coe_nnnorm]; rw [← NNReal.coe_natCast]; rw [NNReal.coe_inj]; rw [Nat.cast_max]
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [pi_nnnorm_le_iff, Fin.forall_fin_two, max_le_iff, NNReal.natCast_natAbs]

Depends on / 依赖: Fin.forall_fin_two, NNReal, NNReal.coe_inj, NNReal.coe_natCast, NNReal.natCast_natAbs, Nat.cast_max, cast_max, coe_inj, coe_natCast, coe_nnnorm, eq_of_forall_ge_iff, forall_fin_two, max_le_iff, natCast_natAbs, pi_nnnorm_le_iff
-/
lemma norm_eq_max_natAbs (x : Fin 2 -> Int) : ‖x‖ = max (x 0).natAbs (x 1).natAbs := by
  rw [← coe_nnnorm]; rw [← NNReal.coe_natCast]; rw [NNReal.coe_inj]; rw [Nat.cast_max]
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [pi_nnnorm_le_iff, Fin.forall_fin_two, max_le_iff, NNReal.natCast_natAbs]

/--
lemma `norm_symm` / 引理 `norm_symm`

English:
lemma norm_symm
  given: (x y : Int)
  statement: ‖![x, y]‖ = ‖![y, x]‖
  proof: by
  simp [EisensteinSeries.norm_eq_max_natAbs, max_comm]

中文:
引理 norm_symm
  条件: (x y : 整数)
  结论: ‖![x, y]‖ = ‖![y, x]‖
  证明: by
  simp [EisensteinSeries.norm_eq_max_natAbs, max_comm]

Depends on / 依赖: EisensteinSeries, EisensteinSeries.norm_eq_max_natAbs, max_comm, norm_eq_max_natAbs
-/
lemma norm_symm (x y : Int) : ‖![x, y]‖ = ‖![y, x]‖ := by
  simp [EisensteinSeries.norm_eq_max_natAbs, max_comm]

/--
theorem `abs_le_left_of_norm` / 定理 `abs_le_left_of_norm`

English:
theorem abs_le_left_of_norm
  given: (m n : Int)
  statement: |n| <= ‖![n, m]‖
  proof: by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  left
  rw [Int.abs_eq_natAbs]
  exact le_refl _

中文:
定理 abs_le_left_of_norm
  条件: (m n : 整数)
  结论: |n| <= ‖![n, m]‖
  证明: by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  left
  rw [Int.abs_eq_natAbs]
  exact le_refl _

Depends on / 依赖: EisensteinSeries, EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Int.abs_eq_natAbs, Matrix, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_max, abs_eq_natAbs, cast_max, cons_val_fin_one, cons_val_one, cons_val_zero, isValue, le_refl, le_sup_iff, norm_eq_max_natAbs
-/
theorem abs_le_left_of_norm (m n : Int) : |n| <= ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  left
  rw [Int.abs_eq_natAbs]
  exact le_refl _

/--
theorem `abs_le_right_of_norm` / 定理 `abs_le_right_of_norm`

English:
theorem abs_le_right_of_norm
  given: (m n : Int)
  statement: |m| <= ‖![n, m]‖
  proof: by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  right
  rw [Int.abs_eq_natAbs]
  exact le_refl _

中文:
定理 abs_le_right_of_norm
  条件: (m n : 整数)
  结论: |m| <= ‖![n, m]‖
  证明: by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  right
  rw [Int.abs_eq_natAbs]
  exact le_refl _

Depends on / 依赖: EisensteinSeries, EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Int.abs_eq_natAbs, Matrix, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_max, abs_eq_natAbs, cast_max, cons_val_fin_one, cons_val_one, cons_val_zero, isValue, le_refl, le_sup_iff, norm_eq_max_natAbs
-/
theorem abs_le_right_of_norm (m n : Int) : |m| <= ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  right
  rw [Int.abs_eq_natAbs]
  exact le_refl _

/--
lemma `abs_norm_eq_max_natAbs` / 引理 `abs_norm_eq_max_natAbs`

English:
lemma abs_norm_eq_max_natAbs
  given: (n : Nat)
  statement: ‖![1, (n + 1 : Int)]‖ = n + 1
  proof: by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

中文:
引理 abs_norm_eq_max_natAbs
  条件: (n : 自然数)
  结论: ‖![1, (n + 1 : 整数)]‖ = n + 1
  证明: by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

Depends on / 依赖: EisensteinSeries, EisensteinSeries.norm_eq_max_natAbs, Matrix, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, cons_val_fin_one, cons_val_one, cons_val_zero, norm_eq_max_natAbs
-/
lemma abs_norm_eq_max_natAbs (n : Nat) : ‖![1, (n + 1 : Int)]‖ = n + 1 := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

/--
lemma `abs_norm_eq_max_natAbs_neg` / 引理 `abs_norm_eq_max_natAbs_neg`

English:
lemma abs_norm_eq_max_natAbs_neg
  given: (n : Nat)
  statement: ‖![1, -(n + 1 : Int)]‖ = n + 1
  proof: by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

中文:
引理 abs_norm_eq_max_natAbs_neg
  条件: (n : 自然数)
  结论: ‖![1, -(n + 1 : 整数)]‖ = n + 1
  证明: by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

Depends on / 依赖: EisensteinSeries, EisensteinSeries.norm_eq_max_natAbs, Matrix, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, cons_val_fin_one, cons_val_one, cons_val_zero, norm_eq_max_natAbs
-/
lemma abs_norm_eq_max_natAbs_neg (n : Nat) : ‖![1, -(n + 1 : Int)]‖ = n + 1 := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

section bounding_functions

/--
Definition of `r1` / `r1` 的定义

English:
definition r1
  signature: : Real
  body: z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)

中文:
定义 r1
  签名: : 实数
  定义体: z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)

Depends on / 依赖: z.im, z.re
-/
def r1 : Real := z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)

/--
lemma `r1_eq` / 引理 `r1_eq`

English:
lemma r1_eq
  statement: r1 z = 1 / ((z.re / z.im) ^ 2 + 1)
  proof: by
  rw [div_pow]; rw [div_add_one (by positivity)]; rw [one_div_div]; rw [r1]

中文:
引理 r1_eq
  结论: r1 z = 1 / ((z.re / z.im) ^ 2 + 1)
  证明: by
  rw [div_pow]; rw [div_add_one (by positivity)]; rw [one_div_div]; rw [r1]

Depends on / 依赖: div_add_one, div_pow, one_div_div
-/
lemma r1_eq : r1 z = 1 / ((z.re / z.im) ^ 2 + 1) := by
  rw [div_pow]; rw [div_add_one (by positivity)]; rw [one_div_div]; rw [r1]

/--
lemma `r1_pos` / 引理 `r1_pos`

English:
lemma r1_pos
  statement: 0 < r1 z
  proof: by
  dsimp only [r1]
  positivity

中文:
引理 r1_pos
  结论: 0 < r1 z
  证明: by
  dsimp only [r1]
  positivity
-/
lemma r1_pos : 0 < r1 z := by
  dsimp only [r1]
  positivity

/--
lemma `r1_aux_bound` / 引理 `r1_aux_bound`

English:
lemma r1_aux_bound
  given: (c : Real) {d : Real} (hd : 1 <= d ^ 2)
  proof: by
  have H1 : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 =
    c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2 := by ring
  have H2 : (c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2) * (z.re ^ 2 + z.im ^ 2)
    - z.im ^ 2 = (c * (z.re ^ 2 + z.im ^ 2) + d * z.re) ^ 2 + (d ^ 2 - 1) * z.im ^ 2 := by ring
  rw [r1]; rw [H1]; rw [div_le_iff₀ (by positivity)]; rw [← sub_nonneg]; rw [H2]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg _))

中文:
引理 r1_aux_bound
  条件: (c : 实数) {d : 实数} (hd : 1 <= d ^ 2)
  证明: by
  have H1 : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 =
    c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2 := by ring
  have H2 : (c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2) * (z.re ^ 2 + z.im ^ 2)
    - z.im ^ 2 = (c * (z.re ^ 2 + z.im ^ 2) + d * z.re) ^ 2 + (d ^ 2 - 1) * z.im ^ 2 := by ring
  rw [r1]; rw [H1]; rw [div_le_iff₀ (by positivity)]; rw [← sub_nonneg]; rw [H2]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg _))

Depends on / 依赖: add_nonneg, mul_nonneg, sq_nonneg, sub_nonneg, sub_nonneg.mpr, z.im, z.re
-/
lemma r1_aux_bound (c : Real) {d : Real} (hd : 1 <= d ^ 2) :
    r1 z <= (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
  have H1 : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 =
    c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2 := by ring
  have H2 : (c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2) * (z.re ^ 2 + z.im ^ 2)
    - z.im ^ 2 = (c * (z.re ^ 2 + z.im ^ 2) + d * z.re) ^ 2 + (d ^ 2 - 1) * z.im ^ 2 := by ring
  rw [r1]; rw [H1]; rw [div_le_iff₀ (by positivity)]; rw [← sub_nonneg]; rw [H2]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg _))

/--
Definition of `r` / `r` 的定义

English:
definition r
  signature: : Real
  body: min z.im √(r1 z)

中文:
定义 r
  签名: : 实数
  定义体: min z.im √(r1 z)

Depends on / 依赖: z.im
-/
def r : Real := min z.im √(r1 z)

/--
lemma `r_pos` / 引理 `r_pos`

English:
lemma r_pos
  statement: 0 < r z
  proof: by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]

中文:
引理 r_pos
  结论: 0 < r z
  证明: by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]

Depends on / 依赖: Real.sqrt_pos, and_self, im_pos, lt_min_iff, r1_pos, sqrt_pos
-/
lemma r_pos : 0 < r z := by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]

/--
lemma `r_lower_bound_on_verticalStrip` / 引理 `r_lower_bound_on_verticalStrip`

English:
lemma r_lower_bound_on_verticalStrip
  given: {A B : Real} (h : 0 < B) (hz : z in verticalStrip A B)
  proof: by
  apply min_le_min hz.2
  gcongr
  simp only [r1_eq, div_pow, one_div]
  rw [inv_le_inv₀ (by positivity) (by positivity)]; rw [add_le_add_iff_right]; rw [← even_two.pow_abs]
  gcongr
  exacts [hz.1, hz.2]

中文:
引理 r_lower_bound_on_verticalStrip
  条件: {A B : 实数} (h : 0 < B) (hz : z in verticalStrip A B)
  证明: by
  apply min_le_min hz.2
  gcongr
  simp only [r1_eq, div_pow, one_div]
  rw [inv_le_inv₀ (by positivity) (by positivity)]; rw [add_le_add_iff_right]; rw [← even_two.pow_abs]
  gcongr
  exacts [hz.1, hz.2]

Depends on / 依赖: add_le_add_iff_right, div_pow, even_two, even_two.pow_abs, exacts, min_le_min, one_div, pow_abs, r1_eq
-/
lemma r_lower_bound_on_verticalStrip {A B : Real} (h : 0 < B) (hz : z in verticalStrip A B) :
    r ⟨⟨A, B⟩, h⟩ <= r z := by
  apply min_le_min hz.2
  gcongr
  simp only [r1_eq, div_pow, one_div]
  rw [inv_le_inv₀ (by positivity) (by positivity)]; rw [add_le_add_iff_right]; rw [← even_two.pow_abs]
  gcongr
  exacts [hz.1, hz.2]

/--
lemma `auxbound1` / 引理 `auxbound1`

English:
lemma auxbound1
  given: {c : Real} (d : Real) (hc : 1 <= c ^ 2)
  statement: r z <= ‖c * (z : Complex) + d‖
  proof: by
  rcases z with ⟨z, hz⟩
  have H1 : z.im <= √((c * z.re + d) ^ 2 + (c * z).im ^ 2) := by
    rw [Real.le_sqrt' hz]; rw [im_ofReal_mul]; rw [mul_pow]
exact (le_mul_of_one_le_left (sq_nonneg _) hc).trans le_add_of_nonneg_left (sq_nonneg _)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ← pow_two, add_im, mul_im,
    coe_im, ofReal_im, zero_mul, add_zero, min_le_iff] using! Or.inl H1

中文:
引理 auxbound1
  条件: {c : 实数} (d : 实数) (hc : 1 <= c ^ 2)
  结论: r z <= ‖c * (z : 复形) + d‖
  证明: by
  rcases z with ⟨z, hz⟩
  have H1 : z.im <= √((c * z.re + d) ^ 2 + (c * z).im ^ 2) := by
    rw [Real.le_sqrt' hz]; rw [im_ofReal_mul]; rw [mul_pow]
exact (le_mul_of_one_le_left (sq_nonneg _) hc).trans le_add_of_nonneg_left (sq_nonneg _)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ← pow_two, add_im, mul_im,
    coe_im, ofReal_im, zero_mul, add_zero, min_le_iff] using! Or.inl H1

Depends on / 依赖: Or.inl, Real.le_sqrt, add_im, add_re, add_zero, coe_im, coe_re, im_ofReal_mul, le_add_of_nonneg_left, le_mul_of_one_le_left, le_sqrt, min_le_iff, mul_im, mul_pow, normSq_apply, norm_def, ofReal_im, pow_two, re_ofReal_mul, sq_nonneg
-/
lemma auxbound1 {c : Real} (d : Real) (hc : 1 <= c ^ 2) : r z <= ‖c * (z : Complex) + d‖ := by
  rcases z with ⟨z, hz⟩
  have H1 : z.im <= √((c * z.re + d) ^ 2 + (c * z).im ^ 2) := by
    rw [Real.le_sqrt' hz]; rw [im_ofReal_mul]; rw [mul_pow]
exact (le_mul_of_one_le_left (sq_nonneg _) hc).trans le_add_of_nonneg_left (sq_nonneg _)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ← pow_two, add_im, mul_im,
    coe_im, ofReal_im, zero_mul, add_zero, min_le_iff] using! Or.inl H1

/--
lemma `auxbound2` / 引理 `auxbound2`

English:
lemma auxbound2
  given: (c : Real) {d : Real} (hd : 1 <= d ^ 2)
  statement: r z <= ‖c * (z : Complex) + d‖
  proof: by
  have H1 : √(r1 z) <= √((c * z.re + d) ^ 2 + (c * z.im) ^ 2) :=
    (Real.sqrt_le_sqrt_iff (by positivity)).mpr (r1_aux_bound _ _ hd)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ofReal_re, ← pow_two,
    add_im, im_ofReal_mul, coe_im, ofReal_im, add_zero, min_le_iff] using Or.inr H1

中文:
引理 auxbound2
  条件: (c : 实数) {d : 实数} (hd : 1 <= d ^ 2)
  结论: r z <= ‖c * (z : 复形) + d‖
  证明: by
  have H1 : √(r1 z) <= √((c * z.re + d) ^ 2 + (c * z.im) ^ 2) :=
    (Real.sqrt_le_sqrt_iff (by positivity)).mpr (r1_aux_bound _ _ hd)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ofReal_re, ← pow_two,
    add_im, im_ofReal_mul, coe_im, ofReal_im, add_zero, min_le_iff] using Or.inr H1

Depends on / 依赖: Or.inr, Real.sqrt_le_sqrt_iff, add_im, add_re, add_zero, coe_im, coe_re, im_ofReal_mul, min_le_iff, normSq_apply, norm_def, ofReal_im, ofReal_re, pow_two, r1_aux_bound, re_ofReal_mul, sqrt_le_sqrt_iff, z.im, z.re
-/
lemma auxbound2 (c : Real) {d : Real} (hd : 1 <= d ^ 2) : r z <= ‖c * (z : Complex) + d‖ := by
  have H1 : √(r1 z) <= √((c * z.re + d) ^ 2 + (c * z.im) ^ 2) :=
    (Real.sqrt_le_sqrt_iff (by positivity)).mpr (r1_aux_bound _ _ hd)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ofReal_re, ← pow_two,
    add_im, im_ofReal_mul, coe_im, ofReal_im, add_zero, min_le_iff] using Or.inr H1

/--
lemma `div_max_sq_ge_one` / 引理 `div_max_sq_ge_one`

English:
lemma div_max_sq_ge_one
  given: (x : Fin 2 -> Int) (hx : x != 0)
  proof: by
  refine (max_choice (x 0).natAbs (x 1).natAbs).imp (fun H0 => ?_) (fun H1 => ?_)
  · have : x 0 != 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H0, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H0, Nat.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]
  · have : x 1 != 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H1, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H1, Nat.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]

中文:
引理 div_max_sq_ge_one
  条件: (x : 有限集 2 -> 整数) (hx : x != 0)
  证明: by
  refine (max_choice (x 0).natAbs (x 1).natAbs).imp (fun H0 => ?_) (fun H1 => ?_)
  · have : x 0 != 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H0, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H0, Nat.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]
  · have : x 1 != 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H1, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H1, Nat.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]

Depends on / 依赖: Int.cast_abs, Int.cast_eq_zero, Int.natAbs_ne_zero, Nat.cast_natAbs, Nat.cast_ne_zero, OfNat.ofNat_ne_zero, cast_abs, cast_eq_zero, cast_natAbs, cast_ne_zero, div_pow, div_self, le_refl, max_choice, natAbs, natAbs_ne_zero, ne_eq, norm_eq_max_natAbs, norm_ne_zero_iff, not_false_eq_true
-/
lemma div_max_sq_ge_one (x : Fin 2 -> Int) (hx : x != 0) :
    1 <= (x 0 / ‖x‖) ^ 2 ∨ 1 <= (x 1 / ‖x‖) ^ 2 := by
  refine (max_choice (x 0).natAbs (x 1).natAbs).imp (fun H0 => ?_) (fun H1 => ?_)
  · have : x 0 != 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H0, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H0, Nat.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]
  · have : x 1 != 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H1, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H1, Nat.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]

/--
lemma `r_mul_max_le` / 引理 `r_mul_max_le`

English:
lemma r_mul_max_le
  given: {x : Fin 2 -> Int} (hx : x != 0)
  statement: r z * ‖x‖ <= ‖x 0 * (z : Complex) + x 1‖
  proof: by
  have hn0 : ‖x‖ != 0 := by rwa [norm_ne_zero_iff]
  have h11 : x 0 * (z : Complex) + x 1 = (x 0 / ‖x‖ * z + x 1 / ‖x‖) * ‖x‖ := by
    rw [div_mul_eq_mul_div]; rw [← add_div]; rw [div_mul_cancel₀ _ (mod_cast hn0)]
  rw [norm_eq_max_natAbs]; rw [h11]; rw [norm_mul]; rw [norm_real]; rw [norm_norm]; rw [norm_eq_max_natAbs]
  gcongr
  · rcases div_max_sq_ge_one x hx with H1 | H2
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound1 z (x 1 / ‖x‖) H1
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound2 z (x 0 / ‖x‖) H2

中文:
引理 r_mul_max_le
  条件: {x : 有限集 2 -> 整数} (hx : x != 0)
  结论: r z * ‖x‖ <= ‖x 0 * (z : 复形) + x 1‖
  证明: by
  have hn0 : ‖x‖ != 0 := by rwa [norm_ne_zero_iff]
  have h11 : x 0 * (z : Complex) + x 1 = (x 0 / ‖x‖ * z + x 1 / ‖x‖) * ‖x‖ := by
    rw [div_mul_eq_mul_div]; rw [← add_div]; rw [div_mul_cancel₀ _ (mod_cast hn0)]
  rw [norm_eq_max_natAbs]; rw [h11]; rw [norm_mul]; rw [norm_real]; rw [norm_norm]; rw [norm_eq_max_natAbs]
  gcongr
  · rcases div_max_sq_ge_one x hx with H1 | H2
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound1 z (x 1 / ‖x‖) H1
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound2 z (x 0 / ‖x‖) H2

Depends on / 依赖: add_div, auxbound1, div_max_sq_ge_one, div_mul_eq_mul_div, mod_cast, norm_eq_max_natAbs, norm_mul, norm_ne_zero_iff, norm_norm, norm_real, ofReal_div, ofReal_intCast
-/
lemma r_mul_max_le {x : Fin 2 -> Int} (hx : x != 0) : r z * ‖x‖ <= ‖x 0 * (z : Complex) + x 1‖ := by
  have hn0 : ‖x‖ != 0 := by rwa [norm_ne_zero_iff]
  have h11 : x 0 * (z : Complex) + x 1 = (x 0 / ‖x‖ * z + x 1 / ‖x‖) * ‖x‖ := by
    rw [div_mul_eq_mul_div]; rw [← add_div]; rw [div_mul_cancel₀ _ (mod_cast hn0)]
  rw [norm_eq_max_natAbs]; rw [h11]; rw [norm_mul]; rw [norm_real]; rw [norm_norm]; rw [norm_eq_max_natAbs]
  gcongr
  · rcases div_max_sq_ge_one x hx with H1 | H2
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound1 z (x 1 / ‖x‖) H1
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound2 z (x 0 / ‖x‖) H2

/--
lemma `summand_bound` / 引理 `summand_bound`

English:
lemma summand_bound
  given: {k : Real} (hk : 0 <= k) (x : Fin 2 -> Int)
  proof: by
  by_cases hx : x = 0
  · simp only [hx, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
    by_cases h : -k = 0
    · rw [h, Real.rpow_zero, Real.rpow_zero, one_mul]
    · rw [Real.zero_rpow h, mul_zero]
  · rw [← Real.mul_rpow (r_pos _).le (norm_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos (r_pos _) (norm_pos_iff.mpr hx)) (r_mul_max_le z hx)
      (neg_nonpos.mpr hk)

中文:
引理 summand_bound
  条件: {k : 实数} (hk : 0 <= k) (x : 有限集 2 -> 整数)
  证明: by
  by_cases hx : x = 0
  · simp only [hx, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
    by_cases h : -k = 0
    · rw [h, Real.rpow_zero, Real.rpow_zero, one_mul]
    · rw [Real.zero_rpow h, mul_zero]
  · rw [← Real.mul_rpow (r_pos _).le (norm_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos (r_pos _) (norm_pos_iff.mpr hx)) (r_mul_max_le z hx)
      (neg_nonpos.mpr hk)

Depends on / 依赖: Int.cast_zero, Pi.zero_apply, Real.mul_rpow, Real.rpow_le_rpow_of_nonpos, Real.rpow_zero, Real.zero_rpow, add_zero, cast_zero, mul_pos, mul_rpow, mul_zero, neg_nonpos, neg_nonpos.mpr, norm_nonneg, norm_pos_iff, norm_pos_iff.mpr, norm_zero, one_mul, r_mul_max_le, r_pos
-/
lemma summand_bound {k : Real} (hk : 0 <= k) (x : Fin 2 -> Int) :
    ‖x 0 * (z : Complex) + x 1‖ ^ (-k) <= (r z) ^ (-k) * ‖x‖ ^ (-k) := by
  by_cases hx : x = 0
  · simp only [hx, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
    by_cases h : -k = 0
    · rw [h, Real.rpow_zero, Real.rpow_zero, one_mul]
    · rw [Real.zero_rpow h, mul_zero]
  · rw [← Real.mul_rpow (r_pos _).le (norm_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos (r_pos _) (norm_pos_iff.mpr hx)) (r_mul_max_le z hx)
      (neg_nonpos.mpr hk)

variable {z} in
/--
lemma `summand_bound_of_mem_verticalStrip` / 引理 `summand_bound_of_mem_verticalStrip`

English:
lemma summand_bound_of_mem_verticalStrip
  statement: {k : Real} (hk : 0 <= k) (x : Fin 2 -> Int)
  proof: by
  refine (summand_bound z hk x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.rpow_le_rpow_of_nonpos (r_pos _) (r_lower_bound_on_verticalStrip z hB hz)
    (neg_nonpos.mpr hk)

中文:
引理 summand_bound_of_mem_verticalStrip
  结论: {k : 实数} (hk : 0 <= k) (x : 有限集 2 -> 整数)
  证明: by
  refine (summand_bound z hk x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.rpow_le_rpow_of_nonpos (r_pos _) (r_lower_bound_on_verticalStrip z hB hz)
    (neg_nonpos.mpr hk)

Depends on / 依赖: Real.rpow_le_rpow_of_nonpos, mul_le_mul_of_nonneg_right, neg_nonpos, neg_nonpos.mpr, r_lower_bound_on_verticalStrip, r_pos, rpow_le_rpow_of_nonpos, summand_bound
-/
lemma summand_bound_of_mem_verticalStrip {k : Real} (hk : 0 <= k) (x : Fin 2 -> Int)
    {A B : Real} (hB : 0 < B) (hz : z in verticalStrip A B) :
    ‖x 0 * (z : Complex) + x 1‖ ^ (-k) <= r ⟨⟨A, B⟩, hB⟩ ^ (-k) * ‖x‖ ^ (-k) := by
  refine (summand_bound z hk x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.rpow_le_rpow_of_nonpos (r_pos _) (r_lower_bound_on_verticalStrip z hB hz)
    (neg_nonpos.mpr hk)

/--
lemma `linear_isTheta_right_add` / 引理 `linear_isTheta_right_add`

English:
lemma linear_isTheta_right_add
  given: (c e : Int) (z : Complex)
  proof: by
  apply IsTheta.add_isLittleO <;>
  [refine Asymptotics.IsLittleO.add_isTheta ?_ (Int.cast_complex_isTheta_cast_real); skip] <;>
  simpa [-Int.cofinite_eq] using
.inr tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real

中文:
引理 linear_isTheta_right_add
  条件: (c e : 整数) (z : 复形)
  证明: by
  apply IsTheta.add_isLittleO <;>
  [refine Asymptotics.IsLittleO.add_isTheta ?_ (Int.cast_complex_isTheta_cast_real); skip] <;>
  simpa [-Int.cofinite_eq] using
.inr tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real

Depends on / 依赖: Asymptotics, Asymptotics.IsLittleO.add_isTheta, Int.cast_complex_isTheta_cast_real, Int.cofinite_eq, Int.isClosedEmbedding_coe_real, IsLittleO, IsTheta, IsTheta.add_isLittleO, add_isLittleO, add_isTheta, cast_complex_isTheta_cast_real, cofinite_eq, isClosedEmbedding_coe_real, tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
-/
lemma linear_isTheta_right_add (c e : Int) (z : Complex) :
    (fun d : Int => c * z + d + e) =Θ[cofinite] fun n => (n : Real) := by
  apply IsTheta.add_isLittleO <;>
  [refine Asymptotics.IsLittleO.add_isTheta ?_ (Int.cast_complex_isTheta_cast_real); skip] <;>
  simpa [-Int.cofinite_eq] using
.inr tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real

/--
lemma `linear_isTheta_left` / 引理 `linear_isTheta_left`

English:
lemma linear_isTheta_left
  given: (d : Int) {z : Complex} (hz : z != 0)
  proof: by
  apply IsTheta.add_isLittleO
  · simp_rw [mul_comm]
    apply Asymptotics.IsTheta.const_mul_left hz Int.cast_complex_isTheta_cast_real
  · simp only [isLittleO_const_left, Int.cast_eq_zero,
      tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real, or_true]

中文:
引理 linear_isTheta_left
  条件: (d : 整数) {z : 复形} (hz : z != 0)
  证明: by
  apply IsTheta.add_isLittleO
  · simp_rw [mul_comm]
    apply Asymptotics.IsTheta.const_mul_left hz Int.cast_complex_isTheta_cast_real
  · simp only [isLittleO_const_left, Int.cast_eq_zero,
      tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real, or_true]

Depends on / 依赖: Asymptotics, Asymptotics.IsTheta.const_mul_left, Int.cast_complex_isTheta_cast_real, Int.cast_eq_zero, Int.isClosedEmbedding_coe_real, IsTheta, IsTheta.add_isLittleO, add_isLittleO, cast_complex_isTheta_cast_real, cast_eq_zero, const_mul_left, isClosedEmbedding_coe_real, isLittleO_const_left, mul_comm, or_true, simp_rw, tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
-/
lemma linear_isTheta_left (d : Int) {z : Complex} (hz : z != 0) :
    (fun (c : Int) => (c * z + d)) =Θ[cofinite] fun n => (n : Real) := by
  apply IsTheta.add_isLittleO
  · simp_rw [mul_comm]
    apply Asymptotics.IsTheta.const_mul_left hz Int.cast_complex_isTheta_cast_real
  · simp only [isLittleO_const_left, Int.cast_eq_zero,
      tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real, or_true]

/--
lemma `linear_inv_isBigO_right_add` / 引理 `linear_inv_isBigO_right_add`

English:
lemma linear_inv_isBigO_right_add
  given: (c e : Int) (z : Complex)
  proof: (linear_isTheta_right_add c e z).inv.isBigO

中文:
引理 linear_inv_isBigO_right_add
  条件: (c e : 整数) (z : 复形)
  证明: (linear_isTheta_right_add c e z).inv.isBigO

Depends on / 依赖: inv.isBigO, isBigO, linear_isTheta_right_add
-/
lemma linear_inv_isBigO_right_add (c e : Int) (z : Complex) :
    (fun (d : Int) => (c * z + d + e)⁻¹) =O[cofinite] fun n => (n : Real)⁻¹ :=
  (linear_isTheta_right_add c e z).inv.isBigO

/--
lemma `linear_inv_isBigO_right` / 引理 `linear_inv_isBigO_right`

English:
lemma linear_inv_isBigO_right
  given: (c : Int) (z : Complex)
  proof: by
  grind [add_zero, (linear_isTheta_right_add c 0 z).inv.isBigO]

中文:
引理 linear_inv_isBigO_right
  条件: (c : 整数) (z : 复形)
  证明: by
  grind [add_zero, (linear_isTheta_right_add c 0 z).inv.isBigO]

Depends on / 依赖: add_zero, inv.isBigO, isBigO, linear_isTheta_right_add
-/
lemma linear_inv_isBigO_right (c : Int) (z : Complex) :
    (fun (d : Int) => (c * z + d)⁻¹) =O[cofinite] fun n => (n : Real)⁻¹ := by
  grind [add_zero, (linear_isTheta_right_add c 0 z).inv.isBigO]

/--
lemma `linear_inv_isBigO_left` / 引理 `linear_inv_isBigO_left`

English:
lemma linear_inv_isBigO_left
  given: (d : Int) {z : Complex} (hz : z != 0)
  proof: (linear_isTheta_left d hz).inv.isBigO

中文:
引理 linear_inv_isBigO_left
  条件: (d : 整数) {z : 复形} (hz : z != 0)
  证明: (linear_isTheta_left d hz).inv.isBigO

Depends on / 依赖: inv.isBigO, isBigO, linear_isTheta_left
-/
lemma linear_inv_isBigO_left (d : Int) {z : Complex} (hz : z != 0) :
    (fun (c : Int) => (c * z + d)⁻¹) =O[cofinite] fun n => (n : Real)⁻¹ :=
  (linear_isTheta_left d hz).inv.isBigO

/--
lemma `tendsto_zero_inv_linear` / 引理 `tendsto_zero_inv_linear`

English:
lemma tendsto_zero_inv_linear
  given: (z : Complex) (b : Int)
  proof: by
  apply IsBigO.trans_tendsto ?_ tendsto_inv_atTop_nhds_zero_nat (F'' := Real)
  have := (isBigO_sup.mp (Int.cofinite_eq ▸ linear_inv_isBigO_right b z)).2
  simpa [← Nat.map_cast_int_atTop, isBigO_map]

中文:
引理 tendsto_zero_inv_linear
  条件: (z : 复形) (b : 整数)
  证明: by
  apply IsBigO.trans_tendsto ?_ tendsto_inv_atTop_nhds_zero_nat (F'' := Real)
  have := (isBigO_sup.mp (Int.cofinite_eq ▸ linear_inv_isBigO_right b z)).2
  simpa [← Nat.map_cast_int_atTop, isBigO_map]

Depends on / 依赖: Int.cofinite_eq, IsBigO, IsBigO.trans_tendsto, Nat.map_cast_int_atTop, cofinite_eq, isBigO_map, isBigO_sup, isBigO_sup.mp, linear_inv_isBigO_right, map_cast_int_atTop, tendsto_inv_atTop_nhds_zero_nat, trans_tendsto
-/
lemma tendsto_zero_inv_linear (z : Complex) (b : Int) :
    Tendsto (fun d : Nat => 1 / ((b : Complex) * z + d)) atTop (𝓝 0) := by
  apply IsBigO.trans_tendsto ?_ tendsto_inv_atTop_nhds_zero_nat (F'' := Real)
  have := (isBigO_sup.mp (Int.cofinite_eq ▸ linear_inv_isBigO_right b z)).2
  simpa [← Nat.map_cast_int_atTop, isBigO_map]

/--
lemma `tendsto_zero_inv_linear_sub` / 引理 `tendsto_zero_inv_linear_sub`

English:
lemma tendsto_zero_inv_linear_sub
  given: (z : Complex) (b : Int)
  proof: by
  grind [neg_zero, (tendsto_zero_inv_linear z (-b)).neg]

中文:
引理 tendsto_zero_inv_linear_sub
  条件: (z : 复形) (b : 整数)
  证明: by
  grind [neg_zero, (tendsto_zero_inv_linear z (-b)).neg]

Depends on / 依赖: neg_zero, tendsto_zero_inv_linear
-/
lemma tendsto_zero_inv_linear_sub (z : Complex) (b : Int) :
    Tendsto (fun d : Nat => 1 / ((b : Complex) * z - d)) atTop (𝓝 0) := by
  grind [neg_zero, (tendsto_zero_inv_linear z (-b)).neg]

end bounding_functions

/--
lemma `summable_one_div_norm_rpow` / 引理 `summable_one_div_norm_rpow`

English:
lemma summable_one_div_norm_rpow
  given: {k : Real} (hk : 2 < k)
  proof: by
  rw [← (finTwoArrowEquiv _).symm.summable_iff]; rw [summable_partition _ Int.existsUnique_mem_box]
  · simp only [finTwoArrowEquiv_symm_apply, Function.comp_def]
    refine ⟨fun n => (hasSum_fintype (β := box (α := Int × Int) n) _).summable, ?_⟩
    suffices Summable fun n : Nat => ∑' (_ : box (α := Int × Int) n), (n : Real) ^ (-k) by
      refine this.congr fun n => tsum_congr fun p => ?_
      simp only [← Int.mem_box.mp p.2, Nat.cast_max, norm_eq_max_natAbs, Matrix.cons_val_zero,
        Matrix.cons_val_one]
    simp only [tsum_fintype, univ_eq_attach, sum_const, card_attach, nsmul_eq_mul]
    apply ((Real.summable_nat_rpow.mpr (by linarith : 1 - k < -1)).mul_left
      8).of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Int.card_box hn.ne']; rw [Real.norm_of_nonneg (by positivity)]; rw [sub_eq_add_neg]; rw [Real.rpow_add (Nat.cast_pos.mpr hn)]; rw [Real.rpow_one]; rw [Nat.cast_mul]; rw [Nat.cast_ofNat]; rw [mul_assoc]
  · exact fun n => Real.rpow_nonneg (norm_nonneg _) _

中文:
引理 summable_one_div_norm_rpow
  条件: {k : 实数} (hk : 2 < k)
  证明: by
  rw [← (finTwoArrowEquiv _).symm.summable_iff]; rw [summable_partition _ Int.existsUnique_mem_box]
  · simp only [finTwoArrowEquiv_symm_apply, Function.comp_def]
    refine ⟨fun n => (hasSum_fintype (β := box (α := Int × Int) n) _).summable, ?_⟩
    suffices Summable fun n : Nat => ∑' (_ : box (α := Int × Int) n), (n : Real) ^ (-k) by
      refine this.congr fun n => tsum_congr fun p => ?_
      simp only [← Int.mem_box.mp p.2, Nat.cast_max, norm_eq_max_natAbs, Matrix.cons_val_zero,
        Matrix.cons_val_one]
    simp only [tsum_fintype, univ_eq_attach, sum_const, card_attach, nsmul_eq_mul]
    apply ((Real.summable_nat_rpow.mpr (by linarith : 1 - k < -1)).mul_left
      8).of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Int.card_box hn.ne']; rw [Real.norm_of_nonneg (by positivity)]; rw [sub_eq_add_neg]; rw [Real.rpow_add (Nat.cast_pos.mpr hn)]; rw [Real.rpow_one]; rw [Nat.cast_mul]; rw [Nat.cast_ofNat]; rw [mul_assoc]
  · exact fun n => Real.rpow_nonneg (norm_nonneg _) _

Depends on / 依赖: Function, Function.comp_def, Int.existsUnique_mem_box, Int.mem_box.mp, Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_max, Summable, cast_max, comp_def, cons_val_one, cons_val_zero, existsUnique_mem_box, finTwoArrowEquiv, finTwoArrowEquiv_symm_apply, hasSum_fintype, mem_box, norm_eq_max_natAbs, summable
-/
lemma summable_one_div_norm_rpow {k : Real} (hk : 2 < k) :
    Summable fun (x : Fin 2 -> Int) => ‖x‖ ^ (-k) := by
  rw [← (finTwoArrowEquiv _).symm.summable_iff]; rw [summable_partition _ Int.existsUnique_mem_box]
  · simp only [finTwoArrowEquiv_symm_apply, Function.comp_def]
    refine ⟨fun n => (hasSum_fintype (β := box (α := Int × Int) n) _).summable, ?_⟩
    suffices Summable fun n : Nat => ∑' (_ : box (α := Int × Int) n), (n : Real) ^ (-k) by
      refine this.congr fun n => tsum_congr fun p => ?_
      simp only [← Int.mem_box.mp p.2, Nat.cast_max, norm_eq_max_natAbs, Matrix.cons_val_zero,
        Matrix.cons_val_one]
    simp only [tsum_fintype, univ_eq_attach, sum_const, card_attach, nsmul_eq_mul]
    apply ((Real.summable_nat_rpow.mpr (by linarith : 1 - k < -1)).mul_left
      8).of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Int.card_box hn.ne']; rw [Real.norm_of_nonneg (by positivity)]; rw [sub_eq_add_neg]; rw [Real.rpow_add (Nat.cast_pos.mpr hn)]; rw [Real.rpow_one]; rw [Nat.cast_mul]; rw [Nat.cast_ofNat]; rw [mul_assoc]
  · exact fun n => Real.rpow_nonneg (norm_nonneg _) _

/--
lemma `summable_inv_of_isBigO_rpow_inv` / 引理 `summable_inv_of_isBigO_rpow_inv`

English:
lemma summable_inv_of_isBigO_rpow_inv
  statement: {α : Type*} [NormedField α] [CompleteSpace α]
  proof: summable_of_isBigO
    ((Real.summable_abs_int_rpow hab).congr fun b => Real.rpow_neg (abs_nonneg ↑b) a) hf

中文:
引理 summable_inv_of_isBigO_rpow_inv
  结论: {α : 类型} [赋范域 α] [完备空间 α]
  证明: summable_of_isBigO
    ((Real.summable_abs_int_rpow hab).congr fun b => Real.rpow_neg (abs_nonneg ↑b) a) hf

Depends on / 依赖: Real.rpow_neg, Real.summable_abs_int_rpow, abs_nonneg, rpow_neg, summable_abs_int_rpow, summable_of_isBigO
-/
lemma summable_inv_of_isBigO_rpow_inv {α : Type*} [NormedField α] [CompleteSpace α]
    {f : Int -> α} {a : Real} (hab : 1 < a)
    (hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : Real)| ^ a)⁻¹) :
    Summable fun n => (f n)⁻¹ :=
  summable_of_isBigO
    ((Real.summable_abs_int_rpow hab).congr fun b => Real.rpow_neg (abs_nonneg ↑b) a) hf

/--
lemma `linear_right_summable` / 引理 `linear_right_summable`

English:
lemma linear_right_summable
  given: (z : Complex) (c : Int) {k : Int} (hk : 2 <= k)
  proof: by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast)
  lift k to Nat using by lia
  grind [(linear_inv_isBigO_right c z).abs_right.pow k,
    zpow_natCast, Int.cast_natCast, Real.rpow_natCast, ← inv_pow]

中文:
引理 linear_right_summable
  条件: (z : 复形) (c : 整数) {k : 整数} (hk : 2 <= k)
  证明: by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast)
  lift k to Nat using by lia
  grind [(linear_inv_isBigO_right c z).abs_right.pow k,
    zpow_natCast, Int.cast_natCast, Real.rpow_natCast, ← inv_pow]

Depends on / 依赖: Int.cast_natCast, Real.rpow_natCast, abs_right, abs_right.pow, cast_natCast, inv_pow, linear_inv_isBigO_right, rpow_natCast, summable_inv_of_isBigO_rpow_inv, zpow_natCast
-/
lemma linear_right_summable (z : Complex) (c : Int) {k : Int} (hk : 2 <= k) :
    Summable fun d : Int => ((c * z + d) ^ k)⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast)
  lift k to Nat using by lia
  grind [(linear_inv_isBigO_right c z).abs_right.pow k,
    zpow_natCast, Int.cast_natCast, Real.rpow_natCast, ← inv_pow]

/--
lemma `linear_left_summable` / 引理 `linear_left_summable`

English:
lemma linear_left_summable
  given: {z : Complex} (hz : z != 0) (d : Int) {k : Int} (hk : 2 <= k)
  proof: by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast)
  lift k to Nat using (by lia)
  simp only [zpow_natCast, Int.cast_natCast, Real.rpow_natCast, ← inv_pow, ← abs_inv]
  apply (linear_inv_isBigO_left d hz).abs_right.pow

中文:
引理 linear_left_summable
  条件: {z : 复形} (hz : z != 0) (d : 整数) {k : 整数} (hk : 2 <= k)
  证明: by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast)
  lift k to Nat using (by lia)
  simp only [zpow_natCast, Int.cast_natCast, Real.rpow_natCast, ← inv_pow, ← abs_inv]
  apply (linear_inv_isBigO_left d hz).abs_right.pow

Depends on / 依赖: Int.cast_natCast, Real.rpow_natCast, abs_inv, abs_right, abs_right.pow, cast_natCast, inv_pow, linear_inv_isBigO_left, rpow_natCast, summable_inv_of_isBigO_rpow_inv, zpow_natCast
-/
lemma linear_left_summable {z : Complex} (hz : z != 0) (d : Int) {k : Int} (hk : 2 <= k) :
    Summable fun c : Int => ((c * z + d) ^ k)⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast)
  lift k to Nat using (by lia)
  simp only [zpow_natCast, Int.cast_natCast, Real.rpow_natCast, ← inv_pow, ← abs_inv]
  apply (linear_inv_isBigO_left d hz).abs_right.pow

/--
lemma `summable_linear_sub_mul_linear_add` / 引理 `summable_linear_sub_mul_linear_add`

English:
lemma summable_linear_sub_mul_linear_add
  given: (z : Complex) (c₁ c₂ : Int)
  proof: by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simpa [pow_two] using! (linear_inv_isBigO_right c₂ z).mul
      (linear_inv_isBigO_right c₁ z).comp_neg_int

中文:
引理 summable_linear_sub_mul_linear_add
  条件: (z : 复形) (c₁ c₂ : 整数)
  证明: by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simpa [pow_two] using! (linear_inv_isBigO_right c₂ z).mul
      (linear_inv_isBigO_right c₁ z).comp_neg_int

Depends on / 依赖: comp_neg_int, linear_inv_isBigO_right, pow_two, summable_inv_of_isBigO_rpow_inv
-/
lemma summable_linear_sub_mul_linear_add (z : Complex) (c₁ c₂ : Int) :
    Summable fun n : Int => ((c₁ * z - n) * (c₂ * z + n))⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simpa [pow_two] using! (linear_inv_isBigO_right c₂ z).mul
      (linear_inv_isBigO_right c₁ z).comp_neg_int

/--
lemma `summable_linear_right_add_one_mul_linear_right` / 引理 `summable_linear_right_add_one_mul_linear_right`

English:
lemma summable_linear_right_add_one_mul_linear_right
  given: (z : Complex) (c₁ c₂ : Int)
  proof: by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simpa [pow_two] using (linear_inv_isBigO_right c₂ z).mul
    (linear_inv_isBigO_right_add c₁ 1 z)

中文:
引理 summable_linear_right_add_one_mul_linear_right
  条件: (z : 复形) (c₁ c₂ : 整数)
  证明: by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simpa [pow_two] using (linear_inv_isBigO_right c₂ z).mul
    (linear_inv_isBigO_right_add c₁ 1 z)

Depends on / 依赖: linear_inv_isBigO_right, linear_inv_isBigO_right_add, pow_two, summable_inv_of_isBigO_rpow_inv
-/
lemma summable_linear_right_add_one_mul_linear_right (z : Complex) (c₁ c₂ : Int) :
    Summable fun n : Int => ((c₁ * z + n + 1) * (c₂ * z + n))⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simpa [pow_two] using (linear_inv_isBigO_right c₂ z).mul
    (linear_inv_isBigO_right_add c₁ 1 z)

/--
lemma `summable_linear_left_mul_linear_left` / 引理 `summable_linear_left_mul_linear_left`

English:
lemma summable_linear_left_mul_linear_left
  given: {z : Complex} (hz : z != 0) (c₁ c₂ : Int)
  proof: by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simp only [Real.rpow_two, abs_mul_abs_self, pow_two]
  simpa using (linear_inv_isBigO_left c₂ hz).mul (linear_inv_isBigO_left c₁ hz)

中文:
引理 summable_linear_left_mul_linear_left
  条件: {z : 复形} (hz : z != 0) (c₁ c₂ : 整数)
  证明: by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simp only [Real.rpow_two, abs_mul_abs_self, pow_two]
  simpa using (linear_inv_isBigO_left c₂ hz).mul (linear_inv_isBigO_left c₁ hz)

Depends on / 依赖: Real.rpow_two, abs_mul_abs_self, linear_inv_isBigO_left, pow_two, rpow_two, summable_inv_of_isBigO_rpow_inv
-/
lemma summable_linear_left_mul_linear_left {z : Complex} (hz : z != 0) (c₁ c₂ : Int) :
    Summable fun n : Int => ((n * z + c₁) * (n * z + c₂))⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simp only [Real.rpow_two, abs_mul_abs_self, pow_two]
  simpa using (linear_inv_isBigO_left c₂ hz).mul (linear_inv_isBigO_left c₁ hz)

/--
lemma `aux_isBigO_linear` / 引理 `aux_isBigO_linear`

English:
lemma aux_isBigO_linear
  given: (z : ℍ) (a b : Int)
  proof: by
  rw [Asymptotics.isBigO_iff]
  have h0 : z in verticalStrip |z.re| (z.im) := by simp [mem_verticalStrip_iff]
  use ‖r ⟨⟨|z.re|, z.im⟩, z.2⟩‖⁻¹
  filter_upwards with m
  apply le_trans (by simpa [Real.rpow_neg_one, add_assoc] using
    summand_bound_of_mem_verticalStrip zero_le_one ![m 0 + a, m 1 + b] z.2 h0)
  simp [abs_of_pos (r_pos _)]

中文:
引理 aux_isBigO_linear
  条件: (z : ℍ) (a b : 整数)
  证明: by
  rw [Asymptotics.isBigO_iff]
  have h0 : z in verticalStrip |z.re| (z.im) := by simp [mem_verticalStrip_iff]
  use ‖r ⟨⟨|z.re|, z.im⟩, z.2⟩‖⁻¹
  filter_upwards with m
  apply le_trans (by simpa [Real.rpow_neg_one, add_assoc] using
    summand_bound_of_mem_verticalStrip zero_le_one ![m 0 + a, m 1 + b] z.2 h0)
  simp [abs_of_pos (r_pos _)]
-/
private lemma aux_isBigO_linear (z : ℍ) (a b : Int) :
    (fun (m : Fin 2 -> Int) => ((m 0 + a : Complex) * z + m 1 + b)⁻¹) =O[cofinite]
    fun (m : Fin 2 -> Int) => ‖![m 0 + a, m 1 + b]‖⁻¹ := by
  rw [Asymptotics.isBigO_iff]
  have h0 : z in verticalStrip |z.re| (z.im) := by simp [mem_verticalStrip_iff]
  use ‖r ⟨⟨|z.re|, z.im⟩, z.2⟩‖⁻¹
  filter_upwards with m
  apply le_trans (by simpa [Real.rpow_neg_one, add_assoc] using
    summand_bound_of_mem_verticalStrip zero_le_one ![m 0 + a, m 1 + b] z.2 h0)
  simp [abs_of_pos (r_pos _)]

/--
lemma `isLittleO_const_left_of_properSpace_of_discreteTopology` / 引理 `isLittleO_const_left_of_properSpace_of_discreteTopology`

English:
lemma isLittleO_const_left_of_properSpace_of_discreteTopology
  proof: by
  simpa [isLittleO_const_left, Function.comp_def] using
.inr tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding IsClosedEmbedding.id

中文:
引理 isLittleO_const_left_of_properSpace_of_discreteTopology
  证明: by
  simpa [isLittleO_const_left, Function.comp_def] using
.inr tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding IsClosedEmbedding.id

Depends on / 依赖: Function, Function.comp_def, IsClosedEmbedding, IsClosedEmbedding.id, comp_def, isLittleO_const_left, tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
-/
lemma isLittleO_const_left_of_properSpace_of_discreteTopology
    {α : Type*} (a : α) [NormedAddCommGroup α] [DiscreteTopology α]
    [ProperSpace α] : (fun _ : α => a) =o[cofinite] (‖·‖) := by
  simpa [isLittleO_const_left, Function.comp_def] using
.inr tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding IsClosedEmbedding.id

/--
lemma `vec_add_const_isTheta` / 引理 `vec_add_const_isTheta`

English:
lemma vec_add_const_isTheta
  given: (a b : Int)
  proof: by
  have (x : Fin 2 -> Int) : ![x 0 + a, x 1 + b] = x + ![a, b] := List.ofFn_inj.mp rfl
  simpa only [isTheta_inv, isTheta_norm_left, this] using! (IsTheta.add_isLittleO
  (by rw [← isTheta_norm_left]) (isLittleO_const_left_of_properSpace_of_discreteTopology ![a, b]))

中文:
引理 vec_add_const_isTheta
  条件: (a b : 整数)
  证明: by
  have (x : Fin 2 -> Int) : ![x 0 + a, x 1 + b] = x + ![a, b] := List.ofFn_inj.mp rfl
  simpa only [isTheta_inv, isTheta_norm_left, this] using! (IsTheta.add_isLittleO
  (by rw [← isTheta_norm_left]) (isLittleO_const_left_of_properSpace_of_discreteTopology ![a, b]))

Depends on / 依赖: IsTheta, IsTheta.add_isLittleO, List.ofFn_inj.mp, add_isLittleO, isLittleO_const_left_of_properSpace_of_discreteTopology, isTheta_inv, isTheta_norm_left, ofFn_inj
-/
lemma vec_add_const_isTheta (a b : Int) :
    (fun (m : Fin 2 -> Int) => ‖![m 0 + a, m 1 + b]‖⁻¹) =Θ[cofinite] (fun m => ‖m‖⁻¹) := by
  have (x : Fin 2 -> Int) : ![x 0 + a, x 1 + b] = x + ![a, b] := List.ofFn_inj.mp rfl
  simpa only [isTheta_inv, isTheta_norm_left, this] using! (IsTheta.add_isLittleO
  (by rw [← isTheta_norm_left]) (isLittleO_const_left_of_properSpace_of_discreteTopology ![a, b]))

/--
lemma `isBigO_linear_add_const_vec` / 引理 `isBigO_linear_add_const_vec`

English:
lemma isBigO_linear_add_const_vec
  given: (z : ℍ) (a b : Int)
  proof: (aux_isBigO_linear z a b).trans (vec_add_const_isTheta a b).isBigO

中文:
引理 isBigO_linear_add_const_vec
  条件: (z : ℍ) (a b : 整数)
  证明: (aux_isBigO_linear z a b).trans (vec_add_const_isTheta a b).isBigO

Depends on / 依赖: aux_isBigO_linear, isBigO, vec_add_const_isTheta
-/
lemma isBigO_linear_add_const_vec (z : ℍ) (a b : Int) :
    (fun m : (Fin 2 -> Int) => (((m 0 : Complex) + a) * z + m 1 + b)⁻¹) =O[cofinite] (fun m => ‖m‖⁻¹) :=
  (aux_isBigO_linear z a b).trans (vec_add_const_isTheta a b).isBigO

/--
lemma `summable_of_isBigO_rpow_norm` / 引理 `summable_of_isBigO_rpow_norm`

English:
lemma summable_of_isBigO_rpow_norm
  statement: {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  proof: summable_of_isBigO
    ((summable_one_div_norm_rpow hab).congr fun b => Real.rpow_neg (norm_nonneg b) a) hf

中文:
引理 summable_of_isBigO_rpow_norm
  结论: {E : 类型} [赋范交换加群 E] [完备空间 E]
  证明: summable_of_isBigO
    ((summable_one_div_norm_rpow hab).congr fun b => Real.rpow_neg (norm_nonneg b) a) hf

Depends on / 依赖: Real.rpow_neg, norm_nonneg, rpow_neg, summable_of_isBigO, summable_one_div_norm_rpow
-/
lemma summable_of_isBigO_rpow_norm {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (Fin 2 -> Int) -> E} {a : Real} (hab : 2 < a)
    (hf : f =O[cofinite] fun n => (‖n‖ ^ a)⁻¹) : Summable f :=
  summable_of_isBigO
    ((summable_one_div_norm_rpow hab).congr fun b => Real.rpow_neg (norm_nonneg b) a) hf

end EisensteinSeries
