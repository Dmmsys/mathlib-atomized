/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Nonnegativity of values of holomorphic functions

We show that if `f` is holomorphic on an open disk `B(c,r)` and all iterated derivatives of `f`
at `c` are nonnegative real, then `f z ≥ 0` for all `z ≥ c` in the disk; see
`DifferentiableOn.nonneg_of_iteratedDeriv_nonneg`. We also provide a
variant `Differentiable.nonneg_of_iteratedDeriv_nonneg` for entire functions and versions
showing `f z ≥ f c` when all iterated derivatives except `f` itself are nonnegative.
-/

public section

open Complex

open scoped ComplexOrder

namespace DifferentiableOn

/--
theorem `nonneg_of_iteratedDeriv_nonneg` / 定理 `nonneg_of_iteratedDeriv_nonneg`

English:
theorem nonneg_of_iteratedDeriv_nonneg
  statement: {f : Complex -> Complex} {c : Complex} {r : Real}
  proof: by
  have H := taylorSeries_eq_on_ball' hz₂ hf
  rw [← sub_nonneg] at hz₁
  have hz' := eq_re_of_ofReal_le hz₁
  rw [hz'] at hz₁ H
  refine H ▸ tsum_nonneg fun n => ?_
  rw [← ofReal_natCast]; rw [← ofReal_pow]; rw [← ofReal_inv]; rw [eq_re_of_ofReal_le (h n)]; rw [← ofReal_mul]; rw [← ofReal_mul]
  norm_cast at hz₁ ⊢
  positivity [zero_re ▸ (Complex.le_def.mp (h n)).1]

中文:
定理 nonneg_of_iteratedDeriv_nonneg
  结论: {f : 复形 -> 复形} {c : 复形} {r : 实数}
  证明: by
  have H := taylorSeries_eq_on_ball' hz₂ hf
  rw [← sub_nonneg] at hz₁
  have hz' := eq_re_of_ofReal_le hz₁
  rw [hz'] at hz₁ H
  refine H ▸ tsum_nonneg fun n => ?_
  rw [← ofReal_natCast]; rw [← ofReal_pow]; rw [← ofReal_inv]; rw [eq_re_of_ofReal_le (h n)]; rw [← ofReal_mul]; rw [← ofReal_mul]
  norm_cast at hz₁ ⊢
  positivity [zero_re ▸ (Complex.le_def.mp (h n)).1]

Depends on / 依赖: Complex.le_def.mp, eq_re_of_ofReal_le, le_def, ofReal_inv, ofReal_mul, ofReal_natCast, ofReal_pow, sub_nonneg, taylorSeries_eq_on_ball, tsum_nonneg, zero_re
-/
theorem nonneg_of_iteratedDeriv_nonneg {f : Complex -> Complex} {c : Complex} {r : Real}
    (hf : DifferentiableOn Complex f (Metric.ball c r)) (h : forall n, 0 <= iteratedDeriv n f c) ⦃z : Complex⦄
    (hz₁ : c <= z) (hz₂ : z in Metric.ball c r) :
    0 <= f z := by
  have H := taylorSeries_eq_on_ball' hz₂ hf
  rw [← sub_nonneg] at hz₁
  have hz' := eq_re_of_ofReal_le hz₁
  rw [hz'] at hz₁ H
  refine H ▸ tsum_nonneg fun n => ?_
  rw [← ofReal_natCast]; rw [← ofReal_pow]; rw [← ofReal_inv]; rw [eq_re_of_ofReal_le (h n)]; rw [← ofReal_mul]; rw [← ofReal_mul]
  norm_cast at hz₁ ⊢
  positivity [zero_re ▸ (Complex.le_def.mp (h n)).1]

end DifferentiableOn

namespace Differentiable

/--
theorem `nonneg_of_iteratedDeriv_nonneg` / 定理 `nonneg_of_iteratedDeriv_nonneg`

English:
theorem nonneg_of_iteratedDeriv_nonneg
  statement: {f : Complex -> Complex} (hf : Differentiable Complex f) {c : Complex}
  proof: by
  refine hf.differentiableOn.nonneg_of_iteratedDeriv_nonneg (r := (z - c).re + 1) h hz ?_
  rw [← sub_nonneg] at hz
  rw [Metric.mem_ball]; rw [dist_eq]; rw [eq_re_of_ofReal_le hz]
  simpa only [Complex.norm_of_nonneg (nonneg_iff.mp hz).1] using! lt_add_one _

中文:
定理 nonneg_of_iteratedDeriv_nonneg
  结论: {f : 复形 -> 复形} (hf : 可微 复形 f) {c : 复形}
  证明: by
  refine hf.differentiableOn.nonneg_of_iteratedDeriv_nonneg (r := (z - c).re + 1) h hz ?_
  rw [← sub_nonneg] at hz
  rw [Metric.mem_ball]; rw [dist_eq]; rw [eq_re_of_ofReal_le hz]
  simpa only [Complex.norm_of_nonneg (nonneg_iff.mp hz).1] using! lt_add_one _

Depends on / 依赖: Complex.norm_of_nonneg, Metric, Metric.mem_ball, differentiableOn, dist_eq, eq_re_of_ofReal_le, hf.differentiableOn.nonneg_of_iteratedDeriv_nonneg, lt_add_one, mem_ball, nonneg_iff, nonneg_iff.mp, nonneg_of_iteratedDeriv_nonneg, norm_of_nonneg, sub_nonneg
-/
theorem nonneg_of_iteratedDeriv_nonneg {f : Complex -> Complex} (hf : Differentiable Complex f) {c : Complex}
    (h : forall n, 0 <= iteratedDeriv n f c) ⦃z : Complex⦄ (hz : c <= z) :
    0 <= f z := by
  refine hf.differentiableOn.nonneg_of_iteratedDeriv_nonneg (r := (z - c).re + 1) h hz ?_
  rw [← sub_nonneg] at hz
  rw [Metric.mem_ball]; rw [dist_eq]; rw [eq_re_of_ofReal_le hz]
  simpa only [Complex.norm_of_nonneg (nonneg_iff.mp hz).1] using! lt_add_one _

/--
theorem `apply_le_of_iteratedDeriv_nonneg` / 定理 `apply_le_of_iteratedDeriv_nonneg`

English:
theorem apply_le_of_iteratedDeriv_nonneg
  statement: {f : Complex -> Complex} {c : Complex} (hf : Differentiable Complex f)
  proof: by
  have h' (n : Nat) : 0 <= iteratedDeriv n (f · - f c) c := by
    cases n with
    | zero => simp only [iteratedDeriv_zero, sub_self, le_refl]
    | succ n =>
      specialize h (n + 1) n.succ_ne_zero
      rw [iteratedDeriv_succ'] at h ⊢
      rwa [funext fun x => deriv_sub_const (f := f) (x := x) (f c)]
exact sub_nonneg.mp nonneg_of_iteratedDeriv_nonneg (hf.sub_const _) h' hz

中文:
定理 apply_le_of_iteratedDeriv_nonneg
  结论: {f : 复形 -> 复形} {c : 复形} (hf : 可微 复形 f)
  证明: by
  have h' (n : Nat) : 0 <= iteratedDeriv n (f · - f c) c := by
    cases n with
    | zero => simp only [iteratedDeriv_zero, sub_self, le_refl]
    | succ n =>
      specialize h (n + 1) n.succ_ne_zero
      rw [iteratedDeriv_succ'] at h ⊢
      rwa [funext fun x => deriv_sub_const (f := f) (x := x) (f c)]
exact sub_nonneg.mp nonneg_of_iteratedDeriv_nonneg (hf.sub_const _) h' hz

Depends on / 依赖: deriv_sub_const, hf.sub_const, iteratedDeriv, iteratedDeriv_succ, iteratedDeriv_zero, le_refl, n.succ_ne_zero, nonneg_of_iteratedDeriv_nonneg, specialize, sub_const, sub_nonneg, sub_nonneg.mp, sub_self, succ_ne_zero
-/
theorem apply_le_of_iteratedDeriv_nonneg {f : Complex -> Complex} {c : Complex} (hf : Differentiable Complex f)
    (h : forall n != 0, 0 <= iteratedDeriv n f c) ⦃z : Complex⦄ (hz : c <= z) :
    f c <= f z := by
  have h' (n : Nat) : 0 <= iteratedDeriv n (f · - f c) c := by
    cases n with
    | zero => simp only [iteratedDeriv_zero, sub_self, le_refl]
    | succ n =>
      specialize h (n + 1) n.succ_ne_zero
      rw [iteratedDeriv_succ'] at h ⊢
      rwa [funext fun x => deriv_sub_const (f := f) (x := x) (f c)]
exact sub_nonneg.mp nonneg_of_iteratedDeriv_nonneg (hf.sub_const _) h' hz

/--
theorem `apply_le_of_iteratedDeriv_alternating` / 定理 `apply_le_of_iteratedDeriv_alternating`

English:
theorem apply_le_of_iteratedDeriv_alternating
  statement: {f : Complex -> Complex} {c : Complex} (hf : Differentiable Complex f)
  proof: by
  convert!
    apply_le_of_iteratedDeriv_nonneg (f := fun z => f (-z)) (hf.comp <| differentiable_neg)
      (fun n hn => ?_) (neg_le_neg_iff.mpr hz) using 1
  · simp only [neg_neg]
  · simp only [neg_neg]
  · simpa only [iteratedDeriv_comp_neg, neg_neg, smul_eq_mul] using h n hn

中文:
定理 apply_le_of_iteratedDeriv_alternating
  结论: {f : 复形 -> 复形} {c : 复形} (hf : 可微 复形 f)
  证明: by
  convert!
    apply_le_of_iteratedDeriv_nonneg (f := fun z => f (-z)) (hf.comp <| differentiable_neg)
      (fun n hn => ?_) (neg_le_neg_iff.mpr hz) using 1
  · simp only [neg_neg]
  · simp only [neg_neg]
  · simpa only [iteratedDeriv_comp_neg, neg_neg, smul_eq_mul] using h n hn

Depends on / 依赖: apply_le_of_iteratedDeriv_nonneg, convert, differentiable_neg, hf.comp, iteratedDeriv_comp_neg, neg_le_neg_iff, neg_le_neg_iff.mpr, neg_neg, smul_eq_mul
-/
theorem apply_le_of_iteratedDeriv_alternating {f : Complex -> Complex} {c : Complex} (hf : Differentiable Complex f)
    (h : forall n != 0, 0 <= (-1) ^ n * iteratedDeriv n f c) ⦃z : Complex⦄ (hz : z <= c) :
    f c <= f z := by
  convert!
    apply_le_of_iteratedDeriv_nonneg (f := fun z => f (-z)) (hf.comp <| differentiable_neg)
      (fun n hn => ?_) (neg_le_neg_iff.mpr hz) using 1
  · simp only [neg_neg]
  · simp only [neg_neg]
  · simpa only [iteratedDeriv_comp_neg, neg_neg, smul_eq_mul] using h n hn

end Differentiable
