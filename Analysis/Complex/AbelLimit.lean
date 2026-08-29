/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Peel
public import Mathlib.Tactic.Positivity

/-!
# Abel's limit theorem

If a real or complex power series for a function has radius of convergence 1 and the series is only
known to converge conditionally at 1, Abel's limit theorem gives the value at 1 as the limit of the
function at 1 from the left. "Left" for complex numbers means within a fixed cone opening to the
left with angle less than `π`.

## Main theorems

* `Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone`:
  Abel's limit theorem for complex power series.
* `Real.tendsto_tsum_powerSeries_nhdsWithin_lt`: Abel's limit theorem for real power series.

## References

* https://planetmath.org/proofofabelslimittheorem
* https://en.wikipedia.org/wiki/Abel%27s_theorem
-/

@[expose] public section


open Filter Finset

open scoped Topology

namespace Complex

section StolzSet

open Real

/--
Definition of `stolzSet` / `stolzSet` 的定义

English:
definition stolzSet
  signature: (M : Real)
  body: {z | ‖z‖ < 1 ∧ ‖1 - z‖ < M * (1 - ‖z‖)}

中文:
定义 stolzSet
  签名: (M : 实数)
  定义体: {z | ‖z‖ < 1 ∧ ‖1 - z‖ < M * (1 - ‖z‖)}
-/
def stolzSet (M : Real) : Set Complex := {z | ‖z‖ < 1 ∧ ‖1 - z‖ < M * (1 - ‖z‖)}

/--
Definition of `stolzCone` / `stolzCone` 的定义

English:
definition stolzCone
  signature: (s : Real)
  body: {z | |z.im| < s * (1 - z.re)}

中文:
定义 stolzCone
  签名: (s : 实数)
  定义体: {z | |z.im| < s * (1 - z.re)}

Depends on / 依赖: z.im, z.re
-/
def stolzCone (s : Real) : Set Complex := {z | |z.im| < s * (1 - z.re)}

/--
theorem `stolzSet_empty` / 定理 `stolzSet_empty`

English:
theorem stolzSet_empty
  given: {M : Real} (hM : M <= 1)
  statement: stolzSet M = ∅
  proof: by
  ext z
  rw [stolzSet]; rw [Set.mem_ofPred]; rw [Set.mem_empty_iff_false]; rw [iff_false]; rw [not_and]; rw [not_lt]; rw [← sub_pos]
  intro zn
  calc
    _ <= 1 * (1 - ‖z‖) := by gcongr
    _ = ‖(1 : Complex)‖ - ‖z‖ := by rw [one_mul, norm_one]
    _ <= _ := norm_sub_norm_le _ _

中文:
定理 stolzSet_empty
  条件: {M : 实数} (hM : M <= 1)
  结论: stolzSet M = ∅
  证明: by
  ext z
  rw [stolzSet]; rw [Set.mem_ofPred]; rw [Set.mem_empty_iff_false]; rw [iff_false]; rw [not_and]; rw [not_lt]; rw [← sub_pos]
  intro zn
  calc
    _ <= 1 * (1 - ‖z‖) := by gcongr
    _ = ‖(1 : Complex)‖ - ‖z‖ := by rw [one_mul, norm_one]
    _ <= _ := norm_sub_norm_le _ _

Depends on / 依赖: Set.mem_empty_iff_false, Set.mem_ofPred, iff_false, mem_empty_iff_false, mem_ofPred, norm_one, norm_sub_norm_le, not_and, not_lt, one_mul, stolzSet, sub_pos
-/
theorem stolzSet_empty {M : Real} (hM : M <= 1) : stolzSet M = ∅ := by
  ext z
  rw [stolzSet]; rw [Set.mem_ofPred]; rw [Set.mem_empty_iff_false]; rw [iff_false]; rw [not_and]; rw [not_lt]; rw [← sub_pos]
  intro zn
  calc
    _ <= 1 * (1 - ‖z‖) := by gcongr
    _ = ‖(1 : Complex)‖ - ‖z‖ := by rw [one_mul, norm_one]
    _ <= _ := norm_sub_norm_le _ _

/--
theorem `nhdsWithin_lt_le_nhdsWithin_stolzSet` / 定理 `nhdsWithin_lt_le_nhdsWithin_stolzSet`

English:
theorem nhdsWithin_lt_le_nhdsWithin_stolzSet
  given: {M : Real} (hM : 1 < M)
  proof: by
  rw [← tendsto_id']
refine tendsto_map' tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ofReal
    (tendsto_nhdsWithin_of_tendsto_nhds <| ofRealCLM.continuous.tendsto' 1 1 rfl) ?_
  simp only [eventually_iff, mem_nhdsWithin]
  refine ⟨Set.Ioo 0 2, isOpen_Ioo, by simp, fun x hx => ?_⟩
  push _ in _ at hx
  simp only [Set.mem_ofPred_eq, stolzSet, ← ofReal_one, ← ofReal_sub, norm_real,
norm_of_nonneg hx.1.1.le, norm_of_nonneg (sub_pos.mpr hx.2).le]
  exact ⟨hx.2, lt_mul_left (sub_pos.mpr hx.2) hM⟩

中文:
定理 nhdsWithin_lt_le_nhdsWithin_stolzSet
  条件: {M : 实数} (hM : 1 < M)
  证明: by
  rw [← tendsto_id']
refine tendsto_map' tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ofReal
    (tendsto_nhdsWithin_of_tendsto_nhds <| ofRealCLM.continuous.tendsto' 1 1 rfl) ?_
  simp only [eventually_iff, mem_nhdsWithin]
  refine ⟨Set.Ioo 0 2, isOpen_Ioo, by simp, fun x hx => ?_⟩
  push _ in _ at hx
  simp only [Set.mem_ofPred_eq, stolzSet, ← ofReal_one, ← ofReal_sub, norm_real,
norm_of_nonneg hx.1.1.le, norm_of_nonneg (sub_pos.mpr hx.2).le]
  exact ⟨hx.2, lt_mul_left (sub_pos.mpr hx.2) hM⟩

Depends on / 依赖: Set.Ioo, Set.mem_ofPred_eq, continuous, eventually_iff, isOpen_Ioo, lt_mul_left, mem_nhdsWithin, mem_ofPred_eq, norm_of_nonneg, norm_real, ofReal, ofRealCLM, ofRealCLM.continuous.tendsto, ofReal_one, ofReal_sub, stolzSet, sub_pos, sub_pos.mpr, tendsto, tendsto_id
-/
theorem nhdsWithin_lt_le_nhdsWithin_stolzSet {M : Real} (hM : 1 < M) :
    (𝓝[<] 1).map ofReal <= 𝓝[stolzSet M] 1 := by
  rw [← tendsto_id']
refine tendsto_map' tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ofReal
    (tendsto_nhdsWithin_of_tendsto_nhds <| ofRealCLM.continuous.tendsto' 1 1 rfl) ?_
  simp only [eventually_iff, mem_nhdsWithin]
  refine ⟨Set.Ioo 0 2, isOpen_Ioo, by simp, fun x hx => ?_⟩
  push _ in _ at hx
  simp only [Set.mem_ofPred_eq, stolzSet, ← ofReal_one, ← ofReal_sub, norm_real,
norm_of_nonneg hx.1.1.le, norm_of_nonneg (sub_pos.mpr hx.2).le]
  exact ⟨hx.2, lt_mul_left (sub_pos.mpr hx.2) hM⟩

-- An ugly technical lemma
/--
lemma `stolzCone_subset_stolzSet_aux'` / 引理 `stolzCone_subset_stolzSet_aux'`

English:
lemma stolzCone_subset_stolzSet_aux'
  given: (s : Real)
  proof: by
  refine ⟨2 * √(1 + s ^ 2) + 1, 1 / (1 + s ^ 2), by positivity, by positivity,
    fun x y hx₀ hx₁ hy => ?_⟩
  have H : √((1 - x) ^ 2 + y ^ 2) <= 1 - x / 2 := by
    calc √((1 - x) ^ 2 + y ^ 2)
_ <= √((1 - x) ^ 2 + (s * x) ^ 2) := sqrt_le_sqrt by rw [← sq_abs y]; gcongr
      _ = √(1 - 2 * x + (1 + s ^ 2) * x * x) := by congr 1; ring
      _ <= √(1 - 2 * x + (1 + s ^ 2) * (1 / (1 + s ^ 2)) * x) := by gcongr
      _ = √(1 - x) := by congr 1; field
      _ <= 1 - x / 2 := by
        simp_rw [sub_eq_add_neg, ← neg_div]
refine sqrt_one_add_le neg_le_neg_iff.mpr (hx₁.trans_le ?_).le
        rw [div_le_one (by positivity)]
exact le_add_of_nonneg_right sq_nonneg s
  calc √(x ^ 2 + y ^ 2)
    _ <= √(x ^ 2 + (s * x) ^ 2) := by rw [← sq_abs y]; gcongr
    _ = √((1 + s ^ 2) * x ^ 2) := by congr; ring
    _ = √(1 + s ^ 2) * x := by rw [sqrt_mul' _ (sq_nonneg x), sqrt_sq hx₀.le]
    _ = 2 * √(1 + s ^ 2) * (x / 2) := by ring
    _ < (2 * √(1 + s ^ 2) + 1) * (x / 2) := by gcongr; exact lt_add_one _
    _ <= _ := by gcongr; exact le_sub_comm.mpr H

中文:
引理 stolzCone_subset_stolzSet_aux'
  条件: (s : 实数)
  证明: by
  refine ⟨2 * √(1 + s ^ 2) + 1, 1 / (1 + s ^ 2), by positivity, by positivity,
    fun x y hx₀ hx₁ hy => ?_⟩
  have H : √((1 - x) ^ 2 + y ^ 2) <= 1 - x / 2 := by
    calc √((1 - x) ^ 2 + y ^ 2)
_ <= √((1 - x) ^ 2 + (s * x) ^ 2) := sqrt_le_sqrt by rw [← sq_abs y]; gcongr
      _ = √(1 - 2 * x + (1 + s ^ 2) * x * x) := by congr 1; ring
      _ <= √(1 - 2 * x + (1 + s ^ 2) * (1 / (1 + s ^ 2)) * x) := by gcongr
      _ = √(1 - x) := by congr 1; field
      _ <= 1 - x / 2 := by
        simp_rw [sub_eq_add_neg, ← neg_div]
refine sqrt_one_add_le neg_le_neg_iff.mpr (hx₁.trans_le ?_).le
        rw [div_le_one (by positivity)]
exact le_add_of_nonneg_right sq_nonneg s
  calc √(x ^ 2 + y ^ 2)
    _ <= √(x ^ 2 + (s * x) ^ 2) := by rw [← sq_abs y]; gcongr
    _ = √((1 + s ^ 2) * x ^ 2) := by congr; ring
    _ = √(1 + s ^ 2) * x := by rw [sqrt_mul' _ (sq_nonneg x), sqrt_sq hx₀.le]
    _ = 2 * √(1 + s ^ 2) * (x / 2) := by ring
    _ < (2 * √(1 + s ^ 2) + 1) * (x / 2) := by gcongr; exact lt_add_one _
    _ <= _ := by gcongr; exact le_sub_comm.mpr H
-/
private lemma stolzCone_subset_stolzSet_aux' (s : Real) :
    exists M ε, 0 < M ∧ 0 < ε ∧ forall x y, 0 < x -> x < ε -> |y| < s * x ->
      √(x ^ 2 + y ^ 2) < M * (1 - √((1 - x) ^ 2 + y ^ 2)) := by
  refine ⟨2 * √(1 + s ^ 2) + 1, 1 / (1 + s ^ 2), by positivity, by positivity,
    fun x y hx₀ hx₁ hy => ?_⟩
  have H : √((1 - x) ^ 2 + y ^ 2) <= 1 - x / 2 := by
    calc √((1 - x) ^ 2 + y ^ 2)
_ <= √((1 - x) ^ 2 + (s * x) ^ 2) := sqrt_le_sqrt by rw [← sq_abs y]; gcongr
      _ = √(1 - 2 * x + (1 + s ^ 2) * x * x) := by congr 1; ring
      _ <= √(1 - 2 * x + (1 + s ^ 2) * (1 / (1 + s ^ 2)) * x) := by gcongr
      _ = √(1 - x) := by congr 1; field
      _ <= 1 - x / 2 := by
        simp_rw [sub_eq_add_neg, ← neg_div]
refine sqrt_one_add_le neg_le_neg_iff.mpr (hx₁.trans_le ?_).le
        rw [div_le_one (by positivity)]
exact le_add_of_nonneg_right sq_nonneg s
  calc √(x ^ 2 + y ^ 2)
    _ <= √(x ^ 2 + (s * x) ^ 2) := by rw [← sq_abs y]; gcongr
    _ = √((1 + s ^ 2) * x ^ 2) := by congr; ring
    _ = √(1 + s ^ 2) * x := by rw [sqrt_mul' _ (sq_nonneg x), sqrt_sq hx₀.le]
    _ = 2 * √(1 + s ^ 2) * (x / 2) := by ring
    _ < (2 * √(1 + s ^ 2) + 1) * (x / 2) := by gcongr; exact lt_add_one _
    _ <= _ := by gcongr; exact le_sub_comm.mpr H

/--
lemma `stolzCone_subset_stolzSet_aux` / 引理 `stolzCone_subset_stolzSet_aux`

English:
lemma stolzCone_subset_stolzSet_aux
  given: {s : Real} (hs : 0 < s)
  proof: by
  peel stolzCone_subset_stolzSet_aux' s with M ε hM hε H
  rintro z ⟨hzl, hzr⟩
  rw [Set.mem_ofPred_eq]; rw [sub_lt_comm]; rw [← one_re]; rw [← sub_re] at hzl
  rw [stolzCone]; rw [Set.mem_ofPred_eq]; rw [← one_re]; rw [← sub_re] at hzr
  replace H :=
    H (1 - z).re z.im ((mul_pos_iff_of_pos_left hs).mp <| (abs_nonneg z.im).trans_lt hzr) hzl hzr
  have h : z.im ^ 2 = (1 - z).im ^ 2 := by
    simp only [sub_im, one_im, zero_sub, neg_sq]
  rw [h]; rw [← norm_eq_sqrt_sq_add_sq]; rw [← h]; rw [sub_re]; rw [one_re]; rw [sub_sub_cancel]; rw [← norm_eq_sqrt_sq_add_sq] at H
exact ⟨sub_pos.mp (mul_pos_iff_of_pos_left hM).mp (norm_nonneg _).trans_lt H, H⟩

中文:
引理 stolzCone_subset_stolzSet_aux
  条件: {s : 实数} (hs : 0 < s)
  证明: by
  peel stolzCone_subset_stolzSet_aux' s with M ε hM hε H
  rintro z ⟨hzl, hzr⟩
  rw [Set.mem_ofPred_eq]; rw [sub_lt_comm]; rw [← one_re]; rw [← sub_re] at hzl
  rw [stolzCone]; rw [Set.mem_ofPred_eq]; rw [← one_re]; rw [← sub_re] at hzr
  replace H :=
    H (1 - z).re z.im ((mul_pos_iff_of_pos_left hs).mp <| (abs_nonneg z.im).trans_lt hzr) hzl hzr
  have h : z.im ^ 2 = (1 - z).im ^ 2 := by
    simp only [sub_im, one_im, zero_sub, neg_sq]
  rw [h]; rw [← norm_eq_sqrt_sq_add_sq]; rw [← h]; rw [sub_re]; rw [one_re]; rw [sub_sub_cancel]; rw [← norm_eq_sqrt_sq_add_sq] at H
exact ⟨sub_pos.mp (mul_pos_iff_of_pos_left hM).mp (norm_nonneg _).trans_lt H, H⟩

Depends on / 依赖: Set.mem_ofPred_eq, abs_nonneg, mem_ofPred_eq, mul_pos_iff_of_pos_left, neg_sq, norm_eq_sqrt_sq_add_sq, one_im, one_re, replace, stolzCone, stolzCone_subset_stolzSet_aux, sub_im, sub_lt_comm, sub_re, trans_lt, z.im, zero_sub
-/
lemma stolzCone_subset_stolzSet_aux {s : Real} (hs : 0 < s) :
    exists M ε, 0 < M ∧ 0 < ε ∧ {z : Complex | 1 - ε < z.re} inter stolzCone s subseteq stolzSet M := by
  peel stolzCone_subset_stolzSet_aux' s with M ε hM hε H
  rintro z ⟨hzl, hzr⟩
  rw [Set.mem_ofPred_eq]; rw [sub_lt_comm]; rw [← one_re]; rw [← sub_re] at hzl
  rw [stolzCone]; rw [Set.mem_ofPred_eq]; rw [← one_re]; rw [← sub_re] at hzr
  replace H :=
    H (1 - z).re z.im ((mul_pos_iff_of_pos_left hs).mp <| (abs_nonneg z.im).trans_lt hzr) hzl hzr
  have h : z.im ^ 2 = (1 - z).im ^ 2 := by
    simp only [sub_im, one_im, zero_sub, neg_sq]
  rw [h]; rw [← norm_eq_sqrt_sq_add_sq]; rw [← h]; rw [sub_re]; rw [one_re]; rw [sub_sub_cancel]; rw [← norm_eq_sqrt_sq_add_sq] at H
exact ⟨sub_pos.mp (mul_pos_iff_of_pos_left hM).mp (norm_nonneg _).trans_lt H, H⟩

/--
lemma `nhdsWithin_stolzCone_le_nhdsWithin_stolzSet` / 引理 `nhdsWithin_stolzCone_le_nhdsWithin_stolzSet`

English:
lemma nhdsWithin_stolzCone_le_nhdsWithin_stolzSet
  given: {s : Real} (hs : 0 < s)
  proof: by
  obtain ⟨M, ε, _, hε, H⟩ := stolzCone_subset_stolzSet_aux hs
  use M
  rw [nhdsWithin_le_iff]; rw [mem_nhdsWithin]
  refine ⟨{w | 1 - ε < w.re}, isOpen_lt continuous_const continuous_re, ?_, H⟩
  simp only [Set.mem_ofPred_eq, one_re, sub_lt_self_iff, hε]

中文:
引理 nhdsWithin_stolzCone_le_nhdsWithin_stolzSet
  条件: {s : 实数} (hs : 0 < s)
  证明: by
  obtain ⟨M, ε, _, hε, H⟩ := stolzCone_subset_stolzSet_aux hs
  use M
  rw [nhdsWithin_le_iff]; rw [mem_nhdsWithin]
  refine ⟨{w | 1 - ε < w.re}, isOpen_lt continuous_const continuous_re, ?_, H⟩
  simp only [Set.mem_ofPred_eq, one_re, sub_lt_self_iff, hε]

Depends on / 依赖: Set.mem_ofPred_eq, continuous_const, continuous_re, isOpen_lt, mem_nhdsWithin, mem_ofPred_eq, nhdsWithin_le_iff, one_re, stolzCone_subset_stolzSet_aux, sub_lt_self_iff, w.re
-/
lemma nhdsWithin_stolzCone_le_nhdsWithin_stolzSet {s : Real} (hs : 0 < s) :
    exists M, 𝓝[stolzCone s] 1 <= 𝓝[stolzSet M] 1 := by
  obtain ⟨M, ε, _, hε, H⟩ := stolzCone_subset_stolzSet_aux hs
  use M
  rw [nhdsWithin_le_iff]; rw [mem_nhdsWithin]
  refine ⟨{w | 1 - ε < w.re}, isOpen_lt continuous_const continuous_re, ?_, H⟩
  simp only [Set.mem_ofPred_eq, one_re, sub_lt_self_iff, hε]

end StolzSet

variable {f : Nat -> Complex} {l : Complex}

/--
lemma `abel_aux` / 引理 `abel_aux`

English:
lemma abel_aux
  given: (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)) {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  let s := fun n => ∑ i in range n, f i
  have k := h.sub (summable_powerSeries_of_norm_lt_one h.cauchySeq hz).hasSum.tendsto_sum_nat
  simp_rw [← sum_sub_distrib, ← mul_one_sub, ← geom_sum_mul_neg, ← mul_assoc, ← sum_mul,
    mul_comm, mul_sum _ _ (f _), range_eq_Ico, ← sum_Ico_Ico_comm', ← range_eq_Ico,
    ← sum_mul] at k
  conv at k =>
    enter [1, n]
    rw [sum_congr (g := fun j => (∑ k in range n]; rw [f k - ∑ k in range (j + 1)]; rw [f k) * z ^ j)
      rfl (fun j hj => by congr 1; exact sum_Ico_eq_sub _ (mem_range.mp hj))]
  suffices Tendsto (fun n => (l - s n) * ∑ i in range n, z ^ i) atTop (𝓝 0) by
    simp_rw [mul_sum] at this
    replace this := (this.const_mul (1 - z)).add k
    conv at this =>
      enter [1, n]
      rw [← mul_add]; rw [← sum_add_distrib]
      enter [2, 2, i]
      rw [← add_mul]; rw [sub_add_sub_cancel]
    rwa [mul_zero, zero_add] at this
  rw [← zero_mul (-1 / (z - 1))]
  apply Tendsto.mul
  · simpa only [neg_zero, neg_sub] using (tendsto_sub_nhds_zero_iff.mpr h).neg
  · conv =>
      enter [1, n]
      rw [geom_sum_eq (by contrapose! hz; simp [hz]), sub_div, sub_eq_add_neg, ← neg_div]
    rw [← zero_add (-1 / (z - 1))]; rw [← zero_div (z - 1)]
    apply Tendsto.add (Tendsto.div_const (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz) (z - 1))
    simp only [zero_div, zero_add, tendsto_const_nhds_iff]

中文:
引理 abel_aux
  条件: (h : 收敛 (fun n => ∑ i in range n, f i) atTop (𝓝 l)) {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  let s := fun n => ∑ i in range n, f i
  have k := h.sub (summable_powerSeries_of_norm_lt_one h.cauchySeq hz).hasSum.tendsto_sum_nat
  simp_rw [← sum_sub_distrib, ← mul_one_sub, ← geom_sum_mul_neg, ← mul_assoc, ← sum_mul,
    mul_comm, mul_sum _ _ (f _), range_eq_Ico, ← sum_Ico_Ico_comm', ← range_eq_Ico,
    ← sum_mul] at k
  conv at k =>
    enter [1, n]
    rw [sum_congr (g := fun j => (∑ k in range n]; rw [f k - ∑ k in range (j + 1)]; rw [f k) * z ^ j)
      rfl (fun j hj => by congr 1; exact sum_Ico_eq_sub _ (mem_range.mp hj))]
  suffices Tendsto (fun n => (l - s n) * ∑ i in range n, z ^ i) atTop (𝓝 0) by
    simp_rw [mul_sum] at this
    replace this := (this.const_mul (1 - z)).add k
    conv at this =>
      enter [1, n]
      rw [← mul_add]; rw [← sum_add_distrib]
      enter [2, 2, i]
      rw [← add_mul]; rw [sub_add_sub_cancel]
    rwa [mul_zero, zero_add] at this
  rw [← zero_mul (-1 / (z - 1))]
  apply Tendsto.mul
  · simpa only [neg_zero, neg_sub] using (tendsto_sub_nhds_zero_iff.mpr h).neg
  · conv =>
      enter [1, n]
      rw [geom_sum_eq (by contrapose! hz; simp [hz]), sub_div, sub_eq_add_neg, ← neg_div]
    rw [← zero_add (-1 / (z - 1))]; rw [← zero_div (z - 1)]
    apply Tendsto.add (Tendsto.div_const (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz) (z - 1))
    simp only [zero_div, zero_add, tendsto_const_nhds_iff]

Depends on / 依赖: cauchySeq, geom_sum_mul_neg, h.cauchySeq, h.sub, hasSum, hasSum.tendsto_sum_nat, mem_ran, mul_assoc, mul_comm, mul_one_sub, mul_sum, range_eq_Ico, simp_rw, sum_Ico_Ico_comm, sum_Ico_eq_sub, sum_congr, sum_mul, sum_sub_distrib, summable_powerSeries_of_norm_lt_one, tendsto_sum_nat
-/
lemma abel_aux (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)) {z : Complex} (hz : ‖z‖ < 1) :
    Tendsto (fun n => (1 - z) * ∑ i in range n, (l - ∑ j in range (i + 1), f j) * z ^ i)
      atTop (𝓝 (l - ∑' n, f n * z ^ n)) := by
  let s := fun n => ∑ i in range n, f i
  have k := h.sub (summable_powerSeries_of_norm_lt_one h.cauchySeq hz).hasSum.tendsto_sum_nat
  simp_rw [← sum_sub_distrib, ← mul_one_sub, ← geom_sum_mul_neg, ← mul_assoc, ← sum_mul,
    mul_comm, mul_sum _ _ (f _), range_eq_Ico, ← sum_Ico_Ico_comm', ← range_eq_Ico,
    ← sum_mul] at k
  conv at k =>
    enter [1, n]
    rw [sum_congr (g := fun j => (∑ k in range n]; rw [f k - ∑ k in range (j + 1)]; rw [f k) * z ^ j)
      rfl (fun j hj => by congr 1; exact sum_Ico_eq_sub _ (mem_range.mp hj))]
  suffices Tendsto (fun n => (l - s n) * ∑ i in range n, z ^ i) atTop (𝓝 0) by
    simp_rw [mul_sum] at this
    replace this := (this.const_mul (1 - z)).add k
    conv at this =>
      enter [1, n]
      rw [← mul_add]; rw [← sum_add_distrib]
      enter [2, 2, i]
      rw [← add_mul]; rw [sub_add_sub_cancel]
    rwa [mul_zero, zero_add] at this
  rw [← zero_mul (-1 / (z - 1))]
  apply Tendsto.mul
  · simpa only [neg_zero, neg_sub] using (tendsto_sub_nhds_zero_iff.mpr h).neg
  · conv =>
      enter [1, n]
      rw [geom_sum_eq (by contrapose! hz; simp [hz]), sub_div, sub_eq_add_neg, ← neg_div]
    rw [← zero_add (-1 / (z - 1))]; rw [← zero_div (z - 1)]
    apply Tendsto.add (Tendsto.div_const (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz) (z - 1))
    simp only [zero_div, zero_add, tendsto_const_nhds_iff]

/--
theorem `tendsto_tsum_powerSeries_nhdsWithin_stolzSet` / 定理 `tendsto_tsum_powerSeries_nhdsWithin_stolzSet`

English:
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzSet
  proof: by
  -- If `M ≤ 1` the Stolz set is empty and the statement is trivial
  rcases le_or_gt M 1 with hM | hM
  · simp_rw [stolzSet_empty hM, nhdsWithin_empty, tendsto_bot]
  -- Abbreviations
  let s := fun n => ∑ i in range n, f i
  let g := fun z => ∑' n, f n * z ^ n
  have hm := Metric.tendsto_atTop.mp h
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [dist_eq_norm] at hm ⊢
  -- Introduce the "challenge" `ε`
  intro ε εpos
  -- First bound, handles the tail
  obtain ⟨B₁, hB₁⟩ := hm (ε / 4 / M) (by positivity)
  -- Second bound, handles the head
  let F := ∑ i in range B₁, ‖l - s (i + 1)‖
  use ε / 4 / (F + 1), by positivity
  intro z ⟨zn, zm⟩ zd
  have p := abel_aux h zn
  simp_rw [Metric.tendsto_atTop, dist_eq_norm, norm_sub_rev] at p
  -- Third bound, regarding the distance between `l - g z` and the rearranged sum
  obtain ⟨B₂, hB₂⟩ := p (ε / 2) (by positivity)
  clear hm p
  replace hB₂ := hB₂ (max B₁ B₂) (by simp)
  suffices ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ < ε / 2 by
    calc
      _ = ‖l - g z‖ := by rw [norm_sub_rev]
      _ = ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i +
          (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by rw [sub_add_cancel _]
      _ <= ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ +
          ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hB₂ this
      _ = _ := add_halves ε
  -- We break the rearranged sum along `B₁`
  calc
    _ = ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i +
        (1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [← mul_add]; rw [sum_range_add_sum_Ico _ (le_max_left B₁ B₂)]
    _ <= ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖(1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
    _ = ‖1 - z‖ * ‖∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖1 - z‖ * ‖∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [norm_mul]; rw [norm_mul]
    _ <= ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i +
        ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i := by
      gcongr <;> simp_rw [← norm_pow, ← norm_mul, norm_sum_le]
  -- then prove that the two pieces are each less than `ε / 4`
  have S₁ : ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ <= ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ := by
        gcongr; nth_rw 3 [← mul_one ‖_‖]
        gcongr; exact pow_le_one₀ (norm_nonneg _) zn.le
      _ <= ‖1 - z‖ * (F + 1) := by gcongr; linarith only
      _ < _ := by rwa [norm_sub_rev, lt_div_iff₀ (by positivity)] at zd
  have S₂ : ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ <= ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ε / 4 / M * ‖z‖ ^ i := by
        gcongr with i hi
        have := hB₁ (i + 1) (by linarith only [(mem_Ico.mp hi).1])
        rw [norm_sub_rev] at this
        exact this.le
      _ = ‖1 - z‖ * (ε / 4 / M) * ∑ i in Ico B₁ (max B₁ B₂), ‖z‖ ^ i := by
        rw [← mul_sum]; rw [← mul_assoc]
      _ <= ‖1 - z‖ * (ε / 4 / M) * ∑' i, ‖z‖ ^ i := by
        gcongr
        exact Summable.sum_le_tsum _ (fun _ _ => by positivity)
          (summable_geometric_of_lt_one (by positivity) zn)
      _ = ‖1 - z‖ * (ε / 4 / M) / (1 - ‖z‖) := by
        rw [tsum_geometric_of_lt_one (by positivity) zn]; rw [← div_eq_mul_inv]
      _ < M * (1 - ‖z‖) * (ε / 4 / M) / (1 - ‖z‖) := by gcongr
      _ = _ := by
        rw [← mul_rotate]; rw [mul_div_cancel_right₀ _ (by linarith only [zn]),
          div_mul_cancel₀ _ (by linarith only [hM])]
  convert! add_lt_add S₁ S₂ using 1
  linarith only

中文:
定理 tendsto_tsum_powerSeries_nhdsWithin_stolzSet
  证明: by
  -- If `M ≤ 1` the Stolz set is empty and the statement is trivial
  rcases le_or_gt M 1 with hM | hM
  · simp_rw [stolzSet_empty hM, nhdsWithin_empty, tendsto_bot]
  -- Abbreviations
  let s := fun n => ∑ i in range n, f i
  let g := fun z => ∑' n, f n * z ^ n
  have hm := Metric.tendsto_atTop.mp h
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [dist_eq_norm] at hm ⊢
  -- Introduce the "challenge" `ε`
  intro ε εpos
  -- First bound, handles the tail
  obtain ⟨B₁, hB₁⟩ := hm (ε / 4 / M) (by positivity)
  -- Second bound, handles the head
  let F := ∑ i in range B₁, ‖l - s (i + 1)‖
  use ε / 4 / (F + 1), by positivity
  intro z ⟨zn, zm⟩ zd
  have p := abel_aux h zn
  simp_rw [Metric.tendsto_atTop, dist_eq_norm, norm_sub_rev] at p
  -- Third bound, regarding the distance between `l - g z` and the rearranged sum
  obtain ⟨B₂, hB₂⟩ := p (ε / 2) (by positivity)
  clear hm p
  replace hB₂ := hB₂ (max B₁ B₂) (by simp)
  suffices ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ < ε / 2 by
    calc
      _ = ‖l - g z‖ := by rw [norm_sub_rev]
      _ = ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i +
          (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by rw [sub_add_cancel _]
      _ <= ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ +
          ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hB₂ this
      _ = _ := add_halves ε
  -- We break the rearranged sum along `B₁`
  calc
    _ = ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i +
        (1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [← mul_add]; rw [sum_range_add_sum_Ico _ (le_max_left B₁ B₂)]
    _ <= ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖(1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
    _ = ‖1 - z‖ * ‖∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖1 - z‖ * ‖∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [norm_mul]; rw [norm_mul]
    _ <= ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i +
        ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i := by
      gcongr <;> simp_rw [← norm_pow, ← norm_mul, norm_sum_le]
  -- then prove that the two pieces are each less than `ε / 4`
  have S₁ : ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ <= ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ := by
        gcongr; nth_rw 3 [← mul_one ‖_‖]
        gcongr; exact pow_le_one₀ (norm_nonneg _) zn.le
      _ <= ‖1 - z‖ * (F + 1) := by gcongr; linarith only
      _ < _ := by rwa [norm_sub_rev, lt_div_iff₀ (by positivity)] at zd
  have S₂ : ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ <= ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ε / 4 / M * ‖z‖ ^ i := by
        gcongr with i hi
        have := hB₁ (i + 1) (by linarith only [(mem_Ico.mp hi).1])
        rw [norm_sub_rev] at this
        exact this.le
      _ = ‖1 - z‖ * (ε / 4 / M) * ∑ i in Ico B₁ (max B₁ B₂), ‖z‖ ^ i := by
        rw [← mul_sum]; rw [← mul_assoc]
      _ <= ‖1 - z‖ * (ε / 4 / M) * ∑' i, ‖z‖ ^ i := by
        gcongr
        exact Summable.sum_le_tsum _ (fun _ _ => by positivity)
          (summable_geometric_of_lt_one (by positivity) zn)
      _ = ‖1 - z‖ * (ε / 4 / M) / (1 - ‖z‖) := by
        rw [tsum_geometric_of_lt_one (by positivity) zn]; rw [← div_eq_mul_inv]
      _ < M * (1 - ‖z‖) * (ε / 4 / M) / (1 - ‖z‖) := by gcongr
      _ = _ := by
        rw [← mul_rotate]; rw [mul_div_cancel_right₀ _ (by linarith only [zn]),
          div_mul_cancel₀ _ (by linarith only [hM])]
  convert! add_lt_add S₁ S₂ using 1
  linarith only
-/
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzSet
    (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)) {M : Real} :
    Tendsto (fun z => ∑' n, f n * z ^ n) (𝓝[stolzSet M] 1) (𝓝 l) := by
  -- If `M ≤ 1` the Stolz set is empty and the statement is trivial
  rcases le_or_gt M 1 with hM | hM
  · simp_rw [stolzSet_empty hM, nhdsWithin_empty, tendsto_bot]
  -- Abbreviations
  let s := fun n => ∑ i in range n, f i
  let g := fun z => ∑' n, f n * z ^ n
  have hm := Metric.tendsto_atTop.mp h
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [dist_eq_norm] at hm ⊢
  -- Introduce the "challenge" `ε`
  intro ε εpos
  -- First bound, handles the tail
  obtain ⟨B₁, hB₁⟩ := hm (ε / 4 / M) (by positivity)
  -- Second bound, handles the head
  let F := ∑ i in range B₁, ‖l - s (i + 1)‖
  use ε / 4 / (F + 1), by positivity
  intro z ⟨zn, zm⟩ zd
  have p := abel_aux h zn
  simp_rw [Metric.tendsto_atTop, dist_eq_norm, norm_sub_rev] at p
  -- Third bound, regarding the distance between `l - g z` and the rearranged sum
  obtain ⟨B₂, hB₂⟩ := p (ε / 2) (by positivity)
  clear hm p
  replace hB₂ := hB₂ (max B₁ B₂) (by simp)
  suffices ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ < ε / 2 by
    calc
      _ = ‖l - g z‖ := by rw [norm_sub_rev]
      _ = ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i +
          (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by rw [sub_add_cancel _]
      _ <= ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ +
          ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hB₂ this
      _ = _ := add_halves ε
  -- We break the rearranged sum along `B₁`
  calc
    _ = ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i +
        (1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [← mul_add]; rw [sum_range_add_sum_Ico _ (le_max_left B₁ B₂)]
    _ <= ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖(1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
    _ = ‖1 - z‖ * ‖∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖1 - z‖ * ‖∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [norm_mul]; rw [norm_mul]
    _ <= ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i +
        ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i := by
      gcongr <;> simp_rw [← norm_pow, ← norm_mul, norm_sum_le]
  -- then prove that the two pieces are each less than `ε / 4`
  have S₁ : ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ <= ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ := by
        gcongr; nth_rw 3 [← mul_one ‖_‖]
        gcongr; exact pow_le_one₀ (norm_nonneg _) zn.le
      _ <= ‖1 - z‖ * (F + 1) := by gcongr; linarith only
      _ < _ := by rwa [norm_sub_rev, lt_div_iff₀ (by positivity)] at zd
  have S₂ : ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ <= ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ε / 4 / M * ‖z‖ ^ i := by
        gcongr with i hi
        have := hB₁ (i + 1) (by linarith only [(mem_Ico.mp hi).1])
        rw [norm_sub_rev] at this
        exact this.le
      _ = ‖1 - z‖ * (ε / 4 / M) * ∑ i in Ico B₁ (max B₁ B₂), ‖z‖ ^ i := by
        rw [← mul_sum]; rw [← mul_assoc]
      _ <= ‖1 - z‖ * (ε / 4 / M) * ∑' i, ‖z‖ ^ i := by
        gcongr
        exact Summable.sum_le_tsum _ (fun _ _ => by positivity)
          (summable_geometric_of_lt_one (by positivity) zn)
      _ = ‖1 - z‖ * (ε / 4 / M) / (1 - ‖z‖) := by
        rw [tsum_geometric_of_lt_one (by positivity) zn]; rw [← div_eq_mul_inv]
      _ < M * (1 - ‖z‖) * (ε / 4 / M) / (1 - ‖z‖) := by gcongr
      _ = _ := by
        rw [← mul_rotate]; rw [mul_div_cancel_right₀ _ (by linarith only [zn]),
          div_mul_cancel₀ _ (by linarith only [hM])]
  convert! add_lt_add S₁ S₂ using 1
  linarith only

/--
theorem `tendsto_tsum_powerSeries_nhdsWithin_stolzCone` / 定理 `tendsto_tsum_powerSeries_nhdsWithin_stolzCone`

English:
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzCone
  proof: (tendsto_tsum_powerSeries_nhdsWithin_stolzSet h).mono_left
    (nhdsWithin_stolzCone_le_nhdsWithin_stolzSet hs).choose_spec

中文:
定理 tendsto_tsum_powerSeries_nhdsWithin_stolzCone
  证明: (tendsto_tsum_powerSeries_nhdsWithin_stolzSet h).mono_left
    (nhdsWithin_stolzCone_le_nhdsWithin_stolzSet hs).choose_spec

Depends on / 依赖: choose_spec, mono_left, nhdsWithin_stolzCone_le_nhdsWithin_stolzSet, tendsto_tsum_powerSeries_nhdsWithin_stolzSet
-/
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzCone
    (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)) {s : Real} (hs : 0 < s) :
    Tendsto (fun z => ∑' n, f n * z ^ n) (𝓝[stolzCone s] 1) (𝓝 l) :=
  (tendsto_tsum_powerSeries_nhdsWithin_stolzSet h).mono_left
    (nhdsWithin_stolzCone_le_nhdsWithin_stolzSet hs).choose_spec

/--
theorem `tendsto_tsum_powerSeries_nhdsWithin_lt` / 定理 `tendsto_tsum_powerSeries_nhdsWithin_lt`

English:
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
  proof: (tendsto_tsum_powerSeries_nhdsWithin_stolzSet (M := 2) h).mono_left
    (nhdsWithin_lt_le_nhdsWithin_stolzSet one_lt_two)

中文:
定理 tendsto_tsum_powerSeries_nhdsWithin_lt
  证明: (tendsto_tsum_powerSeries_nhdsWithin_stolzSet (M := 2) h).mono_left
    (nhdsWithin_lt_le_nhdsWithin_stolzSet one_lt_two)

Depends on / 依赖: mono_left, nhdsWithin_lt_le_nhdsWithin_stolzSet, one_lt_two, tendsto_tsum_powerSeries_nhdsWithin_stolzSet
-/
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)) :
    Tendsto (fun z => ∑' n, f n * z ^ n) ((𝓝[<] 1).map ofReal) (𝓝 l) :=
  (tendsto_tsum_powerSeries_nhdsWithin_stolzSet (M := 2) h).mono_left
    (nhdsWithin_lt_le_nhdsWithin_stolzSet one_lt_two)

end Complex

namespace Real

open Complex

variable {f : Nat -> Real} {l : Real}

/--
theorem `tendsto_tsum_powerSeries_nhdsWithin_lt` / 定理 `tendsto_tsum_powerSeries_nhdsWithin_lt`

English:
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
  proof: by
  have m : (𝓝 l).map ofReal <= 𝓝 ↑l := ofRealCLM.continuous.tendsto l
  replace h := (tendsto_map.comp h).mono_right m
  rw [Function.comp_def] at h
  push_cast at h
  replace h := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h
  rw [tendsto_map'_iff] at h
  rw [Metric.tendsto_nhdsWithin_nhds] at h ⊢
  convert! h
  simp_rw [Function.comp_apply, dist_eq_norm]
  norm_cast

中文:
定理 tendsto_tsum_powerSeries_nhdsWithin_lt
  证明: by
  have m : (𝓝 l).map ofReal <= 𝓝 ↑l := ofRealCLM.continuous.tendsto l
  replace h := (tendsto_map.comp h).mono_right m
  rw [Function.comp_def] at h
  push_cast at h
  replace h := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h
  rw [tendsto_map'_iff] at h
  rw [Metric.tendsto_nhdsWithin_nhds] at h ⊢
  convert! h
  simp_rw [Function.comp_apply, dist_eq_norm]
  norm_cast

Depends on / 依赖: Complex.tendsto_tsum_powerSeries_nhdsWithin_lt, Function, Function.comp_apply, Function.comp_def, Metric, Metric.tendsto_nhdsWithin_nhds, _iff, comp_apply, comp_def, continuous, convert, dist_eq_norm, mono_right, ofReal, ofRealCLM, ofRealCLM.continuous.tendsto, replace, simp_rw, tendsto, tendsto_map
-/
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)) :
    Tendsto (fun x => ∑' n, f n * x ^ n) (𝓝[<] 1) (𝓝 l) := by
  have m : (𝓝 l).map ofReal <= 𝓝 ↑l := ofRealCLM.continuous.tendsto l
  replace h := (tendsto_map.comp h).mono_right m
  rw [Function.comp_def] at h
  push_cast at h
  replace h := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h
  rw [tendsto_map'_iff] at h
  rw [Metric.tendsto_nhdsWithin_nhds] at h ⊢
  convert! h
  simp_rw [Function.comp_apply, dist_eq_norm]
  norm_cast

end Real
