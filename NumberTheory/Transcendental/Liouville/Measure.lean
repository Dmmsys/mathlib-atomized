/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.Residual
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.Analysis.PSeries

/-!
# Volume of the set of Liouville numbers

In this file we prove that the set of Liouville numbers with exponent (irrationality measure)
strictly greater than two is a set of Lebesgue measure zero, see
`volume_iUnion_setOfPred_liouvilleWith`.

Since this set is a residual set, we show that the filters `residual` and `ae volume` are disjoint.
These filters correspond to two common notions of genericity on `ℝ`: residual sets and sets of full
measure. The fact that the filters are disjoint means that two mutually exclusive properties can be
“generic” at the same time (in the sense of different “genericity” filters).

## Tags

Liouville number, Lebesgue measure, residual, generic property
-/

public section

open scoped Filter ENNReal Topology NNReal

open Filter Set Metric MeasureTheory Real

/--
theorem `setOfPred_liouvilleWith_subset_aux` / 定理 `setOfPred_liouvilleWith_subset_aux`

English:
theorem setOfPred_liouvilleWith_subset_aux
  proof: by
  rintro x ⟨p, hp, hxp⟩
  rcases exists_nat_one_div_lt (sub_pos.2 hp) with ⟨n, hn⟩
  rw [lt_sub_iff_add_lt'] at hn
  suffices forall y : Real, LiouvilleWith p y -> y in Ico (0 : Real) 1 -> existsᶠ b : Nat in atTop,
      exists a in Finset.Icc (0 : Int) b, |y - a / b| < 1 / (b : Real) ^ (2 + 1 / (n + 1 : Nat) : Real) by
    simp only [mem_iUnion, mem_preimage]
    have hx : x + ↑(-⌊x⌋) in Ico (0 : Real) 1 := by
      simp only [Int.floor_le, Int.lt_floor_add_one, add_neg_lt_iff_le_add', zero_add, and_self_iff,
        mem_Ico, Int.cast_neg, le_add_neg_iff_add_le]
    exact ⟨-⌊x⌋, n + 1, n.succ_pos, this _ (hxp.add_int _) hx⟩
  clear hxp x; intro x hxp hx01
  refine ((hxp.frequently_lt_rpow_neg hn).and_eventually (eventually_ge_atTop 1)).mono ?_
  rintro b ⟨⟨a, -, hlt⟩, hb⟩
  rw [rpow_neg b.cast_nonneg]; rw [← one_div]; rw [← Nat.cast_succ] at hlt
  refine ⟨a, ?_, hlt⟩
  replace hb : (1 : Real) <= b := Nat.one_le_cast.2 hb
  have hb0 : (0 : Real) < b := zero_lt_one.trans_le hb
  replace hlt : |x - a / b| < 1 / b := by
    refine hlt.trans_le (one_div_le_one_div_of_le hb0 ?_)
    calc
      (b : Real) = (b : Real) ^ (1 : Real) := (rpow_one _).symm
      _ <= (b : Real) ^ (2 + 1 / (n + 1 : Nat) : Real) :=
        rpow_le_rpow_of_exponent_le hb (one_le_two.trans ?_)
    simpa using n.cast_add_one_pos.le
  rw [sub_div' hb0.ne']; rw [abs_div]; rw [abs_of_pos hb0]; rw [div_lt_div_iff_of_pos_right hb0]; rw [abs_sub_lt_iff]; rw [sub_lt_iff_lt_add]; rw [sub_lt_iff_lt_add]; rw [← sub_lt_iff_lt_add'] at hlt
  rw [Finset.mem_Icc]; rw [← Int.lt_add_one_iff]; rw [← Int.lt_add_one_iff]; rw [← neg_lt_iff_pos_add]; rw [add_comm]; rw [←
    @Int.cast_lt Real]; rw [← @Int.cast_lt Real]
  push_cast
  refine ⟨lt_of_le_of_lt ?_ hlt.1, hlt.2.trans_le ?_⟩
  · simp only [mul_nonneg hx01.left b.cast_nonneg, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
  · rw [add_le_add_iff_left]
    exact mul_le_of_le_one_left hb0.le hx01.2.le

@[deprecated (since := "2026-07-09")]
alias setOf_liouvilleWith_subset_aux := setOfPred_liouvilleWith_subset_aux

中文:
定理 setOfPred_liouvilleWith_subset_aux
  证明: by
  rintro x ⟨p, hp, hxp⟩
  rcases exists_nat_one_div_lt (sub_pos.2 hp) with ⟨n, hn⟩
  rw [lt_sub_iff_add_lt'] at hn
  suffices forall y : Real, LiouvilleWith p y -> y in Ico (0 : Real) 1 -> existsᶠ b : Nat in atTop,
      exists a in Finset.Icc (0 : Int) b, |y - a / b| < 1 / (b : Real) ^ (2 + 1 / (n + 1 : Nat) : Real) by
    simp only [mem_iUnion, mem_preimage]
    have hx : x + ↑(-⌊x⌋) in Ico (0 : Real) 1 := by
      simp only [Int.floor_le, Int.lt_floor_add_one, add_neg_lt_iff_le_add', zero_add, and_self_iff,
        mem_Ico, Int.cast_neg, le_add_neg_iff_add_le]
    exact ⟨-⌊x⌋, n + 1, n.succ_pos, this _ (hxp.add_int _) hx⟩
  clear hxp x; intro x hxp hx01
  refine ((hxp.frequently_lt_rpow_neg hn).and_eventually (eventually_ge_atTop 1)).mono ?_
  rintro b ⟨⟨a, -, hlt⟩, hb⟩
  rw [rpow_neg b.cast_nonneg]; rw [← one_div]; rw [← Nat.cast_succ] at hlt
  refine ⟨a, ?_, hlt⟩
  replace hb : (1 : Real) <= b := Nat.one_le_cast.2 hb
  have hb0 : (0 : Real) < b := zero_lt_one.trans_le hb
  replace hlt : |x - a / b| < 1 / b := by
    refine hlt.trans_le (one_div_le_one_div_of_le hb0 ?_)
    calc
      (b : Real) = (b : Real) ^ (1 : Real) := (rpow_one _).symm
      _ <= (b : Real) ^ (2 + 1 / (n + 1 : Nat) : Real) :=
        rpow_le_rpow_of_exponent_le hb (one_le_two.trans ?_)
    simpa using n.cast_add_one_pos.le
  rw [sub_div' hb0.ne']; rw [abs_div]; rw [abs_of_pos hb0]; rw [div_lt_div_iff_of_pos_right hb0]; rw [abs_sub_lt_iff]; rw [sub_lt_iff_lt_add]; rw [sub_lt_iff_lt_add]; rw [← sub_lt_iff_lt_add'] at hlt
  rw [Finset.mem_Icc]; rw [← Int.lt_add_one_iff]; rw [← Int.lt_add_one_iff]; rw [← neg_lt_iff_pos_add]; rw [add_comm]; rw [←
    @Int.cast_lt Real]; rw [← @Int.cast_lt Real]
  push_cast
  refine ⟨lt_of_le_of_lt ?_ hlt.1, hlt.2.trans_le ?_⟩
  · simp only [mul_nonneg hx01.left b.cast_nonneg, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
  · rw [add_le_add_iff_left]
    exact mul_le_of_le_one_left hb0.le hx01.2.le

@[deprecated (since := "2026-07-09")]
alias setOf_liouvilleWith_subset_aux := setOfPred_liouvilleWith_subset_aux

Depends on / 依赖: Finset, Finset.Icc, Int.floor_le, Int.lt_floor_add_one, LiouvilleWith, add_neg_lt_iff_le_add, and_self_iff, exists_nat_one_div_lt, floor_le, lt_floor_add_one, lt_sub_iff_add_lt, mem_Ico, mem_iUnion, mem_preimage, sub_pos, zero_add
-/
theorem setOfPred_liouvilleWith_subset_aux :
    { x : Real | exists p > 2, LiouvilleWith p x } subseteq
      ⋃ m : Int, (· + (m : Real)) ⁻¹' ⋃ n > (0 : Nat),
        { x : Real | existsᶠ b : Nat in atTop, exists a in Finset.Icc (0 : Int) b,
          |x - (a : Int) / b| < 1 / (b : Real) ^ (2 + 1 / n : Real) } := by
  rintro x ⟨p, hp, hxp⟩
  rcases exists_nat_one_div_lt (sub_pos.2 hp) with ⟨n, hn⟩
  rw [lt_sub_iff_add_lt'] at hn
  suffices forall y : Real, LiouvilleWith p y -> y in Ico (0 : Real) 1 -> existsᶠ b : Nat in atTop,
      exists a in Finset.Icc (0 : Int) b, |y - a / b| < 1 / (b : Real) ^ (2 + 1 / (n + 1 : Nat) : Real) by
    simp only [mem_iUnion, mem_preimage]
    have hx : x + ↑(-⌊x⌋) in Ico (0 : Real) 1 := by
      simp only [Int.floor_le, Int.lt_floor_add_one, add_neg_lt_iff_le_add', zero_add, and_self_iff,
        mem_Ico, Int.cast_neg, le_add_neg_iff_add_le]
    exact ⟨-⌊x⌋, n + 1, n.succ_pos, this _ (hxp.add_int _) hx⟩
  clear hxp x; intro x hxp hx01
  refine ((hxp.frequently_lt_rpow_neg hn).and_eventually (eventually_ge_atTop 1)).mono ?_
  rintro b ⟨⟨a, -, hlt⟩, hb⟩
  rw [rpow_neg b.cast_nonneg]; rw [← one_div]; rw [← Nat.cast_succ] at hlt
  refine ⟨a, ?_, hlt⟩
  replace hb : (1 : Real) <= b := Nat.one_le_cast.2 hb
  have hb0 : (0 : Real) < b := zero_lt_one.trans_le hb
  replace hlt : |x - a / b| < 1 / b := by
    refine hlt.trans_le (one_div_le_one_div_of_le hb0 ?_)
    calc
      (b : Real) = (b : Real) ^ (1 : Real) := (rpow_one _).symm
      _ <= (b : Real) ^ (2 + 1 / (n + 1 : Nat) : Real) :=
        rpow_le_rpow_of_exponent_le hb (one_le_two.trans ?_)
    simpa using n.cast_add_one_pos.le
  rw [sub_div' hb0.ne']; rw [abs_div]; rw [abs_of_pos hb0]; rw [div_lt_div_iff_of_pos_right hb0]; rw [abs_sub_lt_iff]; rw [sub_lt_iff_lt_add]; rw [sub_lt_iff_lt_add]; rw [← sub_lt_iff_lt_add'] at hlt
  rw [Finset.mem_Icc]; rw [← Int.lt_add_one_iff]; rw [← Int.lt_add_one_iff]; rw [← neg_lt_iff_pos_add]; rw [add_comm]; rw [←
    @Int.cast_lt Real]; rw [← @Int.cast_lt Real]
  push_cast
  refine ⟨lt_of_le_of_lt ?_ hlt.1, hlt.2.trans_le ?_⟩
  · simp only [mul_nonneg hx01.left b.cast_nonneg, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
  · rw [add_le_add_iff_left]
    exact mul_le_of_le_one_left hb0.le hx01.2.le

@[deprecated (since := "2026-07-09")]
alias setOf_liouvilleWith_subset_aux := setOfPred_liouvilleWith_subset_aux

/-- The set of numbers satisfying the Liouville condition with some exponent `p > 2` has Lebesgue
measure zero. -/
@[simp]
/--
theorem `volume_iUnion_setOfPred_liouvilleWith` / 定理 `volume_iUnion_setOfPred_liouvilleWith`

English:
theorem volume_iUnion_setOfPred_liouvilleWith
  proof: by
  simp only [← ofPred_exists, exists_prop]
  refine measure_mono_null setOfPred_liouvilleWith_subset_aux ?_
  rw [measure_iUnion_null_iff]; intro m; rw [measure_preimage_add_right]; clear m
  refine (measure_biUnion_null_iff <| to_countable _).2 fun n (hn : 1 <= n) => ?_
  generalize hr : (2 + 1 / n : Real) = r
  replace hr : 2 < r := by simp [← hr, zero_lt_one.trans_le hn]
  clear hn n
  refine measure_setOfPred_frequently_eq_zero ?_
  simp only [ofPred_exists, ← exists_prop, ← Real.dist_eq, ← mem_ball, ofPred_mem_eq]
  set B : Int -> Nat -> Set Real := fun a b => ball (a / b) (1 / (b : Real) ^ r)
  have hB : forall a b, volume (B a b) = ↑((2 : Real>=0) / (b : Real>=0) ^ r) := fun a b => by
    rw [Real.volume_ball]; rw [mul_one_div]; rw [← NNReal.coe_two]; rw [← NNReal.coe_natCast]; rw [← NNReal.coe_rpow]; rw [← NNReal.coe_div]; rw [ENNReal.ofReal_coe_nnreal]
  have : forall b : Nat, volume (⋃ a in Finset.Icc (0 : Int) b, B a b) <=
      ↑(2 * ((b : Real>=0) ^ (1 - r) + (b : Real>=0) ^ (-r))) := fun b =>
    calc
      volume (⋃ a in Finset.Icc (0 : Int) b, B a b) <= ∑ a in Finset.Icc (0 : Int) b, volume (B a b) :=
        measure_biUnion_finset_le _ _
      _ = ↑((b + 1) * (2 / (b : Real>=0) ^ r)) := by
        simp only [hB, Int.card_Icc, Finset.sum_const, nsmul_eq_mul, sub_zero,
          Int.toNat_natCast, ← Nat.cast_succ, ENNReal.coe_mul, ENNReal.coe_natCast]
      _ = _ := by
        have : 1 - r != 0 := by linarith
        rw [ENNReal.coe_inj]
        simp [add_mul, div_eq_mul_inv, NNReal.rpow_neg, NNReal.rpow_sub' this, mul_add,
          mul_left_comm]
  refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2 ?_) (ENNReal.tsum_le_tsum this)
  refine (Summable.add ?_ ?_).mul_left _ <;> simp only [NNReal.summable_rpow] <;> linarith

@[deprecated (since := "2026-07-09")]
alias volume_iUnion_setOf_liouvilleWith := volume_iUnion_setOfPred_liouvilleWith

中文:
定理 volume_iUnion_setOfPred_liouvilleWith
  证明: by
  simp only [← ofPred_exists, exists_prop]
  refine measure_mono_null setOfPred_liouvilleWith_subset_aux ?_
  rw [measure_iUnion_null_iff]; intro m; rw [measure_preimage_add_right]; clear m
  refine (measure_biUnion_null_iff <| to_countable _).2 fun n (hn : 1 <= n) => ?_
  generalize hr : (2 + 1 / n : Real) = r
  replace hr : 2 < r := by simp [← hr, zero_lt_one.trans_le hn]
  clear hn n
  refine measure_setOfPred_frequently_eq_zero ?_
  simp only [ofPred_exists, ← exists_prop, ← Real.dist_eq, ← mem_ball, ofPred_mem_eq]
  set B : Int -> Nat -> Set Real := fun a b => ball (a / b) (1 / (b : Real) ^ r)
  have hB : forall a b, volume (B a b) = ↑((2 : Real>=0) / (b : Real>=0) ^ r) := fun a b => by
    rw [Real.volume_ball]; rw [mul_one_div]; rw [← NNReal.coe_two]; rw [← NNReal.coe_natCast]; rw [← NNReal.coe_rpow]; rw [← NNReal.coe_div]; rw [ENNReal.ofReal_coe_nnreal]
  have : forall b : Nat, volume (⋃ a in Finset.Icc (0 : Int) b, B a b) <=
      ↑(2 * ((b : Real>=0) ^ (1 - r) + (b : Real>=0) ^ (-r))) := fun b =>
    calc
      volume (⋃ a in Finset.Icc (0 : Int) b, B a b) <= ∑ a in Finset.Icc (0 : Int) b, volume (B a b) :=
        measure_biUnion_finset_le _ _
      _ = ↑((b + 1) * (2 / (b : Real>=0) ^ r)) := by
        simp only [hB, Int.card_Icc, Finset.sum_const, nsmul_eq_mul, sub_zero,
          Int.toNat_natCast, ← Nat.cast_succ, ENNReal.coe_mul, ENNReal.coe_natCast]
      _ = _ := by
        have : 1 - r != 0 := by linarith
        rw [ENNReal.coe_inj]
        simp [add_mul, div_eq_mul_inv, NNReal.rpow_neg, NNReal.rpow_sub' this, mul_add,
          mul_left_comm]
  refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2 ?_) (ENNReal.tsum_le_tsum this)
  refine (Summable.add ?_ ?_).mul_left _ <;> simp only [NNReal.summable_rpow] <;> linarith

@[deprecated (since := "2026-07-09")]
alias volume_iUnion_setOf_liouvilleWith := volume_iUnion_setOfPred_liouvilleWith

Depends on / 依赖: Real.dist_eq, dist_eq, exists_prop, generalize, measure_biUnion_null_iff, measure_iUnion_null_iff, measure_mono_null, measure_preimage_add_right, measure_setOfPred_frequently_eq_zero, mem_ball, ofPred_exists, replace, setOfPred_liouvilleWith_subset_aux, to_countable, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem volume_iUnion_setOfPred_liouvilleWith :
    volume (⋃ (p : Real) (_hp : 2 < p), { x : Real | LiouvilleWith p x }) = 0 := by
  simp only [← ofPred_exists, exists_prop]
  refine measure_mono_null setOfPred_liouvilleWith_subset_aux ?_
  rw [measure_iUnion_null_iff]; intro m; rw [measure_preimage_add_right]; clear m
  refine (measure_biUnion_null_iff <| to_countable _).2 fun n (hn : 1 <= n) => ?_
  generalize hr : (2 + 1 / n : Real) = r
  replace hr : 2 < r := by simp [← hr, zero_lt_one.trans_le hn]
  clear hn n
  refine measure_setOfPred_frequently_eq_zero ?_
  simp only [ofPred_exists, ← exists_prop, ← Real.dist_eq, ← mem_ball, ofPred_mem_eq]
  set B : Int -> Nat -> Set Real := fun a b => ball (a / b) (1 / (b : Real) ^ r)
  have hB : forall a b, volume (B a b) = ↑((2 : Real>=0) / (b : Real>=0) ^ r) := fun a b => by
    rw [Real.volume_ball]; rw [mul_one_div]; rw [← NNReal.coe_two]; rw [← NNReal.coe_natCast]; rw [← NNReal.coe_rpow]; rw [← NNReal.coe_div]; rw [ENNReal.ofReal_coe_nnreal]
  have : forall b : Nat, volume (⋃ a in Finset.Icc (0 : Int) b, B a b) <=
      ↑(2 * ((b : Real>=0) ^ (1 - r) + (b : Real>=0) ^ (-r))) := fun b =>
    calc
      volume (⋃ a in Finset.Icc (0 : Int) b, B a b) <= ∑ a in Finset.Icc (0 : Int) b, volume (B a b) :=
        measure_biUnion_finset_le _ _
      _ = ↑((b + 1) * (2 / (b : Real>=0) ^ r)) := by
        simp only [hB, Int.card_Icc, Finset.sum_const, nsmul_eq_mul, sub_zero,
          Int.toNat_natCast, ← Nat.cast_succ, ENNReal.coe_mul, ENNReal.coe_natCast]
      _ = _ := by
        have : 1 - r != 0 := by linarith
        rw [ENNReal.coe_inj]
        simp [add_mul, div_eq_mul_inv, NNReal.rpow_neg, NNReal.rpow_sub' this, mul_add,
          mul_left_comm]
  refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2 ?_) (ENNReal.tsum_le_tsum this)
  refine (Summable.add ?_ ?_).mul_left _ <;> simp only [NNReal.summable_rpow] <;> linarith

@[deprecated (since := "2026-07-09")]
alias volume_iUnion_setOf_liouvilleWith := volume_iUnion_setOfPred_liouvilleWith

/--
theorem `ae_not_liouvilleWith` / 定理 `ae_not_liouvilleWith`

English:
theorem ae_not_liouvilleWith
  statement: forallᵐ x, forall p > (2 : Real), ¬LiouvilleWith p x
  proof: by
  simpa only [ae_iff, not_forall, Classical.not_not, ofPred_exists] using
    volume_iUnion_setOfPred_liouvilleWith

中文:
定理 ae_not_liouvilleWith
  结论: 对任意ᵐ x, 对任意 p > (2 : 实数), ¬LiouvilleWith p x
  证明: by
  simpa only [ae_iff, not_forall, Classical.not_not, ofPred_exists] using
    volume_iUnion_setOfPred_liouvilleWith

Depends on / 依赖: Classical, Classical.not_not, ae_iff, not_forall, not_not, ofPred_exists, volume_iUnion_setOfPred_liouvilleWith
-/
theorem ae_not_liouvilleWith : forallᵐ x, forall p > (2 : Real), ¬LiouvilleWith p x := by
  simpa only [ae_iff, not_forall, Classical.not_not, ofPred_exists] using
    volume_iUnion_setOfPred_liouvilleWith

/--
theorem `ae_not_liouville` / 定理 `ae_not_liouville`

English:
theorem ae_not_liouville
  statement: forallᵐ x, ¬Liouville x
  proof: ae_not_liouvilleWith.mono fun _ h₁ h₂ => h₁ 3 (by norm_num) (h₂.liouvilleWith 3)

中文:
定理 ae_not_liouville
  结论: 对任意ᵐ x, ¬Liouville x
  证明: ae_not_liouvilleWith.mono fun _ h₁ h₂ => h₁ 3 (by norm_num) (h₂.liouvilleWith 3)

Depends on / 依赖: ae_not_liouvilleWith, ae_not_liouvilleWith.mono, liouvilleWith
-/
theorem ae_not_liouville : forallᵐ x, ¬Liouville x :=
  ae_not_liouvilleWith.mono fun _ h₁ h₂ => h₁ 3 (by norm_num) (h₂.liouvilleWith 3)

/-- The set of Liouville numbers has Lebesgue measure zero. -/
@[simp]
/--
theorem `volume_setOfPred_liouville` / 定理 `volume_setOfPred_liouville`

English:
theorem volume_setOfPred_liouville
  statement: volume { x : Real | Liouville x } = 0
  proof: by
  simpa only [ae_iff, Classical.not_not] using ae_not_liouville

@[deprecated (since := "2026-07-09")]
alias volume_setOf_liouville := volume_setOfPred_liouville

中文:
定理 volume_setOfPred_liouville
  结论: volume { x : 实数 | Liouville x } = 0
  证明: by
  simpa only [ae_iff, Classical.not_not] using ae_not_liouville

@[deprecated (since := "2026-07-09")]
alias volume_setOf_liouville := volume_setOfPred_liouville

Depends on / 依赖: Classical, Classical.not_not, ae_iff, ae_not_liouville, not_not
-/
theorem volume_setOfPred_liouville : volume { x : Real | Liouville x } = 0 := by
  simpa only [ae_iff, Classical.not_not] using ae_not_liouville

@[deprecated (since := "2026-07-09")]
alias volume_setOf_liouville := volume_setOfPred_liouville

/--
theorem `Real.disjoint_residual_ae` / 定理 `Real.disjoint_residual_ae`

English:
theorem Real.disjoint_residual_ae
  statement: Disjoint (residual Real) (ae volume)
  proof: disjoint_of_disjoint_of_mem disjoint_compl_right eventually_residual_liouville ae_not_liouville

中文:
定理 实数.disjoint_residual_ae
  结论: Disjoint (residual 实数) (ae volume)
  证明: disjoint_of_disjoint_of_mem disjoint_compl_right eventually_residual_liouville ae_not_liouville

Depends on / 依赖: ae_not_liouville, disjoint_compl_right, disjoint_of_disjoint_of_mem, eventually_residual_liouville
-/
theorem Real.disjoint_residual_ae : Disjoint (residual Real) (ae volume) :=
  disjoint_of_disjoint_of_mem disjoint_compl_right eventually_residual_liouville ae_not_liouville
