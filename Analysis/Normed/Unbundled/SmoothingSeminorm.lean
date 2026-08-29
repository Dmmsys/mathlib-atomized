/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Bounds
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# smoothingSeminorm

In this file, we prove [BGR, Proposition 1.3.2/1][bosch-guntzer-remmert]: if `μ` is a
nonarchimedean seminorm on a commutative ring `R`, then
`iInf (fun (n : PNat), (μ(x ^ (n : ℕ))) ^ (1 / (n : ℝ)))` is a power-multiplicative nonarchimedean
seminorm on `R`.

## Main Definitions
* `smoothingSeminormSeq` : the `ℝ`-valued sequence sending `n` to `((f( (x ^ n)) ^ (1 / n : ℝ)`.
* `smoothingFun` : the iInf of the sequence `n ↦ f(x ^ (n : ℕ))) ^ (1 / (n : ℝ)`.
* `smoothingSeminorm` : if `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun`
  is a ring seminorm.

## Main Results

* `tendsto_smoothingFun_of_map_one_le_one` : if `μ 1 ≤ 1`, then `smoothingFun μ x` is the limit
  of `smoothingSeminormSeq μ x` as `n` tends to infinity.
* `isNonarchimedean_smoothingFun` : if `μ 1 ≤ 1` and `μ` is nonarchimedean, then
  `smoothingFun` is nonarchimedean.
* `isPowMul_smoothingFun` : if `μ 1 ≤ 1` and `μ` is nonarchimedean, then
  `smoothingFun μ` is power-multiplicative.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

smoothingSeminorm, seminorm, nonarchimedean
-/

@[expose] public section

noncomputable section

open Filter Nat Real

open scoped Topology NNReal

variable {R : Type*} [CommRing R] (μ : RingSeminorm R)

section smoothingSeminorm

/--
Definition of `smoothingSeminormSeq` / `smoothingSeminormSeq` 的定义

English:
abbreviation smoothingSeminormSeq
  signature: (x : R)
  body: fun n => μ (x ^ n) ^ (1 / n : Real)

中文:
缩写 smoothingSeminormSeq
  签名: (x : R)
  定义体: fun n => μ (x ^ n) ^ (1 / n : Real)
-/
abbrev smoothingSeminormSeq (x : R) : Nat -> Real := fun n => μ (x ^ n) ^ (1 / n : Real)

/--
theorem `smoothingSeminormSeq_exists_pnat` / 定理 `smoothingSeminormSeq_exists_pnat`

English:
theorem smoothingSeminormSeq_exists_pnat
  given: (x : R) {ε : Real} (hε : 0 < ε)
  proof: exists_lt_of_ciInf_lt (lt_add_of_le_of_pos (le_refl _) (half_pos hε))

中文:
定理 smoothingSeminormSeq_exists_pnat
  条件: (x : R) {ε : 实数} (hε : 0 < ε)
  证明: exists_lt_of_ciInf_lt (lt_add_of_le_of_pos (le_refl _) (half_pos hε))
-/
private theorem smoothingSeminormSeq_exists_pnat (x : R) {ε : Real} (hε : 0 < ε) :
    exists m : PNat, μ (x ^ (m : Nat)) ^ (1 / m : Real) <
        (iInf fun n : PNat => μ (x ^ (n : Nat)) ^ (1 / (n : Real))) + ε / 2 :=
  exists_lt_of_ciInf_lt (lt_add_of_le_of_pos (le_refl _) (half_pos hε))

/--
theorem `smoothingSeminormSeq_tendsto_aux` / 定理 `smoothingSeminormSeq_tendsto_aux`

English:
theorem smoothingSeminormSeq_tendsto_aux
  statement: {L : Real} (hL : 0 <= L) {ε : Real} (hε : 0 < ε)
  proof: by
  rw [← mul_one (1 : Real)]
  have h_exp : Tendsto (fun n : Nat => ((n % m1 : Nat) : Real) / (n : Real)) atTop (𝓝 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hm1
  apply Tendsto.mul
  · have h0 : Tendsto (fun t : Nat => -(((t % m1 : Nat) : Real) / (t : Real))) atTop (𝓝 0) := by
      rw [← neg_

中文:
定理 smoothingSeminormSeq_tendsto_aux
  结论: {L : 实数} (hL : 0 <= L) {ε : 实数} (hε : 0 < ε)
  证明: by
  rw [← mul_one (1 : Real)]
  have h_exp : Tendsto (fun n : Nat => ((n % m1 : Nat) : Real) / (n : Real)) atTop (𝓝 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hm1
  apply Tendsto.mul
  · have h0 : Tendsto (fun t : Nat => -(((t % m1 : Nat) : Real) / (t : Real))) atTop (𝓝 0) := by
      rw [← neg_
-/
private theorem smoothingSeminormSeq_tendsto_aux {L : Real} (hL : 0 <= L) {ε : Real} (hε : 0 < ε)
    {m1 : Nat} (hm1 : 0 < m1) {x : R} (hx : μ x != 0) :
    Tendsto
      (fun n : Nat => (L + ε) ^ (-(((n % m1 : Nat) : Real) / (n : Real))) * (μ x ^ (n % m1)) ^ (1 / (n : Real)))
      atTop (𝓝 1) := by
  rw [← mul_one (1 : Real)]
  have h_exp : Tendsto (fun n : Nat => ((n % m1 : Nat) : Real) / (n : Real)) atTop (𝓝 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hm1
  apply Tendsto.mul
  · have h0 : Tendsto (fun t : Nat => -(((t % m1 : Nat) : Real) / (t : Real))) atTop (𝓝 0) := by
      rw [← neg_zero]
      exact Tendsto.neg h_exp
    rw [← rpow_zero (L + ε)]
    apply Tendsto.rpow tendsto_const_nhds h0
    rw [ne_eq]; rw [add_eq_zero_iff_of_nonneg hL (le_of_lt hε)]
    exact Or.inl (not_and_of_not_right _ (ne_of_gt hε))
  · simp_rw [mul_one, ← rpow_natCast, ← rpow_mul (apply_nonneg μ x), ← mul_div_assoc, mul_one,
      ← rpow_zero (μ x)]
    exact Tendsto.rpow tendsto_const_nhds h_exp (Or.inl hx)

/--
theorem `zero_mem_lowerBounds_smoothingSeminormSeq_range` / 定理 `zero_mem_lowerBounds_smoothingSeminormSeq_range`

English:
theorem zero_mem_lowerBounds_smoothingSeminormSeq_range
  given: (x : R)
  proof: by
  rintro y ⟨n, rfl⟩
  positivity

中文:
定理 zero_mem_lowerBounds_smoothingSeminormSeq_range
  条件: (x : R)
  证明: by
  rintro y ⟨n, rfl⟩
  positivity
-/
theorem zero_mem_lowerBounds_smoothingSeminormSeq_range (x : R) :
    0 in lowerBounds (Set.range fun n : Nat+ => μ (x ^ (n : Nat)) ^ (1 / (n : Real))) := by
  rintro y ⟨n, rfl⟩
  positivity

/--
theorem `smoothingSeminormSeq_bddBelow` / 定理 `smoothingSeminormSeq_bddBelow`

English:
theorem smoothingSeminormSeq_bddBelow
  given: (x : R)
  proof: ⟨0, zero_mem_lowerBounds_smoothingSeminormSeq_range μ x⟩

中文:
定理 smoothingSeminormSeq_bddBelow
  条件: (x : R)
  证明: ⟨0, zero_mem_lowerBounds_smoothingSeminormSeq_range μ x⟩

Depends on / 依赖: zero_mem_lowerBounds_smoothingSeminormSeq_range
-/
theorem smoothingSeminormSeq_bddBelow (x : R) :
    BddBelow (Set.range fun n : Nat+ => μ (x ^ (n : Nat)) ^ (1 / (n : Real))) :=
  ⟨0, zero_mem_lowerBounds_smoothingSeminormSeq_range μ x⟩

/--
Definition of `smoothingFun` / `smoothingFun` 的定义

English:
abbreviation smoothingFun
  signature: (x : R)
  body: iInf fun n : PNat => μ (x ^ (n : Nat)) ^ (1 / (n : Real))

中文:
缩写 smoothingFun
  签名: (x : R)
  定义体: iInf fun n : PNat => μ (x ^ (n : Nat)) ^ (1 / (n : Real))
-/
abbrev smoothingFun (x : R) : Real :=
  iInf fun n : PNat => μ (x ^ (n : Nat)) ^ (1 / (n : Real))

/--
theorem `tendsto_smoothingFun_of_eq_zero` / 定理 `tendsto_smoothingFun_of_eq_zero`

English:
theorem tendsto_smoothingFun_of_eq_zero
  given: {x : R} (hx : μ x = 0)
  proof: by
  have h0 (n : Nat) (hn : 1 <= n) : μ (x ^ n) ^ (1 / (n : Real)) = 0 := by
    have hμn : μ (x ^ n) = 0 := by
      apply le_antisymm _ (apply_nonneg μ _)
      rw [← zero_pow (pos_iff_ne_zero.mp hn)]; rw [← hx]
      exact map_pow_le_pow _ x (one_le_iff_ne_zero.mp hn)
    rw [hμn]; rw [zero_rpow

中文:
定理 tendsto_smoothingFun_of_eq_zero
  条件: {x : R} (hx : μ x = 0)
  证明: by
  have h0 (n : Nat) (hn : 1 <= n) : μ (x ^ n) ^ (1 / (n : Real)) = 0 := by
    have hμn : μ (x ^ n) = 0 := by
      apply le_antisymm _ (apply_nonneg μ _)
      rw [← zero_pow (pos_iff_ne_zero.mp hn)]; rw [← hx]
      exact map_pow_le_pow _ x (one_le_iff_ne_zero.mp hn)
    rw [hμn]; rw [zero_rpow

Depends on / 依赖: apply_nonneg, ciInf_le_of_le, le_antisymm, le_of_eq, le_ref, map_pow_le_pow, one_div_cast_ne_zero, one_le_iff_ne_zero, one_le_iff_ne_zero.mp, pos_iff_ne_zero, pos_iff_ne_zero.mp, smoothingSeminormSeq_bddBelow, zero_pow, zero_rpow
-/
theorem tendsto_smoothingFun_of_eq_zero {x : R} (hx : μ x = 0) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) := by
  have h0 (n : Nat) (hn : 1 <= n) : μ (x ^ n) ^ (1 / (n : Real)) = 0 := by
    have hμn : μ (x ^ n) = 0 := by
      apply le_antisymm _ (apply_nonneg μ _)
      rw [← zero_pow (pos_iff_ne_zero.mp hn)]; rw [← hx]
      exact map_pow_le_pow _ x (one_le_iff_ne_zero.mp hn)
    rw [hμn]; rw [zero_rpow (one_div_cast_ne_zero (one_le_iff_ne_zero.mp hn))]
  have hL0 : (iInf fun n : PNat => μ (x ^ (n : Nat)) ^ (1 / (n : Real))) = 0 :=
    le_antisymm
      (ciInf_le_of_le (smoothingSeminormSeq_bddBelow μ x) (1 : PNat) (le_of_eq (h0 1 (le_refl _))))
      (le_ciInf fun n => by positivity)
  simpa only [hL0] using tendsto_atTop_of_eventually_const h0

/--
theorem `tendsto_smoothingFun_of_ne_zero` / 定理 `tendsto_smoothingFun_of_ne_zero`

English:
theorem tendsto_smoothingFun_of_ne_zero
  given: (hμ1 : μ 1 <= 1) {x : R} (hx : μ x != 0)
  proof: by
  let L := iInf fun n : PNat => μ (x ^ (n : Nat)) ^ (1 / (n : Real))
  have hL0 : 0 <= L := le_ciInf fun x => by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  /- For each `ε > 0`, we can find a positive natural number `m1` such that
  `μ x ^ (1 / m1) < L + ε/2`. -/
  obtain ⟨m1, hm1⟩ := s

中文:
定理 tendsto_smoothingFun_of_ne_zero
  条件: (hμ1 : μ 1 <= 1) {x : R} (hx : μ x != 0)
  证明: by
  let L := iInf fun n : PNat => μ (x ^ (n : Nat)) ^ (1 / (n : Real))
  have hL0 : 0 <= L := le_ciInf fun x => by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  /- For each `ε > 0`, we can find a positive natural number `m1` such that
  `μ x ^ (1 / m1) < L + ε/2`. -/
  obtain ⟨m1, hm1⟩ := s

Depends on / 依赖: Metric, Metric.tendsto_atTop, le_ciInf, tendsto_atTop
-/
theorem tendsto_smoothingFun_of_ne_zero (hμ1 : μ 1 <= 1) {x : R} (hx : μ x != 0) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) := by
  let L := iInf fun n : PNat => μ (x ^ (n : Nat)) ^ (1 / (n : Real))
  have hL0 : 0 <= L := le_ciInf fun x => by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  /- For each `ε > 0`, we can find a positive natural number `m1` such that
  `μ x ^ (1 / m1) < L + ε/2`. -/
  obtain ⟨m1, hm1⟩ := smoothingSeminormSeq_exists_pnat μ x hε
  /- For `n` large enough, we have that
    `(L + ε / 2) ^ (-(n % m1) / n)) * (μ x ^ (n % m1)) ^ (1 / n) - 1 ≤ ε / (2 * (L + ε / 2))`. -/
  obtain ⟨m2, hm2⟩ : exists m : Nat, forall n >= m,
      (L + ε / 2) ^ (-(((n % m1 : Nat) : Real) / (n : Real))) * (μ x ^ (n % m1)) ^ (1 / (n : Real)) - 1 <=
      ε / (2 * (L + ε / 2)) := by
    have hε2 : 0 < ε / 2 := half_pos hε
    have hL2 := smoothingSeminormSeq_tendsto_aux μ hL0 hε2 (PNat.pos m1) hx
    rw [Metric.tendsto_atTop] at hL2
    set δ : Real := ε / (2 * (L + ε / 2)) with hδ_def
    have hδ : 0 < δ := by
      rw [hδ_def]; rw [div_mul_eq_div_mul_one_div]
      exact mul_pos hε2
        ((one_div (L + ε / 2)).symm ▸ inv_pos_of_pos (add_pos_of_nonneg_of_pos hL0 hε2))
    obtain ⟨N, hN⟩ := hL2 δ hδ
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq]; rw [abs_lt] at hN
    exact le_of_lt hN.right
  /- We now show that for all `n ≥ max m1 m2`, we have
    `dist (smoothingSeminormSeq μ x n) (smoothingFun μ x) < ε`. -/
  use max (m1 : Nat) m2
  intro n hn
  have hn0 : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le (PNat.pos m1) (le_max_left (m1 : Nat) m2)) hn
  rw [Real.dist_eq]; rw [abs_lt]
  have hL_le : L <= smoothingSeminormSeq μ x n := by
    rw [← PNat.mk_coe n hn0]
    apply ciInf_le (smoothingSeminormSeq_bddBelow μ x)
  refine ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) (sub_nonneg.mpr hL_le), ?_⟩
  -- It is enough to show that `smoothingSeminormSeq μ x n < L + ε`, that is,
  -- `μ (x ^ n) ^ (1 / ↑n) < L + ε`.
  suffices h : smoothingSeminormSeq μ x n < L + ε by rwa [tsub_lt_iff_left hL_le]
  by_cases hxn : μ (x ^ (n % m1)) = 0
  · /- If `μ (x ^ (n % m1)) = 0`, this reduces to showing that
     `μ (x ^ (↑m1 * (n / ↑m1)) * x ^ (n % ↑m1)) ^ (1 / ↑n) ≤
     (μ (x ^ (↑m1 * (n / ↑m1))) * μ (x ^ (n % ↑m1))) ^ (1 / ↑n)`, which follows from the
     submultiplicativity of `μ`. -/
    simp only [smoothingSeminormSeq]
    nth_rw 1 [← div_add_mod n m1]
    have hLε : 0 < L + ε := add_pos_of_nonneg_of_pos hL0 hε
    apply lt_of_le_of_lt _ hLε
    rw [pow_add]; rw [← MulZeroClass.mul_zero (μ (x ^ ((m1 : Nat) * (n / (m1 : Nat)))) ^ (1 / (n : Real)))]; rw [← zero_rpow (one_div_cast_ne_zero (pos_iff_ne_zero.mp hn0))]; rw [← hxn]; rw [← mul_rpow (apply_nonneg μ _) (apply_nonneg μ _)]
    gcongr
    exact map_mul_le_mul μ _ _
  · --Otherwise, we have `0 < μ (x ^ (n % ↑m1))`.
    have hxn' : 0 < μ (x ^ (n % ↑m1)) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hxn)
    simp only [smoothingSeminormSeq]
    nth_rw 1 [← div_add_mod n m1]
    /- We use the submultiplicativity of `μ` to deduce
    `μ (x ^ (m1 * (n / m1)) ^ (1 / n) ≤ (μ (x ^ m1) ^ (n / m1)) ^ (1 / n)`. -/
    have h : μ (x ^ ((m1 : Nat) * (n / (m1 : Nat)))) ^ (1 / (n : Real)) <=
        (μ (x ^ (m1 : Nat)) ^ (n / (m1 : Nat))) ^ (1 / (n : Real)) := by
      gcongr
      rw [pow_mul]
      exact map_pow_le_pow μ (x ^ (m1 : Nat))
        (pos_iff_ne_zero.mp (Nat.div_pos (le_trans (le_max_left (m1 : Nat) m2) hn) (PNat.pos m1)))
    have hL0' : 0 < L + ε / 2 := add_pos_of_nonneg_of_pos hL0 (half_pos hε)
    /- We show that `(μ (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)) <
        (L + ε / 2) ^ (1 - (((n % m1 : ℕ) : ℝ) / (n : ℝ)))`. -/
    have h1 : (μ (x ^ (m1 : Nat)) ^ (n / (m1 : Nat))) ^ (1 / (n : Real)) <
        (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : Nat) : Real) / (n : Real))) := by
      have hm10 : (m1 : Real) != 0 := cast_ne_zero.mpr (_root_.ne_of_gt (PNat.pos m1))
      rw [← rpow_lt_rpow_iff (rpow_nonneg (apply_nonneg μ _) _) (le_of_lt hL0')
        (cast_pos.mpr (PNat.pos m1))]; rw [← rpow_mul (apply_nonneg μ _)]; rw [one_div_mul_cancel hm10]; rw [rpow_one] at hm1
      nth_rw 1 [← rpow_one (L + ε / 2)]
      have : (n : Real) / n = (1 : Real) := div_self (cast_ne_zero.mpr (_root_.ne_of_gt hn0))
      nth_rw 2 [← this]; clear this
      nth_rw 3 [← div_add_mod n m1]
      have h_lt : 0 < ((n / m1 : Nat) : Real) / (n : Real) :=
        div_pos (cast_pos.mpr (Nat.div_pos (le_trans (le_max_left _ _) hn) (PNat.pos m1)))
          (cast_pos.mpr hn0)
      rw [← rpow_natCast]; rw [← rpow_add hL0']; rw [← neg_div]; rw [← add_div]; rw [Nat.cast_add]; rw [add_neg_cancel_right]; rw [Nat.cast_mul]; rw [← rpow_mul (apply_nonneg μ _)]; rw [mul_one_div]; rw [mul_div_assoc]; rw [rpow_mul (le_of_lt hL0')]
      exact rpow_lt_rpow (apply_nonneg μ _) hm1 h_lt
    /- We again use the submultiplicativity of `μ` to deduce
    `μ (x ^ (n % m1)) ^ (1 / n) ≤ (μ x ^ (n % m1)) ^ (1 / n)`. -/
    have h2 : μ (x ^ (n % m1)) ^ (1 / (n : Real)) <= (μ x ^ (n % m1)) ^ (1 / (n : Real)) := by
      by_cases hnm1 : n % m1 = 0
      · simpa [hnm1, pow_zero] using rpow_le_rpow (apply_nonneg μ _) hμ1 (one_div_cast_nonneg _)
      · exact rpow_le_rpow (apply_nonneg μ _) (map_pow_le_pow μ _ hnm1) (one_div_cast_nonneg _)
    /- We bound `(L + ε / 2) ^ (1 -n % m1) / n) * (μ x ^ (n % m1)) ^ (1 / n)` by `L + ε`. -/
    have h3 : (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : Nat) : Real) / (n : Real))) *
          (μ x ^ (n % m1)) ^ (1 / (n : Real)) <= L + ε := by
      have heq : L + ε = L + ε / 2 + ε / 2 := by rw [add_assoc, add_halves]
      rw [heq]; rw [← tsub_le_iff_left]
      nth_rw 3 [← mul_one (L + ε / 2)]
      rw [mul_assoc]; rw [← mul_sub]; rw [mul_comm]; rw [← le_div_iff₀ hL0']; rw [div_div]
      exact hm2 n (le_trans (le_max_right (m1 : Nat) m2) hn)
    have h4 : 0 < μ (x ^ (n % ↑m1)) ^ (1 / (n : Real)) := rpow_pos_of_pos hxn' _
    have h5 : 0 < (L + ε / 2) * (L + ε / 2) ^ (-(↑(n % ↑m1) / (n : Real))) :=
      mul_pos hL0' (rpow_pos_of_pos hL0' _)
    /- We combine the previous steps to deduce that
     `μ (x ^ (↑m1 * (n / ↑m1) + n % ↑m1)) ^ (1 / ↑n) < L + ε`. -/
    calc μ (x ^ ((m1 : Nat) * (n / (m1 : Nat)) + n % m1)) ^ (1 / (n : Real)) =
          μ (x ^ ((m1 : Nat) * (n / (m1 : Nat))) * x ^ (n % m1)) ^ (1 / (n : Real)) := by rw [pow_add]
      _ <= (μ (x ^ ((m1 : Nat) * (n / (m1 : Nat)))) * μ (x ^ (n % m1))) ^ (1 / (n : Real)) :=
        (rpow_le_rpow (apply_nonneg μ _) (map_mul_le_mul μ _ _) (one_div_cast_nonneg _))
      _ = μ (x ^ ((m1 : Nat) * (n / (m1 : Nat)))) ^ (1 / (n : Real)) *
          μ (x ^ (n % m1)) ^ (1 / (n : Real)) :=
        (mul_rpow (apply_nonneg μ _) (apply_nonneg μ _))
      _ <= (μ (x ^ (m1 : Nat)) ^ (n / (m1 : Nat))) ^ (1 / (n : Real)) *
            μ (x ^ (n % m1)) ^ (1 / (n : Real)) := by gcongr
      _ < (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : Nat) : Real) / (n : Real))) *
            μ (x ^ (n % m1)) ^ (1 / (n : Real)) := by gcongr
      _ <= (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : Nat) : Real) / (n : Real))) *
            (μ x ^ (n % m1)) ^ (1 / (n : Real)) := by gcongr
      _ <= L + ε := h3

/--
theorem `tendsto_smoothingFun_of_map_one_le_one` / 定理 `tendsto_smoothingFun_of_map_one_le_one`

English:
theorem tendsto_smoothingFun_of_map_one_le_one
  given: (hμ1 : μ 1 <= 1) (x : R)
  proof: by
  by_cases hx : μ x = 0
  · exact tendsto_smoothingFun_of_eq_zero μ hx
  · exact tendsto_smoothingFun_of_ne_zero μ hμ1 hx

中文:
定理 tendsto_smoothingFun_of_map_one_le_one
  条件: (hμ1 : μ 1 <= 1) (x : R)
  证明: by
  by_cases hx : μ x = 0
  · exact tendsto_smoothingFun_of_eq_zero μ hx
  · exact tendsto_smoothingFun_of_ne_zero μ hμ1 hx

Depends on / 依赖: tendsto_smoothingFun_of_eq_zero, tendsto_smoothingFun_of_ne_zero
-/
theorem tendsto_smoothingFun_of_map_one_le_one (hμ1 : μ 1 <= 1) (x : R) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) := by
  by_cases hx : μ x = 0
  · exact tendsto_smoothingFun_of_eq_zero μ hx
  · exact tendsto_smoothingFun_of_ne_zero μ hμ1 hx

/--
theorem `smoothingFun_nonneg` / 定理 `smoothingFun_nonneg`

English:
theorem smoothingFun_nonneg
  given: (hμ1 : μ 1 <= 1) (x : R)
  statement: 0 <= smoothingFun μ x
  proof: by
  apply ge_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
  simpa [eventually_atTop, ge_iff_le] using ⟨1, fun _ _ => by positivity⟩

中文:
定理 smoothingFun_nonneg
  条件: (hμ1 : μ 1 <= 1) (x : R)
  结论: 0 <= smoothingFun μ x
  证明: by
  apply ge_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
  simpa [eventually_atTop, ge_iff_le] using ⟨1, fun _ _ => by positivity⟩

Depends on / 依赖: eventually_atTop, ge_iff_le, ge_of_tendsto, tendsto_smoothingFun_of_map_one_le_one
-/
theorem smoothingFun_nonneg (hμ1 : μ 1 <= 1) (x : R) : 0 <= smoothingFun μ x := by
  apply ge_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
  simpa [eventually_atTop, ge_iff_le] using ⟨1, fun _ _ => by positivity⟩

/--
theorem `smoothingFun_one_le` / 定理 `smoothingFun_one_le`

English:
theorem smoothingFun_one_le
  given: (hμ1 : μ 1 <= 1)
  statement: smoothingFun μ 1 <= 1
  proof: by
  apply le_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (1 : R))
  simp only [eventually_atTop]
  use 1
  rintro n hn
  simp only [smoothingSeminormSeq]
  rw [one_pow]
  conv_rhs => rw [← one_rpow (1 / n : Real)]
  have hn1 : 0 < (1 / n : Real) := by
    apply _root_.div_pos zero_lt_o

中文:
定理 smoothingFun_one_le
  条件: (hμ1 : μ 1 <= 1)
  结论: smoothingFun μ 1 <= 1
  证明: by
  apply le_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (1 : R))
  simp only [eventually_atTop]
  use 1
  rintro n hn
  simp only [smoothingSeminormSeq]
  rw [one_pow]
  conv_rhs => rw [← one_rpow (1 / n : Real)]
  have hn1 : 0 < (1 / n : Real) := by
    apply _root_.div_pos zero_lt_o

Depends on / 依赖: _root_, _root_.div_pos, apply_nonneg, cast_lt, cast_zero, conv_rhs, div_pos, eventually_atTop, le_of_tendsto, one_pow, one_rpow, rpow_le_rpow_iff, smoothingSeminormSeq, succ_le_iff, succ_le_iff.mp, tendsto_smoothingFun_of_map_one_le_one, zero_le_one, zero_lt_one
-/
theorem smoothingFun_one_le (hμ1 : μ 1 <= 1) : smoothingFun μ 1 <= 1 := by
  apply le_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (1 : R))
  simp only [eventually_atTop]
  use 1
  rintro n hn
  simp only [smoothingSeminormSeq]
  rw [one_pow]
  conv_rhs => rw [← one_rpow (1 / n : Real)]
  have hn1 : 0 < (1 / n : Real) := by
    apply _root_.div_pos zero_lt_one
    rw [← cast_zero]; rw [cast_lt]
    exact succ_le_iff.mp hn
  exact (rpow_le_rpow_iff (apply_nonneg μ _) zero_le_one hn1).mpr hμ1

/--
theorem `smoothingFun_le` / 定理 `smoothingFun_le`

English:
theorem smoothingFun_le
  given: (x : R) (n : PNat)
  proof: ciInf_le (smoothingSeminormSeq_bddBelow μ x) _

中文:
定理 smoothingFun_le
  条件: (x : R) (n : P自然数)
  证明: ciInf_le (smoothingSeminormSeq_bddBelow μ x) _

Depends on / 依赖: ciInf_le, smoothingSeminormSeq_bddBelow
-/
theorem smoothingFun_le (x : R) (n : PNat) :
    smoothingFun μ x <= μ (x ^ (n : Nat)) ^ (1 / n : Real) :=
  ciInf_le (smoothingSeminormSeq_bddBelow μ x) _

/--
theorem `smoothingFun_le_self` / 定理 `smoothingFun_le_self`

English:
theorem smoothingFun_le_self
  given: (x : R)
  statement: smoothingFun μ x <= μ x
  proof: by
  apply (smoothingFun_le μ x 1).trans
  rw [PNat.one_coe]; rw [pow_one]; rw [cast_one]; rw [div_one]; rw [rpow_one]

中文:
定理 smoothingFun_le_self
  条件: (x : R)
  结论: smoothingFun μ x <= μ x
  证明: by
  apply (smoothingFun_le μ x 1).trans
  rw [PNat.one_coe]; rw [pow_one]; rw [cast_one]; rw [div_one]; rw [rpow_one]

Depends on / 依赖: PNat.one_coe, cast_one, div_one, one_coe, pow_one, rpow_one, smoothingFun_le
-/
theorem smoothingFun_le_self (x : R) : smoothingFun μ x <= μ x := by
  apply (smoothingFun_le μ x 1).trans
  rw [PNat.one_coe]; rw [pow_one]; rw [cast_one]; rw [div_one]; rw [rpow_one]

/- In this section, we prove that if `μ` is nonarchimedean, then `smoothingFun μ` is
  nonarchimedean. -/
section IsNonarchimedean

variable {x y : R} (hn : forall n : Nat, exists m < n + 1, μ ((x + y) ^ (n : Nat)) ^ (1 / (n : Real)) <=
  (μ (x ^ m) * μ (y ^ (n - m : Nat))) ^ (1 / (n : Real)))

/--
Definition of `mu` / `mu` 的定义

English:
definition mu
  signature: : Nat -> Nat
  body: fun n => Classical.choose (hn n)

中文:
定义 mu
  签名: : 自然数 -> 自然数
  定义体: fun n => Classical.choose (hn n)
-/
private def mu : Nat -> Nat := fun n => Classical.choose (hn n)

/--
theorem `mu_property` / 定理 `mu_property`

English:
theorem mu_property
  given: (n : Nat)
  statement: μ ((x + y) ^ (n : Nat)) ^ (1 / (n : Real)) <=
  proof: (Classical.choose_spec (hn n)).2

中文:
定理 mu_property
  条件: (n : 自然数)
  结论: μ ((x + y) ^ (n : 自然数)) ^ (1 / (n : 实数)) <=
  证明: (Classical.choose_spec (hn n)).2
-/
private theorem mu_property (n : Nat) : μ ((x + y) ^ (n : Nat)) ^ (1 / (n : Real)) <=
    (μ (x ^ mu μ hn n) * μ (y ^ (n - mu μ hn n : Nat))) ^ (1 / (n : Real)) :=
  (Classical.choose_spec (hn n)).2

/--
theorem `mu_le` / 定理 `mu_le`

English:
theorem mu_le
  given: (n : Nat)
  statement: mu μ hn n <= n
  proof: by
  simpa [mu] using (Classical.choose_spec (hn n)).1

中文:
定理 mu_le
  条件: (n : 自然数)
  结论: mu μ hn n <= n
  证明: by
  simpa [mu] using (Classical.choose_spec (hn n)).1
-/
private theorem mu_le (n : Nat) : mu μ hn n <= n := by
  simpa [mu] using (Classical.choose_spec (hn n)).1

/--
theorem `mu_bdd` / 定理 `mu_bdd`

English:
theorem mu_bdd
  given: (n : Nat)
  statement: (mu μ hn n : Real) / n in Set.Icc (0 : Real) 1
  proof: by
  refine Set.mem_Icc.mpr ⟨div_nonneg (cast_nonneg (mu μ hn n)) (cast_nonneg n), ?_⟩
  by_cases hn0 : n = 0
  · rw [hn0, cast_zero, div_zero]; exact zero_le_one
  · rw [div_le_one (cast_pos.mpr (Nat.pos_of_ne_zero hn0)), cast_le]
    exact mu_le _ _ _

中文:
定理 mu_bdd
  条件: (n : 自然数)
  结论: (mu μ hn n : 实数) / n in Set.Icc (0 : 实数) 1
  证明: by
  refine Set.mem_Icc.mpr ⟨div_nonneg (cast_nonneg (mu μ hn n)) (cast_nonneg n), ?_⟩
  by_cases hn0 : n = 0
  · rw [hn0, cast_zero, div_zero]; exact zero_le_one
  · rw [div_le_one (cast_pos.mpr (Nat.pos_of_ne_zero hn0)), cast_le]
    exact mu_le _ _ _
-/
private theorem mu_bdd (n : Nat) : (mu μ hn n : Real) / n in Set.Icc (0 : Real) 1 := by
  refine Set.mem_Icc.mpr ⟨div_nonneg (cast_nonneg (mu μ hn n)) (cast_nonneg n), ?_⟩
  by_cases hn0 : n = 0
  · rw [hn0, cast_zero, div_zero]; exact zero_le_one
  · rw [div_le_one (cast_pos.mpr (Nat.pos_of_ne_zero hn0)), cast_le]
    exact mu_le _ _ _

/--
theorem `μ_bddBelow` / 定理 `μ_bddBelow`

English:
theorem μ_bddBelow
  given: (s : Nat -> Nat) {x : R} (ψ : Nat -> Nat)
  proof: by
  use 0
  simp only [mem_lowerBounds, eventually_map, eventually_atTop, Set.mem_ofPred_eq,
    forall_exists_index]
  intro r m hm
  exact le_trans (rpow_nonneg (apply_nonneg μ _) _) (hm m (le_refl _))

中文:
定理 μ_bddBelow
  条件: (s : 自然数 -> 自然数) {x : R} (ψ : 自然数 -> 自然数)
  证明: by
  use 0
  simp only [mem_lowerBounds, eventually_map, eventually_atTop, Set.mem_ofPred_eq,
    forall_exists_index]
  intro r m hm
  exact le_trans (rpow_nonneg (apply_nonneg μ _) _) (hm m (le_refl _))
-/
private theorem μ_bddBelow (s : Nat -> Nat) {x : R} (ψ : Nat -> Nat) :
    BddBelow {a : Real |
      forallᶠ n : Real in map (fun n : Nat => μ x ^ (↑(s (ψ n)) * (1 / (ψ n : Real)))) atTop, n <= a} := by
  use 0
  simp only [mem_lowerBounds, eventually_map, eventually_atTop, Set.mem_ofPred_eq,
    forall_exists_index]
  intro r m hm
  exact le_trans (rpow_nonneg (apply_nonneg μ _) _) (hm m (le_refl _))

/--
theorem `μ_bddAbove` / 定理 `μ_bddAbove`

English:
theorem μ_bddAbove
  statement: (hμ1 : μ 1 <= 1) {s : Nat -> Nat} (hs : forall n : Nat, s n <= n) (x : R)
  proof: by
  have hψ : forall n, 0 <= 1 / (ψ n : Real) := fun _ => by simp only [one_div, inv_nonneg, cast_nonneg]
  by_cases! hx : μ x <= 1
  · use 1
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index]
    rintro _ n rfl
    apply le_trans (rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' h

中文:
定理 μ_bddAbove
  结论: (hμ1 : μ 1 <= 1) {s : 自然数 -> 自然数} (hs : 对任意 n : 自然数, s n <= n) (x : R)
  证明: by
  have hψ : forall n, 0 <= 1 / (ψ n : Real) := fun _ => by simp only [one_div, inv_nonneg, cast_nonneg]
  by_cases! hx : μ x <= 1
  · use 1
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index]
    rintro _ n rfl
    apply le_trans (rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' h
-/
private theorem μ_bddAbove (hμ1 : μ 1 <= 1) {s : Nat -> Nat} (hs : forall n : Nat, s n <= n) (x : R)
    (ψ : Nat -> Nat) : BddAbove (Set.range fun n : Nat => μ (x ^ s (ψ n)) ^ (1 / (ψ n : Real))) := by
  have hψ : forall n, 0 <= 1 / (ψ n : Real) := fun _ => by simp only [one_div, inv_nonneg, cast_nonneg]
  by_cases! hx : μ x <= 1
  · use 1
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index]
    rintro _ n rfl
    apply le_trans (rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' hμ1 _ _) (hψ n))
    rw [← rpow_natCast]; rw [← rpow_mul (apply_nonneg _ _)]; rw [mul_one_div]
    exact rpow_le_one (apply_nonneg _ _) hx (div_nonneg (cast_nonneg _) (cast_nonneg _))
  · use μ x
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index]
    rintro _ n rfl
    apply le_trans (rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' hμ1 _ _) (hψ n))
    rw [← rpow_natCast]; rw [← rpow_mul (apply_nonneg _ _)]; rw [mul_one_div]
    conv_rhs => rw [← rpow_one (μ x)]
    rw [rpow_le_rpow_left_iff hx]
    exact div_le_one_of_le₀ (cast_le.mpr (hs (ψ n))) (cast_nonneg _)

/--
theorem `μ_bddAbove'` / 定理 `μ_bddAbove'`

English:
theorem μ_bddAbove'
  statement: (hμ1 : μ 1 <= 1) {s : Nat -> Nat} (hs : forall n : Nat, s n <= n) (x : R)
  proof: by
  rw [Set.image_eq_range]
  convert! μ_bddAbove μ hμ1 hs x ψ
  ext
  simp [one_div, Set.mem_range, Subtype.exists, Set.mem_univ, exists_const]

中文:
定理 μ_bddAbove'
  结论: (hμ1 : μ 1 <= 1) {s : 自然数 -> 自然数} (hs : 对任意 n : 自然数, s n <= n) (x : R)
  证明: by
  rw [Set.image_eq_range]
  convert! μ_bddAbove μ hμ1 hs x ψ
  ext
  simp [one_div, Set.mem_range, Subtype.exists, Set.mem_univ, exists_const]
-/
private theorem μ_bddAbove' (hμ1 : μ 1 <= 1) {s : Nat -> Nat} (hs : forall n : Nat, s n <= n) (x : R)
    (ψ : Nat -> Nat) : BddAbove ((fun n : Nat => μ (x ^ s (ψ n)) ^ (1 / (ψ n : Real))) '' Set.univ) := by
  rw [Set.image_eq_range]
  convert! μ_bddAbove μ hμ1 hs x ψ
  ext
  simp [one_div, Set.mem_range, Subtype.exists, Set.mem_univ, exists_const]

/--
theorem `μ_nonempty` / 定理 `μ_nonempty`

English:
theorem μ_nonempty
  given: {s : Nat -> Nat} (hs_le : forall n : Nat, s n <= n) {x : R} (ψ : Nat -> Nat)
  proof: by
  by_cases hμx : μ x < 1
  · use 1
    simp only [eventually_map, eventually_atTop, Set.mem_ofPred_eq]
    exact ⟨0, fun _ _ => rpow_le_one (apply_nonneg _ _) (le_of_lt hμx)
      (mul_nonneg (cast_nonneg _) (one_div_nonneg.mpr (cast_nonneg _)))⟩
  · use μ x
    simp only [eventually_map, eventua

中文:
定理 μ_nonempty
  条件: {s : 自然数 -> 自然数} (hs_le : 对任意 n : 自然数, s n <= n) {x : R} (ψ : 自然数 -> 自然数)
  证明: by
  by_cases hμx : μ x < 1
  · use 1
    simp only [eventually_map, eventually_atTop, Set.mem_ofPred_eq]
    exact ⟨0, fun _ _ => rpow_le_one (apply_nonneg _ _) (le_of_lt hμx)
      (mul_nonneg (cast_nonneg _) (one_div_nonneg.mpr (cast_nonneg _)))⟩
  · use μ x
    simp only [eventually_map, eventua
-/
private theorem μ_nonempty {s : Nat -> Nat} (hs_le : forall n : Nat, s n <= n) {x : R} (ψ : Nat -> Nat) :
    {a : Real | forallᶠ n : Real in map (fun n : Nat => μ x ^ (↑(s (ψ n)) * (1 / (ψ n : Real)))) atTop,
      n <= a}.Nonempty := by
  by_cases hμx : μ x < 1
  · use 1
    simp only [eventually_map, eventually_atTop, Set.mem_ofPred_eq]
    exact ⟨0, fun _ _ => rpow_le_one (apply_nonneg _ _) (le_of_lt hμx)
      (mul_nonneg (cast_nonneg _) (one_div_nonneg.mpr (cast_nonneg _)))⟩
  · use μ x
    simp only [eventually_map, eventually_atTop, Set.mem_ofPred_eq]
    use 0
    intro b _
    nth_rw 2 [← rpow_one (μ x)]
    apply rpow_le_rpow_of_exponent_le (not_lt.mp hμx)
    rw [mul_one_div]
    exact div_le_one_of_le₀ (cast_le.mpr (hs_le (ψ b))) (cast_nonneg _)

/--
theorem `μ_limsup_le_one` / 定理 `μ_limsup_le_one`

English:
theorem μ_limsup_le_one
  statement: {s : Nat -> Nat} (hs_le : forall n : Nat, s n <= n) {x : R} {ψ : Nat -> Nat}
  proof: by
  simp only [limsup, limsSup]
  rw [csInf_le_iff (μ_bddBelow μ s ψ) (μ_nonempty μ hs_le ψ)]
  · intro c hc_bd
    simp only [mem_lowerBounds, eventually_map, eventually_atTop, Set.mem_ofPred_eq,
      forall_exists_index] at hc_bd
    by_cases hμx : μ x < 1
    · apply hc_bd (1 : Real) 0
      in

中文:
定理 μ_limsup_le_one
  结论: {s : 自然数 -> 自然数} (hs_le : 对任意 n : 自然数, s n <= n) {x : R} {ψ : 自然数 -> 自然数}
  证明: by
  simp only [limsup, limsSup]
  rw [csInf_le_iff (μ_bddBelow μ s ψ) (μ_nonempty μ hs_le ψ)]
  · intro c hc_bd
    simp only [mem_lowerBounds, eventually_map, eventually_atTop, Set.mem_ofPred_eq,
      forall_exists_index] at hc_bd
    by_cases hμx : μ x < 1
    · apply hc_bd (1 : Real) 0
      in
-/
private theorem μ_limsup_le_one {s : Nat -> Nat} (hs_le : forall n : Nat, s n <= n) {x : R} {ψ : Nat -> Nat}
    (hψ_lim : Tendsto ((fun n : Nat => ↑(s n) / (n : Real)) ∘ ψ) atTop (𝓝 0)) :
    limsup (fun n : Nat => μ x ^ ((s (ψ n) : Real) * (1 / (ψ n : Real)))) atTop <= 1 := by
  simp only [limsup, limsSup]
  rw [csInf_le_iff (μ_bddBelow μ s ψ) (μ_nonempty μ hs_le ψ)]
  · intro c hc_bd
    simp only [mem_lowerBounds, eventually_map, eventually_atTop, Set.mem_ofPred_eq,
      forall_exists_index] at hc_bd
    by_cases hμx : μ x < 1
    · apply hc_bd (1 : Real) 0
      intro b _
      exact rpow_le_one (apply_nonneg _ _) (le_of_lt hμx)
          (mul_nonneg (cast_nonneg _) (one_div_nonneg.mpr (cast_nonneg _)))
    · have hμ_lim : Tendsto (fun n : Nat => μ x ^ (↑(s (ψ n)) * (1 / (ψ n : Real)))) atTop (𝓝 1) := by
        nth_rw 1 [← rpow_zero (μ x)]
        convert!
          Tendsto.rpow tendsto_const_nhds hψ_lim
            (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (not_lt.mp hμx))))
        · simp only [rpow_zero, mul_one_div, Function.comp_apply]
        · rw [rpow_zero]
      rw [tendsto_atTop_nhds] at hμ_lim
      apply le_of_forall_pos_le_add
      intro ε hε
      have h1 : (1 : Real) in Set.Ioo 0 (1 + ε) := by
        simp only [Set.mem_Ioo, zero_lt_one, lt_add_iff_pos_right, hε, and_self]
      obtain ⟨k, hk⟩ := hμ_lim (Set.Ioo (0 : Real) (1 + ε)) h1 isOpen_Ioo
      exact hc_bd (1 + ε) k fun b hb => le_of_lt (Set.mem_Ioo.mp (hk b hb)).2

/--
theorem `limsup_mu_le` / 定理 `limsup_mu_le`

English:
theorem limsup_mu_le
  statement: (hμ1 : μ 1 <= 1) {s : Nat -> Nat} (hs_le : forall n : Nat, s n <= n) {x : R}
  proof: by
  by_cases ha : a = 0
  · rw [ha] at hψ_lim
    calc limsup (fun n : Nat => μ (x ^ s (ψ n)) ^ (1 / (ψ n : Real))) atTop <=
          limsup (fun n : Nat => μ x ^ ((s (ψ n) : Real) * (1 / (ψ n : Real)))) atTop := by
          apply csInf_le_csInf _ (μ_nonempty μ hs_le ψ)
          · intro b hb
   

中文:
定理 limsup_mu_le
  结论: (hμ1 : μ 1 <= 1) {s : 自然数 -> 自然数} (hs_le : 对任意 n : 自然数, s n <= n) {x : R}
  证明: by
  by_cases ha : a = 0
  · rw [ha] at hψ_lim
    calc limsup (fun n : Nat => μ (x ^ s (ψ n)) ^ (1 / (ψ n : Real))) atTop <=
          limsup (fun n : Nat => μ x ^ ((s (ψ n) : Real) * (1 / (ψ n : Real)))) atTop := by
          apply csInf_le_csInf _ (μ_nonempty μ hs_le ψ)
          · intro b hb
   
-/
private theorem limsup_mu_le (hμ1 : μ 1 <= 1) {s : Nat -> Nat} (hs_le : forall n : Nat, s n <= n) {x : R}
    {a : Real} (a_in : a in Set.Icc (0 : Real) 1) {ψ : Nat -> Nat} (hψ_mono : StrictMono ψ)
    (hψ_lim : Tendsto ((fun n : Nat => (s n : Real) / ↑n) ∘ ψ) atTop (𝓝 a)) :
    limsup (fun n : Nat => μ (x ^ s (ψ n)) ^ (1 / (ψ n : Real))) atTop <= smoothingFun μ x ^ a := by
  by_cases ha : a = 0
  · rw [ha] at hψ_lim
    calc limsup (fun n : Nat => μ (x ^ s (ψ n)) ^ (1 / (ψ n : Real))) atTop <=
          limsup (fun n : Nat => μ x ^ ((s (ψ n) : Real) * (1 / (ψ n : Real)))) atTop := by
          apply csInf_le_csInf _ (μ_nonempty μ hs_le ψ)
          · intro b hb
            simp only [eventually_map, eventually_atTop, Set.mem_ofPred_eq] at hb ⊢
            obtain ⟨m, hm⟩ := hb
            use m
            intro k hkm
            apply le_trans _ (hm k hkm)
            rw [rpow_mul (apply_nonneg μ x)]; rw [rpow_natCast]
            gcongr
            exact map_pow_le_pow' hμ1 x _
          · use 0
            simp only [mem_lowerBounds, eventually_map, eventually_atTop,
              Set.mem_ofPred_eq, forall_exists_index]
            exact fun _ m hm => le_trans (by positivity) (hm m (le_refl _))
      _ <= 1 := (μ_limsup_le_one μ hs_le hψ_lim)
      _ = smoothingFun μ x ^ a := by rw [ha, rpow_zero]
  · have ha_pos : 0 < a := lt_of_le_of_ne a_in.1 (Ne.symm ha)
    have h_eq : (fun n : Nat =>
        (μ (x ^ s (ψ n)) ^ (1 / (s (ψ n) : Real))) ^ ((s (ψ n) : Real) / (ψ n : Real))) =ᶠ[atTop]
        fun n : Nat => μ (x ^ s (ψ n)) ^ (1 / (ψ n : Real)) := by
      have h : (fun n : Nat => (1 : Real) / (s (ψ n) : Real) * (s (ψ n) : Real)) =ᶠ[atTop] 1 := by
        apply Filter.EventuallyEq.div_mul_cancel_atTop
        exact (tendsto_natCast_atTop_atTop.comp hψ_mono.tendsto_atTop).num ha_pos hψ_lim
      simp_rw [← rpow_mul (apply_nonneg μ _), mul_div]
      exact EventuallyEq.comp₂ EventuallyEq.rfl HPow.hPow (h.div EventuallyEq.rfl)
    exact ((tendsto_smoothingFun_of_map_one_le_one μ hμ1 x |>.comp <|
tendsto_natCast_atTop_iff.mp (tendsto_natCast_atTop_atTop.comp
        hψ_mono.tendsto_atTop).num ha_pos hψ_lim).rpow
hψ_lim .inr ha_pos).congr' h_eq |>.limsup_eq.le

/--
theorem `tendsto_smoothingFun_comp` / 定理 `tendsto_smoothingFun_comp`

English:
theorem tendsto_smoothingFun_comp
  statement: (hμ1 : μ 1 <= 1) (x : R) {ψ : Nat -> Nat}
  proof: have hψ_lim' : Tendsto ψ atTop atTop := StrictMono.tendsto_atTop hψ_mono
  (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).comp hψ_lim'

中文:
定理 tendsto_smoothingFun_comp
  结论: (hμ1 : μ 1 <= 1) (x : R) {ψ : 自然数 -> 自然数}
  证明: have hψ_lim' : Tendsto ψ atTop atTop := StrictMono.tendsto_atTop hψ_mono
  (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).comp hψ_lim'

Depends on / 依赖: StrictMono, StrictMono.tendsto_atTop, Tendsto, tendsto_atTop, tendsto_smoothingFun_of_map_one_le_one
-/
theorem tendsto_smoothingFun_comp (hμ1 : μ 1 <= 1) (x : R) {ψ : Nat -> Nat}
    (hψ_mono : StrictMono ψ) :
    Tendsto (fun n : Nat => μ (x ^ ψ n) ^ (1 / ψ n : Real)) atTop (𝓝 (smoothingFun μ x)) :=
  have hψ_lim' : Tendsto ψ atTop atTop := StrictMono.tendsto_atTop hψ_mono
  (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).comp hψ_lim'

/--
theorem `isNonarchimedean_smoothingFun` / 定理 `isNonarchimedean_smoothingFun`

English:
theorem isNonarchimedean_smoothingFun
  given: (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ)
  proof: by
  -- Fix `x, y : R`.
  intro x y
  have hn : forall n : Nat, exists m < n + 1,
      μ ((x + y) ^ (n : Nat)) ^ (1 / (n : Real)) <= (μ (x ^ m) * μ (y ^ (n - m : Nat))) ^ (1 / (n : Real)) :=
    fun n => RingSeminorm.exists_index_pow_le μ hna x y n
  /- For each `n : ℕ`, we find `mu n` and `nu n` s

中文:
定理 isNonarchimedean_smoothingFun
  条件: (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ)
  证明: by
  -- Fix `x, y : R`.
  intro x y
  have hn : forall n : Nat, exists m < n + 1,
      μ ((x + y) ^ (n : Nat)) ^ (1 / (n : Real)) <= (μ (x ^ m) * μ (y ^ (n - m : Nat))) ^ (1 / (n : Real)) :=
    fun n => RingSeminorm.exists_index_pow_le μ hna x y n
  /- For each `n : ℕ`, we find `mu n` and `nu n` s
-/
theorem isNonarchimedean_smoothingFun (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) :
    IsNonarchimedean (smoothingFun μ) := by
  -- Fix `x, y : R`.
  intro x y
  have hn : forall n : Nat, exists m < n + 1,
      μ ((x + y) ^ (n : Nat)) ^ (1 / (n : Real)) <= (μ (x ^ m) * μ (y ^ (n - m : Nat))) ^ (1 / (n : Real)) :=
    fun n => RingSeminorm.exists_index_pow_le μ hna x y n
  /- For each `n : ℕ`, we find `mu n` and `nu n` such that `mu n + nu n = n` and
    `μ ((x + y) ^ n) ^ (1 / n) ≤ (μ (x ^ (mu n)) * μ (y ^ (nu n))) ^ (1 / n)`. -/
  let mu : Nat -> Nat := fun n => mu μ hn n
  set nu : Nat -> Nat := fun n => n - mu n with hnu
  have hmu_le : forall n : Nat, mu n <= n := fun n => mu_le μ hn n
  have hmu_bdd : forall n : Nat, (mu n : Real) / n in Set.Icc (0 : Real) 1 := fun n => mu_bdd μ hn n
  have hs : Bornology.IsBounded (Set.Icc (0 : Real) 1) := Metric.isBounded_Icc 0 1
  /- Since `0 ≤ (mu n) / n ≤ 1` for all `n`, we can find a subsequence `(ψ n) ⊆ ℕ` such that the
    limit of `mu (ψ n) / ψ n` as `n` tends to infinity exists. We denote this limit by `a`. -/
  obtain ⟨a, a_in, ψ, hψ_mono, hψ_lim⟩ := tendsto_subseq_of_bounded hs hmu_bdd
  rw [closure_Icc] at a_in
  /- The limit of `nu (ψ n) / ψ n` as `n` tends to infinity also exists, and it is equal to
    `b := 1 - a` -/
  set b := 1 - a with hb
  have hb_lim : Tendsto ((fun n : Nat => (nu n : Real) / ↑n) ∘ ψ) atTop (𝓝 b) := by
    apply Tendsto.congr' _ (Tendsto.const_sub 1 hψ_lim)
    simp only [EventuallyEq, Function.comp_apply, eventually_atTop]
    use 1
    intro m hm
    have h0 : (ψ m : Real) != 0 := cast_ne_zero.mpr
      (hψ_mono (Nat.pos_of_ne_zero (one_le_iff_ne_zero.mp hm))).ne_zero
    rw [← div_self h0]; rw [← sub_div]; rw [cast_sub (hmu_le _)]
  have b_in : b in Set.Icc (0 : Real) 1 := Set.Icc.mem_iff_one_sub_mem.mp a_in
  have hnu_le : forall n : Nat, nu n <= n := fun n => by simp only [hnu, tsub_le_self]
  have hx : limsup (fun n : Nat => μ (x ^ mu (ψ n)) ^ (1 / (ψ n : Real))) atTop <=
      smoothingFun μ x ^ a := limsup_mu_le μ hμ1 hmu_le a_in hψ_mono hψ_lim
  have hy : limsup (fun n : Nat => μ (y ^ nu (ψ n)) ^ (1 / (ψ n : Real))) atTop <=
      smoothingFun μ y ^ b :=
    limsup_mu_le μ hμ1 hnu_le b_in hψ_mono hb_lim
  have hxy : limsup
      (fun n => μ (x ^ mu (ψ n)) ^ (1 / (ψ n : Real)) * μ (y ^ nu (ψ n)) ^ (1 / (ψ n : Real))) atTop <=
        smoothingFun μ x ^ a * smoothingFun μ y ^ b := by
    have hxy' :
      limsup (fun n : Nat => μ (x ^ mu (ψ n)) ^ (1 / (ψ n : Real)) * μ (y ^ nu (ψ n)) ^ (1 / (ψ n : Real)))
        atTop <= limsup (fun n : Nat => μ (x ^ mu (ψ n)) ^ (1 / (ψ n : Real))) atTop *
          limsup (fun n : Nat => μ (y ^ nu (ψ n)) ^ (1 / (ψ n : Real))) atTop :=
      limsup_mul_le (Frequently.of_forall (fun n => by positivity))
        (μ_bddAbove μ hμ1 hmu_le x ψ).isBoundedUnder_of_range
        (Eventually.of_forall (fun n => by positivity))
        (μ_bddAbove μ hμ1 hnu_le y ψ).isBoundedUnder_of_range
    have h_bdd : IsBoundedUnder LE.le atTop fun n : Nat => μ (y ^ nu (ψ n)) ^ (1 / (ψ n : Real)) :=
      RingSeminorm.isBoundedUnder μ hμ1 hnu_le ψ
    apply le_trans hxy' (mul_le_mul hx hy (le_limsup_of_frequently_le (Frequently.of_forall
      (fun n => by positivity)) h_bdd) (rpow_nonneg (smoothingFun_nonneg μ hμ1 x) _))
  apply le_of_forall_sub_le
  /- Fix `ε > 0`. We first show that `smoothingFun μ x ^ a * smoothingFun μ y ^ b + ε ≤
    max (smoothingFun μ x) (smoothingFun μ y) + ε`. -/
  intro ε hε
  rw [sub_le_iff_le_add]
  have h_mul : smoothingFun μ x ^ a * smoothingFun μ y ^ b + ε <=
      max (smoothingFun μ x) (smoothingFun μ y) + ε := by
    rw [max_def]
    split_ifs with h
    · rw [add_le_add_iff_right]
      apply le_trans (mul_le_mul_of_nonneg_right
        (rpow_le_rpow (smoothingFun_nonneg μ hμ1 _) h a_in.1)
        (rpow_nonneg (smoothingFun_nonneg μ hμ1 _) _))
      rw [hb]; rw [← rpow_add_of_nonneg (smoothingFun_nonneg μ hμ1 _) a_in.1
        (sub_nonneg.mpr a_in.2)]; rw [add_sub]; rw [add_sub_cancel_left]; rw [rpow_one]
    · rw [add_le_add_iff_right]
      apply le_trans (mul_le_mul_of_nonneg_left
        (rpow_le_rpow (smoothingFun_nonneg μ hμ1 _) (le_of_lt (not_le.mp h)) b_in.1)
        (rpow_nonneg (smoothingFun_nonneg μ hμ1 _) _))
      rw [hb]; rw [← rpow_add_of_nonneg (smoothingFun_nonneg μ hμ1 _) a_in.1
        (sub_nonneg.mpr a_in.2)]; rw [add_sub]; rw [add_sub_cancel_left]; rw [rpow_one]
  apply le_trans _ h_mul
  /- We then show that there exists some natural number `N` such that
    `μ (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ)) * μ (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ)) <
      smoothingFun μ x ^ a * smoothingFun μ y ^ b + ε`. -/
  have hex : exists n : PNat, μ (x ^ mu (ψ n)) ^ (1 / (ψ n : Real)) * μ (y ^ nu (ψ n)) ^ (1 / (ψ n : Real)) <
      smoothingFun μ x ^ a * smoothingFun μ y ^ b + ε :=
    Filter.exists_lt_of_limsup_le (bddAbove_range_mul (μ_bddAbove μ hμ1 hmu_le _ _)
      (fun n => by positivity) (μ_bddAbove μ hμ1 hnu_le _ _)
      (fun n => by positivity)).isBoundedUnder_of_range hxy hε
  obtain ⟨N, hN⟩ := hex
  /- By definition of `smoothingFun`, and applying the inequality `hN`, it suffices to show that
    `μ ((x + y) ^ ψ N) ^ (1 / ψ N) ≤ μ (x ^ mu (ψ N)) ^ (1 / ψ N) * μ (y ^ nu ψ N) ^ (1 / ψ N)`. -/
  apply (ciInf_le (smoothingSeminormSeq_bddBelow μ _)
    ⟨ψ N, (hψ_mono.lt_iff_lt.mpr N.pos).pos⟩).trans (hN.le.trans' _)
  simpa [PNat.mk_coe, hnu, ← mul_rpow (apply_nonneg μ _) (apply_nonneg μ _)] using
    mu_property μ hn (ψ N)

end IsNonarchimedean

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `smoothingSeminorm` / `smoothingSeminorm` 的定义

English:
definition smoothingSeminorm
  signature: (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ)
  body: smoothingFun μ
  map_zero' := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 0)
      tendsto_const_nhds
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    simp only [smoothingSeminormSeq]
    rw [zero_pow (pos_iff_ne_zero.mp h

中文:
定义 smoothingSeminorm
  签名: (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ)
  定义体: smoothingFun μ
  map_zero' := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 0)
      tendsto_const_nhds
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    simp only [smoothingSeminormSeq]
    rw [zero_pow (pos_iff_ne_zero.mp h

Depends on / 依赖: smoothingFun
-/
def smoothingSeminorm (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) : RingSeminorm R where
  toFun := smoothingFun μ
  map_zero' := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 0)
      tendsto_const_nhds
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    simp only [smoothingSeminormSeq]
    rw [zero_pow (pos_iff_ne_zero.mp hn)]; rw [map_zero]; rw [zero_rpow]
    exact one_div_ne_zero (cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn))
  add_le' _ _ := (isNonarchimedean_smoothingFun μ hμ1 hna).add_le (smoothingFun_nonneg μ hμ1)
  neg' n := by
    simp only [smoothingFun]
    congr
    ext n
    rw [neg_pow]
    rcases neg_one_pow_eq_or R n with hpos | hneg
    · rw [hpos, one_mul]
    · rw [hneg, neg_one_mul, map_neg_eq_map μ]
  mul_le' x y := by
    apply le_of_tendsto_of_tendsto' (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x * y))
      (Tendsto.mul (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
        (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y))
    intro n
    have hn : 0 <= 1 / (n : Real) := by simp only [one_div, inv_nonneg, cast_nonneg]
    simp only [smoothingSeminormSeq]
    rw [← mul_rpow (apply_nonneg μ _) (apply_nonneg μ _)]; rw [mul_pow]
    gcongr
    exact map_mul_le_mul μ _ _

/--
theorem `smoothingSeminorm_map_one_le_one` / 定理 `smoothingSeminorm_map_one_le_one`

English:
theorem smoothingSeminorm_map_one_le_one
  statement: (hμ1 : μ 1 <= 1)
  proof: smoothingFun_one_le μ hμ1

中文:
定理 smoothingSeminorm_map_one_le_one
  结论: (hμ1 : μ 1 <= 1)
  证明: smoothingFun_one_le μ hμ1

Depends on / 依赖: CountableCategory, CountableCategory.mk, Subsingleton, Subsingleton.elim, smoothingFun_one_le
-/
theorem smoothingSeminorm_map_one_le_one (hμ1 : μ 1 <= 1)
    (hna : IsNonarchimedean μ) : smoothingSeminorm μ hμ1 hna 1 <= 1 :=
  smoothingFun_one_le μ hμ1

/--
theorem `isPowMul_smoothingFun` / 定理 `isPowMul_smoothingFun`

English:
theorem isPowMul_smoothingFun
  given: (hμ1 : μ 1 <= 1)
  statement: IsPowMul (smoothingFun μ)
  proof: by
  intro x m hm
  have hlim : Tendsto (fun n => smoothingSeminormSeq μ x (m * n)) atTop
      (𝓝 (smoothingFun μ x)) :=
    Tendsto.comp (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x) (tendsto_atTop_atTop_of_monotone
      (fun n k hnk => mul_le_mul_right hnk m) (fun n => ⟨n, le_mul_of_one_le_le

中文:
定理 isPowMul_smoothingFun
  条件: (hμ1 : μ 1 <= 1)
  结论: IsPowMul (smoothingFun μ)
  证明: by
  intro x m hm
  have hlim : Tendsto (fun n => smoothingSeminormSeq μ x (m * n)) atTop
      (𝓝 (smoothingFun μ x)) :=
    Tendsto.comp (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x) (tendsto_atTop_atTop_of_monotone
      (fun n k hnk => mul_le_mul_right hnk m) (fun n => ⟨n, le_mul_of_one_le_le

Depends on / 依赖: Tendsto, Tendsto.comp, Tendsto.pow, _root_, _root_.ne_of_, cast_ne_zero, cast_ne_zero.mpr, h_eq, le_mul_of_one_le_left, mul_le_mul_right, ne_of_, smoothingFun, smoothingSeminormSeq, tendsto_atTop_atTop_of_monotone, tendsto_nhds_unique, tendsto_smoothingFun_of_map_one_le_one
-/
theorem isPowMul_smoothingFun (hμ1 : μ 1 <= 1) : IsPowMul (smoothingFun μ) := by
  intro x m hm
  have hlim : Tendsto (fun n => smoothingSeminormSeq μ x (m * n)) atTop
      (𝓝 (smoothingFun μ x)) :=
    Tendsto.comp (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x) (tendsto_atTop_atTop_of_monotone
      (fun n k hnk => mul_le_mul_right hnk m) (fun n => ⟨n, le_mul_of_one_le_left' hm⟩))
  apply tendsto_nhds_unique _ (Tendsto.pow hlim m)
  have h_eq (n : Nat) : smoothingSeminormSeq μ x (m * n) ^ m = smoothingSeminormSeq μ (x ^ m) n := by
    have hm' : (m : Real) != 0 := cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_lt_of_le zero_lt_one hm))
    simp only [smoothingSeminormSeq]
    rw [pow_mul]; rw [← rpow_natCast]; rw [← rpow_mul (apply_nonneg μ _)]; rw [cast_mul]; rw [← one_div_mul_one_div]; rw [mul_comm (1 / (m : Real))]; rw [mul_assoc]; rw [one_div_mul_cancel hm']; rw [mul_one]
  simpa [h_eq] using tendsto_smoothingFun_of_map_one_le_one μ hμ1 _

/--
theorem `smoothingFun_of_powMul` / 定理 `smoothingFun_of_powMul`

English:
theorem smoothingFun_of_powMul
  statement: (hμ1 : μ 1 <= 1) {x : R}
  proof: by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  have hn0 : (n : Real) != 0 := cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn)
  rw

中文:
定理 smoothingFun_of_powMul
  结论: (hμ1 : μ 1 <= 1) {x : R}
  证明: by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  have hn0 : (n : Real) != 0 := cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn)
  rw

Depends on / 依赖: EventuallyEq, apply_nonneg, cast_ne_zero, cast_ne_zero.mpr, eventually_atTop, mul_one_div_cancel, one_le_iff_ne_zero, one_le_iff_ne_zero.mp, rpow_mul, rpow_natCast, rpow_one, smoothingSeminormSeq, tendsto_const_nhds, tendsto_nhds_unique_of_eventuallyEq, tendsto_smoothingFun_of_map_one_le_one
-/
theorem smoothingFun_of_powMul (hμ1 : μ 1 <= 1) {x : R}
    (hx : forall (n : Nat) (_hn : 1 <= n), μ (x ^ n) = μ x ^ n) : smoothingFun μ x = μ x := by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  have hn0 : (n : Real) != 0 := cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn)
  rw [hx n hn]; rw [← rpow_natCast]; rw [← rpow_mul (apply_nonneg μ _)]; rw [mul_one_div_cancel hn0]; rw [rpow_one]

/--
theorem `smoothingFun_apply_of_map_mul_eq_mul` / 定理 `smoothingFun_apply_of_map_mul_eq_mul`

English:
theorem smoothingFun_apply_of_map_mul_eq_mul
  statement: (hμ1 : μ 1 <= 1) {x : R}
  proof: by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  by_cases hx0 : μ x = 0
  · have hxn : μ (x ^ n) = 0 := by
      apply le_antis

中文:
定理 smoothingFun_apply_of_map_mul_eq_mul
  结论: (hμ1 : μ 1 <= 1) {x : R}
  证明: by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  by_cases hx0 : μ x = 0
  · have hxn : μ (x ^ n) = 0 := by
      apply le_antis

Depends on / 依赖: Countable, Countable.of_equiv, EventuallyEq, InducedCategory, InducedCategory.homEquiv.symm, apply_nonneg, eventually_atTop, homEquiv, le_antisymm, le_trans, map_pow_le_pow, of_equiv, one_div_cast_ne_zero, one_le_iff_ne_zero, one_le_iff_ne_zero.mp, pos_iff_ne_zero, pos_iff_ne_zero.mp, smoothingSeminormSeq, tendsto_const_nhds, tendsto_nhds_unique_of_eventuallyEq
-/
theorem smoothingFun_apply_of_map_mul_eq_mul (hμ1 : μ 1 <= 1) {x : R}
    (hx : forall y : R, μ (x * y) = μ x * μ y) : smoothingFun μ x = μ x := by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  by_cases hx0 : μ x = 0
  · have hxn : μ (x ^ n) = 0 := by
      apply le_antisymm _ (apply_nonneg μ _)
      apply le_trans (map_pow_le_pow μ x (one_le_iff_ne_zero.mp hn))
      rw [hx0]; rw [zero_pow (pos_iff_ne_zero.mp hn)]
    rw [hx0]; rw [hxn]; rw [zero_rpow (one_div_cast_ne_zero (one_le_iff_ne_zero.mp hn))]
  · have h1 : μ 1 = 1 := by rw [← mul_right_inj' hx0, ← hx 1, mul_one, mul_one]
    have hn0 : (n : Real) != 0 := cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_lt_of_le zero_lt_one hn))
    rw [← mul_one (x ^ n)]; rw [pow_mul_apply_eq_pow_mul μ hx]; rw [← rpow_natCast]; rw [h1]; rw [mul_one]; rw [← rpow_mul (apply_nonneg μ _)]; rw [mul_one_div_cancel hn0]; rw [rpow_one]

/--
theorem `smoothingSeminorm_apply_of_map_mul_eq_mul` / 定理 `smoothingSeminorm_apply_of_map_mul_eq_mul`

English:
theorem smoothingSeminorm_apply_of_map_mul_eq_mul
  statement: (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) {x : R}
  proof: smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx

中文:
定理 smoothingSeminorm_apply_of_map_mul_eq_mul
  结论: (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) {x : R}
  证明: smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx

Depends on / 依赖: smoothingFun_apply_of_map_mul_eq_mul
-/
theorem smoothingSeminorm_apply_of_map_mul_eq_mul (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) {x : R}
    (hx : forall y : R, μ (x * y) = μ x * μ y) : smoothingSeminorm μ hμ1 hna x = μ x :=
  smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx

/--
theorem `smoothingFun_of_map_mul_eq_mul` / 定理 `smoothingFun_of_map_mul_eq_mul`

English:
theorem smoothingFun_of_map_mul_eq_mul
  statement: (hμ1 : μ 1 <= 1) {x : R} (hx : forall y : R, μ (x * y) = μ x * μ y)
  proof: by
  have hlim : Tendsto (fun n => μ x * smoothingSeminormSeq μ y n) atTop
      (𝓝 (smoothingFun μ x * smoothingFun μ y)) := by
    rw [smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx]
    exact Tendsto.const_mul _ (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y)
  apply tendsto_nhds_unique_of_eventu

中文:
定理 smoothingFun_of_map_mul_eq_mul
  结论: (hμ1 : μ 1 <= 1) {x : R} (hx : 对任意 y : R, μ (x * y) = μ x * μ y)
  证明: by
  have hlim : Tendsto (fun n => μ x * smoothingSeminormSeq μ y n) atTop
      (𝓝 (smoothingFun μ x * smoothingFun μ y)) := by
    rw [smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx]
    exact Tendsto.const_mul _ (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y)
  apply tendsto_nhds_unique_of_eventu

Depends on / 依赖: EventuallyEq, Nat.cast_ne_zero.mpr, Tendsto, Tendsto.const_mul, _root_, _root_.ne_of_gt, cast_ne_zero, const_mul, eventually_atTop, lt_of_lt_of_le, ne_of_gt, smoothingFun, smoothingFun_apply_of_map_mul_eq_mul, smoothingSeminormSeq, tendsto_nhds_unique_of_eventuallyEq, tendsto_smoothingFun_of_map_one_le_one, zero_l
-/
theorem smoothingFun_of_map_mul_eq_mul (hμ1 : μ 1 <= 1) {x : R} (hx : forall y : R, μ (x * y) = μ x * μ y)
    (y : R) : smoothingFun μ (x * y) = smoothingFun μ x * smoothingFun μ y := by
  have hlim : Tendsto (fun n => μ x * smoothingSeminormSeq μ y n) atTop
      (𝓝 (smoothingFun μ x * smoothingFun μ y)) := by
    rw [smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx]
    exact Tendsto.const_mul _ (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y)
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x * y))
    hlim
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn1
  have hn0 : (n : Real) != 0 := Nat.cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_lt_of_le zero_lt_one hn1))
  simp only [smoothingSeminormSeq]
  rw [mul_pow]; rw [pow_mul_apply_eq_pow_mul μ hx]; rw [mul_rpow (pow_nonneg (apply_nonneg μ _) _)
    (apply_nonneg μ _)]; rw [← rpow_natCast]; rw [← rpow_mul (apply_nonneg μ _)]; rw [mul_one_div_cancel hn0]; rw [rpow_one]

/--
theorem `smoothingSeminorm_of_mul` / 定理 `smoothingSeminorm_of_mul`

English:
theorem smoothingSeminorm_of_mul
  statement: (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) {x : R}
  proof: smoothingFun_of_map_mul_eq_mul μ hμ1 hx y

中文:
定理 smoothingSeminorm_of_mul
  结论: (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) {x : R}
  证明: smoothingFun_of_map_mul_eq_mul μ hμ1 hx y

Depends on / 依赖: smoothingFun_of_map_mul_eq_mul
-/
theorem smoothingSeminorm_of_mul (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) {x : R}
    (hx : forall y : R, μ (x * y) = μ x * μ y) (y : R) :
    smoothingSeminorm μ hμ1 hna (x * y) =
      smoothingSeminorm μ hμ1 hna x * smoothingSeminorm μ hμ1 hna y :=
  smoothingFun_of_map_mul_eq_mul μ hμ1 hx y

end smoothingSeminorm
