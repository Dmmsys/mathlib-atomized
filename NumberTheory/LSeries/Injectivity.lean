/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.NumberTheory.LSeries.Linearity

/-!
# A converging L-series determines its coefficients

We show that two functions `f` and `g : ℕ → ℂ` whose L-series agree and both converge somewhere
must agree on all nonzero arguments. See `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`
and `LSeries_injOn`.
-/

public section

open LSeries Complex

-- The following two lemmas need both `LSeries.Linearity` and `LSeries.Convergence`,
-- so cannot live in either of these files.

/--
lemma `LSeries.abscissaOfAbsConv_add_le` / 引理 `LSeries.abscissaOfAbsConv_add_le`

English:
lemma LSeries.abscissaOfAbsConv_add_le
  given: (f g : Nat -> Complex)
  proof: abscissaOfAbsConv_binop_le LSeriesSummable.add f g

中文:
引理 LSeries.abscissaOfAbsConv_add_le
  条件: (f g : 自然数 -> 复形)
  证明: abscissaOfAbsConv_binop_le LSeriesSummable.add f g

Depends on / 依赖: LSeriesSummable, LSeriesSummable.add, abscissaOfAbsConv_binop_le
-/
lemma LSeries.abscissaOfAbsConv_add_le (f g : Nat -> Complex) :
    abscissaOfAbsConv (f + g) <= max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.add f g

/--
lemma `LSeries.abscissaOfAbsConv_sub_le` / 引理 `LSeries.abscissaOfAbsConv_sub_le`

English:
lemma LSeries.abscissaOfAbsConv_sub_le
  given: (f g : Nat -> Complex)
  proof: abscissaOfAbsConv_binop_le LSeriesSummable.sub f g

private

中文:
引理 LSeries.abscissaOfAbsConv_sub_le
  条件: (f g : 自然数 -> 复形)
  证明: abscissaOfAbsConv_binop_le LSeriesSummable.sub f g

private

Depends on / 依赖: LSeriesSummable, LSeriesSummable.sub, abscissaOfAbsConv_binop_le
-/
lemma LSeries.abscissaOfAbsConv_sub_le (f g : Nat -> Complex) :
    abscissaOfAbsConv (f - g) <= max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.sub f g

private
/--
lemma `cpow_mul_div_cpow_eq_div_div_cpow` / 引理 `cpow_mul_div_cpow_eq_div_div_cpow`

English:
lemma cpow_mul_div_cpow_eq_div_div_cpow
  given: (m n : Nat) (z : Complex) (x : Real)
  proof: by
  have Hn : (0 : Real) <= (n + 1 : Real)⁻¹ := by positivity
  rw [← mul_div_assoc]; rw [mul_comm]; rw [div_eq_mul_inv z]; rw [mul_div_assoc]
  congr
  simp_rw [div_eq_mul_inv]
  rw [show (n + 1 : Complex)⁻¹ = (n + 1 : Real)⁻¹ by simp]; rw [show (n + 1 : Complex) = (n + 1 : Real) by norm_cast]; rw [show (m : Complex) = (m : Real) by norm_cast]; rw [mul_cpow_ofReal_nonneg m.cast_nonneg Hn]; rw [mul_inv]; rw [mul_comm]
  congr
  rw [← cpow_neg]; rw [show (-x : Complex) = (-1 : Real) * x by simp]; rw [cpow_mul_ofReal_nonneg Hn]; rw [Real.rpow_neg_one]; rw [inv_inv]

中文:
引理 cpow_mul_div_cpow_eq_div_div_cpow
  条件: (m n : 自然数) (z : 复形) (x : 实数)
  证明: by
  have Hn : (0 : Real) <= (n + 1 : Real)⁻¹ := by positivity
  rw [← mul_div_assoc]; rw [mul_comm]; rw [div_eq_mul_inv z]; rw [mul_div_assoc]
  congr
  simp_rw [div_eq_mul_inv]
  rw [show (n + 1 : Complex)⁻¹ = (n + 1 : Real)⁻¹ by simp]; rw [show (n + 1 : Complex) = (n + 1 : Real) by norm_cast]; rw [show (m : Complex) = (m : Real) by norm_cast]; rw [mul_cpow_ofReal_nonneg m.cast_nonneg Hn]; rw [mul_inv]; rw [mul_comm]
  congr
  rw [← cpow_neg]; rw [show (-x : Complex) = (-1 : Real) * x by simp]; rw [cpow_mul_ofReal_nonneg Hn]; rw [Real.rpow_neg_one]; rw [inv_inv]

Depends on / 依赖: cast_nonneg, cpow_mul, cpow_neg, div_eq_mul_inv, m.cast_nonneg, mul_comm, mul_cpow_ofReal_nonneg, mul_div_assoc, mul_inv, simp_rw
-/
lemma cpow_mul_div_cpow_eq_div_div_cpow (m n : Nat) (z : Complex) (x : Real) :
    (n + 1) ^ (x : Complex) * (z / m ^ (x : Complex)) = z / (m / (n + 1)) ^ (x : Complex) := by
  have Hn : (0 : Real) <= (n + 1 : Real)⁻¹ := by positivity
  rw [← mul_div_assoc]; rw [mul_comm]; rw [div_eq_mul_inv z]; rw [mul_div_assoc]
  congr
  simp_rw [div_eq_mul_inv]
  rw [show (n + 1 : Complex)⁻¹ = (n + 1 : Real)⁻¹ by simp]; rw [show (n + 1 : Complex) = (n + 1 : Real) by norm_cast]; rw [show (m : Complex) = (m : Real) by norm_cast]; rw [mul_cpow_ofReal_nonneg m.cast_nonneg Hn]; rw [mul_inv]; rw [mul_comm]
  congr
  rw [← cpow_neg]; rw [show (-x : Complex) = (-1 : Real) * x by simp]; rw [cpow_mul_ofReal_nonneg Hn]; rw [Real.rpow_neg_one]; rw [inv_inv]

set_option backward.isDefEq.respectTransparency false in
open Filter Real in
/--
lemma `LSeries.tendsto_cpow_mul_atTop` / 引理 `LSeries.tendsto_cpow_mul_atTop`

English:
lemma LSeries.tendsto_cpow_mul_atTop
  statement: {f : Nat -> Complex} {n : Nat} (h : forall m <= n, f m = 0)
  proof: by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to Real using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  -- `F x m` is the `m`th term of `(n+1)^x * LSeries f x`, except that `F x (n+1) = 0`
  let F := fun (x : Real) => {m | n + 1 < m}.indicator (fun m => f m / (m / (n + 1) : Complex) ^ (x : Complex))
  have hF₀ (x : Real) {m : Nat} (hm : m <= n + 1) : F x m = 0 := by simp [F, not_lt_of_ge hm]
  have hF (x : Real) {m : Nat} (hm : m != n + 1) : F x m = ((n + 1) ^ (x : Complex)) * term f x m := by
    rcases lt_trichotomy m (n + 1) with H | rfl | H
    · simp [Nat.not_lt_of_gt H, term, h m <| Nat.lt_succ_iff.mp H, F]
    · exact (hm rfl).elim
    · simp [H, term, (n.zero_lt_succ.trans H).ne', F, cpow_mul_div_cpow_eq_div_div_cpow]
  have hs {x : Real} (hx : x >= y) : Summable fun m => (n + 1) ^ (x : Complex) * term f x m := by
refine (summable_mul_left_iff <| natCast_add_one_cpow_ne_zero n _).mpr
       LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
simpa only [ofReal_re] using hay.trans_le EReal.coe_le_coe_iff.mpr hx
  -- we can write `(n+1)^x * LSeries f x` as `f (n+1)` plus the series over `F x`
  have key : forall x >= y, (n + 1) ^ (x : Complex) * LSeries f x = f (n + 1) + ∑' m : Nat, F x m := by
    intro x hx
    rw [LSeries]; rw [← tsum_mul_left]; rw [(hs hx).tsum_eq_add_tsum_ite (n + 1)]; rw [pow_mul_term_eq f x n]
    congr
    ext1 m
    rcases eq_or_ne m (n + 1) with rfl | hm
    · simp [hF₀ x le_rfl]
    · simp [hm, hF]
  -- reduce to showing that `∑' m, F x m → 0` as `x → ∞`
  conv => enter [3, 1]; rw [← add_zero (f _)]
  refine Tendsto.congr'
(eventuallyEq_of_mem (s := {x | y <= x}) (mem_atTop y) key).symm tendsto_const_nhds.add ?_
  -- get the prerequisites for applying dominated convergence
  have hys : Summable (F y) := by
    refine ((hs le_rfl).indicator {m | n + 1 < m}).congr fun m => ?_
    by_cases! hm : n + 1 < m
    · simp [hF, hm, hm.ne']
    · simp [hm, hF₀ _ hm]
  have hc (k : Nat) : Tendsto (F · k) atTop (nhds 0) := by
    rcases lt_or_ge (n + 1) k with H | H
    · have H₀ : (0 : Real) <= k / (n + 1) := by positivity
      have H₀' : (0 : Real) <= (n + 1) / k := by positivity
      have H₁ : (k / (n + 1) : Complex) = (k / (n + 1) : Real) := by push_cast; rfl
      have H₂ : (n + 1) / k < (1 : Real) :=
(div_lt_one <| mod_cast n.succ_pos.trans H).mpr mod_cast H
      simp only [Set.mem_ofPred_eq, H, Set.indicator_of_mem, F]
      conv =>
        enter [1, x]
        rw [div_eq_mul_inv]; rw [H₁]; rw [← ofReal_cpow H₀]; rw [← ofReal_inv]; rw [← Real.inv_rpow H₀]; rw [inv_div]
      conv => enter [3, 1]; rw [← mul_zero (f k)]
      exact
        (tendsto_rpow_atTop_of_base_lt_one _ (neg_one_lt_zero.trans_le H₀') H₂).ofReal.const_mul _
    · simp [hF₀ _ H]
  rw [show (0 : Complex) = tsum (fun _ : Nat => 0) from tsum_zero.symm]
refine tendsto_tsum_of_dominated_convergence hys.norm hc eventually_iff.mpr ?_
  filter_upwards [mem_atTop y] with y' hy' k
  -- it remains to show that `‖F y' k‖ ≤ ‖F y k‖` (for `y' ≥ y`)
  rcases lt_or_ge (n + 1) k with H | H
  · simp only [Set.mem_ofPred_eq, H, Set.indicator_of_mem, norm_div, norm_cpow_real,
      Complex.norm_natCast, F]
    rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [Complex.norm_natCast]
    have hkn : 1 <= (k / (n + 1 :) : Real) :=
(one_le_div (by positivity)).mpr mod_cast Nat.le_of_succ_le H
    gcongr
  · simp [hF₀ _ H]

中文:
引理 LSeries.tendsto_cpow_mul_atTop
  结论: {f : 自然数 -> 复形} {n : 自然数} (h : 对任意 m <= n, f m = 0)
  证明: by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to Real using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  -- `F x m` is the `m`th term of `(n+1)^x * LSeries f x`, except that `F x (n+1) = 0`
  let F := fun (x : Real) => {m | n + 1 < m}.indicator (fun m => f m / (m / (n + 1) : Complex) ^ (x : Complex))
  have hF₀ (x : Real) {m : Nat} (hm : m <= n + 1) : F x m = 0 := by simp [F, not_lt_of_ge hm]
  have hF (x : Real) {m : Nat} (hm : m != n + 1) : F x m = ((n + 1) ^ (x : Complex)) * term f x m := by
    rcases lt_trichotomy m (n + 1) with H | rfl | H
    · simp [Nat.not_lt_of_gt H, term, h m <| Nat.lt_succ_iff.mp H, F]
    · exact (hm rfl).elim
    · simp [H, term, (n.zero_lt_succ.trans H).ne', F, cpow_mul_div_cpow_eq_div_div_cpow]
  have hs {x : Real} (hx : x >= y) : Summable fun m => (n + 1) ^ (x : Complex) * term f x m := by
refine (summable_mul_left_iff <| natCast_add_one_cpow_ne_zero n _).mpr
       LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
simpa only [ofReal_re] using hay.trans_le EReal.coe_le_coe_iff.mpr hx
  -- we can write `(n+1)^x * LSeries f x` as `f (n+1)` plus the series over `F x`
  have key : forall x >= y, (n + 1) ^ (x : Complex) * LSeries f x = f (n + 1) + ∑' m : Nat, F x m := by
    intro x hx
    rw [LSeries]; rw [← tsum_mul_left]; rw [(hs hx).tsum_eq_add_tsum_ite (n + 1)]; rw [pow_mul_term_eq f x n]
    congr
    ext1 m
    rcases eq_or_ne m (n + 1) with rfl | hm
    · simp [hF₀ x le_rfl]
    · simp [hm, hF]
  -- reduce to showing that `∑' m, F x m → 0` as `x → ∞`
  conv => enter [3, 1]; rw [← add_zero (f _)]
  refine Tendsto.congr'
(eventuallyEq_of_mem (s := {x | y <= x}) (mem_atTop y) key).symm tendsto_const_nhds.add ?_
  -- get the prerequisites for applying dominated convergence
  have hys : Summable (F y) := by
    refine ((hs le_rfl).indicator {m | n + 1 < m}).congr fun m => ?_
    by_cases! hm : n + 1 < m
    · simp [hF, hm, hm.ne']
    · simp [hm, hF₀ _ hm]
  have hc (k : Nat) : Tendsto (F · k) atTop (nhds 0) := by
    rcases lt_or_ge (n + 1) k with H | H
    · have H₀ : (0 : Real) <= k / (n + 1) := by positivity
      have H₀' : (0 : Real) <= (n + 1) / k := by positivity
      have H₁ : (k / (n + 1) : Complex) = (k / (n + 1) : Real) := by push_cast; rfl
      have H₂ : (n + 1) / k < (1 : Real) :=
(div_lt_one <| mod_cast n.succ_pos.trans H).mpr mod_cast H
      simp only [Set.mem_ofPred_eq, H, Set.indicator_of_mem, F]
      conv =>
        enter [1, x]
        rw [div_eq_mul_inv]; rw [H₁]; rw [← ofReal_cpow H₀]; rw [← ofReal_inv]; rw [← Real.inv_rpow H₀]; rw [inv_div]
      conv => enter [3, 1]; rw [← mul_zero (f k)]
      exact
        (tendsto_rpow_atTop_of_base_lt_one _ (neg_one_lt_zero.trans_le H₀') H₂).ofReal.const_mul _
    · simp [hF₀ _ H]
  rw [show (0 : Complex) = tsum (fun _ : Nat => 0) from tsum_zero.symm]
refine tendsto_tsum_of_dominated_convergence hys.norm hc eventually_iff.mpr ?_
  filter_upwards [mem_atTop y] with y' hy' k
  -- it remains to show that `‖F y' k‖ ≤ ‖F y k‖` (for `y' ≥ y`)
  rcases lt_or_ge (n + 1) k with H | H
  · simp only [Set.mem_ofPred_eq, H, Set.indicator_of_mem, norm_div, norm_cpow_real,
      Complex.norm_natCast, F]
    rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [Complex.norm_natCast]
    have hkn : 1 <= (k / (n + 1 :) : Real) :=
(one_le_div (by positivity)).mpr mod_cast Nat.le_of_succ_le H
    gcongr
  · simp [hF₀ _ H]

Depends on / 依赖: OrderBot, OrderBot.bot_le, bot_le, exists_between, hyt.ne, trans_lt
-/
lemma LSeries.tendsto_cpow_mul_atTop {f : Nat -> Complex} {n : Nat} (h : forall m <= n, f m = 0)
    (ha : abscissaOfAbsConv f < ⊤) :
    Tendsto (fun x : Real => (n + 1) ^ (x : Complex) * LSeries f x) atTop (nhds (f (n + 1))) := by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to Real using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  -- `F x m` is the `m`th term of `(n+1)^x * LSeries f x`, except that `F x (n+1) = 0`
  let F := fun (x : Real) => {m | n + 1 < m}.indicator (fun m => f m / (m / (n + 1) : Complex) ^ (x : Complex))
  have hF₀ (x : Real) {m : Nat} (hm : m <= n + 1) : F x m = 0 := by simp [F, not_lt_of_ge hm]
  have hF (x : Real) {m : Nat} (hm : m != n + 1) : F x m = ((n + 1) ^ (x : Complex)) * term f x m := by
    rcases lt_trichotomy m (n + 1) with H | rfl | H
    · simp [Nat.not_lt_of_gt H, term, h m <| Nat.lt_succ_iff.mp H, F]
    · exact (hm rfl).elim
    · simp [H, term, (n.zero_lt_succ.trans H).ne', F, cpow_mul_div_cpow_eq_div_div_cpow]
  have hs {x : Real} (hx : x >= y) : Summable fun m => (n + 1) ^ (x : Complex) * term f x m := by
refine (summable_mul_left_iff <| natCast_add_one_cpow_ne_zero n _).mpr
       LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
simpa only [ofReal_re] using hay.trans_le EReal.coe_le_coe_iff.mpr hx
  -- we can write `(n+1)^x * LSeries f x` as `f (n+1)` plus the series over `F x`
  have key : forall x >= y, (n + 1) ^ (x : Complex) * LSeries f x = f (n + 1) + ∑' m : Nat, F x m := by
    intro x hx
    rw [LSeries]; rw [← tsum_mul_left]; rw [(hs hx).tsum_eq_add_tsum_ite (n + 1)]; rw [pow_mul_term_eq f x n]
    congr
    ext1 m
    rcases eq_or_ne m (n + 1) with rfl | hm
    · simp [hF₀ x le_rfl]
    · simp [hm, hF]
  -- reduce to showing that `∑' m, F x m → 0` as `x → ∞`
  conv => enter [3, 1]; rw [← add_zero (f _)]
  refine Tendsto.congr'
(eventuallyEq_of_mem (s := {x | y <= x}) (mem_atTop y) key).symm tendsto_const_nhds.add ?_
  -- get the prerequisites for applying dominated convergence
  have hys : Summable (F y) := by
    refine ((hs le_rfl).indicator {m | n + 1 < m}).congr fun m => ?_
    by_cases! hm : n + 1 < m
    · simp [hF, hm, hm.ne']
    · simp [hm, hF₀ _ hm]
  have hc (k : Nat) : Tendsto (F · k) atTop (nhds 0) := by
    rcases lt_or_ge (n + 1) k with H | H
    · have H₀ : (0 : Real) <= k / (n + 1) := by positivity
      have H₀' : (0 : Real) <= (n + 1) / k := by positivity
      have H₁ : (k / (n + 1) : Complex) = (k / (n + 1) : Real) := by push_cast; rfl
      have H₂ : (n + 1) / k < (1 : Real) :=
(div_lt_one <| mod_cast n.succ_pos.trans H).mpr mod_cast H
      simp only [Set.mem_ofPred_eq, H, Set.indicator_of_mem, F]
      conv =>
        enter [1, x]
        rw [div_eq_mul_inv]; rw [H₁]; rw [← ofReal_cpow H₀]; rw [← ofReal_inv]; rw [← Real.inv_rpow H₀]; rw [inv_div]
      conv => enter [3, 1]; rw [← mul_zero (f k)]
      exact
        (tendsto_rpow_atTop_of_base_lt_one _ (neg_one_lt_zero.trans_le H₀') H₂).ofReal.const_mul _
    · simp [hF₀ _ H]
  rw [show (0 : Complex) = tsum (fun _ : Nat => 0) from tsum_zero.symm]
refine tendsto_tsum_of_dominated_convergence hys.norm hc eventually_iff.mpr ?_
  filter_upwards [mem_atTop y] with y' hy' k
  -- it remains to show that `‖F y' k‖ ≤ ‖F y k‖` (for `y' ≥ y`)
  rcases lt_or_ge (n + 1) k with H | H
  · simp only [Set.mem_ofPred_eq, H, Set.indicator_of_mem, norm_div, norm_cpow_real,
      Complex.norm_natCast, F]
    rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [Complex.norm_natCast]
    have hkn : 1 <= (k / (n + 1 :) : Real) :=
(one_le_div (by positivity)).mpr mod_cast Nat.le_of_succ_le H
    gcongr
  · simp [hF₀ _ H]

open Filter in
/--
lemma `LSeries.tendsto_atTop` / 引理 `LSeries.tendsto_atTop`

English:
lemma LSeries.tendsto_atTop
  given: {f : Nat -> Complex} (ha : abscissaOfAbsConv f < ⊤)
  proof: by
  let F (n : Nat) : Complex := if n = 0 then 0 else f n
  have hF₀ : F 0 = 0 := rfl
  have hF {n : Nat} (hn : n != 0) : F n = f n := if_neg hn
  have ha' : abscissaOfAbsConv F < ⊤ := (abscissaOfAbsConv_congr hF).symm ▸ ha
  simp_rw [← LSeries_congr hF]
  convert! LSeries.tendsto_cpow_mul_atTop (n := 0) (fun _ hm => Nat.le_zero.mp hm ▸ hF₀) ha' using 1
  simp

中文:
引理 LSeries.tendsto_atTop
  条件: {f : 自然数 -> 复形} (ha : abscissaOfAbsConv f < ⊤)
  证明: by
  let F (n : Nat) : Complex := if n = 0 then 0 else f n
  have hF₀ : F 0 = 0 := rfl
  have hF {n : Nat} (hn : n != 0) : F n = f n := if_neg hn
  have ha' : abscissaOfAbsConv F < ⊤ := (abscissaOfAbsConv_congr hF).symm ▸ ha
  simp_rw [← LSeries_congr hF]
  convert! LSeries.tendsto_cpow_mul_atTop (n := 0) (fun _ hm => Nat.le_zero.mp hm ▸ hF₀) ha' using 1
  simp

Depends on / 依赖: LSeries, LSeries.tendsto_cpow_mul_atTop, LSeries_congr, Nat.le_zero.mp, abscissaOfAbsConv, abscissaOfAbsConv_congr, convert, if_neg, le_zero, simp_rw, tendsto_cpow_mul_atTop
-/
lemma LSeries.tendsto_atTop {f : Nat -> Complex} (ha : abscissaOfAbsConv f < ⊤) :
    Tendsto (fun x : Real => LSeries f x) atTop (nhds (f 1)) := by
  let F (n : Nat) : Complex := if n = 0 then 0 else f n
  have hF₀ : F 0 = 0 := rfl
  have hF {n : Nat} (hn : n != 0) : F n = f n := if_neg hn
  have ha' : abscissaOfAbsConv F < ⊤ := (abscissaOfAbsConv_congr hF).symm ▸ ha
  simp_rw [← LSeries_congr hF]
  convert! LSeries.tendsto_cpow_mul_atTop (n := 0) (fun _ hm => Nat.le_zero.mp hm ▸ hF₀) ha' using 1
  simp

/--
lemma `LSeries_eq_zero_of_abscissaOfAbsConv_eq_top` / 引理 `LSeries_eq_zero_of_abscissaOfAbsConv_eq_top`

English:
lemma LSeries_eq_zero_of_abscissaOfAbsConv_eq_top
  given: {f : Nat -> Complex} (h : abscissaOfAbsConv f = ⊤)
  proof: by
  ext1 s
exact LSeries.eq_zero_of_not_LSeriesSummable f s mt LSeriesSummable.abscissaOfAbsConv_le
    h ▸ fun H => (H.trans_lt <| EReal.coe_lt_top _).false

中文:
引理 LSeries_eq_zero_of_abscissaOfAbsConv_eq_top
  条件: {f : 自然数 -> 复形} (h : abscissaOfAbsConv f = ⊤)
  证明: by
  ext1 s
exact LSeries.eq_zero_of_not_LSeriesSummable f s mt LSeriesSummable.abscissaOfAbsConv_le
    h ▸ fun H => (H.trans_lt <| EReal.coe_lt_top _).false

Depends on / 依赖: EReal.coe_lt_top, H.trans_lt, LSeries, LSeries.eq_zero_of_not_LSeriesSummable, LSeriesSummable, LSeriesSummable.abscissaOfAbsConv_le, abscissaOfAbsConv_le, coe_lt_top, eq_zero_of_not_LSeriesSummable, trans_lt
-/
lemma LSeries_eq_zero_of_abscissaOfAbsConv_eq_top {f : Nat -> Complex} (h : abscissaOfAbsConv f = ⊤) :
    LSeries f = 0 := by
  ext1 s
exact LSeries.eq_zero_of_not_LSeriesSummable f s mt LSeriesSummable.abscissaOfAbsConv_le
    h ▸ fun H => (H.trans_lt <| EReal.coe_lt_top _).false

open Filter Nat in
/--
lemma `LSeries_eventually_eq_zero_iff'` / 引理 `LSeries_eventually_eq_zero_iff'`

English:
lemma LSeries_eventually_eq_zero_iff'
  given: {f : Nat -> Complex}
  proof: by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using!
Eventually.of_forall by simp [LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h]
  · simp only [ne_eq, h, or_false]
    refine ⟨fun H => ?_, fun H => Eventually.of_forall fun x => ?_⟩
    · let F (n : Nat) : Complex := if n = 0 then 0 else f n
      have hF₀ : F 0 = 0 := rfl
      have hF {n : Nat} (hn : n != 0) : F n = f n := if_neg hn
      suffices forall n, F n = 0 from fun n hn => (hF hn).symm.trans (this n)
      have ha : ¬ abscissaOfAbsConv F = ⊤ := abscissaOfAbsConv_congr hF ▸ h
      have h' (x : Real) : LSeries F x = LSeries f x := LSeries_congr hF x
      have H' (n : Nat) : (fun x : Real => n ^ (x : Complex) * LSeries F x) =ᶠ[atTop] fun _ => 0 := by
        simp only [h']
        rw [eventuallyEq_iff_exists_mem] at H ⊢
        obtain ⟨s, hs⟩ := H
        exact ⟨s, hs.1, fun x hx => by simp [hs.2 hx]⟩
      intro n
      induction n using Nat.strongRecOn with | ind n ih =>
      -- it suffices to show that `n ^ x * LSeries F x` tends to `F n` as `x` tends to `∞`
      suffices Tendsto (fun x : Real => n ^ (x : Complex) * LSeries F x) atTop (nhds (F n)) by
replace this := this.congr' H' n
        simp only [tendsto_const_nhds_iff] at this
        exact this.symm
      cases n with
| zero => exact Tendsto.congr' (H' 0).symm by simp [hF₀]
      | succ n =>
simpa using! LSeries.tendsto_cpow_mul_atTop (fun m hm => ih m <| lt_succ_of_le hm)
            Ne.lt_top ha
    · simp [LSeries_congr (fun {n} => H n) x, show (fun _ : Nat => (0 : Complex)) = 0 from rfl]

中文:
引理 LSeries_eventually_eq_zero_iff'
  条件: {f : 自然数 -> 复形}
  证明: by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using!
Eventually.of_forall by simp [LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h]
  · simp only [ne_eq, h, or_false]
    refine ⟨fun H => ?_, fun H => Eventually.of_forall fun x => ?_⟩
    · let F (n : Nat) : Complex := if n = 0 then 0 else f n
      have hF₀ : F 0 = 0 := rfl
      have hF {n : Nat} (hn : n != 0) : F n = f n := if_neg hn
      suffices forall n, F n = 0 from fun n hn => (hF hn).symm.trans (this n)
      have ha : ¬ abscissaOfAbsConv F = ⊤ := abscissaOfAbsConv_congr hF ▸ h
      have h' (x : Real) : LSeries F x = LSeries f x := LSeries_congr hF x
      have H' (n : Nat) : (fun x : Real => n ^ (x : Complex) * LSeries F x) =ᶠ[atTop] fun _ => 0 := by
        simp only [h']
        rw [eventuallyEq_iff_exists_mem] at H ⊢
        obtain ⟨s, hs⟩ := H
        exact ⟨s, hs.1, fun x hx => by simp [hs.2 hx]⟩
      intro n
      induction n using Nat.strongRecOn with | ind n ih =>
      -- it suffices to show that `n ^ x * LSeries F x` tends to `F n` as `x` tends to `∞`
      suffices Tendsto (fun x : Real => n ^ (x : Complex) * LSeries F x) atTop (nhds (F n)) by
replace this := this.congr' H' n
        simp only [tendsto_const_nhds_iff] at this
        exact this.symm
      cases n with
| zero => exact Tendsto.congr' (H' 0).symm by simp [hF₀]
      | succ n =>
simpa using! LSeries.tendsto_cpow_mul_atTop (fun m hm => ih m <| lt_succ_of_le hm)
            Ne.lt_top ha
    · simp [LSeries_congr (fun {n} => H n) x, show (fun _ : Nat => (0 : Complex)) = 0 from rfl]

Depends on / 依赖: Eventually, Eventually.of_forall, LSeries_eq_zero_of_abscissaOfAbsConv_eq_top, abscissaOfAbsConv, if_neg, ne_eq, of_forall, or_false, symm.trans
-/
lemma LSeries_eventually_eq_zero_iff' {f : Nat -> Complex} :
    (fun x : Real => LSeries f x) =ᶠ[atTop] 0 ↔ (forall n != 0, f n = 0) ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using!
Eventually.of_forall by simp [LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h]
  · simp only [ne_eq, h, or_false]
    refine ⟨fun H => ?_, fun H => Eventually.of_forall fun x => ?_⟩
    · let F (n : Nat) : Complex := if n = 0 then 0 else f n
      have hF₀ : F 0 = 0 := rfl
      have hF {n : Nat} (hn : n != 0) : F n = f n := if_neg hn
      suffices forall n, F n = 0 from fun n hn => (hF hn).symm.trans (this n)
      have ha : ¬ abscissaOfAbsConv F = ⊤ := abscissaOfAbsConv_congr hF ▸ h
      have h' (x : Real) : LSeries F x = LSeries f x := LSeries_congr hF x
      have H' (n : Nat) : (fun x : Real => n ^ (x : Complex) * LSeries F x) =ᶠ[atTop] fun _ => 0 := by
        simp only [h']
        rw [eventuallyEq_iff_exists_mem] at H ⊢
        obtain ⟨s, hs⟩ := H
        exact ⟨s, hs.1, fun x hx => by simp [hs.2 hx]⟩
      intro n
      induction n using Nat.strongRecOn with | ind n ih =>
      -- it suffices to show that `n ^ x * LSeries F x` tends to `F n` as `x` tends to `∞`
      suffices Tendsto (fun x : Real => n ^ (x : Complex) * LSeries F x) atTop (nhds (F n)) by
replace this := this.congr' H' n
        simp only [tendsto_const_nhds_iff] at this
        exact this.symm
      cases n with
| zero => exact Tendsto.congr' (H' 0).symm by simp [hF₀]
      | succ n =>
simpa using! LSeries.tendsto_cpow_mul_atTop (fun m hm => ih m <| lt_succ_of_le hm)
            Ne.lt_top ha
    · simp [LSeries_congr (fun {n} => H n) x, show (fun _ : Nat => (0 : Complex)) = 0 from rfl]

open Nat in
/--
lemma `LSeries_eq_zero_iff` / 引理 `LSeries_eq_zero_iff`

English:
lemma LSeries_eq_zero_iff
  given: {f : Nat -> Complex} (hf : f 0 = 0)
  proof: by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using! LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h
  · simp only [h, or_false]
    refine ⟨fun H => ?_, fun H => H ▸ LSeries_zero⟩
    convert! (LSeries_eventually_eq_zero_iff'.mp ?_).resolve_right h
    · refine ⟨fun H' _ _ => by rw [H', Pi.zero_apply], fun H' => ?_⟩
      ext (- | m)
      · simp [hf]
      · simp [H']
    · simpa only [H] using! Filter.EventuallyEq.rfl

中文:
引理 LSeries_eq_zero_iff
  条件: {f : 自然数 -> 复形} (hf : f 0 = 0)
  证明: by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using! LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h
  · simp only [h, or_false]
    refine ⟨fun H => ?_, fun H => H ▸ LSeries_zero⟩
    convert! (LSeries_eventually_eq_zero_iff'.mp ?_).resolve_right h
    · refine ⟨fun H' _ _ => by rw [H', Pi.zero_apply], fun H' => ?_⟩
      ext (- | m)
      · simp [hf]
      · simp [H']
    · simpa only [H] using! Filter.EventuallyEq.rfl

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.rfl, LSeries_eq_zero_of_abscissaOfAbsConv_eq_top, LSeries_eventually_eq_zero_iff, LSeries_zero, Pi.zero_apply, abscissaOfAbsConv, convert, or_false, resolve_right, zero_apply
-/
lemma LSeries_eq_zero_iff {f : Nat -> Complex} (hf : f 0 = 0) :
    LSeries f = 0 ↔ f = 0 ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using! LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h
  · simp only [h, or_false]
    refine ⟨fun H => ?_, fun H => H ▸ LSeries_zero⟩
    convert! (LSeries_eventually_eq_zero_iff'.mp ?_).resolve_right h
    · refine ⟨fun H' _ _ => by rw [H', Pi.zero_apply], fun H' => ?_⟩
      ext (- | m)
      · simp [hf]
      · simp [H']
    · simpa only [H] using! Filter.EventuallyEq.rfl

open Filter in
/--
lemma `LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq` / 引理 `LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq`

English:
lemma LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq
  statement: {f g : Nat -> Complex}
  proof: by
  rw [EventuallyEq]; rw [eventually_atTop] at h ⊢
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨yf, hyf₁, hyf₂⟩ := exists_between hf
  obtain ⟨yg, hyg₁, hyg₂⟩ := exists_between hg
  lift yf to Real using ⟨hyf₂.ne, ((OrderBot.bot_le _).trans_lt hyf₁).ne'⟩
  lift yg to Real using ⟨hyg₂.ne, ((OrderBot.bot_le _).trans_lt hyg₁).ne'⟩
  refine ⟨max x₀ (max yf yg), fun x hx => ?_⟩
  have Hf : LSeriesSummable f x := by
refine LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ hyf₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
exact (le_max_left _ yg).trans (le_max_right x₀ _).trans hx
  have Hg : LSeriesSummable g x := by
refine LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ hyg₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
exact (le_max_right yf _).trans (le_max_right x₀ _).trans hx
  rw [LSeries_sub Hf Hg]; rw [hx₀ x <| (le_max_left ..).trans hx]; rw [sub_self]; rw [Pi.zero_apply]

中文:
引理 LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq
  结论: {f g : 自然数 -> 复形}
  证明: by
  rw [EventuallyEq]; rw [eventually_atTop] at h ⊢
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨yf, hyf₁, hyf₂⟩ := exists_between hf
  obtain ⟨yg, hyg₁, hyg₂⟩ := exists_between hg
  lift yf to Real using ⟨hyf₂.ne, ((OrderBot.bot_le _).trans_lt hyf₁).ne'⟩
  lift yg to Real using ⟨hyg₂.ne, ((OrderBot.bot_le _).trans_lt hyg₁).ne'⟩
  refine ⟨max x₀ (max yf yg), fun x hx => ?_⟩
  have Hf : LSeriesSummable f x := by
refine LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ hyf₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
exact (le_max_left _ yg).trans (le_max_right x₀ _).trans hx
  have Hg : LSeriesSummable g x := by
refine LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ hyg₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
exact (le_max_right yf _).trans (le_max_right x₀ _).trans hx
  rw [LSeries_sub Hf Hg]; rw [hx₀ x <| (le_max_left ..).trans hx]; rw [sub_self]; rw [Pi.zero_apply]

Depends on / 依赖: EReal.coe_le_coe_iff.mpr, EventuallyEq, LSeriesSummable, LSeriesSummable_of_abscissaOfAbsConv_lt_re, OrderBot, OrderBot.bot_le, bot_le, coe_le_coe_iff, eventually_atTop, exists_between, ofReal_re, trans_le, trans_lt
-/
lemma LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq {f g : Nat -> Complex}
    (hf : abscissaOfAbsConv f < ⊤) (hg : abscissaOfAbsConv g < ⊤)
    (h : (fun x : Real => LSeries f x) =ᶠ[atTop] fun x => LSeries g x) :
    (fun x : Real => LSeries (f - g) x) =ᶠ[atTop] (0 : Real -> Complex) := by
  rw [EventuallyEq]; rw [eventually_atTop] at h ⊢
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨yf, hyf₁, hyf₂⟩ := exists_between hf
  obtain ⟨yg, hyg₁, hyg₂⟩ := exists_between hg
  lift yf to Real using ⟨hyf₂.ne, ((OrderBot.bot_le _).trans_lt hyf₁).ne'⟩
  lift yg to Real using ⟨hyg₂.ne, ((OrderBot.bot_le _).trans_lt hyg₁).ne'⟩
  refine ⟨max x₀ (max yf yg), fun x hx => ?_⟩
  have Hf : LSeriesSummable f x := by
refine LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ hyf₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
exact (le_max_left _ yg).trans (le_max_right x₀ _).trans hx
  have Hg : LSeriesSummable g x := by
refine LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ hyg₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
exact (le_max_right yf _).trans (le_max_right x₀ _).trans hx
  rw [LSeries_sub Hf Hg]; rw [hx₀ x <| (le_max_left ..).trans hx]; rw [sub_self]; rw [Pi.zero_apply]

open Filter in
/--
lemma `LSeries.eq_of_LSeries_eventually_eq` / 引理 `LSeries.eq_of_LSeries_eventually_eq`

English:
lemma LSeries.eq_of_LSeries_eventually_eq
  statement: {f g : Nat -> Complex} (hf : abscissaOfAbsConv f < ⊤)
  proof: by
  have hsub : (fun x : Real => LSeries (f - g) x) =ᶠ[atTop] (0 : Real -> Complex) :=
    LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq hf hg h
  have ha : abscissaOfAbsConv (f - g) != ⊤ :=
lt_top_iff_ne_top.mp (abscissaOfAbsConv_sub_le f g).trans_lt max_lt hf hg
  simpa only [Pi.sub_apply, sub_eq_zero]
    using (LSeries_eventually_eq_zero_iff'.mp hsub).resolve_right ha n hn

中文:
引理 LSeries.eq_of_LSeries_eventually_eq
  结论: {f g : 自然数 -> 复形} (hf : abscissaOfAbsConv f < ⊤)
  证明: by
  have hsub : (fun x : Real => LSeries (f - g) x) =ᶠ[atTop] (0 : Real -> Complex) :=
    LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq hf hg h
  have ha : abscissaOfAbsConv (f - g) != ⊤ :=
lt_top_iff_ne_top.mp (abscissaOfAbsConv_sub_le f g).trans_lt max_lt hf hg
  simpa only [Pi.sub_apply, sub_eq_zero]
    using (LSeries_eventually_eq_zero_iff'.mp hsub).resolve_right ha n hn

Depends on / 依赖: LSeries, LSeries_eventually_eq_zero_iff, LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq, Pi.sub_apply, abscissaOfAbsConv, abscissaOfAbsConv_sub_le, lt_top_iff_ne_top, lt_top_iff_ne_top.mp, max_lt, resolve_right, sub_apply, sub_eq_zero, trans_lt
-/
lemma LSeries.eq_of_LSeries_eventually_eq {f g : Nat -> Complex} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) (h : (fun x : Real => LSeries f x) =ᶠ[atTop] fun x => LSeries g x)
    {n : Nat} (hn : n != 0) :
    f n = g n := by
  have hsub : (fun x : Real => LSeries (f - g) x) =ᶠ[atTop] (0 : Real -> Complex) :=
    LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq hf hg h
  have ha : abscissaOfAbsConv (f - g) != ⊤ :=
lt_top_iff_ne_top.mp (abscissaOfAbsConv_sub_le f g).trans_lt max_lt hf hg
  simpa only [Pi.sub_apply, sub_eq_zero]
    using (LSeries_eventually_eq_zero_iff'.mp hsub).resolve_right ha n hn

/--
lemma `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top` / 引理 `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`

English:
lemma LSeries_eq_iff_of_abscissaOfAbsConv_lt_top
  statement: {f g : Nat -> Complex} (hf : abscissaOfAbsConv f < ⊤)
  proof: by
  refine ⟨fun H n hn => ?_, fun H => funext (LSeries_congr fun {n} => H n)⟩
  refine eq_of_LSeries_eventually_eq hf hg ?_ hn
  exact Filter.Eventually.of_forall fun x => congr_fun H x

中文:
引理 LSeries_eq_iff_of_abscissaOfAbsConv_lt_top
  结论: {f g : 自然数 -> 复形} (hf : abscissaOfAbsConv f < ⊤)
  证明: by
  refine ⟨fun H n hn => ?_, fun H => funext (LSeries_congr fun {n} => H n)⟩
  refine eq_of_LSeries_eventually_eq hf hg ?_ hn
  exact Filter.Eventually.of_forall fun x => congr_fun H x

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, LSeries_congr, congr_fun, eq_of_LSeries_eventually_eq, of_forall
-/
lemma LSeries_eq_iff_of_abscissaOfAbsConv_lt_top {f g : Nat -> Complex} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) :
    LSeries f = LSeries g ↔ forall n != 0, f n = g n := by
  refine ⟨fun H n hn => ?_, fun H => funext (LSeries_congr fun {n} => H n)⟩
  refine eq_of_LSeries_eventually_eq hf hg ?_ hn
  exact Filter.Eventually.of_forall fun x => congr_fun H x

/--
lemma `LSeries_injOn` / 引理 `LSeries_injOn`

English:
lemma LSeries_injOn
  statement: Set.InjOn LSeries {f | f 0 = 0 ∧ abscissaOfAbsConv f < ⊤}
  proof: by
  intro f hf g hg h
  push _ in _ at hf hg
  replace h := (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top hf.2 hg.2).mp h
  ext1 n
  cases n with
  | zero => exact hf.1.trans hg.1.symm
  | succ n => exact h _ n.zero_ne_add_one.symm

中文:
引理 LSeries_injOn
  结论: 集合.单射限制 LSeries {f | f 0 = 0 ∧ abscissaOfAbsConv f < ⊤}
  证明: by
  intro f hf g hg h
  push _ in _ at hf hg
  replace h := (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top hf.2 hg.2).mp h
  ext1 n
  cases n with
  | zero => exact hf.1.trans hg.1.symm
  | succ n => exact h _ n.zero_ne_add_one.symm

Depends on / 依赖: LSeries_eq_iff_of_abscissaOfAbsConv_lt_top, n.zero_ne_add_one.symm, replace, zero_ne_add_one
-/
lemma LSeries_injOn : Set.InjOn LSeries {f | f 0 = 0 ∧ abscissaOfAbsConv f < ⊤} := by
  intro f hf g hg h
  push _ in _ at hf hg
  replace h := (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top hf.2 hg.2).mp h
  ext1 n
  cases n with
  | zero => exact hf.1.trans hg.1.symm
  | succ n => exact h _ n.zero_ne_add_one.symm
