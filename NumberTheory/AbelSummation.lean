/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Order.IsLocallyClosed

/-!
# Abel's summation formula

We prove several versions of Abel's summation formula.

## Results

* `sum_mul_eq_sub_sub_integral_mul`: general statement of the formula for a sum between two
  (nonnegative) reals `a` and `b`.

* `sum_mul_eq_sub_integral_mul`: a specialized version of `sum_mul_eq_sub_sub_integral_mul` for
  the case `a = 0`.

* `sum_mul_eq_sub_integral_mul₀`: a specialized version of `sum_mul_eq_sub_integral_mul` for
  when the first coefficient of the sequence is `0`. This is useful for `ArithmeticFunction`.

Primed versions of the three results above are also stated for when the endpoints are `Nat`.

* `tendsto_sum_mul_atTop_nhds_one_sub_integral`: limit version of `sum_mul_eq_sub_integral_mul`
  when `a` tends to `∞`.

* `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`: limit version of `sum_mul_eq_sub_integral_mul₀`
  when `a` tends to `∞`.

* `summable_mul_of_bigO_atTop`: let `c : ℕ → 𝕜` and `f : ℝ → 𝕜` with `𝕜 = ℝ` or `ℂ`, prove the
  summability of `n ↦ (c n) * (f n)` using Abel's formula under some `bigO` assumptions at infinity.

## References

* <https://en.wikipedia.org/wiki/Abel%27s_summation_formula>

-/

public section

noncomputable section

open Finset MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] (c : Nat -> 𝕜) {f : Real -> 𝕜} {a b : Real}

namespace abelSummationProof

open intervalIntegral IntervalIntegrable

/--
theorem `sumlocc` / 定理 `sumlocc`

English:
theorem sumlocc
  given: {m : Nat} (n : Nat)
  proof: by
  filter_upwards [Ico_ae_eq_Icc] with t h ht
  rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]

中文:
定理 sumlocc
  条件: {m : 自然数} (n : 自然数)
  证明: by
  filter_upwards [Ico_ae_eq_Icc] with t h ht
  rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]
-/
private theorem sumlocc {m : Nat} (n : Nat) :
    forallᵐ t, t in Set.Icc (n : Real) (n + 1) -> ∑ k in Icc m ⌊t⌋₊, c k = ∑ k in Icc m n, c k := by
  filter_upwards [Ico_ae_eq_Icc] with t h ht
  rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]

open scoped Interval in
/--
theorem `integralmulsum` / 定理 `integralmulsum`

English:
theorem integralmulsum
  statement: (hf_diff : forall t in Set.Icc a b, DifferentiableAt Real f t)
  proof: by
  have h_inc₁ : Ι t₁ t₂ subseteq Set.Icc n (n + 1) :=
Set.uIoc_of_le h ▸ Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Icc h₁ h₂
  have h_inc₂ : Set.uIcc t₁ t₂ subseteq Set.Icc a b := Set.uIcc_of_le h ▸ Set.Icc_subset_Icc h₃ h₄
  rw [← integral_deriv_eq_sub (fun t ht => hf_diff t (h_inc₂ ht))]; rw

中文:
定理 integralmulsum
  结论: (hf_diff : 对任意 t in 集合.闭区间 a b, DifferentiableAt 实数 f t)
  证明: by
  have h_inc₁ : Ι t₁ t₂ subseteq Set.Icc n (n + 1) :=
Set.uIoc_of_le h ▸ Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Icc h₁ h₂
  have h_inc₂ : Set.uIcc t₁ t₂ subseteq Set.Icc a b := Set.uIcc_of_le h ▸ Set.Icc_subset_Icc h₃ h₄
  rw [← integral_deriv_eq_sub (fun t ht => hf_diff t (h_inc₂ ht))]; rw
-/
private theorem integralmulsum (hf_diff : forall t in Set.Icc a b, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) (t₁ t₂ : Real) (n : Nat) (h : t₁ <= t₂)
    (h₁ : n <= t₁) (h₂ : t₂ <= n + 1) (h₃ : a <= t₁) (h₄ : t₂ <= b) :
    ∫ t in t₁..t₂, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k =
      (f t₂ - f t₁) * ∑ k in Icc 0 n, c k := by
  have h_inc₁ : Ι t₁ t₂ subseteq Set.Icc n (n + 1) :=
Set.uIoc_of_le h ▸ Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Icc h₁ h₂
  have h_inc₂ : Set.uIcc t₁ t₂ subseteq Set.Icc a b := Set.uIcc_of_le h ▸ Set.Icc_subset_Icc h₃ h₄
  rw [← integral_deriv_eq_sub (fun t ht => hf_diff t (h_inc₂ ht))]; rw [← intervalIntegral.integral_mul_const]
  · refine integral_congr_ae ?_
    filter_upwards [sumlocc c n] with t h h'
    rw [h (h_inc₁ h')]
  · refine (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (hf_int.mono_set ?_)
    rwa [← Set.uIcc_of_le h]

/--
theorem `ineqofmemIco` / 定理 `ineqofmemIco`

English:
theorem ineqofmemIco
  given: {k : Nat} (hk : k in Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊)
  proof: by
  constructor
  · have := (Set.mem_Ico.mp hk).1
exact le_of_lt (Nat.floor_lt' (by lia)).mp this
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2

中文:
定理 ineqofmemIco
  条件: {k : 自然数} (hk : k in 集合.左闭右开区间 (⌊a⌋₊ + 1) ⌊b⌋₊)
  证明: by
  constructor
  · have := (Set.mem_Ico.mp hk).1
exact le_of_lt (Nat.floor_lt' (by lia)).mp this
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2
-/
private theorem ineqofmemIco {k : Nat} (hk : k in Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a <= k ∧ k + 1 <= b := by
  constructor
  · have := (Set.mem_Ico.mp hk).1
exact le_of_lt (Nat.floor_lt' (by lia)).mp this
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2

/--
theorem `ineqofmemIco'` / 定理 `ineqofmemIco'`

English:
theorem ineqofmemIco'
  given: {k : Nat} (hk : k in Ico (⌊a⌋₊ + 1) ⌊b⌋₊)
  proof: ineqofmemIco (by rwa [← Finset.coe_Ico])

中文:
定理 ineqofmemIco'
  条件: {k : 自然数} (hk : k in 左闭右开区间 (⌊a⌋₊ + 1) ⌊b⌋₊)
  证明: ineqofmemIco (by rwa [← Finset.coe_Ico])
-/
private theorem ineqofmemIco' {k : Nat} (hk : k in Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a <= k ∧ k + 1 <= b :=
  ineqofmemIco (by rwa [← Finset.coe_Ico])

/--
theorem `_root_.integrableOn_mul_sum_Icc` / 定理 `_root_.integrableOn_mul_sum_Icc`

English:
theorem _root_.integrableOn_mul_sum_Icc
  statement: {m : Nat} (ha : 0 <= a) {g : Real -> 𝕜}
  proof: by
  obtain hab | hab := le_or_gt a b
  · obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
    · have : forallᵐ t, t in Set.Icc a b -> ∑ k in Icc m ⌊a⌋₊, c k = ∑ k in Icc m ⌊t⌋₊, c k := by
        filter_upwards [sumlocc c ⌊a⌋₊] with t ht₁ ht₂
        rw [ht₁ ⟨(Nat.floor_le ha).trans ht₂.1]

中文:
定理 _root_.integrableOn_mul_sum_Icc
  结论: {m : 自然数} (ha : 0 <= a) {g : 实数 -> 𝕜}
  证明: by
  obtain hab | hab := le_or_gt a b
  · obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
    · have : forallᵐ t, t in Set.Icc a b -> ∑ k in Icc m ⌊a⌋₊, c k = ∑ k in Icc m ⌊t⌋₊, c k := by
        filter_upwards [sumlocc c ⌊a⌋₊] with t ht₁ ht₂
        rw [ht₁ ⟨(Nat.floor_le ha).trans ht₂.1]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.refl, IntegrableOn, IntegrableOn.congr_fun_ae, Nat.floor_le, Nat.floor_le_floor, Nat.lt_floor_add_one, Set.Icc, ae_restrict_iff, congr_fun_ae, eq_or_lt_of_le, filter_upwards, floor_le, floor_le_floor, h_locint, hg_int, hg_int.mul_const, le_or_gt, lt_floor_add_one
-/
theorem _root_.integrableOn_mul_sum_Icc {m : Nat} (ha : 0 <= a) {g : Real -> 𝕜}
    (hg_int : IntegrableOn g (Set.Icc a b)) :
    IntegrableOn (fun t => g t * ∑ k in Icc m ⌊t⌋₊, c k) (Set.Icc a b) := by
  obtain hab | hab := le_or_gt a b
  · obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
    · have : forallᵐ t, t in Set.Icc a b -> ∑ k in Icc m ⌊a⌋₊, c k = ∑ k in Icc m ⌊t⌋₊, c k := by
        filter_upwards [sumlocc c ⌊a⌋₊] with t ht₁ ht₂
        rw [ht₁ ⟨(Nat.floor_le ha).trans ht₂.1]; rw [hb ▸ ht₂.2.trans (Nat.lt_floor_add_one b).le⟩]
      rw [← ae_restrict_iff' measurableSet_Icc] at this
      exact IntegrableOn.congr_fun_ae
        (hg_int.mul_const _) ((Filter.EventuallyEq.refl _ g).mul this)
    · have h_locint {t₁ t₂ : Real} {n : Nat} (h : t₁ <= t₂) (h₁ : n <= t₁) (h₂ : t₂ <= n + 1)
          (h₃ : a <= t₁) (h₄ : t₂ <= b) :
          IntervalIntegrable (fun t => g t * ∑ k in Icc m ⌊t⌋₊, c k) volume t₁ t₂ := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le h]
        exact (IntegrableOn.mono_set (hg_int.mul_const _) (Set.Icc_subset_Icc h₃ h₄)).congr
 ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc h₁ h₂)
 (ae_restrict_iff' measurableSet_Icc).mpr
              (by filter_upwards [sumlocc c n] with t h ht using by rw [h ht])
      have aux1 : 0 <= b := (Nat.pos_of_floor_pos <| (Nat.zero_le _).trans_lt hb).le
      have aux2 : ⌊a⌋₊ + 1 <= b := by rwa [← Nat.cast_add_one, ← Nat.le_floor_iff aux1]
      have aux3 : a <= ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
      have aux4 : a <= ⌊b⌋₊ := le_of_lt (by rwa [← Nat.floor_lt ha])
      -- now break up into 3 subintervals
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (aux3.trans aux2)]
      have I1 : IntervalIntegrable _ volume a ↑(⌊a⌋₊ + 1) :=
        h_locint (mod_cast aux3) (Nat.floor_le ha) (mod_cast le_rfl) le_rfl (mod_cast aux2)
      have I2 : IntervalIntegrable _ volume ↑(⌊a⌋₊ + 1) ⌊b⌋₊ :=
        trans_iterate_Ico hb fun k hk => h_locint (mod_cast k.le_succ)
          le_rfl (mod_cast le_rfl) (ineqofmemIco hk).1 (mod_cast (ineqofmemIco hk).2)
      have I3 : IntervalIntegrable _ volume ⌊b⌋₊ b :=
        h_locint (Nat.floor_le aux1) le_rfl (Nat.lt_floor_add_one _).le aux4 le_rfl
      exact (I1.trans I2).trans I3
  · rw [Set.Icc_eq_empty_of_lt hab]
    exact integrableOn_empty

/--
theorem `_root_.sum_mul_eq_sub_sub_integral_mul` / 定理 `_root_.sum_mul_eq_sub_sub_integral_mul`

English:
theorem _root_.sum_mul_eq_sub_sub_integral_mul
  statement: (ha : 0 <= a) (hab : a <= b)
  proof: by
  rw [← integral_of_le hab]
  have aux1 : ⌊a⌋₊ <= a := Nat.floor_le ha
  have aux2 : b <= ⌊b⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  -- We consider two cases depending on whether the sum is empty or not
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Ioc_eq_empty_of_le le_r

中文:
定理 _root_.sum_mul_eq_sub_sub_integral_mul
  结论: (ha : 0 <= a) (hab : a <= b)
  证明: by
  rw [← integral_of_le hab]
  have aux1 : ⌊a⌋₊ <= a := Nat.floor_le ha
  have aux2 : b <= ⌊b⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  -- We consider two cases depending on whether the sum is empty or not
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Ioc_eq_empty_of_le le_r

Depends on / 依赖: Nat.floor_le, Nat.lt_floor_add_one, floor_le, integral_of_le, lt_floor_add_one
-/
theorem _root_.sum_mul_eq_sub_sub_integral_mul (ha : 0 <= a) (hab : a <= b)
    (hf_diff : forall t in Set.Icc a b, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ k in Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k =
      f b * (∑ k in Icc 0 ⌊b⌋₊, c k) - f a * (∑ k in Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k := by
  rw [← integral_of_le hab]
  have aux1 : ⌊a⌋₊ <= a := Nat.floor_le ha
  have aux2 : b <= ⌊b⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  -- We consider two cases depending on whether the sum is empty or not
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Ioc_eq_empty_of_le le_rfl, sum_empty, ← sub_mul,
      integralmulsum c hf_diff hf_int _ _ ⌊b⌋₊ hab (hb ▸ aux1) aux2 le_rfl le_rfl, sub_self]
  have aux3 : a <= ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  have aux4 : ⌊a⌋₊ + 1 <= b := by rwa [← Nat.cast_add_one, ← Nat.le_floor_iff (ha.trans hab)]
  have aux5 : ⌊b⌋₊ <= b := Nat.floor_le (ha.trans hab)
.le .mp hb have aux6 : a <= ⌊b⌋₊ := Nat.floor_lt ha
  simp_rw [← smul_eq_mul, sum_Ioc_by_parts (fun k => f k) _ hb, range_eq_Ico,
    Ico_add_one_right_eq_Icc, smul_eq_mul]
  have : ∑ k in Ioc ⌊a⌋₊ (⌊b⌋₊ - 1), (f ↑(k + 1) - f k) * ∑ n in Icc 0 k, c n =
        ∑ k in Ico (⌊a⌋₊ + 1) ⌊b⌋₊, ∫ t in k..↑(k + 1), deriv f t * ∑ n in Icc 0 ⌊t⌋₊, c n := by
    rw [← Ico_add_one_add_one_eq_Ioc]; rw [Nat.sub_add_cancel (by lia)]; rw [Eq.comm]
    exact sum_congr rfl fun k hk => (integralmulsum c hf_diff hf_int _ _ _ (mod_cast k.le_succ)
le_rfl (mod_cast le_rfl) (ineqofmemIco' hk).1 mod_cast (ineqofmemIco' hk).2)
  rw [this]; rw [sum_integral_adjacent_intervals_Ico hb]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [← integral_interval_sub_left (a := a) (c := ⌊a⌋₊ + 1)]; rw [← integral_add_adjacent_intervals (b := ⌊b⌋₊) (c := b)]; rw [integralmulsum c hf_diff hf_int _ _ _ aux3 aux1 le_rfl le_rfl aux4]; rw [integralmulsum c hf_diff hf_int _ _ _ aux5 le_rfl aux2 aux6 le_rfl]
  · ring
  -- now deal with the integrability side goals
  -- (Note we have 5 goals, but the 1st and 3rd are identical. TODO: find a non-hacky way of dealing
  -- with both at once.)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux5]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_left aux6)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux3]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux4)
  · exact fun k hk => (intervalIntegrable_iff_integrableOn_Icc_of_le (mod_cast k.le_succ)).mpr
 (integrableOn_mul_sum_Icc c ha hf_int).mono_set
 (Set.Icc_subset_Icc_iff (mod_cast k.le_succ)).mpr mod_cast (ineqofmemIco hk)

/--
theorem `_root_.sum_mul_eq_sub_sub_integral_mul'` / 定理 `_root_.sum_mul_eq_sub_sub_integral_mul'`

English:
theorem _root_.sum_mul_eq_sub_sub_integral_mul'
  statement: {n m : Nat} (h : n <= m)
  proof: by
  convert! sum_mul_eq_sub_sub_integral_mul c n.cast_nonneg (Nat.cast_le.mpr h) hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

中文:
定理 _root_.sum_mul_eq_sub_sub_integral_mul'
  结论: {n m : 自然数} (h : n <= m)
  证明: by
  convert! sum_mul_eq_sub_sub_integral_mul c n.cast_nonneg (Nat.cast_le.mpr h) hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

Depends on / 依赖: Nat.cast_le.mpr, Nat.floor_natCast, all_goals, cast_le, cast_nonneg, convert, floor_natCast, hf_diff, hf_int, n.cast_nonneg, sum_mul_eq_sub_sub_integral_mul
-/
theorem _root_.sum_mul_eq_sub_sub_integral_mul' {n m : Nat} (h : n <= m)
    (hf_diff : forall t in Set.Icc (n : Real) m, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (n : Real) m)) :
    ∑ k in Ioc n m, f k * c k =
      f m * (∑ k in Icc 0 m, c k) - f n * (∑ k in Icc 0 n, c k) -
        ∫ t in Set.Ioc (n : Real) m, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k := by
  convert! sum_mul_eq_sub_sub_integral_mul c n.cast_nonneg (Nat.cast_le.mpr h) hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

end abelSummationProof

section specialversions

/--
theorem `sum_mul_eq_sub_integral_mul` / 定理 `sum_mul_eq_sub_integral_mul`

English:
theorem sum_mul_eq_sub_integral_mul
  statement: {b : Real} (hb : 0 <= b)
  proof: by
  nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _)]
  rw [sum_cons]; rw [← Nat.floor_zero (R := Real)]; rw [sum_mul_eq_sub_sub_integral_mul c le_rfl hb hf_diff
    hf_int]; rw [Nat.floor_zero]; rw [Nat.cast_zero]; rw [Icc_self]; rw [sum_singleton]
  ring

中文:
定理 sum_mul_eq_sub_integral_mul
  结论: {b : 实数} (hb : 0 <= b)
  证明: by
  nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _)]
  rw [sum_cons]; rw [← Nat.floor_zero (R := Real)]; rw [sum_mul_eq_sub_sub_integral_mul c le_rfl hb hf_diff
    hf_int]; rw [Nat.floor_zero]; rw [Nat.cast_zero]; rw [Icc_self]; rw [sum_singleton]
  ring

Depends on / 依赖: Icc_eq_cons_Ioc, Icc_self, Nat.cast_zero, Nat.floor_zero, Nat.zero_le, cast_zero, floor_zero, hf_diff, hf_int, le_rfl, nth_rewrite, sum_cons, sum_mul_eq_sub_sub_integral_mul, sum_singleton, zero_le
-/
theorem sum_mul_eq_sub_integral_mul {b : Real} (hb : 0 <= b)
    (hf_diff : forall t in Set.Icc 0 b, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 0 b)) :
    ∑ k in Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k in Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 0 b, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k := by
  nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _)]
  rw [sum_cons]; rw [← Nat.floor_zero (R := Real)]; rw [sum_mul_eq_sub_sub_integral_mul c le_rfl hb hf_diff
    hf_int]; rw [Nat.floor_zero]; rw [Nat.cast_zero]; rw [Icc_self]; rw [sum_singleton]
  ring

/--
theorem `sum_mul_eq_sub_integral_mul'` / 定理 `sum_mul_eq_sub_integral_mul'`

English:
theorem sum_mul_eq_sub_integral_mul'
  statement: (m : Nat)
  proof: by
  convert! sum_mul_eq_sub_integral_mul c m.cast_nonneg hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

中文:
定理 sum_mul_eq_sub_integral_mul'
  结论: (m : 自然数)
  证明: by
  convert! sum_mul_eq_sub_integral_mul c m.cast_nonneg hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

Depends on / 依赖: Nat.floor_natCast, all_goals, cast_nonneg, convert, floor_natCast, hf_diff, hf_int, m.cast_nonneg, sum_mul_eq_sub_integral_mul
-/
theorem sum_mul_eq_sub_integral_mul' (m : Nat)
    (hf_diff : forall t in Set.Icc (0 : Real) m, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (0 : Real) m)) :
    ∑ k in Icc 0 m, f k * c k =
      f m * (∑ k in Icc 0 m, c k) -
        ∫ t in Set.Ioc (0 : Real) m, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k := by
  convert! sum_mul_eq_sub_integral_mul c m.cast_nonneg hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

/--
theorem `sum_mul_eq_sub_integral_mul₀` / 定理 `sum_mul_eq_sub_integral_mul₀`

English:
theorem sum_mul_eq_sub_integral_mul₀
  statement: (hc : c 0 = 0) (b : Real)
  proof: by
  obtain hb | hb := le_or_gt 1 b
  · have : 1 <= ⌊b⌋₊ := (Nat.one_le_floor_iff _).mpr hb
    nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, ← Icc_add_one_left_eq_Ioc,
      Icc_eq_cons_Ioc (by lia), sum_cons]
    rw [zero_add]; rw [← Nat.floor_one (R := Real)]; rw [sum_mul_eq_sub_sub_i

中文:
定理 sum_mul_eq_sub_integral_mul₀
  结论: (hc : c 0 = 0) (b : 实数)
  证明: by
  obtain hb | hb := le_or_gt 1 b
  · have : 1 <= ⌊b⌋₊ := (Nat.one_le_floor_iff _).mpr hb
    nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, ← Icc_add_one_left_eq_Ioc,
      Icc_eq_cons_Ioc (by lia), sum_cons]
    rw [zero_add]; rw [← Nat.floor_one (R := Real)]; rw [sum_mul_eq_sub_sub_i

Depends on / 依赖: Icc_add_one_left_eq_Ioc, Icc_eq_cons_Ioc, Ioc_succ_singleton, Nat.Ioc_succ_singleton, Nat.cast_one, Nat.floor_one, Nat.one_le_floor_iff, Nat.zero_le, cast_one, floor_one, hf_diff, hf_int, le_or_gt, nth_rewrite, one_le_floor_iff, sum_cons, sum_mul_eq_sub_sub_integral_mul, sum_sing, zero_add, zero_le
-/
theorem sum_mul_eq_sub_integral_mul₀ (hc : c 0 = 0) (b : Real)
    (hf_diff : forall t in Set.Icc 1 b, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 1 b)) :
    ∑ k in Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k in Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 1 b, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k := by
  obtain hb | hb := le_or_gt 1 b
  · have : 1 <= ⌊b⌋₊ := (Nat.one_le_floor_iff _).mpr hb
    nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, ← Icc_add_one_left_eq_Ioc,
      Icc_eq_cons_Ioc (by lia), sum_cons]
    rw [zero_add]; rw [← Nat.floor_one (R := Real)]; rw [sum_mul_eq_sub_sub_integral_mul c zero_le_one hb hf_diff hf_int]; rw [Nat.floor_one]; rw [Nat.cast_one]; rw [Icc_eq_cons_Ioc zero_le_one]; rw [sum_cons]; rw [show 1 = 0 + 1 by rfl]; rw [Nat.Ioc_succ_singleton]; rw [zero_add]; rw [sum_singleton]; rw [hc]; rw [mul_zero]; rw [zero_add]
    ring
  · simp_rw [Nat.floor_eq_zero.mpr hb, Icc_self, sum_singleton, Nat.cast_zero, hc, mul_zero,
      Set.Ioc_eq_empty_of_le hb.le, Measure.restrict_empty, integral_zero_measure, sub_self]

/--
theorem `sum_mul_eq_sub_integral_mul₀'` / 定理 `sum_mul_eq_sub_integral_mul₀'`

English:
theorem sum_mul_eq_sub_integral_mul₀'
  statement: (hc : c 0 = 0) (m : Nat)
  proof: by
  convert! sum_mul_eq_sub_integral_mul₀ c hc m hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

中文:
定理 sum_mul_eq_sub_integral_mul₀'
  结论: (hc : c 0 = 0) (m : 自然数)
  证明: by
  convert! sum_mul_eq_sub_integral_mul₀ c hc m hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

Depends on / 依赖: Nat.floor_natCast, all_goals, convert, floor_natCast, hf_diff, hf_int
-/
theorem sum_mul_eq_sub_integral_mul₀' (hc : c 0 = 0) (m : Nat)
    (hf_diff : forall t in Set.Icc (1 : Real) m, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (1 : Real) m)) :
    ∑ k in Icc 0 m, f k * c k =
      f m * (∑ k in Icc 0 m, c k) -
        ∫ t in Set.Ioc (1 : Real) m, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k := by
  convert! sum_mul_eq_sub_integral_mul₀ c hc m hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

/--
theorem `sum_mul_eq_sub_integral_mul₁` / 定理 `sum_mul_eq_sub_integral_mul₁`

English:
theorem sum_mul_eq_sub_integral_mul₁
  statement: (hc : c 0 = 0) (hc1 : c 1 = 0) (b : Real)
  proof: by
  by_cases! hb : b < 2
  · -- Easy case, everything is 0
    have H₁ : forall n in Icc 0 ⌊b⌋₊, c n = 0 := by grind [(Nat.floor_lt' two_ne_zero).mpr hb]
    have H₂ : forall n in Icc 0 ⌊b⌋₊, f n * c n = 0 := by grind
    simp [sum_eq_zero H₁, sum_eq_zero H₂, Set.Ioc_eq_empty_of_le hb.le]
  -- Spli

中文:
定理 sum_mul_eq_sub_integral_mul₁
  结论: (hc : c 0 = 0) (hc1 : c 1 = 0) (b : 实数)
  证明: by
  by_cases! hb : b < 2
  · -- Easy case, everything is 0
    have H₁ : forall n in Icc 0 ⌊b⌋₊, c n = 0 := by grind [(Nat.floor_lt' two_ne_zero).mpr hb]
    have H₂ : forall n in Icc 0 ⌊b⌋₊, f n * c n = 0 := by grind
    simp [sum_eq_zero H₁, sum_eq_zero H₂, Set.Ioc_eq_empty_of_le hb.le]
  -- Spli

Depends on / 依赖: Ioc_eq_empty_of_le, Nat.floor_lt, Set.Ioc_eq_empty_of_le, everything, floor_lt, hb.le, sum_eq_zero, two_ne_zero
-/
theorem sum_mul_eq_sub_integral_mul₁ (hc : c 0 = 0) (hc1 : c 1 = 0) (b : Real)
    (hf_diff : forall t in Set.Icc 2 b, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 2 b)) :
    ∑ k in Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k in Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 2 b, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k := by
  by_cases! hb : b < 2
  · -- Easy case, everything is 0
    have H₁ : forall n in Icc 0 ⌊b⌋₊, c n = 0 := by grind [(Nat.floor_lt' two_ne_zero).mpr hb]
    have H₂ : forall n in Icc 0 ⌊b⌋₊, f n * c n = 0 := by grind
    simp [sum_eq_zero H₁, sum_eq_zero H₂, Set.Ioc_eq_empty_of_le hb.le]
  -- Split off the first two terms of the sum
  have : 2 <= ⌊b⌋₊ := Nat.le_floor hb
  have H : ∑ k in Icc 0 ⌊b⌋₊, f ↑k * c k = f (2 :) * c 2 + ∑ k in Ioc 2 ⌊b⌋₊, f ↑k * c k := by
    rw [add_sum_Ioc_eq_sum_Icc (f := fun (k : Nat) => f k * c k) this]; rw [show Icc 0 ⌊b⌋₊ = {0]; rw [1} union Icc 2 ⌊b⌋₊ by grind]
    exact sum_union_eq_right fun k hk hk' => by grind
  rw [H]
  -- Apply Abel summation to the remainder
  nth_rewrite 3 [show 2 = ⌊(2 : Real)⌋₊ by simp]
  rw [sum_mul_eq_sub_sub_integral_mul c zero_le_two hb hf_diff hf_int]
  simp [show Icc 0 2 = {0, 1, 2} by rfl, hc, hc1]
  grind

end specialversions

section limit

open Filter Topology abelSummationProof intervalIntegral

/--
theorem `locallyIntegrableOn_mul_sum_Icc` / 定理 `locallyIntegrableOn_mul_sum_Icc`

English:
theorem locallyIntegrableOn_mul_sum_Icc
  statement: {m : Nat} (ha : 0 <= a) {g : Real -> 𝕜}
  proof: by
  refine (locallyIntegrableOn_iff isLocallyClosed_Ici).mpr fun K hK₁ hK₂ => ?_
  by_cases hK₃ : K.Nonempty
  · have h_inf : a <= sInf K := (hK₁ (hK₂.sInf_mem hK₃))
    refine IntegrableOn.mono_set ?_ (Bornology.IsBounded.subset_Icc_sInf_sSup hK₂.isBounded)
    refine integrableOn_mul_sum_Icc _ (h

中文:
定理 locally整数egrableOn_mul_sum_Icc
  结论: {m : 自然数} (ha : 0 <= a) {g : 实数 -> 𝕜}
  证明: by
  refine (locallyIntegrableOn_iff isLocallyClosed_Ici).mpr fun K hK₁ hK₂ => ?_
  by_cases hK₃ : K.Nonempty
  · have h_inf : a <= sInf K := (hK₁ (hK₂.sInf_mem hK₃))
    refine IntegrableOn.mono_set ?_ (Bornology.IsBounded.subset_Icc_sInf_sSup hK₂.isBounded)
    refine integrableOn_mul_sum_Icc _ (h

Depends on / 依赖: Bornology, Bornology.IsBounded.subset_Icc_sInf_sSup, Icc_subset_Ici_iff, IntegrableOn, IntegrableOn.mono_set, IsBounded, K.Nonempty, Nonempty, Real.sInf_le_sSup, Set.Icc_subset_Ici_iff, Set.not_nonempty_iff_eq_empty.mp, bddAbove, bddBelow, h_inf, ha.trans, hg.integrableOn_compact_subset, integrableOn_compact_subset, integrableOn_mul_sum_Icc, isBounded, isCompact_Icc
-/
theorem locallyIntegrableOn_mul_sum_Icc {m : Nat} (ha : 0 <= a) {g : Real -> 𝕜}
    (hg : LocallyIntegrableOn g (Set.Ici a)) :
    LocallyIntegrableOn (fun t => g t * ∑ k in Icc m ⌊t⌋₊, c k) (Set.Ici a) := by
  refine (locallyIntegrableOn_iff isLocallyClosed_Ici).mpr fun K hK₁ hK₂ => ?_
  by_cases hK₃ : K.Nonempty
  · have h_inf : a <= sInf K := (hK₁ (hK₂.sInf_mem hK₃))
    refine IntegrableOn.mono_set ?_ (Bornology.IsBounded.subset_Icc_sInf_sSup hK₂.isBounded)
    refine integrableOn_mul_sum_Icc _ (ha.trans h_inf) ?_
    refine hg.integrableOn_compact_subset ?_ isCompact_Icc
    exact (Set.Icc_subset_Ici_iff (Real.sInf_le_sSup _ hK₂.bddBelow hK₂.bddAbove)).mpr h_inf
  · rw [Set.not_nonempty_iff_eq_empty.mp hK₃]
    exact integrableOn_empty

/--
theorem `tendsto_sum_mul_atTop_nhds_one_sub_integral` / 定理 `tendsto_sum_mul_atTop_nhds_one_sub_integral`

English:
theorem tendsto_sum_mul_atTop_nhds_one_sub_integral
  proof: by
  have h_lim' : Tendsto (fun n : Nat => ∫ t in Set.Ioc (0 : Real) n, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)
      atTop (𝓝 (∫ t in Set.Ioi 0, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)) := by
    refine Tendsto.congr (fun _ => by rw [← integral_of_le (Nat.cast_nonneg _)]) ?_
    refine intervalIntegral_ten

中文:
定理 tendsto_sum_mul_atTop_nhds_one_sub_integral
  证明: by
  have h_lim' : Tendsto (fun n : Nat => ∫ t in Set.Ioc (0 : Real) n, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)
      atTop (𝓝 (∫ t in Set.Ioi 0, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)) := by
    refine Tendsto.congr (fun _ => by rw [← integral_of_le (Nat.cast_nonneg _)]) ?_
    refine intervalIntegral_ten

Depends on / 依赖: Iff.mp, Nat.cast_nonneg, Set.Ioc, Set.Ioi, Tendsto, Tendsto.congr, cast_nonneg, h_lim, h_lim.sub, hf_int, hg_dom, hg_int, integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_of_isBigO_atTop, integral_of_le, intervalIntegral_tendsto_integral_Ioi, le_rfl, locallyIntegrableOn_mul_sum_Icc, tendsto_natCast_atTop_atTop
-/
theorem tendsto_sum_mul_atTop_nhds_one_sub_integral
    (hf_diff : forall t in Set.Ici 0, DifferentiableAt Real f t)
    (hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 0)) {l : 𝕜}
    (h_lim : Tendsto (fun n : Nat => f n * ∑ k in Icc 0 n, c k) atTop (𝓝 l))
    {g : Real -> 𝕜} (hg_dom : (fun t => deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k) =O[atTop] g)
    (hg_int : IntegrableAtFilter g atTop) :
    Tendsto (fun n : Nat => ∑ k in Icc 0 n, f k * c k) atTop
      (𝓝 (l - ∫ t in Set.Ioi 0, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)) := by
  have h_lim' : Tendsto (fun n : Nat => ∫ t in Set.Ioc (0 : Real) n, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)
      atTop (𝓝 (∫ t in Set.Ioi 0, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)) := by
    refine Tendsto.congr (fun _ => by rw [← integral_of_le (Nat.cast_nonneg _)]) ?_
    refine intervalIntegral_tendsto_integral_Ioi _ ?_ tendsto_natCast_atTop_atTop
    exact Iff.mp integrableOn_Ici_iff_integrableOn_Ioi
 (locallyIntegrableOn_mul_sum_Icc c le_rfl hf_int).integrableOn_of_isBigO_atTop
        hg_dom hg_int
  refine (h_lim.sub h_lim').congr (fun _ => ?_)
  rw [sum_mul_eq_sub_integral_mul' _ _ (fun t ht => hf_diff _ ht.1)]
  exact hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc

/--
theorem `tendsto_sum_mul_atTop_nhds_one_sub_integral₀` / 定理 `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`

English:
theorem tendsto_sum_mul_atTop_nhds_one_sub_integral₀
  statement: (hc : c 0 = 0)
  proof: by
  have h : (fun n : Nat => ∫ (x : Real) in (1 : Real)..n, deriv f x * ∑ k in Icc 0 ⌊x⌋₊, c k) =ᶠ[atTop]
      (fun n : Nat => ∫ (t : Real) in Set.Ioc 1 ↑n, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k) := by
    filter_upwards [eventually_ge_atTop 1] with _ h
    rw [← integral_of_le (Nat.one_le_cast.mpr h

中文:
定理 tendsto_sum_mul_atTop_nhds_one_sub_integral₀
  结论: (hc : c 0 = 0)
  证明: by
  have h : (fun n : Nat => ∫ (x : Real) in (1 : Real)..n, deriv f x * ∑ k in Icc 0 ⌊x⌋₊, c k) =ᶠ[atTop]
      (fun n : Nat => ∫ (t : Real) in Set.Ioc 1 ↑n, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k) := by
    filter_upwards [eventually_ge_atTop 1] with _ h
    rw [← integral_of_le (Nat.one_le_cast.mpr h

Depends on / 依赖: Nat.one_le_cast.mpr, Set.Ioc, Set.Ioi, Tendsto, Tendsto.congr, eventually_ge_atTop, filter_upwards, h_lim, integral_of_le, intervalIntegr, one_le_cast
-/
theorem tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (hc : c 0 = 0)
    (hf_diff : forall t in Set.Ici 1, DifferentiableAt Real f t)
    (hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 1)) {l : 𝕜}
    (h_lim : Tendsto (fun n : Nat => f n * ∑ k in Icc 0 n, c k) atTop (𝓝 l))
    {g : Real -> Real} (hg_dom : (fun t => deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k) =O[atTop] g)
    (hg_int : IntegrableAtFilter g atTop) :
    Tendsto (fun n : Nat => ∑ k in Icc 0 n, f k * c k) atTop
      (𝓝 (l - ∫ t in Set.Ioi 1, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)) := by
  have h : (fun n : Nat => ∫ (x : Real) in (1 : Real)..n, deriv f x * ∑ k in Icc 0 ⌊x⌋₊, c k) =ᶠ[atTop]
      (fun n : Nat => ∫ (t : Real) in Set.Ioc 1 ↑n, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k) := by
    filter_upwards [eventually_ge_atTop 1] with _ h
    rw [← integral_of_le (Nat.one_le_cast.mpr h)]
  have h_lim' : Tendsto (fun n : Nat => ∫ t in Set.Ioc (1 : Real) n, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)
      atTop (𝓝 (∫ t in Set.Ioi 1, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k)) := by
    refine Tendsto.congr' h (intervalIntegral_tendsto_integral_Ioi _ ?_ tendsto_natCast_atTop_atTop)
    exact Iff.mp integrableOn_Ici_iff_integrableOn_Ioi
 (locallyIntegrableOn_mul_sum_Icc c zero_le_one hf_int).integrableOn_of_isBigO_atTop
        hg_dom hg_int
  refine (h_lim.sub h_lim').congr (fun _ => ?_)
  rw [sum_mul_eq_sub_integral_mul₀' _ hc _ (fun t ht => hf_diff _ ht.1)]
  exact hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc

end limit

section summable

open Filter abelSummationProof

/--
theorem `summable_mul_of_bigO_atTop_aux` / 定理 `summable_mul_of_bigO_atTop_aux`

English:
theorem summable_mul_of_bigO_atTop_aux
  statement: (m : Nat)
  proof: by
  obtain ⟨C₁, hC₁⟩ := Asymptotics.isBigO_one_nat_atTop_iff.mp h_bdd
  let C₂ := ∫ t in Set.Ioi (m : Real), ‖deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖‖
  refine summable_of_sum_range_norm_le (c := max (C₁ + C₂) 1) fun n => ?_
  cases n with
  | zero => simp only [range_zero, norm_mul, su

中文:
定理 summable_mul_of_bigO_atTop_aux
  结论: (m : 自然数)
  证明: by
  obtain ⟨C₁, hC₁⟩ := Asymptotics.isBigO_one_nat_atTop_iff.mp h_bdd
  let C₂ := ∫ t in Set.Ioi (m : Real), ‖deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖‖
  refine summable_of_sum_range_norm_le (c := max (C₁ + C₂) 1) fun n => ?_
  cases n with
  | zero => simp only [range_zero, norm_mul, su
-/
private theorem summable_mul_of_bigO_atTop_aux (m : Nat)
    (h_bdd : (fun n : Nat => ‖f n‖ * ∑ k in Icc 0 n, ‖c k‖) =O[atTop] fun _ => (1 : Real))
    (hf_int : LocallyIntegrableOn (deriv (fun t => ‖f t‖)) (Set.Ici (m : Real)))
    (hf : forall n : Nat, ∑ k in Icc 0 n, ‖f k‖ * ‖c k‖ =
      ‖f n‖ * ∑ k in Icc 0 n, ‖c k‖ -
        ∫ (t : Real) in Set.Ioc ↑m ↑n, deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖)
    {g : Real -> Real}
    (hg₁ : (fun t => deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖) =O[atTop] g)
    (hg₂ : IntegrableAtFilter g atTop) :
    Summable (fun n : Nat => f n * c n) := by
  obtain ⟨C₁, hC₁⟩ := Asymptotics.isBigO_one_nat_atTop_iff.mp h_bdd
  let C₂ := ∫ t in Set.Ioi (m : Real), ‖deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖‖
  refine summable_of_sum_range_norm_le (c := max (C₁ + C₂) 1) fun n => ?_
  cases n with
  | zero => simp only [range_zero, norm_mul, sum_empty, le_sup_iff, zero_le_one, or_true]
  | succ n =>
      rw [Nat.range_eq_Icc_zero_sub_one _ n.add_one_ne_zero]; rw [add_tsub_cancel_right]
      calc
        _ = ∑ k in Icc 0 n, ‖f k‖ * ‖c k‖ := by simp_rw [norm_mul]
        _ = ‖f n‖ * ∑ k in Icc 0 n, ‖c k‖ -
              ∫ t in Set.Ioc ↑m ↑n, deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖ := ?_
        _ <= C₁ - ∫ t in Set.Ioc ↑m ↑n, deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖ := ?_
        _ <= C₁ + ∫ t in Set.Ioc ↑m ↑n, ‖deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖‖ := ?_
        _ <= C₁ + C₂ := ?_
        _ <= max (C₁ + C₂) 1 := le_max_left _ _
      · exact hf _
      · refine tsub_le_tsub_right (le_of_eq_of_le (Real.norm_of_nonneg ?_).symm (hC₁ n)) _
        exact mul_nonneg (norm_nonneg _) (sum_nonneg fun _ _ => norm_nonneg _)
      · grw [sub_eq_add_neg, neg_le_abs, abs_integral_le_integral_abs]
        simp
      · unfold C₂
        grw [setIntegral_mono_set ?_ (.of_forall fun _ => norm_nonneg _)
          Set.Ioc_subset_Ioi_self.eventuallyLE]
        rw [← integrableOn_Ici_iff_integrableOn_Ioi]; rw [IntegrableOn]; rw [integrable_norm_iff (by fun_prop)]
        exact (locallyIntegrableOn_mul_sum_Icc _ m.cast_nonneg hf_int).integrableOn_of_isBigO_atTop
          hg₁ hg₂

/--
theorem `summable_mul_of_bigO_atTop` / 定理 `summable_mul_of_bigO_atTop`

English:
theorem summable_mul_of_bigO_atTop
  proof: by
  refine summable_mul_of_bigO_atTop_aux c 0 h_bdd (by rwa [Nat.cast_zero]) (fun n => ?_) hg₁ hg₂
  exact_mod_cast sum_mul_eq_sub_integral_mul' _ _ (fun _ ht => hf_diff _ ht.1)
    (hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)

中文:
定理 summable_mul_of_bigO_atTop
  证明: by
  refine summable_mul_of_bigO_atTop_aux c 0 h_bdd (by rwa [Nat.cast_zero]) (fun n => ?_) hg₁ hg₂
  exact_mod_cast sum_mul_eq_sub_integral_mul' _ _ (fun _ ht => hf_diff _ ht.1)
    (hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)

Depends on / 依赖: Icc_subset_Ici_self, Nat.cast_zero, Set.Icc_subset_Ici_self, cast_zero, h_bdd, hf_diff, hf_int, hf_int.integrableOn_compact_subset, integrableOn_compact_subset, isCompact_Icc, sum_mul_eq_sub_integral_mul, summable_mul_of_bigO_atTop_aux
-/
theorem summable_mul_of_bigO_atTop
    (hf_diff : forall t in Set.Ici 0, DifferentiableAt Real (fun x => ‖f x‖) t)
    (hf_int : LocallyIntegrableOn (deriv (fun t => ‖f t‖)) (Set.Ici 0))
    (h_bdd : (fun n : Nat => ‖f n‖ * ∑ k in Icc 0 n, ‖c k‖) =O[atTop] fun _ => (1 : Real))
    {g : Real -> Real} (hg₁ : (fun t => deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖) =O[atTop] g)
    (hg₂ : IntegrableAtFilter g atTop) :
    Summable (fun n : Nat => f n * c n) := by
  refine summable_mul_of_bigO_atTop_aux c 0 h_bdd (by rwa [Nat.cast_zero]) (fun n => ?_) hg₁ hg₂
  exact_mod_cast sum_mul_eq_sub_integral_mul' _ _ (fun _ ht => hf_diff _ ht.1)
    (hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)

/--
theorem `summable_mul_of_bigO_atTop'` / 定理 `summable_mul_of_bigO_atTop'`

English:
theorem summable_mul_of_bigO_atTop'
  proof: by
  have h : forall n, ∑ k in Icc 1 n, ‖c k‖ = ∑ k in Icc 0 n, ‖(fun n => if n = 0 then 0 else c n) k‖ := by
    intro n
    rw [Icc_eq_cons_Ioc n.zero_le]; rw [sum_cons]; rw [← Icc_add_one_left_eq_Ioc]; rw [zero_add]
    simp_rw [if_pos, norm_zero, zero_add]
    exact Finset.sum_congr rfl fun _ h 

中文:
定理 summable_mul_of_bigO_atTop'
  证明: by
  have h : forall n, ∑ k in Icc 1 n, ‖c k‖ = ∑ k in Icc 0 n, ‖(fun n => if n = 0 then 0 else c n) k‖ := by
    intro n
    rw [Icc_eq_cons_Ioc n.zero_le]; rw [sum_cons]; rw [← Icc_add_one_left_eq_Ioc]; rw [zero_add]
    simp_rw [if_pos, norm_zero, zero_add]
    exact Finset.sum_congr rfl fun _ h 

Depends on / 依赖: Finset, Finset.sum_congr, Icc_add_one_left_eq_Ioc, Icc_eq_cons_Ioc, Nat.cast_one, Summable, Summable.congr_atTop, cast_one, congr_atTop, h_bdd, if_neg, if_pos, mem_Icc, mem_Icc.mp, n.zero_le, norm_zero, simp_rw, sum_congr, sum_cons, summable_mul_of_bigO_atTop_aux
-/
theorem summable_mul_of_bigO_atTop'
    (hf_diff : forall t in Set.Ici 1, DifferentiableAt Real (fun x => ‖f x‖) t)
    (hf_int : LocallyIntegrableOn (deriv (fun t => ‖f t‖)) (Set.Ici 1))
    (h_bdd : (fun n : Nat => ‖f n‖ * ∑ k in Icc 1 n, ‖c k‖) =O[atTop] fun _ => (1 : Real))
    {g : Real -> Real} (hg₁ : (fun t => deriv (fun t => ‖f t‖) t * ∑ k in Icc 1 ⌊t⌋₊, ‖c k‖) =O[atTop] g)
    (hg₂ : IntegrableAtFilter g atTop) :
    Summable (fun n : Nat => f n * c n) := by
  have h : forall n, ∑ k in Icc 1 n, ‖c k‖ = ∑ k in Icc 0 n, ‖(fun n => if n = 0 then 0 else c n) k‖ := by
    intro n
    rw [Icc_eq_cons_Ioc n.zero_le]; rw [sum_cons]; rw [← Icc_add_one_left_eq_Ioc]; rw [zero_add]
    simp_rw [if_pos, norm_zero, zero_add]
    exact Finset.sum_congr rfl fun _ h => by rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne']
  simp_rw [h] at h_bdd hg₁
  refine Summable.congr_atTop (summable_mul_of_bigO_atTop_aux (fun n => if n = 0 then 0 else c n) 1
    h_bdd (by rwa [Nat.cast_one]) (fun n => ?_) hg₁ hg₂) ?_
  · exact_mod_cast sum_mul_eq_sub_integral_mul₀' _ (by simp only [reduceIte, norm_zero]) n
      (fun _ ht => hf_diff _ ht.1)
      (hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)
  · filter_upwards [eventually_ne_atTop 0] with k hk
    simp_rw [if_neg hk]

end summable
