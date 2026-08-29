/-
Copyright (c) 2025 P. Michael Kielstra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: P. Michael Kielstra
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Field

/-!
# The trapezoidal rule

This file contains a definition of integration on `[[a, b]]` via the trapezoidal rule, along with
an error bound in terms of a bound on the second derivative of the integrand.

## Main results
- `trapezoidal_error_le`: the convergence theorem for the trapezoidal rule.

## References
We follow the proof on (Wikipedia)[https://en.wikipedia.org/wiki/Trapezoidal_rule] for the error
bound.
-/

@[expose] public section

open MeasureTheory intervalIntegral Interval Finset HasDerivWithinAt Set

/-- Integration of `f` from `a` to `b` using the trapezoidal rule with `N+1` total evaluations of
`f`. (Note the off-by-one problem here: `N` counts the number of trapezoids, not the number of
evaluations.) -/
@[wikidata Q833293]
/--
Definition of `trapezoidal_integral` / `trapezoidal_integral` 的定义

English:
definition trapezoidal_integral
  signature: (f : Real -> Real) (N : Nat) (a b : Real)
  body: ((b - a) / N) * ((f a + f b) / 2 + ∑ k in range (N - 1), f (a + (k + 1) * (b - a) / N))

中文:
定义 trapezoidal_integral
  签名: (f : 实数 -> 实数) (N : 自然数) (a b : 实数)
  定义体: ((b - a) / N) * ((f a + f b) / 2 + ∑ k in range (N - 1), f (a + (k + 1) * (b - a) / N))
-/
noncomputable def trapezoidal_integral (f : Real -> Real) (N : Nat) (a b : Real) : Real :=
  ((b - a) / N) * ((f a + f b) / 2 + ∑ k in range (N - 1), f (a + (k + 1) * (b - a) / N))

/--
Definition of `trapezoidal_error` / `trapezoidal_error` 的定义

English:
definition trapezoidal_error
  signature: (f : Real -> Real) (N : Nat) (a b : Real)
  body: (trapezoidal_integral f N a b) - (∫ x in a..b, f x)

中文:
定义 trapezoidal_error
  签名: (f : 实数 -> 实数) (N : 自然数) (a b : 实数)
  定义体: (trapezoidal_integral f N a b) - (∫ x in a..b, f x)

Depends on / 依赖: trapezoidal_integral
-/
noncomputable def trapezoidal_error (f : Real -> Real) (N : Nat) (a b : Real) : Real :=
  (trapezoidal_integral f N a b) - (∫ x in a..b, f x)

/--
theorem `trapezoidal_integral_symm` / 定理 `trapezoidal_integral_symm`

English:
theorem trapezoidal_integral_symm
  given: (f : Real -> Real) {N : Nat} (N_nonzero : 0 < N) (a b : Real)
  proof: by
  unfold trapezoidal_integral
  rw [neg_mul_eq_neg_mul]; rw [neg_div']; rw [neg_sub]; rw [add_comm (f b) (f a)]; rw [← sum_range_reflect]
  congr 2
  apply sum_congr rfl
  intro k hk
  norm_cast
  rw [tsub_tsub]; rw [add_comm 1]; rw [Nat.cast_add]; rw [Nat.cast_sub (mem_range.mp hk)]; rw [Nat.cas

中文:
定理 trapezoidal_integral_symm
  条件: (f : 实数 -> 实数) {N : 自然数} (N_nonzero : 0 < N) (a b : 实数)
  证明: by
  unfold trapezoidal_integral
  rw [neg_mul_eq_neg_mul]; rw [neg_div']; rw [neg_sub]; rw [add_comm (f b) (f a)]; rw [← sum_range_reflect]
  congr 2
  apply sum_congr rfl
  intro k hk
  norm_cast
  rw [tsub_tsub]; rw [add_comm 1]; rw [Nat.cast_add]; rw [Nat.cast_sub (mem_range.mp hk)]; rw [Nat.cas

Depends on / 依赖: N_nonzero, Nat.cast_add, Nat.cast_sub, add_comm, cast_add, cast_sub, congr_arg, mem_range, mem_range.mp, neg_div, neg_mul_eq_neg_mul, neg_sub, sum_congr, sum_range_reflect, trapezoidal_integral, tsub_tsub
-/
theorem trapezoidal_integral_symm (f : Real -> Real) {N : Nat} (N_nonzero : 0 < N) (a b : Real) :
    trapezoidal_integral f N a b = -(trapezoidal_integral f N b a) := by
  unfold trapezoidal_integral
  rw [neg_mul_eq_neg_mul]; rw [neg_div']; rw [neg_sub]; rw [add_comm (f b) (f a)]; rw [← sum_range_reflect]
  congr 2
  apply sum_congr rfl
  intro k hk
  norm_cast
  rw [tsub_tsub]; rw [add_comm 1]; rw [Nat.cast_add]; rw [Nat.cast_sub (mem_range.mp hk)]; rw [Nat.cast_sub N_nonzero]
  apply congr_arg
  field

/--
theorem `trapezoidal_error_symm` / 定理 `trapezoidal_error_symm`

English:
theorem trapezoidal_error_symm
  given: (f : Real -> Real) {N : Nat} (N_nonzero : 0 < N) (a b : Real)
  proof: by
  unfold trapezoidal_error
  rw [trapezoidal_integral_symm f N_nonzero a b]; rw [integral_symm]; rw [neg_sub_neg]; rw [neg_sub]

中文:
定理 trapezoidal_error_symm
  条件: (f : 实数 -> 实数) {N : 自然数} (N_nonzero : 0 < N) (a b : 实数)
  证明: by
  unfold trapezoidal_error
  rw [trapezoidal_integral_symm f N_nonzero a b]; rw [integral_symm]; rw [neg_sub_neg]; rw [neg_sub]

Depends on / 依赖: N_nonzero, integral_symm, neg_sub, neg_sub_neg, trapezoidal_error, trapezoidal_integral_symm
-/
theorem trapezoidal_error_symm (f : Real -> Real) {N : Nat} (N_nonzero : 0 < N) (a b : Real) :
    trapezoidal_error f N a b = -trapezoidal_error f N b a := by
  unfold trapezoidal_error
  rw [trapezoidal_integral_symm f N_nonzero a b]; rw [integral_symm]; rw [neg_sub_neg]; rw [neg_sub]

/-- Just like exact integration, the trapezoidal integration from `a` to `a` is zero. -/
@[simp]
/--
theorem `trapezoidal_integral_eq` / 定理 `trapezoidal_integral_eq`

English:
theorem trapezoidal_integral_eq
  given: (f : Real -> Real) (N : Nat) (a : Real)
  statement: trapezoidal_integral f N a a = 0
  proof: by
  simp [trapezoidal_integral]

中文:
定理 trapezoidal_integral_eq
  条件: (f : 实数 -> 实数) (N : 自然数) (a : 实数)
  结论: trapezoidal_integral f N a a = 0
  证明: by
  simp [trapezoidal_integral]

Depends on / 依赖: trapezoidal_integral
-/
theorem trapezoidal_integral_eq (f : Real -> Real) (N : Nat) (a : Real) : trapezoidal_integral f N a a = 0 := by
  simp [trapezoidal_integral]

/-- The error of the trapezoidal integration from `a` to `a` is zero. -/
@[simp]
/--
theorem `trapezoidal_error_eq` / 定理 `trapezoidal_error_eq`

English:
theorem trapezoidal_error_eq
  given: (f : Real -> Real) (N : Nat) (a : Real)
  statement: trapezoidal_error f N a a = 0
  proof: by
  simp [trapezoidal_error]

中文:
定理 trapezoidal_error_eq
  条件: (f : 实数 -> 实数) (N : 自然数) (a : 实数)
  结论: trapezoidal_error f N a a = 0
  证明: by
  simp [trapezoidal_error]

Depends on / 依赖: trapezoidal_error
-/
theorem trapezoidal_error_eq (f : Real -> Real) (N : Nat) (a : Real) : trapezoidal_error f N a a = 0 := by
  simp [trapezoidal_error]

/-- An exact formula for integration with a single trapezoid (the "midpoint rule"). -/
@[simp]
/--
theorem `trapezoidal_integral_one` / 定理 `trapezoidal_integral_one`

English:
theorem trapezoidal_integral_one
  given: (f : Real -> Real) (a b : Real)
  proof: by
  simp [trapezoidal_integral, mul_comm_div]

中文:
定理 trapezoidal_integral_one
  条件: (f : 实数 -> 实数) (a b : 实数)
  证明: by
  simp [trapezoidal_integral, mul_comm_div]

Depends on / 依赖: mul_comm_div, trapezoidal_integral
-/
theorem trapezoidal_integral_one (f : Real -> Real) (a b : Real) :
    trapezoidal_integral f 1 a b = (b - a) / 2 * (f a + f b) := by
  simp [trapezoidal_integral, mul_comm_div]

/--
theorem `sum_trapezoidal_integral_adjacent_intervals` / 定理 `sum_trapezoidal_integral_adjacent_intervals`

English:
theorem sum_trapezoidal_integral_adjacent_intervals
  statement: {f : Real -> Real} {N : Nat} {a h : Real}
  proof: by
  simp_rw [trapezoidal_integral_one, add_sub_add_left_eq_sub, ← sub_mul, trapezoidal_integral,
    add_sub_cancel_left, one_mul, ← mul_sum, ← mul_div, show N * (h / N) = h by field]
  rw [sum_add_distrib]; rw [← Nat.sub_one_add_one_eq_of_pos N_nonzero]; rw [sum_range_succ']; rw [sum_range_succ]; 

中文:
定理 sum_trapezoidal_integral_adjacent_intervals
  结论: {f : 实数 -> 实数} {N : 自然数} {a h : 实数}
  证明: by
  simp_rw [trapezoidal_integral_one, add_sub_add_left_eq_sub, ← sub_mul, trapezoidal_integral,
    add_sub_cancel_left, one_mul, ← mul_sum, ← mul_div, show N * (h / N) = h by field]
  rw [sum_add_distrib]; rw [← Nat.sub_one_add_one_eq_of_pos N_nonzero]; rw [sum_range_succ']; rw [sum_range_succ]; 

Depends on / 依赖: N_nonzero, Nat.cast_add, Nat.cast_one, Nat.cast_sub, Nat.sub_one_add_one_eq_of_pos, add_add_add_comm, add_comm, add_sub_add_left_eq_sub, add_sub_cancel_left, cast_add, cast_one, cast_sub, mul_div, mul_sum, one_mul, ring_nf, simp_rw, sub_mul, sub_one_add_one_eq_of_pos, sum_add_distrib
-/
theorem sum_trapezoidal_integral_adjacent_intervals {f : Real -> Real} {N : Nat} {a h : Real}
    (N_nonzero : 0 < N) : ∑ i in range N, trapezoidal_integral f 1 (a + i * h) (a + (i + 1) * h)
      = trapezoidal_integral f N a (a + N * h) := by
  simp_rw [trapezoidal_integral_one, add_sub_add_left_eq_sub, ← sub_mul, trapezoidal_integral,
    add_sub_cancel_left, one_mul, ← mul_sum, ← mul_div, show N * (h / N) = h by field]
  rw [sum_add_distrib]; rw [← Nat.sub_one_add_one_eq_of_pos N_nonzero]; rw [sum_range_succ']; rw [sum_range_succ]; rw [add_add_add_comm]; rw [← sum_add_distrib]; rw [add_comm]; rw [Nat.sub_one_add_one_eq_of_pos N_nonzero]
  simp_rw [Nat.cast_sub N_nonzero, Nat.cast_add, Nat.cast_one, ← two_mul, ← mul_sum]
  ring_nf

/--
theorem `trapezoidal_integral_ext` / 定理 `trapezoidal_integral_ext`

English:
theorem trapezoidal_integral_ext
  given: {f : Real -> Real} {N : Nat} {a h : Real} (N_nonzero : 0 < N)
  proof: by
  rw [← Nat.cast_add_one]; rw [← sum_trapezoidal_integral_adjacent_intervals N_nonzero]; rw [← sum_trapezoidal_integral_adjacent_intervals (Nat.add_pos_left N_nonzero 1)]; rw [sum_range_succ]; rw [Nat.cast_add_one]

中文:
定理 trapezoidal_integral_ext
  条件: {f : 实数 -> 实数} {N : 自然数} {a h : 实数} (N_nonzero : 0 < N)
  证明: by
  rw [← Nat.cast_add_one]; rw [← sum_trapezoidal_integral_adjacent_intervals N_nonzero]; rw [← sum_trapezoidal_integral_adjacent_intervals (Nat.add_pos_left N_nonzero 1)]; rw [sum_range_succ]; rw [Nat.cast_add_one]

Depends on / 依赖: N_nonzero, Nat.add_pos_left, Nat.cast_add_one, add_pos_left, cast_add_one, sum_range_succ, sum_trapezoidal_integral_adjacent_intervals
-/
theorem trapezoidal_integral_ext {f : Real -> Real} {N : Nat} {a h : Real} (N_nonzero : 0 < N) :
    trapezoidal_integral f N a (a + N * h) + trapezoidal_integral f 1 (a + N * h) (a + (N + 1) * h)
      = trapezoidal_integral f (N + 1) a (a + (N + 1) * h) := by
  rw [← Nat.cast_add_one]; rw [← sum_trapezoidal_integral_adjacent_intervals N_nonzero]; rw [← sum_trapezoidal_integral_adjacent_intervals (Nat.add_pos_left N_nonzero 1)]; rw [sum_range_succ]; rw [Nat.cast_add_one]

/--
theorem `sum_trapezoidal_error_adjacent_intervals` / 定理 `sum_trapezoidal_error_adjacent_intervals`

English:
theorem sum_trapezoidal_error_adjacent_intervals
  statement: {f : Real -> Real} {N : Nat} {a h : Real} (N_nonzero : 0 < N)
  proof: by
  unfold trapezoidal_error
  rw [sum_sub_distrib]; rw [sum_trapezoidal_integral_adjacent_intervals N_nonzero]
  norm_cast
  rw [sum_integral_adjacent_intervals]
  · simp
  · intro k hk
    suffices forall {k : Nat}, k <= N -> a + k * h in [[a, a + N * h]] from
      IntervalIntegrable.mono h_f_in

中文:
定理 sum_trapezoidal_error_adjacent_intervals
  结论: {f : 实数 -> 实数} {N : 自然数} {a h : 实数} (N_nonzero : 0 < N)
  证明: by
  unfold trapezoidal_error
  rw [sum_sub_distrib]; rw [sum_trapezoidal_integral_adjacent_intervals N_nonzero]
  norm_cast
  rw [sum_integral_adjacent_intervals]
  · simp
  · intro k hk
    suffices forall {k : Nat}, k <= N -> a + k * h in [[a, a + N * h]] from
      IntervalIntegrable.mono h_f_in

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.mono, N_nonzero, Nat.cast_le, Set.mem_uIcc, Set.uIcc_subset_uIcc, cast_le, h_f_int, h_neg, h_pos, hk.le, le_rfl, le_total, mem_uIcc, mul_le_mul_of_nonpos_right, sum_integral_adjacent_intervals, sum_sub_distrib, sum_trapezoidal_integral_adjacent_intervals, trapezoidal_error, uIcc_subset_uIcc
-/
theorem sum_trapezoidal_error_adjacent_intervals {f : Real -> Real} {N : Nat} {a h : Real} (N_nonzero : 0 < N)
    (h_f_int : IntervalIntegrable f volume a (a + N * h)) :
    ∑ i in range N, trapezoidal_error f 1 (a + i * h) (a + (i + 1) * h)
      = trapezoidal_error f N a (a + N * h) := by
  unfold trapezoidal_error
  rw [sum_sub_distrib]; rw [sum_trapezoidal_integral_adjacent_intervals N_nonzero]
  norm_cast
  rw [sum_integral_adjacent_intervals]
  · simp
  · intro k hk
    suffices forall {k : Nat}, k <= N -> a + k * h in [[a, a + N * h]] from
      IntervalIntegrable.mono h_f_int (Set.uIcc_subset_uIcc (this hk.le) (this hk)) le_rfl
    rcases le_total h 0 with h_neg | h_pos <;> intro k hk <;> rw [← Nat.cast_le (α := Real)] at hk
    · simpa [Set.mem_uIcc] using .inr
        ⟨mul_le_mul_of_nonpos_right hk h_neg, mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg h_neg⟩
    · exact Set.mem_uIcc_of_le (le_add_of_nonneg_right (by positivity)) (by grw [hk])

/--
lemma `trapezoidal_error_le_of_lt'` / 引理 `trapezoidal_error_le_of_lt'`

English:
lemma trapezoidal_error_le_of_lt'
  statement: {f : Real -> Real} {ζ : Real} {a b : Real} (a_lt_b : a < b)
  proof: by
  rw [mul_div_assoc]; rw [mul_comm]
  let g (t : Real) := trapezoidal_error f 1 a t
  -- Hand-computed expressions for g' and g''.
  let dg (t : Real) := (1 / 2) * (f a + f t) + ((t - a) / 2) * (derivWithin f (Icc a b) t) - f t
  let ddg (t : Real) := ((t - a) / 2) * (iteratedDerivWithin 2 f (Icc

中文:
引理 trapezoidal_error_le_of_lt'
  结论: {f : 实数 -> 实数} {ζ : 实数} {a b : 实数} (a_lt_b : a < b)
  证明: by
  rw [mul_div_assoc]; rw [mul_comm]
  let g (t : Real) := trapezoidal_error f 1 a t
  -- Hand-computed expressions for g' and g''.
  let dg (t : Real) := (1 / 2) * (f a + f t) + ((t - a) / 2) * (derivWithin f (Icc a b) t) - f t
  let ddg (t : Real) := ((t - a) / 2) * (iteratedDerivWithin 2 f (Icc
-/
private lemma trapezoidal_error_le_of_lt' {f : Real -> Real} {ζ : Real} {a b : Real} (a_lt_b : a < b)
    (h_df : DifferentiableOn Real f (Icc a b))
    (h_ddf : DifferentiableOn Real (derivWithin f (Icc a b)) (Icc a b))
    (fpp_bound : forall x, |iteratedDerivWithin 2 f (Icc a b) x| <= ζ) :
    |trapezoidal_error f 1 a b| <= (b - a) ^ 3 * ζ / 12 := by
  rw [mul_div_assoc]; rw [mul_comm]
  let g (t : Real) := trapezoidal_error f 1 a t
  -- Hand-computed expressions for g' and g''.
  let dg (t : Real) := (1 / 2) * (f a + f t) + ((t - a) / 2) * (derivWithin f (Icc a b) t) - f t
  let ddg (t : Real) := ((t - a) / 2) * (iteratedDerivWithin 2 f (Icc a b) t)
  -- Compute g' by applying standard derivative identities.
  have h_dg (y : Real) (hy : y in Icc a b) : HasDerivWithinAt g (dg y) (Icc a b) y := by
    unfold g trapezoidal_error trapezoidal_integral
    simp only [Nat.cast_one, div_one, tsub_self, Finset.range_zero, sum_empty, add_zero]
    simp_rw [← mul_comm_div]
    refine fun_sub (fun_mul (div_const (sub_const _ (hasDerivWithinAt_id _ _)) _)
      (const_add _ (h_df y hy).hasDerivWithinAt)) ?_
    have := Fact.mk hy -- Needed for integral_hasDerivWithinAt_right
    apply integral_hasDerivWithinAt_right
    · exact (h_df.continuousOn.mono (Icc_subset_Icc le_rfl hy.2)).intervalIntegrable_of_Icc hy.1
    · exact h_df.continuousOn.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc y
    · exact h_df.continuousOn.continuousWithinAt hy
  -- Compute g'', once again applying standard derivative identities.
  have h_ddg (y : Real) (hx : y in Icc a b) : HasDerivWithinAt dg (ddg y) (Icc a b) y := by
    -- The eventual expression for g'' has several terms that cancel, which we have to undo here
    -- so that the various HasDerivWithinAt theorems will have everything they need.
    let dfaky := derivWithin f (Icc a b) y
    rw [(by ring : ddg y = (1 / 2) * dfaky + ((1 / 2) * dfaky + ddg y) - dfaky)]
    refine fun_sub (fun_add (const_mul _ (const_add _ (h_df y hx).hasDerivWithinAt))
      (fun_mul (div_const (sub_const _ (hasDerivWithinAt_id _ _)) _) ?_))
      (h_df y hx).hasDerivWithinAt
    rw [iteratedDerivWithin_eq_iterate]
    exact (h_ddf y hx).hasDerivWithinAt
  -- Technically this would work for all x ≥ a, but we only need it for x ∈ Icc a b (and it makes
  -- more pure-mathematical sense that way).
  have bound_ddg (x : Real) (hx : x in Icc a b) : |ddg x| <= (ζ / 2) * ((x - a) ^ 1) := by
    simp_rw [pow_one, ddg, abs_mul, abs_div, abs_two]
    grw [fpp_bound x, abs_of_nonneg (sub_nonneg.mpr hx.1), div_mul_comm]
  have key {φ φ' : Real -> Real} (h : forall x in Icc a b, HasDerivWithinAt φ (φ' x) (Icc a b) x) (h0 : φ a = 0)
      {c : Real} {n : Nat} (h_bound : forall t in Icc a b, |φ' t| <= c * (t - a) ^ n) :
      forall t in Icc a b, |φ t| <= c / (n + 1) * (t - a) ^ (n + 1) := by
    intro t ht
    have hB (x) : HasDerivAt (fun y => c / (n + 1) * (y - a) ^ (n + 1)) (c * (x - a) ^ n) x := by
      convert!
        (hasDerivAt_const x (c / (n + 1))).mul
          (((hasDerivAt_id x).sub (hasDerivAt_const x a)).pow (n + 1)) using 1
      simp [sub_eq_add_neg, field]
    simpa [Real.norm_eq_abs, h0] using image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun x hx => (h x hx).continuousWithinAt)
      (fun x hx => by grind [Icc_mem_nhdsGE_of_mem, mono_of_mem_nhdsWithin])
      (by simp [h0]) hB (fun x hx => h_bound x (Ico_subset_Icc_self hx)) ht
  exact (key h_dg (trapezoidal_error_eq f 1 a) (key h_ddg (by ring) bound_ddg) b
    ⟨a_lt_b.le, le_rfl⟩).trans_eq (by ring_nf)

/--
lemma `trapezoidal_error_le_of_lt` / 引理 `trapezoidal_error_le_of_lt`

English:
lemma trapezoidal_error_le_of_lt
  statement: {f : Real -> Real} {ζ : Real} {a b : Real} (a_lt_b : a < b)
  proof: by
  let h := (b - a) / N
  let ak (k : Nat) := a + k * h
  have h0 : forall k : Nat, ak (k + 1) - ak k = h := by simp [ak, ← sub_mul]
  have hab : 0 < b - a := sub_pos.mpr a_lt_b
  have hpos : 0 < h := by positivity
  have hb : b = a + N * h := by field
  rw [hb]; rw [← sum_trapezoidal_error_adjace

中文:
引理 trapezoidal_error_le_of_lt
  结论: {f : 实数 -> 实数} {ζ : 实数} {a b : 实数} (a_lt_b : a < b)
  证明: by
  let h := (b - a) / N
  let ak (k : Nat) := a + k * h
  have h0 : forall k : Nat, ak (k + 1) - ak k = h := by simp [ak, ← sub_mul]
  have hab : 0 < b - a := sub_pos.mpr a_lt_b
  have hpos : 0 < h := by positivity
  have hb : b = a + N * h := by field
  rw [hb]; rw [← sum_trapezoidal_error_adjace
-/
private lemma trapezoidal_error_le_of_lt {f : Real -> Real} {ζ : Real} {a b : Real} (a_lt_b : a < b)
    (h_df : DifferentiableOn Real f (Icc a b))
    (h_ddf : DifferentiableOn Real (derivWithin f (Icc a b)) (Icc a b))
    (fpp_bound : forall x, |iteratedDerivWithin 2 f (Icc a b) x| <= ζ)
    {N : Nat} (N_nonzero : 0 < N) :
    |trapezoidal_error f N a b| <= (b - a) ^ 3 * ζ / (12 * N ^ 2) := by
  let h := (b - a) / N
  let ak (k : Nat) := a + k * h
  have h0 : forall k : Nat, ak (k + 1) - ak k = h := by simp [ak, ← sub_mul]
  have hab : 0 < b - a := sub_pos.mpr a_lt_b
  have hpos : 0 < h := by positivity
  have hb : b = a + N * h := by field
  rw [hb]; rw [← sum_trapezoidal_error_adjacent_intervals N_nonzero
    (hb ▸ h_df.continuousOn.intervalIntegrable_of_Icc a_lt_b.le)]
  grw [abs_sum_le_sum_abs]
  suffices forall k in range N, |trapezoidal_error f 1 (ak k) (ak (k + 1))| <= (ζ / 12) * h ^ 3 by
    norm_cast
    calc
      _ <= ∑ k in range N, ζ / 12 * h ^ 3 := sum_le_sum this
      _ = N * (ζ / 12 * h ^ 3) := by simp [sum_const]
      _ = _ := by push_cast; field
  intro k hk
  rw [Finset.mem_range] at hk
  have h1 : a <= ak k := by simp only [ak, le_add_iff_nonneg_right]; positivity
  have h2 : ak (k + 1) <= b := by simp only [ak, hb]; grw [Nat.lt_iff_add_one_le.mp hk]
  have h3 : Icc (ak k) (ak (k + 1)) subseteq Icc a b := Icc_subset_Icc h1 h2
  have h4 : ak k < ak (k + 1) := by rwa [← sub_pos, h0]
  have h5 : EqOn (derivWithin f (Icc a b))
      (derivWithin f (Icc (ak k) (ak (k + 1)))) (Icc (ak k) (ak (k + 1))) := by
    intro x hx
    rw [← derivWithin_subset h3 (uniqueDiffOn_Icc h4 x hx) (h_df x (h3 hx))]
  have h6 : EqOn (iteratedDerivWithin 2 f (Icc a b))
    (iteratedDerivWithin 2 f (Icc (ak k) (ak (k + 1)))) (Icc (ak k) (ak (k + 1))) := by
    intro x hx
    simp only [iteratedDerivWithin_succ', iteratedDerivWithin_zero]
    rw [← derivWithin_subset h3 (uniqueDiffOn_Icc h4 x hx) (h_ddf x (h3 hx))]
    exact derivWithin_congr h5 (h5 hx)
  have h7 (x : Real) : |iteratedDerivWithin 2 f (Set.Icc (ak k) (ak (k + 1))) x| <= ζ := by
    by_cases hx : x in Icc (ak k) (ak (k + 1))
    · grw [← h6 hx, fpp_bound]
    · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure
        (by rwa [closure_Icc]), abs_zero]
      exact (abs_nonneg _).trans (fpp_bound 0)
  refine (trapezoidal_error_le_of_lt' (ζ := ζ) h4 (h_df.mono h3) ?_ h7).trans_eq ?_
  · refine h_ddf.congr_mono (fun x hx => ?_) h3
    exact derivWithin_subset h3 (uniqueDiffOn_Icc h4 x hx) (h_df x (h3 hx))
  · rw [h0, mul_div_assoc, mul_comm]

/--
theorem `trapezoidal_error_le` / 定理 `trapezoidal_error_le`

English:
theorem trapezoidal_error_le
  statement: {f : Real -> Real} {a b : Real}
  proof: by
  rcases lt_trichotomy a b with h_lt | h_eq | h_gt
  -- Standard case: a < b
  · rw [uIcc_of_lt h_lt] at *
    rw [abs_of_pos (sub_pos.mpr h_lt)]
    exact trapezoidal_error_le_of_lt h_lt h_df h_ddf fpp_bound N_nonzero
  -- Trivial case: a = b
  · simp [h_eq]
  -- Slightly trickier case: a > b (r

中文:
定理 trapezoidal_error_le
  结论: {f : 实数 -> 实数} {a b : 实数}
  证明: by
  rcases lt_trichotomy a b with h_lt | h_eq | h_gt
  -- Standard case: a < b
  · rw [uIcc_of_lt h_lt] at *
    rw [abs_of_pos (sub_pos.mpr h_lt)]
    exact trapezoidal_error_le_of_lt h_lt h_df h_ddf fpp_bound N_nonzero
  -- Trivial case: a = b
  · simp [h_eq]
  -- Slightly trickier case: a > b (r

Depends on / 依赖: h_eq, h_gt, h_lt, lt_trichotomy
-/
theorem trapezoidal_error_le {f : Real -> Real} {a b : Real}
    (h_df : DifferentiableOn Real f [[a, b]])
    (h_ddf : DifferentiableOn Real (derivWithin f [[a, b]]) [[a, b]]) {ζ : Real}
    (fpp_bound : forall x, |iteratedDerivWithin 2 f [[a, b]] x| <= ζ) {N : Nat} (N_nonzero : 0 < N) :
    |trapezoidal_error f N a b| <= |b - a| ^ 3 * ζ / (12 * N ^ 2) := by
  rcases lt_trichotomy a b with h_lt | h_eq | h_gt
  -- Standard case: a < b
  · rw [uIcc_of_lt h_lt] at *
    rw [abs_of_pos (sub_pos.mpr h_lt)]
    exact trapezoidal_error_le_of_lt h_lt h_df h_ddf fpp_bound N_nonzero
  -- Trivial case: a = b
  · simp [h_eq]
  -- Slightly trickier case: a > b (requires flipping the direction and sign of the true and
  -- approximate integrals)
  · rw [uIcc_of_gt h_gt] at *
    rw [abs_of_neg (sub_neg.mpr h_gt)]; rw [neg_sub]; rw [trapezoidal_error_symm f N_nonzero a b]; rw [abs_neg]
    exact trapezoidal_error_le_of_lt h_gt h_df h_ddf fpp_bound N_nonzero

/--
theorem `trapezoidal_error_le_of_c2` / 定理 `trapezoidal_error_le_of_c2`

English:
theorem trapezoidal_error_le_of_c2
  statement: {f : Real -> Real} {a b : Real} (h_f_c2 : ContDiffOn Real 2 f [[a, b]])
  proof: by
  -- This use of rcases slightly duplicates effort from the proof of trapezoidal_error_le, but doing
  -- it any other way that I can think of would be worse.
  rcases eq_or_ne a b with h_eq | h_ne
  · simp [h_eq]
  -- Once we have a ≠ b, all the necessary assumptions on f follow pretty quickly f

中文:
定理 trapezoidal_error_le_of_c2
  结论: {f : 实数 -> 实数} {a b : 实数} (h_f_c2 : ContDiffOn 实数 2 f [[a, b]])
  证明: by
  -- This use of rcases slightly duplicates effort from the proof of trapezoidal_error_le, but doing
  -- it any other way that I can think of would be worse.
  rcases eq_or_ne a b with h_eq | h_ne
  · simp [h_eq]
  -- Once we have a ≠ b, all the necessary assumptions on f follow pretty quickly f
-/
theorem trapezoidal_error_le_of_c2 {f : Real -> Real} {a b : Real} (h_f_c2 : ContDiffOn Real 2 f [[a, b]])
    {ζ : Real} (fpp_bound : forall x, |iteratedDerivWithin 2 f [[a, b]] x| <= ζ) {N : Nat}
    (N_nonzero : 0 < N) : |trapezoidal_error f N a b| <= |b - a| ^ 3 * ζ / (12 * N ^ 2) := by
  -- This use of rcases slightly duplicates effort from the proof of trapezoidal_error_le, but doing
  -- it any other way that I can think of would be worse.
  rcases eq_or_ne a b with h_eq | h_ne
  · simp [h_eq]
  -- Once we have a ≠ b, all the necessary assumptions on f follow pretty quickly from its being
  -- C^2.
  have h_ddf : DifferentiableOn Real (derivWithin f [[a, b]]) [[a, b]] := by
    rw [← iteratedDerivWithin_one]
    exact h_f_c2.differentiableOn_iteratedDerivWithin (by norm_cast) (uniqueDiffOn_uIcc h_ne)
  exact trapezoidal_error_le (h_f_c2.differentiableOn two_ne_zero) h_ddf fpp_bound N_nonzero
