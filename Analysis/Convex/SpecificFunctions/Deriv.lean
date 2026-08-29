/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Convex.Deriv

/-!
# Collection of convex functions

In this file we prove that certain specific functions are strictly convex, including the following:

* `Even.strictConvexOn_pow` : For an even `n : ℕ` with `2 ≤ n`, `fun x => x ^ n` is strictly convex.
* `strictConvexOn_pow` : For `n : ℕ`, with `2 ≤ n`, `fun x => x ^ n` is strictly convex on $[0,+∞)$.
* `strictConvexOn_zpow` : For `m : ℤ` with `m ≠ 0, 1`, `fun x => x ^ m` is strictly convex on
  $[0, +∞)$.
* `strictConcaveOn_sin_Icc` : `sin` is strictly concave on $[0, π]$
* `strictConcaveOn_cos_Icc` : `cos` is strictly concave on $[-π/2, π/2]$

## TODO

These convexity lemmas are proved by checking the sign of the second derivative. If desired, most
of these could also be switched to elementary proofs, like in
`Analysis.Convex.SpecificFunctions.Basic`.

-/

public section


open Real Set

open scoped NNReal

/--
theorem `strictConvexOn_pow` / 定理 `strictConvexOn_pow`

English:
theorem strictConvexOn_pow
  given: {n : Nat} (hn : 2 <= n)
  statement: StrictConvexOn Real (Ici 0) fun x : Real => x ^ n
  proof: by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici _) (continuousOn_pow _)
  eta_expand
  simp_rw [deriv_pow_field, interior_Ici]
  exact fun x (hx : 0 < x) y _ hxy => mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ hxy hx.le <| Nat.sub_ne_zero_of_lt hn) (by positivity)

中文:
定理 strictConvexOn_pow
  条件: {n : 自然数} (hn : 2 <= n)
  结论: StrictConvexOn 实数 (左闭右无界区间 0) fun x : 实数 => x ^ n
  证明: by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici _) (continuousOn_pow _)
  eta_expand
  simp_rw [deriv_pow_field, interior_Ici]
  exact fun x (hx : 0 < x) y _ hxy => mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ hxy hx.le <| Nat.sub_ne_zero_of_lt hn) (by positivity)

Depends on / 依赖: Nat.sub_ne_zero_of_lt, StrictMonoOn, StrictMonoOn.strictConvexOn_of_deriv, continuousOn_pow, convex_Ici, deriv_pow_field, eta_expand, hx.le, interior_Ici, mul_lt_mul_of_pos_left, simp_rw, strictConvexOn_of_deriv, sub_ne_zero_of_lt
-/
theorem strictConvexOn_pow {n : Nat} (hn : 2 <= n) : StrictConvexOn Real (Ici 0) fun x : Real => x ^ n := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici _) (continuousOn_pow _)
  eta_expand
  simp_rw [deriv_pow_field, interior_Ici]
  exact fun x (hx : 0 < x) y _ hxy => mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ hxy hx.le <| Nat.sub_ne_zero_of_lt hn) (by positivity)

/--
theorem `Even.strictConvexOn_pow` / 定理 `Even.strictConvexOn_pow`

English:
theorem Even.strictConvexOn_pow
  given: {n : Nat} (hn : Even n) (h : n != 0)
  proof: by
  apply StrictMono.strictConvexOn_univ_of_deriv (continuous_pow n)
  eta_expand
  simp_rw [deriv_pow_field]
  replace h := Nat.pos_of_ne_zero h
  exact StrictMono.const_mul (Odd.strictMono_pow <| Nat.Even.sub_odd h hn <| Nat.odd_iff.2 rfl)
    (Nat.cast_pos.2 h)

中文:
定理 Even.strictConvexOn_pow
  条件: {n : 自然数} (hn : Even n) (h : n != 0)
  证明: by
  apply StrictMono.strictConvexOn_univ_of_deriv (continuous_pow n)
  eta_expand
  simp_rw [deriv_pow_field]
  replace h := Nat.pos_of_ne_zero h
  exact StrictMono.const_mul (Odd.strictMono_pow <| Nat.Even.sub_odd h hn <| Nat.odd_iff.2 rfl)
    (Nat.cast_pos.2 h)

Depends on / 依赖: Nat.Even.sub_odd, Nat.cast_pos, Nat.odd_iff, Nat.pos_of_ne_zero, Odd.strictMono_pow, StrictMono, StrictMono.const_mul, StrictMono.strictConvexOn_univ_of_deriv, cast_pos, const_mul, continuous_pow, deriv_pow_field, eta_expand, odd_iff, pos_of_ne_zero, replace, simp_rw, strictConvexOn_univ_of_deriv, strictMono_pow, sub_odd
-/
theorem Even.strictConvexOn_pow {n : Nat} (hn : Even n) (h : n != 0) :
    StrictConvexOn Real Set.univ fun x : Real => x ^ n := by
  apply StrictMono.strictConvexOn_univ_of_deriv (continuous_pow n)
  eta_expand
  simp_rw [deriv_pow_field]
  replace h := Nat.pos_of_ne_zero h
  exact StrictMono.const_mul (Odd.strictMono_pow <| Nat.Even.sub_odd h hn <| Nat.odd_iff.2 rfl)
    (Nat.cast_pos.2 h)

/--
theorem `Finset.prod_nonneg_of_card_nonpos_even` / 定理 `Finset.prod_nonneg_of_card_nonpos_even`

English:
theorem Finset.prod_nonneg_of_card_nonpos_even
  statement: {α β : Type*}
  proof: calc
    0 <= ∏ x in s, (if f x <= 0 then (-1 : β) else 1) * f x :=
      Finset.prod_nonneg fun x _ => by
        split_ifs with hx
        · simp [hx]
        linarith
    _ = _ := by
      rw [Finset.prod_mul_distrib]; rw [Finset.prod_ite]; rw [Finset.prod_const_one]; rw [mul_one]; rw [Finset.prod_const]; rw [neg_one_pow_eq_pow_mod_two]; rw [Nat.even_iff.1 h0]; rw [pow_zero]; rw [one_mul]

中文:
定理 有限集.prod_nonneg_of_card_nonpos_even
  结论: {α β : 类型}
  证明: calc
    0 <= ∏ x in s, (if f x <= 0 then (-1 : β) else 1) * f x :=
      Finset.prod_nonneg fun x _ => by
        split_ifs with hx
        · simp [hx]
        linarith
    _ = _ := by
      rw [Finset.prod_mul_distrib]; rw [Finset.prod_ite]; rw [Finset.prod_const_one]; rw [mul_one]; rw [Finset.prod_const]; rw [neg_one_pow_eq_pow_mod_two]; rw [Nat.even_iff.1 h0]; rw [pow_zero]; rw [one_mul]

Depends on / 依赖: Finset, Finset.prod_const, Finset.prod_const_one, Finset.prod_ite, Finset.prod_mul_distrib, Finset.prod_nonneg, Nat.even_iff, even_iff, mul_one, neg_one_pow_eq_pow_mod_two, one_mul, pow_zero, prod_const, prod_const_one, prod_ite, prod_mul_distrib, prod_nonneg, split_ifs
-/
theorem Finset.prod_nonneg_of_card_nonpos_even {α β : Type*}
    [CommRing β] [LinearOrder β] [IsStrictOrderedRing β] {f : α -> β}
    [DecidablePred fun x => f x <= 0] {s : Finset α} (h0 : Even (s.filter fun x => f x <= 0).card) :
    0 <= ∏ x in s, f x :=
  calc
    0 <= ∏ x in s, (if f x <= 0 then (-1 : β) else 1) * f x :=
      Finset.prod_nonneg fun x _ => by
        split_ifs with hx
        · simp [hx]
        linarith
    _ = _ := by
      rw [Finset.prod_mul_distrib]; rw [Finset.prod_ite]; rw [Finset.prod_const_one]; rw [mul_one]; rw [Finset.prod_const]; rw [neg_one_pow_eq_pow_mod_two]; rw [Nat.even_iff.1 h0]; rw [pow_zero]; rw [one_mul]

/--
theorem `int_prod_range_nonneg` / 定理 `int_prod_range_nonneg`

English:
theorem int_prod_range_nonneg
  given: (m : Int) (n : Nat) (hn : Even n)
  proof: by
  rcases hn with ⟨n, rfl⟩
  induction n with
  | zero => simp
  | succ n ihn =>
    rw [← two_mul] at ihn
    rw [← two_mul]; rw [mul_add]; rw [mul_one]; rw [← one_add_one_eq_two]; rw [← add_assoc]; rw [Finset.prod_range_succ]; rw [Finset.prod_range_succ]; rw [mul_assoc]
    refine mul_nonneg ihn ?_; generalize (1 + 1) * n = k
    rcases le_or_gt m k with hmk | hmk
    · have : m <= k + 1 := hmk.trans (lt_add_one (k : Int)).le
      convert! mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) _
      convert! sub_nonpos_of_le this
    · exact mul_nonneg (sub_nonneg_of_le hmk.le) (sub_nonneg_of_le hmk)

中文:
定理 int_prod_range_nonneg
  条件: (m : 整数) (n : 自然数) (hn : Even n)
  证明: by
  rcases hn with ⟨n, rfl⟩
  induction n with
  | zero => simp
  | succ n ihn =>
    rw [← two_mul] at ihn
    rw [← two_mul]; rw [mul_add]; rw [mul_one]; rw [← one_add_one_eq_two]; rw [← add_assoc]; rw [Finset.prod_range_succ]; rw [Finset.prod_range_succ]; rw [mul_assoc]
    refine mul_nonneg ihn ?_; generalize (1 + 1) * n = k
    rcases le_or_gt m k with hmk | hmk
    · have : m <= k + 1 := hmk.trans (lt_add_one (k : Int)).le
      convert! mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) _
      convert! sub_nonpos_of_le this
    · exact mul_nonneg (sub_nonneg_of_le hmk.le) (sub_nonneg_of_le hmk)

Depends on / 依赖: Finset, Finset.prod_range_succ, add_assoc, convert, generalize, hmk.trans, le_or_gt, lt_add_one, mul_add, mul_assoc, mul_nonneg, mul_nonneg_of_nonpos_of_nonpos, mul_one, one_add_one_eq_two, prod_range_succ, sub_nonpos_of_le, two_mul
-/
theorem int_prod_range_nonneg (m : Int) (n : Nat) (hn : Even n) :
    0 <= ∏ k in Finset.range n, (m - k) := by
  rcases hn with ⟨n, rfl⟩
  induction n with
  | zero => simp
  | succ n ihn =>
    rw [← two_mul] at ihn
    rw [← two_mul]; rw [mul_add]; rw [mul_one]; rw [← one_add_one_eq_two]; rw [← add_assoc]; rw [Finset.prod_range_succ]; rw [Finset.prod_range_succ]; rw [mul_assoc]
    refine mul_nonneg ihn ?_; generalize (1 + 1) * n = k
    rcases le_or_gt m k with hmk | hmk
    · have : m <= k + 1 := hmk.trans (lt_add_one (k : Int)).le
      convert! mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) _
      convert! sub_nonpos_of_le this
    · exact mul_nonneg (sub_nonneg_of_le hmk.le) (sub_nonneg_of_le hmk)

/--
theorem `int_prod_range_pos` / 定理 `int_prod_range_pos`

English:
theorem int_prod_range_pos
  given: {m : Int} {n : Nat} (hn : Even n) (hm : m ∉ Ico (0 : Int) n)
  proof: by
  refine (int_prod_range_nonneg m n hn).lt_of_ne fun h => hm ?_
  rw [eq_comm]; rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [sub_eq_zero.1 h]
exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.2 Finset.mem_range.1 ha⟩

中文:
定理 int_prod_range_pos
  条件: {m : 整数} {n : 自然数} (hn : Even n) (hm : m ∉ 左闭右开区间 (0 : 整数) n)
  证明: by
  refine (int_prod_range_nonneg m n hn).lt_of_ne fun h => hm ?_
  rw [eq_comm]; rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [sub_eq_zero.1 h]
exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.2 Finset.mem_range.1 ha⟩

Depends on / 依赖: Finset, Finset.mem_range, Finset.prod_eq_zero_iff, Int.natCast_nonneg, Int.ofNat_lt, eq_comm, int_prod_range_nonneg, lt_of_ne, mem_range, natCast_nonneg, ofNat_lt, prod_eq_zero_iff, sub_eq_zero
-/
theorem int_prod_range_pos {m : Int} {n : Nat} (hn : Even n) (hm : m ∉ Ico (0 : Int) n) :
    0 < ∏ k in Finset.range n, (m - k) := by
  refine (int_prod_range_nonneg m n hn).lt_of_ne fun h => hm ?_
  rw [eq_comm]; rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [sub_eq_zero.1 h]
exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.2 Finset.mem_range.1 ha⟩

/--
theorem `strictConvexOn_zpow` / 定理 `strictConvexOn_zpow`

English:
theorem strictConvexOn_zpow
  given: {m : Int} (hm₀ : m != 0) (hm₁ : m != 1)
  proof: by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · exact (continuousOn_zpow₀ m).mono fun x hx => ne_of_gt hx
  intro x hx
  rw [mem_Ioi] at hx
  rw [iter_deriv_zpow]
  refine mul_pos ?_ (zpow_pos hx _)
  norm_cast
  refine int_prod_range_pos (by decide) fun hm => ?_
  rw [← Finset.coe_Ico] at hm
  norm_cast at hm
  fin_cases hm <;> simp_all

中文:
定理 strictConvexOn_zpow
  条件: {m : 整数} (hm₀ : m != 0) (hm₁ : m != 1)
  证明: by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · exact (continuousOn_zpow₀ m).mono fun x hx => ne_of_gt hx
  intro x hx
  rw [mem_Ioi] at hx
  rw [iter_deriv_zpow]
  refine mul_pos ?_ (zpow_pos hx _)
  norm_cast
  refine int_prod_range_pos (by decide) fun hm => ?_
  rw [← Finset.coe_Ico] at hm
  norm_cast at hm
  fin_cases hm <;> simp_all

Depends on / 依赖: Finset, Finset.coe_Ico, coe_Ico, convex_Ioi, fin_cases, int_prod_range_pos, iter_deriv_zpow, mem_Ioi, mul_pos, ne_of_gt, strictConvexOn_of_deriv2_pos, zpow_pos
-/
theorem strictConvexOn_zpow {m : Int} (hm₀ : m != 0) (hm₁ : m != 1) :
    StrictConvexOn Real (Ioi 0) fun x : Real => x ^ m := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · exact (continuousOn_zpow₀ m).mono fun x hx => ne_of_gt hx
  intro x hx
  rw [mem_Ioi] at hx
  rw [iter_deriv_zpow]
  refine mul_pos ?_ (zpow_pos hx _)
  norm_cast
  refine int_prod_range_pos (by decide) fun hm => ?_
  rw [← Finset.coe_Ico] at hm
  norm_cast at hm
  fin_cases hm <;> simp_all

section SqrtMulLog

/--
theorem `hasDerivAt_sqrt_mul_log` / 定理 `hasDerivAt_sqrt_mul_log`

English:
theorem hasDerivAt_sqrt_mul_log
  given: {x : Real} (hx : x != 0)
  proof: by
  convert! (hasDerivAt_sqrt hx).mul (hasDerivAt_log hx) using 1
  rw [add_div]; rw [div_mul_cancel_left₀ two_ne_zero]; rw [← div_eq_mul_inv]; rw [sqrt_div_self']; rw [add_comm]; rw [one_div]; rw [one_div]; rw [← div_eq_inv_mul]

中文:
定理 hasDerivAt_sqrt_mul_log
  条件: {x : 实数} (hx : x != 0)
  证明: by
  convert! (hasDerivAt_sqrt hx).mul (hasDerivAt_log hx) using 1
  rw [add_div]; rw [div_mul_cancel_left₀ two_ne_zero]; rw [← div_eq_mul_inv]; rw [sqrt_div_self']; rw [add_comm]; rw [one_div]; rw [one_div]; rw [← div_eq_inv_mul]

Depends on / 依赖: add_comm, add_div, convert, div_eq_inv_mul, div_eq_mul_inv, hasDerivAt_log, hasDerivAt_sqrt, one_div, sqrt_div_self, two_ne_zero
-/
theorem hasDerivAt_sqrt_mul_log {x : Real} (hx : x != 0) :
    HasDerivAt (fun x => √x * log x) ((2 + log x) / (2 * √x)) x := by
  convert! (hasDerivAt_sqrt hx).mul (hasDerivAt_log hx) using 1
  rw [add_div]; rw [div_mul_cancel_left₀ two_ne_zero]; rw [← div_eq_mul_inv]; rw [sqrt_div_self']; rw [add_comm]; rw [one_div]; rw [one_div]; rw [← div_eq_inv_mul]

/--
theorem `deriv_sqrt_mul_log` / 定理 `deriv_sqrt_mul_log`

English:
theorem deriv_sqrt_mul_log
  given: (x : Real)
  proof: by
  rcases lt_or_ge 0 x with hx | hx
  · exact (hasDerivAt_sqrt_mul_log hx.ne').deriv
  · rw [sqrt_eq_zero_of_nonpos hx, mul_zero, div_zero]
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic 0 x hx)
    refine (hasDerivWithinAt_const x _ 0).congr_of_mem (fun x hx => ?_) hx
    rw [sqrt_eq_zero_of_nonpos hx]; rw [zero_mul]

中文:
定理 deriv_sqrt_mul_log
  条件: (x : 实数)
  证明: by
  rcases lt_or_ge 0 x with hx | hx
  · exact (hasDerivAt_sqrt_mul_log hx.ne').deriv
  · rw [sqrt_eq_zero_of_nonpos hx, mul_zero, div_zero]
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic 0 x hx)
    refine (hasDerivWithinAt_const x _ 0).congr_of_mem (fun x hx => ?_) hx
    rw [sqrt_eq_zero_of_nonpos hx]; rw [zero_mul]

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.deriv_eq_zero, congr_of_mem, deriv_eq_zero, div_zero, hasDerivAt_sqrt_mul_log, hasDerivWithinAt_const, hx.ne, lt_or_ge, mul_zero, sqrt_eq_zero_of_nonpos, uniqueDiffOn_Iic, zero_mul
-/
theorem deriv_sqrt_mul_log (x : Real) :
    deriv (fun x => √x * log x) x = (2 + log x) / (2 * √x) := by
  rcases lt_or_ge 0 x with hx | hx
  · exact (hasDerivAt_sqrt_mul_log hx.ne').deriv
  · rw [sqrt_eq_zero_of_nonpos hx, mul_zero, div_zero]
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic 0 x hx)
    refine (hasDerivWithinAt_const x _ 0).congr_of_mem (fun x hx => ?_) hx
    rw [sqrt_eq_zero_of_nonpos hx]; rw [zero_mul]

/--
theorem `deriv_sqrt_mul_log'` / 定理 `deriv_sqrt_mul_log'`

English:
theorem deriv_sqrt_mul_log'
  proof: funext deriv_sqrt_mul_log

中文:
定理 deriv_sqrt_mul_log'
  证明: funext deriv_sqrt_mul_log

Depends on / 依赖: deriv_sqrt_mul_log
-/
theorem deriv_sqrt_mul_log' :
    (deriv fun x => √x * log x) = fun x => (2 + log x) / (2 * √x) :=
  funext deriv_sqrt_mul_log

/--
theorem `deriv2_sqrt_mul_log` / 定理 `deriv2_sqrt_mul_log`

English:
theorem deriv2_sqrt_mul_log
  given: (x : Real)
  proof: by
  simp only [Nat.iterate, deriv_sqrt_mul_log']
  rcases le_or_gt x 0 with hx | hx
  · rw [sqrt_eq_zero_of_nonpos hx, zero_pow three_ne_zero, mul_zero, div_zero]
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic 0 x hx)
    refine (hasDerivWithinAt_const _ _ 0).congr_of_mem (fun x hx => ?_) hx
    rw [sqrt_eq_zero_of_nonpos hx]; rw [mul_zero]; rw [div_zero]
  · have h₀ : √x != 0 := sqrt_ne_zero'.2 hx
    convert!
      (((hasDerivAt_log hx.ne').const_add 2).div ((hasDerivAt_sqrt hx.ne').const_mul 2) <|
          mul_ne_zero two_ne_zero h₀).deriv using 1
    nth_rw 3 [← mul_self_sqrt hx.le]
    field

中文:
定理 deriv2_sqrt_mul_log
  条件: (x : 实数)
  证明: by
  simp only [Nat.iterate, deriv_sqrt_mul_log']
  rcases le_or_gt x 0 with hx | hx
  · rw [sqrt_eq_zero_of_nonpos hx, zero_pow three_ne_zero, mul_zero, div_zero]
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic 0 x hx)
    refine (hasDerivWithinAt_const _ _ 0).congr_of_mem (fun x hx => ?_) hx
    rw [sqrt_eq_zero_of_nonpos hx]; rw [mul_zero]; rw [div_zero]
  · have h₀ : √x != 0 := sqrt_ne_zero'.2 hx
    convert!
      (((hasDerivAt_log hx.ne').const_add 2).div ((hasDerivAt_sqrt hx.ne').const_mul 2) <|
          mul_ne_zero two_ne_zero h₀).deriv using 1
    nth_rw 3 [← mul_self_sqrt hx.le]
    field

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.deriv_eq_zero, Nat.iterate, congr_of_mem, const_add, const_mul, convert, deriv_eq_zero, deriv_sqrt_mul_log, div_zero, hasDerivAt_log, hasDerivAt_sqrt, hasDerivWithinAt_const, hx.ne, iterate, le_or_gt, mul_ne_, mul_zero, sqrt_eq_zero_of_nonpos, sqrt_ne_zero
-/
theorem deriv2_sqrt_mul_log (x : Real) :
    deriv^[2] (fun x => √x * log x) x = -log x / (4 * √x ^ 3) := by
  simp only [Nat.iterate, deriv_sqrt_mul_log']
  rcases le_or_gt x 0 with hx | hx
  · rw [sqrt_eq_zero_of_nonpos hx, zero_pow three_ne_zero, mul_zero, div_zero]
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic 0 x hx)
    refine (hasDerivWithinAt_const _ _ 0).congr_of_mem (fun x hx => ?_) hx
    rw [sqrt_eq_zero_of_nonpos hx]; rw [mul_zero]; rw [div_zero]
  · have h₀ : √x != 0 := sqrt_ne_zero'.2 hx
    convert!
      (((hasDerivAt_log hx.ne').const_add 2).div ((hasDerivAt_sqrt hx.ne').const_mul 2) <|
          mul_ne_zero two_ne_zero h₀).deriv using 1
    nth_rw 3 [← mul_self_sqrt hx.le]
    field

/--
theorem `strictConcaveOn_sqrt_mul_log_Ioi` / 定理 `strictConcaveOn_sqrt_mul_log_Ioi`

English:
theorem strictConcaveOn_sqrt_mul_log_Ioi
  proof: by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 1) _ fun x hx => ?_
  · exact continuous_sqrt.continuousOn.mul
      (continuousOn_log.mono fun x hx => ne_of_gt (zero_lt_one.trans hx))
  · rw [deriv2_sqrt_mul_log x]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (log_pos hx))
      (mul_pos four_pos (pow_pos (sqrt_pos.mpr (zero_lt_one.trans hx)) 3))

中文:
定理 strictConcaveOn_sqrt_mul_log_Ioi
  证明: by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 1) _ fun x hx => ?_
  · exact continuous_sqrt.continuousOn.mul
      (continuousOn_log.mono fun x hx => ne_of_gt (zero_lt_one.trans hx))
  · rw [deriv2_sqrt_mul_log x]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (log_pos hx))
      (mul_pos four_pos (pow_pos (sqrt_pos.mpr (zero_lt_one.trans hx)) 3))

Depends on / 依赖: continuousOn, continuousOn_log, continuousOn_log.mono, continuous_sqrt, continuous_sqrt.continuousOn.mul, convex_Ioi, deriv2_sqrt_mul_log, div_neg_of_neg_of_pos, four_pos, log_pos, mul_pos, ne_of_gt, neg_neg_of_pos, pow_pos, sqrt_pos, sqrt_pos.mpr, strictConcaveOn_of_deriv2_neg, zero_lt_one, zero_lt_one.trans
-/
theorem strictConcaveOn_sqrt_mul_log_Ioi :
    StrictConcaveOn Real (Set.Ioi 1) fun x => √x * log x := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 1) _ fun x hx => ?_
  · exact continuous_sqrt.continuousOn.mul
      (continuousOn_log.mono fun x hx => ne_of_gt (zero_lt_one.trans hx))
  · rw [deriv2_sqrt_mul_log x]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (log_pos hx))
      (mul_pos four_pos (pow_pos (sqrt_pos.mpr (zero_lt_one.trans hx)) 3))

end SqrtMulLog

open scoped Real

/--
theorem `strictConcaveOn_sin_Icc` / 定理 `strictConcaveOn_sin_Icc`

English:
theorem strictConcaveOn_sin_Icc
  statement: StrictConcaveOn Real (Icc 0 π) sin
  proof: by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_sin fun x hx => ?_
  rw [interior_Icc] at hx
  simp [sin_pos_of_mem_Ioo hx]

中文:
定理 strictConcaveOn_sin_Icc
  结论: StrictConcaveOn 实数 (闭区间 0 π) sin
  证明: by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_sin fun x hx => ?_
  rw [interior_Icc] at hx
  simp [sin_pos_of_mem_Ioo hx]

Depends on / 依赖: continuousOn_sin, convex_Icc, interior_Icc, sin_pos_of_mem_Ioo, strictConcaveOn_of_deriv2_neg
-/
theorem strictConcaveOn_sin_Icc : StrictConcaveOn Real (Icc 0 π) sin := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_sin fun x hx => ?_
  rw [interior_Icc] at hx
  simp [sin_pos_of_mem_Ioo hx]

/--
theorem `strictConcaveOn_cos_Icc` / 定理 `strictConcaveOn_cos_Icc`

English:
theorem strictConcaveOn_cos_Icc
  statement: StrictConcaveOn Real (Icc (-(π / 2)) (π / 2)) cos
  proof: by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_cos fun x hx => ?_
  rw [interior_Icc] at hx
  simp [cos_pos_of_mem_Ioo hx]

中文:
定理 strictConcaveOn_cos_Icc
  结论: StrictConcaveOn 实数 (闭区间 (-(π / 2)) (π / 2)) cos
  证明: by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_cos fun x hx => ?_
  rw [interior_Icc] at hx
  simp [cos_pos_of_mem_Ioo hx]

Depends on / 依赖: continuousOn_cos, convex_Icc, cos_pos_of_mem_Ioo, interior_Icc, strictConcaveOn_of_deriv2_neg
-/
theorem strictConcaveOn_cos_Icc : StrictConcaveOn Real (Icc (-(π / 2)) (π / 2)) cos := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_cos fun x hx => ?_
  rw [interior_Icc] at hx
  simp [cos_pos_of_mem_Ioo hx]
