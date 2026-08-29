/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Michael Stoll
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# L-series

Given a sequence `f: ℕ → ℂ`, we define the corresponding L-series.

## Main Definitions

* `LSeries.term f s n` is the `n`th term of the L-series of the sequence `f` at `s : ℂ`.
  We define it to be zero when `n = 0`.

* `LSeries f` is the L-series with a given sequence `f` as its coefficients. This is not the
  analytic continuation (which does not necessarily exist), just the sum of the infinite series if
  it exists and zero otherwise.

* `LSeriesSummable f s` indicates that the L-series of `f` converges at `s : ℂ`.

* `LSeriesHasSum f s a` expresses that the L-series of `f` converges (absolutely) at `s : ℂ` to
  `a : ℂ`.

## Main Results

* `LSeriesSummable_of_isBigO_rpow`: the `LSeries` of a sequence `f` such that `f = O(n^(x-1))`
  converges at `s` when `x < s.re`.

* `LSeriesSummable.isBigO_rpow`: if the `LSeries` of `f` is summable at `s`, then `f = O(n^(re s))`.

## Notation

We introduce `L` as notation for `LSeries` and `↗f` as notation for `fun n : ℕ ↦ (f n : ℂ)`,
both scoped to `LSeries.notation`. The latter makes it convenient to use arithmetic functions
or Dirichlet characters (or anything that coerces to a function `N → R`, where `ℕ` coerces
to `N` and `R` coerces to `ℂ`) as arguments to `LSeries` etc.

## Reference

For some background on the design decisions made when implementing L-series in Mathlib
(and applications motivating the development), see the paper
[Formalizing zeta and L-functions in Lean](https://arxiv.org/abs/2503.00959)
by David Loeffler and Michael Stoll.

## Tags

L-series
-/

@[expose] public section

open Complex

/-!
### The terms of an L-series

We define the `n`th term evaluated at a complex number `s` of the L-series associated
to a sequence `f : ℕ → ℂ`, `LSeries.term f s n`, and provide some basic API.

We set `LSeries.term f s 0 = 0`, and for positive `n`, `LSeries.term f s n = f n / n ^ s`.
-/

namespace LSeries

/-- The `n`th term of the L-series of `f` evaluated at `s`. We set it to zero when `n = 0`. -/
noncomputable
/--
Definition of `term` / `term` 的定义

English:
definition term
  signature: (f : Nat -> Complex) (s : Complex) (n : Nat)
  body: if n = 0 then 0 else f n / n ^ s

中文:
定义 term
  签名: (f : 自然数 -> Complex) (s : Complex) (n : 自然数)
  定义体: if n = 0 then 0 else f n / n ^ s
-/
def term (f : Nat -> Complex) (s : Complex) (n : Nat) : Complex :=
  if n = 0 then 0 else f n / n ^ s

/--
lemma `term_def` / 引理 `term_def`

English:
lemma term_def
  given: (f : Nat -> Complex) (s : Complex) (n : Nat)
  proof: rfl

中文:
引理 term_def
  条件: (f : 自然数 -> Complex) (s : Complex) (n : 自然数)
  证明: rfl
-/
lemma term_def (f : Nat -> Complex) (s : Complex) (n : Nat) :
    term f s n = if n = 0 then 0 else f n / n ^ s :=
  rfl

/--
lemma `term_def₀` / 引理 `term_def₀`

English:
lemma term_def₀
  given: {f : Nat -> Complex} (hf : f 0 = 0) (s : Complex) (n : Nat)
  proof: by
  rw [LSeries.term]
  split_ifs with h <;> simp [h, hf, cpow_neg, div_eq_inv_mul, mul_comm]

@[simp]

中文:
引理 term_def₀
  条件: {f : 自然数 -> Complex} (hf : f 0 = 0) (s : Complex) (n : 自然数)
  证明: by
  rw [LSeries.term]
  split_ifs with h <;> simp [h, hf, cpow_neg, div_eq_inv_mul, mul_comm]

@[simp]

Depends on / 依赖: LSeries, LSeries.term, cpow_neg, div_eq_inv_mul, mul_comm, split_ifs
-/
lemma term_def₀ {f : Nat -> Complex} (hf : f 0 = 0) (s : Complex) (n : Nat) :
    LSeries.term f s n = f n * (n : Complex) ^ (-s) := by
  rw [LSeries.term]
  split_ifs with h <;> simp [h, hf, cpow_neg, div_eq_inv_mul, mul_comm]

@[simp]
/--
lemma `term_zero` / 引理 `term_zero`

English:
lemma term_zero
  given: (f : Nat -> Complex) (s : Complex)
  statement: term f s 0 = 0
  proof: rfl

中文:
引理 term_zero
  条件: (f : 自然数 -> Complex) (s : Complex)
  结论: term f s 0 = 0
  证明: rfl
-/
lemma term_zero (f : Nat -> Complex) (s : Complex) : term f s 0 = 0 := rfl

-- We put `hn` first for convenience, so that we can write `rw [LSeries.term_of_ne_zero hn]` etc.
@[simp]
/--
lemma `term_of_ne_zero` / 引理 `term_of_ne_zero`

English:
lemma term_of_ne_zero
  given: {n : Nat} (hn : n != 0) (f : Nat -> Complex) (s : Complex)
  proof: if_neg hn

中文:
引理 term_of_ne_zero
  条件: {n : 自然数} (hn : n != 0) (f : 自然数 -> Complex) (s : Complex)
  证明: if_neg hn

Depends on / 依赖: if_neg
-/
lemma term_of_ne_zero {n : Nat} (hn : n != 0) (f : Nat -> Complex) (s : Complex) :
    term f s n = f n / n ^ s :=
  if_neg hn

/--
lemma `term_of_ne_zero'` / 引理 `term_of_ne_zero'`

English:
lemma term_of_ne_zero'
  given: {s : Complex} (hs : s != 0) (f : Nat -> Complex) (n : Nat)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [term_zero, Nat.cast_zero, zero_cpow hs, div_zero]
  · rw [term_of_ne_zero hn]

中文:
引理 term_of_ne_zero'
  条件: {s : Complex} (hs : s != 0) (f : 自然数 -> Complex) (n : 自然数)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [term_zero, Nat.cast_zero, zero_cpow hs, div_zero]
  · rw [term_of_ne_zero hn]

Depends on / 依赖: Nat.cast_zero, cast_zero, div_zero, eq_or_ne, term_of_ne_zero, term_zero, zero_cpow
-/
lemma term_of_ne_zero' {s : Complex} (hs : s != 0) (f : Nat -> Complex) (n : Nat) :
    term f s n = f n / n ^ s := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [term_zero, Nat.cast_zero, zero_cpow hs, div_zero]
  · rw [term_of_ne_zero hn]

/--
lemma `term_congr` / 引理 `term_congr`

English:
lemma term_congr
  given: {f g : Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n) (s : Complex) (n : Nat)
  proof: by
  rcases eq_or_ne n 0 with hn | hn <;> simp [hn, h]

中文:
引理 term_congr
  条件: {f g : 自然数 -> Complex} (h : 对任意 {n}, n != 0 -> f n = g n) (s : Complex) (n : 自然数)
  证明: by
  rcases eq_or_ne n 0 with hn | hn <;> simp [hn, h]

Depends on / 依赖: eq_or_ne
-/
lemma term_congr {f g : Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n) (s : Complex) (n : Nat) :
    term f s n = term g s n := by
  rcases eq_or_ne n 0 with hn | hn <;> simp [hn, h]

/--
lemma `pow_mul_term_eq` / 引理 `pow_mul_term_eq`

English:
lemma pow_mul_term_eq
  given: (f : Nat -> Complex) (s : Complex) (n : Nat)
  proof: by
  simp [term, natCast_add_one_cpow_ne_zero n _, mul_div_assoc']

中文:
引理 pow_mul_term_eq
  条件: (f : 自然数 -> Complex) (s : Complex) (n : 自然数)
  证明: by
  simp [term, natCast_add_one_cpow_ne_zero n _, mul_div_assoc']

Depends on / 依赖: mul_div_assoc, natCast_add_one_cpow_ne_zero
-/
lemma pow_mul_term_eq (f : Nat -> Complex) (s : Complex) (n : Nat) :
    (n + 1) ^ s * term f s (n + 1) = f (n + 1) := by
  simp [term, natCast_add_one_cpow_ne_zero n _, mul_div_assoc']

/--
lemma `norm_term_eq` / 引理 `norm_term_eq`

English:
lemma norm_term_eq
  given: (f : Nat -> Complex) (s : Complex) (n : Nat)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, norm_natCast_cpow_of_pos <| Nat.pos_of_ne_zero hn]

中文:
引理 norm_term_eq
  条件: (f : 自然数 -> Complex) (s : Complex) (n : 自然数)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, norm_natCast_cpow_of_pos <| Nat.pos_of_ne_zero hn]

Depends on / 依赖: Nat.pos_of_ne_zero, eq_or_ne, norm_natCast_cpow_of_pos, pos_of_ne_zero
-/
lemma norm_term_eq (f : Nat -> Complex) (s : Complex) (n : Nat) :
    ‖term f s n‖ = if n = 0 then 0 else ‖f n‖ / n ^ s.re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, norm_natCast_cpow_of_pos <| Nat.pos_of_ne_zero hn]

/--
lemma `norm_term_le` / 引理 `norm_term_le`

English:
lemma norm_term_le
  given: {f g : Nat -> Complex} (s : Complex) {n : Nat} (h : ‖f n‖ <= ‖g n‖)
  proof: by
  simp only [norm_term_eq]
  split
  · rfl
  · gcongr

中文:
引理 norm_term_le
  条件: {f g : 自然数 -> Complex} (s : Complex) {n : 自然数} (h : ‖f n‖ <= ‖g n‖)
  证明: by
  simp only [norm_term_eq]
  split
  · rfl
  · gcongr

Depends on / 依赖: norm_term_eq
-/
lemma norm_term_le {f g : Nat -> Complex} (s : Complex) {n : Nat} (h : ‖f n‖ <= ‖g n‖) :
    ‖term f s n‖ <= ‖term g s n‖ := by
  simp only [norm_term_eq]
  split
  · rfl
  · gcongr

/--
lemma `norm_term_le_of_re_le_re` / 引理 `norm_term_le_of_re_le_re`

English:
lemma norm_term_le_of_re_le_re
  given: (f : Nat -> Complex) {s s' : Complex} (h : s.re <= s'.re) (n : Nat)
  proof: by
  simp only [norm_term_eq]
  split
  · next => rfl
· next hn => gcongr; exact Nat.one_le_cast.mpr Nat.one_le_iff_ne_zero.mpr hn

中文:
引理 norm_term_le_of_re_le_re
  条件: (f : 自然数 -> Complex) {s s' : Complex} (h : s.re <= s'.re) (n : 自然数)
  证明: by
  simp only [norm_term_eq]
  split
  · next => rfl
· next hn => gcongr; exact Nat.one_le_cast.mpr Nat.one_le_iff_ne_zero.mpr hn

Depends on / 依赖: Nat.one_le_cast.mpr, Nat.one_le_iff_ne_zero.mpr, norm_term_eq, one_le_cast, one_le_iff_ne_zero
-/
lemma norm_term_le_of_re_le_re (f : Nat -> Complex) {s s' : Complex} (h : s.re <= s'.re) (n : Nat) :
    ‖term f s' n‖ <= ‖term f s n‖ := by
  simp only [norm_term_eq]
  split
  · next => rfl
· next hn => gcongr; exact Nat.one_le_cast.mpr Nat.one_le_iff_ne_zero.mpr hn

section positivity

open scoped ComplexOrder

/--
lemma `term_nonneg` / 引理 `term_nonneg`

English:
lemma term_nonneg
  given: {a : Nat -> Complex} {n : Nat} (h : 0 <= a n) (x : Real)
  statement: 0 <= term a x n
  proof: by
  rw [term_def]
  split_ifs with hn
  exacts [le_rfl, mul_nonneg h (inv_natCast_cpow_ofReal_pos hn x).le]

中文:
引理 term_nonneg
  条件: {a : 自然数 -> Complex} {n : 自然数} (h : 0 <= a n) (x : 实数)
  结论: 0 <= term a x n
  证明: by
  rw [term_def]
  split_ifs with hn
  exacts [le_rfl, mul_nonneg h (inv_natCast_cpow_ofReal_pos hn x).le]

Depends on / 依赖: exacts, inv_natCast_cpow_ofReal_pos, le_rfl, mul_nonneg, split_ifs, term_def
-/
lemma term_nonneg {a : Nat -> Complex} {n : Nat} (h : 0 <= a n) (x : Real) : 0 <= term a x n := by
  rw [term_def]
  split_ifs with hn
  exacts [le_rfl, mul_nonneg h (inv_natCast_cpow_ofReal_pos hn x).le]

/--
lemma `term_pos` / 引理 `term_pos`

English:
lemma term_pos
  given: {a : Nat -> Complex} {n : Nat} (hn : n != 0) (h : 0 < a n) (x : Real)
  statement: 0 < term a x n
  proof: by
simpa only [term_of_ne_zero hn] using! mul_pos h inv_natCast_cpow_ofReal_pos hn x

中文:
引理 term_pos
  条件: {a : 自然数 -> Complex} {n : 自然数} (hn : n != 0) (h : 0 < a n) (x : 实数)
  结论: 0 < term a x n
  证明: by
simpa only [term_of_ne_zero hn] using! mul_pos h inv_natCast_cpow_ofReal_pos hn x

Depends on / 依赖: inv_natCast_cpow_ofReal_pos, mul_pos, term_of_ne_zero
-/
lemma term_pos {a : Nat -> Complex} {n : Nat} (hn : n != 0) (h : 0 < a n) (x : Real) : 0 < term a x n := by
simpa only [term_of_ne_zero hn] using! mul_pos h inv_natCast_cpow_ofReal_pos hn x

end positivity

end LSeries

/-!
### Definition of the L-series and related statements

We define `LSeries f s` of `f : ℕ → ℂ` as the sum over `LSeries.term f s`.
We also provide predicates `LSeriesSummable f s` stating that `LSeries f s` is summable
and `LSeriesHasSum f s a` stating that the L-series of `f` is summable at `s` and converges
to `a : ℂ`.
-/

open LSeries

/-- The value of the L-series of the sequence `f` at the point `s`
if it converges absolutely there, and `0` otherwise. -/
noncomputable
/--
Definition of `LSeries` / `LSeries` 的定义

English:
definition LSeries
  signature: (f : Nat -> Complex) (s : Complex)
  body: ∑' n, term f s n

中文:
定义 LSeries
  签名: (f : 自然数 -> Complex) (s : Complex)
  定义体: ∑' n, term f s n
-/
def LSeries (f : Nat -> Complex) (s : Complex) : Complex :=
  ∑' n, term f s n

/--
lemma `LSeries_congr` / 引理 `LSeries_congr`

English:
lemma LSeries_congr
  given: {f g : Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n) (s : Complex)
  proof: tsum_congr term_congr h s

中文:
引理 LSeries_congr
  条件: {f g : 自然数 -> Complex} (h : 对任意 {n}, n != 0 -> f n = g n) (s : Complex)
  证明: tsum_congr term_congr h s

Depends on / 依赖: term_congr, tsum_congr
-/
lemma LSeries_congr {f g : Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n) (s : Complex) :
    LSeries f s = LSeries g s :=
tsum_congr term_congr h s

/--
lemma `LSeries_def₀` / 引理 `LSeries_def₀`

English:
lemma LSeries_def₀
  given: {f : Nat -> Complex} (hf : f 0 = 0) (s : Complex)
  proof: by
  simp [LSeries, LSeries.term_def₀ hf, cpow_neg, div_eq_mul_inv]

中文:
引理 LSeries_def₀
  条件: {f : 自然数 -> Complex} (hf : f 0 = 0) (s : Complex)
  证明: by
  simp [LSeries, LSeries.term_def₀ hf, cpow_neg, div_eq_mul_inv]

Depends on / 依赖: LSeries, LSeries.term_def, cpow_neg, div_eq_mul_inv
-/
lemma LSeries_def₀ {f : Nat -> Complex} (hf : f 0 = 0) (s : Complex) :
    LSeries f s = ∑' n, f n / (n ^ s) := by
  simp [LSeries, LSeries.term_def₀ hf, cpow_neg, div_eq_mul_inv]

/--
Definition of `LSeriesSummable` / `LSeriesSummable` 的定义

English:
definition LSeriesSummable
  signature: (f : Nat -> Complex) (s : Complex)
  body: Summable (term f s)

中文:
定义 LSeriesSummable
  签名: (f : 自然数 -> Complex) (s : Complex)
  定义体: Summable (term f s)

Depends on / 依赖: Summable
-/
def LSeriesSummable (f : Nat -> Complex) (s : Complex) : Prop :=
  Summable (term f s)

/--
lemma `LSeriesSummable_congr` / 引理 `LSeriesSummable_congr`

English:
lemma LSeriesSummable_congr
  given: {f g : Nat -> Complex} (s : Complex) (h : forall {n}, n != 0 -> f n = g n)
  proof: summable_congr term_congr h s

中文:
引理 LSeriesSummable_congr
  条件: {f g : 自然数 -> Complex} (s : Complex) (h : 对任意 {n}, n != 0 -> f n = g n)
  证明: summable_congr term_congr h s

Depends on / 依赖: summable_congr, term_congr
-/
lemma LSeriesSummable_congr {f g : Nat -> Complex} (s : Complex) (h : forall {n}, n != 0 -> f n = g n) :
    LSeriesSummable f s ↔ LSeriesSummable g s :=
summable_congr term_congr h s

open Filter in
/--
lemma `LSeriesSummable.congr'` / 引理 `LSeriesSummable.congr'`

English:
lemma LSeriesSummable.congr'
  given: {f g : Nat -> Complex} (s : Complex) (h : f =ᶠ[atTop] g) (hf : LSeriesSummable f s)
  proof: by
  rw [← Nat.cofinite_eq_atTop] at h
  refine (summable_norm_iff.mpr hf).of_norm_bounded_eventually ?_
  have : term f s =ᶠ[cofinite] term g s := by
    rw [eventuallyEq_iff_exists_mem] at h ⊢
    obtain ⟨S, hS, hS'⟩ := h
refine ⟨S \ {0}, sdiff_mem hS (Set.finite_singleton 0).compl_mem_cofinite, f

中文:
引理 LSeriesSummable.congr'
  条件: {f g : 自然数 -> Complex} (s : Complex) (h : f =ᶠ[atTop] g) (hf : LSeriesSummable f s)
  证明: by
  rw [← Nat.cofinite_eq_atTop] at h
  refine (summable_norm_iff.mpr hf).of_norm_bounded_eventually ?_
  have : term f s =ᶠ[cofinite] term g s := by
    rw [eventuallyEq_iff_exists_mem] at h ⊢
    obtain ⟨S, hS, hS'⟩ := h
refine ⟨S \ {0}, sdiff_mem hS (Set.finite_singleton 0).compl_mem_cofinite, f

Depends on / 依赖: Nat.cofinite_eq_atTop, Set.finite_singleton, Set.mem_sdiff, Set.mem_singleton_iff, cofinite, cofinite_eq_atTop, compl_mem_cofinite, eventuallyEq_iff_exists_mem, finite_singleton, mem_sdiff, mem_singleton_iff, of_norm_bounded_eventually, sdiff_mem, summable_norm_iff, summable_norm_iff.mpr, this.symm.mono
-/
lemma LSeriesSummable.congr' {f g : Nat -> Complex} (s : Complex) (h : f =ᶠ[atTop] g) (hf : LSeriesSummable f s) :
    LSeriesSummable g s := by
  rw [← Nat.cofinite_eq_atTop] at h
  refine (summable_norm_iff.mpr hf).of_norm_bounded_eventually ?_
  have : term f s =ᶠ[cofinite] term g s := by
    rw [eventuallyEq_iff_exists_mem] at h ⊢
    obtain ⟨S, hS, hS'⟩ := h
refine ⟨S \ {0}, sdiff_mem hS (Set.finite_singleton 0).compl_mem_cofinite, fun n hn => ?_⟩
    rw [Set.mem_sdiff]; rw [Set.mem_singleton_iff] at hn
    simp [hn.2, hS' hn.1]
  exact this.symm.mono fun n hn => by simp [hn]

open Filter in
/--
lemma `LSeriesSummable_congr'` / 引理 `LSeriesSummable_congr'`

English:
lemma LSeriesSummable_congr'
  given: {f g : Nat -> Complex} (s : Complex) (h : f =ᶠ[atTop] g)
  proof: ⟨fun H => H.congr' s h, fun H => H.congr' s h.symm⟩

中文:
引理 LSeriesSummable_congr'
  条件: {f g : 自然数 -> Complex} (s : Complex) (h : f =ᶠ[atTop] g)
  证明: ⟨fun H => H.congr' s h, fun H => H.congr' s h.symm⟩

Depends on / 依赖: H.congr, h.symm
-/
lemma LSeriesSummable_congr' {f g : Nat -> Complex} (s : Complex) (h : f =ᶠ[atTop] g) :
    LSeriesSummable f s ↔ LSeriesSummable g s :=
  ⟨fun H => H.congr' s h, fun H => H.congr' s h.symm⟩

/--
theorem `LSeries.eq_zero_of_not_LSeriesSummable` / 定理 `LSeries.eq_zero_of_not_LSeriesSummable`

English:
theorem LSeries.eq_zero_of_not_LSeriesSummable
  given: (f : Nat -> Complex) (s : Complex)
  proof: tsum_eq_zero_of_not_summable

@[simp]

中文:
定理 LSeries.eq_zero_of_not_LSeriesSummable
  条件: (f : 自然数 -> Complex) (s : Complex)
  证明: tsum_eq_zero_of_not_summable

@[simp]

Depends on / 依赖: tsum_eq_zero_of_not_summable
-/
theorem LSeries.eq_zero_of_not_LSeriesSummable (f : Nat -> Complex) (s : Complex) :
    ¬ LSeriesSummable f s -> LSeries f s = 0 :=
  tsum_eq_zero_of_not_summable

@[simp]
/--
theorem `LSeriesSummable_zero` / 定理 `LSeriesSummable_zero`

English:
theorem LSeriesSummable_zero
  given: {s : Complex}
  statement: LSeriesSummable 0 s
  proof: by
  simp [LSeriesSummable, funext (term_def 0 s), summable_zero]

中文:
定理 LSeriesSummable_zero
  条件: {s : Complex}
  结论: LSeriesSummable 0 s
  证明: by
  simp [LSeriesSummable, funext (term_def 0 s), summable_zero]

Depends on / 依赖: LSeriesSummable, summable_zero, term_def
-/
theorem LSeriesSummable_zero {s : Complex} : LSeriesSummable 0 s := by
  simp [LSeriesSummable, funext (term_def 0 s), summable_zero]

/--
Definition of `LSeriesHasSum` / `LSeriesHasSum` 的定义

English:
definition LSeriesHasSum
  signature: (f : Nat -> Complex) (s a : Complex)
  body: HasSum (term f s) a

中文:
定义 LSeriesHasSum
  签名: (f : 自然数 -> Complex) (s a : Complex)
  定义体: HasSum (term f s) a

Depends on / 依赖: HasSum
-/
def LSeriesHasSum (f : Nat -> Complex) (s a : Complex) : Prop :=
  HasSum (term f s) a

/--
lemma `LSeriesHasSum.LSeriesSummable` / 引理 `LSeriesHasSum.LSeriesSummable`

English:
lemma LSeriesHasSum.LSeriesSummable
  statement: {f : Nat -> Complex} {s a : Complex}
  proof: h.summable

中文:
引理 LSeriesHasSum.LSeriesSummable
  结论: {f : 自然数 -> Complex} {s a : Complex}
  证明: h.summable

Depends on / 依赖: h.summable, summable
-/
lemma LSeriesHasSum.LSeriesSummable {f : Nat -> Complex} {s a : Complex}
    (h : LSeriesHasSum f s a) : LSeriesSummable f s :=
  h.summable

/--
lemma `LSeriesHasSum.LSeries_eq` / 引理 `LSeriesHasSum.LSeries_eq`

English:
lemma LSeriesHasSum.LSeries_eq
  statement: {f : Nat -> Complex} {s a : Complex}
  proof: h.tsum_eq

中文:
引理 LSeriesHasSum.LSeries_eq
  结论: {f : 自然数 -> Complex} {s a : Complex}
  证明: h.tsum_eq

Depends on / 依赖: h.tsum_eq, tsum_eq
-/
lemma LSeriesHasSum.LSeries_eq {f : Nat -> Complex} {s a : Complex}
    (h : LSeriesHasSum f s a) : LSeries f s = a :=
  h.tsum_eq

/--
lemma `LSeriesSummable.LSeriesHasSum` / 引理 `LSeriesSummable.LSeriesHasSum`

English:
lemma LSeriesSummable.LSeriesHasSum
  given: {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s)
  proof: h.hasSum

中文:
引理 LSeriesSummable.LSeriesHasSum
  条件: {f : 自然数 -> Complex} {s : Complex} (h : LSeriesSummable f s)
  证明: h.hasSum

Depends on / 依赖: h.hasSum, hasSum
-/
lemma LSeriesSummable.LSeriesHasSum {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s) :
    LSeriesHasSum f s (LSeries f s) :=
  h.hasSum

/--
lemma `LSeriesHasSum_iff` / 引理 `LSeriesHasSum_iff`

English:
lemma LSeriesHasSum_iff
  given: {f : Nat -> Complex} {s a : Complex}
  proof: ⟨fun H => ⟨H.LSeriesSummable, H.LSeries_eq⟩, fun ⟨H₁, H₂⟩ => H₂ ▸ H₁.LSeriesHasSum⟩

中文:
引理 LSeriesHasSum_iff
  条件: {f : 自然数 -> Complex} {s a : Complex}
  证明: ⟨fun H => ⟨H.LSeriesSummable, H.LSeries_eq⟩, fun ⟨H₁, H₂⟩ => H₂ ▸ H₁.LSeriesHasSum⟩

Depends on / 依赖: H.LSeriesSummable, H.LSeries_eq, LSeriesHasSum, LSeriesSummable, LSeries_eq
-/
lemma LSeriesHasSum_iff {f : Nat -> Complex} {s a : Complex} :
    LSeriesHasSum f s a ↔ LSeriesSummable f s ∧ LSeries f s = a :=
  ⟨fun H => ⟨H.LSeriesSummable, H.LSeries_eq⟩, fun ⟨H₁, H₂⟩ => H₂ ▸ H₁.LSeriesHasSum⟩

/--
lemma `LSeriesHasSum_congr` / 引理 `LSeriesHasSum_congr`

English:
lemma LSeriesHasSum_congr
  given: {f g : Nat -> Complex} (s a : Complex) (h : forall {n}, n != 0 -> f n = g n)
  proof: by
  simp [LSeriesHasSum_iff, LSeriesSummable_congr s h, LSeries_congr h s]

中文:
引理 LSeriesHasSum_congr
  条件: {f g : 自然数 -> Complex} (s a : Complex) (h : 对任意 {n}, n != 0 -> f n = g n)
  证明: by
  simp [LSeriesHasSum_iff, LSeriesSummable_congr s h, LSeries_congr h s]

Depends on / 依赖: LSeriesHasSum_iff, LSeriesSummable_congr, LSeries_congr
-/
lemma LSeriesHasSum_congr {f g : Nat -> Complex} (s a : Complex) (h : forall {n}, n != 0 -> f n = g n) :
    LSeriesHasSum f s a ↔ LSeriesHasSum g s a := by
  simp [LSeriesHasSum_iff, LSeriesSummable_congr s h, LSeries_congr h s]

/--
lemma `LSeriesSummable.of_re_le_re` / 引理 `LSeriesSummable.of_re_le_re`

English:
lemma LSeriesSummable.of_re_le_re
  statement: {f : Nat -> Complex} {s s' : Complex} (h : s.re <= s'.re)
  proof: by
  rw [LSeriesSummable]; rw [← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le_of_re_le_re f h)

中文:
引理 LSeriesSummable.of_re_le_re
  结论: {f : 自然数 -> Complex} {s s' : Complex} (h : s.re <= s'.re)
  证明: by
  rw [LSeriesSummable]; rw [← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le_of_re_le_re f h)

Depends on / 依赖: LSeriesSummable, hf.of_nonneg_of_le, norm_nonneg, norm_term_le_of_re_le_re, of_nonneg_of_le, summable_norm_iff
-/
lemma LSeriesSummable.of_re_le_re {f : Nat -> Complex} {s s' : Complex} (h : s.re <= s'.re)
    (hf : LSeriesSummable f s) : LSeriesSummable f s' := by
  rw [LSeriesSummable]; rw [← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le_of_re_le_re f h)

/--
theorem `LSeriesSummable_iff_of_re_eq_re` / 定理 `LSeriesSummable_iff_of_re_eq_re`

English:
theorem LSeriesSummable_iff_of_re_eq_re
  given: {f : Nat -> Complex} {s s' : Complex} (h : s.re = s'.re)
  proof: ⟨fun H => H.of_re_le_re h.le, fun H => H.of_re_le_re h.symm.le⟩

中文:
定理 LSeriesSummable_iff_of_re_eq_re
  条件: {f : 自然数 -> Complex} {s s' : Complex} (h : s.re = s'.re)
  证明: ⟨fun H => H.of_re_le_re h.le, fun H => H.of_re_le_re h.symm.le⟩

Depends on / 依赖: H.of_re_le_re, h.le, h.symm.le, of_re_le_re
-/
theorem LSeriesSummable_iff_of_re_eq_re {f : Nat -> Complex} {s s' : Complex} (h : s.re = s'.re) :
    LSeriesSummable f s ↔ LSeriesSummable f s' :=
  ⟨fun H => H.of_re_le_re h.le, fun H => H.of_re_le_re h.symm.le⟩

/--
Definition of `LSeries.delta` / `LSeries.delta` 的定义

English:
definition LSeries.delta
  signature: (n : Nat)
  body: if n = 1 then 1 else 0

中文:
定义 LSeries.delta
  签名: (n : 自然数)
  定义体: if n = 1 then 1 else 0
-/
def LSeries.delta (n : Nat) : Complex :=
  if n = 1 then 1 else 0

/-!
### Notation
-/

@[inherit_doc]
scoped[LSeries.notation] notation "L" => LSeries

/-- We introduce notation `↗f` for `f` interpreted as a function `ℕ → ℂ`.

Let `R` be a ring with a coercion to `ℂ`. Then we can write `↗χ` when `χ : DirichletCharacter R`
or `↗f` when `f : ArithmeticFunction R` or simply `f : N → R` with a coercion from `ℕ` to `N`
as an argument to `LSeries`, `LSeriesHasSum`, `LSeriesSummable` etc. -/
scoped[LSeries.notation] notation:max "↗" f:max => fun n : Nat => (f n : Complex)

@[inherit_doc]
scoped[LSeries.notation] notation "δ" => delta

/-!
### LSeries of 0 and δ
-/

@[simp]
/--
lemma `LSeries_zero` / 引理 `LSeries_zero`

English:
lemma LSeries_zero
  statement: LSeries 0 = 0
  proof: by
  ext
  simp [LSeries, LSeries.term]

中文:
引理 LSeries_zero
  结论: LSeries 0 = 0
  证明: by
  ext
  simp [LSeries, LSeries.term]

Depends on / 依赖: LSeries, LSeries.term
-/
lemma LSeries_zero : LSeries 0 = 0 := by
  ext
  simp [LSeries, LSeries.term]

section delta

open scoped LSeries.notation

namespace LSeries

open Nat Complex

/--
lemma `term_delta` / 引理 `term_delta`

English:
lemma term_delta
  given: (s : Complex) (n : Nat)
  statement: term δ s n = if n = 1 then 1 else 0
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases eq_or_ne n 1 with hn' | hn' <;>
    simp [hn, hn', delta]

中文:
引理 term_delta
  条件: (s : Complex) (n : 自然数)
  结论: term δ s n = if n = 1 then 1 else 0
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases eq_or_ne n 1 with hn' | hn' <;>
    simp [hn, hn', delta]

Depends on / 依赖: eq_or_ne
-/
lemma term_delta (s : Complex) (n : Nat) : term δ s n = if n = 1 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases eq_or_ne n 1 with hn' | hn' <;>
    simp [hn, hn', delta]

/--
lemma `mul_delta_eq_smul_delta` / 引理 `mul_delta_eq_smul_delta`

English:
lemma mul_delta_eq_smul_delta
  given: {f : Nat -> Complex}
  statement: f * δ = f 1 • δ
  proof: by
  ext n
  by_cases hn : n = 1 <;>
  simp [hn, delta]

中文:
引理 mul_delta_eq_smul_delta
  条件: {f : 自然数 -> Complex}
  结论: f * δ = f 1 • δ
  证明: by
  ext n
  by_cases hn : n = 1 <;>
  simp [hn, delta]
-/
lemma mul_delta_eq_smul_delta {f : Nat -> Complex} : f * δ = f 1 • δ := by
  ext n
  by_cases hn : n = 1 <;>
  simp [hn, delta]

/--
lemma `mul_delta` / 引理 `mul_delta`

English:
lemma mul_delta
  given: {f : Nat -> Complex} (h : f 1 = 1)
  statement: f * δ = δ
  proof: by
  rw [mul_delta_eq_smul_delta]; rw [h]; rw [one_smul]

中文:
引理 mul_delta
  条件: {f : 自然数 -> Complex} (h : f 1 = 1)
  结论: f * δ = δ
  证明: by
  rw [mul_delta_eq_smul_delta]; rw [h]; rw [one_smul]

Depends on / 依赖: mul_delta_eq_smul_delta, one_smul
-/
lemma mul_delta {f : Nat -> Complex} (h : f 1 = 1) : f * δ = δ := by
  rw [mul_delta_eq_smul_delta]; rw [h]; rw [one_smul]

/--
lemma `delta_mul_eq_smul_delta` / 引理 `delta_mul_eq_smul_delta`

English:
lemma delta_mul_eq_smul_delta
  given: {f : Nat -> Complex}
  statement: δ * f = f 1 • δ
  proof: mul_comm δ f ▸ mul_delta_eq_smul_delta

中文:
引理 delta_mul_eq_smul_delta
  条件: {f : 自然数 -> Complex}
  结论: δ * f = f 1 • δ
  证明: mul_comm δ f ▸ mul_delta_eq_smul_delta

Depends on / 依赖: mul_comm, mul_delta_eq_smul_delta
-/
lemma delta_mul_eq_smul_delta {f : Nat -> Complex} : δ * f = f 1 • δ :=
  mul_comm δ f ▸ mul_delta_eq_smul_delta

/--
lemma `delta_mul` / 引理 `delta_mul`

English:
lemma delta_mul
  given: {f : Nat -> Complex} (h : f 1 = 1)
  statement: δ * f = δ
  proof: mul_comm δ f ▸ mul_delta h

中文:
引理 delta_mul
  条件: {f : 自然数 -> Complex} (h : f 1 = 1)
  结论: δ * f = δ
  证明: mul_comm δ f ▸ mul_delta h

Depends on / 依赖: mul_comm, mul_delta
-/
lemma delta_mul {f : Nat -> Complex} (h : f 1 = 1) : δ * f = δ :=
  mul_comm δ f ▸ mul_delta h

end LSeries

/--
lemma `LSeries_delta` / 引理 `LSeries_delta`

English:
lemma LSeries_delta
  statement: LSeries δ = 1
  proof: by
  ext
  simp [LSeries, LSeries.term_delta]

中文:
引理 LSeries_delta
  结论: LSeries δ = 1
  证明: by
  ext
  simp [LSeries, LSeries.term_delta]

Depends on / 依赖: LSeries, LSeries.term_delta, term_delta
-/
lemma LSeries_delta : LSeries δ = 1 := by
  ext
  simp [LSeries, LSeries.term_delta]

end delta


/-!
### Criteria for and consequences of summability of L-series

We relate summability of L-series with bounds on the coefficients in terms of powers of `n`.
-/

/--
lemma `LSeriesSummable.le_const_mul_rpow` / 引理 `LSeriesSummable.le_const_mul_rpow`

English:
lemma LSeriesSummable.le_const_mul_rpow
  given: {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s)
  proof: by
  replace h := h.norm
  use tsum fun n => ‖term f s n‖
  by_contra! ⟨n, hn₀, hn⟩
  have := h.le_tsum n fun _ _ => norm_nonneg _
  rw [norm_term_eq]; rw [if_neg hn₀]; rw [div_le_iff₀ Real.rpow_pos_of_pos (Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn₀) _] at this
  exact (this.trans_lt hn).false.elim

中文:
引理 LSeriesSummable.le_const_mul_rpow
  条件: {f : 自然数 -> Complex} {s : Complex} (h : LSeriesSummable f s)
  证明: by
  replace h := h.norm
  use tsum fun n => ‖term f s n‖
  by_contra! ⟨n, hn₀, hn⟩
  have := h.le_tsum n fun _ _ => norm_nonneg _
  rw [norm_term_eq]; rw [if_neg hn₀]; rw [div_le_iff₀ Real.rpow_pos_of_pos (Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn₀) _] at this
  exact (this.trans_lt hn).false.elim

Depends on / 依赖: Nat.cast_pos.mpr, Nat.pos_of_ne_zero, Real.rpow_pos_of_pos, cast_pos, false.elim, h.le_tsum, h.norm, if_neg, le_tsum, norm_nonneg, norm_term_eq, pos_of_ne_zero, replace, rpow_pos_of_pos, this.trans_lt, trans_lt
-/
lemma LSeriesSummable.le_const_mul_rpow {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s) :
    exists C, forall n != 0, ‖f n‖ <= C * n ^ s.re := by
  replace h := h.norm
  use tsum fun n => ‖term f s n‖
  by_contra! ⟨n, hn₀, hn⟩
  have := h.le_tsum n fun _ _ => norm_nonneg _
  rw [norm_term_eq]; rw [if_neg hn₀]; rw [div_le_iff₀ Real.rpow_pos_of_pos (Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn₀) _] at this
  exact (this.trans_lt hn).false.elim

open Filter in
/--
lemma `LSeriesSummable.isBigO_rpow` / 引理 `LSeriesSummable.isBigO_rpow`

English:
lemma LSeriesSummable.isBigO_rpow
  given: {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s)
  proof: by
  obtain ⟨C, hC⟩ := h.le_const_mul_rpow
refine Asymptotics.IsBigO.of_bound C eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  convert! hC n (Nat.pos_iff_ne_zero.mp hn) using 2
  rw [Real.norm_eq_abs]; rw [Real.abs_rpow_of_nonneg n.cast_nonneg]; rw [abs_of_nonneg n.cast_nonneg]

中文:
引理 LSeriesSummable.isBigO_rpow
  条件: {f : 自然数 -> Complex} {s : Complex} (h : LSeriesSummable f s)
  证明: by
  obtain ⟨C, hC⟩ := h.le_const_mul_rpow
refine Asymptotics.IsBigO.of_bound C eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  convert! hC n (Nat.pos_iff_ne_zero.mp hn) using 2
  rw [Real.norm_eq_abs]; rw [Real.abs_rpow_of_nonneg n.cast_nonneg]; rw [abs_of_nonneg n.cast_nonneg]

Depends on / 依赖: Asymptotics, Asymptotics.IsBigO.of_bound, IsBigO, Nat.pos_iff_ne_zero.mp, Real.abs_rpow_of_nonneg, Real.norm_eq_abs, abs_of_nonneg, abs_rpow_of_nonneg, cast_nonneg, convert, eventually_atTop, eventually_atTop.mpr, h.le_const_mul_rpow, le_const_mul_rpow, n.cast_nonneg, norm_eq_abs, of_bound, pos_iff_ne_zero
-/
lemma LSeriesSummable.isBigO_rpow {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s) :
    f =O[atTop] fun n => (n : Real) ^ s.re := by
  obtain ⟨C, hC⟩ := h.le_const_mul_rpow
refine Asymptotics.IsBigO.of_bound C eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  convert! hC n (Nat.pos_iff_ne_zero.mp hn) using 2
  rw [Real.norm_eq_abs]; rw [Real.abs_rpow_of_nonneg n.cast_nonneg]; rw [abs_of_nonneg n.cast_nonneg]

/--
lemma `LSeriesSummable_of_le_const_mul_rpow` / 引理 `LSeriesSummable_of_le_const_mul_rpow`

English:
lemma LSeriesSummable_of_le_const_mul_rpow
  statement: {f : Nat -> Complex} {x : Real} {s : Complex} (hs : x < s.re)
  proof: by
  obtain ⟨C, hC⟩ := h
have hC₀ : 0 <= C := (norm_nonneg <| f 1).trans by simpa using hC 1 one_ne_zero
  have hsum : Summable fun n : Nat => ‖(C : Complex) / n ^ (s + (1 - x))‖ := by
    simp_rw [div_eq_mul_inv, norm_mul, ← cpow_neg]
    have hsx : -s.re + x - 1 < -1 := by linarith only [hs]
refin

中文:
引理 LSeriesSummable_of_le_const_mul_rpow
  结论: {f : 自然数 -> Complex} {x : 实数} {s : Complex} (hs : x < s.re)
  证明: by
  obtain ⟨C, hC⟩ := h
have hC₀ : 0 <= C := (norm_nonneg <| f 1).trans by simpa using hC 1 one_ne_zero
  have hsum : Summable fun n : Nat => ‖(C : Complex) / n ^ (s + (1 - x))‖ := by
    simp_rw [div_eq_mul_inv, norm_mul, ← cpow_neg]
    have hsx : -s.re + x - 1 < -1 := by linarith only [hs]
refin

Depends on / 依赖: Filter, Filter.eventually_atTop, Summable, Summable.mul_left, Summable.of_norm_bounded_eventually_nat, cpow_neg, div_eq_mul_inv, eventually_atTop, le_of_eq, mul_left, norm_mul, norm_nonneg, norm_norm, of_norm_bounded_eventually_nat, one_ne_zero, s.re, simp_rw
-/
lemma LSeriesSummable_of_le_const_mul_rpow {f : Nat -> Complex} {x : Real} {s : Complex} (hs : x < s.re)
    (h : exists C, forall n != 0, ‖f n‖ <= C * n ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := h
have hC₀ : 0 <= C := (norm_nonneg <| f 1).trans by simpa using hC 1 one_ne_zero
  have hsum : Summable fun n : Nat => ‖(C : Complex) / n ^ (s + (1 - x))‖ := by
    simp_rw [div_eq_mul_inv, norm_mul, ← cpow_neg]
    have hsx : -s.re + x - 1 < -1 := by linarith only [hs]
refine Summable.mul_left _
      Summable.of_norm_bounded_eventually_nat (g := fun n => (n : Real) ^ (-s.re + x - 1)) ?_ ?_
    · simpa
    · simp only [norm_norm, Filter.eventually_atTop]
      refine ⟨1, fun n hn => le_of_eq ?_⟩
      simp only [norm_natCast_cpow_of_pos hn, add_re, sub_re, neg_re, ofReal_re, one_re]
      ring_nf
refine Summable.of_norm hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa only [term_zero, norm_zero] using norm_nonneg _
  have hn' : 0 < (n : Real) ^ s.re := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  simp_rw [term_of_ne_zero hn.ne', norm_div, norm_natCast_cpow_of_pos hn, div_le_iff₀ hn',
    norm_real, Real.norm_of_nonneg hC₀, div_eq_mul_inv, mul_assoc,
← Real.rpow_neg Nat.cast_nonneg _, ← Real.rpow_add Nat.cast_pos.mpr hn]
simpa using hC n Nat.pos_iff_ne_zero.mp hn

open Filter Finset Real Nat in
/--
lemma `LSeriesSummable_of_isBigO_rpow` / 引理 `LSeriesSummable_of_isBigO_rpow`

English:
lemma LSeriesSummable_of_isBigO_rpow
  statement: {f : Nat -> Complex} {x : Real} {s : Complex} (hs : x < s.re)
  proof: by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨m, hm⟩ := eventually_atTop.mp hC
  let C' := max C (max' (insert 0 (image (fun n : Nat => ‖f n‖ / (n : Real) ^ (x - 1)) (range m)))
    (insert_nonempty 0 _))
have hC'₀ : 0 <= C' := (le_max' _ _ (mem_insert.mpr (Or.inl rfl))).trans le_max_

中文:
引理 LSeriesSummable_of_isBigO_rpow
  结论: {f : 自然数 -> Complex} {x : 实数} {s : Complex} (hs : x < s.re)
  证明: by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨m, hm⟩ := eventually_atTop.mp hC
  let C' := max C (max' (insert 0 (image (fun n : Nat => ‖f n‖ / (n : Real) ^ (x - 1)) (range m)))
    (insert_nonempty 0 _))
have hC'₀ : 0 <= C' := (le_max' _ _ (mem_insert.mpr (Or.inl rfl))).trans le_max_

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_iff.mp, LSeriesSummable_of_le_const_mul_rpow, Or.inl, eventually_atTop, eventually_atTop.mp, insert, insert_nonempty, isBigO_iff, le_max, le_max_left, le_max_right, le_or_gt, mem_insert, mem_insert.mpr
-/
lemma LSeriesSummable_of_isBigO_rpow {f : Nat -> Complex} {x : Real} {s : Complex} (hs : x < s.re)
    (h : f =O[atTop] fun n => (n : Real) ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨m, hm⟩ := eventually_atTop.mp hC
  let C' := max C (max' (insert 0 (image (fun n : Nat => ‖f n‖ / (n : Real) ^ (x - 1)) (range m)))
    (insert_nonempty 0 _))
have hC'₀ : 0 <= C' := (le_max' _ _ (mem_insert.mpr (Or.inl rfl))).trans le_max_right ..
  have hCC' : C <= C' := le_max_left ..
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨C', fun n hn₀ => ?_⟩
  rcases le_or_gt m n with hn | hn
  · refine (hm n hn).trans ?_
    have hn₀ : (0 : Real) <= n := cast_nonneg _
    gcongr
    rw [Real.norm_eq_abs]; rw [abs_rpow_of_nonneg hn₀]; rw [abs_of_nonneg hn₀]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn₀
    refine (div_le_iff₀ <| rpow_pos_of_pos (cast_pos.mpr hn') _).mp ?_
refine (le_max' _ _ <| mem_insert_of_mem ?_).trans le_max_right ..
    exact mem_image.mpr ⟨n, mem_range.mpr hn, rfl⟩

/--
theorem `LSeriesSummable_of_bounded_of_one_lt_re` / 定理 `LSeriesSummable_of_bounded_of_one_lt_re`

English:
theorem LSeriesSummable_of_bounded_of_one_lt_re
  statement: {f : Nat -> Complex} {m : Real}
  proof: LSeriesSummable_of_le_const_mul_rpow hs ⟨m, fun n hn => by simp [h n hn]⟩

中文:
定理 LSeriesSummable_of_bounded_of_one_lt_re
  结论: {f : 自然数 -> Complex} {m : 实数}
  证明: LSeriesSummable_of_le_const_mul_rpow hs ⟨m, fun n hn => by simp [h n hn]⟩

Depends on / 依赖: LSeriesSummable_of_le_const_mul_rpow
-/
theorem LSeriesSummable_of_bounded_of_one_lt_re {f : Nat -> Complex} {m : Real}
    (h : forall n != 0, ‖f n‖ <= m) {s : Complex} (hs : 1 < s.re) :
    LSeriesSummable f s :=
  LSeriesSummable_of_le_const_mul_rpow hs ⟨m, fun n hn => by simp [h n hn]⟩

/--
theorem `LSeriesSummable_of_bounded_of_one_lt_real` / 定理 `LSeriesSummable_of_bounded_of_one_lt_real`

English:
theorem LSeriesSummable_of_bounded_of_one_lt_real
  statement: {f : Nat -> Complex} {m : Real}
  proof: LSeriesSummable_of_bounded_of_one_lt_re h by simp [hs]

中文:
定理 LSeriesSummable_of_bounded_of_one_lt_real
  结论: {f : 自然数 -> Complex} {m : 实数}
  证明: LSeriesSummable_of_bounded_of_one_lt_re h by simp [hs]

Depends on / 依赖: LSeriesSummable_of_bounded_of_one_lt_re
-/
theorem LSeriesSummable_of_bounded_of_one_lt_real {f : Nat -> Complex} {m : Real}
    (h : forall n != 0, ‖f n‖ <= m) {s : Real} (hs : 1 < s) :
    LSeriesSummable f s :=
LSeriesSummable_of_bounded_of_one_lt_re h by simp [hs]
