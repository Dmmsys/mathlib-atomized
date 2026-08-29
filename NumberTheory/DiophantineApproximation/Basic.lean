/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.Basic

/-!
# Diophantine Approximation

The first part of this file gives proofs of various versions of
**Dirichlet's approximation theorem** and its important consequence that when $\xi$ is an
irrational real number, then there are infinitely many rationals $x/y$ (in lowest terms)
such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{y^2} \,.$$
The proof is based on the pigeonhole principle.

The second part of the file gives a proof of **Legendre's Theorem** on rational approximation,
which states that if $\xi$ is a real number and $x/y$ is a rational number such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{2y^2} \,,$$
then $x/y$ must be a convergent of the continued fraction expansion of $\xi$.

## Main statements

The main results are three variants of Dirichlet's approximation theorem:
* `Real.exists_int_int_abs_mul_sub_le`, which states that for all real `ξ` and natural `0 < n`,
  there are integers `j` and `k` with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`,
* `Real.exists_nat_abs_mul_sub_round_le`, which replaces `j` by `round(k*ξ)` and uses
  a natural number `k`,
* `Real.exists_rat_abs_sub_le_and_den_le`, which says that there is a rational number `q`
  satisfying `|ξ - q| ≤ 1/((n+1)*q.den)` and `q.den ≤ n`,

and
* `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, which states that
  for irrational `ξ`, the set `{q : ℚ | |ξ - q| < 1/q.den^2}` is infinite.

We also show a converse,
* `Rat.finite_rat_abs_sub_lt_one_div_den_sq`, which states that the set above is finite
  when `ξ` is a rational number.

Both statements are combined to give an equivalence,
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`.

There are two versions of Legendre's Theorem. One, `Real.exists_rat_eq_convergent`, uses
`Real.convergent`, a simple recursive definition of the convergents that is also defined
in this file, whereas the other, `Real.exists_convs_eq_rat` defined in the file
`Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean`, uses
`GenContFract.convs` of `GenContFract.of ξ`.

## Implementation notes

We use the namespace `Real` for the results on real numbers and `Rat` for the results
on rational numbers. We introduce a secondary namespace `Real.ContfracLegendre`
to separate off a definition and some technical auxiliary lemmas used in the proof
of Legendre's Theorem. For remarks on the proof of Legendre's Theorem, see below.

## References

<https://en.wikipedia.org/wiki/Dirichlet%27s_approximation_theorem>
<https://de.wikipedia.org/wiki/Kettenbruch> (The German Wikipedia page on continued
fractions is much more extensive than the English one.)

## Tags

Diophantine approximation, Dirichlet's approximation theorem, continued fraction
-/

@[expose] public section


namespace Real

section Dirichlet

/-!
### Dirichlet's approximation theorem

We show that for any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.den ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.den)`.
-/


open Finset Int

/--
theorem `exists_int_int_abs_mul_sub_le` / 定理 `exists_int_int_abs_mul_sub_le`

English:
theorem exists_int_int_abs_mul_sub_le
  given: (ξ : Real) {n : Nat} (n_pos : 0 < n)
  proof: by
  let f : Int -> Int := fun m => ⌊fract (ξ * m) * (n + 1)⌋
  have hn : 0 < (n : Real) + 1 := mod_cast Nat.succ_pos _
have hfu := fun m : Int => mul_lt_of_lt_one_left hn fract_lt_one (ξ * ↑m)
  conv in |_| <= _ => rw [mul_comm, le_div_iff₀ hn, ← abs_of_pos hn, ← abs_mul]
  let D := Icc (0 : Int) n
  by_cases! H : exists m in D, f m = n
  · obtain ⟨m, hm, hf⟩ := H
    have hf' : ((n : Int) : Real) <= fract (ξ * m) * (n + 1) := hf ▸ floor_le (fract (ξ * m) * (n + 1))
    have hm₀ : 0 < m := by
      have hf₀ : f 0 = 0 := by
        simp only [f, cast_zero, mul_zero, fract_zero, zero_mul, floor_zero]
      refine Ne.lt_of_le (fun h => n_pos.ne ?_) (mem_Icc.mp hm).1
      exact mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n)
    refine ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, ?_⟩
    rw [cast_add]; rw [← sub_sub]; rw [sub_mul]; rw [cast_one]; rw [one_mul]; rw [abs_le]
    refine
⟨le_sub_iff_add_le.mpr ?_, sub_le_iff_le_add.mpr le_of_lt (hfu m).trans lt_one_add _⟩
    simpa only [neg_add_cancel_comm_assoc] using! hf'
  · have hD : #(Ico (0 : Int) n) < #D := by rw [card_Icc, card_Ico]; exact lt_add_one n
    have hfu' : forall m, f m <= n := fun m => lt_add_one_iff.mp (floor_lt.mpr (mod_cast hfu m))
    have hwd : forall m : Int, m in D -> f m in Ico (0 : Int) n := fun x hx =>
      mem_Ico.mpr
        ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le), Ne.lt_of_le (H x hx) (hfu' x)⟩
    obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ : exists x in D, exists y in D, x < y ∧ f x = f y := by
      obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd
      rcases lt_trichotomy x y with (h | h | h)
      exacts [⟨x, hx, y, hy, h, hxy⟩, False.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩]
    refine
      ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
sub_le_iff_le_add.mpr le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, ?_⟩
    convert_to! |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| <= 1
    · congr; push_cast; simp only [fract]; ring
    exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le

中文:
定理 存在_int_int_abs_mul_sub_le
  条件: (ξ : 实数) {n : 自然数} (n_pos : 0 < n)
  证明: by
  let f : Int -> Int := fun m => ⌊fract (ξ * m) * (n + 1)⌋
  have hn : 0 < (n : Real) + 1 := mod_cast Nat.succ_pos _
have hfu := fun m : Int => mul_lt_of_lt_one_left hn fract_lt_one (ξ * ↑m)
  conv in |_| <= _ => rw [mul_comm, le_div_iff₀ hn, ← abs_of_pos hn, ← abs_mul]
  let D := Icc (0 : Int) n
  by_cases! H : exists m in D, f m = n
  · obtain ⟨m, hm, hf⟩ := H
    have hf' : ((n : Int) : Real) <= fract (ξ * m) * (n + 1) := hf ▸ floor_le (fract (ξ * m) * (n + 1))
    have hm₀ : 0 < m := by
      have hf₀ : f 0 = 0 := by
        simp only [f, cast_zero, mul_zero, fract_zero, zero_mul, floor_zero]
      refine Ne.lt_of_le (fun h => n_pos.ne ?_) (mem_Icc.mp hm).1
      exact mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n)
    refine ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, ?_⟩
    rw [cast_add]; rw [← sub_sub]; rw [sub_mul]; rw [cast_one]; rw [one_mul]; rw [abs_le]
    refine
⟨le_sub_iff_add_le.mpr ?_, sub_le_iff_le_add.mpr le_of_lt (hfu m).trans lt_one_add _⟩
    simpa only [neg_add_cancel_comm_assoc] using! hf'
  · have hD : #(Ico (0 : Int) n) < #D := by rw [card_Icc, card_Ico]; exact lt_add_one n
    have hfu' : forall m, f m <= n := fun m => lt_add_one_iff.mp (floor_lt.mpr (mod_cast hfu m))
    have hwd : forall m : Int, m in D -> f m in Ico (0 : Int) n := fun x hx =>
      mem_Ico.mpr
        ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le), Ne.lt_of_le (H x hx) (hfu' x)⟩
    obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ : exists x in D, exists y in D, x < y ∧ f x = f y := by
      obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd
      rcases lt_trichotomy x y with (h | h | h)
      exacts [⟨x, hx, y, hy, h, hxy⟩, False.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩]
    refine
      ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
sub_le_iff_le_add.mpr le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, ?_⟩
    convert_to! |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| <= 1
    · congr; push_cast; simp only [fract]; ring
    exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le

Depends on / 依赖: Nat.succ_pos, abs_mul, abs_of_pos, floor_le, fract_lt_one, mod_cast, mul_comm, mul_lt_of_lt_one_left, succ_pos
-/
theorem exists_int_int_abs_mul_sub_le (ξ : Real) {n : Nat} (n_pos : 0 < n) :
    exists j k : Int, 0 < k ∧ k <= n ∧ |↑k * ξ - j| <= 1 / (n + 1) := by
  let f : Int -> Int := fun m => ⌊fract (ξ * m) * (n + 1)⌋
  have hn : 0 < (n : Real) + 1 := mod_cast Nat.succ_pos _
have hfu := fun m : Int => mul_lt_of_lt_one_left hn fract_lt_one (ξ * ↑m)
  conv in |_| <= _ => rw [mul_comm, le_div_iff₀ hn, ← abs_of_pos hn, ← abs_mul]
  let D := Icc (0 : Int) n
  by_cases! H : exists m in D, f m = n
  · obtain ⟨m, hm, hf⟩ := H
    have hf' : ((n : Int) : Real) <= fract (ξ * m) * (n + 1) := hf ▸ floor_le (fract (ξ * m) * (n + 1))
    have hm₀ : 0 < m := by
      have hf₀ : f 0 = 0 := by
        simp only [f, cast_zero, mul_zero, fract_zero, zero_mul, floor_zero]
      refine Ne.lt_of_le (fun h => n_pos.ne ?_) (mem_Icc.mp hm).1
      exact mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n)
    refine ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, ?_⟩
    rw [cast_add]; rw [← sub_sub]; rw [sub_mul]; rw [cast_one]; rw [one_mul]; rw [abs_le]
    refine
⟨le_sub_iff_add_le.mpr ?_, sub_le_iff_le_add.mpr le_of_lt (hfu m).trans lt_one_add _⟩
    simpa only [neg_add_cancel_comm_assoc] using! hf'
  · have hD : #(Ico (0 : Int) n) < #D := by rw [card_Icc, card_Ico]; exact lt_add_one n
    have hfu' : forall m, f m <= n := fun m => lt_add_one_iff.mp (floor_lt.mpr (mod_cast hfu m))
    have hwd : forall m : Int, m in D -> f m in Ico (0 : Int) n := fun x hx =>
      mem_Ico.mpr
        ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le), Ne.lt_of_le (H x hx) (hfu' x)⟩
    obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ : exists x in D, exists y in D, x < y ∧ f x = f y := by
      obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd
      rcases lt_trichotomy x y with (h | h | h)
      exacts [⟨x, hx, y, hy, h, hxy⟩, False.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩]
    refine
      ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
sub_le_iff_le_add.mpr le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, ?_⟩
    convert_to! |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| <= 1
    · congr; push_cast; simp only [fract]; ring
    exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le

/--
theorem `exists_nat_abs_mul_sub_round_le` / 定理 `exists_nat_abs_mul_sub_round_le`

English:
theorem exists_nat_abs_mul_sub_round_le
  given: (ξ : Real) {n : Nat} (n_pos : 0 < n)
  proof: by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk := toNat_of_nonneg hk₀.le
  rw [← hk] at hk₀ hk₁ h
  exact ⟨k.toNat, natCast_pos.mp hk₀, Nat.cast_le.mp hk₁, (round_le (↑k.toNat * ξ) j).trans h⟩

中文:
定理 存在_nat_abs_mul_sub_round_le
  条件: (ξ : 实数) {n : 自然数} (n_pos : 0 < n)
  证明: by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk := toNat_of_nonneg hk₀.le
  rw [← hk] at hk₀ hk₁ h
  exact ⟨k.toNat, natCast_pos.mp hk₀, Nat.cast_le.mp hk₁, (round_le (↑k.toNat * ξ) j).trans h⟩

Depends on / 依赖: Nat.cast_le.mp, cast_le, exists_int_int_abs_mul_sub_le, k.toNat, n_pos, natCast_pos, natCast_pos.mp, round_le, toNat_of_nonneg
-/
theorem exists_nat_abs_mul_sub_round_le (ξ : Real) {n : Nat} (n_pos : 0 < n) :
    exists k : Nat, 0 < k ∧ k <= n ∧ |↑k * ξ - round (↑k * ξ)| <= 1 / (n + 1) := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk := toNat_of_nonneg hk₀.le
  rw [← hk] at hk₀ hk₁ h
  exact ⟨k.toNat, natCast_pos.mp hk₀, Nat.cast_le.mp hk₁, (round_le (↑k.toNat * ξ) j).trans h⟩

/--
theorem `exists_rat_abs_sub_le_and_den_le` / 定理 `exists_rat_abs_sub_le_and_den_le`

English:
theorem exists_rat_abs_sub_le_and_den_le
  given: (ξ : Real) {n : Nat} (n_pos : 0 < n)
  proof: by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk₀' : (0 : Real) < k := Int.cast_pos.mpr hk₀
  have hden : ((j / k : Rat).den : Int) <= k := by
    convert! le_of_dvd hk₀ (Rat.den_dvd j k)
    exact Rat.intCast_div_eq_divInt _ _
  refine ⟨j / k, ?_, Nat.cast_le.mp (hden.trans hk₁)⟩
  rw [← div_div]; rw [le_div_iff₀ (Nat.cast_pos.mpr <| Rat.pos _ : (0 : Real) < _)]
  refine (mul_le_mul_of_nonneg_left (Int.cast_le.mpr hden : _ <= (k : Real)) (abs_nonneg _)).trans ?_
  rwa [← abs_of_pos hk₀', Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, ← abs_mul, sub_mul,
    div_mul_cancel₀ _ hk₀'.ne', mul_comm]

中文:
定理 存在_rat_abs_sub_le_and_den_le
  条件: (ξ : 实数) {n : 自然数} (n_pos : 0 < n)
  证明: by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk₀' : (0 : Real) < k := Int.cast_pos.mpr hk₀
  have hden : ((j / k : Rat).den : Int) <= k := by
    convert! le_of_dvd hk₀ (Rat.den_dvd j k)
    exact Rat.intCast_div_eq_divInt _ _
  refine ⟨j / k, ?_, Nat.cast_le.mp (hden.trans hk₁)⟩
  rw [← div_div]; rw [le_div_iff₀ (Nat.cast_pos.mpr <| Rat.pos _ : (0 : Real) < _)]
  refine (mul_le_mul_of_nonneg_left (Int.cast_le.mpr hden : _ <= (k : Real)) (abs_nonneg _)).trans ?_
  rwa [← abs_of_pos hk₀', Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, ← abs_mul, sub_mul,
    div_mul_cancel₀ _ hk₀'.ne', mul_comm]

Depends on / 依赖: Int.cast_le.mpr, Int.cast_pos.mpr, Nat.cast_le.mp, Nat.cast_pos.mpr, Rat.den_dvd, Rat.intCast_div_eq_divInt, Rat.pos, abs_nonneg, abs_of_pos, cast_le, cast_pos, convert, den_dvd, div_div, exists_int_int_abs_mul_sub_le, hden.trans, intCast_div_eq_divInt, le_of_dvd, mul_le_mul_of_nonneg_left, n_pos
-/
theorem exists_rat_abs_sub_le_and_den_le (ξ : Real) {n : Nat} (n_pos : 0 < n) :
    exists q : Rat, |ξ - q| <= 1 / ((n + 1) * q.den) ∧ q.den <= n := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk₀' : (0 : Real) < k := Int.cast_pos.mpr hk₀
  have hden : ((j / k : Rat).den : Int) <= k := by
    convert! le_of_dvd hk₀ (Rat.den_dvd j k)
    exact Rat.intCast_div_eq_divInt _ _
  refine ⟨j / k, ?_, Nat.cast_le.mp (hden.trans hk₁)⟩
  rw [← div_div]; rw [le_div_iff₀ (Nat.cast_pos.mpr <| Rat.pos _ : (0 : Real) < _)]
  refine (mul_le_mul_of_nonneg_left (Int.cast_le.mpr hden : _ <= (k : Real)) (abs_nonneg _)).trans ?_
  rwa [← abs_of_pos hk₀', Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, ← abs_mul, sub_mul,
    div_mul_cancel₀ _ hk₀'.ne', mul_comm]

end Dirichlet

section RatApprox

/-!
### Infinitely many good approximations to irrational numbers

We show that an irrational real number `ξ` has infinitely many "good rational approximations",
i.e., fractions `x/y` in lowest terms such that `|ξ - x/y| < 1/y^2`.
-/


open Set

/--
theorem `exists_rat_abs_sub_lt_and_lt_of_irrational` / 定理 `exists_rat_abs_sub_lt_and_lt_of_irrational`

English:
theorem exists_rat_abs_sub_lt_and_lt_of_irrational
  given: {ξ : Real} (hξ : Irrational ξ) (q : Rat)
  proof: by
  have h := abs_pos.mpr (sub_ne_zero.mpr <| Irrational.ne_rat hξ q)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|)
  have m_pos : (0 : Real) < m := (one_div_pos.mpr h).trans hm
  obtain ⟨q', hbd, hden⟩ := exists_rat_abs_sub_le_and_den_le ξ (Nat.cast_pos.mp m_pos)
  have den_pos : (0 : Real) < q'.den := Nat.cast_pos.mpr q'.pos
  have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos
  refine
    ⟨q', lt_of_le_of_lt hbd ?_,
lt_of_le_of_lt hbd
(one_div_lt md_pos h).mpr
hm.trans
lt_of_lt_of_le (lt_add_one _)
(le_mul_iff_one_le_right <| add_pos m_pos zero_lt_one).mpr
                mod_cast (q'.pos : 1 <= q'.den)⟩
  rw [sq]; rw [one_div_lt_one_div md_pos (mul_pos den_pos den_pos)]; rw [mul_lt_mul_iff_left₀ den_pos]
  exact lt_add_of_le_of_pos (Nat.cast_le.mpr hden) zero_lt_one

中文:
定理 存在_rat_abs_sub_lt_and_lt_of_irrational
  条件: {ξ : 实数} (hξ : Irrational ξ) (q : 有理数)
  证明: by
  have h := abs_pos.mpr (sub_ne_zero.mpr <| Irrational.ne_rat hξ q)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|)
  have m_pos : (0 : Real) < m := (one_div_pos.mpr h).trans hm
  obtain ⟨q', hbd, hden⟩ := exists_rat_abs_sub_le_and_den_le ξ (Nat.cast_pos.mp m_pos)
  have den_pos : (0 : Real) < q'.den := Nat.cast_pos.mpr q'.pos
  have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos
  refine
    ⟨q', lt_of_le_of_lt hbd ?_,
lt_of_le_of_lt hbd
(one_div_lt md_pos h).mpr
hm.trans
lt_of_lt_of_le (lt_add_one _)
(le_mul_iff_one_le_right <| add_pos m_pos zero_lt_one).mpr
                mod_cast (q'.pos : 1 <= q'.den)⟩
  rw [sq]; rw [one_div_lt_one_div md_pos (mul_pos den_pos den_pos)]; rw [mul_lt_mul_iff_left₀ den_pos]
  exact lt_add_of_le_of_pos (Nat.cast_le.mpr hden) zero_lt_one

Depends on / 依赖: Irrational, Irrational.ne_rat, Nat.cast_pos.mp, Nat.cast_pos.mpr, abs_pos, abs_pos.mpr, add_pos, cast_pos, den_pos, exists_nat_gt, exists_rat_abs_sub_le_and_den_le, hm.trans, lt_add_one, lt_of_le_of_lt, lt_of_lt_of_le, m_pos, md_pos, mul_pos, ne_rat, one_div_lt
-/
theorem exists_rat_abs_sub_lt_and_lt_of_irrational {ξ : Real} (hξ : Irrational ξ) (q : Rat) :
    exists q' : Rat, |ξ - q'| < 1 / (q'.den : Real) ^ 2 ∧ |ξ - q'| < |ξ - q| := by
  have h := abs_pos.mpr (sub_ne_zero.mpr <| Irrational.ne_rat hξ q)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|)
  have m_pos : (0 : Real) < m := (one_div_pos.mpr h).trans hm
  obtain ⟨q', hbd, hden⟩ := exists_rat_abs_sub_le_and_den_le ξ (Nat.cast_pos.mp m_pos)
  have den_pos : (0 : Real) < q'.den := Nat.cast_pos.mpr q'.pos
  have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos
  refine
    ⟨q', lt_of_le_of_lt hbd ?_,
lt_of_le_of_lt hbd
(one_div_lt md_pos h).mpr
hm.trans
lt_of_lt_of_le (lt_add_one _)
(le_mul_iff_one_le_right <| add_pos m_pos zero_lt_one).mpr
                mod_cast (q'.pos : 1 <= q'.den)⟩
  rw [sq]; rw [one_div_lt_one_div md_pos (mul_pos den_pos den_pos)]; rw [mul_lt_mul_iff_left₀ den_pos]
  exact lt_add_of_le_of_pos (Nat.cast_le.mpr hden) zero_lt_one

/--
theorem `infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` / 定理 `infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`

English:
theorem infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational
  given: {ξ : Real} (hξ : Irrational ξ)
  proof: by
  refine Or.resolve_left (Set.finite_or_infinite _) fun h => ?_
  obtain ⟨q, _, hq⟩ :=
    exists_min_image {q : Rat | |ξ - q| < 1 / (q.den : Real) ^ 2} (fun q => |ξ - q|) h
      ⟨⌊ξ⌋, by simp [abs_of_nonneg, Int.fract_lt_one]⟩
  obtain ⟨q', hmem, hbetter⟩ := exists_rat_abs_sub_lt_and_lt_of_irrational hξ q
  exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter)

中文:
定理 infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational
  条件: {ξ : 实数} (hξ : Irrational ξ)
  证明: by
  refine Or.resolve_left (Set.finite_or_infinite _) fun h => ?_
  obtain ⟨q, _, hq⟩ :=
    exists_min_image {q : Rat | |ξ - q| < 1 / (q.den : Real) ^ 2} (fun q => |ξ - q|) h
      ⟨⌊ξ⌋, by simp [abs_of_nonneg, Int.fract_lt_one]⟩
  obtain ⟨q', hmem, hbetter⟩ := exists_rat_abs_sub_lt_and_lt_of_irrational hξ q
  exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter)

Depends on / 依赖: Int.fract_lt_one, Or.resolve_left, Set.finite_or_infinite, abs_of_nonneg, exists_min_image, exists_rat_abs_sub_lt_and_lt_of_irrational, finite_or_infinite, fract_lt_one, hbetter, lt_irrefl, lt_of_le_of_lt, q.den, resolve_left
-/
theorem infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational {ξ : Real} (hξ : Irrational ξ) :
    {q : Rat | |ξ - q| < 1 / (q.den : Real) ^ 2}.Infinite := by
  refine Or.resolve_left (Set.finite_or_infinite _) fun h => ?_
  obtain ⟨q, _, hq⟩ :=
    exists_min_image {q : Rat | |ξ - q| < 1 / (q.den : Real) ^ 2} (fun q => |ξ - q|) h
      ⟨⌊ξ⌋, by simp [abs_of_nonneg, Int.fract_lt_one]⟩
  obtain ⟨q', hmem, hbetter⟩ := exists_rat_abs_sub_lt_and_lt_of_irrational hξ q
  exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter)

end RatApprox

end Real

namespace Rat

/-!
### Finitely many good approximations to rational numbers

We now show that a rational number `ξ` has only finitely many good rational
approximations.
-/


open Set

/--
theorem `den_le_and_le_num_le_of_sub_lt_one_div_den_sq` / 定理 `den_le_and_le_num_le_of_sub_lt_one_div_den_sq`

English:
theorem den_le_and_le_num_le_of_sub_lt_one_div_den_sq
  statement: {ξ q : Rat}
  proof: by
  have hq₀ : (0 : Rat) < q.den := Nat.cast_pos.mpr q.pos
  replace h : |ξ * q.den - q.num| < 1 / q.den := by
    rw [← mul_lt_mul_iff_left₀ hq₀] at h
    conv_lhs at h => rw [← abs_of_pos hq₀, ← abs_mul, sub_mul, mul_den_eq_num]
    rwa [sq, div_mul, mul_div_cancel_left₀ _ hq₀.ne'] at h
  constructor
  · rcases eq_or_ne ξ q with (rfl | H)
    · exact le_rfl
    · have hξ₀ : (0 : Rat) < ξ.den := Nat.cast_pos.mpr ξ.pos
      rw [← Rat.num_div_den ξ]; rw [div_mul_eq_mul_div]; rw [div_sub' hξ₀.ne']; rw [abs_div]; rw [abs_of_pos hξ₀]; rw [div_lt_iff₀ hξ₀]; rw [div_mul_comm]; rw [mul_one] at h
      refine Nat.cast_le.mp ((one_lt_div hq₀).mp <| lt_of_le_of_lt ?_ h).le
      norm_cast
      rw [mul_comm _ q.num]
      exact Int.one_le_abs (sub_ne_zero_of_ne <| mt Rat.eq_iff_mul_eq_mul.mpr H)
  · obtain ⟨h₁, h₂⟩ :=
      abs_sub_lt_iff.mp
        (h.trans_le <|
(one_div_le zero_lt_one hq₀).mp (@one_div_one Rat _).symm ▸ Nat.cast_le.mpr q.pos)
    rw [sub_lt_iff_lt_add]; rw [add_comm] at h₁ h₂
    rw [← sub_lt_iff_lt_add] at h₂
    norm_cast at h₁ h₂
    exact
      ⟨sub_le_iff_le_add.mpr (Int.ceil_le.mpr h₁.le), sub_le_iff_le_add.mp (Int.le_floor.mpr h₂.le)⟩

中文:
定理 den_le_and_le_num_le_of_sub_lt_one_div_den_sq
  结论: {ξ q : 有理数}
  证明: by
  have hq₀ : (0 : Rat) < q.den := Nat.cast_pos.mpr q.pos
  replace h : |ξ * q.den - q.num| < 1 / q.den := by
    rw [← mul_lt_mul_iff_left₀ hq₀] at h
    conv_lhs at h => rw [← abs_of_pos hq₀, ← abs_mul, sub_mul, mul_den_eq_num]
    rwa [sq, div_mul, mul_div_cancel_left₀ _ hq₀.ne'] at h
  constructor
  · rcases eq_or_ne ξ q with (rfl | H)
    · exact le_rfl
    · have hξ₀ : (0 : Rat) < ξ.den := Nat.cast_pos.mpr ξ.pos
      rw [← Rat.num_div_den ξ]; rw [div_mul_eq_mul_div]; rw [div_sub' hξ₀.ne']; rw [abs_div]; rw [abs_of_pos hξ₀]; rw [div_lt_iff₀ hξ₀]; rw [div_mul_comm]; rw [mul_one] at h
      refine Nat.cast_le.mp ((one_lt_div hq₀).mp <| lt_of_le_of_lt ?_ h).le
      norm_cast
      rw [mul_comm _ q.num]
      exact Int.one_le_abs (sub_ne_zero_of_ne <| mt Rat.eq_iff_mul_eq_mul.mpr H)
  · obtain ⟨h₁, h₂⟩ :=
      abs_sub_lt_iff.mp
        (h.trans_le <|
(one_div_le zero_lt_one hq₀).mp (@one_div_one Rat _).symm ▸ Nat.cast_le.mpr q.pos)
    rw [sub_lt_iff_lt_add]; rw [add_comm] at h₁ h₂
    rw [← sub_lt_iff_lt_add] at h₂
    norm_cast at h₁ h₂
    exact
      ⟨sub_le_iff_le_add.mpr (Int.ceil_le.mpr h₁.le), sub_le_iff_le_add.mp (Int.le_floor.mpr h₂.le)⟩

Depends on / 依赖: Nat.cast_pos.mpr, Rat.num_div_den, abs_div, abs_mul, abs_of_pos, cast_pos, conv_lhs, div_mul, div_mul_eq_mul_div, div_sub, eq_or_ne, le_rfl, mul_den_eq_num, num_div_den, q.den, q.num, q.pos, replace, sub_mul
-/
theorem den_le_and_le_num_le_of_sub_lt_one_div_den_sq {ξ q : Rat}
    (h : |ξ - q| < 1 / (q.den : Rat) ^ 2) :
    q.den <= ξ.den ∧ ⌈ξ * q.den⌉ - 1 <= q.num ∧ q.num <= ⌊ξ * q.den⌋ + 1 := by
  have hq₀ : (0 : Rat) < q.den := Nat.cast_pos.mpr q.pos
  replace h : |ξ * q.den - q.num| < 1 / q.den := by
    rw [← mul_lt_mul_iff_left₀ hq₀] at h
    conv_lhs at h => rw [← abs_of_pos hq₀, ← abs_mul, sub_mul, mul_den_eq_num]
    rwa [sq, div_mul, mul_div_cancel_left₀ _ hq₀.ne'] at h
  constructor
  · rcases eq_or_ne ξ q with (rfl | H)
    · exact le_rfl
    · have hξ₀ : (0 : Rat) < ξ.den := Nat.cast_pos.mpr ξ.pos
      rw [← Rat.num_div_den ξ]; rw [div_mul_eq_mul_div]; rw [div_sub' hξ₀.ne']; rw [abs_div]; rw [abs_of_pos hξ₀]; rw [div_lt_iff₀ hξ₀]; rw [div_mul_comm]; rw [mul_one] at h
      refine Nat.cast_le.mp ((one_lt_div hq₀).mp <| lt_of_le_of_lt ?_ h).le
      norm_cast
      rw [mul_comm _ q.num]
      exact Int.one_le_abs (sub_ne_zero_of_ne <| mt Rat.eq_iff_mul_eq_mul.mpr H)
  · obtain ⟨h₁, h₂⟩ :=
      abs_sub_lt_iff.mp
        (h.trans_le <|
(one_div_le zero_lt_one hq₀).mp (@one_div_one Rat _).symm ▸ Nat.cast_le.mpr q.pos)
    rw [sub_lt_iff_lt_add]; rw [add_comm] at h₁ h₂
    rw [← sub_lt_iff_lt_add] at h₂
    norm_cast at h₁ h₂
    exact
      ⟨sub_le_iff_le_add.mpr (Int.ceil_le.mpr h₁.le), sub_le_iff_le_add.mp (Int.le_floor.mpr h₂.le)⟩

/--
theorem `finite_rat_abs_sub_lt_one_div_den_sq` / 定理 `finite_rat_abs_sub_lt_one_div_den_sq`

English:
theorem finite_rat_abs_sub_lt_one_div_den_sq
  given: (ξ : Rat)
  proof: by
  let f : Rat -> Int × Nat := fun q => (q.num, q.den)
  set s := {q : Rat | |ξ - q| < 1 / (q.den : Rat) ^ 2}
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk_inj] at hab
    rw [← Rat.num_div_den a]; rw [← Rat.num_div_den b]; rw [hab.1]; rw [hab.2]
  have H : f '' s subseteq ⋃ (y : Nat) (_ : y in Ioc 0 ξ.den), Icc (⌈ξ * y⌉ - 1) (⌊ξ * y⌋ + 1) ×ˢ {y} := by
    intro xy hxy
    simp only [mem_image] at hxy
    obtain ⟨q, hq₁, hq₂⟩ := hxy
    obtain ⟨hd, hn⟩ := den_le_and_le_num_le_of_sub_lt_one_div_den_sq hq₁
    simp_rw [mem_iUnion]
    refine ⟨q.den, Set.mem_Ioc.mpr ⟨q.pos, hd⟩, ?_⟩
    simp only [prod_singleton, mem_image, mem_Icc]
    exact ⟨q.num, hn, hq₂⟩
  refine (Finite.subset ?_ H).of_finite_image hinj.injOn
  exact Finite.biUnion (finite_Ioc _ _) fun x _ => Finite.prod (finite_Icc _ _) (finite_singleton _)

中文:
定理 finite_rat_abs_sub_lt_one_div_den_sq
  条件: (ξ : 有理数)
  证明: by
  let f : Rat -> Int × Nat := fun q => (q.num, q.den)
  set s := {q : Rat | |ξ - q| < 1 / (q.den : Rat) ^ 2}
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk_inj] at hab
    rw [← Rat.num_div_den a]; rw [← Rat.num_div_den b]; rw [hab.1]; rw [hab.2]
  have H : f '' s subseteq ⋃ (y : Nat) (_ : y in Ioc 0 ξ.den), Icc (⌈ξ * y⌉ - 1) (⌊ξ * y⌋ + 1) ×ˢ {y} := by
    intro xy hxy
    simp only [mem_image] at hxy
    obtain ⟨q, hq₁, hq₂⟩ := hxy
    obtain ⟨hd, hn⟩ := den_le_and_le_num_le_of_sub_lt_one_div_den_sq hq₁
    simp_rw [mem_iUnion]
    refine ⟨q.den, Set.mem_Ioc.mpr ⟨q.pos, hd⟩, ?_⟩
    simp only [prod_singleton, mem_image, mem_Icc]
    exact ⟨q.num, hn, hq₂⟩
  refine (Finite.subset ?_ H).of_finite_image hinj.injOn
  exact Finite.biUnion (finite_Ioc _ _) fun x _ => Finite.prod (finite_Icc _ _) (finite_singleton _)

Depends on / 依赖: Function, Function.Injective, Injective, Prod.mk_inj, Rat.num_div_den, den_le_and_le_num_le_of_sub_lt_one_, mem_image, mk_inj, num_div_den, q.den, q.num, subseteq
-/
theorem finite_rat_abs_sub_lt_one_div_den_sq (ξ : Rat) :
    {q : Rat | |ξ - q| < 1 / (q.den : Rat) ^ 2}.Finite := by
  let f : Rat -> Int × Nat := fun q => (q.num, q.den)
  set s := {q : Rat | |ξ - q| < 1 / (q.den : Rat) ^ 2}
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk_inj] at hab
    rw [← Rat.num_div_den a]; rw [← Rat.num_div_den b]; rw [hab.1]; rw [hab.2]
  have H : f '' s subseteq ⋃ (y : Nat) (_ : y in Ioc 0 ξ.den), Icc (⌈ξ * y⌉ - 1) (⌊ξ * y⌋ + 1) ×ˢ {y} := by
    intro xy hxy
    simp only [mem_image] at hxy
    obtain ⟨q, hq₁, hq₂⟩ := hxy
    obtain ⟨hd, hn⟩ := den_le_and_le_num_le_of_sub_lt_one_div_den_sq hq₁
    simp_rw [mem_iUnion]
    refine ⟨q.den, Set.mem_Ioc.mpr ⟨q.pos, hd⟩, ?_⟩
    simp only [prod_singleton, mem_image, mem_Icc]
    exact ⟨q.num, hn, hq₂⟩
  refine (Finite.subset ?_ H).of_finite_image hinj.injOn
  exact Finite.biUnion (finite_Ioc _ _) fun x _ => Finite.prod (finite_Icc _ _) (finite_singleton _)

end Rat

/--
theorem `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational` / 定理 `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`

English:
theorem Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational
  given: (ξ : Real)
  proof: by
  refine
    ⟨fun h => (irrational_iff_ne_rational ξ).mpr fun a b _ => ?_,
      Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational⟩
  contrapose! h
  convert! Rat.finite_rat_abs_sub_lt_one_div_den_sq ((a : Rat) / b) with q
  rw [h]; rw [(by (push_cast; rfl) : (1 : Real) / (q.den : Real) ^ 2 = (1 / (q.den : Rat) ^ 2 : Rat))]
  norm_cast

中文:
定理 实数.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational
  条件: (ξ : 实数)
  证明: by
  refine
    ⟨fun h => (irrational_iff_ne_rational ξ).mpr fun a b _ => ?_,
      Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational⟩
  contrapose! h
  convert! Rat.finite_rat_abs_sub_lt_one_div_den_sq ((a : Rat) / b) with q
  rw [h]; rw [(by (push_cast; rfl) : (1 : Real) / (q.den : Real) ^ 2 = (1 / (q.den : Rat) ^ 2 : Rat))]
  norm_cast

Depends on / 依赖: Rat.finite_rat_abs_sub_lt_one_div_den_sq, Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational, contrapose, convert, finite_rat_abs_sub_lt_one_div_den_sq, infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational, irrational_iff_ne_rational, q.den
-/
theorem Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational (ξ : Real) :
    {q : Rat | |ξ - q| < 1 / (q.den : Real) ^ 2}.Infinite ↔ Irrational ξ := by
  refine
    ⟨fun h => (irrational_iff_ne_rational ξ).mpr fun a b _ => ?_,
      Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational⟩
  contrapose! h
  convert! Rat.finite_rat_abs_sub_lt_one_div_den_sq ((a : Rat) / b) with q
  rw [h]; rw [(by (push_cast; rfl) : (1 : Real) / (q.den : Real) ^ 2 = (1 / (q.den : Rat) ^ 2 : Rat))]
  norm_cast

/-!
### Legendre's Theorem on Rational Approximation

We prove **Legendre's Theorem** on rational approximation: If $\xi$ is a real number and
$x/y$ is a rational number such that $|\xi - x/y| < 1/(2y^2)$,
then $x/y$ is a convergent of the continued fraction expansion of $\xi$.

The proof is by induction. However, the induction proof does not work with the
statement as given, since the assumption is too weak to imply the corresponding
statement for the application of the induction hypothesis. This can be remedied
by making the statement slightly stronger. Namely, we assume that $|\xi - x/y| < 1/(y(2y-1))$
when $y \ge 2$ and $-\frac{1}{2} < \xi - x < 1$ when $y = 1$.
-/


section Convergent

namespace Real

open Int

/-!
### Convergents: definition and API lemmas
-/


/--
Definition of `convergent` / `convergent` 的定义

English:
definition convergent
  signature: : Real -> Nat -> Rat

中文:
定义 convergent
  签名: : 实数 -> 自然数 -> 有理数
-/
noncomputable def convergent : Real -> Nat -> Rat
  | ξ, 0 => ⌊ξ⌋
  | ξ, n + 1 => ⌊ξ⌋ + (convergent (fract ξ)⁻¹ n)⁻¹

/-- The zeroth convergent of `ξ` is `⌊ξ⌋`. -/
@[simp]
/--
theorem `convergent_zero` / 定理 `convergent_zero`

English:
theorem convergent_zero
  given: (ξ : Real)
  statement: ξ.convergent 0 = ⌊ξ⌋
  proof: rfl

中文:
定理 convergent_zero
  条件: (ξ : 实数)
  结论: ξ.convergent 0 = ⌊ξ⌋
  证明: rfl
-/
theorem convergent_zero (ξ : Real) : ξ.convergent 0 = ⌊ξ⌋ :=
  rfl

/-- The `(n+1)`th convergent of `ξ` is the `n`th convergent of `1/(fract ξ)`. -/
@[simp]
/--
theorem `convergent_succ` / 定理 `convergent_succ`

English:
theorem convergent_succ
  given: (ξ : Real) (n : Nat)
  proof: rfl

中文:
定理 convergent_succ
  条件: (ξ : 实数) (n : 自然数)
  证明: rfl
-/
theorem convergent_succ (ξ : Real) (n : Nat) :
    ξ.convergent (n + 1) = ⌊ξ⌋ + ((fract ξ)⁻¹.convergent n)⁻¹ :=
  rfl

/-- All convergents of `0` are zero. -/
@[simp]
/--
theorem `convergent_of_zero` / 定理 `convergent_of_zero`

English:
theorem convergent_of_zero
  given: (n : Nat)
  statement: convergent 0 n = 0
  proof: by
  induction n with
  | zero => simp only [convergent_zero, floor_zero, cast_zero]
  | succ n ih =>
    simp only [ih, convergent_succ, floor_zero, cast_zero, fract_zero, add_zero, inv_zero]

中文:
定理 convergent_of_zero
  条件: (n : 自然数)
  结论: convergent 0 n = 0
  证明: by
  induction n with
  | zero => simp only [convergent_zero, floor_zero, cast_zero]
  | succ n ih =>
    simp only [ih, convergent_succ, floor_zero, cast_zero, fract_zero, add_zero, inv_zero]

Depends on / 依赖: add_zero, cast_zero, convergent_succ, convergent_zero, floor_zero, fract_zero, inv_zero
-/
theorem convergent_of_zero (n : Nat) : convergent 0 n = 0 := by
  induction n with
  | zero => simp only [convergent_zero, floor_zero, cast_zero]
  | succ n ih =>
    simp only [ih, convergent_succ, floor_zero, cast_zero, fract_zero, add_zero, inv_zero]

/-- If `ξ` is an integer, all its convergents equal `ξ`. -/
@[simp]
/--
theorem `convergent_of_int` / 定理 `convergent_of_int`

English:
theorem convergent_of_int
  given: {ξ : Int} (n : Nat)
  statement: convergent ξ n = ξ
  proof: by
  cases n
  · simp only [convergent_zero, floor_intCast]
  · simp only [convergent_succ, floor_intCast, fract_intCast, convergent_of_zero, add_zero,
      inv_zero]

中文:
定理 convergent_of_int
  条件: {ξ : 整数} (n : 自然数)
  结论: convergent ξ n = ξ
  证明: by
  cases n
  · simp only [convergent_zero, floor_intCast]
  · simp only [convergent_succ, floor_intCast, fract_intCast, convergent_of_zero, add_zero,
      inv_zero]

Depends on / 依赖: add_zero, convergent_of_zero, convergent_succ, convergent_zero, floor_intCast, fract_intCast, inv_zero
-/
theorem convergent_of_int {ξ : Int} (n : Nat) : convergent ξ n = ξ := by
  cases n
  · simp only [convergent_zero, floor_intCast]
  · simp only [convergent_succ, floor_intCast, fract_intCast, convergent_of_zero, add_zero,
      inv_zero]

end Real

end Convergent

/-!
### The key technical condition for the induction proof
-/


namespace Real

open Int

-- this is not `private`, as it is used in the public `exists_rat_eq_convergent'` below.
/--
Definition of `ContfracLegendre.Ass` / `ContfracLegendre.Ass` 的定义

English:
definition ContfracLegendre.Ass
  signature: (ξ : Real) (u v : Int)
  body: IsCoprime u v ∧ (v = 1 -> (-(1 / 2) : Real) < ξ - u) ∧
    |ξ - u / v| < ((v : Real) * (2 * v - 1))⁻¹

中文:
定义 ContfracLegendre.Ass
  签名: (ξ : 实数) (u v : 整数)
  定义体: IsCoprime u v ∧ (v = 1 -> (-(1 / 2) : Real) < ξ - u) ∧
    |ξ - u / v| < ((v : Real) * (2 * v - 1))⁻¹

Depends on / 依赖: IsCoprime
-/
def ContfracLegendre.Ass (ξ : Real) (u v : Int) : Prop :=
  IsCoprime u v ∧ (v = 1 -> (-(1 / 2) : Real) < ξ - u) ∧
    |ξ - u / v| < ((v : Real) * (2 * v - 1))⁻¹

-- ### Auxiliary lemmas
-- This saves a few lines below, as it is frequently needed.
/--
theorem `aux₀` / 定理 `aux₀`

English:
theorem aux₀
  given: {v : Int} (hv : 0 < v)
  statement: (0 : Real) < v ∧ (0 : Real) < 2 * v - 1
  proof: ⟨cast_pos.mpr hv, by norm_cast; lia⟩

中文:
定理 aux₀
  条件: {v : 整数} (hv : 0 < v)
  结论: (0 : 实数) < v ∧ (0 : 实数) < 2 * v - 1
  证明: ⟨cast_pos.mpr hv, by norm_cast; lia⟩
-/
private theorem aux₀ {v : Int} (hv : 0 < v) : (0 : Real) < v ∧ (0 : Real) < 2 * v - 1 :=
  ⟨cast_pos.mpr hv, by norm_cast; lia⟩

-- In the following, we assume that `ass ξ u v` holds and `v ≥ 2`.
variable {ξ : Real} {u v : Int}

section
variable (hv : 2 <= v) (h : ContfracLegendre.Ass ξ u v)
include hv h

-- The fractional part of `ξ` is positive.
/--
theorem `aux₁` / 定理 `aux₁`

English:
theorem aux₁
  statement: 0 < fract ξ
  proof: by
  have hv₀ : (0 : Real) < v := cast_pos.mpr (zero_lt_two.trans_le hv)
  obtain ⟨hv₁, hv₂⟩ := aux₀ (zero_lt_two.trans_le hv)
  obtain ⟨hcop, _, h⟩ := h
  refine fract_pos.mpr fun hf => ?_
  rw [hf] at h
  have H : (2 * v - 1 : Real) < 1 := by
    refine (mul_lt_iff_lt_one_right hv₀).1 ((inv_lt_inv₀ hv₀ (mul_pos hv₁ hv₂)).1 (h.trans_le' ?_))
    have h' : (⌊ξ⌋ : Real) - u / v = (⌊ξ⌋ * v - u) / v := by field
    rw [h']; rw [abs_div]; rw [abs_of_pos hv₀]; rw [← one_div]; rw [div_le_div_iff_of_pos_right hv₀]
    norm_cast
    rw [← zero_add (1 : Int)]; rw [add_one_le_iff]; rw [abs_pos]; rw [sub_ne_zero]
    rintro rfl
    cases isUnit_iff.mp (isCoprime_self.mp (IsCoprime.mul_left_iff.mp hcop).2) <;> lia
  norm_cast at H
  linarith only [hv, H]

中文:
定理 aux₁
  结论: 0 < fract ξ
  证明: by
  have hv₀ : (0 : Real) < v := cast_pos.mpr (zero_lt_two.trans_le hv)
  obtain ⟨hv₁, hv₂⟩ := aux₀ (zero_lt_two.trans_le hv)
  obtain ⟨hcop, _, h⟩ := h
  refine fract_pos.mpr fun hf => ?_
  rw [hf] at h
  have H : (2 * v - 1 : Real) < 1 := by
    refine (mul_lt_iff_lt_one_right hv₀).1 ((inv_lt_inv₀ hv₀ (mul_pos hv₁ hv₂)).1 (h.trans_le' ?_))
    have h' : (⌊ξ⌋ : Real) - u / v = (⌊ξ⌋ * v - u) / v := by field
    rw [h']; rw [abs_div]; rw [abs_of_pos hv₀]; rw [← one_div]; rw [div_le_div_iff_of_pos_right hv₀]
    norm_cast
    rw [← zero_add (1 : Int)]; rw [add_one_le_iff]; rw [abs_pos]; rw [sub_ne_zero]
    rintro rfl
    cases isUnit_iff.mp (isCoprime_self.mp (IsCoprime.mul_left_iff.mp hcop).2) <;> lia
  norm_cast at H
  linarith only [hv, H]
-/
private theorem aux₁ : 0 < fract ξ := by
  have hv₀ : (0 : Real) < v := cast_pos.mpr (zero_lt_two.trans_le hv)
  obtain ⟨hv₁, hv₂⟩ := aux₀ (zero_lt_two.trans_le hv)
  obtain ⟨hcop, _, h⟩ := h
  refine fract_pos.mpr fun hf => ?_
  rw [hf] at h
  have H : (2 * v - 1 : Real) < 1 := by
    refine (mul_lt_iff_lt_one_right hv₀).1 ((inv_lt_inv₀ hv₀ (mul_pos hv₁ hv₂)).1 (h.trans_le' ?_))
    have h' : (⌊ξ⌋ : Real) - u / v = (⌊ξ⌋ * v - u) / v := by field
    rw [h']; rw [abs_div]; rw [abs_of_pos hv₀]; rw [← one_div]; rw [div_le_div_iff_of_pos_right hv₀]
    norm_cast
    rw [← zero_add (1 : Int)]; rw [add_one_le_iff]; rw [abs_pos]; rw [sub_ne_zero]
    rintro rfl
    cases isUnit_iff.mp (isCoprime_self.mp (IsCoprime.mul_left_iff.mp hcop).2) <;> lia
  norm_cast at H
  linarith only [hv, H]

-- An auxiliary lemma for the inductive step.
/--
theorem `aux₂` / 定理 `aux₂`

English:
theorem aux₂
  statement: 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v
  proof: by
  obtain ⟨hcop, _, h⟩ := h
  obtain ⟨hv₀, hv₀'⟩ := aux₀ (zero_lt_two.trans_le hv)
  have hv₁ : 0 < 2 * v - 1 := by linarith only [hv]
  rw [← one_div]; rw [lt_div_iff₀ (mul_pos hv₀ hv₀')]; rw [← abs_of_pos (mul_pos hv₀ hv₀')]; rw [← abs_mul]; rw [sub_mul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [div_mul_cancel₀ _ hv₀.ne']; rw [abs_sub_comm]; rw [abs_lt]; rw [lt_sub_iff_add_lt]; rw [sub_lt_iff_lt_add]; rw [mul_assoc] at h
  have hu₀ : 0 <= u - ⌊ξ⌋ * v := by
    refine (mul_nonneg_iff_of_pos_right hv₁).mp ?_
    rw [← sub_one_lt_iff]; rw [zero_sub]
    replace h := h.1
    rw [← lt_sub_iff_add_lt]; rw [← mul_assoc]; rw [← sub_mul] at h
    exact mod_cast
      h.trans_le
        ((mul_le_mul_iff_left₀ <| hv₀').mpr <|
          (sub_le_sub_iff_left (u : Real)).mpr ((mul_le_mul_iff_left₀ hv₀).mpr (floor_le ξ)))
  have hu₁ : u - ⌊ξ⌋ * v <= v := by
    refine _root_.le_of_mul_le_mul_right (le_of_lt_add_one ?_) hv₁
    replace h := h.2
    rw [← sub_lt_iff_lt_add]; rw [← mul_assoc]; rw [← sub_mul]; rw [← add_lt_add_iff_right (v * (2 * v - 1) : Real)]; rw [add_comm (1 : Real)] at h
    have :=
flip mul_lt_mul_of_pos_right hv₀' (sub_lt_sub_iff_left (u : Real)).mpr
flip mul_lt_mul_of_pos_right hv₀ sub_right_lt_of_lt_add lt_floor_add_one ξ
    rw [sub_mul ξ]; rw [one_mul]; rw [← sub_add]; rw [add_mul] at this
    exact mod_cast this.trans h
  have huv_cop : IsCoprime (u - ⌊ξ⌋ * v) v := by
    rwa [sub_eq_add_neg, ← neg_mul, IsCoprime.add_mul_right_left_iff]
  refine ⟨lt_of_le_of_ne' hu₀ fun hf => ?_, lt_of_le_of_ne hu₁ fun hf => ?_⟩ <;>
    · rw [hf] at huv_cop
      simp only [isCoprime_zero_left, isCoprime_self, isUnit_iff] at huv_cop
      rcases huv_cop with huv_cop | huv_cop <;> linarith only [hv, huv_cop]

中文:
定理 aux₂
  结论: 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v
  证明: by
  obtain ⟨hcop, _, h⟩ := h
  obtain ⟨hv₀, hv₀'⟩ := aux₀ (zero_lt_two.trans_le hv)
  have hv₁ : 0 < 2 * v - 1 := by linarith only [hv]
  rw [← one_div]; rw [lt_div_iff₀ (mul_pos hv₀ hv₀')]; rw [← abs_of_pos (mul_pos hv₀ hv₀')]; rw [← abs_mul]; rw [sub_mul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [div_mul_cancel₀ _ hv₀.ne']; rw [abs_sub_comm]; rw [abs_lt]; rw [lt_sub_iff_add_lt]; rw [sub_lt_iff_lt_add]; rw [mul_assoc] at h
  have hu₀ : 0 <= u - ⌊ξ⌋ * v := by
    refine (mul_nonneg_iff_of_pos_right hv₁).mp ?_
    rw [← sub_one_lt_iff]; rw [zero_sub]
    replace h := h.1
    rw [← lt_sub_iff_add_lt]; rw [← mul_assoc]; rw [← sub_mul] at h
    exact mod_cast
      h.trans_le
        ((mul_le_mul_iff_left₀ <| hv₀').mpr <|
          (sub_le_sub_iff_left (u : Real)).mpr ((mul_le_mul_iff_left₀ hv₀).mpr (floor_le ξ)))
  have hu₁ : u - ⌊ξ⌋ * v <= v := by
    refine _root_.le_of_mul_le_mul_right (le_of_lt_add_one ?_) hv₁
    replace h := h.2
    rw [← sub_lt_iff_lt_add]; rw [← mul_assoc]; rw [← sub_mul]; rw [← add_lt_add_iff_right (v * (2 * v - 1) : Real)]; rw [add_comm (1 : Real)] at h
    have :=
flip mul_lt_mul_of_pos_right hv₀' (sub_lt_sub_iff_left (u : Real)).mpr
flip mul_lt_mul_of_pos_right hv₀ sub_right_lt_of_lt_add lt_floor_add_one ξ
    rw [sub_mul ξ]; rw [one_mul]; rw [← sub_add]; rw [add_mul] at this
    exact mod_cast this.trans h
  have huv_cop : IsCoprime (u - ⌊ξ⌋ * v) v := by
    rwa [sub_eq_add_neg, ← neg_mul, IsCoprime.add_mul_right_left_iff]
  refine ⟨lt_of_le_of_ne' hu₀ fun hf => ?_, lt_of_le_of_ne hu₁ fun hf => ?_⟩ <;>
    · rw [hf] at huv_cop
      simp only [isCoprime_zero_left, isCoprime_self, isUnit_iff] at huv_cop
      rcases huv_cop with huv_cop | huv_cop <;> linarith only [hv, huv_cop]
-/
private theorem aux₂ : 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v := by
  obtain ⟨hcop, _, h⟩ := h
  obtain ⟨hv₀, hv₀'⟩ := aux₀ (zero_lt_two.trans_le hv)
  have hv₁ : 0 < 2 * v - 1 := by linarith only [hv]
  rw [← one_div]; rw [lt_div_iff₀ (mul_pos hv₀ hv₀')]; rw [← abs_of_pos (mul_pos hv₀ hv₀')]; rw [← abs_mul]; rw [sub_mul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [div_mul_cancel₀ _ hv₀.ne']; rw [abs_sub_comm]; rw [abs_lt]; rw [lt_sub_iff_add_lt]; rw [sub_lt_iff_lt_add]; rw [mul_assoc] at h
  have hu₀ : 0 <= u - ⌊ξ⌋ * v := by
    refine (mul_nonneg_iff_of_pos_right hv₁).mp ?_
    rw [← sub_one_lt_iff]; rw [zero_sub]
    replace h := h.1
    rw [← lt_sub_iff_add_lt]; rw [← mul_assoc]; rw [← sub_mul] at h
    exact mod_cast
      h.trans_le
        ((mul_le_mul_iff_left₀ <| hv₀').mpr <|
          (sub_le_sub_iff_left (u : Real)).mpr ((mul_le_mul_iff_left₀ hv₀).mpr (floor_le ξ)))
  have hu₁ : u - ⌊ξ⌋ * v <= v := by
    refine _root_.le_of_mul_le_mul_right (le_of_lt_add_one ?_) hv₁
    replace h := h.2
    rw [← sub_lt_iff_lt_add]; rw [← mul_assoc]; rw [← sub_mul]; rw [← add_lt_add_iff_right (v * (2 * v - 1) : Real)]; rw [add_comm (1 : Real)] at h
    have :=
flip mul_lt_mul_of_pos_right hv₀' (sub_lt_sub_iff_left (u : Real)).mpr
flip mul_lt_mul_of_pos_right hv₀ sub_right_lt_of_lt_add lt_floor_add_one ξ
    rw [sub_mul ξ]; rw [one_mul]; rw [← sub_add]; rw [add_mul] at this
    exact mod_cast this.trans h
  have huv_cop : IsCoprime (u - ⌊ξ⌋ * v) v := by
    rwa [sub_eq_add_neg, ← neg_mul, IsCoprime.add_mul_right_left_iff]
  refine ⟨lt_of_le_of_ne' hu₀ fun hf => ?_, lt_of_le_of_ne hu₁ fun hf => ?_⟩ <;>
    · rw [hf] at huv_cop
      simp only [isCoprime_zero_left, isCoprime_self, isUnit_iff] at huv_cop
      rcases huv_cop with huv_cop | huv_cop <;> linarith only [hv, huv_cop]

-- The key step: the relevant inequality persists in the inductive step.
/--
theorem `aux₃` / 定理 `aux₃`

English:
theorem aux₃
  proof: by
  obtain ⟨hu₀, huv⟩ := aux₂ hv h
  have hξ₀ := aux₁ hv h
  set u' := u - ⌊ξ⌋ * v with hu'
  have hu'Real : (u' : Real) = u - ⌊ξ⌋ * v := mod_cast hu'
  rw [← hu'Real]
  replace hu'Real := (eq_sub_iff_add_eq.mp hu'Real).symm
  obtain ⟨Hu, Hu'⟩ := aux₀ hu₀
  obtain ⟨Hv, Hv'⟩ := aux₀ (zero_lt_two.trans_le hv)
  have H₁ := div_pos (div_pos Hv Hu) hξ₀
  replace h := h.2.2
  have h' : |fract ξ - u' / v| < ((v : Real) * (2 * v - 1))⁻¹ := by
    rwa [hu'Real, add_div, mul_div_cancel_right₀ _ Hv.ne', ← sub_sub, sub_right_comm] at h
  have H : (2 * u' - 1 : Real) <= (2 * v - 1) * fract ξ := by
    replace h := (abs_lt.mp h).1
    have : (2 * (v : Real) - 1) * (-((v : Real) * (2 * v - 1))⁻¹ + u' / v) = 2 * u' - (1 + u') / v := by
      field
    rw [hu'Real]; rw [add_div]; rw [mul_div_cancel_right₀ _ Hv.ne']; rw [← sub_sub]; rw [sub_right_comm]; rw [self_sub_floor]; rw [lt_sub_iff_add_lt]; rw [← mul_lt_mul_iff_right₀ Hv']; rw [this] at h
    refine LE.le.trans ?_ h.le
    rw [sub_le_sub_iff_left]; rw [div_le_one Hv]; rw [add_comm]
    exact mod_cast huv
  calc
    |(fract ξ)⁻¹ - v / u'| = |(fract ξ - u' / v) * (v / u' / fract ξ)| := by
      rw [abs_sub_comm]; congr 1; field
    _ = |fract ξ - u' / v| * (v / u' / fract ξ) := by rw [abs_mul, abs_of_pos H₁]
    _ < ((v : Real) * (2 * v - 1))⁻¹ * (v / u' / fract ξ) := by gcongr
    _ = (u' * ((2 * v - 1) * fract ξ))⁻¹ := by field
    _ <= (u' * (2 * u' - 1) : Real)⁻¹ := by gcongr

中文:
定理 aux₃
  证明: by
  obtain ⟨hu₀, huv⟩ := aux₂ hv h
  have hξ₀ := aux₁ hv h
  set u' := u - ⌊ξ⌋ * v with hu'
  have hu'Real : (u' : Real) = u - ⌊ξ⌋ * v := mod_cast hu'
  rw [← hu'Real]
  replace hu'Real := (eq_sub_iff_add_eq.mp hu'Real).symm
  obtain ⟨Hu, Hu'⟩ := aux₀ hu₀
  obtain ⟨Hv, Hv'⟩ := aux₀ (zero_lt_two.trans_le hv)
  have H₁ := div_pos (div_pos Hv Hu) hξ₀
  replace h := h.2.2
  have h' : |fract ξ - u' / v| < ((v : Real) * (2 * v - 1))⁻¹ := by
    rwa [hu'Real, add_div, mul_div_cancel_right₀ _ Hv.ne', ← sub_sub, sub_right_comm] at h
  have H : (2 * u' - 1 : Real) <= (2 * v - 1) * fract ξ := by
    replace h := (abs_lt.mp h).1
    have : (2 * (v : Real) - 1) * (-((v : Real) * (2 * v - 1))⁻¹ + u' / v) = 2 * u' - (1 + u') / v := by
      field
    rw [hu'Real]; rw [add_div]; rw [mul_div_cancel_right₀ _ Hv.ne']; rw [← sub_sub]; rw [sub_right_comm]; rw [self_sub_floor]; rw [lt_sub_iff_add_lt]; rw [← mul_lt_mul_iff_right₀ Hv']; rw [this] at h
    refine LE.le.trans ?_ h.le
    rw [sub_le_sub_iff_left]; rw [div_le_one Hv]; rw [add_comm]
    exact mod_cast huv
  calc
    |(fract ξ)⁻¹ - v / u'| = |(fract ξ - u' / v) * (v / u' / fract ξ)| := by
      rw [abs_sub_comm]; congr 1; field
    _ = |fract ξ - u' / v| * (v / u' / fract ξ) := by rw [abs_mul, abs_of_pos H₁]
    _ < ((v : Real) * (2 * v - 1))⁻¹ * (v / u' / fract ξ) := by gcongr
    _ = (u' * ((2 * v - 1) * fract ξ))⁻¹ := by field
    _ <= (u' * (2 * u' - 1) : Real)⁻¹ := by gcongr
-/
private theorem aux₃ :
    |(fract ξ)⁻¹ - v / (u - ⌊ξ⌋ * v)| < (((u : Real) - ⌊ξ⌋ * v) * (2 * (u - ⌊ξ⌋ * v) - 1))⁻¹ := by
  obtain ⟨hu₀, huv⟩ := aux₂ hv h
  have hξ₀ := aux₁ hv h
  set u' := u - ⌊ξ⌋ * v with hu'
  have hu'Real : (u' : Real) = u - ⌊ξ⌋ * v := mod_cast hu'
  rw [← hu'Real]
  replace hu'Real := (eq_sub_iff_add_eq.mp hu'Real).symm
  obtain ⟨Hu, Hu'⟩ := aux₀ hu₀
  obtain ⟨Hv, Hv'⟩ := aux₀ (zero_lt_two.trans_le hv)
  have H₁ := div_pos (div_pos Hv Hu) hξ₀
  replace h := h.2.2
  have h' : |fract ξ - u' / v| < ((v : Real) * (2 * v - 1))⁻¹ := by
    rwa [hu'Real, add_div, mul_div_cancel_right₀ _ Hv.ne', ← sub_sub, sub_right_comm] at h
  have H : (2 * u' - 1 : Real) <= (2 * v - 1) * fract ξ := by
    replace h := (abs_lt.mp h).1
    have : (2 * (v : Real) - 1) * (-((v : Real) * (2 * v - 1))⁻¹ + u' / v) = 2 * u' - (1 + u') / v := by
      field
    rw [hu'Real]; rw [add_div]; rw [mul_div_cancel_right₀ _ Hv.ne']; rw [← sub_sub]; rw [sub_right_comm]; rw [self_sub_floor]; rw [lt_sub_iff_add_lt]; rw [← mul_lt_mul_iff_right₀ Hv']; rw [this] at h
    refine LE.le.trans ?_ h.le
    rw [sub_le_sub_iff_left]; rw [div_le_one Hv]; rw [add_comm]
    exact mod_cast huv
  calc
    |(fract ξ)⁻¹ - v / u'| = |(fract ξ - u' / v) * (v / u' / fract ξ)| := by
      rw [abs_sub_comm]; congr 1; field
    _ = |fract ξ - u' / v| * (v / u' / fract ξ) := by rw [abs_mul, abs_of_pos H₁]
    _ < ((v : Real) * (2 * v - 1))⁻¹ * (v / u' / fract ξ) := by gcongr
    _ = (u' * ((2 * v - 1) * fract ξ))⁻¹ := by field
    _ <= (u' * (2 * u' - 1) : Real)⁻¹ := by gcongr

-- The conditions `ass ξ u v` persist in the inductive step.
/--
theorem `invariant` / 定理 `invariant`

English:
theorem invariant
  statement: ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * v)
  proof: by
  refine ⟨?_, fun huv => ?_, mod_cast aux₃ hv h⟩
  · rw [sub_eq_add_neg, ← neg_mul, isCoprime_comm, IsCoprime.add_mul_right_left_iff]
    exact h.1
  · obtain hv₀' := (aux₀ (zero_lt_two.trans_le hv)).2
    have Hv : (v * (2 * v - 1) : Real)⁻¹ + (v : Real)⁻¹ = 2 / (2 * v - 1) := by
      simp [field]
    have Huv : (u / v : Real) = ⌊ξ⌋ + (v : Real)⁻¹ := by
      rw [sub_eq_iff_eq_add'.mp huv]; simp [field]
    have h' := (abs_sub_lt_iff.mp h.2.2).1
    rw [Huv]; rw [← sub_sub]; rw [sub_lt_iff_lt_add]; rw [self_sub_floor]; rw [Hv] at h'
    rwa [lt_sub_iff_add_lt', (by ring : (v : Real) + -(1 / 2) = (2 * v - 1) / 2),
      lt_inv_comm₀ (div_pos hv₀' zero_lt_two) (aux₁ hv h), inv_div]

中文:
定理 invariant
  结论: ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * v)
  证明: by
  refine ⟨?_, fun huv => ?_, mod_cast aux₃ hv h⟩
  · rw [sub_eq_add_neg, ← neg_mul, isCoprime_comm, IsCoprime.add_mul_right_left_iff]
    exact h.1
  · obtain hv₀' := (aux₀ (zero_lt_two.trans_le hv)).2
    have Hv : (v * (2 * v - 1) : Real)⁻¹ + (v : Real)⁻¹ = 2 / (2 * v - 1) := by
      simp [field]
    have Huv : (u / v : Real) = ⌊ξ⌋ + (v : Real)⁻¹ := by
      rw [sub_eq_iff_eq_add'.mp huv]; simp [field]
    have h' := (abs_sub_lt_iff.mp h.2.2).1
    rw [Huv]; rw [← sub_sub]; rw [sub_lt_iff_lt_add]; rw [self_sub_floor]; rw [Hv] at h'
    rwa [lt_sub_iff_add_lt', (by ring : (v : Real) + -(1 / 2) = (2 * v - 1) / 2),
      lt_inv_comm₀ (div_pos hv₀' zero_lt_two) (aux₁ hv h), inv_div]
-/
private theorem invariant : ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * v) := by
  refine ⟨?_, fun huv => ?_, mod_cast aux₃ hv h⟩
  · rw [sub_eq_add_neg, ← neg_mul, isCoprime_comm, IsCoprime.add_mul_right_left_iff]
    exact h.1
  · obtain hv₀' := (aux₀ (zero_lt_two.trans_le hv)).2
    have Hv : (v * (2 * v - 1) : Real)⁻¹ + (v : Real)⁻¹ = 2 / (2 * v - 1) := by
      simp [field]
    have Huv : (u / v : Real) = ⌊ξ⌋ + (v : Real)⁻¹ := by
      rw [sub_eq_iff_eq_add'.mp huv]; simp [field]
    have h' := (abs_sub_lt_iff.mp h.2.2).1
    rw [Huv]; rw [← sub_sub]; rw [sub_lt_iff_lt_add]; rw [self_sub_floor]; rw [Hv] at h'
    rwa [lt_sub_iff_add_lt', (by ring : (v : Real) + -(1 / 2) = (2 * v - 1) / 2),
      lt_inv_comm₀ (div_pos hv₀' zero_lt_two) (aux₁ hv h), inv_div]

end

/-!
### The main result
-/


/--
theorem `exists_rat_eq_convergent'` / 定理 `exists_rat_eq_convergent'`

English:
theorem exists_rat_eq_convergent'
  given: {v : Nat} (h : ContfracLegendre.Ass ξ u v)
  proof: by
  induction v using Nat.strong_induction_on generalizing ξ u with | h v ih => ?_
  rcases lt_trichotomy v 1 with (ht | rfl | ht)
  · replace h := h.2.2
    simp only [Nat.lt_one_iff.mp ht, Nat.cast_zero, div_zero, tsub_zero, zero_mul,
      cast_zero, inv_zero] at h
    exact False.elim (lt_irrefl _ <| (abs_nonneg ξ).trans_lt h)
  · rw [Nat.cast_one, div_one]
    obtain ⟨_, h₁, h₂⟩ := h
    rcases le_or_gt (u : Real) ξ with ht | ht
    · use 0
      rw [convergent_zero]; rw [Rat.intCast_inj]; rw [eq_comm]; rw [floor_eq_iff]
      convert! And.intro ht (sub_lt_iff_lt_add'.mp (abs_lt.mp h₂).2) <;> norm_num
    · replace h₁ := lt_sub_iff_add_lt'.mp (h₁ rfl)
      have hξ₁ : ⌊ξ⌋ = u - 1 := by
        rw [floor_eq_iff]; rw [cast_sub]; rw [cast_one]; rw [sub_add_cancel]
        exact ⟨(((sub_lt_sub_iff_left _).mpr one_half_lt_one).trans h₁).le, ht⟩
      rcases eq_or_ne ξ ⌊ξ⌋ with Hξ | Hξ
      · rw [Hξ, hξ₁, cast_sub, cast_one, ← sub_eq_add_neg, sub_lt_sub_iff_left] at h₁
        exact False.elim (lt_irrefl _ <| h₁.trans one_half_lt_one)
      · have hξ₂ : ⌊(fract ξ)⁻¹⌋ = 1 := by
          rw [floor_eq_iff]; rw [cast_one]; rw [le_inv_comm₀ zero_lt_one (fract_pos.mpr Hξ)]; rw [inv_one]; rw [one_add_one_eq_two]; rw [inv_lt_comm₀ (fract_pos.mpr Hξ) zero_lt_two]
          refine ⟨(fract_lt_one ξ).le, ?_⟩
          rw [fract]; rw [hξ₁]; rw [cast_sub]; rw [cast_one]; rw [lt_sub_iff_add_lt']; rw [sub_add]
          convert! h₁ using 1
          rw [sub_eq_add_neg]
          norm_num
        use 1
        simp [convergent, hξ₁, hξ₂, cast_sub, cast_one]
  · obtain ⟨huv₀, huv₁⟩ := aux₂ (Nat.cast_le.mpr ht) h
    have Hv : (v : Rat) != 0 := (Nat.cast_pos.mpr (zero_lt_one.trans ht)).ne'
    have huv₁' : (u - ⌊ξ⌋ * v).toNat < v := by zify; rwa [toNat_of_nonneg huv₀.le]
    have inv : ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * ↑v).toNat :=
      (toNat_of_nonneg huv₀.le).symm ▸ invariant (Nat.cast_le.mpr ht) h
    obtain ⟨n, hn⟩ := ih (u - ⌊ξ⌋ * v).toNat huv₁' inv
    use n + 1
    rw [convergent_succ]; rw [← hn]; rw [(mod_cast toNat_of_nonneg huv₀.le : ((u - ⌊ξ⌋ * v).toNat : Rat) = u - ⌊ξ⌋ * v)]; rw [cast_natCast]; rw [inv_div]; rw [sub_div]; rw [mul_div_cancel_right₀ _ Hv]; rw [add_sub_cancel]

中文:
定理 存在_rat_eq_convergent'
  条件: {v : 自然数} (h : ContfracLegendre.Ass ξ u v)
  证明: by
  induction v using Nat.strong_induction_on generalizing ξ u with | h v ih => ?_
  rcases lt_trichotomy v 1 with (ht | rfl | ht)
  · replace h := h.2.2
    simp only [Nat.lt_one_iff.mp ht, Nat.cast_zero, div_zero, tsub_zero, zero_mul,
      cast_zero, inv_zero] at h
    exact False.elim (lt_irrefl _ <| (abs_nonneg ξ).trans_lt h)
  · rw [Nat.cast_one, div_one]
    obtain ⟨_, h₁, h₂⟩ := h
    rcases le_or_gt (u : Real) ξ with ht | ht
    · use 0
      rw [convergent_zero]; rw [Rat.intCast_inj]; rw [eq_comm]; rw [floor_eq_iff]
      convert! And.intro ht (sub_lt_iff_lt_add'.mp (abs_lt.mp h₂).2) <;> norm_num
    · replace h₁ := lt_sub_iff_add_lt'.mp (h₁ rfl)
      have hξ₁ : ⌊ξ⌋ = u - 1 := by
        rw [floor_eq_iff]; rw [cast_sub]; rw [cast_one]; rw [sub_add_cancel]
        exact ⟨(((sub_lt_sub_iff_left _).mpr one_half_lt_one).trans h₁).le, ht⟩
      rcases eq_or_ne ξ ⌊ξ⌋ with Hξ | Hξ
      · rw [Hξ, hξ₁, cast_sub, cast_one, ← sub_eq_add_neg, sub_lt_sub_iff_left] at h₁
        exact False.elim (lt_irrefl _ <| h₁.trans one_half_lt_one)
      · have hξ₂ : ⌊(fract ξ)⁻¹⌋ = 1 := by
          rw [floor_eq_iff]; rw [cast_one]; rw [le_inv_comm₀ zero_lt_one (fract_pos.mpr Hξ)]; rw [inv_one]; rw [one_add_one_eq_two]; rw [inv_lt_comm₀ (fract_pos.mpr Hξ) zero_lt_two]
          refine ⟨(fract_lt_one ξ).le, ?_⟩
          rw [fract]; rw [hξ₁]; rw [cast_sub]; rw [cast_one]; rw [lt_sub_iff_add_lt']; rw [sub_add]
          convert! h₁ using 1
          rw [sub_eq_add_neg]
          norm_num
        use 1
        simp [convergent, hξ₁, hξ₂, cast_sub, cast_one]
  · obtain ⟨huv₀, huv₁⟩ := aux₂ (Nat.cast_le.mpr ht) h
    have Hv : (v : Rat) != 0 := (Nat.cast_pos.mpr (zero_lt_one.trans ht)).ne'
    have huv₁' : (u - ⌊ξ⌋ * v).toNat < v := by zify; rwa [toNat_of_nonneg huv₀.le]
    have inv : ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * ↑v).toNat :=
      (toNat_of_nonneg huv₀.le).symm ▸ invariant (Nat.cast_le.mpr ht) h
    obtain ⟨n, hn⟩ := ih (u - ⌊ξ⌋ * v).toNat huv₁' inv
    use n + 1
    rw [convergent_succ]; rw [← hn]; rw [(mod_cast toNat_of_nonneg huv₀.le : ((u - ⌊ξ⌋ * v).toNat : Rat) = u - ⌊ξ⌋ * v)]; rw [cast_natCast]; rw [inv_div]; rw [sub_div]; rw [mul_div_cancel_right₀ _ Hv]; rw [add_sub_cancel]

Depends on / 依赖: False.elim, Nat.cast_one, Nat.cast_zero, Nat.lt_one_iff.mp, Nat.strong_induction_on, Rat.intCast_inj, abs_nonneg, cast_one, cast_zero, convergent_zero, convert, div_one, div_zero, eq_comm, floor_eq_iff, generalizing, intCast_inj, inv_zero, le_or_gt, lt_irrefl
-/
theorem exists_rat_eq_convergent' {v : Nat} (h : ContfracLegendre.Ass ξ u v) :
    exists n, (u / v : Rat) = ξ.convergent n := by
  induction v using Nat.strong_induction_on generalizing ξ u with | h v ih => ?_
  rcases lt_trichotomy v 1 with (ht | rfl | ht)
  · replace h := h.2.2
    simp only [Nat.lt_one_iff.mp ht, Nat.cast_zero, div_zero, tsub_zero, zero_mul,
      cast_zero, inv_zero] at h
    exact False.elim (lt_irrefl _ <| (abs_nonneg ξ).trans_lt h)
  · rw [Nat.cast_one, div_one]
    obtain ⟨_, h₁, h₂⟩ := h
    rcases le_or_gt (u : Real) ξ with ht | ht
    · use 0
      rw [convergent_zero]; rw [Rat.intCast_inj]; rw [eq_comm]; rw [floor_eq_iff]
      convert! And.intro ht (sub_lt_iff_lt_add'.mp (abs_lt.mp h₂).2) <;> norm_num
    · replace h₁ := lt_sub_iff_add_lt'.mp (h₁ rfl)
      have hξ₁ : ⌊ξ⌋ = u - 1 := by
        rw [floor_eq_iff]; rw [cast_sub]; rw [cast_one]; rw [sub_add_cancel]
        exact ⟨(((sub_lt_sub_iff_left _).mpr one_half_lt_one).trans h₁).le, ht⟩
      rcases eq_or_ne ξ ⌊ξ⌋ with Hξ | Hξ
      · rw [Hξ, hξ₁, cast_sub, cast_one, ← sub_eq_add_neg, sub_lt_sub_iff_left] at h₁
        exact False.elim (lt_irrefl _ <| h₁.trans one_half_lt_one)
      · have hξ₂ : ⌊(fract ξ)⁻¹⌋ = 1 := by
          rw [floor_eq_iff]; rw [cast_one]; rw [le_inv_comm₀ zero_lt_one (fract_pos.mpr Hξ)]; rw [inv_one]; rw [one_add_one_eq_two]; rw [inv_lt_comm₀ (fract_pos.mpr Hξ) zero_lt_two]
          refine ⟨(fract_lt_one ξ).le, ?_⟩
          rw [fract]; rw [hξ₁]; rw [cast_sub]; rw [cast_one]; rw [lt_sub_iff_add_lt']; rw [sub_add]
          convert! h₁ using 1
          rw [sub_eq_add_neg]
          norm_num
        use 1
        simp [convergent, hξ₁, hξ₂, cast_sub, cast_one]
  · obtain ⟨huv₀, huv₁⟩ := aux₂ (Nat.cast_le.mpr ht) h
    have Hv : (v : Rat) != 0 := (Nat.cast_pos.mpr (zero_lt_one.trans ht)).ne'
    have huv₁' : (u - ⌊ξ⌋ * v).toNat < v := by zify; rwa [toNat_of_nonneg huv₀.le]
    have inv : ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * ↑v).toNat :=
      (toNat_of_nonneg huv₀.le).symm ▸ invariant (Nat.cast_le.mpr ht) h
    obtain ⟨n, hn⟩ := ih (u - ⌊ξ⌋ * v).toNat huv₁' inv
    use n + 1
    rw [convergent_succ]; rw [← hn]; rw [(mod_cast toNat_of_nonneg huv₀.le : ((u - ⌊ξ⌋ * v).toNat : Rat) = u - ⌊ξ⌋ * v)]; rw [cast_natCast]; rw [inv_div]; rw [sub_div]; rw [mul_div_cancel_right₀ _ Hv]; rw [add_sub_cancel]

/--
theorem `exists_rat_eq_convergent` / 定理 `exists_rat_eq_convergent`

English:
theorem exists_rat_eq_convergent
  given: {q : Rat} (h : |ξ - q| < 1 / (2 * (q.den : Real) ^ 2))
  proof: by
  refine q.num_div_den ▸ exists_rat_eq_convergent' ⟨?_, fun hd => ?_, ?_⟩
  · exact isCoprime_iff_nat_coprime.mpr (natAbs_natCast q.den ▸ q.reduced)
  · rw [← q.den_eq_one_iff.mp (Nat.cast_eq_one.mp hd)] at h
    simpa only [Rat.den_intCast, Nat.cast_one, one_pow, mul_one] using! (abs_lt.mp h).1
  · obtain ⟨hq₀, hq₁⟩ := aux₀ (Nat.cast_pos.mpr q.pos)
    replace hq₁ := mul_pos hq₀ hq₁
    have hq₂ : (0 : Real) < 2 * (q.den * q.den) := mul_pos zero_lt_two (mul_pos hq₀ hq₀)
    rw [cast_natCast] at *
    rw [(by norm_cast : (q.num / q.den : Real) = (q.num / q.den : Rat))]; rw [Rat.num_div_den]
    exact h.trans (by rw [← one_div, sq, one_div_lt_one_div hq₂ hq₁, ← sub_pos]; ring_nf; exact hq₀)

中文:
定理 存在_rat_eq_convergent
  条件: {q : 有理数} (h : |ξ - q| < 1 / (2 * (q.den : 实数) ^ 2))
  证明: by
  refine q.num_div_den ▸ exists_rat_eq_convergent' ⟨?_, fun hd => ?_, ?_⟩
  · exact isCoprime_iff_nat_coprime.mpr (natAbs_natCast q.den ▸ q.reduced)
  · rw [← q.den_eq_one_iff.mp (Nat.cast_eq_one.mp hd)] at h
    simpa only [Rat.den_intCast, Nat.cast_one, one_pow, mul_one] using! (abs_lt.mp h).1
  · obtain ⟨hq₀, hq₁⟩ := aux₀ (Nat.cast_pos.mpr q.pos)
    replace hq₁ := mul_pos hq₀ hq₁
    have hq₂ : (0 : Real) < 2 * (q.den * q.den) := mul_pos zero_lt_two (mul_pos hq₀ hq₀)
    rw [cast_natCast] at *
    rw [(by norm_cast : (q.num / q.den : Real) = (q.num / q.den : Rat))]; rw [Rat.num_div_den]
    exact h.trans (by rw [← one_div, sq, one_div_lt_one_div hq₂ hq₁, ← sub_pos]; ring_nf; exact hq₀)

Depends on / 依赖: Nat.cast_eq_one.mp, Nat.cast_one, Nat.cast_pos.mpr, Rat.den_intCast, abs_lt, abs_lt.mp, cast_eq_one, cast_natCast, cast_one, cast_pos, den_eq_one_iff, den_intCast, exists_rat_eq_convergent, isCoprime_iff_nat_coprime, isCoprime_iff_nat_coprime.mpr, mul_one, mul_pos, natAbs_natCast, num_div_den, one_pow
-/
theorem exists_rat_eq_convergent {q : Rat} (h : |ξ - q| < 1 / (2 * (q.den : Real) ^ 2)) :
    exists n, q = ξ.convergent n := by
  refine q.num_div_den ▸ exists_rat_eq_convergent' ⟨?_, fun hd => ?_, ?_⟩
  · exact isCoprime_iff_nat_coprime.mpr (natAbs_natCast q.den ▸ q.reduced)
  · rw [← q.den_eq_one_iff.mp (Nat.cast_eq_one.mp hd)] at h
    simpa only [Rat.den_intCast, Nat.cast_one, one_pow, mul_one] using! (abs_lt.mp h).1
  · obtain ⟨hq₀, hq₁⟩ := aux₀ (Nat.cast_pos.mpr q.pos)
    replace hq₁ := mul_pos hq₀ hq₁
    have hq₂ : (0 : Real) < 2 * (q.den * q.den) := mul_pos zero_lt_two (mul_pos hq₀ hq₀)
    rw [cast_natCast] at *
    rw [(by norm_cast : (q.num / q.den : Real) = (q.num / q.den : Rat))]; rw [Rat.num_div_den]
    exact h.trans (by rw [← one_div, sq, one_div_lt_one_div hq₂ hq₁, ← sub_pos]; ring_nf; exact hq₀)

end Real
