/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.IsPoly

/-!
## The Frobenius operator

If `R` has characteristic `p`, then there is a ring endomorphism `frobenius R p`
that raises `r : R` to the power `p`.
By applying `WittVector.map` to `frobenius R p`, we obtain a ring endomorphism `𝕎 R →+* 𝕎 R`.
It turns out that this endomorphism can be described by polynomials over `ℤ`
that do not depend on `R` or the fact that it has characteristic `p`.
In this way, we obtain a Frobenius endomorphism `WittVector.frobeniusFun : 𝕎 R → 𝕎 R`
for every commutative ring `R`.

Unfortunately, the aforementioned polynomials cannot be obtained using the machinery
of `wittStructureInt` that was developed in `StructurePolynomial.lean`.
We therefore have to define the polynomials by hand, and check that they have the required property.

In case `R` has characteristic `p`, we show in `frobenius_eq_map_frobenius`
that `WittVector.frobeniusFun` is equal to `WittVector.map (frobenius R p)`.

### Main definitions and results

* `frobeniusPoly`: the polynomials that describe the coefficients of `frobeniusFun`;
* `frobeniusFun`: the Frobenius endomorphism on Witt vectors;
* `frobeniusFun_isPoly`: the tautological assertion that Frobenius is a polynomial function;
* `frobenius_eq_map_frobenius`: the fact that in characteristic `p`, Frobenius is equal to
  `WittVector.map (frobenius R p)`.

TODO: Show that `WittVector.frobeniusFun` is a ring homomorphism,
and bundle it into `WittVector.frobenius`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


namespace WittVector

variable {p : Nat} {R : Type*} [hp : Fact p.Prime] [CommRing R]

local notation "𝕎" => WittVector p -- type as `\bbW`

noncomputable section

open MvPolynomial Finset

variable (p)

/--
Definition of `frobeniusPolyRat` / `frobeniusPolyRat` 的定义

English:
definition frobeniusPolyRat
  signature: (n : Nat)
  body: bind₁ (wittPolynomial p Rat ∘ fun n => n + 1) (xInTermsOfW p Rat n)

中文:
定义 frobeniusPolyRat
  签名: (n : 自然数)
  定义体: bind₁ (wittPolynomial p Rat ∘ fun n => n + 1) (xInTermsOfW p Rat n)

Depends on / 依赖: wittPolynomial, xInTermsOfW
-/
def frobeniusPolyRat (n : Nat) : MvPolynomial Nat Rat :=
  bind₁ (wittPolynomial p Rat ∘ fun n => n + 1) (xInTermsOfW p Rat n)

/--
theorem `bind₁_frobeniusPolyRat_wittPolynomial` / 定理 `bind₁_frobeniusPolyRat_wittPolynomial`

English:
theorem bind₁_frobeniusPolyRat_wittPolynomial
  given: (n : Nat)
  proof: by
  delta frobeniusPolyRat
  rw [← bind₁_bind₁]; rw [bind₁_xInTermsOfW_wittPolynomial]; rw [bind₁_X_right]; rw [Function.comp_apply]

local notation "v" => multiplicity

中文:
定理 bind₁_frobeniusPolyRat_wittPolynomial
  条件: (n : 自然数)
  证明: by
  delta frobeniusPolyRat
  rw [← bind₁_bind₁]; rw [bind₁_xInTermsOfW_wittPolynomial]; rw [bind₁_X_right]; rw [Function.comp_apply]

local notation "v" => multiplicity

Depends on / 依赖: Function, Function.comp_apply, comp_apply, frobeniusPolyRat
-/
theorem bind₁_frobeniusPolyRat_wittPolynomial (n : Nat) :
    bind₁ (frobeniusPolyRat p) (wittPolynomial p Rat n) = wittPolynomial p Rat (n + 1) := by
  delta frobeniusPolyRat
  rw [← bind₁_bind₁]; rw [bind₁_xInTermsOfW_wittPolynomial]; rw [bind₁_X_right]; rw [Function.comp_apply]

local notation "v" => multiplicity

/--
Definition of `frobeniusPolyAux` / `frobeniusPolyAux` 的定义

English:
definition frobeniusPolyAux
  signature: : Nat -> MvPolynomial Nat Int
  body: i.is_lt
      ∑ j in range (p ^ (n - i)),
        (((X (i : Nat) ^ p) ^ (p ^ (n - (i : Nat)) - (j + 1)) : MvPolynomial Nat Int) *
        (frobeniusPolyAux i) ^ (j + 1)) *
        C (((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p (j + 1)))
          * ↑p ^ (j - v p (j + 1)) : Nat) : Int)

omit hp in

中文:
定义 frobeniusPolyAux
  签名: : 自然数 -> 多元多项式 自然数 整数
  定义体: i.is_lt
      ∑ j in range (p ^ (n - i)),
        (((X (i : Nat) ^ p) ^ (p ^ (n - (i : Nat)) - (j + 1)) : MvPolynomial Nat Int) *
        (frobeniusPolyAux i) ^ (j + 1)) *
        C (((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p (j + 1)))
          * ↑p ^ (j - v p (j + 1)) : Nat) : Int)

omit hp in

Depends on / 依赖: i.is_lt, is_lt
-/
noncomputable def frobeniusPolyAux : Nat -> MvPolynomial Nat Int
  | n => X (n + 1) - ∑ i : Fin n, have _ := i.is_lt
      ∑ j in range (p ^ (n - i)),
        (((X (i : Nat) ^ p) ^ (p ^ (n - (i : Nat)) - (j + 1)) : MvPolynomial Nat Int) *
        (frobeniusPolyAux i) ^ (j + 1)) *
        C (((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p (j + 1)))
          * ↑p ^ (j - v p (j + 1)) : Nat) : Int)

omit hp in
/--
theorem `frobeniusPolyAux_eq` / 定理 `frobeniusPolyAux_eq`

English:
theorem frobeniusPolyAux_eq
  given: (n : Nat)
  proof: by
  rw [frobeniusPolyAux]; rw [← Fin.sum_univ_eq_sum_range]

中文:
定理 frobeniusPolyAux_eq
  条件: (n : 自然数)
  证明: by
  rw [frobeniusPolyAux]; rw [← Fin.sum_univ_eq_sum_range]

Depends on / 依赖: Fin.sum_univ_eq_sum_range, frobeniusPolyAux, sum_univ_eq_sum_range
-/
theorem frobeniusPolyAux_eq (n : Nat) :
    frobeniusPolyAux p n =
      X (n + 1) - ∑ i in range n,
          ∑ j in range (p ^ (n - i)),
            (X i ^ p) ^ (p ^ (n - i) - (j + 1)) * frobeniusPolyAux p i ^ (j + 1) *
              C ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - v p (j + 1)) *
                ↑p ^ (j - v p (j + 1)) : Nat) := by
  rw [frobeniusPolyAux]; rw [← Fin.sum_univ_eq_sum_range]

/--
Definition of `frobeniusPoly` / `frobeniusPoly` 的定义

English:
definition frobeniusPoly
  signature: (n : Nat)
  body: X n ^ p + C (p : Int) * frobeniusPolyAux p n

中文:
定义 frobeniusPoly
  签名: (n : 自然数)
  定义体: X n ^ p + C (p : Int) * frobeniusPolyAux p n

Depends on / 依赖: frobeniusPolyAux
-/
def frobeniusPoly (n : Nat) : MvPolynomial Nat Int :=
  X n ^ p + C (p : Int) * frobeniusPolyAux p n

/-
Our next goal is to prove
```
lemma map_frobeniusPoly (n : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (frobeniusPoly p n) = frobeniusPolyRat p n
```
This lemma has a rather long proof, but it mostly boils down to applying induction,
and then using the following two key facts at the right point.
-/
/--
theorem `map_frobeniusPoly.key₁` / 定理 `map_frobeniusPoly.key₁`

English:
theorem map_frobeniusPoly.key₁
  given: (n j : Nat) (hj : j < p ^ n)
  proof: by
  apply pow_dvd_of_le_emultiplicity
  rw [hp.out.emultiplicity_choose_prime_pow hj j.succ_ne_zero]

中文:
定理 map_frobeniusPoly.key₁
  条件: (n j : 自然数) (hj : j < p ^ n)
  证明: by
  apply pow_dvd_of_le_emultiplicity
  rw [hp.out.emultiplicity_choose_prime_pow hj j.succ_ne_zero]

Depends on / 依赖: emultiplicity_choose_prime_pow, hp.out.emultiplicity_choose_prime_pow, j.succ_ne_zero, pow_dvd_of_le_emultiplicity, succ_ne_zero
-/
theorem map_frobeniusPoly.key₁ (n j : Nat) (hj : j < p ^ n) :
    p ^ (n - v p (j + 1)) ∣ (p ^ n).choose (j + 1) := by
  apply pow_dvd_of_le_emultiplicity
  rw [hp.out.emultiplicity_choose_prime_pow hj j.succ_ne_zero]

/--
theorem `map_frobeniusPoly.key₂` / 定理 `map_frobeniusPoly.key₂`

English:
theorem map_frobeniusPoly.key₂
  given: {n i j : Nat} (hi : i <= n) (hj : j < p ^ (n - i))
  proof: by
  generalize h : v p (j + 1) = m
  rsuffices ⟨h₁, h₂⟩ : m <= n - i ∧ m <= j
  · rw [tsub_add_eq_add_tsub h₂, add_comm i j, add_tsub_assoc_of_le (h₁.trans (Nat.sub_le n i)),
      add_assoc, tsub_right_comm, add_comm i,
      tsub_add_cancel_of_le (le_tsub_of_add_le_right ((le_tsub_iff_left hi).mp h₁))]
  have hle : p ^ m <= j + 1 := h ▸ Nat.le_of_dvd j.succ_pos (pow_multiplicity_dvd _ _)
  exact ⟨(Nat.pow_le_pow_iff_right hp.1.one_lt).1 (hle.trans hj),
     Nat.le_of_lt_succ ((m.lt_pow_self hp.1.one_lt).trans_le hle)⟩

中文:
定理 map_frobeniusPoly.key₂
  条件: {n i j : 自然数} (hi : i <= n) (hj : j < p ^ (n - i))
  证明: by
  generalize h : v p (j + 1) = m
  rsuffices ⟨h₁, h₂⟩ : m <= n - i ∧ m <= j
  · rw [tsub_add_eq_add_tsub h₂, add_comm i j, add_tsub_assoc_of_le (h₁.trans (Nat.sub_le n i)),
      add_assoc, tsub_right_comm, add_comm i,
      tsub_add_cancel_of_le (le_tsub_of_add_le_right ((le_tsub_iff_left hi).mp h₁))]
  have hle : p ^ m <= j + 1 := h ▸ Nat.le_of_dvd j.succ_pos (pow_multiplicity_dvd _ _)
  exact ⟨(Nat.pow_le_pow_iff_right hp.1.one_lt).1 (hle.trans hj),
     Nat.le_of_lt_succ ((m.lt_pow_self hp.1.one_lt).trans_le hle)⟩

Depends on / 依赖: Nat.le_of_dvd, Nat.le_of_lt_succ, Nat.pow_le_pow_iff_right, Nat.sub_le, add_assoc, add_comm, add_tsub_assoc_of_le, generalize, hle.trans, j.succ_pos, le_of_dvd, le_of_lt_succ, le_tsub_iff_left, le_tsub_of_add_le_right, lt_pow_self, m.lt_pow_self, one_lt, pow_le_pow_iff_right, pow_multiplicity_dvd, rsuffices
-/
theorem map_frobeniusPoly.key₂ {n i j : Nat} (hi : i <= n) (hj : j < p ^ (n - i)) :
    j - v p (j + 1) + n = i + j + (n - i - v p (j + 1)) := by
  generalize h : v p (j + 1) = m
  rsuffices ⟨h₁, h₂⟩ : m <= n - i ∧ m <= j
  · rw [tsub_add_eq_add_tsub h₂, add_comm i j, add_tsub_assoc_of_le (h₁.trans (Nat.sub_le n i)),
      add_assoc, tsub_right_comm, add_comm i,
      tsub_add_cancel_of_le (le_tsub_of_add_le_right ((le_tsub_iff_left hi).mp h₁))]
  have hle : p ^ m <= j + 1 := h ▸ Nat.le_of_dvd j.succ_pos (pow_multiplicity_dvd _ _)
  exact ⟨(Nat.pow_le_pow_iff_right hp.1.one_lt).1 (hle.trans hj),
     Nat.le_of_lt_succ ((m.lt_pow_self hp.1.one_lt).trans_le hle)⟩

/--
theorem `map_frobeniusPoly` / 定理 `map_frobeniusPoly`

English:
theorem map_frobeniusPoly
  given: (n : Nat)
  proof: by
  rw [frobeniusPoly]; rw [map_add]; rw [map_mul]; rw [map_pow]; rw [map_C]; rw [map_X]; rw [eq_intCast]; rw [Int.cast_natCast]; rw [frobeniusPolyRat]
  refine Nat.strong_induction_on n ?_; clear n
  intro n IH
  rw [xInTermsOfW_eq]
  simp only [map_sum, map_sub, map_mul, map_pow (bind₁ _), bind₁_C_right]
  have h1 : (p : Rat) ^ n * ⅟(p : Rat) ^ n = 1 := by rw [← mul_pow, mul_invOf_self, one_pow]
  rw [bind₁_X_right]; rw [Function.comp_apply]; rw [wittPolynomial_eq_sum_C_mul_X_pow]; rw [sum_range_succ]; rw [sum_range_succ]; rw [tsub_self]; rw [add_tsub_cancel_left]; rw [pow_zero]; rw [pow_one]; rw [pow_one]; rw [sub_mul]; rw [add_mul]; rw [add_mul]; rw [mul_right_comm]; rw [mul_right_comm (C ((p : Rat) ^ (n + 1)))]; rw [← C_mul]; rw [← C_mul]; rw [pow_succ']; rw [mul_assoc (p : Rat) ((p : Rat) ^ n)]; rw [h1]; rw [mul_one]; rw [C_1]; rw [one_mul]; rw [add_comm _ (X n ^ p)]; rw [add_assoc]; rw [← add_sub]; rw [add_right_inj]; rw [frobeniusPolyAux_eq]; rw [map_sub]; rw [map_X]; rw [mul_sub]; rw [sub_eq_add_neg]; rw [add_comm _ (C (p : Rat) * X (n + 1))]; rw [← add_sub]; rw [add_right_inj]; rw [neg_eq_iff_eq_neg]; rw [neg_sub]; rw [eq_comm]
  simp only [map_sum, mul_sum, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← IH i hi]
  clear IH
  rw [add_comm (X i ^ p)]; rw [add_pow]; rw [sum_range_succ']; rw [pow_zero]; rw [tsub_zero]; rw [Nat.choose_zero_right]; rw [one_mul]; rw [Nat.cast_one]; rw [mul_one]; rw [mul_add]; rw [add_mul]; rw [Nat.succ_sub (le_of_lt hi)]; rw [Nat.succ_eq_add_one (n - i)]; rw [pow_succ']; rw [pow_mul]; rw [add_sub_cancel_right]; rw [mul_sum]; rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [map_mul]; rw [map_mul]; rw [map_pow]; rw [map_pow]; rw [map_pow]; rw [map_pow]; rw [map_pow]; rw [map_C]; rw [map_X]; rw [mul_pow]
  rw [mul_comm (C (p : Rat) ^ i)]; rw [mul_comm _ ((X i ^ p) ^ _)]; rw [mul_comm (C (p : Rat) ^ (j + 1))]; rw [mul_comm (C (p : Rat))]
  simp only [mul_assoc]
  apply congr_arg
  apply congr_arg
  rw [← C_eq_coe_nat]
  simp only [← map_pow, ← C_mul]
  rw [C_inj]
  simp only [invOf_eq_inv, eq_intCast, inv_pow, Int.cast_natCast, Nat.cast_mul, Int.cast_mul]
  rw [Rat.natCast_div _ _ (map_frobeniusPoly.key₁ p (n - i) j hj)]
  push_cast
  linear_combination (norm := skip) -p / p ^ n / p ^ (n - i - v p (j + 1))
    * (p ^ (n - i)).choose (j + 1) * congr((p : Rat) ^ $(map_frobeniusPoly.key₂ p hi.le hj))
  field [hp.1.ne_zero]

中文:
定理 map_frobeniusPoly
  条件: (n : 自然数)
  证明: by
  rw [frobeniusPoly]; rw [map_add]; rw [map_mul]; rw [map_pow]; rw [map_C]; rw [map_X]; rw [eq_intCast]; rw [Int.cast_natCast]; rw [frobeniusPolyRat]
  refine Nat.strong_induction_on n ?_; clear n
  intro n IH
  rw [xInTermsOfW_eq]
  simp only [map_sum, map_sub, map_mul, map_pow (bind₁ _), bind₁_C_right]
  have h1 : (p : Rat) ^ n * ⅟(p : Rat) ^ n = 1 := by rw [← mul_pow, mul_invOf_self, one_pow]
  rw [bind₁_X_right]; rw [Function.comp_apply]; rw [wittPolynomial_eq_sum_C_mul_X_pow]; rw [sum_range_succ]; rw [sum_range_succ]; rw [tsub_self]; rw [add_tsub_cancel_left]; rw [pow_zero]; rw [pow_one]; rw [pow_one]; rw [sub_mul]; rw [add_mul]; rw [add_mul]; rw [mul_right_comm]; rw [mul_right_comm (C ((p : Rat) ^ (n + 1)))]; rw [← C_mul]; rw [← C_mul]; rw [pow_succ']; rw [mul_assoc (p : Rat) ((p : Rat) ^ n)]; rw [h1]; rw [mul_one]; rw [C_1]; rw [one_mul]; rw [add_comm _ (X n ^ p)]; rw [add_assoc]; rw [← add_sub]; rw [add_right_inj]; rw [frobeniusPolyAux_eq]; rw [map_sub]; rw [map_X]; rw [mul_sub]; rw [sub_eq_add_neg]; rw [add_comm _ (C (p : Rat) * X (n + 1))]; rw [← add_sub]; rw [add_right_inj]; rw [neg_eq_iff_eq_neg]; rw [neg_sub]; rw [eq_comm]
  simp only [map_sum, mul_sum, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← IH i hi]
  clear IH
  rw [add_comm (X i ^ p)]; rw [add_pow]; rw [sum_range_succ']; rw [pow_zero]; rw [tsub_zero]; rw [Nat.choose_zero_right]; rw [one_mul]; rw [Nat.cast_one]; rw [mul_one]; rw [mul_add]; rw [add_mul]; rw [Nat.succ_sub (le_of_lt hi)]; rw [Nat.succ_eq_add_one (n - i)]; rw [pow_succ']; rw [pow_mul]; rw [add_sub_cancel_right]; rw [mul_sum]; rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [map_mul]; rw [map_mul]; rw [map_pow]; rw [map_pow]; rw [map_pow]; rw [map_pow]; rw [map_pow]; rw [map_C]; rw [map_X]; rw [mul_pow]
  rw [mul_comm (C (p : Rat) ^ i)]; rw [mul_comm _ ((X i ^ p) ^ _)]; rw [mul_comm (C (p : Rat) ^ (j + 1))]; rw [mul_comm (C (p : Rat))]
  simp only [mul_assoc]
  apply congr_arg
  apply congr_arg
  rw [← C_eq_coe_nat]
  simp only [← map_pow, ← C_mul]
  rw [C_inj]
  simp only [invOf_eq_inv, eq_intCast, inv_pow, Int.cast_natCast, Nat.cast_mul, Int.cast_mul]
  rw [Rat.natCast_div _ _ (map_frobeniusPoly.key₁ p (n - i) j hj)]
  push_cast
  linear_combination (norm := skip) -p / p ^ n / p ^ (n - i - v p (j + 1))
    * (p ^ (n - i)).choose (j + 1) * congr((p : Rat) ^ $(map_frobeniusPoly.key₂ p hi.le hj))
  field [hp.1.ne_zero]

Depends on / 依赖: Function, Function.comp_apply, Int.cast_natCast, Nat.strong_induction_on, cast_natCast, comp_apply, eq_intCast, frobeniusPoly, frobeniusPolyRat, map_C, map_X, map_add, map_mul, map_pow, map_sub, map_sum, mul_invOf_self, mul_pow, one_pow, strong_induction_on
-/
theorem map_frobeniusPoly (n : Nat) :
    MvPolynomial.map (Int.castRingHom Rat) (frobeniusPoly p n) = frobeniusPolyRat p n := by
  rw [frobeniusPoly]; rw [map_add]; rw [map_mul]; rw [map_pow]; rw [map_C]; rw [map_X]; rw [eq_intCast]; rw [Int.cast_natCast]; rw [frobeniusPolyRat]
  refine Nat.strong_induction_on n ?_; clear n
  intro n IH
  rw [xInTermsOfW_eq]
  simp only [map_sum, map_sub, map_mul, map_pow (bind₁ _), bind₁_C_right]
  have h1 : (p : Rat) ^ n * ⅟(p : Rat) ^ n = 1 := by rw [← mul_pow, mul_invOf_self, one_pow]
  rw [bind₁_X_right]; rw [Function.comp_apply]; rw [wittPolynomial_eq_sum_C_mul_X_pow]; rw [sum_range_succ]; rw [sum_range_succ]; rw [tsub_self]; rw [add_tsub_cancel_left]; rw [pow_zero]; rw [pow_one]; rw [pow_one]; rw [sub_mul]; rw [add_mul]; rw [add_mul]; rw [mul_right_comm]; rw [mul_right_comm (C ((p : Rat) ^ (n + 1)))]; rw [← C_mul]; rw [← C_mul]; rw [pow_succ']; rw [mul_assoc (p : Rat) ((p : Rat) ^ n)]; rw [h1]; rw [mul_one]; rw [C_1]; rw [one_mul]; rw [add_comm _ (X n ^ p)]; rw [add_assoc]; rw [← add_sub]; rw [add_right_inj]; rw [frobeniusPolyAux_eq]; rw [map_sub]; rw [map_X]; rw [mul_sub]; rw [sub_eq_add_neg]; rw [add_comm _ (C (p : Rat) * X (n + 1))]; rw [← add_sub]; rw [add_right_inj]; rw [neg_eq_iff_eq_neg]; rw [neg_sub]; rw [eq_comm]
  simp only [map_sum, mul_sum, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← IH i hi]
  clear IH
  rw [add_comm (X i ^ p)]; rw [add_pow]; rw [sum_range_succ']; rw [pow_zero]; rw [tsub_zero]; rw [Nat.choose_zero_right]; rw [one_mul]; rw [Nat.cast_one]; rw [mul_one]; rw [mul_add]; rw [add_mul]; rw [Nat.succ_sub (le_of_lt hi)]; rw [Nat.succ_eq_add_one (n - i)]; rw [pow_succ']; rw [pow_mul]; rw [add_sub_cancel_right]; rw [mul_sum]; rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [map_mul]; rw [map_mul]; rw [map_pow]; rw [map_pow]; rw [map_pow]; rw [map_pow]; rw [map_pow]; rw [map_C]; rw [map_X]; rw [mul_pow]
  rw [mul_comm (C (p : Rat) ^ i)]; rw [mul_comm _ ((X i ^ p) ^ _)]; rw [mul_comm (C (p : Rat) ^ (j + 1))]; rw [mul_comm (C (p : Rat))]
  simp only [mul_assoc]
  apply congr_arg
  apply congr_arg
  rw [← C_eq_coe_nat]
  simp only [← map_pow, ← C_mul]
  rw [C_inj]
  simp only [invOf_eq_inv, eq_intCast, inv_pow, Int.cast_natCast, Nat.cast_mul, Int.cast_mul]
  rw [Rat.natCast_div _ _ (map_frobeniusPoly.key₁ p (n - i) j hj)]
  push_cast
  linear_combination (norm := skip) -p / p ^ n / p ^ (n - i - v p (j + 1))
    * (p ^ (n - i)).choose (j + 1) * congr((p : Rat) ^ $(map_frobeniusPoly.key₂ p hi.le hj))
  field [hp.1.ne_zero]

/--
theorem `frobeniusPoly_zmod` / 定理 `frobeniusPoly_zmod`

English:
theorem frobeniusPoly_zmod
  given: (n : Nat)
  proof: by
  rw [frobeniusPoly]; rw [map_add]; rw [map_pow]; rw [map_mul]; rw [map_X]; rw [map_C]
  simp only [Int.cast_natCast, add_zero, eq_intCast, ZMod.natCast_self, zero_mul, C_0]

@[simp]

中文:
定理 frobeniusPoly_zmod
  条件: (n : 自然数)
  证明: by
  rw [frobeniusPoly]; rw [map_add]; rw [map_pow]; rw [map_mul]; rw [map_X]; rw [map_C]
  simp only [Int.cast_natCast, add_zero, eq_intCast, ZMod.natCast_self, zero_mul, C_0]

@[simp]

Depends on / 依赖: Int.cast_natCast, ZMod.natCast_self, add_zero, cast_natCast, eq_intCast, frobeniusPoly, map_C, map_X, map_add, map_mul, map_pow, natCast_self, zero_mul
-/
theorem frobeniusPoly_zmod (n : Nat) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n) = X n ^ p := by
  rw [frobeniusPoly]; rw [map_add]; rw [map_pow]; rw [map_mul]; rw [map_X]; rw [map_C]
  simp only [Int.cast_natCast, add_zero, eq_intCast, ZMod.natCast_self, zero_mul, C_0]

@[simp]
/--
theorem `bind₁_frobeniusPoly_wittPolynomial` / 定理 `bind₁_frobeniusPoly_wittPolynomial`

English:
theorem bind₁_frobeniusPoly_wittPolynomial
  given: (n : Nat)
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_bind₁, map_frobeniusPoly, bind₁_frobeniusPolyRat_wittPolynomial,
    map_wittPolynomial]

中文:
定理 bind₁_frobeniusPoly_wittPolynomial
  条件: (n : 自然数)
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_bind₁, map_frobeniusPoly, bind₁_frobeniusPolyRat_wittPolynomial,
    map_wittPolynomial]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, castRingHom, cast_injective, map_frobeniusPoly, map_injective, map_wittPolynomial
-/
theorem bind₁_frobeniusPoly_wittPolynomial (n : Nat) :
    bind₁ (frobeniusPoly p) (wittPolynomial p Int n) = wittPolynomial p Int (n + 1) := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_bind₁, map_frobeniusPoly, bind₁_frobeniusPolyRat_wittPolynomial,
    map_wittPolynomial]

variable {p}

/--
Definition of `frobeniusFun` / `frobeniusFun` 的定义

English:
definition frobeniusFun
  signature: (x : 𝕎 R)
  body: mk p fun n => MvPolynomial.aeval x.coeff (frobeniusPoly p n)

omit hp in

中文:
定义 frobeniusFun
  签名: (x : 𝕎 R)
  定义体: mk p fun n => MvPolynomial.aeval x.coeff (frobeniusPoly p n)

omit hp in

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, frobeniusPoly, x.coeff
-/
def frobeniusFun (x : 𝕎 R) : 𝕎 R :=
  mk p fun n => MvPolynomial.aeval x.coeff (frobeniusPoly p n)

omit hp in
/--
theorem `coeff_frobeniusFun` / 定理 `coeff_frobeniusFun`

English:
theorem coeff_frobeniusFun
  given: (x : 𝕎 R) (n : Nat)
  proof: by
  rw [frobeniusFun]; rw [coeff_mk]

中文:
定理 coeff_frobeniusFun
  条件: (x : 𝕎 R) (n : 自然数)
  证明: by
  rw [frobeniusFun]; rw [coeff_mk]

Depends on / 依赖: coeff_mk, frobeniusFun
-/
theorem coeff_frobeniusFun (x : 𝕎 R) (n : Nat) :
    coeff (frobeniusFun x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n) := by
  rw [frobeniusFun]; rw [coeff_mk]

variable (p) in
/--
Instance `frobeniusFun_isPoly` / 实例 `frobeniusFun_isPoly`

English:
instance frobeniusFun_isPoly
  signature: : IsPoly p fun R _ Rcr => @frobeniusFun p R _ Rcr
  body: ⟨⟨frobeniusPoly p, by intros; funext n; apply coeff_frobeniusFun⟩⟩

@[ghost_simps]

中文:
实例 frobeniusFun_isPoly
  签名: : 是Poly p fun R _ Rcr => @frobeniusFun p R _ Rcr
  定义体: ⟨⟨frobeniusPoly p, by intros; funext n; apply coeff_frobeniusFun⟩⟩

@[ghost_simps]

Depends on / 依赖: coeff_frobeniusFun, frobeniusPoly, intros
-/
instance frobeniusFun_isPoly : IsPoly p fun R _ Rcr => @frobeniusFun p R _ Rcr :=
  ⟨⟨frobeniusPoly p, by intros; funext n; apply coeff_frobeniusFun⟩⟩

@[ghost_simps]
/--
theorem `ghostComponent_frobeniusFun` / 定理 `ghostComponent_frobeniusFun`

English:
theorem ghostComponent_frobeniusFun
  given: (n : Nat) (x : 𝕎 R)
  proof: by
  simp only [ghostComponent_apply, frobeniusFun, coeff_mk, ← bind₁_frobeniusPoly_wittPolynomial,
    aeval_bind₁]

中文:
定理 ghostComponent_frobeniusFun
  条件: (n : 自然数) (x : 𝕎 R)
  证明: by
  simp only [ghostComponent_apply, frobeniusFun, coeff_mk, ← bind₁_frobeniusPoly_wittPolynomial,
    aeval_bind₁]

Depends on / 依赖: coeff_mk, frobeniusFun, ghostComponent_apply
-/
theorem ghostComponent_frobeniusFun (n : Nat) (x : 𝕎 R) :
    ghostComponent n (frobeniusFun x) = ghostComponent (n + 1) x := by
  simp only [ghostComponent_apply, frobeniusFun, coeff_mk, ← bind₁_frobeniusPoly_wittPolynomial,
    aeval_bind₁]

/--
Definition of `frobenius` / `frobenius` 的定义

English:
definition frobenius
  signature: : 𝕎 R ->+* 𝕎 R where
  body: frobeniusFun
  map_zero' := by
    refine IsPoly.ext (IsPoly.comp (hg := frobeniusFun_isPoly p) (hf := WittVector.zeroIsPoly))
      (IsPoly.comp (hg := WittVector.zeroIsPoly) (hf := frobeniusFun_isPoly p))
      ?_ _ 0
    simp only [Function.comp_apply, map_zero, forall_const]
    ghost_simp
  map_one' := by
    refine
      IsPoly.ext (IsPoly.comp (hg := frobeniusFun_isPoly p) (hf := WittVector.oneIsPoly))
        (IsPoly.comp (hg := WittVector.oneIsPoly) (hf := frobeniusFun_isPoly p)) ?_ _ 0
    simp only [Function.comp_apply, map_one, forall_const]
    ghost_simp
  map_add' := by ghost_calc _ _; ghost_simp
  map_mul' := by ghost_calc _ _; ghost_simp

中文:
定义 frobenius
  签名: : 𝕎 R ->+* 𝕎 R where
  定义体: frobeniusFun
  map_zero' := by
    refine IsPoly.ext (IsPoly.comp (hg := frobeniusFun_isPoly p) (hf := WittVector.zeroIsPoly))
      (IsPoly.comp (hg := WittVector.zeroIsPoly) (hf := frobeniusFun_isPoly p))
      ?_ _ 0
    simp only [Function.comp_apply, map_zero, forall_const]
    ghost_simp
  map_one' := by
    refine
      IsPoly.ext (IsPoly.comp (hg := frobeniusFun_isPoly p) (hf := WittVector.oneIsPoly))
        (IsPoly.comp (hg := WittVector.oneIsPoly) (hf := frobeniusFun_isPoly p)) ?_ _ 0
    simp only [Function.comp_apply, map_one, forall_const]
    ghost_simp
  map_add' := by ghost_calc _ _; ghost_simp
  map_mul' := by ghost_calc _ _; ghost_simp

Depends on / 依赖: frobeniusFun
-/
def frobenius : 𝕎 R ->+* 𝕎 R where
  toFun := frobeniusFun
  map_zero' := by
    refine IsPoly.ext (IsPoly.comp (hg := frobeniusFun_isPoly p) (hf := WittVector.zeroIsPoly))
      (IsPoly.comp (hg := WittVector.zeroIsPoly) (hf := frobeniusFun_isPoly p))
      ?_ _ 0
    simp only [Function.comp_apply, map_zero, forall_const]
    ghost_simp
  map_one' := by
    refine
      IsPoly.ext (IsPoly.comp (hg := frobeniusFun_isPoly p) (hf := WittVector.oneIsPoly))
        (IsPoly.comp (hg := WittVector.oneIsPoly) (hf := frobeniusFun_isPoly p)) ?_ _ 0
    simp only [Function.comp_apply, map_one, forall_const]
    ghost_simp
  map_add' := by ghost_calc _ _; ghost_simp
  map_mul' := by ghost_calc _ _; ghost_simp

/--
theorem `coeff_frobenius` / 定理 `coeff_frobenius`

English:
theorem coeff_frobenius
  given: (x : 𝕎 R) (n : Nat)
  proof: coeff_frobeniusFun _ _

@[ghost_simps]

中文:
定理 coeff_frobenius
  条件: (x : 𝕎 R) (n : 自然数)
  证明: coeff_frobeniusFun _ _

@[ghost_simps]

Depends on / 依赖: coeff_frobeniusFun
-/
theorem coeff_frobenius (x : 𝕎 R) (n : Nat) :
    coeff (frobenius x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n) :=
  coeff_frobeniusFun _ _

@[ghost_simps]
/--
theorem `ghostComponent_frobenius` / 定理 `ghostComponent_frobenius`

English:
theorem ghostComponent_frobenius
  given: (n : Nat) (x : 𝕎 R)
  proof: ghostComponent_frobeniusFun _ _

中文:
定理 ghostComponent_frobenius
  条件: (n : 自然数) (x : 𝕎 R)
  证明: ghostComponent_frobeniusFun _ _

Depends on / 依赖: ghostComponent_frobeniusFun
-/
theorem ghostComponent_frobenius (n : Nat) (x : 𝕎 R) :
    ghostComponent n (frobenius x) = ghostComponent (n + 1) x :=
  ghostComponent_frobeniusFun _ _

variable (p)

/--
Instance `frobenius_isPoly` / 实例 `frobenius_isPoly`

English:
instance frobenius_isPoly
  signature: : IsPoly p fun R _Rcr => @frobenius p R _ _Rcr
  body: frobeniusFun_isPoly _

中文:
实例 frobenius_isPoly
  签名: : 是Poly p fun R _Rcr => @frobenius p R _ _Rcr
  定义体: frobeniusFun_isPoly _

Depends on / 依赖: frobeniusFun_isPoly
-/
instance frobenius_isPoly : IsPoly p fun R _Rcr => @frobenius p R _ _Rcr :=
  frobeniusFun_isPoly _

section CharP

variable [CharP R p]

@[simp]
/--
theorem `coeff_frobenius_charP` / 定理 `coeff_frobenius_charP`

English:
theorem coeff_frobenius_charP
  given: (x : 𝕎 R) (n : Nat)
  statement: coeff (frobenius x) n = x.coeff n ^ p
  proof: by
  rw [coeff_frobenius]
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  -- outline of the calculation, proofs follow below
  calc
    aeval (fun k => x.coeff k) (frobeniusPoly p n) =
        aeval (fun k => x.coeff k)
          (MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n)) := ?_
    _ = aeval (fun k => x.coeff k) (X n ^ p : MvPolynomial Nat (ZMod p)) := ?_
    _ = x.coeff n ^ p := ?_
  · conv_rhs => rw [aeval_eq_eval₂Hom, eval₂Hom_map_hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl
  · rw [frobeniusPoly_zmod]
  · rw [map_pow, aeval_X]

中文:
定理 coeff_frobenius_charP
  条件: (x : 𝕎 R) (n : 自然数)
  结论: coeff (frobenius x) n = x.coeff n ^ p
  证明: by
  rw [coeff_frobenius]
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  -- outline of the calculation, proofs follow below
  calc
    aeval (fun k => x.coeff k) (frobeniusPoly p n) =
        aeval (fun k => x.coeff k)
          (MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n)) := ?_
    _ = aeval (fun k => x.coeff k) (X n ^ p : MvPolynomial Nat (ZMod p)) := ?_
    _ = x.coeff n ^ p := ?_
  · conv_rhs => rw [aeval_eq_eval₂Hom, eval₂Hom_map_hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl
  · rw [frobeniusPoly_zmod]
  · rw [map_pow, aeval_X]

Depends on / 依赖: Algebra, ZMod.algebra, algebra, coeff_frobenius
-/
theorem coeff_frobenius_charP (x : 𝕎 R) (n : Nat) : coeff (frobenius x) n = x.coeff n ^ p := by
  rw [coeff_frobenius]
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  -- outline of the calculation, proofs follow below
  calc
    aeval (fun k => x.coeff k) (frobeniusPoly p n) =
        aeval (fun k => x.coeff k)
          (MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n)) := ?_
    _ = aeval (fun k => x.coeff k) (X n ^ p : MvPolynomial Nat (ZMod p)) := ?_
    _ = x.coeff n ^ p := ?_
  · conv_rhs => rw [aeval_eq_eval₂Hom, eval₂Hom_map_hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl
  · rw [frobeniusPoly_zmod]
  · rw [map_pow, aeval_X]

/--
theorem `frobenius_eq_map_frobenius` / 定理 `frobenius_eq_map_frobenius`

English:
theorem frobenius_eq_map_frobenius
  statement: @frobenius p R _ _ = map (_root_.frobenius R p)
  proof: by
  ext (x n)
  simp only [coeff_frobenius_charP, map_coeff, frobenius_def]

@[simp]

中文:
定理 frobenius_eq_map_frobenius
  结论: @frobenius p R _ _ = map (_root_.frobenius R p)
  证明: by
  ext (x n)
  simp only [coeff_frobenius_charP, map_coeff, frobenius_def]

@[simp]

Depends on / 依赖: coeff_frobenius_charP, frobenius_def, map_coeff
-/
theorem frobenius_eq_map_frobenius : @frobenius p R _ _ = map (_root_.frobenius R p) := by
  ext (x n)
  simp only [coeff_frobenius_charP, map_coeff, frobenius_def]

@[simp]
/--
theorem `frobenius_zmodp` / 定理 `frobenius_zmodp`

English:
theorem frobenius_zmodp
  given: (x : 𝕎 (ZMod p))
  statement: frobenius x = x
  proof: by
  simp only [WittVector.ext_iff, coeff_frobenius_charP, ZMod.pow_card,
    forall_const]

中文:
定理 frobenius_zmodp
  条件: (x : 𝕎 (ZMod p))
  结论: frobenius x = x
  证明: by
  simp only [WittVector.ext_iff, coeff_frobenius_charP, ZMod.pow_card,
    forall_const]

Depends on / 依赖: WittVector, WittVector.ext_iff, ZMod.pow_card, coeff_frobenius_charP, ext_iff, forall_const, pow_card
-/
theorem frobenius_zmodp (x : 𝕎 (ZMod p)) : frobenius x = x := by
  simp only [WittVector.ext_iff, coeff_frobenius_charP, ZMod.pow_card,
    forall_const]

variable (R)

/-- `WittVector.frobenius` as an equiv. -/
@[simps -fullyApplied]
/--
Definition of `frobeniusEquiv` / `frobeniusEquiv` 的定义

English:
definition frobeniusEquiv
  signature: [PerfectRing R p]
  body: { (WittVector.frobenius : WittVector p R ->+* WittVector p R) with
    toFun := WittVector.frobenius
    invFun := map (_root_.frobeniusEquiv R p).symm
    left_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobeniusEquiv_symm_apply_frobenius R p _
    right_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobenius_apply_frobeniusEquiv_symm R p _ }

中文:
定义 frobeniusEquiv
  签名: [完美环 R p]
  定义体: { (WittVector.frobenius : WittVector p R ->+* WittVector p R) with
    toFun := WittVector.frobenius
    invFun := map (_root_.frobeniusEquiv R p).symm
    left_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobeniusEquiv_symm_apply_frobenius R p _
    right_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobenius_apply_frobeniusEquiv_symm R p _ }

Depends on / 依赖: WittVector, WittVector.frobenius, _root_, _root_.frobeniusEquiv, frobenius, frobeniusEquiv, frobeniusEquiv_symm_apply_frobenius, frobenius_apply_frobeniusEquiv_symm, frobenius_eq_map_frobenius, invFun, left_inv, right_inv
-/
def frobeniusEquiv [PerfectRing R p] : WittVector p R ≃+* WittVector p R :=
  { (WittVector.frobenius : WittVector p R ->+* WittVector p R) with
    toFun := WittVector.frobenius
    invFun := map (_root_.frobeniusEquiv R p).symm
    left_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobeniusEquiv_symm_apply_frobenius R p _
    right_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobenius_apply_frobeniusEquiv_symm R p _ }

/--
theorem `frobenius_bijective` / 定理 `frobenius_bijective`

English:
theorem frobenius_bijective
  given: [PerfectRing R p]
  proof: (frobeniusEquiv p R).bijective

中文:
定理 frobenius_bijective
  条件: [完美环 R p]
  证明: (frobeniusEquiv p R).bijective

Depends on / 依赖: bijective, frobeniusEquiv
-/
theorem frobenius_bijective [PerfectRing R p] :
    Function.Bijective (@WittVector.frobenius p R _ _) :=
  (frobeniusEquiv p R).bijective

end CharP

end

end WittVector
