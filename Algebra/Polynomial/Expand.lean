/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

## Main definitions

* `Polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `Polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/

@[expose] public section


universe u v w

open Polynomial

open Finset

namespace Polynomial

section CommSemiring

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : Nat)

/--
Definition of `expand` / `expand` 的定义

English:
definition expand
  signature: : R[X] ->ₐ[R] R[X]
  body: { (eval₂RingHom C (X ^ p) : R[X] ->+* R[X]) with commutes' := fun _ => eval₂_C _ _ }

中文:
定义 expand
  签名: : R[X] ->ₐ[R] R[X]
  定义体: { (eval₂RingHom C (X ^ p) : R[X] ->+* R[X]) with commutes' := fun _ => eval₂_C _ _ }

Depends on / 依赖: commutes
-/
noncomputable def expand : R[X] ->ₐ[R] R[X] :=
  { (eval₂RingHom C (X ^ p) : R[X] ->+* R[X]) with commutes' := fun _ => eval₂_C _ _ }

/--
theorem `coe_expand` / 定理 `coe_expand`

English:
theorem coe_expand
  statement: (expand R p : R[X] -> R[X]) = eval₂ C (X ^ p)
  proof: rfl

中文:
定理 coe_expand
  结论: (expand R p : R[X] -> R[X]) = eval₂ C (X ^ p)
  证明: rfl
-/
theorem coe_expand : (expand R p : R[X] -> R[X]) = eval₂ C (X ^ p) :=
  rfl

variable {R}

/--
theorem `expand_eq_comp_X_pow` / 定理 `expand_eq_comp_X_pow`

English:
theorem expand_eq_comp_X_pow
  given: {f : R[X]}
  statement: expand R p f = f.comp (X ^ p)
  proof: rfl

中文:
定理 expand_eq_comp_X_pow
  条件: {f : R[X]}
  结论: expand R p f = f.comp (X ^ p)
  证明: rfl
-/
theorem expand_eq_comp_X_pow {f : R[X]} : expand R p f = f.comp (X ^ p) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `expand_eq_sum` / 定理 `expand_eq_sum`

English:
theorem expand_eq_sum
  given: {f : R[X]}
  statement: expand R p f = f.sum fun e a => C a * (X ^ p) ^ e
  proof: by
  simp [expand, eval₂_eq_sum]

@[simp]

中文:
定理 expand_eq_sum
  条件: {f : R[X]}
  结论: expand R p f = f.求和 fun e a => C a * (X ^ p) ^ e
  证明: by
  simp [expand, eval₂_eq_sum]

@[simp]

Depends on / 依赖: expand
-/
theorem expand_eq_sum {f : R[X]} : expand R p f = f.sum fun e a => C a * (X ^ p) ^ e := by
  simp [expand, eval₂_eq_sum]

@[simp]
/--
theorem `expand_C` / 定理 `expand_C`

English:
theorem expand_C
  given: (r : R)
  statement: expand R p (C r) = C r
  proof: eval₂_C _ _

@[simp]

中文:
定理 expand_C
  条件: (r : R)
  结论: expand R p (C r) = C r
  证明: eval₂_C _ _

@[simp]
-/
theorem expand_C (r : R) : expand R p (C r) = C r :=
  eval₂_C _ _

@[simp]
/--
theorem `expand_X` / 定理 `expand_X`

English:
theorem expand_X
  statement: expand R p X = X ^ p
  proof: eval₂_X _ _

中文:
定理 expand_X
  结论: expand R p X = X ^ p
  证明: eval₂_X _ _
-/
theorem expand_X : expand R p X = X ^ p :=
  eval₂_X _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `expand_monomial` / 定理 `expand_monomial`

English:
theorem expand_monomial
  given: (r : R)
  statement: expand R p (monomial q r) = monomial (q * p) r
  proof: by
  simp_rw [← smul_X_eq_monomial, map_smul, map_pow, expand_X, mul_comm, pow_mul]

中文:
定理 expand_monomial
  条件: (r : R)
  结论: expand R p (monomial q r) = monomial (q * p) r
  证明: by
  simp_rw [← smul_X_eq_monomial, map_smul, map_pow, expand_X, mul_comm, pow_mul]

Depends on / 依赖: expand_X, map_pow, map_smul, mul_comm, pow_mul, simp_rw, smul_X_eq_monomial
-/
theorem expand_monomial (r : R) : expand R p (monomial q r) = monomial (q * p) r := by
  simp_rw [← smul_X_eq_monomial, map_smul, map_pow, expand_X, mul_comm, pow_mul]

/--
theorem `expand_expand` / 定理 `expand_expand`

English:
theorem expand_expand
  given: (f : R[X])
  statement: expand R p (expand R q f) = expand R (p * q) f
  proof: Polynomial.induction_on f (fun r => by simp_rw [expand_C])
    (fun f g ihf ihg => by simp_rw [map_add, ihf, ihg]) fun n r _ => by
    simp_rw [map_mul, expand_C, map_pow, expand_X, map_pow, expand_X, pow_mul]

中文:
定理 expand_expand
  条件: (f : R[X])
  结论: expand R p (expand R q f) = expand R (p * q) f
  证明: Polynomial.induction_on f (fun r => by simp_rw [expand_C])
    (fun f g ihf ihg => by simp_rw [map_add, ihf, ihg]) fun n r _ => by
    simp_rw [map_mul, expand_C, map_pow, expand_X, map_pow, expand_X, pow_mul]

Depends on / 依赖: Polynomial, Polynomial.induction_on, expand_C, expand_X, induction_on, map_add, map_mul, map_pow, pow_mul, simp_rw
-/
theorem expand_expand (f : R[X]) : expand R p (expand R q f) = expand R (p * q) f :=
  Polynomial.induction_on f (fun r => by simp_rw [expand_C])
    (fun f g ihf ihg => by simp_rw [map_add, ihf, ihg]) fun n r _ => by
    simp_rw [map_mul, expand_C, map_pow, expand_X, map_pow, expand_X, pow_mul]

/--
theorem `expand_mul` / 定理 `expand_mul`

English:
theorem expand_mul
  given: (f : R[X])
  statement: expand R (p * q) f = expand R p (expand R q f)
  proof: (expand_expand p q f).symm

@[simp]

中文:
定理 expand_mul
  条件: (f : R[X])
  结论: expand R (p * q) f = expand R p (expand R q f)
  证明: (expand_expand p q f).symm

@[simp]

Depends on / 依赖: expand_expand
-/
theorem expand_mul (f : R[X]) : expand R (p * q) f = expand R p (expand R q f) :=
  (expand_expand p q f).symm

@[simp]
/--
theorem `expand_zero` / 定理 `expand_zero`

English:
theorem expand_zero
  given: (f : R[X])
  statement: expand R 0 f = C (eval 1 f)
  proof: by simp [expand]

@[simp]

中文:
定理 expand_zero
  条件: (f : R[X])
  结论: expand R 0 f = C (eval 1 f)
  证明: by simp [expand]

@[simp]

Depends on / 依赖: expand
-/
theorem expand_zero (f : R[X]) : expand R 0 f = C (eval 1 f) := by simp [expand]

@[simp]
/--
theorem `expand_one` / 定理 `expand_one`

English:
theorem expand_one
  given: (f : R[X])
  statement: expand R 1 f = f
  proof: Polynomial.induction_on f (fun r => by rw [expand_C])
    (fun f g ihf ihg => by rw [map_add, ihf, ihg]) fun n r _ => by
    rw [map_mul]; rw [expand_C]; rw [map_pow]; rw [expand_X]; rw [pow_one]

中文:
定理 expand_one
  条件: (f : R[X])
  结论: expand R 1 f = f
  证明: Polynomial.induction_on f (fun r => by rw [expand_C])
    (fun f g ihf ihg => by rw [map_add, ihf, ihg]) fun n r _ => by
    rw [map_mul]; rw [expand_C]; rw [map_pow]; rw [expand_X]; rw [pow_one]

Depends on / 依赖: Polynomial, Polynomial.induction_on, expand_C, expand_X, induction_on, map_add, map_mul, map_pow, pow_one
-/
theorem expand_one (f : R[X]) : expand R 1 f = f :=
  Polynomial.induction_on f (fun r => by rw [expand_C])
    (fun f g ihf ihg => by rw [map_add, ihf, ihg]) fun n r _ => by
    rw [map_mul]; rw [expand_C]; rw [map_pow]; rw [expand_X]; rw [pow_one]

/--
theorem `expand_pow` / 定理 `expand_pow`

English:
theorem expand_pow
  given: (f : R[X])
  statement: expand R (p ^ q) f = (expand R p)^[q] f
  proof: Nat.recOn q (by rw [pow_zero, expand_one, Function.iterate_zero, id]) fun n ih => by
    rw [Function.iterate_succ_apply']; rw [pow_succ']; rw [expand_mul]; rw [ih]

中文:
定理 expand_pow
  条件: (f : R[X])
  结论: expand R (p ^ q) f = (expand R p)^[q] f
  证明: Nat.recOn q (by rw [pow_zero, expand_one, Function.iterate_zero, id]) fun n ih => by
    rw [Function.iterate_succ_apply']; rw [pow_succ']; rw [expand_mul]; rw [ih]

Depends on / 依赖: Function, Function.iterate_succ_apply, Function.iterate_zero, Nat.recOn, expand_mul, expand_one, iterate_succ_apply, iterate_zero, pow_succ, pow_zero
-/
theorem expand_pow (f : R[X]) : expand R (p ^ q) f = (expand R p)^[q] f :=
  Nat.recOn q (by rw [pow_zero, expand_one, Function.iterate_zero, id]) fun n ih => by
    rw [Function.iterate_succ_apply']; rw [pow_succ']; rw [expand_mul]; rw [ih]

/--
theorem `derivative_expand` / 定理 `derivative_expand`

English:
theorem derivative_expand
  given: (f : R[X])
  statement: Polynomial.derivative (expand R p f) =
  proof: by
  rw [coe_expand]; rw [derivative_eval₂_C]; rw [derivative_pow]; rw [C_eq_natCast]; rw [derivative_X]; rw [mul_one]

中文:
定理 derivative_expand
  条件: (f : R[X])
  结论: 多项式.derivative (expand R p f) =
  证明: by
  rw [coe_expand]; rw [derivative_eval₂_C]; rw [derivative_pow]; rw [C_eq_natCast]; rw [derivative_X]; rw [mul_one]

Depends on / 依赖: C_eq_natCast, coe_expand, derivative_X, derivative_pow, mul_one
-/
theorem derivative_expand (f : R[X]) : Polynomial.derivative (expand R p f) =
    expand R p (Polynomial.derivative f) * (p * (X ^ (p - 1) : R[X])) := by
  rw [coe_expand]; rw [derivative_eval₂_C]; rw [derivative_pow]; rw [C_eq_natCast]; rw [derivative_X]; rw [mul_one]

/--
theorem `coeff_expand` / 定理 `coeff_expand`

English:
theorem coeff_expand
  given: {p : Nat} (hp : 0 < p) (f : R[X]) (n : Nat)
  proof: by
  simp only [expand_eq_sum]
  simp_rw [coeff_sum, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, sum]
  split_ifs with h
  · rw [Finset.sum_eq_single (n / p), Nat.mul_div_cancel' h, if_pos rfl]
    · intro b _ hb2
      rw [if_neg]
      intro hb3
      apply hb2
      rw [← hb3]; rw [Nat.mu

中文:
定理 coeff_expand
  条件: {p : 自然数} (hp : 0 < p) (f : R[X]) (n : 自然数)
  证明: by
  simp only [expand_eq_sum]
  simp_rw [coeff_sum, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, sum]
  split_ifs with h
  · rw [Finset.sum_eq_single (n / p), Nat.mul_div_cancel' h, if_pos rfl]
    · intro b _ hb2
      rw [if_neg]
      intro hb3
      apply hb2
      rw [← hb3]; rw [Nat.mu

Depends on / 依赖: C_mul_X_pow_eq_monomial, Finset, Finset.sum_eq_single, Finset.sum_eq_zero, Nat.mul_div_cancel, Nat.mul_div_cancel_left, coeff_monomial, coeff_sum, expand_eq_sum, hkn.symm, if_neg, if_pos, mul_div_cancel, mul_div_cancel_left, notMem_support_iff, pow_mul, simp_rw, split_ifs, sum_eq_single, sum_eq_zero
-/
theorem coeff_expand {p : Nat} (hp : 0 < p) (f : R[X]) (n : Nat) :
    (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
  simp only [expand_eq_sum]
  simp_rw [coeff_sum, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, sum]
  split_ifs with h
  · rw [Finset.sum_eq_single (n / p), Nat.mul_div_cancel' h, if_pos rfl]
    · intro b _ hb2
      rw [if_neg]
      intro hb3
      apply hb2
      rw [← hb3]; rw [Nat.mul_div_cancel_left b hp]
    · intro hn
      rw [notMem_support_iff.1 hn]
      split_ifs <;> rfl
  · rw [Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    exact fun hkn => h ⟨k, hkn.symm⟩

@[simp]
/--
theorem `coeff_expand_mul` / 定理 `coeff_expand_mul`

English:
theorem coeff_expand_mul
  given: {p : Nat} (hp : 0 < p) (f : R[X]) (n : Nat)
  proof: by
  rw [coeff_expand hp]; rw [if_pos (dvd_mul_left _ _)]; rw [Nat.mul_div_cancel _ hp]

@[simp]

中文:
定理 coeff_expand_mul
  条件: {p : 自然数} (hp : 0 < p) (f : R[X]) (n : 自然数)
  证明: by
  rw [coeff_expand hp]; rw [if_pos (dvd_mul_left _ _)]; rw [Nat.mul_div_cancel _ hp]

@[simp]

Depends on / 依赖: Nat.mul_div_cancel, coeff_expand, dvd_mul_left, if_pos, mul_div_cancel
-/
theorem coeff_expand_mul {p : Nat} (hp : 0 < p) (f : R[X]) (n : Nat) :
    (expand R p f).coeff (n * p) = f.coeff n := by
  rw [coeff_expand hp]; rw [if_pos (dvd_mul_left _ _)]; rw [Nat.mul_div_cancel _ hp]

@[simp]
/--
theorem `coeff_expand_mul'` / 定理 `coeff_expand_mul'`

English:
theorem coeff_expand_mul'
  given: {p : Nat} (hp : 0 < p) (f : R[X]) (n : Nat)
  proof: by rw [mul_comm, coeff_expand_mul hp]

中文:
定理 coeff_expand_mul'
  条件: {p : 自然数} (hp : 0 < p) (f : R[X]) (n : 自然数)
  证明: by rw [mul_comm, coeff_expand_mul hp]

Depends on / 依赖: coeff_expand_mul, mul_comm
-/
theorem coeff_expand_mul' {p : Nat} (hp : 0 < p) (f : R[X]) (n : Nat) :
    (expand R p f).coeff (p * n) = f.coeff n := by rw [mul_comm, coeff_expand_mul hp]

/--
theorem `expand_injective` / 定理 `expand_injective`

English:
theorem expand_injective
  given: {n : Nat} (hn : 0 < n)
  statement: Function.Injective (expand R n)
  proof: fun g g' H =>
  ext fun k => by rw [← coeff_expand_mul hn, H, coeff_expand_mul hn]

中文:
定理 expand_injective
  条件: {n : 自然数} (hn : 0 < n)
  结论: 函数.单射 (expand R n)
  证明: fun g g' H =>
  ext fun k => by rw [← coeff_expand_mul hn, H, coeff_expand_mul hn]
-/
theorem expand_injective {n : Nat} (hn : 0 < n) : Function.Injective (expand R n) := fun g g' H =>
  ext fun k => by rw [← coeff_expand_mul hn, H, coeff_expand_mul hn]

/--
theorem `expand_inj` / 定理 `expand_inj`

English:
theorem expand_inj
  given: {p : Nat} (hp : 0 < p) {f g : R[X]}
  statement: expand R p f = expand R p g ↔ f = g
  proof: (expand_injective hp).eq_iff

中文:
定理 expand_inj
  条件: {p : 自然数} (hp : 0 < p) {f g : R[X]}
  结论: expand R p f = expand R p g ↔ f = g
  证明: (expand_injective hp).eq_iff

Depends on / 依赖: eq_iff, expand_injective
-/
theorem expand_inj {p : Nat} (hp : 0 < p) {f g : R[X]} : expand R p f = expand R p g ↔ f = g :=
  (expand_injective hp).eq_iff

/--
theorem `expand_eq_zero` / 定理 `expand_eq_zero`

English:
theorem expand_eq_zero
  given: {p : Nat} (hp : 0 < p) {f : R[X]}
  statement: expand R p f = 0 ↔ f = 0
  proof: (expand_injective hp).eq_iff' (map_zero _)

中文:
定理 expand_eq_zero
  条件: {p : 自然数} (hp : 0 < p) {f : R[X]}
  结论: expand R p f = 0 ↔ f = 0
  证明: (expand_injective hp).eq_iff' (map_zero _)

Depends on / 依赖: eq_iff, expand_injective, map_zero
-/
theorem expand_eq_zero {p : Nat} (hp : 0 < p) {f : R[X]} : expand R p f = 0 ↔ f = 0 :=
  (expand_injective hp).eq_iff' (map_zero _)

/--
theorem `expand_ne_zero` / 定理 `expand_ne_zero`

English:
theorem expand_ne_zero
  given: {p : Nat} (hp : 0 < p) {f : R[X]}
  statement: expand R p f != 0 ↔ f != 0
  proof: (expand_eq_zero hp).not

中文:
定理 expand_ne_zero
  条件: {p : 自然数} (hp : 0 < p) {f : R[X]}
  结论: expand R p f != 0 ↔ f != 0
  证明: (expand_eq_zero hp).not

Depends on / 依赖: expand_eq_zero
-/
theorem expand_ne_zero {p : Nat} (hp : 0 < p) {f : R[X]} : expand R p f != 0 ↔ f != 0 :=
  (expand_eq_zero hp).not

/--
theorem `expand_eq_C` / 定理 `expand_eq_C`

English:
theorem expand_eq_C
  given: {p : Nat} (hp : 0 < p) {f : R[X]} {r : R}
  statement: expand R p f = C r ↔ f = C r
  proof: by
  rw [← expand_C]; rw [expand_inj hp]; rw [expand_C]

中文:
定理 expand_eq_C
  条件: {p : 自然数} (hp : 0 < p) {f : R[X]} {r : R}
  结论: expand R p f = C r ↔ f = C r
  证明: by
  rw [← expand_C]; rw [expand_inj hp]; rw [expand_C]

Depends on / 依赖: expand_C, expand_inj
-/
theorem expand_eq_C {p : Nat} (hp : 0 < p) {f : R[X]} {r : R} : expand R p f = C r ↔ f = C r := by
  rw [← expand_C]; rw [expand_inj hp]; rw [expand_C]

/--
theorem `natDegree_expand` / 定理 `natDegree_expand`

English:
theorem natDegree_expand
  given: (p : Nat) (f : R[X])
  statement: (expand R p f).natDegree = f.natDegree * p
  proof: by
  rcases p.eq_zero_or_pos with hp | hp
  · rw [hp, coe_expand, pow_zero, mul_zero, ← C_1, eval₂_hom, natDegree_C]
  by_cases hf : f = 0
  · rw [hf, map_zero, natDegree_zero, zero_mul]
  have hf1 : expand R p f != 0 := mt (expand_eq_zero hp).1 hf
  rw [← Nat.cast_inj (R := WithBot Nat)]; rw [← deg

中文:
定理 natDegree_expand
  条件: (p : 自然数) (f : R[X])
  结论: (expand R p f).natDegree = f.natDegree * p
  证明: by
  rcases p.eq_zero_or_pos with hp | hp
  · rw [hp, coe_expand, pow_zero, mul_zero, ← C_1, eval₂_hom, natDegree_C]
  by_cases hf : f = 0
  · rw [hf, map_zero, natDegree_zero, zero_mul]
  have hf1 : expand R p f != 0 := mt (expand_eq_zero hp).1 hf
  rw [← Nat.cast_inj (R := WithBot Nat)]; rw [← deg

Depends on / 依赖: Nat.cast_inj, Nat.div_, WithBot, cast_inj, coe_expand, coeff_eq_zero_of_natDegree_lt, coeff_expand, contrapose, degree_eq_natDegree, degree_le_iff_coeff_zero, div_, eq_zero_or_pos, expand, expand_eq_zero, le_antisymm, map_zero, mul_zero, natDegree_C, natDegree_zero, p.eq_zero_or_pos
-/
theorem natDegree_expand (p : Nat) (f : R[X]) : (expand R p f).natDegree = f.natDegree * p := by
  rcases p.eq_zero_or_pos with hp | hp
  · rw [hp, coe_expand, pow_zero, mul_zero, ← C_1, eval₂_hom, natDegree_C]
  by_cases hf : f = 0
  · rw [hf, map_zero, natDegree_zero, zero_mul]
  have hf1 : expand R p f != 0 := mt (expand_eq_zero hp).1 hf
  rw [← Nat.cast_inj (R := WithBot Nat)]; rw [← degree_eq_natDegree hf1]
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 fun n hn => ?_) ?_
  · rw [coeff_expand hp]
    split_ifs with hpn
    · rw [coeff_eq_zero_of_natDegree_lt]
      contrapose! hn
      norm_cast
      rw [← Nat.div_mul_cancel hpn]
      exact Nat.mul_le_mul_right p hn
    · rfl
  · refine le_degree_of_ne_zero ?_
    rw [coeff_expand_mul hp]; rw [← leadingCoeff]
    exact mt leadingCoeff_eq_zero.1 hf

/--
theorem `leadingCoeff_expand` / 定理 `leadingCoeff_expand`

English:
theorem leadingCoeff_expand
  given: {p : Nat} {f : R[X]} (hp : 0 < p)
  proof: by
  simp_rw [leadingCoeff, natDegree_expand, coeff_expand_mul hp]

中文:
定理 leadingCoeff_expand
  条件: {p : 自然数} {f : R[X]} (hp : 0 < p)
  证明: by
  simp_rw [leadingCoeff, natDegree_expand, coeff_expand_mul hp]

Depends on / 依赖: coeff_expand_mul, leadingCoeff, natDegree_expand, simp_rw
-/
theorem leadingCoeff_expand {p : Nat} {f : R[X]} (hp : 0 < p) :
    (expand R p f).leadingCoeff = f.leadingCoeff := by
  simp_rw [leadingCoeff, natDegree_expand, coeff_expand_mul hp]

/--
theorem `monic_expand_iff` / 定理 `monic_expand_iff`

English:
theorem monic_expand_iff
  given: {p : Nat} {f : R[X]} (hp : 0 < p)
  statement: (expand R p f).Monic ↔ f.Monic
  proof: by
  simp only [Monic, leadingCoeff_expand hp]

alias ⟨_, Monic.expand⟩ := monic_expand_iff

中文:
定理 monic_expand_iff
  条件: {p : 自然数} {f : R[X]} (hp : 0 < p)
  结论: (expand R p f).Monic ↔ f.Monic
  证明: by
  simp only [Monic, leadingCoeff_expand hp]

alias ⟨_, Monic.expand⟩ := monic_expand_iff

Depends on / 依赖: leadingCoeff_expand
-/
theorem monic_expand_iff {p : Nat} {f : R[X]} (hp : 0 < p) : (expand R p f).Monic ↔ f.Monic := by
  simp only [Monic, leadingCoeff_expand hp]

alias ⟨_, Monic.expand⟩ := monic_expand_iff

/--
theorem `map_expand` / 定理 `map_expand`

English:
theorem map_expand
  given: {p : Nat} {f : R ->+* S} {q : R[X]}
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  ext
  rw [coeff_map]; rw [coeff_expand (Nat.pos_of_ne_zero hp)]; rw [coeff_expand (Nat.pos_of_ne_zero hp)]
  split_ifs <;> simp_all

@[simp]

中文:
定理 map_expand
  条件: {p : 自然数} {f : R ->+* S} {q : R[X]}
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  ext
  rw [coeff_map]; rw [coeff_expand (Nat.pos_of_ne_zero hp)]; rw [coeff_expand (Nat.pos_of_ne_zero hp)]
  split_ifs <;> simp_all

@[simp]

Depends on / 依赖: Nat.pos_of_ne_zero, coeff_expand, coeff_map, pos_of_ne_zero, split_ifs
-/
theorem map_expand {p : Nat} {f : R ->+* S} {q : R[X]} :
    map f (expand R p q) = expand S p (map f q) := by
  by_cases hp : p = 0
  · simp [hp]
  ext
  rw [coeff_map]; rw [coeff_expand (Nat.pos_of_ne_zero hp)]; rw [coeff_expand (Nat.pos_of_ne_zero hp)]
  split_ifs <;> simp_all

@[simp]
/--
theorem `expand_eval` / 定理 `expand_eval`

English:
theorem expand_eval
  given: (p : Nat) (P : R[X]) (r : R)
  statement: eval r (expand R p P) = eval (r ^ p) P
  proof: by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add]; rw [eval_add]; rw [eval_add]; rw [hf]; rw [hg]

@[simp]

中文:
定理 expand_eval
  条件: (p : 自然数) (P : R[X]) (r : R)
  结论: eval r (expand R p P) = eval (r ^ p) P
  证明: by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add]; rw [eval_add]; rw [eval_add]; rw [hf]; rw [hg]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.induction_on, eval_add, induction_on, map_add
-/
theorem expand_eval (p : Nat) (P : R[X]) (r : R) : eval r (expand R p P) = eval (r ^ p) P := by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add]; rw [eval_add]; rw [eval_add]; rw [hf]; rw [hg]

@[simp]
/--
theorem `expand_aeval` / 定理 `expand_aeval`

English:
theorem expand_aeval
  given: {A : Type*} [Semiring A] [Algebra R A] (p : Nat) (P : R[X]) (r : A)
  proof: by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add]; rw [aeval_add]; rw [aeval_add]; rw [hf]; rw [hg]

中文:
定理 expand_aeval
  条件: {A : 类型} [半环 A] [代数 R A] (p : 自然数) (P : R[X]) (r : A)
  证明: by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add]; rw [aeval_add]; rw [aeval_add]; rw [hf]; rw [hg]

Depends on / 依赖: Polynomial, Polynomial.induction_on, aeval_add, induction_on, map_add
-/
theorem expand_aeval {A : Type*} [Semiring A] [Algebra R A] (p : Nat) (P : R[X]) (r : A) :
    aeval r (expand R p P) = aeval (r ^ p) P := by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add]; rw [aeval_add]; rw [aeval_add]; rw [hf]; rw [hg]

/--
Definition of `contract` / `contract` 的定义

English:
definition contract
  signature: (p : Nat) (f : R[X])
  body: ∑ n in range (f.natDegree + 1), monomial n (f.coeff (n * p))

中文:
定义 contract
  签名: (p : 自然数) (f : R[X])
  定义体: ∑ n in range (f.natDegree + 1), monomial n (f.coeff (n * p))

Depends on / 依赖: f.coeff, f.natDegree, monomial, natDegree
-/
noncomputable def contract (p : Nat) (f : R[X]) : R[X] :=
  ∑ n in range (f.natDegree + 1), monomial n (f.coeff (n * p))

/--
theorem `coeff_contract` / 定理 `coeff_contract`

English:
theorem coeff_contract
  given: {p : Nat} (hp : p != 0) (f : R[X]) (n : Nat)
  proof: by
  simp only [contract, coeff_monomial, sum_ite_eq', finsetSum_coeff, mem_range, not_lt,
    ite_eq_left_iff]
  intro hn
  apply (coeff_eq_zero_of_natDegree_lt _).symm
  calc
    f.natDegree < f.natDegree + 1 := Nat.lt_succ_self _
    _ <= n * 1 := by simpa only [mul_one] using hn
    _ <= n * p :

中文:
定理 coeff_contract
  条件: {p : 自然数} (hp : p != 0) (f : R[X]) (n : 自然数)
  证明: by
  simp only [contract, coeff_monomial, sum_ite_eq', finsetSum_coeff, mem_range, not_lt,
    ite_eq_left_iff]
  intro hn
  apply (coeff_eq_zero_of_natDegree_lt _).symm
  calc
    f.natDegree < f.natDegree + 1 := Nat.lt_succ_self _
    _ <= n * 1 := by simpa only [mul_one] using hn
    _ <= n * p :

Depends on / 依赖: Nat.lt_succ_self, bot_lt, coeff_eq_zero_of_natDegree_lt, coeff_monomial, contract, f.natDegree, finsetSum_coeff, hp.bot_lt, ite_eq_left_iff, lt_succ_self, mem_range, mul_one, natDegree, not_lt, sum_ite_eq
-/
theorem coeff_contract {p : Nat} (hp : p != 0) (f : R[X]) (n : Nat) :
    (contract p f).coeff n = f.coeff (n * p) := by
  simp only [contract, coeff_monomial, sum_ite_eq', finsetSum_coeff, mem_range, not_lt,
    ite_eq_left_iff]
  intro hn
  apply (coeff_eq_zero_of_natDegree_lt _).symm
  calc
    f.natDegree < f.natDegree + 1 := Nat.lt_succ_self _
    _ <= n * 1 := by simpa only [mul_one] using hn
    _ <= n * p := by gcongr; exact hp.bot_lt

/--
theorem `map_contract` / 定理 `map_contract`

English:
theorem map_contract
  given: {p : Nat} (hp : p != 0) {f : R ->+* S} {q : R[X]}
  proof: ext fun n => by
  simp only [coeff_map, coeff_contract hp]

中文:
定理 map_contract
  条件: {p : 自然数} (hp : p != 0) {f : R ->+* S} {q : R[X]}
  证明: ext fun n => by
  simp only [coeff_map, coeff_contract hp]

Depends on / 依赖: coeff_contract, coeff_map
-/
theorem map_contract {p : Nat} (hp : p != 0) {f : R ->+* S} {q : R[X]} :
    (q.contract p).map f = (q.map f).contract p := ext fun n => by
  simp only [coeff_map, coeff_contract hp]

/--
theorem `contract_expand` / 定理 `contract_expand`

English:
theorem contract_expand
  given: {f : R[X]} (hp : p != 0)
  statement: contract p (expand R p f) = f
  proof: by
  ext
  simp [coeff_contract hp, coeff_expand hp.bot_lt, Nat.mul_div_cancel _ hp.bot_lt]

中文:
定理 contract_expand
  条件: {f : R[X]} (hp : p != 0)
  结论: contract p (expand R p f) = f
  证明: by
  ext
  simp [coeff_contract hp, coeff_expand hp.bot_lt, Nat.mul_div_cancel _ hp.bot_lt]

Depends on / 依赖: Nat.mul_div_cancel, bot_lt, coeff_contract, coeff_expand, hp.bot_lt, mul_div_cancel
-/
theorem contract_expand {f : R[X]} (hp : p != 0) : contract p (expand R p f) = f := by
  ext
  simp [coeff_contract hp, coeff_expand hp.bot_lt, Nat.mul_div_cancel _ hp.bot_lt]

/--
theorem `contract_one` / 定理 `contract_one`

English:
theorem contract_one
  given: {f : R[X]}
  statement: contract 1 f = f
  proof: ext fun n => by rw [coeff_contract one_ne_zero, mul_one]

中文:
定理 contract_one
  条件: {f : R[X]}
  结论: contract 1 f = f
  证明: ext fun n => by rw [coeff_contract one_ne_zero, mul_one]

Depends on / 依赖: coeff_contract, mul_one, one_ne_zero
-/
theorem contract_one {f : R[X]} : contract 1 f = f :=
  ext fun n => by rw [coeff_contract one_ne_zero, mul_one]

/--
theorem `contract_C` / 定理 `contract_C`

English:
theorem contract_C
  given: (r : R)
  statement: contract p (C r) = C r
  proof: by simp [contract]

中文:
定理 contract_C
  条件: (r : R)
  结论: contract p (C r) = C r
  证明: by simp [contract]
-/
@[simp] theorem contract_C (r : R) : contract p (C r) = C r := by simp [contract]

/--
theorem `contract_add` / 定理 `contract_add`

English:
theorem contract_add
  given: {p : Nat} (hp : p != 0) (f g : R[X])
  proof: by
  ext; simp_rw [coeff_add, coeff_contract hp, coeff_add]

中文:
定理 contract_add
  条件: {p : 自然数} (hp : p != 0) (f g : R[X])
  证明: by
  ext; simp_rw [coeff_add, coeff_contract hp, coeff_add]

Depends on / 依赖: coeff_add, coeff_contract, simp_rw
-/
theorem contract_add {p : Nat} (hp : p != 0) (f g : R[X]) :
    contract p (f + g) = contract p f + contract p g := by
  ext; simp_rw [coeff_add, coeff_contract hp, coeff_add]

/--
theorem `contract_mul_expand` / 定理 `contract_mul_expand`

English:
theorem contract_mul_expand
  given: {p : Nat} (hp : p != 0) (f g : R[X])
  proof: by
  ext n
  rw [coeff_contract hp]; rw [coeff_mul]; rw [coeff_mul]; rw [← sum_subset
    (s₁ := (antidiagonal n).image fun x => (x.1 * p]; rw [x.2 * p))]; rw [sum_image]
  · simp_rw [coeff_expand_mul hp.bot_lt, coeff_contract hp]
  · intro x hx y hy eq; simpa only [Prod.ext_iff, Nat.mul_right_cance

中文:
定理 contract_mul_expand
  条件: {p : 自然数} (hp : p != 0) (f g : R[X])
  证明: by
  ext n
  rw [coeff_contract hp]; rw [coeff_mul]; rw [coeff_mul]; rw [← sum_subset
    (s₁ := (antidiagonal n).image fun x => (x.1 * p]; rw [x.2 * p))]; rw [sum_image]
  · simp_rw [coeff_expand_mul hp.bot_lt, coeff_contract hp]
  · intro x hx y hy eq; simpa only [Prod.ext_iff, Nat.mul_right_cance

Depends on / 依赖: Nat.mul_right_cancel_iff, Prod.ext_iff, add_mul, antidiagonal, bot_lt, coeff_contract, coeff_expand_mul, coeff_mul, ext_iff, hp.bot_lt, mem_antidiagonal, mem_image, mul_right_cancel_iff, simp_rw, subset_iff, sum_image, sum_subset
-/
theorem contract_mul_expand {p : Nat} (hp : p != 0) (f g : R[X]) :
    contract p (f * expand R p g) = contract p f * g := by
  ext n
  rw [coeff_contract hp]; rw [coeff_mul]; rw [coeff_mul]; rw [← sum_subset
    (s₁ := (antidiagonal n).image fun x => (x.1 * p]; rw [x.2 * p))]; rw [sum_image]
  · simp_rw [coeff_expand_mul hp.bot_lt, coeff_contract hp]
  · intro x hx y hy eq; simpa only [Prod.ext_iff, Nat.mul_right_cancel_iff hp.bot_lt] using eq
  · simp_rw [subset_iff, mem_image, mem_antidiagonal]; rintro _ ⟨x, rfl, rfl⟩; simp_rw [add_mul]
  simp_rw [mem_image, mem_antidiagonal]
  intro ⟨x, y⟩ eq nex
  by_cases h : p ∣ y
  · obtain ⟨x, rfl⟩ : p ∣ x := (Nat.dvd_add_iff_left h).mpr (eq ▸ dvd_mul_left p n)
    obtain ⟨y, rfl⟩ := h
    refine (nex ⟨⟨x, y⟩, (Nat.mul_right_cancel_iff hp.bot_lt).mp ?_, by simp_rw [mul_comm]⟩).elim
    rw [← eq]; rw [mul_comm]; rw [mul_add]
  · rw [coeff_expand hp.bot_lt, if_neg h, mul_zero]

/--
theorem `isCoprime_expand` / 定理 `isCoprime_expand`

English:
theorem isCoprime_expand
  given: {f g : R[X]} {p : Nat} (hp : p != 0)
  proof: ⟨fun ⟨a, b, eq⟩ => ⟨contract p a, contract p b, by
    simp_rw [← contract_mul_expand hp, ← contract_add hp, eq, ← C_1, contract_C]⟩, (·.map _)⟩

中文:
定理 isCoprime_expand
  条件: {f g : R[X]} {p : 自然数} (hp : p != 0)
  证明: ⟨fun ⟨a, b, eq⟩ => ⟨contract p a, contract p b, by
    simp_rw [← contract_mul_expand hp, ← contract_add hp, eq, ← C_1, contract_C]⟩, (·.map _)⟩
-/
@[simp] theorem isCoprime_expand {f g : R[X]} {p : Nat} (hp : p != 0) :
    IsCoprime (expand R p f) (expand R p g) ↔ IsCoprime f g :=
  ⟨fun ⟨a, b, eq⟩ => ⟨contract p a, contract p b, by
    simp_rw [← contract_mul_expand hp, ← contract_add hp, eq, ← C_1, contract_C]⟩, (·.map _)⟩

section ExpChar

/--
theorem `expand_contract` / 定理 `expand_contract`

English:
theorem expand_contract
  statement: [CharP R p] [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0)
  proof: by
  ext n
  rw [coeff_expand hp.bot_lt]; rw [coeff_contract hp]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · rcases n with - | n
    · exact absurd (dvd_zero p) h
    have := coeff_derivative f n
    rw [hf]; rw [coeff_zero]; rw [zero_eq_mul] at this
    rcases this with h' | _
    · rw [h'

中文:
定理 expand_contract
  结论: [特征p R p] [无零因子 R] {f : R[X]} (hf : 多项式.derivative f = 0)
  证明: by
  ext n
  rw [coeff_expand hp.bot_lt]; rw [coeff_contract hp]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · rcases n with - | n
    · exact absurd (dvd_zero p) h
    have := coeff_derivative f n
    rw [hf]; rw [coeff_zero]; rw [zero_eq_mul] at this
    rcases this with h' | _
    · rw [h'

Depends on / 依赖: CharP.cast_eq_zero_iff, Nat.cast_succ, Nat.div_mul_cancel, absurd, bot_lt, cast_eq_zero_iff, cast_succ, coeff_contract, coeff_derivative, coeff_expand, coeff_zero, div_mul_cancel, dvd_zero, hp.bot_lt, rename_i, split_ifs, zero_eq_mul
-/
theorem expand_contract [CharP R p] [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0)
    (hp : p != 0) : expand R p (contract p f) = f := by
  ext n
  rw [coeff_expand hp.bot_lt]; rw [coeff_contract hp]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · rcases n with - | n
    · exact absurd (dvd_zero p) h
    have := coeff_derivative f n
    rw [hf]; rw [coeff_zero]; rw [zero_eq_mul] at this
    rcases this with h' | _
    · rw [h']
    rename_i _ _ _ h'
    rw [← Nat.cast_succ]; rw [CharP.cast_eq_zero_iff R p] at h'
    exact absurd h' h

variable [ExpChar R p]

/--
theorem `expand_contract'` / 定理 `expand_contract'`

English:
theorem expand_contract'
  given: [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0)
  proof: by
  obtain _ | @⟨_, hprime, hchar⟩ := ‹ExpChar R p›
  · rw [expand_one, contract_one]
  · have := Fact.mk hchar; exact expand_contract p hf hprime.ne_zero

中文:
定理 expand_contract'
  条件: [无零因子 R] {f : R[X]} (hf : 多项式.derivative f = 0)
  证明: by
  obtain _ | @⟨_, hprime, hchar⟩ := ‹ExpChar R p›
  · rw [expand_one, contract_one]
  · have := Fact.mk hchar; exact expand_contract p hf hprime.ne_zero

Depends on / 依赖: ExpChar, Fact.mk, contract_one, expand_contract, expand_one, hprime, hprime.ne_zero, ne_zero
-/
theorem expand_contract' [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0) :
    expand R p (contract p f) = f := by
  obtain _ | @⟨_, hprime, hchar⟩ := ‹ExpChar R p›
  · rw [expand_one, contract_one]
  · have := Fact.mk hchar; exact expand_contract p hf hprime.ne_zero

/--
theorem `map_frobenius_expand` / 定理 `map_frobenius_expand`

English:
theorem map_frobenius_expand
  given: (f : R[X])
  statement: map (frobenius R p) (expand R p f) = f ^ p
  proof: by
  refine f.induction_on' (fun a b ha hb => ?_) fun n a => ?_
  · rw [map_add, Polynomial.map_add, ha, hb, add_pow_expChar]
  · rw [expand_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
      mul_pow, ← C.map_pow, frobenius_def]
    ring

中文:
定理 map_frobenius_expand
  条件: (f : R[X])
  结论: map (frobenius R p) (expand R p f) = f ^ p
  证明: by
  refine f.induction_on' (fun a b ha hb => ?_) fun n a => ?_
  · rw [map_add, Polynomial.map_add, ha, hb, add_pow_expChar]
  · rw [expand_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
      mul_pow, ← C.map_pow, frobenius_def]
    ring

Depends on / 依赖: C.map_pow, C_mul_X_pow_eq_monomial, Polynomial, Polynomial.map_add, add_pow_expChar, expand_monomial, f.induction_on, frobenius_def, induction_on, map_add, map_monomial, map_pow, mul_pow
-/
theorem map_frobenius_expand (f : R[X]) : map (frobenius R p) (expand R p f) = f ^ p := by
  refine f.induction_on' (fun a b ha hb => ?_) fun n a => ?_
  · rw [map_add, Polynomial.map_add, ha, hb, add_pow_expChar]
  · rw [expand_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
      mul_pow, ← C.map_pow, frobenius_def]
    ring

/--
theorem `map_iterateFrobenius_expand` / 定理 `map_iterateFrobenius_expand`

English:
theorem map_iterateFrobenius_expand
  given: (f : R[X]) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

中文:
定理 map_iterateFrobenius_expand
  条件: (f : R[X]) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

Depends on / 依赖: add_comm, conv_lhs, expand_mul, iterateFrobenius_add, iterateFrobenius_one, map_expand, map_frobenius_expand, map_map, n_ih, pow_mul, pow_succ, simp_rw
-/
theorem map_iterateFrobenius_expand (f : R[X]) (n : Nat) :
    map (iterateFrobenius R p n) (expand R (p ^ n) f) = f ^ p ^ n := by
  induction n with
  | zero => simp
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

end ExpChar

end CommSemiring

section rootMultiplicity

variable {R : Type u} [CommRing R] {p n : Nat} [ExpChar R p] {f : R[X]} {r : R}

/--
theorem `rootMultiplicity_expand_pow` / 定理 `rootMultiplicity_expand_pow`

English:
theorem rootMultiplicity_expand_pow
  proof: by
  obtain rfl | h0 := eq_or_ne f 0; · simp
  obtain ⟨g, hg, ndvd⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h0 (r ^ p ^ n)
  rw [dvd_iff_isRoot]; rw [← eval_X (x := r)]; rw [← eval_pow]; rw [← isRoot_comp]; rw [← expand_eq_comp_X_pow] at ndvd
  conv_lhs => rw [hg, map_mul, map_pow, map_s

中文:
定理 rootMultiplicity_expand_pow
  证明: by
  obtain rfl | h0 := eq_or_ne f 0; · simp
  obtain ⟨g, hg, ndvd⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h0 (r ^ p ^ n)
  rw [dvd_iff_isRoot]; rw [← eval_X (x := r)]; rw [← eval_pow]; rw [← isRoot_comp]; rw [← expand_eq_comp_X_pow] at ndvd
  conv_lhs => rw [hg, map_mul, map_pow, map_s

Depends on / 依赖: conv_lhs, dvd_iff_isRoot, eq_or_ne, eval_X, eval_pow, exists_eq_pow_rootMultiplicity_mul_and_not_dvd, expChar_pow_pos, expand_C, expand_X, expand_eq_comp_X_pow, expand_ne_zero, f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd, isRoot_comp, map_mul, map_pow, map_sub, mul_comm, pow_mul, right_ne_zero_of_mul, rootMultiplicity_eq_ze
-/
theorem rootMultiplicity_expand_pow :
    (expand R (p ^ n) f).rootMultiplicity r = p ^ n * f.rootMultiplicity (r ^ p ^ n) := by
  obtain rfl | h0 := eq_or_ne f 0; · simp
  obtain ⟨g, hg, ndvd⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h0 (r ^ p ^ n)
  rw [dvd_iff_isRoot]; rw [← eval_X (x := r)]; rw [← eval_pow]; rw [← isRoot_comp]; rw [← expand_eq_comp_X_pow] at ndvd
  conv_lhs => rw [hg, map_mul, map_pow, map_sub, expand_X, expand_C, map_pow, ← sub_pow_expChar_pow,
    ← pow_mul, mul_comm, rootMultiplicity_mul_X_sub_C_pow (expand_ne_zero (expChar_pow_pos R p n)
.mpr right_ne_zero_of_mul hg ▸ h0), rootMultiplicity_eq_zero ndvd, zero_add]

/--
theorem `rootMultiplicity_expand` / 定理 `rootMultiplicity_expand`

English:
theorem rootMultiplicity_expand
  proof: by
  rw [← pow_one p]; rw [rootMultiplicity_expand_pow]

中文:
定理 rootMultiplicity_expand
  证明: by
  rw [← pow_one p]; rw [rootMultiplicity_expand_pow]

Depends on / 依赖: pow_one, rootMultiplicity_expand_pow
-/
theorem rootMultiplicity_expand :
    (expand R p f).rootMultiplicity r = p * f.rootMultiplicity (r ^ p) := by
  rw [← pow_one p]; rw [rootMultiplicity_expand_pow]

end rootMultiplicity

section IsDomain

variable (R : Type u) [CommRing R] [IsDomain R]

/--
theorem `isLocalHom_expand` / 定理 `isLocalHom_expand`

English:
theorem isLocalHom_expand
  given: {p : Nat} (hp : 0 < p)
  statement: IsLocalHom (expand R p)
  proof: by
  refine ⟨fun f hf1 => ?_⟩
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit hf1)
  rw [coeff_expand hp]; rw [if_pos (dvd_zero _)]; rw [p.zero_div] at hf2
  rw [hf2]; rw [isUnit_C] at hf1; rw [expand_eq_C hp] at hf2; rwa [hf2, isUnit_C]

中文:
定理 isLocalHom_expand
  条件: {p : 自然数} (hp : 0 < p)
  结论: 是Local态射 (expand R p)
  证明: by
  refine ⟨fun f hf1 => ?_⟩
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit hf1)
  rw [coeff_expand hp]; rw [if_pos (dvd_zero _)]; rw [p.zero_div] at hf2
  rw [hf2]; rw [isUnit_C] at hf1; rw [expand_eq_C hp] at hf2; rwa [hf2, isUnit_C]

Depends on / 依赖: coeff_expand, degree_eq_zero_of_isUnit, dvd_zero, eq_C_of_degree_eq_zero, expand_eq_C, if_pos, isUnit_C, p.zero_div, zero_div
-/
theorem isLocalHom_expand {p : Nat} (hp : 0 < p) : IsLocalHom (expand R p) := by
  refine ⟨fun f hf1 => ?_⟩
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit hf1)
  rw [coeff_expand hp]; rw [if_pos (dvd_zero _)]; rw [p.zero_div] at hf2
  rw [hf2]; rw [isUnit_C] at hf1; rw [expand_eq_C hp] at hf2; rwa [hf2, isUnit_C]

variable {R}

/--
theorem `of_irreducible_expand` / 定理 `of_irreducible_expand`

English:
theorem of_irreducible_expand
  given: {p : Nat} (hp : p != 0) {f : R[X]} (hf : Irreducible (expand R p f))
  proof: let _ := isLocalHom_expand R hp.bot_lt
  hf.of_map

中文:
定理 of_irreducible_expand
  条件: {p : 自然数} (hp : p != 0) {f : R[X]} (hf : 不可约 (expand R p f))
  证明: let _ := isLocalHom_expand R hp.bot_lt
  hf.of_map

Depends on / 依赖: bot_lt, hf.of_map, hp.bot_lt, isLocalHom_expand, of_map
-/
theorem of_irreducible_expand {p : Nat} (hp : p != 0) {f : R[X]} (hf : Irreducible (expand R p f)) :
    Irreducible f :=
  let _ := isLocalHom_expand R hp.bot_lt
  hf.of_map

/--
theorem `of_irreducible_expand_pow` / 定理 `of_irreducible_expand_pow`

English:
theorem of_irreducible_expand_pow
  given: {p : Nat} (hp : p != 0) {f : R[X]} {n : Nat}
  proof: Nat.recOn n (fun hf => by rwa [pow_zero, expand_one] at hf) fun n ih hf =>
ih of_irreducible_expand hp by
      rw [pow_succ'] at hf
      rwa [expand_expand]

中文:
定理 of_irreducible_expand_pow
  条件: {p : 自然数} (hp : p != 0) {f : R[X]} {n : 自然数}
  证明: Nat.recOn n (fun hf => by rwa [pow_zero, expand_one] at hf) fun n ih hf =>
ih of_irreducible_expand hp by
      rw [pow_succ'] at hf
      rwa [expand_expand]

Depends on / 依赖: Nat.recOn, expand_expand, expand_one, of_irreducible_expand, pow_succ, pow_zero
-/
theorem of_irreducible_expand_pow {p : Nat} (hp : p != 0) {f : R[X]} {n : Nat} :
    Irreducible (expand R (p ^ n) f) -> Irreducible f :=
  Nat.recOn n (fun hf => by rwa [pow_zero, expand_one] at hf) fun n ih hf =>
ih of_irreducible_expand hp by
      rw [pow_succ'] at hf
      rwa [expand_expand]

end IsDomain

end Polynomial
