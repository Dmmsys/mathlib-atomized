/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.RingTheory.PowerSeries.Basic

/-!

# Formal power series in one variable - Truncation

`PowerSeries.trunc n φ` truncates a (univariate) formal power series
to the polynomial that has the same coefficients as `φ`, for all `m < n`,
and `0` otherwise.

-/

@[expose] public section

noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section Trunc
variable [Semiring R]
open Finset Nat

set_option backward.privateInPublic true in
/--
Definition of `truncAux` / `truncAux` 的定义

English:
definition truncAux
  signature: (n : Nat) (φ : R⟦X⟧)
  body: ∑ m in Ico 0 n, Polynomial.monomial m (coeff m φ)

中文:
定义 truncAux
  签名: (n : 自然数) (φ : R⟦X⟧)
  定义体: ∑ m in Ico 0 n, Polynomial.monomial m (coeff m φ)
-/
private def truncAux (n : Nat) (φ : R⟦X⟧) : R[X] :=
  ∑ m in Ico 0 n, Polynomial.monomial m (coeff m φ)

/--
theorem `coeff_truncAux` / 定理 `coeff_truncAux`

English:
theorem coeff_truncAux
  given: (m) (n) (φ : R⟦X⟧)
  proof: by
  simp [truncAux, Polynomial.coeff_monomial]

中文:
定理 coeff_truncAux
  条件: (m) (n) (φ : R⟦X⟧)
  证明: by
  simp [truncAux, Polynomial.coeff_monomial]
-/
private theorem coeff_truncAux (m) (n) (φ : R⟦X⟧) :
    (truncAux n φ).coeff m = if m < n then coeff m φ else 0 := by
  simp [truncAux, Polynomial.coeff_monomial]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `trunc` / `trunc` 的定义

English:
definition trunc
  signature: (n : Nat)
  body: truncAux n
  map_add' φ ψ := Polynomial.ext fun m => by
    simp only [coeff_truncAux, Polynomial.coeff_add]
    split_ifs with H
    · rfl
    · rw [zero_add]
  map_smul' t φ := by ext; simp [truncAux, Polynomial.coeff_monomial]

中文:
定义 trunc
  签名: (n : 自然数)
  定义体: truncAux n
  map_add' φ ψ := Polynomial.ext fun m => by
    simp only [coeff_truncAux, Polynomial.coeff_add]
    split_ifs with H
    · rfl
    · rw [zero_add]
  map_smul' t φ := by ext; simp [truncAux, Polynomial.coeff_monomial]

Depends on / 依赖: truncAux
-/
def trunc (n : Nat) : R⟦X⟧ ->ₗ[R] R[X] where
  toFun := truncAux n
  map_add' φ ψ := Polynomial.ext fun m => by
    simp only [coeff_truncAux, Polynomial.coeff_add]
    split_ifs with H
    · rfl
    · rw [zero_add]
  map_smul' t φ := by ext; simp [truncAux, Polynomial.coeff_monomial]

/--
lemma `trunc_apply` / 引理 `trunc_apply`

English:
lemma trunc_apply
  given: (n : Nat) (φ : R⟦X⟧)
  proof: rfl

中文:
引理 trunc_apply
  条件: (n : 自然数) (φ : R⟦X⟧)
  证明: rfl
-/
lemma trunc_apply (n : Nat) (φ : R⟦X⟧) :
    trunc n φ = ∑ m in Ico 0 n, Polynomial.monomial m (coeff m φ) := rfl

/--
theorem `coeff_trunc` / 定理 `coeff_trunc`

English:
theorem coeff_trunc
  given: (m) (n) (φ : R⟦X⟧)
  proof: by
  simp [trunc, coeff_truncAux]

@[simp]

中文:
定理 coeff_trunc
  条件: (m) (n) (φ : R⟦X⟧)
  证明: by
  simp [trunc, coeff_truncAux]

@[simp]

Depends on / 依赖: coeff_truncAux
-/
theorem coeff_trunc (m) (n) (φ : R⟦X⟧) :
    (trunc n φ).coeff m = if m < n then coeff m φ else 0 := by
  simp [trunc, coeff_truncAux]

@[simp]
/--
theorem `trunc_one` / 定理 `trunc_one`

English:
theorem trunc_one
  given: (n)
  statement: trunc (n + 1) (1 : R⟦X⟧) = 1
  proof: Polynomial.ext fun m => by
    grind [PowerSeries.coeff_trunc, PowerSeries.coeff_one, Polynomial.coeff_one]

@[simp]

中文:
定理 trunc_one
  条件: (n)
  结论: trunc (n + 1) (1 : R⟦X⟧) = 1
  证明: Polynomial.ext fun m => by
    grind [PowerSeries.coeff_trunc, PowerSeries.coeff_one, Polynomial.coeff_one]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.coeff_one, Polynomial.ext, PowerSeries, PowerSeries.coeff_one, PowerSeries.coeff_trunc, coeff_one, coeff_trunc
-/
theorem trunc_one (n) : trunc (n + 1) (1 : R⟦X⟧) = 1 :=
  Polynomial.ext fun m => by
    grind [PowerSeries.coeff_trunc, PowerSeries.coeff_one, Polynomial.coeff_one]

@[simp]
/--
theorem `trunc_C` / 定理 `trunc_C`

English:
theorem trunc_C
  given: (n) (a : R)
  statement: trunc (n + 1) (C a) = Polynomial.C a
  proof: Polynomial.ext fun m => by
    rw [coeff_trunc]; rw [coeff_C]; rw [Polynomial.coeff_C]
    split_ifs with H <;> first | rfl | try simp_all

中文:
定理 trunc_C
  条件: (n) (a : R)
  结论: trunc (n + 1) (C a) = Polynomial.C a
  证明: Polynomial.ext fun m => by
    rw [coeff_trunc]; rw [coeff_C]; rw [Polynomial.coeff_C]
    split_ifs with H <;> first | rfl | try simp_all

Depends on / 依赖: Polynomial, Polynomial.coeff_C, Polynomial.ext, coeff_C, coeff_trunc, split_ifs
-/
theorem trunc_C (n) (a : R) : trunc (n + 1) (C a) = Polynomial.C a :=
  Polynomial.ext fun m => by
    rw [coeff_trunc]; rw [coeff_C]; rw [Polynomial.coeff_C]
    split_ifs with H <;> first | rfl | try simp_all

/--
theorem `trunc_succ` / 定理 `trunc_succ`

English:
theorem trunc_succ
  given: (f : R⟦X⟧) (n : Nat)
  proof: by
  rw [trunc_apply]; rw [Ico_zero_eq_range]; rw [sum_range_succ]; rw [trunc_apply]; rw [Ico_zero_eq_range]

中文:
定理 trunc_succ
  条件: (f : R⟦X⟧) (n : 自然数)
  证明: by
  rw [trunc_apply]; rw [Ico_zero_eq_range]; rw [sum_range_succ]; rw [trunc_apply]; rw [Ico_zero_eq_range]

Depends on / 依赖: Ico_zero_eq_range, sum_range_succ, trunc_apply
-/
theorem trunc_succ (f : R⟦X⟧) (n : Nat) :
    trunc n.succ f = trunc n f + Polynomial.monomial n (coeff n f) := by
  rw [trunc_apply]; rw [Ico_zero_eq_range]; rw [sum_range_succ]; rw [trunc_apply]; rw [Ico_zero_eq_range]

/--
theorem `natDegree_trunc_lt` / 定理 `natDegree_trunc_lt`

English:
theorem natDegree_trunc_lt
  given: (f : R⟦X⟧) (n)
  statement: (trunc (n + 1) f).natDegree < n + 1
  proof: by
  simp +contextual [natDegree_le_iff_coeff_eq_zero, coeff_trunc]

中文:
定理 natDegree_trunc_lt
  条件: (f : R⟦X⟧) (n)
  结论: (trunc (n + 1) f).natDegree < n + 1
  证明: by
  simp +contextual [natDegree_le_iff_coeff_eq_zero, coeff_trunc]

Depends on / 依赖: coeff_trunc, contextual, natDegree_le_iff_coeff_eq_zero
-/
theorem natDegree_trunc_lt (f : R⟦X⟧) (n) : (trunc (n + 1) f).natDegree < n + 1 := by
  simp +contextual [natDegree_le_iff_coeff_eq_zero, coeff_trunc]

/--
lemma `trunc_zero'` / 引理 `trunc_zero'`

English:
lemma trunc_zero'
  given: {f : R⟦X⟧}
  statement: trunc 0 f = 0
  proof: rfl

中文:
引理 trunc_zero'
  条件: {f : R⟦X⟧}
  结论: trunc 0 f = 0
  证明: rfl
-/
@[simp] lemma trunc_zero' {f : R⟦X⟧} : trunc 0 f = 0 := rfl

/--
theorem `degree_trunc_lt` / 定理 `degree_trunc_lt`

English:
theorem degree_trunc_lt
  given: (f : R⟦X⟧) (n)
  statement: (trunc n f).degree < n
  proof: by
  simp +contextual [degree_lt_iff_coeff_zero, coeff_trunc]

中文:
定理 degree_trunc_lt
  条件: (f : R⟦X⟧) (n)
  结论: (trunc n f).degree < n
  证明: by
  simp +contextual [degree_lt_iff_coeff_zero, coeff_trunc]

Depends on / 依赖: LightProfinite, LightProfinite.epi_iff_surjective, coeff_trunc, contextual, degree_lt_iff_coeff_zero, epi_iff_surjective, hy.symm
-/
theorem degree_trunc_lt (f : R⟦X⟧) (n) : (trunc n f).degree < n := by
  simp +contextual [degree_lt_iff_coeff_zero, coeff_trunc]

/--
theorem `eval₂_trunc_eq_sum_range` / 定理 `eval₂_trunc_eq_sum_range`

English:
theorem eval₂_trunc_eq_sum_range
  given: {S : Type*} [Semiring S] (s : S) (G : R ->+* S) (n) (f : R⟦X⟧)
  proof: by
  cases n with
  | zero =>
    rw [trunc_zero']; rw [range_zero]; rw [sum_empty]; rw [eval₂_zero]
  | succ n =>
    have := natDegree_trunc_lt f n
    rw [eval₂_eq_sum_range' (hn := this)]
    apply sum_congr rfl
    intro _ h
    rw [mem_range] at h
    congr
    rw [coeff_trunc]; rw [if_pos h]

中文:
定理 eval₂_trunc_eq_sum_range
  条件: {S : 类型} [Semiring S] (s : S) (G : R ->+* S) (n) (f : R⟦X⟧)
  证明: by
  cases n with
  | zero =>
    rw [trunc_zero']; rw [range_zero]; rw [sum_empty]; rw [eval₂_zero]
  | succ n =>
    have := natDegree_trunc_lt f n
    rw [eval₂_eq_sum_range' (hn := this)]
    apply sum_congr rfl
    intro _ h
    rw [mem_range] at h
    congr
    rw [coeff_trunc]; rw [if_pos h]

Depends on / 依赖: LightProfinite, LightProfinite.epi_iff_surjective, coeff_trunc, epi_iff_surjective, if_pos, mem_range, natDegree_trunc_lt, range_zero, sum_congr, sum_empty, trunc_zero
-/
theorem eval₂_trunc_eq_sum_range {S : Type*} [Semiring S] (s : S) (G : R ->+* S) (n) (f : R⟦X⟧) :
    (trunc n f).eval₂ G s = ∑ i in range n, G (coeff i f) * s ^ i := by
  cases n with
  | zero =>
    rw [trunc_zero']; rw [range_zero]; rw [sum_empty]; rw [eval₂_zero]
  | succ n =>
    have := natDegree_trunc_lt f n
    rw [eval₂_eq_sum_range' (hn := this)]
    apply sum_congr rfl
    intro _ h
    rw [mem_range] at h
    congr
    rw [coeff_trunc]; rw [if_pos h]

/--
theorem `trunc_X` / 定理 `trunc_X`

English:
theorem trunc_X
  given: (n)
  statement: trunc (n + 2) X = (Polynomial.X : R[X])
  proof: by
  ext d
  rw [coeff_trunc]; rw [coeff_X]
  split_ifs with h₁ h₂
  · rw [h₂, coeff_X_one]
  · rw [coeff_X_of_ne_one h₂]
  · rw [coeff_X_of_ne_one]
    intro hd
    apply h₁
    rw [hd]
    exact n.one_lt_succ_succ

中文:
定理 trunc_X
  条件: (n)
  结论: trunc (n + 2) X = (Polynomial.X : R[X])
  证明: by
  ext d
  rw [coeff_trunc]; rw [coeff_X]
  split_ifs with h₁ h₂
  · rw [h₂, coeff_X_one]
  · rw [coeff_X_of_ne_one h₂]
  · rw [coeff_X_of_ne_one]
    intro hd
    apply h₁
    rw [hd]
    exact n.one_lt_succ_succ
-/
@[simp] theorem trunc_X (n) : trunc (n + 2) X = (Polynomial.X : R[X]) := by
  ext d
  rw [coeff_trunc]; rw [coeff_X]
  split_ifs with h₁ h₂
  · rw [h₂, coeff_X_one]
  · rw [coeff_X_of_ne_one h₂]
  · rw [coeff_X_of_ne_one]
    intro hd
    apply h₁
    rw [hd]
    exact n.one_lt_succ_succ

/--
lemma `trunc_X_of` / 引理 `trunc_X_of`

English:
lemma trunc_X_of
  given: {n : Nat} (hn : 2 <= n)
  statement: trunc n X = (Polynomial.X : R[X])
  proof: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact trunc_X n

@[simp]

中文:
引理 trunc_X_of
  条件: {n : 自然数} (hn : 2 <= n)
  结论: trunc n X = (Polynomial.X : R[X])
  证明: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact trunc_X n

@[simp]

Depends on / 依赖: Nat.exists_eq_add_of_le, exists_eq_add_of_le, trunc_X
-/
lemma trunc_X_of {n : Nat} (hn : 2 <= n) : trunc n X = (Polynomial.X : R[X]) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact trunc_X n

@[simp]
/--
lemma `trunc_one_left` / 引理 `trunc_one_left`

English:
lemma trunc_one_left
  given: (p : R⟦X⟧)
  statement: trunc (R := R) 1 p = .C (coeff 0 p)
  proof: by
  ext i; simp +contextual [coeff_trunc, Polynomial.coeff_C]

中文:
引理 trunc_one_left
  条件: (p : R⟦X⟧)
  结论: trunc (R := R) 1 p = .C (coeff 0 p)
  证明: by
  ext i; simp +contextual [coeff_trunc, Polynomial.coeff_C]

Depends on / 依赖: Polynomial, Polynomial.coeff_C, coeff_C, coeff_trunc, contextual
-/
lemma trunc_one_left (p : R⟦X⟧) : trunc (R := R) 1 p = .C (coeff 0 p) := by
  ext i; simp +contextual [coeff_trunc, Polynomial.coeff_C]

/--
lemma `trunc_one_X` / 引理 `trunc_one_X`

English:
lemma trunc_one_X
  statement: trunc (R := R) 1 X = 0
  proof: by simp

@[simp]

中文:
引理 trunc_one_X
  结论: trunc (R := R) 1 X = 0
  证明: by simp

@[simp]
-/
lemma trunc_one_X : trunc (R := R) 1 X = 0 := by simp

@[simp]
/--
lemma `trunc_C_mul` / 引理 `trunc_C_mul`

English:
lemma trunc_C_mul
  given: (n : Nat) (r : R) (f : R⟦X⟧)
  statement: trunc n (C r * f) = .C r * trunc n f
  proof: by
  ext i; simp [coeff_trunc]

@[simp]

中文:
引理 trunc_C_mul
  条件: (n : 自然数) (r : R) (f : R⟦X⟧)
  结论: trunc n (C r * f) = .C r * trunc n f
  证明: by
  ext i; simp [coeff_trunc]

@[simp]

Depends on / 依赖: coeff_trunc
-/
lemma trunc_C_mul (n : Nat) (r : R) (f : R⟦X⟧) : trunc n (C r * f) = .C r * trunc n f := by
  ext i; simp [coeff_trunc]

@[simp]
/--
lemma `trunc_mul_C` / 引理 `trunc_mul_C`

English:
lemma trunc_mul_C
  given: (n : Nat) (f : R⟦X⟧) (r : R)
  statement: trunc n (f * C r) = trunc n f * .C r
  proof: by
  ext i; simp [coeff_trunc]

中文:
引理 trunc_mul_C
  条件: (n : 自然数) (f : R⟦X⟧) (r : R)
  结论: trunc n (f * C r) = trunc n f * .C r
  证明: by
  ext i; simp [coeff_trunc]

Depends on / 依赖: coeff_trunc
-/
lemma trunc_mul_C (n : Nat) (f : R⟦X⟧) (r : R) : trunc n (f * C r) = trunc n f * .C r := by
  ext i; simp [coeff_trunc]

/--
lemma `eq_shift_mul_X_pow_add_trunc` / 引理 `eq_shift_mul_X_pow_add_trunc`

English:
lemma eq_shift_mul_X_pow_add_trunc
  given: (n : Nat) (f : R⟦X⟧)
  proof: by
  ext j
  rw [map_add]; rw [Polynomial.coeff_coe]; rw [coeff_mul_X_pow']; rw [coeff_trunc]
  simp_rw [← not_le, ite_not, ite_add_ite]
  simp +contextual

中文:
引理 eq_shift_mul_X_pow_add_trunc
  条件: (n : 自然数) (f : R⟦X⟧)
  证明: by
  ext j
  rw [map_add]; rw [Polynomial.coeff_coe]; rw [coeff_mul_X_pow']; rw [coeff_trunc]
  simp_rw [← not_le, ite_not, ite_add_ite]
  simp +contextual

Depends on / 依赖: Polynomial, Polynomial.coeff_coe, coeff_coe, coeff_mul_X_pow, coeff_trunc, contextual, ite_add_ite, ite_not, map_add, not_le, simp_rw
-/
lemma eq_shift_mul_X_pow_add_trunc (n : Nat) (f : R⟦X⟧) :
    f = (mk fun i => coeff (i + n) f) * X ^ n + (f.trunc n : R⟦X⟧) := by
  ext j
  rw [map_add]; rw [Polynomial.coeff_coe]; rw [coeff_mul_X_pow']; rw [coeff_trunc]
  simp_rw [← not_le, ite_not, ite_add_ite]
  simp +contextual

/--
lemma `eq_X_pow_mul_shift_add_trunc` / 引理 `eq_X_pow_mul_shift_add_trunc`

English:
lemma eq_X_pow_mul_shift_add_trunc
  given: (n : Nat) (f : R⟦X⟧)
  proof: by
  rw [← (commute_X_pow _ n).eq]; rw [← eq_shift_mul_X_pow_add_trunc]

中文:
引理 eq_X_pow_mul_shift_add_trunc
  条件: (n : 自然数) (f : R⟦X⟧)
  证明: by
  rw [← (commute_X_pow _ n).eq]; rw [← eq_shift_mul_X_pow_add_trunc]

Depends on / 依赖: commute_X_pow, eq_shift_mul_X_pow_add_trunc
-/
lemma eq_X_pow_mul_shift_add_trunc (n : Nat) (f : R⟦X⟧) :
    f = X ^ n * (mk fun i => coeff (i + n) f) + (f.trunc n : R⟦X⟧) := by
  rw [← (commute_X_pow _ n).eq]; rw [← eq_shift_mul_X_pow_add_trunc]

/--
lemma `monomial_eq_C_mul_X_pow` / 引理 `monomial_eq_C_mul_X_pow`

English:
lemma monomial_eq_C_mul_X_pow
  given: (r : R) (n : Nat)
  statement: monomial n r = C r * X ^ n
  proof: by
  ext; simp [coeff_X_pow, coeff_monomial]

@[simp]

中文:
引理 monomial_eq_C_mul_X_pow
  条件: (r : R) (n : 自然数)
  结论: monomial n r = C r * X ^ n
  证明: by
  ext; simp [coeff_X_pow, coeff_monomial]

@[simp]

Depends on / 依赖: coeff_X_pow, coeff_monomial
-/
lemma monomial_eq_C_mul_X_pow (r : R) (n : Nat) : monomial n r = C r * X ^ n := by
  ext; simp [coeff_X_pow, coeff_monomial]

@[simp]
/--
lemma `trunc_X_pow_self_mul` / 引理 `trunc_X_pow_self_mul`

English:
lemma trunc_X_pow_self_mul
  given: (n : Nat) (p : R⟦X⟧)
  statement: (X ^ n * p).trunc n = 0
  proof: by
  ext; simp +contextual [coeff_trunc, coeff_X_pow_mul']

中文:
引理 trunc_X_pow_self_mul
  条件: (n : 自然数) (p : R⟦X⟧)
  结论: (X ^ n * p).trunc n = 0
  证明: by
  ext; simp +contextual [coeff_trunc, coeff_X_pow_mul']

Depends on / 依赖: coeff_X_pow_mul, coeff_trunc, contextual
-/
lemma trunc_X_pow_self_mul (n : Nat) (p : R⟦X⟧) : (X ^ n * p).trunc n = 0 := by
  ext; simp +contextual [coeff_trunc, coeff_X_pow_mul']

end Trunc

section Trunc
/-
Lemmas in this section involve the coercion `R[X] → R⟦X⟧`, so they may only be stated in the case
`R` is commutative. This is because the coercion is an `R`-algebra map.
-/
variable {R : Type*} [CommSemiring R]

open Nat hiding pow_succ pow_zero
open Finset Finset.Nat

/--
theorem `trunc_trunc_of_le` / 定理 `trunc_trunc_of_le`

English:
theorem trunc_trunc_of_le
  given: {n m} (f : R⟦X⟧) (hnm : n <= m := by rfl)
  proof: by
  ext d
  rw [coeff_trunc]; rw [coeff_trunc]; rw [coeff_coe]
  split_ifs with h
  · rw [coeff_trunc, if_pos <| lt_of_lt_of_le h hnm]
  · rfl

中文:
定理 trunc_trunc_of_le
  条件: {n m} (f : R⟦X⟧) (hnm : n <= m := by rfl)
  证明: by
  ext d
  rw [coeff_trunc]; rw [coeff_trunc]; rw [coeff_coe]
  split_ifs with h
  · rw [coeff_trunc, if_pos <| lt_of_lt_of_le h hnm]
  · rfl

Depends on / 依赖: coeff_coe, coeff_trunc, if_pos, lt_of_lt_of_le, split_ifs
-/
theorem trunc_trunc_of_le {n m} (f : R⟦X⟧) (hnm : n <= m := by rfl) :
    trunc n ↑(trunc m f) = trunc n f := by
  ext d
  rw [coeff_trunc]; rw [coeff_trunc]; rw [coeff_coe]
  split_ifs with h
  · rw [coeff_trunc, if_pos <| lt_of_lt_of_le h hnm]
  · rfl

/--
theorem `trunc_trunc` / 定理 `trunc_trunc`

English:
theorem trunc_trunc
  given: {n} (f : R⟦X⟧)
  statement: trunc n ↑(trunc n f) = trunc n f
  proof: trunc_trunc_of_le f

中文:
定理 trunc_trunc
  条件: {n} (f : R⟦X⟧)
  结论: trunc n ↑(trunc n f) = trunc n f
  证明: trunc_trunc_of_le f
-/
@[simp] theorem trunc_trunc {n} (f : R⟦X⟧) : trunc n ↑(trunc n f) = trunc n f :=
  trunc_trunc_of_le f

/--
theorem `trunc_trunc_mul` / 定理 `trunc_trunc_mul`

English:
theorem trunc_trunc_mul
  given: {n} (f g : R⟦X⟧)
  proof: by
  ext m
  rw [coeff_trunc]; rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, sum_congr rfl]
    intro _ hab
    have ha := lt_of_le_of_lt (antidiagonal.fst_le hab) h
    rw [coeff_coe]; rw [coeff_trunc]; rw [if_pos ha]
  · rfl

中文:
定理 trunc_trunc_mul
  条件: {n} (f g : R⟦X⟧)
  证明: by
  ext m
  rw [coeff_trunc]; rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, sum_congr rfl]
    intro _ hab
    have ha := lt_of_le_of_lt (antidiagonal.fst_le hab) h
    rw [coeff_coe]; rw [coeff_trunc]; rw [if_pos ha]
  · rfl
-/
@[simp] theorem trunc_trunc_mul {n} (f g : R⟦X⟧) :
    trunc n ((trunc n f) * g : R⟦X⟧) = trunc n (f * g) := by
  ext m
  rw [coeff_trunc]; rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, sum_congr rfl]
    intro _ hab
    have ha := lt_of_le_of_lt (antidiagonal.fst_le hab) h
    rw [coeff_coe]; rw [coeff_trunc]; rw [if_pos ha]
  · rfl

/--
theorem `trunc_mul_trunc` / 定理 `trunc_mul_trunc`

English:
theorem trunc_mul_trunc
  given: {n} (f g : R⟦X⟧)
  proof: by
  rw [mul_comm]; rw [trunc_trunc_mul]; rw [mul_comm]

中文:
定理 trunc_mul_trunc
  条件: {n} (f g : R⟦X⟧)
  证明: by
  rw [mul_comm]; rw [trunc_trunc_mul]; rw [mul_comm]
-/
@[simp] theorem trunc_mul_trunc {n} (f g : R⟦X⟧) :
    trunc n (f * (trunc n g) : R⟦X⟧) = trunc n (f * g) := by
  rw [mul_comm]; rw [trunc_trunc_mul]; rw [mul_comm]

/--
theorem `trunc_trunc_mul_trunc` / 定理 `trunc_trunc_mul_trunc`

English:
theorem trunc_trunc_mul_trunc
  given: {n} (f g : R⟦X⟧)
  proof: by
  rw [trunc_trunc_mul]; rw [trunc_mul_trunc]

中文:
定理 trunc_trunc_mul_trunc
  条件: {n} (f g : R⟦X⟧)
  证明: by
  rw [trunc_trunc_mul]; rw [trunc_mul_trunc]

Depends on / 依赖: trunc_mul_trunc, trunc_trunc_mul
-/
theorem trunc_trunc_mul_trunc {n} (f g : R⟦X⟧) :
    trunc n (trunc n f * trunc n g : R⟦X⟧) = trunc n (f * g) := by
  rw [trunc_trunc_mul]; rw [trunc_mul_trunc]

/--
theorem `trunc_trunc_pow` / 定理 `trunc_trunc_pow`

English:
theorem trunc_trunc_pow
  given: (f : R⟦X⟧) (n a : Nat)
  proof: by
  induction a with
  | zero =>
    rw [pow_zero]; rw [pow_zero]
  | succ a ih =>
    rw [_root_.pow_succ']; rw [_root_.pow_succ']; rw [trunc_trunc_mul]; rw [← trunc_trunc_mul_trunc]; rw [ih]; rw [trunc_trunc_mul_trunc]

中文:
定理 trunc_trunc_pow
  条件: (f : R⟦X⟧) (n a : 自然数)
  证明: by
  induction a with
  | zero =>
    rw [pow_zero]; rw [pow_zero]
  | succ a ih =>
    rw [_root_.pow_succ']; rw [_root_.pow_succ']; rw [trunc_trunc_mul]; rw [← trunc_trunc_mul_trunc]; rw [ih]; rw [trunc_trunc_mul_trunc]

Depends on / 依赖: CompHausLike, TotallyDisconnectedSpace
-/
@[simp] theorem trunc_trunc_pow (f : R⟦X⟧) (n a : Nat) :
    trunc n ((trunc n f : R⟦X⟧) ^ a) = trunc n (f ^ a) := by
  induction a with
  | zero =>
    rw [pow_zero]; rw [pow_zero]
  | succ a ih =>
    rw [_root_.pow_succ']; rw [_root_.pow_succ']; rw [trunc_trunc_mul]; rw [← trunc_trunc_mul_trunc]; rw [ih]; rw [trunc_trunc_mul_trunc]

/--
theorem `trunc_coe_eq_self` / 定理 `trunc_coe_eq_self`

English:
theorem trunc_coe_eq_self
  given: {n} {f : R[X]} (hn : natDegree f < n)
  statement: trunc n (f : R⟦X⟧) = f
  proof: by
  rw [← Polynomial.coe_inj]
  ext m
  rw [coeff_coe]; rw [coeff_trunc]
  split
  case isTrue h => rfl
  case isFalse h =>
    rw [not_lt] at h
    rw [coeff_coe]; symm
exact coeff_eq_zero_of_natDegree_lt lt_of_lt_of_le hn h

中文:
定理 trunc_coe_eq_self
  条件: {n} {f : R[X]} (hn : natDegree f < n)
  结论: trunc n (f : R⟦X⟧) = f
  证明: by
  rw [← Polynomial.coe_inj]
  ext m
  rw [coeff_coe]; rw [coeff_trunc]
  split
  case isTrue h => rfl
  case isFalse h =>
    rw [not_lt] at h
    rw [coeff_coe]; symm
exact coeff_eq_zero_of_natDegree_lt lt_of_lt_of_le hn h

Depends on / 依赖: Polynomial, Polynomial.coe_inj, TotallyDisconnectedSpace, coe_inj, coeff_coe, coeff_eq_zero_of_natDegree_lt, coeff_trunc, isFalse, isTrue, lt_of_lt_of_le, not_lt
-/
theorem trunc_coe_eq_self {n} {f : R[X]} (hn : natDegree f < n) : trunc n (f : R⟦X⟧) = f := by
  rw [← Polynomial.coe_inj]
  ext m
  rw [coeff_coe]; rw [coeff_trunc]
  split
  case isTrue h => rfl
  case isFalse h =>
    rw [not_lt] at h
    rw [coeff_coe]; symm
exact coeff_eq_zero_of_natDegree_lt lt_of_lt_of_le hn h

/--
theorem `coeff_coe_trunc_of_lt` / 定理 `coeff_coe_trunc_of_lt`

English:
theorem coeff_coe_trunc_of_lt
  given: {n m} {f : R⟦X⟧} (h : n < m)
  proof: by
  rwa [coeff_coe, coeff_trunc, if_pos]

中文:
定理 coeff_coe_trunc_of_lt
  条件: {n m} {f : R⟦X⟧} (h : n < m)
  证明: by
  rwa [coeff_coe, coeff_trunc, if_pos]

Depends on / 依赖: coeff_coe, coeff_trunc, if_pos
-/
theorem coeff_coe_trunc_of_lt {n m} {f : R⟦X⟧} (h : n < m) :
    coeff n (trunc m f) = coeff n f := by
  rwa [coeff_coe, coeff_trunc, if_pos]

/--
theorem `coeff_mul_eq_coeff_trunc_mul_trunc₂` / 定理 `coeff_mul_eq_coeff_trunc_mul_trunc₂`

English:
theorem coeff_mul_eq_coeff_trunc_mul_trunc₂
  given: {n a b} (f g : R⟦X⟧) (ha : n < a) (hb : n < b)
  proof: by
  symm
  rw [← coeff_coe_trunc_of_lt n.lt_succ_self]; rw [← trunc_trunc_mul_trunc]; rw [trunc_trunc_of_le f ha]; rw [trunc_trunc_of_le g hb]; rw [trunc_trunc_mul_trunc]; rw [coeff_coe_trunc_of_lt n.lt_succ_self]

中文:
定理 coeff_mul_eq_coeff_trunc_mul_trunc₂
  条件: {n a b} (f g : R⟦X⟧) (ha : n < a) (hb : n < b)
  证明: by
  symm
  rw [← coeff_coe_trunc_of_lt n.lt_succ_self]; rw [← trunc_trunc_mul_trunc]; rw [trunc_trunc_of_le f ha]; rw [trunc_trunc_of_le g hb]; rw [trunc_trunc_mul_trunc]; rw [coeff_coe_trunc_of_lt n.lt_succ_self]

Depends on / 依赖: coeff_coe_trunc_of_lt, lt_succ_self, n.lt_succ_self, trunc_trunc_mul_trunc, trunc_trunc_of_le
-/
theorem coeff_mul_eq_coeff_trunc_mul_trunc₂ {n a b} (f g : R⟦X⟧) (ha : n < a) (hb : n < b) :
    coeff n (f * g) = coeff n ((trunc a f : R⟦X⟧) * (trunc b g : R⟦X⟧)) := by
  symm
  rw [← coeff_coe_trunc_of_lt n.lt_succ_self]; rw [← trunc_trunc_mul_trunc]; rw [trunc_trunc_of_le f ha]; rw [trunc_trunc_of_le g hb]; rw [trunc_trunc_mul_trunc]; rw [coeff_coe_trunc_of_lt n.lt_succ_self]

/--
theorem `coeff_mul_eq_coeff_trunc_mul_trunc` / 定理 `coeff_mul_eq_coeff_trunc_mul_trunc`

English:
theorem coeff_mul_eq_coeff_trunc_mul_trunc
  given: {d n} (f g) (h : d < n)
  proof: coeff_mul_eq_coeff_trunc_mul_trunc₂ f g h h

中文:
定理 coeff_mul_eq_coeff_trunc_mul_trunc
  条件: {d n} (f g) (h : d < n)
  证明: coeff_mul_eq_coeff_trunc_mul_trunc₂ f g h h

Depends on / 依赖: X.prop
-/
theorem coeff_mul_eq_coeff_trunc_mul_trunc {d n} (f g) (h : d < n) :
    coeff d (f * g) = coeff d ((trunc n f : R⟦X⟧) * (trunc n g : R⟦X⟧)) :=
  coeff_mul_eq_coeff_trunc_mul_trunc₂ f g h h

end Trunc

section Ring

variable [Ring R]

@[simp]
/--
lemma `trunc_sub` / 引理 `trunc_sub`

English:
lemma trunc_sub
  given: (n : Nat) (φ ψ : R⟦X⟧)
  statement: trunc n (φ - ψ) = trunc n φ - trunc n ψ
  proof: by
  ext i
  simp

中文:
引理 trunc_sub
  条件: (n : 自然数) (φ ψ : R⟦X⟧)
  结论: trunc n (φ - ψ) = trunc n φ - trunc n ψ
  证明: by
  ext i
  simp
-/
lemma trunc_sub (n : Nat) (φ ψ : R⟦X⟧) : trunc n (φ - ψ) = trunc n φ - trunc n ψ := by
  ext i
  simp

end Ring

section Map
variable {S : Type*} [Semiring R] [Semiring S] (f : R ->+* S)

/--
lemma `trunc_map` / 引理 `trunc_map`

English:
lemma trunc_map
  given: (p : R⟦X⟧) (n : Nat)
  statement: (p.map f).trunc n = (p.trunc n).map f
  proof: by
  ext m; simp [coeff_trunc, apply_ite f]

中文:
引理 trunc_map
  条件: (p : R⟦X⟧) (n : 自然数)
  结论: (p.map f).trunc n = (p.trunc n).map f
  证明: by
  ext m; simp [coeff_trunc, apply_ite f]

Depends on / 依赖: X.prop, apply_ite, coeff_trunc
-/
lemma trunc_map (p : R⟦X⟧) (n : Nat) : (p.map f).trunc n = (p.trunc n).map f := by
  ext m; simp [coeff_trunc, apply_ite f]

end Map

end PowerSeries

end
