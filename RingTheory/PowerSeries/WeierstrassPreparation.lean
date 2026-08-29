/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.RingTheory.PowerSeries.CoeffMulMem
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!

# Weierstrass preparation theorem for power series over a complete local ring

In this file we define Weierstrass division, Weierstrass factorization, and prove
Weierstrass preparation theorem.

We assume that a ring is adic complete with respect to some ideal.
If such ideal is a maximal ideal, then by `isLocalRing_of_isAdicComplete_maximal`,
such ring has only one maximal ideal, and hence it is a complete local ring.

## Main definitions

- `PowerSeries.IsWeierstrassDivisionAt f g q r I`: let `f` and `g` be power series over `A`, `I` be
  an ideal of `A`, this is a `Prop` which asserts that a power series
  `q` and a polynomial `r` of degree `< n` satisfy `f = g * q + r`, where `n` is the order of the
  image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
  it's mathematically not considered).

- `PowerSeries.IsWeierstrassDivision`: version of `PowerSeries.IsWeierstrassDivisionAt`
  for local rings with respect to its maximal ideal.

- `PowerSeries.IsWeierstrassDivisorAt g I`: let `g` be a power series over `A`, `I` be an ideal of
  `A`, this is a `Prop` which asserts that the `n`-th coefficient
  of `g` is a unit, where `n` is the order of the image of `g` in `(A / I)⟦X⟧`
  (defined to be zero if such image is zero, in which case it's mathematically not considered).

  This property guarantees that if the `A` is `I`-adic complete, then `g` can be used as a divisor
  in Weierstrass division (`PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`).

- `PowerSeries.IsWeierstrassDivisor`: version of `PowerSeries.IsWeierstrassDivisorAt` for
  local rings with respect to its maximal ideal.

- `PowerSeries.IsWeierstrassFactorizationAt g f h I`: for a power series `g` over `A` and
  an ideal `I` of `A`, this is a `Prop` which asserts that `f` is a distinguished polynomial at `I`,
  `h` is a formal power series over `A` that is a unit and such that `g = f * h`.

- `PowerSeries.IsWeierstrassFactorization`: version of `PowerSeries.IsWeierstrassFactorizationAt`
  for local rings with respect to its maximal ideal.

## Main results

- `PowerSeries.exists_isWeierstrassDivision`: **Weierstrass division**
  ([washington_cyclotomic], Proposition 7.2): let `f`, `g` be power series
  over a complete local ring, such that the image of `g` in the residue field is not zero.
  Let `n` be the order of the image of `g` in the residue field. Then there exists a power series
  `q` and a polynomial `r` of degree `< n`, such that `f = g * q + r`.

- `PowerSeries.IsWeierstrassDivision.elim`,
  `PowerSeries.IsWeierstrassDivision.unique`: `q` and `r` in the Weierstrass division are unique.

- `PowerSeries.exists_isWeierstrassFactorization`: **Weierstrass preparation theorem**
  ([washington_cyclotomic], Theorem 7.3): let `g` be a power series
  over a complete local ring, such that its image in the residue field is
  not zero. Then there exists a distinguished polynomial `f` and a power series `h`
  which is a unit, such that `g = f * h`.

- `PowerSeries.IsWeierstrassFactorization.elim`,
  `PowerSeries.IsWeierstrassFactorization.unique`: `f` and `h` in Weierstrass preparation
  theorem are unique.

- `Polynomial.IsDistinguishedAt.algEquivQuotient`: a distinguished polynomial `g` induces a
  natural isomorphism `A[X] / (g) ≃ₐ[A] A⟦X⟧ / (g)`.

- `PowerSeries.IsWeierstrassFactorizationAt.algEquivQuotient`: a Weierstrass factorization
  `g = f * h` induces a natural isomorphism `A[X] / (f) ≃ₐ[A] A⟦X⟧ / (g)`.

- `PowerSeries.algEquivQuotientWeierstrassDistinguished`:
  if `g` is a power series over a complete local ring,
  such that its image in the residue field is not zero, then there is a natural isomorphism
  `A[X] / (f) ≃ₐ[A] A⟦X⟧ / (g)` where `f` is `PowerSeries.weierstrassDistinguished g`.

## References

- [Washington, Lawrence C. *Introduction to cyclotomic fields.*][washington_cyclotomic]

-/

@[expose] public section

open scoped Polynomial

namespace PowerSeries

variable {A : Type*} [CommRing A]

/-!

## Weierstrass division

-/

section IsWeierstrassDivisionAt

variable (f g q : A⟦X⟧) (r : A[X]) (I : Ideal A)

/-- Let `f`, `g` be power series over `A`, `I` be an ideal of `A`,
`PowerSeries.IsWeierstrassDivisionAt f g q r I` is a `Prop` which asserts that a power series
`q` and a polynomial `r` of degree `< n` satisfy `f = g * q + r`, where `n` is the order of the
image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
it's mathematically not considered). -/
@[mk_iff]
/--
Definition of `IsWeierstrassDivisionAt` / `IsWeierstrassDivisionAt` 的定义

English:
structure IsWeierstrassDivisionAt
  parameters: : Prop where
  axioms and operations (2):
    - degree_lt : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat
    - eq_mul_add : f = g * q + r

中文:
结构 是WeierstrassDivisionAt
  参数: : 命题 where
  公理与运算 (2 个):
    - degree_lt : r.degree < (g.map (理想.商.mk I)).order.to自然数
    - eq_mul_add : f = g * q + r
-/
structure IsWeierstrassDivisionAt : Prop where
  degree_lt : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat
  eq_mul_add : f = g * q + r

/--
Definition of `IsWeierstrassDivision` / `IsWeierstrassDivision` 的定义

English:
abbreviation IsWeierstrassDivision
  signature: [IsLocalRing A]
  body: f.IsWeierstrassDivisionAt g q r (IsLocalRing.maximalIdeal A)

中文:
缩写 IsWeierstrassDivision
  签名: [是局部环 A]
  定义体: f.IsWeierstrassDivisionAt g q r (IsLocalRing.maximalIdeal A)

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal, IsWeierstrassDivisionAt, f.IsWeierstrassDivisionAt, maximalIdeal
-/
abbrev IsWeierstrassDivision [IsLocalRing A] : Prop :=
  f.IsWeierstrassDivisionAt g q r (IsLocalRing.maximalIdeal A)

/--
theorem `isWeierstrassDivisionAt_zero` / 定理 `isWeierstrassDivisionAt_zero`

English:
theorem isWeierstrassDivisionAt_zero
  statement: IsWeierstrassDivisionAt 0 g 0 0 I
  proof: by
  constructor
  · rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · simp

中文:
定理 isWeierstrassDivisionAt_zero
  结论: 是WeierstrassDivisionAt 0 g 0 0 I
  证明: by
  constructor
  · rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · simp

Depends on / 依赖: Polynomial, Polynomial.degree_zero, WithBot, WithBot.bot_lt_coe, bot_lt_coe, degree_zero
-/
theorem isWeierstrassDivisionAt_zero : IsWeierstrassDivisionAt 0 g 0 0 I := by
  constructor
  · rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · simp

variable {f g q r I}

namespace IsWeierstrassDivisionAt

/--
theorem `coeff_f_sub_r_mem` / 定理 `coeff_f_sub_r_mem`

English:
theorem coeff_f_sub_r_mem
  statement: (H : f.IsWeierstrassDivisionAt g q r I)
  proof: by
  replace H := H.2
  rw [← sub_eq_iff_eq_add] at H
  rw [H]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal i (fun j hj => ?_) i le_rfl
  have := coeff_of_lt_order_toNat _ (lt_of_le_of_lt hj hi)
  rwa [coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at this

中文:
定理 coeff_f_sub_r_mem
  结论: (H : f.是WeierstrassDivisionAt g q r I)
  证明: by
  replace H := H.2
  rw [← sub_eq_iff_eq_add] at H
  rw [H]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal i (fun j hj => ?_) i le_rfl
  have := coeff_of_lt_order_toNat _ (lt_of_le_of_lt hj hi)
  rwa [coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at this

Depends on / 依赖: Ideal.mk_ker, RingHom, RingHom.mem_ker, coeff_map, coeff_mul_mem_ideal_of_coeff_left_mem_ideal, coeff_of_lt_order_toNat, le_rfl, lt_of_le_of_lt, mem_ker, mk_ker, replace, sub_eq_iff_eq_add
-/
theorem coeff_f_sub_r_mem (H : f.IsWeierstrassDivisionAt g q r I)
    {i : Nat} (hi : i < (g.map (Ideal.Quotient.mk I)).order.toNat) :
    coeff i (f - r : A⟦X⟧) in I := by
  replace H := H.2
  rw [← sub_eq_iff_eq_add] at H
  rw [H]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal i (fun j hj => ?_) i le_rfl
  have := coeff_of_lt_order_toNat _ (lt_of_le_of_lt hj hi)
  rwa [coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at this

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: {f' q' r'} (H : f.IsWeierstrassDivisionAt g q r I)
  proof: ⟨(Polynomial.degree_add_le _ _).trans_lt (sup_lt_iff.2 ⟨H.degree_lt, H'.degree_lt⟩), by
    rw [H.eq_mul_add]; rw [H'.eq_mul_add]; rw [Polynomial.coe_add]; ring⟩

中文:
定理 add
  结论: {f' q' r'} (H : f.是WeierstrassDivisionAt g q r I)
  证明: ⟨(Polynomial.degree_add_le _ _).trans_lt (sup_lt_iff.2 ⟨H.degree_lt, H'.degree_lt⟩), by
    rw [H.eq_mul_add]; rw [H'.eq_mul_add]; rw [Polynomial.coe_add]; ring⟩

Depends on / 依赖: H.degree_lt, H.eq_mul_add, Polynomial, Polynomial.coe_add, Polynomial.degree_add_le, coe_add, degree_add_le, degree_lt, eq_mul_add, sup_lt_iff, trans_lt
-/
theorem add {f' q' r'} (H : f.IsWeierstrassDivisionAt g q r I)
    (H' : f'.IsWeierstrassDivisionAt g q' r' I) :
    (f + f').IsWeierstrassDivisionAt g (q + q') (r + r') I :=
  ⟨(Polynomial.degree_add_le _ _).trans_lt (sup_lt_iff.2 ⟨H.degree_lt, H'.degree_lt⟩), by
    rw [H.eq_mul_add]; rw [H'.eq_mul_add]; rw [Polynomial.coe_add]; ring⟩

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (H : f.IsWeierstrassDivisionAt g q r I) (a : A)
  proof: ⟨(Polynomial.degree_smul_le a _).trans_lt H.degree_lt, by
    simp [H.eq_mul_add, Algebra.smul_def, mul_add, mul_left_comm]⟩

中文:
定理 smul
  条件: (H : f.是WeierstrassDivisionAt g q r I) (a : A)
  证明: ⟨(Polynomial.degree_smul_le a _).trans_lt H.degree_lt, by
    simp [H.eq_mul_add, Algebra.smul_def, mul_add, mul_left_comm]⟩

Depends on / 依赖: Algebra, Algebra.smul_def, H.degree_lt, H.eq_mul_add, Polynomial, Polynomial.degree_smul_le, degree_lt, degree_smul_le, eq_mul_add, mul_add, mul_left_comm, smul_def, trans_lt
-/
theorem smul (H : f.IsWeierstrassDivisionAt g q r I) (a : A) :
    (a • f).IsWeierstrassDivisionAt g (a • q) (a • r) I :=
  ⟨(Polynomial.degree_smul_le a _).trans_lt H.degree_lt, by
    simp [H.eq_mul_add, Algebra.smul_def, mul_add, mul_left_comm]⟩

end IsWeierstrassDivisionAt

end IsWeierstrassDivisionAt

section IsWeierstrassDivisorAt

variable (g : A⟦X⟧) (I : Ideal A)

/--
Definition of `IsWeierstrassDivisorAt` / `IsWeierstrassDivisorAt` 的定义

English:
definition IsWeierstrassDivisorAt
  signature: : Prop
  body: IsUnit (coeff (g.map (Ideal.Quotient.mk I)).order.toNat g)

中文:
定义 IsWeierstrassDivisorAt
  签名: : 命题
  定义体: IsUnit (coeff (g.map (Ideal.Quotient.mk I)).order.toNat g)

Depends on / 依赖: Ideal.Quotient.mk, IsUnit, Quotient, g.map, order.toNat
-/
def IsWeierstrassDivisorAt : Prop :=
  IsUnit (coeff (g.map (Ideal.Quotient.mk I)).order.toNat g)

/--
Definition of `IsWeierstrassDivisor` / `IsWeierstrassDivisor` 的定义

English:
abbreviation IsWeierstrassDivisor
  signature: [IsLocalRing A]
  body: g.IsWeierstrassDivisorAt (IsLocalRing.maximalIdeal A)

中文:
缩写 IsWeierstrassDivisor
  签名: [是局部环 A]
  定义体: g.IsWeierstrassDivisorAt (IsLocalRing.maximalIdeal A)

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal, IsWeierstrassDivisorAt, g.IsWeierstrassDivisorAt, maximalIdeal
-/
abbrev IsWeierstrassDivisor [IsLocalRing A] : Prop :=
  g.IsWeierstrassDivisorAt (IsLocalRing.maximalIdeal A)

variable {g} in
/--
theorem `IsWeierstrassDivisor.of_map_ne_zero` / 定理 `IsWeierstrassDivisor.of_map_ne_zero`

English:
theorem IsWeierstrassDivisor.of_map_ne_zero
  statement: [IsLocalRing A]
  proof: by
  rw [IsWeierstrassDivisor]; rw [IsWeierstrassDivisorAt]; rw [← IsLocalRing.notMem_maximalIdeal]
  have h := coeff_order hg
  contrapose h
  rwa [coeff_map, IsLocalRing.residue_eq_zero_iff]

中文:
定理 IsWeierstrassDivisor.of_map_ne_zero
  结论: [是局部环 A]
  证明: by
  rw [IsWeierstrassDivisor]; rw [IsWeierstrassDivisorAt]; rw [← IsLocalRing.notMem_maximalIdeal]
  have h := coeff_order hg
  contrapose h
  rwa [coeff_map, IsLocalRing.residue_eq_zero_iff]

Depends on / 依赖: IsLocalRing, IsLocalRing.notMem_maximalIdeal, IsLocalRing.residue_eq_zero_iff, IsWeierstrassDivisor, IsWeierstrassDivisorAt, coeff_map, coeff_order, contrapose, notMem_maximalIdeal, residue_eq_zero_iff
-/
theorem IsWeierstrassDivisor.of_map_ne_zero [IsLocalRing A]
    (hg : g.map (IsLocalRing.residue A) != 0) : g.IsWeierstrassDivisor := by
  rw [IsWeierstrassDivisor]; rw [IsWeierstrassDivisorAt]; rw [← IsLocalRing.notMem_maximalIdeal]
  have h := coeff_order hg
  contrapose h
  rwa [coeff_map, IsLocalRing.residue_eq_zero_iff]

/--
theorem `_root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt` / 定理 `_root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt`

English:
theorem _root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt
  statement: {g : A[X]} {I : Ideal A}
  proof: by
  have : g.natDegree = _ := congr(ENat.toNat $(H.coe_natDegree_eq_order_map g 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  simp [IsWeierstrassDivisorAt, ← this, H.monic.leadingCoeff]

中文:
定理 _root_.多项式.是DistinguishedAt.isWeierstrassDivisorAt
  结论: {g : A[X]} {I : 理想 A}
  证明: by
  have : g.natDegree = _ := congr(ENat.toNat $(H.coe_natDegree_eq_order_map g 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  simp [IsWeierstrassDivisorAt, ← this, H.monic.leadingCoeff]

Depends on / 依赖: ENat.toNat, H.coe_natDegree_eq_order_map, H.monic.leadingCoeff, Ideal.ne_top_iff_one, IsWeierstrassDivisorAt, coe_natDegree_eq_order_map, constantCoeff_one, g.natDegree, leadingCoeff, natDegree, ne_top_iff_one
-/
theorem _root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt {g : A[X]} {I : Ideal A}
    (H : g.IsDistinguishedAt I) (hI : I != ⊤) : IsWeierstrassDivisorAt g I := by
  have : g.natDegree = _ := congr(ENat.toNat $(H.coe_natDegree_eq_order_map g 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  simp [IsWeierstrassDivisorAt, ← this, H.monic.leadingCoeff]

/--
theorem `_root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt'` / 定理 `_root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt'`

English:
theorem _root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt'
  statement: {g : A[X]} {I : Ideal A}
  proof: by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsHausdorff ⊤ A›.subsingleton
    exact isUnit_of_subsingleton _
  exact H.isWeierstrassDivisorAt hI

中文:
定理 _root_.多项式.是DistinguishedAt.isWeierstrassDivisorAt'
  结论: {g : A[X]} {I : 理想 A}
  证明: by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsHausdorff ⊤ A›.subsingleton
    exact isUnit_of_subsingleton _
  exact H.isWeierstrassDivisorAt hI

Depends on / 依赖: FintypeCat, FintypeCat.toProfiniteFullyFaithful.full, H.isWeierstrassDivisorAt, IsHausdorff, eq_or_ne, isUnit_of_subsingleton, isWeierstrassDivisorAt, subsingleton, toProfiniteFullyFaithful
-/
theorem _root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt' {g : A[X]} {I : Ideal A}
    (H : g.IsDistinguishedAt I) [IsHausdorff I A] : IsWeierstrassDivisorAt g I := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsHausdorff ⊤ A›.subsingleton
    exact isUnit_of_subsingleton _
  exact H.isWeierstrassDivisorAt hI

/--
theorem `coeff_trunc_order_mem` / 定理 `coeff_trunc_order_mem`

English:
theorem coeff_trunc_order_mem
  given: (i : Nat)
  proof: by
  rw [coeff_trunc]
  split_ifs with h
  · simpa [← RingHom.mem_ker] using coeff_of_lt_order_toNat _ h
  · exact zero_mem _

中文:
定理 coeff_trunc_order_mem
  条件: (i : 自然数)
  证明: by
  rw [coeff_trunc]
  split_ifs with h
  · simpa [← RingHom.mem_ker] using coeff_of_lt_order_toNat _ h
  · exact zero_mem _

Depends on / 依赖: Finite
-/
private theorem coeff_trunc_order_mem (i : Nat) :
    (g.trunc (g.map (Ideal.Quotient.mk I)).order.toNat).coeff i in I := by
  rw [coeff_trunc]
  split_ifs with h
  · simpa [← RingHom.mem_ker] using coeff_of_lt_order_toNat _ h
  · exact zero_mem _

namespace IsWeierstrassDivisorAt

variable {g I} (H : g.IsWeierstrassDivisorAt I)
include H

/--
theorem `isUnit_shift` / 定理 `isUnit_shift`

English:
theorem isUnit_shift
  statement: IsUnit mk fun i =>
  proof: by
  simpa [isUnit_iff_constantCoeff]

中文:
定理 isUnit_shift
  结论: 是单位 mk fun i =>
  证明: by
  simpa [isUnit_iff_constantCoeff]

Depends on / 依赖: Finite, isUnit_iff_constantCoeff
-/
theorem isUnit_shift : IsUnit mk fun i =>
    coeff (i + (g.map (Ideal.Quotient.mk I)).order.toNat) g := by
  simpa [isUnit_iff_constantCoeff]

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: (H : g.IsWeierstrassDivisorAt I) (f : A⟦X⟧)

中文:
定义 seq
  签名: (H : g.IsWeierstrassDivisorAt I) (f : A⟦X⟧)
-/
noncomputable def seq (H : g.IsWeierstrassDivisorAt I) (f : A⟦X⟧) : Nat -> A⟦X⟧
  | 0 => 0
  | k + 1 =>
    H.seq f k + (mk fun i => coeff (i + (g.map (Ideal.Quotient.mk I)).order.toNat)
      (f - g * H.seq f k)) * H.isUnit_shift.unit⁻¹

variable (a : A) (f f' : A⟦X⟧)

/--
theorem `coeff_seq_mem` / 定理 `coeff_seq_mem`

English:
theorem coeff_seq_mem
  given: (k : Nat) {i : Nat} (hi : i >= (g.map (Ideal.Quotient.mk I)).order.toNat)
  proof: by
  induction k generalizing hi i with
  | zero => simp
  | succ k hq =>
    rw [seq]
    set q := H.seq f k
    set s := f - g * q
    set n := (g.map (Ideal.Quotient.mk I)).order.toNat
    have hs := s.eq_X_pow_mul_shift_add_trunc n
    set s₀ := s.trunc n
    set s₁ := PowerSeries.mk fun i => coeff (i + n) s
    set q' := q + s₁ * H.isUnit_shift.unit⁻¹
    have key : f - g * q' = (s₀ : A⟦X⟧) - (g.trunc n : A⟦X⟧) * s₁ * H.isUnit_shift.unit⁻¹ := by
      trans s + g * (q - q')
      · simp_rw [s]; ring
      simp_rw [q']
      rw [sub_add_cancel_left]; rw [mul_neg]; rw [← mul_assoc]; rw [mul_right_comm]
      nth_rw 1 [g.eq_X_pow_mul_shift_add_trunc n]
      rw [add_mul]; rw [mul_assoc]; rw [IsUnit.mul_val_inv]; rw [hs]
      ring
    rw [key]; rw [map_sub]; rw [Polynomial.coeff_coe]; rw [coeff_trunc]; rw [if_neg hi.not_gt]; rw [zero_sub]; rw [neg_mem_iff]; rw [pow_succ']
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) i
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
      (by simp [n, g.coeff_trunc_order_mem]) (fun i => ?_) i
    rw [coeff_mk]
    exact hq (by simp)

中文:
定理 coeff_seq_mem
  条件: (k : 自然数) {i : 自然数} (hi : i >= (g.map (理想.商.mk I)).order.to自然数)
  证明: by
  induction k generalizing hi i with
  | zero => simp
  | succ k hq =>
    rw [seq]
    set q := H.seq f k
    set s := f - g * q
    set n := (g.map (Ideal.Quotient.mk I)).order.toNat
    have hs := s.eq_X_pow_mul_shift_add_trunc n
    set s₀ := s.trunc n
    set s₁ := PowerSeries.mk fun i => coeff (i + n) s
    set q' := q + s₁ * H.isUnit_shift.unit⁻¹
    have key : f - g * q' = (s₀ : A⟦X⟧) - (g.trunc n : A⟦X⟧) * s₁ * H.isUnit_shift.unit⁻¹ := by
      trans s + g * (q - q')
      · simp_rw [s]; ring
      simp_rw [q']
      rw [sub_add_cancel_left]; rw [mul_neg]; rw [← mul_assoc]; rw [mul_right_comm]
      nth_rw 1 [g.eq_X_pow_mul_shift_add_trunc n]
      rw [add_mul]; rw [mul_assoc]; rw [IsUnit.mul_val_inv]; rw [hs]
      ring
    rw [key]; rw [map_sub]; rw [Polynomial.coeff_coe]; rw [coeff_trunc]; rw [if_neg hi.not_gt]; rw [zero_sub]; rw [neg_mem_iff]; rw [pow_succ']
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) i
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
      (by simp [n, g.coeff_trunc_order_mem]) (fun i => ?_) i
    rw [coeff_mk]
    exact hq (by simp)

Depends on / 依赖: H.isUnit_shift.unit, H.seq, Ideal.Quotient.mk, PowerSeries, PowerSeries.mk, Quotient, eq_X_pow_mul_shift_add_trunc, g.map, g.trunc, generalizing, isUnit_shift, order.toNat, s.eq_X_pow_mul_shift_add_trunc, s.trunc, simp_rw, sub_add_cancel_left
-/
theorem coeff_seq_mem (k : Nat) {i : Nat} (hi : i >= (g.map (Ideal.Quotient.mk I)).order.toNat) :
    coeff i (f - g * H.seq f k) in I ^ k := by
  induction k generalizing hi i with
  | zero => simp
  | succ k hq =>
    rw [seq]
    set q := H.seq f k
    set s := f - g * q
    set n := (g.map (Ideal.Quotient.mk I)).order.toNat
    have hs := s.eq_X_pow_mul_shift_add_trunc n
    set s₀ := s.trunc n
    set s₁ := PowerSeries.mk fun i => coeff (i + n) s
    set q' := q + s₁ * H.isUnit_shift.unit⁻¹
    have key : f - g * q' = (s₀ : A⟦X⟧) - (g.trunc n : A⟦X⟧) * s₁ * H.isUnit_shift.unit⁻¹ := by
      trans s + g * (q - q')
      · simp_rw [s]; ring
      simp_rw [q']
      rw [sub_add_cancel_left]; rw [mul_neg]; rw [← mul_assoc]; rw [mul_right_comm]
      nth_rw 1 [g.eq_X_pow_mul_shift_add_trunc n]
      rw [add_mul]; rw [mul_assoc]; rw [IsUnit.mul_val_inv]; rw [hs]
      ring
    rw [key]; rw [map_sub]; rw [Polynomial.coeff_coe]; rw [coeff_trunc]; rw [if_neg hi.not_gt]; rw [zero_sub]; rw [neg_mem_iff]; rw [pow_succ']
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) i
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
      (by simp [n, g.coeff_trunc_order_mem]) (fun i => ?_) i
    rw [coeff_mk]
    exact hq (by simp)

/--
theorem `coeff_seq_succ_sub_seq_mem` / 定理 `coeff_seq_succ_sub_seq_mem`

English:
theorem coeff_seq_succ_sub_seq_mem
  given: (k i : Nat)
  proof: by
  rw [seq]; rw [add_sub_cancel_left]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) i
  rw [coeff_mk]
  exact H.coeff_seq_mem f k (by simp)

@[simp]

中文:
定理 coeff_seq_succ_sub_seq_mem
  条件: (k i : 自然数)
  证明: by
  rw [seq]; rw [add_sub_cancel_left]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) i
  rw [coeff_mk]
  exact H.coeff_seq_mem f k (by simp)

@[simp]

Depends on / 依赖: H.coeff_seq_mem, add_sub_cancel_left, coeff_mk, coeff_mul_mem_ideal_of_coeff_left_mem_ideal, coeff_seq_mem
-/
theorem coeff_seq_succ_sub_seq_mem (k i : Nat) :
    coeff i (H.seq f (k + 1) - H.seq f k) in I ^ k := by
  rw [seq]; rw [add_sub_cancel_left]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) i
  rw [coeff_mk]
  exact H.coeff_seq_mem f k (by simp)

@[simp]
/--
theorem `seq_zero` / 定理 `seq_zero`

English:
theorem seq_zero
  statement: H.seq f 0 = 0
  proof: rfl

中文:
定理 seq_zero
  结论: H.seq f 0 = 0
  证明: rfl
-/
theorem seq_zero : H.seq f 0 = 0 := rfl

/--
theorem `seq_one` / 定理 `seq_one`

English:
theorem seq_one
  statement: H.seq f 1 = (PowerSeries.mk fun i => coeff
  proof: by
  simp_rw [seq, mul_zero, zero_add, sub_zero]

中文:
定理 seq_one
  结论: H.seq f 1 = (幂级数.mk fun i => coeff
  证明: by
  simp_rw [seq, mul_zero, zero_add, sub_zero]

Depends on / 依赖: mul_zero, simp_rw, sub_zero, zero_add
-/
theorem seq_one : H.seq f 1 = (PowerSeries.mk fun i => coeff
    (i + (g.map (Ideal.Quotient.mk I)).order.toNat) f) * H.isUnit_shift.unit⁻¹ := by
  simp_rw [seq, mul_zero, zero_add, sub_zero]

/--
Definition of `divCoeff` / `divCoeff` 的定义

English:
definition divCoeff
  signature: [IsPrecomplete I A] (i : Nat)
  body: Classical.indefiniteDescription _ IsPrecomplete.prec' (I := I)
    (fun k => coeff i (H.seq f k)) fun {m} {n} hn => by
      induction n, hn using Nat.le_induction with
      | base => rw [SModEq.def]
      | succ n hn ih =>
        refine ih.trans (SModEq.symm ?_)
        rw [SModEq.sub_mem]; rw [smul_eq_mul]; rw [Ideal.mul_top]; rw [← map_sub]
        exact Ideal.pow_le_pow_right hn (H.coeff_seq_succ_sub_seq_mem f n i)

中文:
定义 divCoeff
  签名: [是Precomplete I A] (i : 自然数)
  定义体: Classical.indefiniteDescription _ IsPrecomplete.prec' (I := I)
    (fun k => coeff i (H.seq f k)) fun {m} {n} hn => by
      induction n, hn using Nat.le_induction with
      | base => rw [SModEq.def]
      | succ n hn ih =>
        refine ih.trans (SModEq.symm ?_)
        rw [SModEq.sub_mem]; rw [smul_eq_mul]; rw [Ideal.mul_top]; rw [← map_sub]
        exact Ideal.pow_le_pow_right hn (H.coeff_seq_succ_sub_seq_mem f n i)

Depends on / 依赖: Classical, Classical.indefiniteDescription, H.coeff_seq_succ_sub_seq_mem, H.seq, Ideal.mul_top, Ideal.pow_le_pow_right, IsPrecomplete, IsPrecomplete.prec, Nat.le_induction, SModEq, SModEq.def, SModEq.sub_mem, SModEq.symm, coeff_seq_succ_sub_seq_mem, ih.trans, indefiniteDescription, le_induction, map_sub, mul_top, pow_le_pow_right
-/
noncomputable def divCoeff [IsPrecomplete I A] (i : Nat) :=
Classical.indefiniteDescription _ IsPrecomplete.prec' (I := I)
    (fun k => coeff i (H.seq f k)) fun {m} {n} hn => by
      induction n, hn using Nat.le_induction with
      | base => rw [SModEq.def]
      | succ n hn ih =>
        refine ih.trans (SModEq.symm ?_)
        rw [SModEq.sub_mem]; rw [smul_eq_mul]; rw [Ideal.mul_top]; rw [← map_sub]
        exact Ideal.pow_le_pow_right hn (H.coeff_seq_succ_sub_seq_mem f n i)

/--
Definition of `div` / `div` 的定义

English:
definition div
  signature: [IsPrecomplete I A]
  body: PowerSeries.mk fun i => (H.divCoeff f i).1

中文:
定义 div
  签名: [是Precomplete I A]
  定义体: PowerSeries.mk fun i => (H.divCoeff f i).1

Depends on / 依赖: H.divCoeff, PowerSeries, PowerSeries.mk, divCoeff
-/
noncomputable def div [IsPrecomplete I A] : A⟦X⟧ := PowerSeries.mk fun i => (H.divCoeff f i).1

/--
theorem `coeff_div` / 定理 `coeff_div`

English:
theorem coeff_div
  given: [IsPrecomplete I A] (i : Nat)
  statement: coeff i (H.div f) = (H.divCoeff f i).1
  proof: by
  simp [div]

中文:
定理 coeff_div
  条件: [是Precomplete I A] (i : 自然数)
  结论: coeff i (H.div f) = (H.divCoeff f i).1
  证明: by
  simp [div]
-/
theorem coeff_div [IsPrecomplete I A] (i : Nat) : coeff i (H.div f) = (H.divCoeff f i).1 := by
  simp [div]

/--
theorem `coeff_div_sub_seq_mem` / 定理 `coeff_div_sub_seq_mem`

English:
theorem coeff_div_sub_seq_mem
  given: [IsPrecomplete I A] (k i : Nat)
  proof: by
  simpa [coeff_div, SModEq.sub_mem] using ((H.divCoeff f i).2 k).symm

中文:
定理 coeff_div_sub_seq_mem
  条件: [是Precomplete I A] (k i : 自然数)
  证明: by
  simpa [coeff_div, SModEq.sub_mem] using ((H.divCoeff f i).2 k).symm

Depends on / 依赖: H.divCoeff, SModEq, SModEq.sub_mem, coeff_div, divCoeff, sub_mem
-/
theorem coeff_div_sub_seq_mem [IsPrecomplete I A] (k i : Nat) :
    coeff i (H.div f - (H.seq f k)) in I ^ k := by
  simpa [coeff_div, SModEq.sub_mem] using ((H.divCoeff f i).2 k).symm

/--
Definition of `mod` / `mod` 的定义

English:
definition mod
  signature: [IsPrecomplete I A]
  body: (f - g * H.div f).trunc (g.map (Ideal.Quotient.mk I)).order.toNat

中文:
定义 mod
  签名: [是Precomplete I A]
  定义体: (f - g * H.div f).trunc (g.map (Ideal.Quotient.mk I)).order.toNat

Depends on / 依赖: H.div, Ideal.Quotient.mk, Quotient, g.map, order.toNat
-/
noncomputable def mod [IsPrecomplete I A] : A[X] :=
  (f - g * H.div f).trunc (g.map (Ideal.Quotient.mk I)).order.toNat

/--
theorem `isWeierstrassDivisionAt_div_mod` / 定理 `isWeierstrassDivisionAt_div_mod`

English:
theorem isWeierstrassDivisionAt_div_mod
  given: [IsAdicComplete I A]
  proof: by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    rw [Subsingleton.elim f 0]; rw [Subsingleton.elim (H.div 0) 0]; rw [Subsingleton.elim (H.mod 0) 0]
    exact g.isWeierstrassDivisionAt_zero _
  constructor
  · exact degree_trunc_lt _ _
  · rw [mod, add_comm, ← sub_eq_iff_eq_add]
    ext i
    rw [Polynomial.coeff_coe]; rw [coeff_trunc]
    split_ifs with hi
    · rfl
    refine IsHausdorff.haus' (I := I) _ fun k => ?_
    rw [SModEq.zero]; rw [smul_eq_mul]; rw [Ideal.mul_top]; rw [show f - g * H.div f =
      f - g * (H.seq f k) - g * (H.div f - (H.seq f k)) by ring]; rw [map_sub]
exact Ideal.sub_mem _ (H.coeff_seq_mem f k (not_lt.1 hi))
      coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (H.coeff_div_sub_seq_mem f k) i

中文:
定理 isWeierstrassDivisionAt_div_mod
  条件: [是AdicComplete I A]
  证明: by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    rw [Subsingleton.elim f 0]; rw [Subsingleton.elim (H.div 0) 0]; rw [Subsingleton.elim (H.mod 0) 0]
    exact g.isWeierstrassDivisionAt_zero _
  constructor
  · exact degree_trunc_lt _ _
  · rw [mod, add_comm, ← sub_eq_iff_eq_add]
    ext i
    rw [Polynomial.coeff_coe]; rw [coeff_trunc]
    split_ifs with hi
    · rfl
    refine IsHausdorff.haus' (I := I) _ fun k => ?_
    rw [SModEq.zero]; rw [smul_eq_mul]; rw [Ideal.mul_top]; rw [show f - g * H.div f =
      f - g * (H.seq f k) - g * (H.div f - (H.seq f k)) by ring]; rw [map_sub]
exact Ideal.sub_mem _ (H.coeff_seq_mem f k (not_lt.1 hi))
      coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (H.coeff_div_sub_seq_mem f k) i

Depends on / 依赖: H.div, H.mod, Ideal.mul_top, IsAdicComplete, IsHausdorff, IsHausdorff.haus, Polynomial, Polynomial.coeff_coe, SModEq, SModEq.zero, Subsingleton, Subsingleton.elim, add_comm, coeff_coe, coeff_trunc, degree_trunc_lt, eq_or_ne, g.isWeierstrassDivisionAt_zero, isWeierstrassDivisionAt_zero, mul_top
-/
theorem isWeierstrassDivisionAt_div_mod [IsAdicComplete I A] :
    f.IsWeierstrassDivisionAt g (H.div f) (H.mod f) I := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    rw [Subsingleton.elim f 0]; rw [Subsingleton.elim (H.div 0) 0]; rw [Subsingleton.elim (H.mod 0) 0]
    exact g.isWeierstrassDivisionAt_zero _
  constructor
  · exact degree_trunc_lt _ _
  · rw [mod, add_comm, ← sub_eq_iff_eq_add]
    ext i
    rw [Polynomial.coeff_coe]; rw [coeff_trunc]
    split_ifs with hi
    · rfl
    refine IsHausdorff.haus' (I := I) _ fun k => ?_
    rw [SModEq.zero]; rw [smul_eq_mul]; rw [Ideal.mul_top]; rw [show f - g * H.div f =
      f - g * (H.seq f k) - g * (H.div f - (H.seq f k)) by ring]; rw [map_sub]
exact Ideal.sub_mem _ (H.coeff_seq_mem f k (not_lt.1 hi))
      coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (H.coeff_div_sub_seq_mem f k) i

/--
theorem `eq_zero_of_mul_eq` / 定理 `eq_zero_of_mul_eq`

English:
theorem eq_zero_of_mul_eq
  statement: [IsHausdorff I A]
  proof: by
  suffices forall k i, coeff i q in I ^ k by
    have hq : q = 0 := by
      ext i
      refine IsHausdorff.haus' (I := I) _ fun k => ?_
      rw [SModEq.zero]; rw [smul_eq_mul]; rw [Ideal.mul_top]
      exact this _ _
    rw [hq]; rw [mul_zero]; rw [Eq.comm]; rw [Polynomial.coe_eq_zero_iff] at heq
    exact ⟨hq, heq⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [g.eq_X_pow_mul_shift_add_trunc (g.map (Ideal.Quotient.mk I)).order.toNat] at heq
    have h1 : forall i, coeff i r in I ^ (k + 1) := fun i => by
      rcases lt_or_ge i (g.map (Ideal.Quotient.mk I)).order.toNat with hi | hi
      · rw [← heq, pow_succ']
        refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i (fun j hj => ?_)
          (fun j _ => ih j) i le_rfl
        rw [map_add]; rw [Polynomial.coeff_coe]
        refine Ideal.add_mem _ ?_ (g.coeff_trunc_order_mem I j)
        simp_rw [coeff_X_pow_mul', if_neg (lt_of_le_of_lt hj hi).not_ge, zero_mem]
      simp_rw [Polynomial.coeff_coe,
        Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by simpa)), zero_mem]
    rw [add_mul]; rw [mul_comm (X ^ _)]; rw [← eq_sub_iff_add_eq] at heq
    replace heq := congr(H.isUnit_shift.unit⁻¹ * $heq)
    rw [← mul_assoc]; rw [← mul_assoc]; rw [IsUnit.val_inv_mul]; rw [one_mul] at heq
    intro i
    rw [← coeff_X_pow_mul _ (g.map (Ideal.Quotient.mk I)).order.toNat i]; rw [heq]
    refine coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (fun i => ?_) _
    rw [map_sub]
    refine Ideal.sub_mem _ (h1 _) ?_
    rw [pow_succ']
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (fun i => ?_) ih _
    simp_rw [Polynomial.coeff_coe, g.coeff_trunc_order_mem]

中文:
定理 eq_zero_of_mul_eq
  结论: [是豪斯多夫 I A]
  证明: by
  suffices forall k i, coeff i q in I ^ k by
    have hq : q = 0 := by
      ext i
      refine IsHausdorff.haus' (I := I) _ fun k => ?_
      rw [SModEq.zero]; rw [smul_eq_mul]; rw [Ideal.mul_top]
      exact this _ _
    rw [hq]; rw [mul_zero]; rw [Eq.comm]; rw [Polynomial.coe_eq_zero_iff] at heq
    exact ⟨hq, heq⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [g.eq_X_pow_mul_shift_add_trunc (g.map (Ideal.Quotient.mk I)).order.toNat] at heq
    have h1 : forall i, coeff i r in I ^ (k + 1) := fun i => by
      rcases lt_or_ge i (g.map (Ideal.Quotient.mk I)).order.toNat with hi | hi
      · rw [← heq, pow_succ']
        refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i (fun j hj => ?_)
          (fun j _ => ih j) i le_rfl
        rw [map_add]; rw [Polynomial.coeff_coe]
        refine Ideal.add_mem _ ?_ (g.coeff_trunc_order_mem I j)
        simp_rw [coeff_X_pow_mul', if_neg (lt_of_le_of_lt hj hi).not_ge, zero_mem]
      simp_rw [Polynomial.coeff_coe,
        Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by simpa)), zero_mem]
    rw [add_mul]; rw [mul_comm (X ^ _)]; rw [← eq_sub_iff_add_eq] at heq
    replace heq := congr(H.isUnit_shift.unit⁻¹ * $heq)
    rw [← mul_assoc]; rw [← mul_assoc]; rw [IsUnit.val_inv_mul]; rw [one_mul] at heq
    intro i
    rw [← coeff_X_pow_mul _ (g.map (Ideal.Quotient.mk I)).order.toNat i]; rw [heq]
    refine coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (fun i => ?_) _
    rw [map_sub]
    refine Ideal.sub_mem _ (h1 _) ?_
    rw [pow_succ']
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (fun i => ?_) ih _
    simp_rw [Polynomial.coeff_coe, g.coeff_trunc_order_mem]

Depends on / 依赖: Eq.comm, Ideal.Quotient.mk, Ideal.mul_top, IsHausdorff, IsHausdorff.haus, Polynomial, Polynomial.coe_eq_zero_iff, Quotient, SModEq, SModEq.zero, coe_eq_zero_iff, eq_X_pow_mul_shift_add_trunc, g.eq_X_pow_mul_shift_add_trunc, g.map, lt_or_ge, mul_top, mul_zero, order.toNat, smul_eq_mul
-/
theorem eq_zero_of_mul_eq [IsHausdorff I A]
    {q : A⟦X⟧} {r : A[X]} (hdeg : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat)
    (heq : g * q = r) : q = 0 ∧ r = 0 := by
  suffices forall k i, coeff i q in I ^ k by
    have hq : q = 0 := by
      ext i
      refine IsHausdorff.haus' (I := I) _ fun k => ?_
      rw [SModEq.zero]; rw [smul_eq_mul]; rw [Ideal.mul_top]
      exact this _ _
    rw [hq]; rw [mul_zero]; rw [Eq.comm]; rw [Polynomial.coe_eq_zero_iff] at heq
    exact ⟨hq, heq⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [g.eq_X_pow_mul_shift_add_trunc (g.map (Ideal.Quotient.mk I)).order.toNat] at heq
    have h1 : forall i, coeff i r in I ^ (k + 1) := fun i => by
      rcases lt_or_ge i (g.map (Ideal.Quotient.mk I)).order.toNat with hi | hi
      · rw [← heq, pow_succ']
        refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i (fun j hj => ?_)
          (fun j _ => ih j) i le_rfl
        rw [map_add]; rw [Polynomial.coeff_coe]
        refine Ideal.add_mem _ ?_ (g.coeff_trunc_order_mem I j)
        simp_rw [coeff_X_pow_mul', if_neg (lt_of_le_of_lt hj hi).not_ge, zero_mem]
      simp_rw [Polynomial.coeff_coe,
        Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by simpa)), zero_mem]
    rw [add_mul]; rw [mul_comm (X ^ _)]; rw [← eq_sub_iff_add_eq] at heq
    replace heq := congr(H.isUnit_shift.unit⁻¹ * $heq)
    rw [← mul_assoc]; rw [← mul_assoc]; rw [IsUnit.val_inv_mul]; rw [one_mul] at heq
    intro i
    rw [← coeff_X_pow_mul _ (g.map (Ideal.Quotient.mk I)).order.toNat i]; rw [heq]
    refine coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (fun i => ?_) _
    rw [map_sub]
    refine Ideal.sub_mem _ (h1 _) ?_
    rw [pow_succ']
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (fun i => ?_) ih _
    simp_rw [Polynomial.coeff_coe, g.coeff_trunc_order_mem]

/--
theorem `eq_of_mul_add_eq_mul_add` / 定理 `eq_of_mul_add_eq_mul_add`

English:
theorem eq_of_mul_add_eq_mul_add
  statement: [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]}
  proof: by
  replace heq : g * (q - q') = ↑(r' - r) := by
    rw [← eq_sub_iff_add_eq] at heq
    rw [Polynomial.coe_sub]; rw [mul_sub]; rw [heq]
    ring
  have h := H.eq_zero_of_mul_eq (lt_of_le_of_lt (r'.degree_sub_le r) (max_lt hr' hr)) heq
  simp_rw [sub_eq_zero] at h
  exact ⟨h.1, h.2.symm⟩

@[simp]

中文:
定理 eq_of_mul_add_eq_mul_add
  结论: [是豪斯多夫 I A] {q q' : A⟦X⟧} {r r' : A[X]}
  证明: by
  replace heq : g * (q - q') = ↑(r' - r) := by
    rw [← eq_sub_iff_add_eq] at heq
    rw [Polynomial.coe_sub]; rw [mul_sub]; rw [heq]
    ring
  have h := H.eq_zero_of_mul_eq (lt_of_le_of_lt (r'.degree_sub_le r) (max_lt hr' hr)) heq
  simp_rw [sub_eq_zero] at h
  exact ⟨h.1, h.2.symm⟩

@[simp]

Depends on / 依赖: H.eq_zero_of_mul_eq, Polynomial, Polynomial.coe_sub, coe_sub, degree_sub_le, eq_sub_iff_add_eq, eq_zero_of_mul_eq, lt_of_le_of_lt, max_lt, mul_sub, replace, simp_rw, sub_eq_zero
-/
theorem eq_of_mul_add_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]}
    (hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat)
    (hr' : r'.degree < (g.map (Ideal.Quotient.mk I)).order.toNat)
    (heq : g * q + r = g * q' + r') : q = q' ∧ r = r' := by
  replace heq : g * (q - q') = ↑(r' - r) := by
    rw [← eq_sub_iff_add_eq] at heq
    rw [Polynomial.coe_sub]; rw [mul_sub]; rw [heq]
    ring
  have h := H.eq_zero_of_mul_eq (lt_of_le_of_lt (r'.degree_sub_le r) (max_lt hr' hr)) heq
  simp_rw [sub_eq_zero] at h
  exact ⟨h.1, h.2.symm⟩

@[simp]
/--
theorem `div_add` / 定理 `div_add`

English:
theorem div_add
  given: [IsAdicComplete I A]
  statement: H.div (f + f') = H.div f + H.div f'
  proof: by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]

中文:
定理 div_add
  条件: [是AdicComplete I A]
  结论: H.div (f + f') = H.div f + H.div f'
  证明: by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]

Depends on / 依赖: H.eq_of_mul_add_eq_mul_add, H.isWeierstrassDivisionAt_div_mod, H1.degree_lt, H1.eq_mul_add, H2.degree_lt, H2.eq_mul_add.symm.trans, degree_lt, eq_mul_add, eq_of_mul_add_eq_mul_add, isWeierstrassDivisionAt_div_mod
-/
theorem div_add [IsAdicComplete I A] : H.div (f + f') = H.div f + H.div f' := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]
/--
theorem `div_smul` / 定理 `div_smul`

English:
theorem div_smul
  given: [IsAdicComplete I A]
  statement: H.div (a • f) = a • H.div f
  proof: by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]

中文:
定理 div_smul
  条件: [是AdicComplete I A]
  结论: H.div (a • f) = a • H.div f
  证明: by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]

Depends on / 依赖: H.eq_of_mul_add_eq_mul_add, H.isWeierstrassDivisionAt_div_mod, H1.degree_lt, H1.eq_mul_add, H2.degree_lt, H2.eq_mul_add.symm.trans, degree_lt, eq_mul_add, eq_of_mul_add_eq_mul_add, isWeierstrassDivisionAt_div_mod
-/
theorem div_smul [IsAdicComplete I A] : H.div (a • f) = a • H.div f := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]
/--
theorem `div_zero` / 定理 `div_zero`

English:
theorem div_zero
  given: [IsAdicComplete I A]
  statement: H.div 0 = 0
  proof: by
  simpa using H.div_smul 0 0

@[simp]

中文:
定理 div_zero
  条件: [是AdicComplete I A]
  结论: H.div 0 = 0
  证明: by
  simpa using H.div_smul 0 0

@[simp]

Depends on / 依赖: H.div_smul, div_smul
-/
theorem div_zero [IsAdicComplete I A] : H.div 0 = 0 := by
  simpa using H.div_smul 0 0

@[simp]
/--
theorem `mod_add` / 定理 `mod_add`

English:
theorem mod_add
  given: [IsAdicComplete I A]
  statement: H.mod (f + f') = H.mod f + H.mod f'
  proof: by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]

中文:
定理 mod_add
  条件: [是AdicComplete I A]
  结论: H.mod (f + f') = H.mod f + H.mod f'
  证明: by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]

Depends on / 依赖: H.eq_of_mul_add_eq_mul_add, H.isWeierstrassDivisionAt_div_mod, H1.degree_lt, H1.eq_mul_add, H2.degree_lt, H2.eq_mul_add.symm.trans, degree_lt, eq_mul_add, eq_of_mul_add_eq_mul_add, isWeierstrassDivisionAt_div_mod
-/
theorem mod_add [IsAdicComplete I A] : H.mod (f + f') = H.mod f + H.mod f' := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]
/--
theorem `mod_smul` / 定理 `mod_smul`

English:
theorem mod_smul
  given: [IsAdicComplete I A]
  statement: H.mod (a • f) = a • H.mod f
  proof: by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]

中文:
定理 mod_smul
  条件: [是AdicComplete I A]
  结论: H.mod (a • f) = a • H.mod f
  证明: by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]

Depends on / 依赖: H.eq_of_mul_add_eq_mul_add, H.isWeierstrassDivisionAt_div_mod, H1.degree_lt, H1.eq_mul_add, H2.degree_lt, H2.eq_mul_add.symm.trans, degree_lt, eq_mul_add, eq_of_mul_add_eq_mul_add, isWeierstrassDivisionAt_div_mod
-/
theorem mod_smul [IsAdicComplete I A] : H.mod (a • f) = a • H.mod f := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]
/--
theorem `mod_zero` / 定理 `mod_zero`

English:
theorem mod_zero
  given: [IsAdicComplete I A]
  statement: H.mod 0 = 0
  proof: by
  simpa using H.mod_smul 0 0

中文:
定理 mod_zero
  条件: [是AdicComplete I A]
  结论: H.mod 0 = 0
  证明: by
  simpa using H.mod_smul 0 0

Depends on / 依赖: H.mod_smul, mod_smul
-/
theorem mod_zero [IsAdicComplete I A] : H.mod 0 = 0 := by
  simpa using H.mod_smul 0 0

/--
Definition of `mod'` / `mod'` 的定义

English:
definition mod'
  signature: [IsAdicComplete I A]
  body: Quotient.lift (fun f => H.mod f) fun f f' hf => by
    have hf := (Submodule.quotientRel_def (p := Ideal.span {g})).mp hf
    rw [Ideal.mem_span_singleton'] at hf
    obtain ⟨a, ha⟩ := hf
    obtain ⟨hf1, hf2⟩ := H.isWeierstrassDivisionAt_div_mod f
    obtain ⟨hf'1, hf'2⟩ := H.isWeierstrassDivisionAt_div_mod f'
    rw [eq_sub_iff_add_eq]; rw [hf2]; rw [hf'2]; rw [← add_assoc]; rw [mul_comm]; rw [← mul_add] at ha
    exact (H.eq_of_mul_add_eq_mul_add hf'1 hf1 ha).2.symm
  map_add' f f' := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    obtain ⟨f', rfl⟩ := Ideal.Quotient.mk_surjective f'
    exact H.mod_add f f'
  map_smul' a f := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    exact H.mod_smul a f

@[simp]

中文:
定义 mod'
  签名: [是AdicComplete I A]
  定义体: Quotient.lift (fun f => H.mod f) fun f f' hf => by
    have hf := (Submodule.quotientRel_def (p := Ideal.span {g})).mp hf
    rw [Ideal.mem_span_singleton'] at hf
    obtain ⟨a, ha⟩ := hf
    obtain ⟨hf1, hf2⟩ := H.isWeierstrassDivisionAt_div_mod f
    obtain ⟨hf'1, hf'2⟩ := H.isWeierstrassDivisionAt_div_mod f'
    rw [eq_sub_iff_add_eq]; rw [hf2]; rw [hf'2]; rw [← add_assoc]; rw [mul_comm]; rw [← mul_add] at ha
    exact (H.eq_of_mul_add_eq_mul_add hf'1 hf1 ha).2.symm
  map_add' f f' := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    obtain ⟨f', rfl⟩ := Ideal.Quotient.mk_surjective f'
    exact H.mod_add f f'
  map_smul' a f := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    exact H.mod_smul a f

@[simp]

Depends on / 依赖: H.eq_of_mul_add_eq_mul_add, H.isWeierstrassDivisionAt_div_mod, H.mod, Ideal.Quotient, Ideal.mem_span_singleton, Ideal.span, Quotient, Quotient.lift, Submodule, Submodule.quotientRel_def, add_assoc, eq_of_mul_add_eq_mul_add, eq_sub_iff_add_eq, isWeierstrassDivisionAt_div_mod, map_add, mem_span_singleton, mul_add, mul_comm, quotientRel_def
-/
noncomputable def mod' [IsAdicComplete I A] : A⟦X⟧ ⧸ Ideal.span {g} ->ₗ[A] A[X] where
  toFun := Quotient.lift (fun f => H.mod f) fun f f' hf => by
    have hf := (Submodule.quotientRel_def (p := Ideal.span {g})).mp hf
    rw [Ideal.mem_span_singleton'] at hf
    obtain ⟨a, ha⟩ := hf
    obtain ⟨hf1, hf2⟩ := H.isWeierstrassDivisionAt_div_mod f
    obtain ⟨hf'1, hf'2⟩ := H.isWeierstrassDivisionAt_div_mod f'
    rw [eq_sub_iff_add_eq]; rw [hf2]; rw [hf'2]; rw [← add_assoc]; rw [mul_comm]; rw [← mul_add] at ha
    exact (H.eq_of_mul_add_eq_mul_add hf'1 hf1 ha).2.symm
  map_add' f f' := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    obtain ⟨f', rfl⟩ := Ideal.Quotient.mk_surjective f'
    exact H.mod_add f f'
  map_smul' a f := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    exact H.mod_smul a f

@[simp]
/--
theorem `mod'_mk_eq_mod` / 定理 `mod'_mk_eq_mod`

English:
theorem mod'_mk_eq_mod
  given: [IsAdicComplete I A] {f : A⟦X⟧}
  proof: rfl

中文:
定理 mod'_mk_eq_mod
  条件: [是AdicComplete I A] {f : A⟦X⟧}
  证明: rfl
-/
theorem mod'_mk_eq_mod [IsAdicComplete I A] {f : A⟦X⟧} :
    H.mod' (Ideal.Quotient.mk _ f) = H.mod f := rfl

/--
theorem `div_coe_eq_zero` / 定理 `div_coe_eq_zero`

English:
theorem div_coe_eq_zero
  statement: [IsAdicComplete I A] {r : A[X]}
  proof: by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).1

中文:
定理 div_coe_eq_zero
  结论: [是AdicComplete I A] {r : A[X]}
  证明: by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).1

Depends on / 依赖: H.div, H.eq_of_mul_add_eq_mul_add, H.isWeierstrassDivisionAt_div_mod, eq_of_mul_add_eq_mul_add, h2.symm, isWeierstrassDivisionAt_div_mod
-/
theorem div_coe_eq_zero [IsAdicComplete I A] {r : A[X]}
    (hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat) : H.div r = 0 := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).1

/--
theorem `mod_coe_eq_self` / 定理 `mod_coe_eq_self`

English:
theorem mod_coe_eq_self
  statement: [IsAdicComplete I A] {r : A[X]}
  proof: by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).2

@[simp]

中文:
定理 mod_coe_eq_self
  结论: [是AdicComplete I A] {r : A[X]}
  证明: by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).2

@[simp]

Depends on / 依赖: H.div, H.eq_of_mul_add_eq_mul_add, H.isWeierstrassDivisionAt_div_mod, eq_of_mul_add_eq_mul_add, h2.symm, isWeierstrassDivisionAt_div_mod
-/
theorem mod_coe_eq_self [IsAdicComplete I A] {r : A[X]}
    (hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat) : H.mod r = r := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).2

@[simp]
/--
theorem `mk_mod'_eq_self` / 定理 `mk_mod'_eq_self`

English:
theorem mk_mod'_eq_self
  given: [IsAdicComplete I A] {f : A⟦X⟧ ⧸ Ideal.span {g}}
  proof: by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  rw [mod'_mk_eq_mod]; rw [Eq.comm]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [Ideal.mem_span_singleton']
  use H.div f
  rw [eq_sub_iff_add_eq]; rw [mul_comm]; rw [(H.isWeierstrassDivisionAt_div_mod f).2.symm]

中文:
定理 mk_mod'_eq_self
  条件: [是AdicComplete I A] {f : A⟦X⟧ ⧸ 理想.span {g}}
  证明: by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  rw [mod'_mk_eq_mod]; rw [Eq.comm]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [Ideal.mem_span_singleton']
  use H.div f
  rw [eq_sub_iff_add_eq]; rw [mul_comm]; rw [(H.isWeierstrassDivisionAt_div_mod f).2.symm]

Depends on / 依赖: Eq.comm, H.div, H.isWeierstrassDivisionAt_div_mod, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.Quotient.mk_surjective, Ideal.mem_span_singleton, Quotient, _mk_eq_mod, eq_sub_iff_add_eq, isWeierstrassDivisionAt_div_mod, mem_span_singleton, mk_eq_mk_iff_sub_mem, mk_surjective, mul_comm
-/
theorem mk_mod'_eq_self [IsAdicComplete I A] {f : A⟦X⟧ ⧸ Ideal.span {g}} :
    Ideal.Quotient.mk _ (H.mod' f : A⟦X⟧) = f := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  rw [mod'_mk_eq_mod]; rw [Eq.comm]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [Ideal.mem_span_singleton']
  use H.div f
  rw [eq_sub_iff_add_eq]; rw [mul_comm]; rw [(H.isWeierstrassDivisionAt_div_mod f).2.symm]

end IsWeierstrassDivisorAt

section Equiv

variable {g : A[X]} {I : Ideal A} (H : g.IsDistinguishedAt I) [IsAdicComplete I A]
include H

/-- A distinguished polynomial `g` induces a natural isomorphism `A[X] / (g) ≃ₐ[A] A⟦X⟧ / (g)`. -/
@[simps! apply symm_apply]
/--
Definition of `_root_.Polynomial.IsDistinguishedAt.algEquivQuotient` / `_root_.Polynomial.IsDistinguishedAt.algEquivQuotient` 的定义

English:
definition _root_.Polynomial.IsDistinguishedAt.algEquivQuotient
  signature: :
  body: Ideal.quotientMapₐ _ (Polynomial.coeToPowerSeries.algHom A) fun a ha => by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [Ideal.mem_comap, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self,
      map_id, id_eq, Ideal.mem_span_singleton']
    exact ⟨b, by simp [← hb]⟩
  invFun := Ideal.Quotient.mk _ ∘ H.isWeierstrassDivisorAt'.mod'
  left_inv f := by
    rcases subsingleton_or_nontrivial A with _ | _
    · have : Subsingleton A[X] := inferInstance
      have : Subsingleton (A[X] ⧸ Ideal.span {g}) := Quot.Subsingleton
      exact Subsingleton.elim _ _
    have hI : I != ⊤ := by
      rintro rfl
      exact not_subsingleton _ ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    have := Ideal.Quotient.nontrivial_iff.mpr hI
    obtain ⟨f, hfdeg, rfl⟩ : exists r : A[X], r.degree < g.degree ∧ Ideal.Quotient.mk _ r = f := by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
      refine ⟨f %ₘ g, Polynomial.degree_modByMonic_lt f H.monic, ?_⟩
      rw [Eq.comm]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [Ideal.mem_span_singleton']
      exact ⟨f /ₘ g, by rw [Polynomial.modByMonic_eq_sub_mul_div]; ring⟩
    have h1 : g.degree = ((g : A⟦X⟧).map (Ideal.Quotient.mk I)).order.toNat := by
      convert!
        H.degree_eq_coe_lift_order_map g 1 (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one])
          (by simp)
      exact (ENat.lift_eq_toNat_of_lt_top _).symm
    dsimp
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [Ideal.mem_span_singleton']
    exact ⟨0, by simp [H.isWeierstrassDivisorAt'.mod_coe_eq_self (hfdeg.trans_eq h1)]⟩
  right_inv f := by exact H.isWeierstrassDivisorAt'.mk_mod'_eq_self

中文:
定义 _root_.多项式.是DistinguishedAt.algEquivQuotient
  签名: :
  定义体: Ideal.quotientMapₐ _ (Polynomial.coeToPowerSeries.algHom A) fun a ha => by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [Ideal.mem_comap, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self,
      map_id, id_eq, Ideal.mem_span_singleton']
    exact ⟨b, by simp [← hb]⟩
  invFun := Ideal.Quotient.mk _ ∘ H.isWeierstrassDivisorAt'.mod'
  left_inv f := by
    rcases subsingleton_or_nontrivial A with _ | _
    · have : Subsingleton A[X] := inferInstance
      have : Subsingleton (A[X] ⧸ Ideal.span {g}) := Quot.Subsingleton
      exact Subsingleton.elim _ _
    have hI : I != ⊤ := by
      rintro rfl
      exact not_subsingleton _ ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    have := Ideal.Quotient.nontrivial_iff.mpr hI
    obtain ⟨f, hfdeg, rfl⟩ : exists r : A[X], r.degree < g.degree ∧ Ideal.Quotient.mk _ r = f := by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
      refine ⟨f %ₘ g, Polynomial.degree_modByMonic_lt f H.monic, ?_⟩
      rw [Eq.comm]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [Ideal.mem_span_singleton']
      exact ⟨f /ₘ g, by rw [Polynomial.modByMonic_eq_sub_mul_div]; ring⟩
    have h1 : g.degree = ((g : A⟦X⟧).map (Ideal.Quotient.mk I)).order.toNat := by
      convert!
        H.degree_eq_coe_lift_order_map g 1 (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one])
          (by simp)
      exact (ENat.lift_eq_toNat_of_lt_top _).symm
    dsimp
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [Ideal.mem_span_singleton']
    exact ⟨0, by simp [H.isWeierstrassDivisorAt'.mod_coe_eq_self (hfdeg.trans_eq h1)]⟩
  right_inv f := by exact H.isWeierstrassDivisorAt'.mk_mod'_eq_self

Depends on / 依赖: Algebra, Algebra.algebraMap_self, H.isWeierstrassDivisorAt, Ideal.Quotient.mk, Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.quotientMap, Ideal.span, Polynomial, Polynomial.coeToPowerSeries.algHom, Polynomial.coeToPowerSeries.algHom_apply, Quotient, Subsingleton, algHom, algHom_apply, algebraMap_self, coeToPowerSeries, id_eq, invFun, isWeierstrassDivisorAt
-/
noncomputable def _root_.Polynomial.IsDistinguishedAt.algEquivQuotient :
    (A[X] ⧸ Ideal.span {g}) ≃ₐ[A] A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)} where
  __ := Ideal.quotientMapₐ _ (Polynomial.coeToPowerSeries.algHom A) fun a ha => by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [Ideal.mem_comap, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self,
      map_id, id_eq, Ideal.mem_span_singleton']
    exact ⟨b, by simp [← hb]⟩
  invFun := Ideal.Quotient.mk _ ∘ H.isWeierstrassDivisorAt'.mod'
  left_inv f := by
    rcases subsingleton_or_nontrivial A with _ | _
    · have : Subsingleton A[X] := inferInstance
      have : Subsingleton (A[X] ⧸ Ideal.span {g}) := Quot.Subsingleton
      exact Subsingleton.elim _ _
    have hI : I != ⊤ := by
      rintro rfl
      exact not_subsingleton _ ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    have := Ideal.Quotient.nontrivial_iff.mpr hI
    obtain ⟨f, hfdeg, rfl⟩ : exists r : A[X], r.degree < g.degree ∧ Ideal.Quotient.mk _ r = f := by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
      refine ⟨f %ₘ g, Polynomial.degree_modByMonic_lt f H.monic, ?_⟩
      rw [Eq.comm]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [Ideal.mem_span_singleton']
      exact ⟨f /ₘ g, by rw [Polynomial.modByMonic_eq_sub_mul_div]; ring⟩
    have h1 : g.degree = ((g : A⟦X⟧).map (Ideal.Quotient.mk I)).order.toNat := by
      convert!
        H.degree_eq_coe_lift_order_map g 1 (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one])
          (by simp)
      exact (ENat.lift_eq_toNat_of_lt_top _).symm
    dsimp
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [Ideal.mem_span_singleton']
    exact ⟨0, by simp [H.isWeierstrassDivisorAt'.mod_coe_eq_self (hfdeg.trans_eq h1)]⟩
  right_inv f := by exact H.isWeierstrassDivisorAt'.mk_mod'_eq_self

end Equiv

end IsWeierstrassDivisorAt

section IsLocalRing

variable [IsLocalRing A] (a : A) (f f' g : A⟦X⟧)

variable {g} in
/--
theorem `exists_isWeierstrassDivision` / 定理 `exists_isWeierstrassDivision`

English:
theorem exists_isWeierstrassDivision
  statement: [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  proof: ⟨_, _, (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f⟩

中文:
定理 存在_isWeierstrassDivision
  结论: [是AdicComplete (是局部环.maximalIdeal A) A]
  证明: ⟨_, _, (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f⟩

Depends on / 依赖: IsWeierstrassDivisor, IsWeierstrassDivisor.of_map_ne_zero, isWeierstrassDivisionAt_div_mod, of_map_ne_zero
-/
theorem exists_isWeierstrassDivision [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hg : g.map (IsLocalRing.residue A) != 0) : exists q r, f.IsWeierstrassDivision g q r :=
  ⟨_, _, (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f⟩

-- Unfortunately there is no Unicode subscript `w`.

/--
Definition of `weierstrassDiv` / `weierstrassDiv` 的定义

English:
definition weierstrassDiv
  signature: [IsPrecomplete (IsLocalRing.maximalIdeal A) A]
  body: open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) != 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).div f
  else
    0

中文:
定义 weierstrassDiv
  签名: [是Precomplete (是局部环.maximalIdeal A) A]
  定义体: open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) != 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).div f
  else
    0

Depends on / 依赖: Classical, IsLocalRing, IsLocalRing.residue, IsWeierstrassDivisor, IsWeierstrassDivisor.of_map_ne_zero, g.map, of_map_ne_zero, residue, scoped
-/
noncomputable def weierstrassDiv [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : A⟦X⟧ :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) != 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).div f
  else
    0

/--
Definition of `weierstrassMod` / `weierstrassMod` 的定义

English:
definition weierstrassMod
  signature: [IsPrecomplete (IsLocalRing.maximalIdeal A) A]
  body: open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) != 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).mod f
  else
    0

@[inherit_doc]
infixl:70 " /ʷ " => weierstrassDiv

@[inherit_doc]
infixl:70 " %ʷ " => weierstrassMod

@[simp]

中文:
定义 weierstrassMod
  签名: [是Precomplete (是局部环.maximalIdeal A) A]
  定义体: open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) != 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).mod f
  else
    0

@[inherit_doc]
infixl:70 " /ʷ " => weierstrassDiv

@[inherit_doc]
infixl:70 " %ʷ " => weierstrassMod

@[simp]

Depends on / 依赖: Classical, IsLocalRing, IsLocalRing.residue, IsWeierstrassDivisor, IsWeierstrassDivisor.of_map_ne_zero, g.map, of_map_ne_zero, residue, scoped
-/
noncomputable def weierstrassMod [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : A[X] :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) != 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).mod f
  else
    0

@[inherit_doc]
infixl:70 " /ʷ " => weierstrassDiv

@[inherit_doc]
infixl:70 " %ʷ " => weierstrassMod

@[simp]
/--
theorem `weierstrassDiv_zero_right` / 定理 `weierstrassDiv_zero_right`

English:
theorem weierstrassDiv_zero_right
  given: [IsPrecomplete (IsLocalRing.maximalIdeal A) A]
  statement: f /ʷ 0 = 0
  proof: by
  rw [weierstrassDiv]; rw [dif_neg (by simp)]

alias weierstrassDiv_zero := weierstrassDiv_zero_right

@[simp]

中文:
定理 weierstrassDiv_zero_right
  条件: [是Precomplete (是局部环.maximalIdeal A) A]
  结论: f /ʷ 0 = 0
  证明: by
  rw [weierstrassDiv]; rw [dif_neg (by simp)]

alias weierstrassDiv_zero := weierstrassDiv_zero_right

@[simp]

Depends on / 依赖: dif_neg, weierstrassDiv
-/
theorem weierstrassDiv_zero_right [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : f /ʷ 0 = 0 := by
  rw [weierstrassDiv]; rw [dif_neg (by simp)]

alias weierstrassDiv_zero := weierstrassDiv_zero_right

@[simp]
/--
theorem `weierstrassMod_zero_right` / 定理 `weierstrassMod_zero_right`

English:
theorem weierstrassMod_zero_right
  given: [IsPrecomplete (IsLocalRing.maximalIdeal A) A]
  statement: f %ʷ 0 = 0
  proof: by
  rw [weierstrassMod]; rw [dif_neg (by simp)]

alias weierstrassMod_zero := weierstrassMod_zero_right

中文:
定理 weierstrassMod_zero_right
  条件: [是Precomplete (是局部环.maximalIdeal A) A]
  结论: f %ʷ 0 = 0
  证明: by
  rw [weierstrassMod]; rw [dif_neg (by simp)]

alias weierstrassMod_zero := weierstrassMod_zero_right

Depends on / 依赖: dif_neg, weierstrassMod
-/
theorem weierstrassMod_zero_right [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : f %ʷ 0 = 0 := by
  rw [weierstrassMod]; rw [dif_neg (by simp)]

alias weierstrassMod_zero := weierstrassMod_zero_right

/--
theorem `degree_weierstrassMod_lt` / 定理 `degree_weierstrassMod_lt`

English:
theorem degree_weierstrassMod_lt
  given: [IsPrecomplete (IsLocalRing.maximalIdeal A) A]
  proof: by
  rw [weierstrassMod]
  split_ifs with hg
  · exact degree_trunc_lt _ _
  · nontriviality A
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _

中文:
定理 degree_weierstrassMod_lt
  条件: [是Precomplete (是局部环.maximalIdeal A) A]
  证明: by
  rw [weierstrassMod]
  split_ifs with hg
  · exact degree_trunc_lt _ _
  · nontriviality A
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _

Depends on / 依赖: Polynomial, Polynomial.degree_zero, WithBot, WithBot.bot_lt_coe, bot_lt_coe, degree_trunc_lt, degree_zero, nontriviality, split_ifs, weierstrassMod
-/
theorem degree_weierstrassMod_lt [IsPrecomplete (IsLocalRing.maximalIdeal A) A] :
    (f %ʷ g).degree < (g.map (IsLocalRing.residue A)).order.toNat := by
  rw [weierstrassMod]
  split_ifs with hg
  · exact degree_trunc_lt _ _
  · nontriviality A
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _

section

variable {g} (hg : g.map (IsLocalRing.residue A) != 0)
include hg

/--
theorem `isWeierstrassDivision_weierstrassDiv_weierstrassMod` / 定理 `isWeierstrassDivision_weierstrassDiv_weierstrassMod`

English:
theorem isWeierstrassDivision_weierstrassDiv_weierstrassMod
  proof: by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f

中文:
定理 isWeierstrassDivision_weierstrassDiv_weierstrassMod
  证明: by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f

Depends on / 依赖: IsWeierstrassDivisor, IsWeierstrassDivisor.of_map_ne_zero, dif_pos, isWeierstrassDivisionAt_div_mod, of_map_ne_zero, simp_rw, weierstrassDiv, weierstrassMod
-/
theorem isWeierstrassDivision_weierstrassDiv_weierstrassMod
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    f.IsWeierstrassDivision g (f /ʷ g) (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f

/--
theorem `eq_mul_weierstrassDiv_add_weierstrassMod` / 定理 `eq_mul_weierstrassDiv_add_weierstrassMod`

English:
theorem eq_mul_weierstrassDiv_add_weierstrassMod
  proof: by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact ((IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f).2

中文:
定理 eq_mul_weierstrassDiv_add_weierstrassMod
  证明: by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact ((IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f).2

Depends on / 依赖: IsWeierstrassDivisor, IsWeierstrassDivisor.of_map_ne_zero, dif_pos, isWeierstrassDivisionAt_div_mod, of_map_ne_zero, simp_rw, weierstrassDiv, weierstrassMod
-/
theorem eq_mul_weierstrassDiv_add_weierstrassMod
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    f = g * (f /ʷ g) + (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact ((IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f).2

variable {f} in
/--
theorem `IsWeierstrassDivision.elim` / 定理 `IsWeierstrassDivision.elim`

English:
theorem IsWeierstrassDivision.elim
  statement: [IsHausdorff (IsLocalRing.maximalIdeal A) A]
  proof: (IsWeierstrassDivisor.of_map_ne_zero hg).eq_of_mul_add_eq_mul_add H.1 H2.1 (H.2.symm.trans H2.2)

中文:
定理 IsWeierstrassDivision.elim
  结论: [是豪斯多夫 (是局部环.maximalIdeal A) A]
  证明: (IsWeierstrassDivisor.of_map_ne_zero hg).eq_of_mul_add_eq_mul_add H.1 H2.1 (H.2.symm.trans H2.2)

Depends on / 依赖: IsWeierstrassDivisor, IsWeierstrassDivisor.of_map_ne_zero, eq_of_mul_add_eq_mul_add, of_map_ne_zero, symm.trans
-/
theorem IsWeierstrassDivision.elim [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {q q' : A⟦X⟧} {r r' : A[X]}
    (H : f.IsWeierstrassDivision g q r) (H2 : f.IsWeierstrassDivision g q' r') : q = q' ∧ r = r' :=
  (IsWeierstrassDivisor.of_map_ne_zero hg).eq_of_mul_add_eq_mul_add H.1 H2.1 (H.2.symm.trans H2.2)

/--
theorem `IsWeierstrassDivision.eq_zero` / 定理 `IsWeierstrassDivision.eq_zero`

English:
theorem IsWeierstrassDivision.eq_zero
  statement: [IsHausdorff (IsLocalRing.maximalIdeal A) A]
  proof: H.elim hg (g.isWeierstrassDivisionAt_zero _)

中文:
定理 IsWeierstrassDivision.eq_zero
  结论: [是豪斯多夫 (是局部环.maximalIdeal A) A]
  证明: H.elim hg (g.isWeierstrassDivisionAt_zero _)

Depends on / 依赖: H.elim, g.isWeierstrassDivisionAt_zero, isWeierstrassDivisionAt_zero
-/
theorem IsWeierstrassDivision.eq_zero [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {q : A⟦X⟧} {r : A[X]}
    (H : IsWeierstrassDivision 0 g q r) : q = 0 ∧ r = 0 :=
  H.elim hg (g.isWeierstrassDivisionAt_zero _)

variable {f} in
/--
theorem `IsWeierstrassDivision.unique` / 定理 `IsWeierstrassDivision.unique`

English:
theorem IsWeierstrassDivision.unique
  statement: [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  proof: H.elim hg (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod hg)

中文:
定理 IsWeierstrassDivision.unique
  结论: [是AdicComplete (是局部环.maximalIdeal A) A]
  证明: H.elim hg (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod hg)

Depends on / 依赖: H.elim, f.isWeierstrassDivision_weierstrassDiv_weierstrassMod, isWeierstrassDivision_weierstrassDiv_weierstrassMod
-/
theorem IsWeierstrassDivision.unique [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {q : A⟦X⟧} {r : A[X]}
    (H : f.IsWeierstrassDivision g q r) : q = f /ʷ g ∧ r = f %ʷ g :=
  H.elim hg (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod hg)

end

@[simp]
/--
theorem `add_weierstrassDiv` / 定理 `add_weierstrassDiv`

English:
theorem add_weierstrassDiv
  given: [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  proof: by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]

中文:
定理 add_weierstrassDiv
  条件: [是AdicComplete (是局部环.maximalIdeal A) A]
  证明: by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]

Depends on / 依赖: simp_rw, split_ifs, weierstrassDiv
-/
theorem add_weierstrassDiv [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (f + f') /ʷ g = f /ʷ g + f' /ʷ g := by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]
/--
theorem `smul_weierstrassDiv` / 定理 `smul_weierstrassDiv`

English:
theorem smul_weierstrassDiv
  given: [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  proof: by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]

中文:
定理 smul_weierstrassDiv
  条件: [是AdicComplete (是局部环.maximalIdeal A) A]
  证明: by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]

Depends on / 依赖: epi_iff_surjective, i.proj_surjective, proj_surjective, simp_rw, split_ifs, weierstrassDiv
-/
theorem smul_weierstrassDiv [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (a • f) /ʷ g = a • (f /ʷ g) := by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]
/--
theorem `weierstrassDiv_zero_left` / 定理 `weierstrassDiv_zero_left`

English:
theorem weierstrassDiv_zero_left
  given: [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  statement: 0 /ʷ g = 0
  proof: by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

alias zero_weierstrassDiv := weierstrassDiv_zero_left

@[simp]

中文:
定理 weierstrassDiv_zero_left
  条件: [是AdicComplete (是局部环.maximalIdeal A) A]
  结论: 0 /ʷ g = 0
  证明: by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

alias zero_weierstrassDiv := weierstrassDiv_zero_left

@[simp]

Depends on / 依赖: simp_rw, split_ifs, weierstrassDiv
-/
theorem weierstrassDiv_zero_left [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : 0 /ʷ g = 0 := by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

alias zero_weierstrassDiv := weierstrassDiv_zero_left

@[simp]
/--
theorem `add_weierstrassMod` / 定理 `add_weierstrassMod`

English:
theorem add_weierstrassMod
  given: [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  proof: by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]

中文:
定理 add_weierstrassMod
  条件: [是AdicComplete (是局部环.maximalIdeal A) A]
  证明: by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]

Depends on / 依赖: simp_rw, split_ifs, weierstrassMod
-/
theorem add_weierstrassMod [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (f + f') %ʷ g = f %ʷ g + f' %ʷ g := by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]
/--
theorem `smul_weierstrassMod` / 定理 `smul_weierstrassMod`

English:
theorem smul_weierstrassMod
  given: [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  proof: by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]

中文:
定理 smul_weierstrassMod
  条件: [是AdicComplete (是局部环.maximalIdeal A) A]
  证明: by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]

Depends on / 依赖: simp_rw, split_ifs, weierstrassMod
-/
theorem smul_weierstrassMod [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (a • f) %ʷ g = a • (f %ʷ g) := by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]
/--
theorem `weierstrassMod_zero_left` / 定理 `weierstrassMod_zero_left`

English:
theorem weierstrassMod_zero_left
  given: [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  statement: 0 %ʷ g = 0
  proof: by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

alias zero_weierstrassMod := weierstrassMod_zero_left

中文:
定理 weierstrassMod_zero_left
  条件: [是AdicComplete (是局部环.maximalIdeal A) A]
  结论: 0 %ʷ g = 0
  证明: by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

alias zero_weierstrassMod := weierstrassMod_zero_left

Depends on / 依赖: simp_rw, split_ifs, weierstrassMod
-/
theorem weierstrassMod_zero_left [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : 0 %ʷ g = 0 := by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

alias zero_weierstrassMod := weierstrassMod_zero_left

end IsLocalRing

/-!

## Weierstrass preparation theorem

-/

/-- If `f` is a polynomial over `A`, `g` and `h` are power series over `A`,
then `PowerSeries.IsWeierstrassFactorizationAt g f h I` is a `Prop` which asserts that `f` is
distinguished at `I`, `h` is a unit, such that `g = f * h`. -/
@[mk_iff]
/--
Definition of `IsWeierstrassFactorizationAt` / `IsWeierstrassFactorizationAt` 的定义

English:
structure IsWeierstrassFactorizationAt
  parameters: (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) (I : Ideal A)
  axioms and operations (3):
    - isDistinguishedAt : f.IsDistinguishedAt I
    - isUnit : IsUnit h
    - eq_mul : g = f * h

中文:
结构 是WeierstrassFactorizationAt
  参数: (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) (I : 理想 A)
  公理与运算 (3 个):
    - isDistinguishedAt : f.是DistinguishedAt I
    - isUnit : 是单位 h
    - eq_mul : g = f * h
-/
structure IsWeierstrassFactorizationAt (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) (I : Ideal A) : Prop where
  isDistinguishedAt : f.IsDistinguishedAt I
  isUnit : IsUnit h
  eq_mul : g = f * h

/--
Definition of `IsWeierstrassFactorization` / `IsWeierstrassFactorization` 的定义

English:
abbreviation IsWeierstrassFactorization
  signature: (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) [IsLocalRing A]
  body: g.IsWeierstrassFactorizationAt f h (IsLocalRing.maximalIdeal A)

中文:
缩写 IsWeierstrassFactorization
  签名: (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) [是局部环 A]
  定义体: g.IsWeierstrassFactorizationAt f h (IsLocalRing.maximalIdeal A)

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal, IsWeierstrassFactorizationAt, g.IsWeierstrassFactorizationAt, maximalIdeal
-/
abbrev IsWeierstrassFactorization (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) [IsLocalRing A] : Prop :=
  g.IsWeierstrassFactorizationAt f h (IsLocalRing.maximalIdeal A)

namespace IsWeierstrassFactorizationAt

variable {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} {I : Ideal A} (H : g.IsWeierstrassFactorizationAt f h I)
include H

/--
theorem `map_ne_zero_of_ne_top` / 定理 `map_ne_zero_of_ne_top`

English:
theorem map_ne_zero_of_ne_top
  given: (hI : I != ⊤)
  statement: g.map (Ideal.Quotient.mk I) != 0
  proof: by
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [congr(map (Ideal.Quotient.mk I) $(H.eq_mul))]; rw [map_mul]; rw [← Polynomial.polynomial_map_coe]; rw [ne_eq]; rw [(H.isUnit.map _).mul_left_eq_zero]
  exact_mod_cast f.map_monic_ne_zero (f := Ideal.Quotient.mk I) H.isDistinguishedAt.monic

中文:
定理 map_ne_zero_of_ne_top
  条件: (hI : I != ⊤)
  结论: g.map (理想.商.mk I) != 0
  证明: by
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [congr(map (Ideal.Quotient.mk I) $(H.eq_mul))]; rw [map_mul]; rw [← Polynomial.polynomial_map_coe]; rw [ne_eq]; rw [(H.isUnit.map _).mul_left_eq_zero]
  exact_mod_cast f.map_monic_ne_zero (f := Ideal.Quotient.mk I) H.isDistinguishedAt.monic

Depends on / 依赖: H.eq_mul, H.isDistinguishedAt.monic, H.isUnit.map, Ideal.Quotient.mk, Ideal.Quotient.nontrivial_iff.mpr, Polynomial, Polynomial.polynomial_map_coe, Quotient, eq_mul, f.map_monic_ne_zero, isDistinguishedAt, isUnit, map_monic_ne_zero, map_mul, mul_left_eq_zero, ne_eq, nontrivial_iff, polynomial_map_coe
-/
theorem map_ne_zero_of_ne_top (hI : I != ⊤) : g.map (Ideal.Quotient.mk I) != 0 := by
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [congr(map (Ideal.Quotient.mk I) $(H.eq_mul))]; rw [map_mul]; rw [← Polynomial.polynomial_map_coe]; rw [ne_eq]; rw [(H.isUnit.map _).mul_left_eq_zero]
  exact_mod_cast f.map_monic_ne_zero (f := Ideal.Quotient.mk I) H.isDistinguishedAt.monic

/--
theorem `degree_eq_coe_lift_order_map_of_ne_top` / 定理 `degree_eq_coe_lift_order_map_of_ne_top`

English:
theorem degree_eq_coe_lift_order_map_of_ne_top
  given: (hI : I != ⊤)
  proof: by
  refine H.isDistinguishedAt.degree_eq_coe_lift_order_map g h ?_ H.eq_mul
  contrapose hI
  exact Ideal.eq_top_of_isUnit_mem _ hI (isUnit_iff_constantCoeff.1 H.isUnit)

中文:
定理 degree_eq_coe_lift_order_map_of_ne_top
  条件: (hI : I != ⊤)
  证明: by
  refine H.isDistinguishedAt.degree_eq_coe_lift_order_map g h ?_ H.eq_mul
  contrapose hI
  exact Ideal.eq_top_of_isUnit_mem _ hI (isUnit_iff_constantCoeff.1 H.isUnit)

Depends on / 依赖: H.eq_mul, H.isDistinguishedAt.degree_eq_coe_lift_order_map, H.isUnit, Ideal.eq_top_of_isUnit_mem, contrapose, degree_eq_coe_lift_order_map, eq_mul, eq_top_of_isUnit_mem, isDistinguishedAt, isUnit, isUnit_iff_constantCoeff
-/
theorem degree_eq_coe_lift_order_map_of_ne_top (hI : I != ⊤) :
    f.degree = (g.map (Ideal.Quotient.mk I)).order.lift
      (order_finite_iff_ne_zero.2 (H.map_ne_zero_of_ne_top hI)) := by
  refine H.isDistinguishedAt.degree_eq_coe_lift_order_map g h ?_ H.eq_mul
  contrapose hI
  exact Ideal.eq_top_of_isUnit_mem _ hI (isUnit_iff_constantCoeff.1 H.isUnit)

/--
theorem `natDegree_eq_toNat_order_map_of_ne_top` / 定理 `natDegree_eq_toNat_order_map_of_ne_top`

English:
theorem natDegree_eq_toNat_order_map_of_ne_top
  given: (hI : I != ⊤)
  proof: by
  rw [Polynomial.natDegree]; rw [H.degree_eq_coe_lift_order_map_of_ne_top hI]; rw [ENat.lift_eq_toNat_of_lt_top]
  exact WithBot.unbotD_coe _ _

中文:
定理 natDegree_eq_to自然数_order_map_of_ne_top
  条件: (hI : I != ⊤)
  证明: by
  rw [Polynomial.natDegree]; rw [H.degree_eq_coe_lift_order_map_of_ne_top hI]; rw [ENat.lift_eq_toNat_of_lt_top]
  exact WithBot.unbotD_coe _ _

Depends on / 依赖: ENat.lift_eq_toNat_of_lt_top, H.degree_eq_coe_lift_order_map_of_ne_top, Polynomial, Polynomial.natDegree, WithBot, WithBot.unbotD_coe, degree_eq_coe_lift_order_map_of_ne_top, lift_eq_toNat_of_lt_top, natDegree, unbotD_coe
-/
theorem natDegree_eq_toNat_order_map_of_ne_top (hI : I != ⊤) :
    f.natDegree = (g.map (Ideal.Quotient.mk I)).order.toNat := by
  rw [Polynomial.natDegree]; rw [H.degree_eq_coe_lift_order_map_of_ne_top hI]; rw [ENat.lift_eq_toNat_of_lt_top]
  exact WithBot.unbotD_coe _ _

/-- If `g = f * h` is a Weierstrass factorization, then there is a
natural isomorphism `A[X] / (f) ≃ₐ[A] A⟦X⟧ / (g)`. -/
@[simps! apply]
/--
Definition of `algEquivQuotient` / `algEquivQuotient` 的定义

English:
definition algEquivQuotient
  signature: [IsAdicComplete I A]
  body: H.isDistinguishedAt.algEquivQuotient.trans Ideal.quotientEquivAlgOfEq A
    by rw [H.eq_mul, Ideal.span_singleton_mul_right_unit H.isUnit]

@[simp]

中文:
定义 algEquivQuotient
  签名: [是AdicComplete I A]
  定义体: H.isDistinguishedAt.algEquivQuotient.trans Ideal.quotientEquivAlgOfEq A
    by rw [H.eq_mul, Ideal.span_singleton_mul_right_unit H.isUnit]

@[simp]

Depends on / 依赖: H.eq_mul, H.isDistinguishedAt.algEquivQuotient.trans, H.isUnit, Ideal.quotientEquivAlgOfEq, Ideal.span_singleton_mul_right_unit, algEquivQuotient, eq_mul, isDistinguishedAt, isUnit, quotientEquivAlgOfEq, span_singleton_mul_right_unit
-/
noncomputable def algEquivQuotient [IsAdicComplete I A] :
    (A[X] ⧸ Ideal.span {f}) ≃ₐ[A] A⟦X⟧ ⧸ Ideal.span {g} :=
H.isDistinguishedAt.algEquivQuotient.trans Ideal.quotientEquivAlgOfEq A
    by rw [H.eq_mul, Ideal.span_singleton_mul_right_unit H.isUnit]

@[simp]
/--
theorem `algEquivQuotient_symm_apply` / 定理 `algEquivQuotient_symm_apply`

English:
theorem algEquivQuotient_symm_apply
  given: [IsAdicComplete I A] (x : A⟦X⟧ ⧸ Ideal.span {g})
  proof: by
  simp [algEquivQuotient]

中文:
定理 algEquivQuotient_symm_apply
  条件: [是AdicComplete I A] (x : A⟦X⟧ ⧸ 理想.span {g})
  证明: by
  simp [algEquivQuotient]

Depends on / 依赖: algEquivQuotient
-/
theorem algEquivQuotient_symm_apply [IsAdicComplete I A] (x : A⟦X⟧ ⧸ Ideal.span {g}) :
    H.algEquivQuotient.symm x = Ideal.Quotient.mk _
      (H.isDistinguishedAt.isWeierstrassDivisorAt'.mod' <| Ideal.quotientEquivAlgOfEq A
        (by rw [H.eq_mul, Ideal.span_singleton_mul_right_unit H.isUnit]) x) := by
  simp [algEquivQuotient]

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: {g' : A⟦X⟧} {f' : A[X]} {h' : A⟦X⟧} (H' : g'.IsWeierstrassFactorizationAt f' h' I)
  proof: ⟨H.isDistinguishedAt.mul H'.isDistinguishedAt, H.isUnit.mul H'.isUnit, by
    rw [H.eq_mul]; rw [H'.eq_mul]; rw [Polynomial.coe_mul]; ring⟩

中文:
定理 mul
  条件: {g' : A⟦X⟧} {f' : A[X]} {h' : A⟦X⟧} (H' : g'.是WeierstrassFactorizationAt f' h' I)
  证明: ⟨H.isDistinguishedAt.mul H'.isDistinguishedAt, H.isUnit.mul H'.isUnit, by
    rw [H.eq_mul]; rw [H'.eq_mul]; rw [Polynomial.coe_mul]; ring⟩

Depends on / 依赖: H.eq_mul, H.isDistinguishedAt.mul, H.isUnit.mul, Polynomial, Polynomial.coe_mul, coe_mul, eq_mul, isDistinguishedAt, isUnit
-/
theorem mul {g' : A⟦X⟧} {f' : A[X]} {h' : A⟦X⟧} (H' : g'.IsWeierstrassFactorizationAt f' h' I) :
    (g * g').IsWeierstrassFactorizationAt (f * f') (h * h') I :=
  ⟨H.isDistinguishedAt.mul H'.isDistinguishedAt, H.isUnit.mul H'.isUnit, by
    rw [H.eq_mul]; rw [H'.eq_mul]; rw [Polynomial.coe_mul]; ring⟩

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: {a : A} (ha : IsUnit a)
  statement: (a • g).IsWeierstrassFactorizationAt f (a • h) I
  proof: by
  refine ⟨H.isDistinguishedAt, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (ha.map _).mul H.isUnit
  · simp [H.eq_mul]

中文:
定理 smul
  条件: {a : A} (ha : 是单位 a)
  结论: (a • g).是WeierstrassFactorizationAt f (a • h) I
  证明: by
  refine ⟨H.isDistinguishedAt, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (ha.map _).mul H.isUnit
  · simp [H.eq_mul]

Depends on / 依赖: Algebra, Algebra.smul_def, H.eq_mul, H.isDistinguishedAt, H.isUnit, eq_mul, ha.map, isDistinguishedAt, isUnit, smul_def
-/
theorem smul {a : A} (ha : IsUnit a) : (a • g).IsWeierstrassFactorizationAt f (a • h) I := by
  refine ⟨H.isDistinguishedAt, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (ha.map _).mul H.isUnit
  · simp [H.eq_mul]

end IsWeierstrassFactorizationAt

variable [IsLocalRing A]

namespace IsWeierstrassFactorization

variable {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorization f h)
include H

/--
theorem `map_ne_zero` / 定理 `map_ne_zero`

English:
theorem map_ne_zero
  statement: g.map (IsLocalRing.residue A) != 0
  proof: H.map_ne_zero_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

中文:
定理 map_ne_zero
  结论: g.map (是局部环.residue A) != 0
  证明: H.map_ne_zero_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

Depends on / 依赖: H.map_ne_zero_of_ne_top, Ideal.IsMaximal.ne_top, IsMaximal, map_ne_zero_of_ne_top, ne_top
-/
theorem map_ne_zero : g.map (IsLocalRing.residue A) != 0 :=
  H.map_ne_zero_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

/--
theorem `degree_eq_coe_lift_order_map` / 定理 `degree_eq_coe_lift_order_map`

English:
theorem degree_eq_coe_lift_order_map
  statement: f.degree = (g.map (IsLocalRing.residue A)).order.lift
  proof: H.degree_eq_coe_lift_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

中文:
定理 degree_eq_coe_lift_order_map
  结论: f.degree = (g.map (是局部环.residue A)).order.lift
  证明: H.degree_eq_coe_lift_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

Depends on / 依赖: H.degree_eq_coe_lift_order_map_of_ne_top, Ideal.IsMaximal.ne_top, IsMaximal, degree_eq_coe_lift_order_map_of_ne_top, ne_top
-/
theorem degree_eq_coe_lift_order_map : f.degree = (g.map (IsLocalRing.residue A)).order.lift
    (order_finite_iff_ne_zero.2 H.map_ne_zero) :=
  H.degree_eq_coe_lift_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

/--
theorem `natDegree_eq_toNat_order_map` / 定理 `natDegree_eq_toNat_order_map`

English:
theorem natDegree_eq_toNat_order_map
  proof: H.natDegree_eq_toNat_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

中文:
定理 natDegree_eq_to自然数_order_map
  证明: H.natDegree_eq_toNat_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

Depends on / 依赖: H.natDegree_eq_toNat_order_map_of_ne_top, Ideal.IsMaximal.ne_top, IsMaximal, natDegree_eq_toNat_order_map_of_ne_top, ne_top
-/
theorem natDegree_eq_toNat_order_map :
    f.natDegree = (g.map (IsLocalRing.residue A)).order.toNat :=
  H.natDegree_eq_toNat_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

end IsWeierstrassFactorization

/--
theorem `IsWeierstrassDivision.isUnit_of_map_ne_zero` / 定理 `IsWeierstrassDivision.isUnit_of_map_ne_zero`

English:
theorem IsWeierstrassDivision.isUnit_of_map_ne_zero
  proof: by
  obtain ⟨H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat, H2⟩ := H
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  replace H2 := congr(coeff n (($H2).map (IsLocalRing.residue A)))
  simp_rw [map_pow, map_X, coeff_X_pow_self, map_add, map_mul, coeff_map,
    Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_degree_lt H1, map_zero, add_zero] at H2
  rw [isUnit_iff_constantCoeff]; rw [← isUnit_map_iff (IsLocalRing.residue A)]
  rw [coeff_mul]; rw [← Finset.sum_subset (s₁ := {(n]; rw [0)}) (by simp) (fun p hp hnotMem => ?_)]; rw [Finset.sum_singleton]; rw [coeff_map]; rw [coeff_map]; rw [coeff_zero_eq_constantCoeff]; rw [mul_comm] at H2
  · exact .of_mul_eq_one _ H2.symm
  · rw [coeff_of_lt_order p.1 ?_]
    · rw [zero_mul]
    · rw [← ENat.lt_lift_iff (h := order_finite_iff_ne_zero.2 hg), ENat.lift_eq_toNat_of_lt_top]
      refine (Finset.HasAntidiagonal.antidiagonal.fst_le hp).lt_of_ne ?_
      contrapose hnotMem
      rwa [Finset.mem_singleton, Finset.HasAntidiagonal.antidiagonal_congr hp (by simp)]

中文:
定理 IsWeierstrassDivision.isUnit_of_map_ne_zero
  证明: by
  obtain ⟨H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat, H2⟩ := H
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  replace H2 := congr(coeff n (($H2).map (IsLocalRing.residue A)))
  simp_rw [map_pow, map_X, coeff_X_pow_self, map_add, map_mul, coeff_map,
    Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_degree_lt H1, map_zero, add_zero] at H2
  rw [isUnit_iff_constantCoeff]; rw [← isUnit_map_iff (IsLocalRing.residue A)]
  rw [coeff_mul]; rw [← Finset.sum_subset (s₁ := {(n]; rw [0)}) (by simp) (fun p hp hnotMem => ?_)]; rw [Finset.sum_singleton]; rw [coeff_map]; rw [coeff_map]; rw [coeff_zero_eq_constantCoeff]; rw [mul_comm] at H2
  · exact .of_mul_eq_one _ H2.symm
  · rw [coeff_of_lt_order p.1 ?_]
    · rw [zero_mul]
    · rw [← ENat.lt_lift_iff (h := order_finite_iff_ne_zero.2 hg), ENat.lift_eq_toNat_of_lt_top]
      refine (Finset.HasAntidiagonal.antidiagonal.fst_le hp).lt_of_ne ?_
      contrapose hnotMem
      rwa [Finset.mem_singleton, Finset.HasAntidiagonal.antidiagonal_congr hp (by simp)]

Depends on / 依赖: Finset, Finset.sum_subset, IsLocalRing, IsLocalRing.residue, Polynomial, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_degree_lt, add_zero, coeff_X_pow_self, coeff_coe, coeff_eq_zero_of_degree_lt, coeff_map, coeff_mul, degree, g.map, isUnit_iff_constantCoeff, isUnit_map_iff, map_X, map_add, map_mul
-/
theorem IsWeierstrassDivision.isUnit_of_map_ne_zero
    {g q : A⟦X⟧} {r : A[X]} (hg : g.map (IsLocalRing.residue A) != 0)
    (H : (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g q r) :
    IsUnit q := by
  obtain ⟨H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat, H2⟩ := H
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  replace H2 := congr(coeff n (($H2).map (IsLocalRing.residue A)))
  simp_rw [map_pow, map_X, coeff_X_pow_self, map_add, map_mul, coeff_map,
    Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_degree_lt H1, map_zero, add_zero] at H2
  rw [isUnit_iff_constantCoeff]; rw [← isUnit_map_iff (IsLocalRing.residue A)]
  rw [coeff_mul]; rw [← Finset.sum_subset (s₁ := {(n]; rw [0)}) (by simp) (fun p hp hnotMem => ?_)]; rw [Finset.sum_singleton]; rw [coeff_map]; rw [coeff_map]; rw [coeff_zero_eq_constantCoeff]; rw [mul_comm] at H2
  · exact .of_mul_eq_one _ H2.symm
  · rw [coeff_of_lt_order p.1 ?_]
    · rw [zero_mul]
    · rw [← ENat.lt_lift_iff (h := order_finite_iff_ne_zero.2 hg), ENat.lift_eq_toNat_of_lt_top]
      refine (Finset.HasAntidiagonal.antidiagonal.fst_le hp).lt_of_ne ?_
      contrapose hnotMem
      rwa [Finset.mem_singleton, Finset.HasAntidiagonal.antidiagonal_congr hp (by simp)]

/--
theorem `IsWeierstrassDivision.isWeierstrassFactorization` / 定理 `IsWeierstrassDivision.isWeierstrassFactorization`

English:
theorem IsWeierstrassDivision.isWeierstrassFactorization
  proof: by
  have H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat := H.1
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  set f := Polynomial.X ^ n - r
  replace H1 : r.degree < (Polynomial.X (R := A) ^ n).degree := by rwa [Polynomial.degree_X_pow]
  have hfdeg : f.natDegree = n := by
    suffices f.degree = n by rw [Polynomial.natDegree, this]; rfl
    rw [Polynomial.degree_sub_eq_left_of_degree_lt H1]; rw [Polynomial.degree_X_pow]
  refine ⟨⟨⟨fun {i} hi => ?_⟩, .sub_of_left (Polynomial.monic_X_pow _) H1⟩, Units.isUnit _, ?_⟩
  · rw [hfdeg] at hi
    simp_rw [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff]
    have := H.coeff_f_sub_r_mem hi
    rwa [map_sub, coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff, Polynomial.coeff_coe] at this
  · have := congr($(H.2) * ↑(H.isUnit_of_map_ne_zero hg).unit⁻¹)
    rw [add_mul]; rw [mul_assoc]; rw [IsUnit.mul_val_inv]; rw [mul_one]; rw [← sub_eq_iff_eq_add] at this
    simp_rw [← this, f, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, sub_mul]

中文:
定理 IsWeierstrassDivision.isWeierstrassFactorization
  证明: by
  have H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat := H.1
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  set f := Polynomial.X ^ n - r
  replace H1 : r.degree < (Polynomial.X (R := A) ^ n).degree := by rwa [Polynomial.degree_X_pow]
  have hfdeg : f.natDegree = n := by
    suffices f.degree = n by rw [Polynomial.natDegree, this]; rfl
    rw [Polynomial.degree_sub_eq_left_of_degree_lt H1]; rw [Polynomial.degree_X_pow]
  refine ⟨⟨⟨fun {i} hi => ?_⟩, .sub_of_left (Polynomial.monic_X_pow _) H1⟩, Units.isUnit _, ?_⟩
  · rw [hfdeg] at hi
    simp_rw [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff]
    have := H.coeff_f_sub_r_mem hi
    rwa [map_sub, coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff, Polynomial.coeff_coe] at this
  · have := congr($(H.2) * ↑(H.isUnit_of_map_ne_zero hg).unit⁻¹)
    rw [add_mul]; rw [mul_assoc]; rw [IsUnit.mul_val_inv]; rw [mul_one]; rw [← sub_eq_iff_eq_add] at this
    simp_rw [← this, f, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, sub_mul]

Depends on / 依赖: IsLocalRing, IsLocalRing.residue, Polynomial, Polynomial.X, Polynomial.degree_X_pow, Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.monic_X_pow, Polynomial.natDegree, degree, degree_X_pow, degree_sub_eq_left_of_degree_lt, f.degree, f.natDegree, g.map, monic_X_pow, natDegree, order.toNat, r.degree, replace, residue
-/
theorem IsWeierstrassDivision.isWeierstrassFactorization
    {g q : A⟦X⟧} {r : A[X]} (hg : g.map (IsLocalRing.residue A) != 0)
    (H : (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g q r) :
    g.IsWeierstrassFactorization
      (Polynomial.X ^ (g.map (IsLocalRing.residue A)).order.toNat - r)
      ↑(H.isUnit_of_map_ne_zero hg).unit⁻¹ := by
  have H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat := H.1
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  set f := Polynomial.X ^ n - r
  replace H1 : r.degree < (Polynomial.X (R := A) ^ n).degree := by rwa [Polynomial.degree_X_pow]
  have hfdeg : f.natDegree = n := by
    suffices f.degree = n by rw [Polynomial.natDegree, this]; rfl
    rw [Polynomial.degree_sub_eq_left_of_degree_lt H1]; rw [Polynomial.degree_X_pow]
  refine ⟨⟨⟨fun {i} hi => ?_⟩, .sub_of_left (Polynomial.monic_X_pow _) H1⟩, Units.isUnit _, ?_⟩
  · rw [hfdeg] at hi
    simp_rw [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff]
    have := H.coeff_f_sub_r_mem hi
    rwa [map_sub, coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff, Polynomial.coeff_coe] at this
  · have := congr($(H.2) * ↑(H.isUnit_of_map_ne_zero hg).unit⁻¹)
    rw [add_mul]; rw [mul_assoc]; rw [IsUnit.mul_val_inv]; rw [mul_one]; rw [← sub_eq_iff_eq_add] at this
    simp_rw [← this, f, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, sub_mul]

/--
theorem `IsWeierstrassFactorization.isWeierstrassDivision` / 定理 `IsWeierstrassFactorization.isWeierstrassDivision`

English:
theorem IsWeierstrassFactorization.isWeierstrassDivision
  proof: by
  set n := (g.map (IsLocalRing.residue A)).order.toNat with hn
  constructor
  · refine (Polynomial.degree_sub_lt_left ?_ (Polynomial.monic_X_pow n).ne_zero ?_).trans_eq
      (by simpa)
    · simp_rw [H.degree_eq_coe_lift_order_map, Polynomial.degree_X_pow, n,
        ENat.lift_eq_toNat_of_lt_top]
    · rw [(Polynomial.monic_X_pow n).leadingCoeff, H.isDistinguishedAt.monic.leadingCoeff]
  · simp_rw [H.eq_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, Polynomial.coe_sub,
      Polynomial.coe_pow, Polynomial.coe_X, add_sub_cancel]

中文:
定理 IsWeierstrassFactorization.isWeierstrassDivision
  证明: by
  set n := (g.map (IsLocalRing.residue A)).order.toNat with hn
  constructor
  · refine (Polynomial.degree_sub_lt_left ?_ (Polynomial.monic_X_pow n).ne_zero ?_).trans_eq
      (by simpa)
    · simp_rw [H.degree_eq_coe_lift_order_map, Polynomial.degree_X_pow, n,
        ENat.lift_eq_toNat_of_lt_top]
    · rw [(Polynomial.monic_X_pow n).leadingCoeff, H.isDistinguishedAt.monic.leadingCoeff]
  · simp_rw [H.eq_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, Polynomial.coe_sub,
      Polynomial.coe_pow, Polynomial.coe_X, add_sub_cancel]

Depends on / 依赖: ENat.lift_eq_toNat_of_lt_top, H.degree_eq_coe_lift_order_map, H.eq_mul, H.isDistinguishedAt.monic.leadingCoeff, IsLocalRing, IsLocalRing.residue, IsUnit, IsUnit.mul_val_inv, Polynomial, Polynomial.coe_X, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.degree_X_pow, Polynomial.degree_sub_lt_left, Polynomial.monic_X_pow, add_sub_cancel, coe_X, coe_pow, coe_sub, degree_X_pow
-/
theorem IsWeierstrassFactorization.isWeierstrassDivision
    {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorization f h) :
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g ↑H.isUnit.unit⁻¹
      (Polynomial.X ^ (g.map (IsLocalRing.residue A)).order.toNat - f) := by
  set n := (g.map (IsLocalRing.residue A)).order.toNat with hn
  constructor
  · refine (Polynomial.degree_sub_lt_left ?_ (Polynomial.monic_X_pow n).ne_zero ?_).trans_eq
      (by simpa)
    · simp_rw [H.degree_eq_coe_lift_order_map, Polynomial.degree_X_pow, n,
        ENat.lift_eq_toNat_of_lt_top]
    · rw [(Polynomial.monic_X_pow n).leadingCoeff, H.isDistinguishedAt.monic.leadingCoeff]
  · simp_rw [H.eq_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, Polynomial.coe_sub,
      Polynomial.coe_pow, Polynomial.coe_X, add_sub_cancel]

/--
theorem `IsWeierstrassFactorization.elim` / 定理 `IsWeierstrassFactorization.elim`

English:
theorem IsWeierstrassFactorization.elim
  statement: [IsHausdorff (IsLocalRing.maximalIdeal A) A]
  proof: by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivision.elim H.map_ne_zero H2.isWeierstrassDivision
  rw [← Units.ext_iff]; rw [inv_inj]; rw [Units.ext_iff] at h1
  exact ⟨by simpa using h2, h1⟩

中文:
定理 IsWeierstrassFactorization.elim
  结论: [是豪斯多夫 (是局部环.maximalIdeal A) A]
  证明: by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivision.elim H.map_ne_zero H2.isWeierstrassDivision
  rw [← Units.ext_iff]; rw [inv_inj]; rw [Units.ext_iff] at h1
  exact ⟨by simpa using h2, h1⟩

Depends on / 依赖: H.isWeierstrassDivision.elim, H.map_ne_zero, H2.isWeierstrassDivision, Units.ext_iff, ext_iff, inv_inj, isWeierstrassDivision, map_ne_zero
-/
theorem IsWeierstrassFactorization.elim [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} {f f' : A[X]} {h h' : A⟦X⟧} (H : g.IsWeierstrassFactorization f h)
    (H2 : g.IsWeierstrassFactorization f' h') : f = f' ∧ h = h' := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivision.elim H.map_ne_zero H2.isWeierstrassDivision
  rw [← Units.ext_iff]; rw [inv_inj]; rw [Units.ext_iff] at h1
  exact ⟨by simpa using h2, h1⟩

section IsAdicComplete

variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {a : A} {g g' : A⟦X⟧} {f : A[X]} {h : A⟦X⟧}

/--
theorem `exists_isWeierstrassFactorization` / 定理 `exists_isWeierstrassFactorization`

English:
theorem exists_isWeierstrassFactorization
  given: (hg : g.map (IsLocalRing.residue A) != 0)
  proof: by
  obtain ⟨q, r, H⟩ :=
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).exists_isWeierstrassDivision hg
  exact ⟨_, _, H.isWeierstrassFactorization hg⟩

中文:
定理 存在_isWeierstrassFactorization
  条件: (hg : g.map (是局部环.residue A) != 0)
  证明: by
  obtain ⟨q, r, H⟩ :=
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).exists_isWeierstrassDivision hg
  exact ⟨_, _, H.isWeierstrassFactorization hg⟩

Depends on / 依赖: H.isWeierstrassFactorization, IsLocalRing, IsLocalRing.residue, exists_isWeierstrassDivision, g.map, isWeierstrassFactorization, order.toNat, residue
-/
theorem exists_isWeierstrassFactorization (hg : g.map (IsLocalRing.residue A) != 0) :
    exists f h, g.IsWeierstrassFactorization f h := by
  obtain ⟨q, r, H⟩ :=
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).exists_isWeierstrassDivision hg
  exact ⟨_, _, H.isWeierstrassFactorization hg⟩

variable (g) in
/--
Definition of `weierstrassDistinguished` / `weierstrassDistinguished` 的定义

English:
definition weierstrassDistinguished
  signature: (hg : g.map (IsLocalRing.residue A) != 0)
  body: (g.exists_isWeierstrassFactorization hg).choose

中文:
定义 weierstrassDistinguished
  签名: (hg : g.map (是局部环.residue A) != 0)
  定义体: (g.exists_isWeierstrassFactorization hg).choose

Depends on / 依赖: exists_isWeierstrassFactorization, g.exists_isWeierstrassFactorization
-/
noncomputable def weierstrassDistinguished (hg : g.map (IsLocalRing.residue A) != 0) : A[X] :=
  (g.exists_isWeierstrassFactorization hg).choose

variable (g) in
/--
Definition of `weierstrassUnit` / `weierstrassUnit` 的定义

English:
definition weierstrassUnit
  signature: (hg : g.map (IsLocalRing.residue A) != 0)
  body: (g.exists_isWeierstrassFactorization hg).choose_spec.choose

中文:
定义 weierstrassUnit
  签名: (hg : g.map (是局部环.residue A) != 0)
  定义体: (g.exists_isWeierstrassFactorization hg).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, exists_isWeierstrassFactorization, g.exists_isWeierstrassFactorization
-/
noncomputable def weierstrassUnit (hg : g.map (IsLocalRing.residue A) != 0) : A⟦X⟧ :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose

/--
theorem `isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit` / 定理 `isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit`

English:
theorem isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
  proof: (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec

中文:
定理 isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
  证明: (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec

Depends on / 依赖: choose_spec, choose_spec.choose_spec, exists_isWeierstrassFactorization, g.exists_isWeierstrassFactorization
-/
theorem isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (hg : g.map (IsLocalRing.residue A) != 0) :
    g.IsWeierstrassFactorization (g.weierstrassDistinguished hg) (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec

/--
Definition of `algEquivQuotientWeierstrassDistinguished` / `algEquivQuotientWeierstrassDistinguished` 的定义

English:
abbreviation algEquivQuotientWeierstrassDistinguished
  body: (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg).algEquivQuotient

中文:
缩写 algEquivQuotientWeierstrassDistinguished
  定义体: (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg).algEquivQuotient

Depends on / 依赖: algEquivQuotient, g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit, isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
-/
noncomputable abbrev algEquivQuotientWeierstrassDistinguished
    (hg : g.map (IsLocalRing.residue A) != 0) :=
  (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg).algEquivQuotient

/--
theorem `isDistinguishedAt_weierstrassDistinguished` / 定理 `isDistinguishedAt_weierstrassDistinguished`

English:
theorem isDistinguishedAt_weierstrassDistinguished
  given: (hg : g.map (IsLocalRing.residue A) != 0)
  proof: (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isDistinguishedAt

中文:
定理 isDistinguishedAt_weierstrassDistinguished
  条件: (hg : g.map (是局部环.residue A) != 0)
  证明: (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isDistinguishedAt

Depends on / 依赖: choose_spec, choose_spec.choose_spec.isDistinguishedAt, exists_isWeierstrassFactorization, g.exists_isWeierstrassFactorization, isDistinguishedAt
-/
theorem isDistinguishedAt_weierstrassDistinguished (hg : g.map (IsLocalRing.residue A) != 0) :
    (g.weierstrassDistinguished hg).IsDistinguishedAt (IsLocalRing.maximalIdeal A) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isDistinguishedAt

/--
theorem `isUnit_weierstrassUnit` / 定理 `isUnit_weierstrassUnit`

English:
theorem isUnit_weierstrassUnit
  given: (hg : g.map (IsLocalRing.residue A) != 0)
  proof: (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isUnit

中文:
定理 isUnit_weierstrassUnit
  条件: (hg : g.map (是局部环.residue A) != 0)
  证明: (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isUnit

Depends on / 依赖: choose_spec, choose_spec.choose_spec.isUnit, exists_isWeierstrassFactorization, g.exists_isWeierstrassFactorization, isUnit
-/
theorem isUnit_weierstrassUnit (hg : g.map (IsLocalRing.residue A) != 0) :
    IsUnit (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isUnit

/--
theorem `eq_weierstrassDistinguished_mul_weierstrassUnit` / 定理 `eq_weierstrassDistinguished_mul_weierstrassUnit`

English:
theorem eq_weierstrassDistinguished_mul_weierstrassUnit
  given: (hg : g.map (IsLocalRing.residue A) != 0)
  proof: (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.eq_mul

中文:
定理 eq_weierstrassDistinguished_mul_weierstrassUnit
  条件: (hg : g.map (是局部环.residue A) != 0)
  证明: (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.eq_mul

Depends on / 依赖: choose_spec, choose_spec.choose_spec.eq_mul, eq_mul, exists_isWeierstrassFactorization, g.exists_isWeierstrassFactorization
-/
theorem eq_weierstrassDistinguished_mul_weierstrassUnit (hg : g.map (IsLocalRing.residue A) != 0) :
    g = g.weierstrassDistinguished hg * g.weierstrassUnit hg :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.eq_mul

/--
theorem `IsWeierstrassFactorization.unique` / 定理 `IsWeierstrassFactorization.unique`

English:
theorem IsWeierstrassFactorization.unique
  proof: H.elim (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg)

@[simp]

中文:
定理 IsWeierstrassFactorization.unique
  证明: H.elim (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg)

@[simp]

Depends on / 依赖: H.elim, g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit, isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
-/
theorem IsWeierstrassFactorization.unique
    (H : g.IsWeierstrassFactorization f h) (hg : g.map (IsLocalRing.residue A) != 0) :
    f = g.weierstrassDistinguished hg ∧ h = g.weierstrassUnit hg :=
  H.elim (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg)

@[simp]
/--
theorem `weierstrassDistinguished_mul` / 定理 `weierstrassDistinguished_mul`

English:
theorem weierstrassDistinguished_mul
  given: (hg : (g * g').map (IsLocalRing.residue A) != 0)
  proof: by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).1

@[simp]

中文:
定理 weierstrassDistinguished_mul
  条件: (hg : (g * g').map (是局部环.residue A) != 0)
  证明: by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).1

@[simp]

Depends on / 依赖: H.mul, g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit, isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
-/
theorem weierstrassDistinguished_mul (hg : (g * g').map (IsLocalRing.residue A) != 0) :
    (g * g').weierstrassDistinguished hg =
      g.weierstrassDistinguished (fun h => hg (by simp [h])) *
        g'.weierstrassDistinguished (fun h => hg (by simp [h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).1

@[simp]
/--
theorem `weierstrassUnit_mul` / 定理 `weierstrassUnit_mul`

English:
theorem weierstrassUnit_mul
  given: (hg : (g * g').map (IsLocalRing.residue A) != 0)
  proof: by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).2

@[simp]

中文:
定理 weierstrassUnit_mul
  条件: (hg : (g * g').map (是局部环.residue A) != 0)
  证明: by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).2

@[simp]

Depends on / 依赖: H.mul, g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit, isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
-/
theorem weierstrassUnit_mul (hg : (g * g').map (IsLocalRing.residue A) != 0) :
    (g * g').weierstrassUnit hg =
      g.weierstrassUnit (fun h => hg (by simp [h])) *
        g'.weierstrassUnit (fun h => hg (by simp [h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).2

@[simp]
/--
theorem `weierstrassDistinguished_smul` / 定理 `weierstrassDistinguished_smul`

English:
theorem weierstrassDistinguished_smul
  given: (hg : (a • g).map (IsLocalRing.residue A) != 0)
  proof: by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a != 0 := fun h => hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).1

@[simp]

中文:
定理 weierstrassDistinguished_smul
  条件: (hg : (a • g).map (是局部环.residue A) != 0)
  证明: by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a != 0 := fun h => hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).1

@[simp]

Depends on / 依赖: Algebra, Algebra.smul_def, H.smul, IsLocalRing, IsLocalRing.residue, g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit, isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit, residue, smul_def
-/
theorem weierstrassDistinguished_smul (hg : (a • g).map (IsLocalRing.residue A) != 0) :
    (a • g).weierstrassDistinguished hg =
      g.weierstrassDistinguished (fun h => hg (by simp [Algebra.smul_def, h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a != 0 := fun h => hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).1

@[simp]
/--
theorem `weierstrassUnit_smul` / 定理 `weierstrassUnit_smul`

English:
theorem weierstrassUnit_smul
  given: (hg : (a • g).map (IsLocalRing.residue A) != 0)
  proof: by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a != 0 := fun h => hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).2

中文:
定理 weierstrassUnit_smul
  条件: (hg : (a • g).map (是局部环.residue A) != 0)
  证明: by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a != 0 := fun h => hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).2

Depends on / 依赖: Algebra, Algebra.smul_def, H.smul, IsLocalRing, IsLocalRing.residue, g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit, isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit, residue, smul_def
-/
theorem weierstrassUnit_smul (hg : (a • g).map (IsLocalRing.residue A) != 0) :
    (a • g).weierstrassUnit hg =
      a • g.weierstrassUnit (fun h => hg (by simp [Algebra.smul_def, h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h => hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a != 0 := fun h => hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).2

end IsAdicComplete

end PowerSeries
