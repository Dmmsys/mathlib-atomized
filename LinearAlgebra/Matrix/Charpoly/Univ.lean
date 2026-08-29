/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The universal characteristic polynomial

In this file we define the universal characteristic polynomial `Matrix.charpoly.univ`,
which is the characteristic polynomial of the matrix with entries `Xᵢⱼ`,
and hence has coefficients that are multivariate polynomials.

It is universal in the sense that one obtains the characteristic polynomial of a matrix `M`
by evaluating the coefficients of `univ` at the entries of `M`.

We use it to show that the coefficients of the characteristic polynomial
of a matrix are homogeneous polynomials in the matrix entries.

## Main results

* `Matrix.charpoly.univ`: the universal characteristic polynomial
* `Matrix.charpoly.univ_map_eval₂Hom`: evaluating `univ` on the entries of a matrix `M`
  gives the characteristic polynomial of `M`.
* `Matrix.charpoly.univ_coeff_isHomogeneous`:
  the `i`-th coefficient of `univ` is a homogeneous polynomial of degree `n - i`.
-/

public section

namespace Matrix.charpoly

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
variable (f : R ->+* S)

variable (R) in
/-- The universal characteristic polynomial for `n × n`-matrices,
is the characteristic polynomial of `Matrix.mvPolynomialX n n ℤ` with entries `Xᵢⱼ`.

Its `i`-th coefficient is a homogeneous polynomial of degree `n - i`,
see `Matrix.charpoly.univ_coeff_isHomogeneous`.

By evaluating the coefficients at the entries of a matrix `M`,
one obtains the characteristic polynomial of `M`,
see `Matrix.charpoly.univ_map_eval₂Hom`. -/
noncomputable
/--
Definition of `univ` / `univ` 的定义

English:
abbreviation univ
  signature: : Polynomial (MvPolynomial (n × n) R)
  body: charpoly mvPolynomialX n n R

中文:
缩写 univ
  签名: : 多项式 (多元多项式 (n × n) R)
  定义体: charpoly mvPolynomialX n n R

Depends on / 依赖: charpoly, mvPolynomialX
-/
abbrev univ : Polynomial (MvPolynomial (n × n) R) :=
charpoly mvPolynomialX n n R

open MvPolynomial RingHomClass in
@[simp]
/--
lemma `univ_map_eval₂Hom` / 引理 `univ_map_eval₂Hom`

English:
lemma univ_map_eval₂Hom
  given: (M : n × n -> S)
  proof: by
  rw [univ]; rw [← charpoly_map]; rw [coe_eval₂Hom]; rw [← mvPolynomialX_map_eval₂ f (Matrix.of M.curry)]
  simp only [of_apply, Function.curry_apply, Prod.mk.eta]

中文:
引理 univ_map_eval₂Hom
  条件: (M : n × n -> S)
  证明: by
  rw [univ]; rw [← charpoly_map]; rw [coe_eval₂Hom]; rw [← mvPolynomialX_map_eval₂ f (Matrix.of M.curry)]
  simp only [of_apply, Function.curry_apply, Prod.mk.eta]

Depends on / 依赖: Function, Function.curry_apply, M.curry, Matrix, Matrix.of, Prod.mk.eta, charpoly_map, curry_apply, of_apply
-/
lemma univ_map_eval₂Hom (M : n × n -> S) :
    (univ R n).map (eval₂Hom f M) = charpoly (Matrix.of M.curry) := by
  rw [univ]; rw [← charpoly_map]; rw [coe_eval₂Hom]; rw [← mvPolynomialX_map_eval₂ f (Matrix.of M.curry)]
  simp only [of_apply, Function.curry_apply, Prod.mk.eta]

/--
lemma `univ_map_map` / 引理 `univ_map_map`

English:
lemma univ_map_map
  proof: by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]; rw [univ_map_eval₂Hom]; rfl

@[simp]

中文:
引理 univ_map_map
  证明: by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]; rw [univ_map_eval₂Hom]; rfl

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.map_eq_eval
-/
lemma univ_map_map :
    (univ R n).map (MvPolynomial.map f) = univ S n := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]; rw [univ_map_eval₂Hom]; rfl

@[simp]
/--
lemma `univ_coeff_eval₂Hom` / 引理 `univ_coeff_eval₂Hom`

English:
lemma univ_coeff_eval₂Hom
  given: (M : n × n -> S) (i : Nat)
  proof: by
  rw [← univ_map_eval₂Hom n f M]; rw [Polynomial.coeff_map]

中文:
引理 univ_coeff_eval₂Hom
  条件: (M : n × n -> S) (i : 自然数)
  证明: by
  rw [← univ_map_eval₂Hom n f M]; rw [Polynomial.coeff_map]

Depends on / 依赖: Polynomial, Polynomial.coeff_map, coeff_map
-/
lemma univ_coeff_eval₂Hom (M : n × n -> S) (i : Nat) :
    MvPolynomial.eval₂Hom f M ((univ R n).coeff i) =
      (charpoly (Matrix.of M.curry)).coeff i := by
  rw [← univ_map_eval₂Hom n f M]; rw [Polynomial.coeff_map]

variable (R)

/--
lemma `univ_monic` / 引理 `univ_monic`

English:
lemma univ_monic
  statement: (univ R n).Monic
  proof: charpoly_monic (mvPolynomialX n n R)

中文:
引理 univ_monic
  结论: (univ R n).Monic
  证明: charpoly_monic (mvPolynomialX n n R)

Depends on / 依赖: charpoly_monic, mvPolynomialX
-/
lemma univ_monic : (univ R n).Monic := charpoly_monic (mvPolynomialX n n R)

/--
lemma `univ_natDegree` / 引理 `univ_natDegree`

English:
lemma univ_natDegree
  given: [Nontrivial R]
  statement: (univ R n).natDegree = Fintype.card n
  proof: charpoly_natDegree_eq_dim (mvPolynomialX n n R)

@[simp]

中文:
引理 univ_natDegree
  条件: [非平凡 R]
  结论: (univ R n).natDegree = 有限类型.card n
  证明: charpoly_natDegree_eq_dim (mvPolynomialX n n R)

@[simp]

Depends on / 依赖: charpoly_natDegree_eq_dim, mvPolynomialX
-/
lemma univ_natDegree [Nontrivial R] : (univ R n).natDegree = Fintype.card n :=
  charpoly_natDegree_eq_dim (mvPolynomialX n n R)

@[simp]
/--
lemma `univ_coeff_card` / 引理 `univ_coeff_card`

English:
lemma univ_coeff_card
  statement: (univ R n).coeff (Fintype.card n) = 1
  proof: by
  suffices Polynomial.coeff (univ Int n) (Fintype.card n) = 1 by
    rw [← univ_map_map n (Int.castRingHom R)]; rw [Polynomial.coeff_map]; rw [this]; rw [map_one]
  rw [← univ_natDegree Int n]
  exact (univ_monic Int n).leadingCoeff

中文:
引理 univ_coeff_card
  结论: (univ R n).coeff (有限类型.card n) = 1
  证明: by
  suffices Polynomial.coeff (univ Int n) (Fintype.card n) = 1 by
    rw [← univ_map_map n (Int.castRingHom R)]; rw [Polynomial.coeff_map]; rw [this]; rw [map_one]
  rw [← univ_natDegree Int n]
  exact (univ_monic Int n).leadingCoeff

Depends on / 依赖: Fintype, Fintype.card, Int.castRingHom, Polynomial, Polynomial.coeff, Polynomial.coeff_map, castRingHom, coeff_map, leadingCoeff, map_one, univ_map_map, univ_monic, univ_natDegree
-/
lemma univ_coeff_card : (univ R n).coeff (Fintype.card n) = 1 := by
  suffices Polynomial.coeff (univ Int n) (Fintype.card n) = 1 by
    rw [← univ_map_map n (Int.castRingHom R)]; rw [Polynomial.coeff_map]; rw [this]; rw [map_one]
  rw [← univ_natDegree Int n]
  exact (univ_monic Int n).leadingCoeff

open MvPolynomial in
/--
lemma `optionEquivLeft_symm_univ_isHomogeneous` / 引理 `optionEquivLeft_symm_univ_isHomogeneous`

English:
lemma optionEquivLeft_symm_univ_isHomogeneous
  proof: by
  have aux : Fintype.card n = 0 + ∑ i : n, 1 := by
    simp only [zero_add, Finset.sum_const, smul_eq_mul, mul_one, Fintype.card]
  simp only [aux, univ, charpoly, charmatrix, scalar_apply, RingHom.mapMatrix_apply, det_apply',
    sub_apply, map_apply, of_apply, map_sum, map_mul, map_intCast, map

中文:
引理 optionEquivLeft_symm_univ_isHomogeneous
  证明: by
  have aux : Fintype.card n = 0 + ∑ i : n, 1 := by
    simp only [zero_add, Finset.sum_const, smul_eq_mul, mul_one, Fintype.card]
  simp only [aux, univ, charpoly, charmatrix, scalar_apply, RingHom.mapMatrix_apply, det_apply',
    sub_apply, map_apply, of_apply, map_sum, map_mul, map_intCast, map

Depends on / 依赖: Finset, Finset.sum_const, Fintype, Fintype.card, IsHomogeneous, IsHomogeneous.mul, IsHomogeneous.pro, IsHomogeneous.sum, Polynomial, Polynomial.aevalTower_C, RingHom, RingHom.mapMatrix_apply, aevalTower_C, charmatrix, charpoly, det_apply, diagonal, isHomogeneous_C, mapMatrix_apply, map_apply
-/
lemma optionEquivLeft_symm_univ_isHomogeneous :
    ((optionEquivLeft R (n × n)).symm (univ R n)).IsHomogeneous (Fintype.card n) := by
  have aux : Fintype.card n = 0 + ∑ i : n, 1 := by
    simp only [zero_add, Finset.sum_const, smul_eq_mul, mul_one, Fintype.card]
  simp only [aux, univ, charpoly, charmatrix, scalar_apply, RingHom.mapMatrix_apply, det_apply',
    sub_apply, map_apply, of_apply, map_sum, map_mul, map_intCast, map_prod, map_sub,
    optionEquivLeft_symm_apply, Polynomial.aevalTower_C, rename_X, diagonal, mvPolynomialX]
  apply IsHomogeneous.sum
  rintro i -
  apply IsHomogeneous.mul
  · apply isHomogeneous_C
  · apply IsHomogeneous.prod
    rintro j -
    by_cases h : i j = j
    · simp only [h, ↓reduceIte, Polynomial.aevalTower_X, IsHomogeneous.sub, isHomogeneous_X]
    · simp only [h, ↓reduceIte, map_zero, zero_sub, (isHomogeneous_X _ _).neg]

/--
lemma `univ_coeff_isHomogeneous` / 引理 `univ_coeff_isHomogeneous`

English:
lemma univ_coeff_isHomogeneous
  given: (i j : Nat) (h : i + j = Fintype.card n)
  proof: (optionEquivLeft_symm_univ_isHomogeneous R n).coeff_isHomogeneous_of_optionEquivLeft_symm _ _ h

中文:
引理 univ_coeff_isHomogeneous
  条件: (i j : 自然数) (h : i + j = 有限类型.card n)
  证明: (optionEquivLeft_symm_univ_isHomogeneous R n).coeff_isHomogeneous_of_optionEquivLeft_symm _ _ h

Depends on / 依赖: coeff_isHomogeneous_of_optionEquivLeft_symm, optionEquivLeft_symm_univ_isHomogeneous
-/
lemma univ_coeff_isHomogeneous (i j : Nat) (h : i + j = Fintype.card n) :
    ((univ R n).coeff i).IsHomogeneous j :=
  (optionEquivLeft_symm_univ_isHomogeneous R n).coeff_isHomogeneous_of_optionEquivLeft_symm _ _ h

end Matrix.charpoly
