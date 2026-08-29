/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Vieta's Formula

The main result is `Multiset.prod_X_add_C_eq_sum_esymm`, which shows that the product of
linear terms `X + λ` with `λ` in a `Multiset s` is equal to a linear combination of the
symmetric functions `esymm s`.

From this, we deduce `MvPolynomial.prod_X_add_C_eq_sum_esymm` which is the equivalent formula
for the product of linear terms `X + X i` with `i` in a `Fintype σ` as a linear combination
of the symmetric polynomials `esymm σ R j`.

For `R` be an integral domain (so that `p.roots` is defined for any `p : R[X]` as a multiset),
we derive `Polynomial.coeff_eq_esymm_roots_of_card`, the relationship between the coefficients and
the roots of `p` for a polynomial `p` that splits (i.e. having as many roots as its degree).
-/

public section

open Finset Polynomial

namespace Multiset

section Semiring

variable {R : Type*} [CommSemiring R]

/--
theorem `prod_X_add_C_eq_sum_esymm` / 定理 `prod_X_add_C_eq_sum_esymm`

English:
theorem prod_X_add_C_eq_sum_esymm
  given: (s : Multiset R)
  proof: by
  classical
    rw [prod_map_add]; rw [antidiagonal_eq_map_powerset]; rw [map_map]; rw [← bind_powerset_len]; rw [map_bind]; rw [sum_bind]; rw [Finset.sum_eq_multiset_sum]; rw [Finset.range_val]; rw [map_congr (Eq.refl _)]
    intro _ _
    rw [esymm]; rw [← sum_hom']; rw [← sum_map_mul_right]; r

中文:
定理 prod_X_add_C_eq_sum_esymm
  条件: (s : Multiset R)
  证明: by
  classical
    rw [prod_map_add]; rw [antidiagonal_eq_map_powerset]; rw [map_map]; rw [← bind_powerset_len]; rw [map_bind]; rw [sum_bind]; rw [Finset.sum_eq_multiset_sum]; rw [Finset.range_val]; rw [map_congr (Eq.refl _)]
    intro _ _
    rw [esymm]; rw [← sum_hom']; rw [← sum_map_mul_right]; r

Depends on / 依赖: Eq.refl, Finset, Finset.range_val, Finset.sum_eq_multiset_sum, Polynomial, Polynomial.C, antidiagonal_eq_map_powerset, bind_powerset_len, card_sub, classical, map_bind, map_congr, map_id, map_map, mem_powersetCard, prod_hom, prod_map_add, prod_replicate, range_val, sum_bind
-/
theorem prod_X_add_C_eq_sum_esymm (s : Multiset R) :
    (s.map fun r => X + C r).prod =
      ∑ j in Finset.range (Multiset.card s + 1), (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  classical
    rw [prod_map_add]; rw [antidiagonal_eq_map_powerset]; rw [map_map]; rw [← bind_powerset_len]; rw [map_bind]; rw [sum_bind]; rw [Finset.sum_eq_multiset_sum]; rw [Finset.range_val]; rw [map_congr (Eq.refl _)]
    intro _ _
    rw [esymm]; rw [← sum_hom']; rw [← sum_map_mul_right]; rw [map_congr (Eq.refl _)]
    intro s ht
    rw [mem_powersetCard] at ht
    dsimp
    rw [prod_hom' s (Polynomial.C : R ->+* R[X])]
    simp [ht, prod_replicate, map_id', card_sub]

/--
theorem `prod_X_add_C_coeff` / 定理 `prod_X_add_C_coeff`

English:
theorem prod_X_add_C_coeff
  given: (s : Multiset R) {k : Nat} (h : k <= Multiset.card s)
  proof: by
  convert! Polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k using 1
  simp_rw [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem (Multiset.card s - k) _] <;> grind

中文:
定理 prod_X_add_C_coeff
  条件: (s : Multiset R) {k : 自然数} (h : k <= Multiset.card s)
  证明: by
  convert! Polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k using 1
  simp_rw [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem (Multiset.card s - k) _] <;> grind

Depends on / 依赖: Finset, Finset.sum_eq_single_of_mem, Multiset, Multiset.card, Polynomial, Polynomial.ext_iff.mp, coeff_C_mul_X_pow, convert, ext_iff, finsetSum_coeff, prod_X_add_C_eq_sum_esymm, simp_rw, sum_eq_single_of_mem
-/
theorem prod_X_add_C_coeff (s : Multiset R) {k : Nat} (h : k <= Multiset.card s) :
    (s.map fun r => X + C r).prod.coeff k = s.esymm (Multiset.card s - k) := by
  convert! Polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k using 1
  simp_rw [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem (Multiset.card s - k) _] <;> grind

/--
theorem `prod_X_add_C_coeff'` / 定理 `prod_X_add_C_coeff'`

English:
theorem prod_X_add_C_coeff'
  given: {σ} (s : Multiset σ) (r : σ -> R) {k : Nat} (h : k <= Multiset.card s)
  proof: by
  rw [← Function.comp_def (f := fun r => X + C r) (g := r)]; rw [← map_map]; rw [prod_X_add_C_coeff]
    <;> rw [s.card_map r]; assumption

中文:
定理 prod_X_add_C_coeff'
  条件: {σ} (s : Multiset σ) (r : σ -> R) {k : 自然数} (h : k <= Multiset.card s)
  证明: by
  rw [← Function.comp_def (f := fun r => X + C r) (g := r)]; rw [← map_map]; rw [prod_X_add_C_coeff]
    <;> rw [s.card_map r]; assumption

Depends on / 依赖: Function, Function.comp_def, card_map, comp_def, map_map, prod_X_add_C_coeff, s.card_map
-/
theorem prod_X_add_C_coeff' {σ} (s : Multiset σ) (r : σ -> R) {k : Nat} (h : k <= Multiset.card s) :
    (s.map fun i => X + C (r i)).prod.coeff k = (s.map r).esymm (Multiset.card s - k) := by
  rw [← Function.comp_def (f := fun r => X + C r) (g := r)]; rw [← map_map]; rw [prod_X_add_C_coeff]
    <;> rw [s.card_map r]; assumption

/--
theorem `_root_.Finset.prod_X_add_C_coeff` / 定理 `_root_.Finset.prod_X_add_C_coeff`

English:
theorem _root_.Finset.prod_X_add_C_coeff
  given: {σ} (s : Finset σ) (r : σ -> R) {k : Nat} (h : k <= #s)
  proof: by
  rw [Finset.prod]; rw [prod_X_add_C_coeff' _ r h]; rw [Finset.esymm_map_val]
  rfl

中文:
定理 _root_.Finset.prod_X_add_C_coeff
  条件: {σ} (s : Finset σ) (r : σ -> R) {k : 自然数} (h : k <= #s)
  证明: by
  rw [Finset.prod]; rw [prod_X_add_C_coeff' _ r h]; rw [Finset.esymm_map_val]
  rfl

Depends on / 依赖: Finset, Finset.esymm_map_val, Finset.prod, esymm_map_val, prod_X_add_C_coeff
-/
theorem _root_.Finset.prod_X_add_C_coeff {σ} (s : Finset σ) (r : σ -> R) {k : Nat} (h : k <= #s) :
    (∏ i in s, (X + C (r i))).coeff k = ∑ t in s.powersetCard (#s - k), ∏ i in t, r i := by
  rw [Finset.prod]; rw [prod_X_add_C_coeff' _ r h]; rw [Finset.esymm_map_val]
  rfl

end Semiring

section Ring

variable {R : Type*} [CommRing R]

/--
theorem `esymm_neg` / 定理 `esymm_neg`

English:
theorem esymm_neg
  given: (s : Multiset R) (k : Nat)
  statement: (map Neg.neg s).esymm k = (-1) ^ k * esymm s k
  proof: by
  rw [esymm]; rw [esymm]; rw [← Multiset.sum_map_mul_left]; rw [Multiset.powersetCard_map]; rw [Multiset.map_map]; rw [map_congr rfl]
  intro x hx
  rw [(mem_powersetCard.mp hx).right.symm]; rw [← prod_replicate]; rw [← Multiset.map_const]
  nth_rw 3 [← map_id' x]
  rw [← prod_map_mul]; rw [map_c

中文:
定理 esymm_neg
  条件: (s : Multiset R) (k : 自然数)
  结论: (map Neg.neg s).esymm k = (-1) ^ k * esymm s k
  证明: by
  rw [esymm]; rw [esymm]; rw [← Multiset.sum_map_mul_left]; rw [Multiset.powersetCard_map]; rw [Multiset.map_map]; rw [map_congr rfl]
  intro x hx
  rw [(mem_powersetCard.mp hx).right.symm]; rw [← prod_replicate]; rw [← Multiset.map_const]
  nth_rw 3 [← map_id' x]
  rw [← prod_map_mul]; rw [map_c

Depends on / 依赖: Function, Function.comp_apply, Multiset, Multiset.map_const, Multiset.map_map, Multiset.powersetCard_map, Multiset.sum_map_mul_left, UniformSpace, ValuativeRel, comp_apply, map_congr, map_const, map_id, map_map, mem_powersetCard, mem_powersetCard.mp, neg_one_mul, nth_rw, powersetCard_map, prod_map_mul
-/
theorem esymm_neg (s : Multiset R) (k : Nat) : (map Neg.neg s).esymm k = (-1) ^ k * esymm s k := by
  rw [esymm]; rw [esymm]; rw [← Multiset.sum_map_mul_left]; rw [Multiset.powersetCard_map]; rw [Multiset.map_map]; rw [map_congr rfl]
  intro x hx
  rw [(mem_powersetCard.mp hx).right.symm]; rw [← prod_replicate]; rw [← Multiset.map_const]
  nth_rw 3 [← map_id' x]
  rw [← prod_map_mul]; rw [map_congr rfl]; rw [Function.comp_apply]
  exact fun z _ => neg_one_mul z

/--
theorem `prod_X_sub_X_eq_sum_esymm` / 定理 `prod_X_sub_X_eq_sum_esymm`

English:
theorem prod_X_sub_X_eq_sum_esymm
  given: (s : Multiset R)
  proof: by
  conv_lhs =>
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert! prod_X_add_C_eq_sum_esymm (map (fun t => -t) s) using 1
  · rw [map_map]; rfl
  · simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one]

中文:
定理 prod_X_sub_X_eq_sum_esymm
  条件: (s : Multiset R)
  证明: by
  conv_lhs =>
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert! prod_X_add_C_eq_sum_esymm (map (fun t => -t) s) using 1
  · rw [map_map]; rfl
  · simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one]

Depends on / 依赖: card_map, conv_lhs, convert, esymm_neg, map_map, map_mul, map_neg, map_one, map_pow, mul_assoc, prod_X_add_C_eq_sum_esymm, sub_eq_add_neg
-/
theorem prod_X_sub_X_eq_sum_esymm (s : Multiset R) :
    (s.map fun t => X - C t).prod =
      ∑ j in Finset.range (Multiset.card s + 1),
        (-1) ^ j * (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  conv_lhs =>
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert! prod_X_add_C_eq_sum_esymm (map (fun t => -t) s) using 1
  · rw [map_map]; rfl
  · simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one]

/--
theorem `prod_X_sub_C_coeff` / 定理 `prod_X_sub_C_coeff`

English:
theorem prod_X_sub_C_coeff
  given: (s : Multiset R) {k : Nat} (h : k <= Multiset.card s)
  proof: by
  conv_lhs =>
    congr
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert! prod_X_add_C_coeff (map (fun t => -t) s) _ using 1
  · rw [map_map]; rfl
  · rw [esymm_neg, card_map]
  · rwa [card_map]

中文:
定理 prod_X_sub_C_coeff
  条件: (s : Multiset R) {k : 自然数} (h : k <= Multiset.card s)
  证明: by
  conv_lhs =>
    congr
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert! prod_X_add_C_coeff (map (fun t => -t) s) _ using 1
  · rw [map_map]; rfl
  · rw [esymm_neg, card_map]
  · rwa [card_map]

Depends on / 依赖: card_map, conv_lhs, convert, esymm_neg, map_map, map_neg, prod_X_add_C_coeff, sub_eq_add_neg
-/
theorem prod_X_sub_C_coeff (s : Multiset R) {k : Nat} (h : k <= Multiset.card s) :
    (s.map fun t => X - C t).prod.coeff k =
    (-1) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k) := by
  conv_lhs =>
    congr
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert! prod_X_add_C_coeff (map (fun t => -t) s) _ using 1
  · rw [map_map]; rfl
  · rw [esymm_neg, card_map]
  · rwa [card_map]

/--
theorem `_root_.Polynomial.coeff_eq_esymm_roots_of_card` / 定理 `_root_.Polynomial.coeff_eq_esymm_roots_of_card`

English:
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_card
  statement: [IsDomain R] {p : R[X]}
  proof: by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  rw [coeff_C_mul]; rw [mul_assoc]; congr
  have : k <= card (roots p) := by rw [hroots]; exact h
  convert! p.roots.prod_X_sub_C_coeff this using 3 <;> rw [hroots]

中文:
定理 _root_.Polynomial.coeff_eq_esymm_roots_of_card
  结论: [IsDomain R] {p : R[X]}
  证明: by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  rw [coeff_C_mul]; rw [mul_assoc]; congr
  have : k <= card (roots p) := by rw [hroots]; exact h
  convert! p.roots.prod_X_sub_C_coeff this using 3 <;> rw [hroots]

Depends on / 依赖: C_leadingCoeff_mul_prod_multiset_X_sub_C, coeff_C_mul, conv_lhs, convert, hroots, mul_assoc, p.roots.prod_X_sub_C_coeff, prod_X_sub_C_coeff
-/
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_card [IsDomain R] {p : R[X]}
    (hroots : Multiset.card p.roots = p.natDegree) {k : Nat} (h : k <= p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  rw [coeff_C_mul]; rw [mul_assoc]; congr
  have : k <= card (roots p) := by rw [hroots]; exact h
  convert! p.roots.prod_X_sub_C_coeff this using 3 <;> rw [hroots]

/--
theorem `_root_.Polynomial.coeff_eq_esymm_roots_of_splits` / 定理 `_root_.Polynomial.coeff_eq_esymm_roots_of_splits`

English:
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_splits
  statement: {F} [Field F] {p : F[X]}
  proof: Polynomial.coeff_eq_esymm_roots_of_card (splits_iff_card_roots.1 hsplit) h

中文:
定理 _root_.Polynomial.coeff_eq_esymm_roots_of_splits
  结论: {F} [Field F] {p : F[X]}
  证明: Polynomial.coeff_eq_esymm_roots_of_card (splits_iff_card_roots.1 hsplit) h

Depends on / 依赖: Polynomial, Polynomial.coeff_eq_esymm_roots_of_card, coeff_eq_esymm_roots_of_card, hsplit, splits_iff_card_roots
-/
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_splits {F} [Field F] {p : F[X]}
    (hsplit : p.Splits) {k : Nat} (h : k <= p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) :=
  Polynomial.coeff_eq_esymm_roots_of_card (splits_iff_card_roots.1 hsplit) h

end Ring

end Multiset

section MvPolynomial

open Finset Polynomial Fintype

variable (R σ : Type*) [CommSemiring R] [Fintype σ]

/--
theorem `MvPolynomial.prod_C_add_X_eq_sum_esymm` / 定理 `MvPolynomial.prod_C_add_X_eq_sum_esymm`

English:
theorem MvPolynomial.prod_C_add_X_eq_sum_esymm
  proof: by
  let s := Finset.univ.val.map fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map]; rw [← Finset.card_univ]; rw [Finset.card_def]
  simp_rw [this, MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  co

中文:
定理 MvPolynomial.prod_C_add_X_eq_sum_esymm
  证明: by
  let s := Finset.univ.val.map fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map]; rw [← Finset.card_univ]; rw [Finset.card_def]
  simp_rw [this, MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  co

Depends on / 依赖: Finset, Finset.card_def, Finset.card_univ, Finset.prod_eq_multiset_prod, Finset.univ.val.map, Fintype, Fintype.card, Function, Function.comp_apply, Multiset, Multiset.card, Multiset.card_map, Multiset.map_map, Multiset.prod_X_add_C_eq_sum_esymm, MvPolynomial, MvPolynomial.X, MvPolynomial.esymm_eq_multiset_esymm, Valued, Valued.isTopologicalDivisionRing, card_def
-/
theorem MvPolynomial.prod_C_add_X_eq_sum_esymm :
    (∏ i : σ, (Polynomial.X + Polynomial.C (MvPolynomial.X i))) =
      ∑ j in range (card σ + 1), Polynomial.C
        (MvPolynomial.esymm σ R j) * Polynomial.X ^ (card σ - j) := by
  let s := Finset.univ.val.map fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map]; rw [← Finset.card_univ]; rw [Finset.card_def]
  simp_rw [this, MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  convert! Multiset.prod_X_add_C_eq_sum_esymm s
  simp_rw [s, Multiset.map_map, Function.comp_apply]

/--
theorem `MvPolynomial.prod_X_add_C_coeff` / 定理 `MvPolynomial.prod_X_add_C_coeff`

English:
theorem MvPolynomial.prod_X_add_C_coeff
  given: (k : Nat) (h : k <= card σ)
  proof: by
  let s := Finset.univ.val.map fun i => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map]; rw [← Finset.card_univ]; rw [Finset.card_def]
  rw [this] at h ⊢
  rw [MvPolynomial.esymm_eq_multiset_esymm σ R]; rw [Finset.prod_eq_multiset_p

中文:
定理 MvPolynomial.prod_X_add_C_coeff
  条件: (k : 自然数) (h : k <= card σ)
  证明: by
  let s := Finset.univ.val.map fun i => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map]; rw [← Finset.card_univ]; rw [Finset.card_def]
  rw [this] at h ⊢
  rw [MvPolynomial.esymm_eq_multiset_esymm σ R]; rw [Finset.prod_eq_multiset_p

Depends on / 依赖: Finset, Finset.card_def, Finset.card_univ, Finset.prod_eq_multiset_prod, Finset.univ.val.map, Fintype, Fintype.card, Function, Function.comp_apply, IsTopologicalAddGroup, IsTopologicalAddGroup.t2Space_of_zero_sep, Multiset, Multiset.card, Multiset.card_map, Multiset.map_map, Multiset.prod_X_add_C_coeff, MvPolynomial, MvPolynomial.X, MvPolynomial.esymm_eq_multiset_esymm, T0Space
-/
theorem MvPolynomial.prod_X_add_C_coeff (k : Nat) (h : k <= card σ) :
    (∏ i : σ, (Polynomial.X + Polynomial.C (MvPolynomial.X i)) : Polynomial _).coeff k =
    MvPolynomial.esymm σ R (card σ - k) := by
  let s := Finset.univ.val.map fun i => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map]; rw [← Finset.card_univ]; rw [Finset.card_def]
  rw [this] at h ⊢
  rw [MvPolynomial.esymm_eq_multiset_esymm σ R]; rw [Finset.prod_eq_multiset_prod]
  convert! Multiset.prod_X_add_C_coeff s h
  simp_rw [s, Multiset.map_map, Function.comp_apply]

end MvPolynomial
