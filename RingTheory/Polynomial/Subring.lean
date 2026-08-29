/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Subring.Defs

import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Polynomials over subrings

Given a ring `K` with a subring `R`, we construct a map from polynomials in `K[X]` with coefficients
in `R` to `R[X]`. We provide several lemmas to deal with coefficients, degree, and evaluation of
`Polynomial.toSubring`.

## Main Definitions

* `Polynomial.toSubring` : given a polynomial `P` in `K[X]` whose coefficients all belong to a
  subring `R` of the ring `K`, `P.toSubring R` is the corresponding polynomial in `R[X]`.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Ring R] (p : R[X]) (T : Subring R)

/--
Definition of `toSubring` / `toSubring` 的定义

English:
definition toSubring
  signature: (hp : (↑p.coeffs : Set R) subseteq T)
  body: ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
        letI := Classical.decEq R
        if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_coeffs H)⟩ : T)

中文:
定义 toSubring
  签名: (hp : (↑p.coeffs : Set R) subseteq T)
  定义体: ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
        letI := Classical.decEq R
        if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_coeffs H)⟩ : T)

Depends on / 依赖: Classical, Classical.decEq, H.symm, T.zero_mem, coeff_mem_coeffs, monomial, p.coeff, p.coeff_mem_coeffs, p.support, support, zero_mem
-/
noncomputable def toSubring (hp : (↑p.coeffs : Set R) subseteq T) : T[X] :=
  ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
        letI := Classical.decEq R
        if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_coeffs H)⟩ : T)

variable (hp : (↑p.coeffs : Set R) subseteq T)

@[simp]
/--
theorem `coeff_toSubring` / 定理 `coeff_toSubring`

English:
theorem coeff_toSubring
  given: {n : Nat}
  statement: ↑(coeff (toSubring p T hp) n) = coeff p n
  proof: by
  classical
  simp only [toSubring, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl

中文:
定理 coeff_toSubring
  条件: {n : 自然数}
  结论: ↑(coeff (toSubring p T hp) n) = coeff p n
  证明: by
  classical
  simp only [toSubring, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl

Depends on / 依赖: Finset, Finset.sum_ite_eq, classical, coeff_monomial, finsetSum_coeff, ite_not, mem_support_iff, split_ifs, sum_ite_eq, toSubring
-/
theorem coeff_toSubring {n : Nat} : ↑(coeff (toSubring p T hp) n) = coeff p n := by
  classical
  simp only [toSubring, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl

/--
theorem `coeff_toSubring'` / 定理 `coeff_toSubring'`

English:
theorem coeff_toSubring'
  given: {n : Nat}
  statement: (coeff (toSubring p T hp) n).1 = coeff p n
  proof: by
  simp

@[simp]

中文:
定理 coeff_toSubring'
  条件: {n : 自然数}
  结论: (coeff (toSubring p T hp) n).1 = coeff p n
  证明: by
  simp

@[simp]
-/
theorem coeff_toSubring' {n : Nat} : (coeff (toSubring p T hp) n).1 = coeff p n := by
  simp

@[simp]
/--
theorem `support_toSubring` / 定理 `support_toSubring`

English:
theorem support_toSubring
  statement: support (toSubring p T hp) = support p
  proof: by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩

@[simp]

中文:
定理 support_toSubring
  结论: support (toSubring p T hp) = support p
  证明: by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, ZeroMemClass, ZeroMemClass.coe_zero, coe_injective, coe_zero, coeff_toSubring, conv_rhs, mem_support_iff, not_iff_not
-/
theorem support_toSubring : support (toSubring p T hp) = support p := by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩

@[simp]
/--
theorem `degree_toSubring` / 定理 `degree_toSubring`

English:
theorem degree_toSubring
  statement: (toSubring p T hp).degree = p.degree
  proof: by simp [degree]

@[simp]

中文:
定理 degree_toSubring
  结论: (toSubring p T hp).degree = p.degree
  证明: by simp [degree]

@[simp]

Depends on / 依赖: degree
-/
theorem degree_toSubring : (toSubring p T hp).degree = p.degree := by simp [degree]

@[simp]
/--
theorem `natDegree_toSubring` / 定理 `natDegree_toSubring`

English:
theorem natDegree_toSubring
  statement: (toSubring p T hp).natDegree = p.natDegree
  proof: by simp [natDegree]

@[simp]

中文:
定理 natDegree_toSubring
  结论: (toSubring p T hp).natDegree = p.natDegree
  证明: by simp [natDegree]

@[simp]

Depends on / 依赖: natDegree
-/
theorem natDegree_toSubring : (toSubring p T hp).natDegree = p.natDegree := by simp [natDegree]

@[simp]
/--
theorem `monic_toSubring` / 定理 `monic_toSubring`

English:
theorem monic_toSubring
  statement: Monic (toSubring p T hp) ↔ Monic p
  proof: by
  simp_rw [Monic, leadingCoeff, natDegree_toSubring, ← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩

@[simp]

中文:
定理 monic_toSubring
  结论: Monic (toSubring p T hp) ↔ Monic p
  证明: by
  simp_rw [Monic, leadingCoeff, natDegree_toSubring, ← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩

@[simp]

Depends on / 依赖: OneMemClass, OneMemClass.coe_one, Subtype, Subtype.coe_injective, coe_injective, coe_one, coeff_toSubring, leadingCoeff, natDegree_toSubring, simp_rw
-/
theorem monic_toSubring : Monic (toSubring p T hp) ↔ Monic p := by
  simp_rw [Monic, leadingCoeff, natDegree_toSubring, ← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩

@[simp]
/--
theorem `toSubring_zero` / 定理 `toSubring_zero`

English:
theorem toSubring_zero
  statement: toSubring (0 : R[X]) T (by simp [coeffs]) = 0
  proof: by
  ext i
  simp

@[simp]

中文:
定理 toSubring_zero
  结论: toSubring (0 : R[X]) T (by simp [coeffs]) = 0
  证明: by
  ext i
  simp

@[simp]
-/
theorem toSubring_zero : toSubring (0 : R[X]) T (by simp [coeffs]) = 0 := by
  ext i
  simp

@[simp]
/--
theorem `toSubring_one` / 定理 `toSubring_one`

English:
theorem toSubring_one
  proof: ext fun i => Subtype.ext by
    rw [coeff_toSubring']; rw [coeff_one]; rw [coeff_one]; rw [apply_ite Subtype.val]; rw [ZeroMemClass.coe_zero]; rw [OneMemClass.coe_one]

@[simp]

中文:
定理 toSubring_one
  证明: ext fun i => Subtype.ext by
    rw [coeff_toSubring']; rw [coeff_one]; rw [coeff_one]; rw [apply_ite Subtype.val]; rw [ZeroMemClass.coe_zero]; rw [OneMemClass.coe_one]

@[simp]

Depends on / 依赖: OneMemClass, OneMemClass.coe_one, Subtype, Subtype.ext, Subtype.val, ZeroMemClass, ZeroMemClass.coe_zero, apply_ite, coe_one, coe_zero, coeff_one, coeff_toSubring
-/
theorem toSubring_one :
    toSubring (1 : R[X]) T
        (Set.Subset.trans coeffs_one <| Finset.singleton_subset_set_iff.2 T.one_mem) =
      1 :=
ext fun i => Subtype.ext by
    rw [coeff_toSubring']; rw [coeff_one]; rw [coeff_one]; rw [apply_ite Subtype.val]; rw [ZeroMemClass.coe_zero]; rw [OneMemClass.coe_one]

@[simp]
/--
theorem `map_toSubring` / 定理 `map_toSubring`

English:
theorem map_toSubring
  statement: (p.toSubring T hp).map (Subring.subtype T) = p
  proof: by
  ext n
  simp [coeff_map]

中文:
定理 map_toSubring
  结论: (p.toSubring T hp).map (Subring.subtype T) = p
  证明: by
  ext n
  simp [coeff_map]

Depends on / 依赖: coeff_map
-/
theorem map_toSubring : (p.toSubring T hp).map (Subring.subtype T) = p := by
  ext n
  simp [coeff_map]

variable (T : Subring R)

/--
Definition of `ofSubring` / `ofSubring` 的定义

English:
definition ofSubring
  signature: (p : T[X])
  body: ∑ i in p.support, monomial i (p.coeff i : R)

中文:
定义 ofSubring
  签名: (p : T[X])
  定义体: ∑ i in p.support, monomial i (p.coeff i : R)

Depends on / 依赖: monomial, p.coeff, p.support, support
-/
noncomputable def ofSubring (p : T[X]) : R[X] :=
  ∑ i in p.support, monomial i (p.coeff i : R)

/--
theorem `coeff_ofSubring` / 定理 `coeff_ofSubring`

English:
theorem coeff_ofSubring
  given: (p : T[X]) (n : Nat)
  statement: coeff (ofSubring T p) n = (coeff p n : T)
  proof: by
  simp only [ofSubring, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, Classical.not_not, ite_eq_left_iff]
  intro h
  rw [h]; rw [ZeroMemClass.coe_zero]

@[simp]

中文:
定理 coeff_ofSubring
  条件: (p : T[X]) (n : 自然数)
  结论: coeff (ofSubring T p) n = (coeff p n : T)
  证明: by
  simp only [ofSubring, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, Classical.not_not, ite_eq_left_iff]
  intro h
  rw [h]; rw [ZeroMemClass.coe_zero]

@[simp]

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.sum_ite_eq, ZeroMemClass, ZeroMemClass.coe_zero, coe_zero, coeff_monomial, finsetSum_coeff, ite_eq_left_iff, mem_support_iff, not_not, ofSubring, sum_ite_eq
-/
theorem coeff_ofSubring (p : T[X]) (n : Nat) : coeff (ofSubring T p) n = (coeff p n : T) := by
  simp only [ofSubring, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, Classical.not_not, ite_eq_left_iff]
  intro h
  rw [h]; rw [ZeroMemClass.coe_zero]

@[simp]
/--
theorem `coeffs_ofSubring` / 定理 `coeffs_ofSubring`

English:
theorem coeffs_ofSubring
  given: {p : T[X]}
  statement: (↑(p.ofSubring T).coeffs : Set R) subseteq T
  proof: by
  intro i hi
  simp only [coeffs, Set.mem_image, mem_support_iff, Ne, Finset.mem_coe,
    (Finset.coe_image)] at hi
  rcases hi with ⟨n, _, h'n⟩
  rw [← h'n]; rw [coeff_ofSubring]
  exact Subtype.mem (coeff p n : T)

中文:
定理 coeffs_ofSubring
  条件: {p : T[X]}
  结论: (↑(p.ofSubring T).coeffs : Set R) subseteq T
  证明: by
  intro i hi
  simp only [coeffs, Set.mem_image, mem_support_iff, Ne, Finset.mem_coe,
    (Finset.coe_image)] at hi
  rcases hi with ⟨n, _, h'n⟩
  rw [← h'n]; rw [coeff_ofSubring]
  exact Subtype.mem (coeff p n : T)

Depends on / 依赖: Finset, Finset.coe_image, Finset.mem_coe, Set.mem_image, Subtype, Subtype.mem, coe_image, coeff_ofSubring, coeffs, mem_coe, mem_image, mem_support_iff
-/
theorem coeffs_ofSubring {p : T[X]} : (↑(p.ofSubring T).coeffs : Set R) subseteq T := by
  intro i hi
  simp only [coeffs, Set.mem_image, mem_support_iff, Ne, Finset.mem_coe,
    (Finset.coe_image)] at hi
  rcases hi with ⟨n, _, h'n⟩
  rw [← h'n]; rw [coeff_ofSubring]
  exact Subtype.mem (coeff p n : T)

end Polynomial
