/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Subring
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Polynomials that lift

Given semirings `R` and `S` with a morphism `f : R →+* S`, we define a subsemiring `lifts` of
`S[X]` by the image of `RingHom.of (map f)`.
Then, we prove that a polynomial that lifts can always be lifted to a polynomial of the same degree
and that a monic polynomial that lifts can be lifted to a monic polynomial (of the same degree).

## Main definition

* `lifts (f : R →+* S)` : the subsemiring of polynomials that lift.

## Main results

* `lifts_and_degree_eq` : A polynomial lifts if and only if it can be lifted to a polynomial
  of the same degree.
* `lifts_and_degree_eq_and_monic` : A monic polynomial lifts if and only if it can be lifted to a
  monic polynomial of the same degree.
* `lifts_iff_alg` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
  `mapAlg`, where `mapAlg : R[X] →ₐ[R] S[X]` is the only `R`-algebra map
  that sends `X` to `X`.

## Implementation details

In general `R` and `S` are semirings, so `lifts` is a semiring. In the case of rings, see
`lifts_iff_liftsRing`.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/

@[expose] public section


open Polynomial

noncomputable section

namespace Polynomial

universe u v w

section Semiring

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R ->+* S}

/--
Definition of `lifts` / `lifts` 的定义

English:
definition lifts
  signature: (f : R ->+* S)
  body: RingHom.rangeS (mapRingHom f)

中文:
定义 lifts
  签名: (f : R ->+* S)
  定义体: RingHom.rangeS (mapRingHom f)

Depends on / 依赖: RingHom, RingHom.rangeS, mapRingHom, rangeS
-/
def lifts (f : R ->+* S) : Subsemiring S[X] :=
  RingHom.rangeS (mapRingHom f)

/--
theorem `mem_lifts` / 定理 `mem_lifts`

English:
theorem mem_lifts
  given: (p : S[X])
  statement: p in lifts f ↔ exists q : R[X], map f q = p
  proof: by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]

中文:
定理 mem_lifts
  条件: (p : S[X])
  结论: p in lifts f ↔ 存在 q : R[X], map f q = p
  证明: by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]

Depends on / 依赖: RingHom, RingHom.mem_rangeS, coe_mapRingHom, mem_rangeS
-/
theorem mem_lifts (p : S[X]) : p in lifts f ↔ exists q : R[X], map f q = p := by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]

/--
theorem `lifts_iff_set_range` / 定理 `lifts_iff_set_range`

English:
theorem lifts_iff_set_range
  given: (p : S[X])
  statement: p in lifts f ↔ p in Set.range (map f)
  proof: by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]

中文:
定理 lifts_iff_set_range
  条件: (p : S[X])
  结论: p in lifts f ↔ p in Set.range (map f)
  证明: by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]

Depends on / 依赖: RingHom, RingHom.mem_rangeS, Set.mem_range, coe_mapRingHom, mem_range, mem_rangeS
-/
theorem lifts_iff_set_range (p : S[X]) : p in lifts f ↔ p in Set.range (map f) := by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]

/--
theorem `lifts_iff_ringHom_rangeS` / 定理 `lifts_iff_ringHom_rangeS`

English:
theorem lifts_iff_ringHom_rangeS
  given: (p : S[X])
  statement: p in lifts f ↔ p in (mapRingHom f).rangeS
  proof: by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]

中文:
定理 lifts_iff_ringHom_rangeS
  条件: (p : S[X])
  结论: p in lifts f ↔ p in (mapRingHom f).rangeS
  证明: by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]

Depends on / 依赖: RingHom, RingHom.mem_rangeS, coe_mapRingHom, mem_rangeS
-/
theorem lifts_iff_ringHom_rangeS (p : S[X]) : p in lifts f ↔ p in (mapRingHom f).rangeS := by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]

/--
theorem `lifts_iff_coeff_lifts` / 定理 `lifts_iff_coeff_lifts`

English:
theorem lifts_iff_coeff_lifts
  given: (p : S[X])
  statement: p in lifts f ↔ forall n : Nat, p.coeff n in Set.range f
  proof: by
  rw [lifts_iff_ringHom_rangeS]; rw [mem_map_rangeS f]
  rfl

中文:
定理 lifts_iff_coeff_lifts
  条件: (p : S[X])
  结论: p in lifts f ↔ 对任意 n : 自然数, p.coeff n in Set.range f
  证明: by
  rw [lifts_iff_ringHom_rangeS]; rw [mem_map_rangeS f]
  rfl

Depends on / 依赖: lifts_iff_ringHom_rangeS, mem_map_rangeS
-/
theorem lifts_iff_coeff_lifts (p : S[X]) : p in lifts f ↔ forall n : Nat, p.coeff n in Set.range f := by
  rw [lifts_iff_ringHom_rangeS]; rw [mem_map_rangeS f]
  rfl

/--
theorem `lifts_iff_coeffs_subset_range` / 定理 `lifts_iff_coeffs_subset_range`

English:
theorem lifts_iff_coeffs_subset_range
  given: (p : S[X])
  proof: by
  rw [lifts_iff_coeff_lifts]
  constructor
  · intro h _ hc
    obtain ⟨n, ⟨-, hn⟩⟩ := mem_coeffs_iff.mp hc
    exact hn ▸ h n
  · intro h n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
· exact h coeff_mem_coeffs hn

中文:
定理 lifts_iff_coeffs_subset_range
  条件: (p : S[X])
  证明: by
  rw [lifts_iff_coeff_lifts]
  constructor
  · intro h _ hc
    obtain ⟨n, ⟨-, hn⟩⟩ := mem_coeffs_iff.mp hc
    exact hn ▸ h n
  · intro h n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
· exact h coeff_mem_coeffs hn

Depends on / 依赖: coeff_mem_coeffs, lifts_iff_coeff_lifts, mem_coeffs_iff, mem_coeffs_iff.mp, p.coeff
-/
theorem lifts_iff_coeffs_subset_range (p : S[X]) :
    p in lifts f ↔ (p.coeffs : Set S) subseteq Set.range f := by
  rw [lifts_iff_coeff_lifts]
  constructor
  · intro h _ hc
    obtain ⟨n, ⟨-, hn⟩⟩ := mem_coeffs_iff.mp hc
    exact hn ▸ h n
  · intro h n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
· exact h coeff_mem_coeffs hn

/--
theorem `mem_lifts_of_surjective` / 定理 `mem_lifts_of_surjective`

English:
theorem mem_lifts_of_surjective
  given: (hf : Function.Surjective f) (p : S[X])
  statement: p in lifts f
  proof: (lifts_iff_coeff_lifts p).mpr fun n => hf (p.coeff n)

中文:
定理 mem_lifts_of_surjective
  条件: (hf : Function.Surjective f) (p : S[X])
  结论: p in lifts f
  证明: (lifts_iff_coeff_lifts p).mpr fun n => hf (p.coeff n)

Depends on / 依赖: lifts_iff_coeff_lifts, p.coeff
-/
theorem mem_lifts_of_surjective (hf : Function.Surjective f) (p : S[X]) : p in lifts f :=
  (lifts_iff_coeff_lifts p).mpr fun n => hf (p.coeff n)

/--
theorem `C_mem_lifts` / 定理 `C_mem_lifts`

English:
theorem C_mem_lifts
  given: (f : R ->+* S) (r : R)
  statement: C (f r) in lifts f
  proof: ⟨C r, by
    simp only [coe_mapRingHom, map_C]⟩

中文:
定理 C_mem_lifts
  条件: (f : R ->+* S) (r : R)
  结论: C (f r) in lifts f
  证明: ⟨C r, by
    simp only [coe_mapRingHom, map_C]⟩

Depends on / 依赖: coe_mapRingHom, map_C
-/
theorem C_mem_lifts (f : R ->+* S) (r : R) : C (f r) in lifts f :=
  ⟨C r, by
    simp only [coe_mapRingHom, map_C]⟩

/--
theorem `C'_mem_lifts` / 定理 `C'_mem_lifts`

English:
theorem C'_mem_lifts
  given: {f : R ->+* S} {s : S} (h : s in Set.range f)
  statement: C s in lifts f
  proof: by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use C r
  simp only [coe_mapRingHom, map_C]

中文:
定理 C'_mem_lifts
  条件: {f : R ->+* S} {s : S} (h : s in Set.range f)
  结论: C s in lifts f
  证明: by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use C r
  simp only [coe_mapRingHom, map_C]

Depends on / 依赖: Set.mem_range, coe_mapRingHom, map_C, mem_range
-/
theorem C'_mem_lifts {f : R ->+* S} {s : S} (h : s in Set.range f) : C s in lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use C r
  simp only [coe_mapRingHom, map_C]

/--
theorem `X_mem_lifts` / 定理 `X_mem_lifts`

English:
theorem X_mem_lifts
  given: (f : R ->+* S)
  statement: (X : S[X]) in lifts f
  proof: ⟨X, by
    simp only [coe_mapRingHom, map_X]⟩

中文:
定理 X_mem_lifts
  条件: (f : R ->+* S)
  结论: (X : S[X]) in lifts f
  证明: ⟨X, by
    simp only [coe_mapRingHom, map_X]⟩

Depends on / 依赖: coe_mapRingHom, map_X
-/
theorem X_mem_lifts (f : R ->+* S) : (X : S[X]) in lifts f :=
  ⟨X, by
    simp only [coe_mapRingHom, map_X]⟩

/--
theorem `X_pow_mem_lifts` / 定理 `X_pow_mem_lifts`

English:
theorem X_pow_mem_lifts
  given: (f : R ->+* S) (n : Nat)
  statement: (X ^ n : S[X]) in lifts f
  proof: ⟨X ^ n, by
    simp only [coe_mapRingHom, map_pow, map_X]⟩

中文:
定理 X_pow_mem_lifts
  条件: (f : R ->+* S) (n : 自然数)
  结论: (X ^ n : S[X]) in lifts f
  证明: ⟨X ^ n, by
    simp only [coe_mapRingHom, map_pow, map_X]⟩

Depends on / 依赖: coe_mapRingHom, map_X, map_pow
-/
theorem X_pow_mem_lifts (f : R ->+* S) (n : Nat) : (X ^ n : S[X]) in lifts f :=
  ⟨X ^ n, by
    simp only [coe_mapRingHom, map_pow, map_X]⟩

/--
theorem `base_mul_mem_lifts` / 定理 `base_mul_mem_lifts`

English:
theorem base_mul_mem_lifts
  given: {p : S[X]} (r : R) (hp : p in lifts f)
  statement: C (f r) * p in lifts f
  proof: by
  simp only [lifts, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨p₁, rfl⟩ := hp
  use C r * p₁
  simp only [coe_mapRingHom, map_C, map_mul]

中文:
定理 base_mul_mem_lifts
  条件: {p : S[X]} (r : R) (hp : p in lifts f)
  结论: C (f r) * p in lifts f
  证明: by
  simp only [lifts, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨p₁, rfl⟩ := hp
  use C r * p₁
  simp only [coe_mapRingHom, map_C, map_mul]

Depends on / 依赖: RingHom, RingHom.mem_rangeS, coe_mapRingHom, map_C, map_mul, mem_rangeS
-/
theorem base_mul_mem_lifts {p : S[X]} (r : R) (hp : p in lifts f) : C (f r) * p in lifts f := by
  simp only [lifts, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨p₁, rfl⟩ := hp
  use C r * p₁
  simp only [coe_mapRingHom, map_C, map_mul]

/--
theorem `monomial_mem_lifts` / 定理 `monomial_mem_lifts`

English:
theorem monomial_mem_lifts
  given: {s : S} (n : Nat) (h : s in Set.range f)
  statement: monomial n s in lifts f
  proof: by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use monomial n r
  simp only [coe_mapRingHom, map_monomial]

中文:
定理 monomial_mem_lifts
  条件: {s : S} (n : 自然数) (h : s in Set.range f)
  结论: monomial n s in lifts f
  证明: by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use monomial n r
  simp only [coe_mapRingHom, map_monomial]

Depends on / 依赖: Set.mem_range, coe_mapRingHom, map_monomial, mem_range, monomial
-/
theorem monomial_mem_lifts {s : S} (n : Nat) (h : s in Set.range f) : monomial n s in lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use monomial n r
  simp only [coe_mapRingHom, map_monomial]

/--
theorem `erase_mem_lifts` / 定理 `erase_mem_lifts`

English:
theorem erase_mem_lifts
  given: {p : S[X]} (n : Nat) (h : p in lifts f)
  statement: p.erase n in lifts f
  proof: by
  rw [lifts_iff_ringHom_rangeS]; rw [mem_map_rangeS] at h ⊢
  intro k
  by_cases hk : k = n
  · use 0
    simp only [hk, map_zero, erase_same]
  obtain ⟨i, hi⟩ := h k
  use i
  simp only [hi, hk, erase_ne, Ne, not_false_iff]

中文:
定理 erase_mem_lifts
  条件: {p : S[X]} (n : 自然数) (h : p in lifts f)
  结论: p.erase n in lifts f
  证明: by
  rw [lifts_iff_ringHom_rangeS]; rw [mem_map_rangeS] at h ⊢
  intro k
  by_cases hk : k = n
  · use 0
    simp only [hk, map_zero, erase_same]
  obtain ⟨i, hi⟩ := h k
  use i
  simp only [hi, hk, erase_ne, Ne, not_false_iff]

Depends on / 依赖: erase_ne, erase_same, lifts_iff_ringHom_rangeS, map_zero, mem_map_rangeS, not_false_iff
-/
theorem erase_mem_lifts {p : S[X]} (n : Nat) (h : p in lifts f) : p.erase n in lifts f := by
  rw [lifts_iff_ringHom_rangeS]; rw [mem_map_rangeS] at h ⊢
  intro k
  by_cases hk : k = n
  · use 0
    simp only [hk, map_zero, erase_same]
  obtain ⟨i, hi⟩ := h k
  use i
  simp only [hi, hk, erase_ne, Ne, not_false_iff]

section LiftDeg

/--
theorem `monomial_mem_lifts_and_degree_eq` / 定理 `monomial_mem_lifts_and_degree_eq`

English:
theorem monomial_mem_lifts_and_degree_eq
  given: {s : S} {n : Nat} (hl : monomial n s in lifts f)
  proof: by
  rcases eq_or_ne s 0 with rfl | h
  · exact ⟨0, by simp⟩
  obtain ⟨a, rfl⟩ := coeff_monomial_same n s ▸ (monomial n s).lifts_iff_coeff_lifts.mp hl n
  refine ⟨monomial n a, map_monomial f, ?_⟩
  rw [degree_monomial]; rw [degree_monomial n h]
  exact mt (fun ha => ha ▸ map_zero f) h

中文:
定理 monomial_mem_lifts_and_degree_eq
  条件: {s : S} {n : 自然数} (hl : monomial n s in lifts f)
  证明: by
  rcases eq_or_ne s 0 with rfl | h
  · exact ⟨0, by simp⟩
  obtain ⟨a, rfl⟩ := coeff_monomial_same n s ▸ (monomial n s).lifts_iff_coeff_lifts.mp hl n
  refine ⟨monomial n a, map_monomial f, ?_⟩
  rw [degree_monomial]; rw [degree_monomial n h]
  exact mt (fun ha => ha ▸ map_zero f) h

Depends on / 依赖: coeff_monomial_same, degree_monomial, eq_or_ne, lifts_iff_coeff_lifts, lifts_iff_coeff_lifts.mp, map_monomial, map_zero, monomial
-/
theorem monomial_mem_lifts_and_degree_eq {s : S} {n : Nat} (hl : monomial n s in lifts f) :
    exists q : R[X], map f q = monomial n s ∧ q.degree = (monomial n s).degree := by
  rcases eq_or_ne s 0 with rfl | h
  · exact ⟨0, by simp⟩
  obtain ⟨a, rfl⟩ := coeff_monomial_same n s ▸ (monomial n s).lifts_iff_coeff_lifts.mp hl n
  refine ⟨monomial n a, map_monomial f, ?_⟩
  rw [degree_monomial]; rw [degree_monomial n h]
  exact mt (fun ha => ha ▸ map_zero f) h

/--
theorem `exists_support_eq_of_mem_lifts` / 定理 `exists_support_eq_of_mem_lifts`

English:
theorem exists_support_eq_of_mem_lifts
  given: {p : S[X]} (hlifts : p in lifts f)
  proof: by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : Nat -> R := fun k => (hlifts k).choose
  have hg : forall k, f (g k) = p.coeff k := fun k => (hlifts k).choose_spec
  let q : R[X] := ∑ k in p.support, monomial k (g k)
  have hq : map f q = p := by simp_rw [q, Polynomial.map_sum, map_monomial, hg,

中文:
定理 exists_support_eq_of_mem_lifts
  条件: {p : S[X]} (hlifts : p in lifts f)
  证明: by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : Nat -> R := fun k => (hlifts k).choose
  have hg : forall k, f (g k) = p.coeff k := fun k => (hlifts k).choose_spec
  let q : R[X] := ∑ k in p.support, monomial k (g k)
  have hq : map f q = p := by simp_rw [q, Polynomial.map_sum, map_monomial, hg,

Depends on / 依赖: Finset, Finset.ext_iff, Finset.sum_ite_eq, Polynomial, Polynomial.map_sum, and_iff_left_iff_im, as_sum_support, choose_spec, coeff_monomial, ext_iff, finsetSum_coeff, hlifts, ite_ne_right_iff, lifts_iff_coeff_lifts, map_monomial, map_sum, mem_support_iff, monomial, p.coeff, p.support
-/
theorem exists_support_eq_of_mem_lifts {p : S[X]} (hlifts : p in lifts f) :
    exists q : R[X], map f q = p ∧ q.support = p.support := by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : Nat -> R := fun k => (hlifts k).choose
  have hg : forall k, f (g k) = p.coeff k := fun k => (hlifts k).choose_spec
  let q : R[X] := ∑ k in p.support, monomial k (g k)
  have hq : map f q = p := by simp_rw [q, Polynomial.map_sum, map_monomial, hg, ← as_sum_support]
  have hq' : q.support = p.support := by
    simp_rw [Finset.ext_iff, mem_support_iff, q, finsetSum_coeff, coeff_monomial,
      Finset.sum_ite_eq', ite_ne_right_iff, mem_support_iff, and_iff_left_iff_imp, not_imp_not]
    exact fun k h => by rw [← hg, h, map_zero]
  exact ⟨q, hq, hq'⟩

/--
theorem `exists_degree_eq_of_mem_lifts` / 定理 `exists_degree_eq_of_mem_lifts`

English:
theorem exists_degree_eq_of_mem_lifts
  given: {p : S[X]} (hlifts : p in lifts f)
  proof: by
  obtain ⟨q, hq, hq'⟩ := exists_support_eq_of_mem_lifts hlifts
  exact ⟨q, hq, congrArg Finset.max hq'⟩

中文:
定理 exists_degree_eq_of_mem_lifts
  条件: {p : S[X]} (hlifts : p in lifts f)
  证明: by
  obtain ⟨q, hq, hq'⟩ := exists_support_eq_of_mem_lifts hlifts
  exact ⟨q, hq, congrArg Finset.max hq'⟩

Depends on / 依赖: Finset, Finset.max, exists_support_eq_of_mem_lifts, hlifts
-/
theorem exists_degree_eq_of_mem_lifts {p : S[X]} (hlifts : p in lifts f) :
    exists q : R[X], map f q = p ∧ q.degree = p.degree := by
  obtain ⟨q, hq, hq'⟩ := exists_support_eq_of_mem_lifts hlifts
  exact ⟨q, hq, congrArg Finset.max hq'⟩

/--
theorem `exists_natDegree_eq_of_mem_lifts` / 定理 `exists_natDegree_eq_of_mem_lifts`

English:
theorem exists_natDegree_eq_of_mem_lifts
  given: {p : S[X]} (hlifts : p in lifts f)
  proof: (exists_degree_eq_of_mem_lifts hlifts).imp fun _ => And.imp_right natDegree_eq_of_degree_eq

@[deprecated (since := "2026-02-11")]
alias mem_lifts_and_degree_eq := exists_degree_eq_of_mem_lifts

中文:
定理 exists_natDegree_eq_of_mem_lifts
  条件: {p : S[X]} (hlifts : p in lifts f)
  证明: (exists_degree_eq_of_mem_lifts hlifts).imp fun _ => And.imp_right natDegree_eq_of_degree_eq

@[deprecated (since := "2026-02-11")]
alias mem_lifts_and_degree_eq := exists_degree_eq_of_mem_lifts

Depends on / 依赖: And.imp_right, exists_degree_eq_of_mem_lifts, hlifts, imp_right, natDegree_eq_of_degree_eq
-/
theorem exists_natDegree_eq_of_mem_lifts {p : S[X]} (hlifts : p in lifts f) :
    exists q, map f q = p ∧ q.natDegree = p.natDegree :=
  (exists_degree_eq_of_mem_lifts hlifts).imp fun _ => And.imp_right natDegree_eq_of_degree_eq

@[deprecated (since := "2026-02-11")]
alias mem_lifts_and_degree_eq := exists_degree_eq_of_mem_lifts

end LiftDeg

section Monic

/--
theorem `lifts_and_degree_eq_and_monic` / 定理 `lifts_and_degree_eq_and_monic`

English:
theorem lifts_and_degree_eq_and_monic
  statement: [Nontrivial S] {p : S[X]} (hlifts : p in lifts f)
  proof: by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : Nat -> R := fun k => (hlifts k).choose
  have hg k : f (g k) = p.coeff k := (hlifts k).choose_spec
  let q : R[X] := X ^ p.natDegree + ∑ k in Finset.range p.natDegree, C (g k) * X ^ k
  have hq : map f q = p := by
    simp_rw [q, Polynomial.map_add

中文:
定理 lifts_and_degree_eq_and_monic
  结论: [Nontrivial S] {p : S[X]} (hlifts : p in lifts f)
  证明: by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : Nat -> R := fun k => (hlifts k).choose
  have hg k : f (g k) = p.coeff k := (hlifts k).choose_spec
  let q : R[X] := X ^ p.natDegree + ∑ k in Finset.range p.natDegree, C (g k) * X ^ k
  have hq : map f q = p := by
    simp_rw [q, Polynomial.map_add

Depends on / 依赖: Fin.sum_univ_eq_sum_range, Finset, Finset.range, Polynomial, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sum, as_sum, choose_spec, degree_sum_fin_lt, hlifts, hp.as_sum, lifts_iff_coeff_lifts, map_C, map_X, map_add, map_mul, map_pow, map_sum
-/
theorem lifts_and_degree_eq_and_monic [Nontrivial S] {p : S[X]} (hlifts : p in lifts f)
    (hp : p.Monic) : exists q : R[X], map f q = p ∧ q.degree = p.degree ∧ q.Monic := by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : Nat -> R := fun k => (hlifts k).choose
  have hg k : f (g k) = p.coeff k := (hlifts k).choose_spec
  let q : R[X] := X ^ p.natDegree + ∑ k in Finset.range p.natDegree, C (g k) * X ^ k
  have hq : map f q = p := by
    simp_rw [q, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, hg, ← hp.as_sum]
  have h : q.Monic := monic_X_pow_add (by simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt])
  exact ⟨q, hq, hq ▸ (h.degree_map f).symm, h⟩

/--
theorem `lifts_and_natDegree_eq_and_monic` / 定理 `lifts_and_natDegree_eq_and_monic`

English:
theorem lifts_and_natDegree_eq_and_monic
  given: {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic)
  proof: by
  rcases subsingleton_or_nontrivial S with hR | hR
  · obtain rfl : p = 1 := Subsingleton.elim _ _
    exact ⟨1, Subsingleton.elim _ _, by simp, by simp⟩
  obtain ⟨p', h₁, h₂, h₃⟩ := lifts_and_degree_eq_and_monic hlifts hp
  exact ⟨p', h₁, natDegree_eq_of_degree_eq h₂, h₃⟩

中文:
定理 lifts_and_natDegree_eq_and_monic
  条件: {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic)
  证明: by
  rcases subsingleton_or_nontrivial S with hR | hR
  · obtain rfl : p = 1 := Subsingleton.elim _ _
    exact ⟨1, Subsingleton.elim _ _, by simp, by simp⟩
  obtain ⟨p', h₁, h₂, h₃⟩ := lifts_and_degree_eq_and_monic hlifts hp
  exact ⟨p', h₁, natDegree_eq_of_degree_eq h₂, h₃⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, hlifts, lifts_and_degree_eq_and_monic, natDegree_eq_of_degree_eq, subsingleton_or_nontrivial
-/
theorem lifts_and_natDegree_eq_and_monic {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic) :
    exists q : R[X], map f q = p ∧ q.natDegree = p.natDegree ∧ q.Monic := by
  rcases subsingleton_or_nontrivial S with hR | hR
  · obtain rfl : p = 1 := Subsingleton.elim _ _
    exact ⟨1, Subsingleton.elim _ _, by simp, by simp⟩
  obtain ⟨p', h₁, h₂, h₃⟩ := lifts_and_degree_eq_and_monic hlifts hp
  exact ⟨p', h₁, natDegree_eq_of_degree_eq h₂, h₃⟩

end Monic

end Semiring

section Ring

variable {R : Type u} [Ring R] {S : Type v} [Ring S] (f : R ->+* S)

/--
Definition of `liftsRing` / `liftsRing` 的定义

English:
definition liftsRing
  signature: (f : R ->+* S)
  body: RingHom.range (mapRingHom f)

中文:
定义 liftsRing
  签名: (f : R ->+* S)
  定义体: RingHom.range (mapRingHom f)

Depends on / 依赖: RingHom, RingHom.range, mapRingHom
-/
def liftsRing (f : R ->+* S) : Subring S[X] :=
  RingHom.range (mapRingHom f)

/--
theorem `lifts_iff_liftsRing` / 定理 `lifts_iff_liftsRing`

English:
theorem lifts_iff_liftsRing
  given: (p : S[X])
  statement: p in lifts f ↔ p in liftsRing f
  proof: by
  simp only [lifts, liftsRing, RingHom.mem_range, RingHom.mem_rangeS]

中文:
定理 lifts_iff_liftsRing
  条件: (p : S[X])
  结论: p in lifts f ↔ p in liftsRing f
  证明: by
  simp only [lifts, liftsRing, RingHom.mem_range, RingHom.mem_rangeS]

Depends on / 依赖: RingHom, RingHom.mem_range, RingHom.mem_rangeS, liftsRing, mem_range, mem_rangeS
-/
theorem lifts_iff_liftsRing (p : S[X]) : p in lifts f ↔ p in liftsRing f := by
  simp only [lifts, liftsRing, RingHom.mem_range, RingHom.mem_rangeS]

end Ring

section Algebra

variable {R : Type u} [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]

/--
theorem `mem_lifts_iff_mem_alg` / 定理 `mem_lifts_iff_mem_alg`

English:
theorem mem_lifts_iff_mem_alg
  statement: (R : Type u) [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]
  proof: by
  simp only [coe_mapRingHom, lifts, mapAlg_eq_map, AlgHom.mem_range, RingHom.mem_rangeS]

中文:
定理 mem_lifts_iff_mem_alg
  结论: (R : 类型u) [CommSemiring R] {S : 类型v} [Semiring S] [Algebra R S]
  证明: by
  simp only [coe_mapRingHom, lifts, mapAlg_eq_map, AlgHom.mem_range, RingHom.mem_rangeS]

Depends on / 依赖: AlgHom, AlgHom.mem_range, RingHom, RingHom.mem_rangeS, coe_mapRingHom, mapAlg_eq_map, mem_range, mem_rangeS
-/
theorem mem_lifts_iff_mem_alg (R : Type u) [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]
    (p : S[X]) : p in lifts (algebraMap R S) ↔ p in AlgHom.range (@mapAlg R _ S _ _) := by
  simp only [coe_mapRingHom, lifts, mapAlg_eq_map, AlgHom.mem_range, RingHom.mem_rangeS]

/--
theorem `smul_mem_lifts` / 定理 `smul_mem_lifts`

English:
theorem smul_mem_lifts
  given: {p : S[X]} (r : R) (hp : p in lifts (algebraMap R S))
  proof: by
  rw [mem_lifts_iff_mem_alg] at hp ⊢
  exact Subalgebra.smul_mem (mapAlg R S).range hp r

中文:
定理 smul_mem_lifts
  条件: {p : S[X]} (r : R) (hp : p in lifts (algebraMap R S))
  证明: by
  rw [mem_lifts_iff_mem_alg] at hp ⊢
  exact Subalgebra.smul_mem (mapAlg R S).range hp r

Depends on / 依赖: Subalgebra, Subalgebra.smul_mem, mapAlg, mem_lifts_iff_mem_alg, smul_mem
-/
theorem smul_mem_lifts {p : S[X]} (r : R) (hp : p in lifts (algebraMap R S)) :
    r • p in lifts (algebraMap R S) := by
  rw [mem_lifts_iff_mem_alg] at hp ⊢
  exact Subalgebra.smul_mem (mapAlg R S).range hp r

/--
theorem `monic_of_monic_mapAlg` / 定理 `monic_of_monic_mapAlg`

English:
theorem monic_of_monic_mapAlg
  given: [FaithfulSMul R S] {p : Polynomial R} (hp : (mapAlg R S p).Monic)
  proof: monic_of_injective (FaithfulSMul.algebraMap_injective R S) hp

中文:
定理 monic_of_monic_mapAlg
  条件: [FaithfulSMul R S] {p : Polynomial R} (hp : (mapAlg R S p).Monic)
  证明: monic_of_injective (FaithfulSMul.algebraMap_injective R S) hp

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, monic_of_injective
-/
theorem monic_of_monic_mapAlg [FaithfulSMul R S] {p : Polynomial R} (hp : (mapAlg R S p).Monic) :
    p.Monic :=
  monic_of_injective (FaithfulSMul.algebraMap_injective R S) hp

end Algebra

end Polynomial
