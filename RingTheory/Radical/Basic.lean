/-
Copyright (c) 2024 Jineon Baek, Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee, Bhavik Mehta, Arend Mellendijk
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Radical of an element of a unique factorization normalization monoid

This file defines the radical of an element `a` in a unique factorization normalization
monoid as the product of normalized prime factors of `a` without duplication.
This is different from the radical of an ideal.

Lemmas relating to natural numbers and integers are in `Mathlib.RingTheory.Radical.NatInt`.

## Main declarations

- `radical`: The radical of an element `a` in a unique factorization monoid is the product of
  its prime factors.
- `radical_eq_of_associated`: If `a` and `b` are associates, i.e. `a * u = b` for some unit `u`,
  then `radical a = radical b`.
- `radical_mul_of_isUnit_left`: Multiplying by a unit does not change the radical.
- `radical_dvd_self`: `radical a` divides `a`.
- `radical_pow`: `radical (a ^ n) = radical a` for any `n ≥ 1`.
- `radical_of_prime`: Radical of a prime element is equal to its normalization.
- `radical_pow_of_prime`: Radical of a power of a prime element is equal to its normalization.
- `radical_mul`, `radical_prod`: Radical is multiplicative for (pairwise) relatively prime elements.
- `radical_mul_dvd`, `radical_prod_dvd`: Radical of a product divides the product of radicals.

### For Euclidean domains

- `EuclideanDomain.divRadical`: For an element `a` in a Euclidean domain, `a / radical a`.
- `EuclideanDomain.divRadical_mul`: `divRadical` of a product is the product of `divRadical`s.
- `IsCoprime.divRadical`: `divRadical` of coprime elements are coprime.

## TODO

- Connect this notion with `Ideal.radical`. Particularly, for a principal ideal,
  `Ideal.radical (Ideal.span {a}) = Ideal.span {radical a}`.
-/

@[expose] public noncomputable section

namespace UniqueFactorizationMonoid

variable {M : Type*} [CommMonoidWithZero M] [NormalizationMonoid M]
  [UniqueFactorizationMonoid M] {a b u : M}

open scoped Classical in
/--
Definition of `primeFactors` / `primeFactors` 的定义

English:
definition primeFactors
  signature: (a : M)
  body: (normalizedFactors a).toFinset

@[simp]

中文:
定义 primeFactors
  签名: (a : M)
  定义体: (normalizedFactors a).toFinset

@[simp]

Depends on / 依赖: CompactT2, CompactT2.ExtremallyDisconnected.projective, ExtremallyDisconnected, Function, Function.Surjective, Profinite, Profinite.epi_iff_surjective, Surjective, X.prop, congr_fun, continuous, epi_iff_surjective, f.hom.hom.continuous, h.left, h.right, hom.hom.continuous, normalizedFactors, projective, toFinset, toProfinite
-/
def primeFactors (a : M) : Finset M :=
  (normalizedFactors a).toFinset

@[simp]
/--
theorem `toFinset_normalizedFactors` / 定理 `toFinset_normalizedFactors`

English:
theorem toFinset_normalizedFactors
  given: [DecidableEq M]
  proof: by
  unfold primeFactors
  convert rfl

中文:
定理 toFinset_normalizedFactors
  条件: [DecidableEq M]
  证明: by
  unfold primeFactors
  convert rfl

Depends on / 依赖: CompactT2, CompactT2.ExtremallyDisconnected.projective, ExtremallyDisconnected, Function, Function.Surjective, Stonean, Stonean.epi_iff_surjective, Surjective, X.prop, X.toTop, congr_fun, continuous, convert, epi_iff_surjective, f.hom.hom.continuous, h.left, h.right, hom.hom.continuous, primeFactors, projective
-/
theorem toFinset_normalizedFactors [DecidableEq M] :
    (normalizedFactors a).toFinset = primeFactors a := by
  unfold primeFactors
  convert rfl

/--
lemma `mem_primeFactors` / 引理 `mem_primeFactors`

English:
lemma mem_primeFactors
  statement: a in primeFactors b ↔ a in normalizedFactors b
  proof: by
  simp only [primeFactors, Multiset.mem_toFinset]

中文:
引理 mem_primeFactors
  结论: a in primeFactors b ↔ a in normalizedFactors b
  证明: by
  simp only [primeFactors, Multiset.mem_toFinset]

Depends on / 依赖: Multiset, Multiset.mem_toFinset, mem_toFinset, primeFactors
-/
lemma mem_primeFactors : a in primeFactors b ↔ a in normalizedFactors b := by
  simp only [primeFactors, Multiset.mem_toFinset]

/--
theorem `_root_.Associated.primeFactors_eq` / 定理 `_root_.Associated.primeFactors_eq`

English:
theorem _root_.Associated.primeFactors_eq
  given: {a b : M} (h : Associated a b)
  proof: by
  unfold primeFactors
  rw [h.normalizedFactors_eq]

中文:
定理 _root_.Associated.primeFactors_eq
  条件: {a b : M} (h : Associated a b)
  证明: by
  unfold primeFactors
  rw [h.normalizedFactors_eq]

Depends on / 依赖: h.normalizedFactors_eq, normalizedFactors_eq, primeFactors
-/
theorem _root_.Associated.primeFactors_eq {a b : M} (h : Associated a b) :
    primeFactors a = primeFactors b := by
  unfold primeFactors
  rw [h.normalizedFactors_eq]

/--
lemma `primeFactors_zero` / 引理 `primeFactors_zero`

English:
lemma primeFactors_zero
  statement: primeFactors (0 : M) = ∅
  proof: by simp [primeFactors]

中文:
引理 primeFactors_zero
  结论: primeFactors (0 : M) = ∅
  证明: by simp [primeFactors]
-/
@[simp] lemma primeFactors_zero : primeFactors (0 : M) = ∅ := by simp [primeFactors]

/--
lemma `primeFactors_one` / 引理 `primeFactors_one`

English:
lemma primeFactors_one
  statement: primeFactors (1 : M) = ∅
  proof: by simp [primeFactors]

中文:
引理 primeFactors_one
  结论: primeFactors (1 : M) = ∅
  证明: by simp [primeFactors]
-/
@[simp] lemma primeFactors_one : primeFactors (1 : M) = ∅ := by simp [primeFactors]

/--
lemma `pairwise_primeFactors_isRelPrime` / 引理 `pairwise_primeFactors_isRelPrime`

English:
lemma pairwise_primeFactors_isRelPrime
  proof: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  intro x hx y hy hxy
  simp only [Finset.mem_coe, mem_primeFactors, mem_normalizedFactors_iff' ha₀] at hx hy
  rw [hx.1.isRelPrime_iff_not_dvd]
  contrapose hxy
  have : Associated x y := hx.1.associated_of_dvd hy.1 hxy
  exact this.eq_of_normalized hx

中文:
引理 pairwise_primeFactors_isRelPrime
  证明: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  intro x hx y hy hxy
  simp only [Finset.mem_coe, mem_primeFactors, mem_normalizedFactors_iff' ha₀] at hx hy
  rw [hx.1.isRelPrime_iff_not_dvd]
  contrapose hxy
  have : Associated x y := hx.1.associated_of_dvd hy.1 hxy
  exact this.eq_of_normalized hx

Depends on / 依赖: Associated, Finset, Finset.mem_coe, associated_of_dvd, contrapose, eq_of_normalized, eq_or_ne, isRelPrime_iff_not_dvd, mem_coe, mem_normalizedFactors_iff, mem_primeFactors, this.eq_of_normalized
-/
lemma pairwise_primeFactors_isRelPrime :
    Set.Pairwise (primeFactors a : Set M) IsRelPrime := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  intro x hx y hy hxy
  simp only [Finset.mem_coe, mem_primeFactors, mem_normalizedFactors_iff' ha₀] at hx hy
  rw [hx.1.isRelPrime_iff_not_dvd]
  contrapose hxy
  have : Associated x y := hx.1.associated_of_dvd hy.1 hxy
  exact this.eq_of_normalized hx.2.1 hy.2.1

/--
theorem `primeFactors_pow` / 定理 `primeFactors_pow`

English:
theorem primeFactors_pow
  given: (a : M) {n : Nat} (hn : n != 0)
  statement: primeFactors (a ^ n) = primeFactors a
  proof: by
  simp_rw [primeFactors, normalizedFactors_pow, Multiset.toFinset_nsmul _ _ hn]

@[simp]

中文:
定理 primeFactors_pow
  条件: (a : M) {n : 自然数} (hn : n != 0)
  结论: primeFactors (a ^ n) = primeFactors a
  证明: by
  simp_rw [primeFactors, normalizedFactors_pow, Multiset.toFinset_nsmul _ _ hn]

@[simp]

Depends on / 依赖: Multiset, Multiset.toFinset_nsmul, normalizedFactors_pow, primeFactors, simp_rw, toFinset_nsmul
-/
theorem primeFactors_pow (a : M) {n : Nat} (hn : n != 0) : primeFactors (a ^ n) = primeFactors a := by
  simp_rw [primeFactors, normalizedFactors_pow, Multiset.toFinset_nsmul _ _ hn]

@[simp]
/--
theorem `primeFactors_pow'` / 定理 `primeFactors_pow'`

English:
theorem primeFactors_pow'
  given: (a : M) {n : Nat} [NeZero n]
  statement: primeFactors (a ^ n) = primeFactors a
  proof: primeFactors_pow a NeZero.out

中文:
定理 primeFactors_pow'
  条件: (a : M) {n : 自然数} [NeZero n]
  结论: primeFactors (a ^ n) = primeFactors a
  证明: primeFactors_pow a NeZero.out

Depends on / 依赖: NeZero, NeZero.out, primeFactors_pow
-/
theorem primeFactors_pow' (a : M) {n : Nat} [NeZero n] : primeFactors (a ^ n) = primeFactors a :=
  primeFactors_pow a NeZero.out

/--
lemma `normalizedFactors_nodup` / 引理 `normalizedFactors_nodup`

English:
lemma normalizedFactors_nodup
  given: (ha : IsRadical a)
  statement: (normalizedFactors a).Nodup
  proof: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rwa [← squarefree_iff_nodup_normalizedFactors ha₀, ← isRadical_iff_squarefree_of_ne_zero ha₀]

中文:
引理 normalizedFactors_nodup
  条件: (ha : IsRadical a)
  结论: (normalizedFactors a).Nodup
  证明: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rwa [← squarefree_iff_nodup_normalizedFactors ha₀, ← isRadical_iff_squarefree_of_ne_zero ha₀]

Depends on / 依赖: eq_or_ne, isRadical_iff_squarefree_of_ne_zero, squarefree_iff_nodup_normalizedFactors
-/
lemma normalizedFactors_nodup (ha : IsRadical a) : (normalizedFactors a).Nodup := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rwa [← squarefree_iff_nodup_normalizedFactors ha₀, ← isRadical_iff_squarefree_of_ne_zero ha₀]

/--
lemma `primeFactors_of_isUnit` / 引理 `primeFactors_of_isUnit`

English:
lemma primeFactors_of_isUnit
  given: (h : IsUnit a)
  statement: primeFactors a = ∅
  proof: by
  classical
  rw [primeFactors]; rw [normalizedFactors_of_isUnit h]; rw [Multiset.toFinset_zero]

中文:
引理 primeFactors_of_isUnit
  条件: (h : IsUnit a)
  结论: primeFactors a = ∅
  证明: by
  classical
  rw [primeFactors]; rw [normalizedFactors_of_isUnit h]; rw [Multiset.toFinset_zero]

Depends on / 依赖: InducedCategory, InducedCategory.homMk, Multiset, Multiset.toFinset_zero, classical, normalizedFactors_of_isUnit, primeFactors, profiniteToCompHaus, profiniteToCompHaus.obj, projectivePresentation, projectivePresentation.f.hom, toFinset_zero
-/
lemma primeFactors_of_isUnit (h : IsUnit a) : primeFactors a = ∅ := by
  classical
  rw [primeFactors]; rw [normalizedFactors_of_isUnit h]; rw [Multiset.toFinset_zero]

/--
theorem `primeFactors_eq_empty_iff` / 定理 `primeFactors_eq_empty_iff`

English:
theorem primeFactors_eq_empty_iff
  given: (ha : a != 0)
  statement: primeFactors a = ∅ ↔ IsUnit a
  proof: by
  classical
  rw [primeFactors]; rw [Multiset.toFinset_eq_empty]; rw [normalizedFactors_eq_zero_iff ha]

中文:
定理 primeFactors_eq_empty_iff
  条件: (ha : a != 0)
  结论: primeFactors a = ∅ ↔ IsUnit a
  证明: by
  classical
  rw [primeFactors]; rw [Multiset.toFinset_eq_empty]; rw [normalizedFactors_eq_zero_iff ha]

Depends on / 依赖: CompHaus, CompHaus.epi_iff_surjective, Multiset, Multiset.toFinset_eq_empty, classical, epi_iff_surjective, normalizedFactors_eq_zero_iff, primeFactors, profiniteToCompHaus, profiniteToCompHaus.obj, projectivePresentation, projectivePresentation.epi, toFinset_eq_empty
-/
theorem primeFactors_eq_empty_iff (ha : a != 0) : primeFactors a = ∅ ↔ IsUnit a := by
  classical
  rw [primeFactors]; rw [Multiset.toFinset_eq_empty]; rw [normalizedFactors_eq_zero_iff ha]

/--
lemma `primeFactors_val_eq_normalizedFactors` / 引理 `primeFactors_val_eq_normalizedFactors`

English:
lemma primeFactors_val_eq_normalizedFactors
  given: (ha : IsRadical a)
  proof: by
  classical
  rw [primeFactors]; rw [Multiset.toFinset_val]; rw [Multiset.dedup_eq_self]
  exact normalizedFactors_nodup ha

中文:
引理 primeFactors_val_eq_normalizedFactors
  条件: (ha : IsRadical a)
  证明: by
  classical
  rw [primeFactors]; rw [Multiset.toFinset_val]; rw [Multiset.dedup_eq_self]
  exact normalizedFactors_nodup ha

Depends on / 依赖: Multiset, Multiset.dedup_eq_self, Multiset.toFinset_val, classical, dedup_eq_self, normalizedFactors_nodup, primeFactors, toFinset_val
-/
lemma primeFactors_val_eq_normalizedFactors (ha : IsRadical a) :
    (primeFactors a).val = normalizedFactors a := by
  classical
  rw [primeFactors]; rw [Multiset.toFinset_val]; rw [Multiset.dedup_eq_self]
  exact normalizedFactors_nodup ha

-- Note that the non-zero assumptions are necessary here.
/--
theorem `primeFactors_mul_eq_union` / 定理 `primeFactors_mul_eq_union`

English:
theorem primeFactors_mul_eq_union
  given: [DecidableEq M] (ha : a != 0) (hb : b != 0)
  proof: by
  ext p
  simp [mem_normalizedFactors_iff', mem_primeFactors, ha, hb]

中文:
定理 primeFactors_mul_eq_union
  条件: [DecidableEq M] (ha : a != 0) (hb : b != 0)
  证明: by
  ext p
  simp [mem_normalizedFactors_iff', mem_primeFactors, ha, hb]

Depends on / 依赖: mem_normalizedFactors_iff, mem_primeFactors
-/
theorem primeFactors_mul_eq_union [DecidableEq M] (ha : a != 0) (hb : b != 0) :
    primeFactors (a * b) = primeFactors a union primeFactors b := by
  ext p
  simp [mem_normalizedFactors_iff', mem_primeFactors, ha, hb]

/--
theorem `disjoint_primeFactors` / 定理 `disjoint_primeFactors`

English:
theorem disjoint_primeFactors
  given: (hc : IsRelPrime a b)
  proof: by
  classical
  exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)

中文:
定理 disjoint_primeFactors
  条件: (hc : IsRelPrime a b)
  证明: by
  classical
  exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)

Depends on / 依赖: Multiset, Multiset.disjoint_toFinset.mpr, classical, disjoint_normalizedFactors, disjoint_toFinset
-/
theorem disjoint_primeFactors (hc : IsRelPrime a b) :
    Disjoint (primeFactors a) (primeFactors b) := by
  classical
  exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)

/--
theorem `primeFactors_mul_eq_disjUnion` / 定理 `primeFactors_mul_eq_disjUnion`

English:
theorem primeFactors_mul_eq_disjUnion
  given: (hc : IsRelPrime a b)
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · rw [isRelPrime_zero_left] at hc
    simp only [zero_mul, primeFactors_zero, Finset.empty_disjUnion, primeFactors_of_isUnit hc]
  obtain rfl | hb := eq_or_ne b 0
  · rw [isRelPrime_zero_right] at hc
    simp only [mul_zero, primeFactors_zero, primeFactors_of_i

中文:
定理 primeFactors_mul_eq_disjUnion
  条件: (hc : IsRelPrime a b)
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · rw [isRelPrime_zero_left] at hc
    simp only [zero_mul, primeFactors_zero, Finset.empty_disjUnion, primeFactors_of_isUnit hc]
  obtain rfl | hb := eq_or_ne b 0
  · rw [isRelPrime_zero_right] at hc
    simp only [mul_zero, primeFactors_zero, primeFactors_of_i

Depends on / 依赖: Finset, Finset.disjUnion_empty, Finset.disjUnion_eq_union, Finset.empty_disjUnion, classical, disjUnion_empty, disjUnion_eq_union, empty_disjUnion, eq_or_ne, isRelPrime_zero_left, isRelPrime_zero_right, mul_zero, primeFactors_mul_eq_union, primeFactors_of_isUnit, primeFactors_zero, zero_mul
-/
theorem primeFactors_mul_eq_disjUnion (hc : IsRelPrime a b) :
    primeFactors (a * b) =
      (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc) := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [isRelPrime_zero_left] at hc
    simp only [zero_mul, primeFactors_zero, Finset.empty_disjUnion, primeFactors_of_isUnit hc]
  obtain rfl | hb := eq_or_ne b 0
  · rw [isRelPrime_zero_right] at hc
    simp only [mul_zero, primeFactors_zero, primeFactors_of_isUnit hc, Finset.disjUnion_empty]
  classical
  rw [Finset.disjUnion_eq_union]; rw [primeFactors_mul_eq_union ha hb]

/--
Definition of `radical` / `radical` 的定义

English:
definition radical
  signature: (a : M)
  body: (primeFactors a).prod id

中文:
定义 radical
  签名: (a : M)
  定义体: (primeFactors a).prod id

Depends on / 依赖: primeFactors
-/
def radical (a : M) : M :=
  (primeFactors a).prod id

/--
theorem `radical_zero` / 定理 `radical_zero`

English:
theorem radical_zero
  statement: radical (0 : M) = 1
  proof: by simp [radical]

中文:
定理 radical_zero
  结论: radical (0 : M) = 1
  证明: by simp [radical]
-/
@[simp] theorem radical_zero : radical (0 : M) = 1 := by simp [radical]
/--
theorem `radical_one` / 定理 `radical_one`

English:
theorem radical_one
  statement: radical (1 : M) = 1
  proof: by simp [radical]

中文:
定理 radical_one
  结论: radical (1 : M) = 1
  证明: by simp [radical]
-/
@[simp] theorem radical_one : radical (1 : M) = 1 := by simp [radical]
/--
theorem `radical_eq_of_associated` / 定理 `radical_eq_of_associated`

English:
theorem radical_eq_of_associated
  given: (h : Associated a b)
  statement: radical a = radical b
  proof: by
  rw [radical]; rw [radical]; rw [Associated.primeFactors_eq h]

中文:
定理 radical_eq_of_associated
  条件: (h : Associated a b)
  结论: radical a = radical b
  证明: by
  rw [radical]; rw [radical]; rw [Associated.primeFactors_eq h]

Depends on / 依赖: Associated, Associated.primeFactors_eq, primeFactors_eq, radical
-/
theorem radical_eq_of_associated (h : Associated a b) : radical a = radical b := by
  rw [radical]; rw [radical]; rw [Associated.primeFactors_eq h]

/--
lemma `radical_associated` / 引理 `radical_associated`

English:
lemma radical_associated
  given: (ha : IsRadical a) (ha' : a != 0)
  proof: by
  rw [radical]; rw [← Finset.prod_val]; rw [primeFactors_val_eq_normalizedFactors ha]
  exact prod_normalizedFactors ha'

中文:
引理 radical_associated
  条件: (ha : IsRadical a) (ha' : a != 0)
  证明: by
  rw [radical]; rw [← Finset.prod_val]; rw [primeFactors_val_eq_normalizedFactors ha]
  exact prod_normalizedFactors ha'

Depends on / 依赖: Finset, Finset.prod_val, primeFactors_val_eq_normalizedFactors, prod_normalizedFactors, prod_val, radical
-/
lemma radical_associated (ha : IsRadical a) (ha' : a != 0) :
    Associated (radical a) a := by
  rw [radical]; rw [← Finset.prod_val]; rw [primeFactors_val_eq_normalizedFactors ha]
  exact prod_normalizedFactors ha'

/--
lemma `_root_.IsRadical.dvd_radical` / 引理 `_root_.IsRadical.dvd_radical`

English:
lemma _root_.IsRadical.dvd_radical
  given: (ha : IsRadical a) (ha' : a != 0)
  statement: a ∣ radical a
  proof: (radical_associated ha ha').dvd'

中文:
引理 _root_.IsRadical.dvd_radical
  条件: (ha : IsRadical a) (ha' : a != 0)
  结论: a ∣ radical a
  证明: (radical_associated ha ha').dvd'

Depends on / 依赖: radical_associated
-/
lemma _root_.IsRadical.dvd_radical (ha : IsRadical a) (ha' : a != 0) : a ∣ radical a :=
  (radical_associated ha ha').dvd'

/--
theorem `radical_of_isUnit` / 定理 `radical_of_isUnit`

English:
theorem radical_of_isUnit
  given: (h : IsUnit a)
  statement: radical a = 1
  proof: (radical_eq_of_associated (associated_one_iff_isUnit.mpr h)).trans radical_one

中文:
定理 radical_of_isUnit
  条件: (h : IsUnit a)
  结论: radical a = 1
  证明: (radical_eq_of_associated (associated_one_iff_isUnit.mpr h)).trans radical_one

Depends on / 依赖: associated_one_iff_isUnit, associated_one_iff_isUnit.mpr, radical_eq_of_associated, radical_one
-/
theorem radical_of_isUnit (h : IsUnit a) : radical a = 1 :=
  (radical_eq_of_associated (associated_one_iff_isUnit.mpr h)).trans radical_one

/--
theorem `radical_mul_of_isUnit_left` / 定理 `radical_mul_of_isUnit_left`

English:
theorem radical_mul_of_isUnit_left
  given: (h : IsUnit u)
  statement: radical (u * a) = radical a
  proof: radical_eq_of_associated (associated_unit_mul_left _ _ h)

中文:
定理 radical_mul_of_isUnit_left
  条件: (h : IsUnit u)
  结论: radical (u * a) = radical a
  证明: radical_eq_of_associated (associated_unit_mul_left _ _ h)

Depends on / 依赖: associated_unit_mul_left, radical_eq_of_associated
-/
theorem radical_mul_of_isUnit_left (h : IsUnit u) : radical (u * a) = radical a :=
  radical_eq_of_associated (associated_unit_mul_left _ _ h)

/--
theorem `radical_mul_of_isUnit_right` / 定理 `radical_mul_of_isUnit_right`

English:
theorem radical_mul_of_isUnit_right
  given: (h : IsUnit u)
  statement: radical (a * u) = radical a
  proof: radical_eq_of_associated (associated_mul_unit_left _ _ h)

中文:
定理 radical_mul_of_isUnit_right
  条件: (h : IsUnit u)
  结论: radical (a * u) = radical a
  证明: radical_eq_of_associated (associated_mul_unit_left _ _ h)

Depends on / 依赖: associated_mul_unit_left, radical_eq_of_associated
-/
theorem radical_mul_of_isUnit_right (h : IsUnit u) : radical (a * u) = radical a :=
  radical_eq_of_associated (associated_mul_unit_left _ _ h)

/--
theorem `radical_pow` / 定理 `radical_pow`

English:
theorem radical_pow
  given: (a : M) {n : Nat} (hn : n != 0)
  statement: radical (a ^ n) = radical a
  proof: by
  simp_rw [radical, primeFactors_pow a hn]

中文:
定理 radical_pow
  条件: (a : M) {n : 自然数} (hn : n != 0)
  结论: radical (a ^ n) = radical a
  证明: by
  simp_rw [radical, primeFactors_pow a hn]

Depends on / 依赖: primeFactors_pow, radical, simp_rw
-/
theorem radical_pow (a : M) {n : Nat} (hn : n != 0) : radical (a ^ n) = radical a := by
  simp_rw [radical, primeFactors_pow a hn]

/--
theorem `radical_pow_dvd` / 定理 `radical_pow_dvd`

English:
theorem radical_pow_dvd
  given: {n : Nat}
  statement: radical (a ^ n) ∣ radical a
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [radical_pow _ hn]

中文:
定理 radical_pow_dvd
  条件: {n : 自然数}
  结论: radical (a ^ n) ∣ radical a
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [radical_pow _ hn]

Depends on / 依赖: eq_or_ne, radical_pow
-/
theorem radical_pow_dvd {n : Nat} : radical (a ^ n) ∣ radical a := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [radical_pow _ hn]

/--
theorem `radical_dvd_self` / 定理 `radical_dvd_self`

English:
theorem radical_dvd_self
  statement: radical a ∣ a
  proof: by
  classical
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (prod_normalizedFactors ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors]; rw [Multiset.toFinset_val]
    apply Multiset.dedup_le

中文:
定理 radical_dvd_self
  结论: radical a ∣ a
  证明: by
  classical
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (prod_normalizedFactors ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors]; rw [Multiset.toFinset_val]
    apply Multiset.dedup_le

Depends on / 依赖: Finset, Finset.prod_val, Multiset, Multiset.dedup_le, Multiset.prod_dvd_prod_of_le, Multiset.toFinset_val, classical, dedup_le, dvd_iff_dvd_right, dvd_zero, primeFactors, prod_dvd_prod_of_le, prod_normalizedFactors, prod_val, radical, toFinset_val
-/
theorem radical_dvd_self : radical a ∣ a := by
  classical
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (prod_normalizedFactors ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors]; rw [Multiset.toFinset_val]
    apply Multiset.dedup_le

/--
theorem `radical_of_prime` / 定理 `radical_of_prime`

English:
theorem radical_of_prime
  given: (ha : Prime a)
  statement: radical a = normalize a
  proof: by
  rw [radical]; rw [primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]

中文:
定理 radical_of_prime
  条件: (ha : Prime a)
  结论: radical a = normalize a
  证明: by
  rw [radical]; rw [primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]

Depends on / 依赖: Finset, Finset.prod_singleton, Multiset, Multiset.toFinset_singleton, ha.irreducible, irreducible, normalizedFactors_irreducible, primeFactors, prod_singleton, radical, toFinset_singleton
-/
theorem radical_of_prime (ha : Prime a) : radical a = normalize a := by
  rw [radical]; rw [primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]

/--
theorem `radical_pow_of_prime` / 定理 `radical_pow_of_prime`

English:
theorem radical_pow_of_prime
  given: (ha : Prime a) {n : Nat} (hn : n != 0)
  proof: by
  rw [radical_pow a hn]
  exact radical_of_prime ha

中文:
定理 radical_pow_of_prime
  条件: (ha : Prime a) {n : 自然数} (hn : n != 0)
  证明: by
  rw [radical_pow a hn]
  exact radical_of_prime ha

Depends on / 依赖: radical_of_prime, radical_pow
-/
theorem radical_pow_of_prime (ha : Prime a) {n : Nat} (hn : n != 0) :
    radical (a ^ n) = normalize a := by
  rw [radical_pow a hn]
  exact radical_of_prime ha

/--
theorem `radical_ne_zero` / 定理 `radical_ne_zero`

English:
theorem radical_ne_zero
  given: [Nontrivial M]
  statement: radical a != 0
  proof: by
  rw [radical]; rw [← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_notMem_normalizedFactors _

中文:
定理 radical_ne_zero
  条件: [Nontrivial M]
  结论: radical a != 0
  证明: by
  rw [radical]; rw [← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_notMem_normalizedFactors _
-/
@[simp] theorem radical_ne_zero [Nontrivial M] : radical a != 0 := by
  rw [radical]; rw [← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_notMem_normalizedFactors _

/--
lemma `dvd_radical_iff_of_irreducible` / 引理 `dvd_radical_iff_of_irreducible`

English:
lemma dvd_radical_iff_of_irreducible
  given: (ha : Irreducible a) (hb : b != 0)
  proof: by
  constructor
  · intro ha
    exact ha.trans radical_dvd_self
  · intro ha'
    obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd hb ha ha'
    exact hc'.dvd.trans (Finset.dvd_prod_of_mem _ (by simpa [mem_primeFactors] using hc))

中文:
引理 dvd_radical_iff_of_irreducible
  条件: (ha : Irreducible a) (hb : b != 0)
  证明: by
  constructor
  · intro ha
    exact ha.trans radical_dvd_self
  · intro ha'
    obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd hb ha ha'
    exact hc'.dvd.trans (Finset.dvd_prod_of_mem _ (by simpa [mem_primeFactors] using hc))

Depends on / 依赖: Finset, Finset.dvd_prod_of_mem, dvd.trans, dvd_prod_of_mem, exists_mem_normalizedFactors_of_dvd, ha.trans, mem_primeFactors, radical_dvd_self
-/
lemma dvd_radical_iff_of_irreducible (ha : Irreducible a) (hb : b != 0) :
    a ∣ radical b ↔ a ∣ b := by
  constructor
  · intro ha
    exact ha.trans radical_dvd_self
  · intro ha'
    obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd hb ha ha'
    exact hc'.dvd.trans (Finset.dvd_prod_of_mem _ (by simpa [mem_primeFactors] using hc))

/--
lemma `isRadical_radical` / 引理 `isRadical_radical`

English:
lemma isRadical_radical
  statement: IsRadical (radical a)
  proof: by
  intro n p ha
  rw [radical]
  apply Finset.prod_dvd_of_isRelPrime
  · exact pairwise_primeFactors_isRelPrime
  intro i hi
  simp only [mem_primeFactors] at hi
  have : i ∣ radical a := by
    rw [dvd_radical_iff_of_irreducible]
    · exact dvd_of_mem_normalizedFactors hi
    · exact irreducible

中文:
引理 isRadical_radical
  结论: IsRadical (radical a)
  证明: by
  intro n p ha
  rw [radical]
  apply Finset.prod_dvd_of_isRelPrime
  · exact pairwise_primeFactors_isRelPrime
  intro i hi
  simp only [mem_primeFactors] at hi
  have : i ∣ radical a := by
    rw [dvd_radical_iff_of_irreducible]
    · exact dvd_of_mem_normalizedFactors hi
    · exact irreducible

Depends on / 依赖: Finset, Finset.prod_dvd_of_isRelPrime, Multiset, Multiset.notMem_zero, dvd_of_mem_normalizedFactors, dvd_radical_iff_of_irreducible, irreducible_of_normalized_factor, isRadical, mem_primeFactors, normalizedFactors_zero, notMem_zero, pairwise_primeFactors_isRelPrime, prime_of_normalized_factor, prod_dvd_of_isRelPrime, radical, this.trans
-/
lemma isRadical_radical : IsRadical (radical a) := by
  intro n p ha
  rw [radical]
  apply Finset.prod_dvd_of_isRelPrime
  · exact pairwise_primeFactors_isRelPrime
  intro i hi
  simp only [mem_primeFactors] at hi
  have : i ∣ radical a := by
    rw [dvd_radical_iff_of_irreducible]
    · exact dvd_of_mem_normalizedFactors hi
    · exact irreducible_of_normalized_factor i hi
    · rintro rfl
      simp only [normalizedFactors_zero, Multiset.notMem_zero] at hi
  exact (prime_of_normalized_factor i hi).isRadical n p (this.trans ha)

/--
lemma `squarefree_radical` / 引理 `squarefree_radical`

English:
lemma squarefree_radical
  statement: Squarefree (radical a)
  proof: by
  nontriviality M
  exact isRadical_radical.squarefree (by simp [radical_ne_zero])

中文:
引理 squarefree_radical
  结论: Squarefree (radical a)
  证明: by
  nontriviality M
  exact isRadical_radical.squarefree (by simp [radical_ne_zero])

Depends on / 依赖: isRadical_radical, isRadical_radical.squarefree, nontriviality, radical_ne_zero, squarefree
-/
lemma squarefree_radical : Squarefree (radical a) := by
  nontriviality M
  exact isRadical_radical.squarefree (by simp [radical_ne_zero])

/--
lemma `primeFactors_radical` / 引理 `primeFactors_radical`

English:
lemma primeFactors_radical
  statement: primeFactors (radical a) = primeFactors a
  proof: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [primeFactors]
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  ext p
  simp +contextual [mem_primeFactors, mem_normalizedFactors_iff',
    dvd_radical_iff_of_irreducible, ha₀]

中文:
引理 primeFactors_radical
  结论: primeFactors (radical a) = primeFactors a
  证明: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [primeFactors]
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  ext p
  simp +contextual [mem_primeFactors, mem_normalizedFactors_iff',
    dvd_radical_iff_of_irreducible, ha₀]
-/
@[simp] lemma primeFactors_radical : primeFactors (radical a) = primeFactors a := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [primeFactors]
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  ext p
  simp +contextual [mem_primeFactors, mem_normalizedFactors_iff',
    dvd_radical_iff_of_irreducible, ha₀]

/--
lemma `radical_eq_iff_primeFactors_eq` / 引理 `radical_eq_iff_primeFactors_eq`

English:
lemma radical_eq_iff_primeFactors_eq
  proof: ⟨fun h => by rw [← primeFactors_radical, h]; exact primeFactors_radical,
    fun h => by simp [radical, h]⟩

中文:
引理 radical_eq_iff_primeFactors_eq
  证明: ⟨fun h => by rw [← primeFactors_radical, h]; exact primeFactors_radical,
    fun h => by simp [radical, h]⟩

Depends on / 依赖: primeFactors_radical, radical
-/
lemma radical_eq_iff_primeFactors_eq :
    radical a = radical b ↔ primeFactors a = primeFactors b :=
  ⟨fun h => by rw [← primeFactors_radical, h]; exact primeFactors_radical,
    fun h => by simp [radical, h]⟩

/--
theorem `radical_eq_one_iff` / 定理 `radical_eq_one_iff`

English:
theorem radical_eq_one_iff
  statement: radical a = 1 ↔ a = 0 ∨ IsUnit a
  proof: by
  refine ⟨?_, (Or.elim · (by simp +contextual) radical_of_isUnit)⟩
  intro h
  rw [or_iff_not_imp_left]
  intro ha
  have : primeFactors a = ∅ := by rw [← primeFactors_radical, h, primeFactors_one]
  rwa [primeFactors_eq_empty_iff ha] at this

@[simp]

中文:
定理 radical_eq_one_iff
  结论: radical a = 1 ↔ a = 0 ∨ IsUnit a
  证明: by
  refine ⟨?_, (Or.elim · (by simp +contextual) radical_of_isUnit)⟩
  intro h
  rw [or_iff_not_imp_left]
  intro ha
  have : primeFactors a = ∅ := by rw [← primeFactors_radical, h, primeFactors_one]
  rwa [primeFactors_eq_empty_iff ha] at this

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, Or.elim, TopCat, contextual, or_iff_not_imp_left, primeFactors, primeFactors_eq_empty_iff, primeFactors_one, primeFactors_radical, radical_of_isUnit
-/
theorem radical_eq_one_iff : radical a = 1 ↔ a = 0 ∨ IsUnit a := by
  refine ⟨?_, (Or.elim · (by simp +contextual) radical_of_isUnit)⟩
  intro h
  rw [or_iff_not_imp_left]
  intro ha
  have : primeFactors a = ∅ := by rw [← primeFactors_radical, h, primeFactors_one]
  rwa [primeFactors_eq_empty_iff ha] at this

@[simp]
/--
lemma `radical_radical` / 引理 `radical_radical`

English:
lemma radical_radical
  statement: radical (radical a) = radical a
  proof: radical_eq_iff_primeFactors_eq.mpr primeFactors_radical

中文:
引理 radical_radical
  结论: radical (radical a) = radical a
  证明: radical_eq_iff_primeFactors_eq.mpr primeFactors_radical

Depends on / 依赖: primeFactors_radical, radical_eq_iff_primeFactors_eq, radical_eq_iff_primeFactors_eq.mpr
-/
lemma radical_radical : radical (radical a) = radical a :=
  radical_eq_iff_primeFactors_eq.mpr primeFactors_radical

/--
lemma `radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors` / 引理 `radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors`

English:
lemma radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors
  proof: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  rw [dvd_iff_normalizedFactors_le_normalizedFactors radical_ne_zero radical_ne_zero]; rw [Multiset.le_iff_subset (normalizedFactors_nodup isRadical_radical)]
  simp only [Multiset.subset_iff, ← mem_primeFactors, pri

中文:
引理 radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors
  证明: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  rw [dvd_iff_normalizedFactors_le_normalizedFactors radical_ne_zero radical_ne_zero]; rw [Multiset.le_iff_subset (normalizedFactors_nodup isRadical_radical)]
  simp only [Multiset.subset_iff, ← mem_primeFactors, pri

Depends on / 依赖: Multiset, Multiset.le_iff_subset, Multiset.subset_iff, Nontrivial, dvd_iff_normalizedFactors_le_normalizedFactors, eq_or_ne, f.hom, isRadical_radical, le_iff_subset, mem_primeFactors, normalizedFactors_nodup, primeFactors_radical, radical_ne_zero, subset_iff
-/
lemma radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors :
    radical a ∣ radical b ↔ normalizedFactors a subseteq normalizedFactors b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  rw [dvd_iff_normalizedFactors_le_normalizedFactors radical_ne_zero radical_ne_zero]; rw [Multiset.le_iff_subset (normalizedFactors_nodup isRadical_radical)]
  simp only [Multiset.subset_iff, ← mem_primeFactors, primeFactors_radical]

/--
lemma `radical_dvd_radical_iff_primeFactors_subset_primeFactors` / 引理 `radical_dvd_radical_iff_primeFactors_subset_primeFactors`

English:
lemma radical_dvd_radical_iff_primeFactors_subset_primeFactors
  proof: by
  classical
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors]; rw [primeFactors]; rw [primeFactors]; rw [Multiset.toFinset_subset]

中文:
引理 radical_dvd_radical_iff_primeFactors_subset_primeFactors
  证明: by
  classical
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors]; rw [primeFactors]; rw [primeFactors]; rw [Multiset.toFinset_subset]

Depends on / 依赖: Multiset, Multiset.toFinset_subset, classical, primeFactors, radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors, toFinset_subset
-/
lemma radical_dvd_radical_iff_primeFactors_subset_primeFactors :
    radical a ∣ radical b ↔ primeFactors a subseteq primeFactors b := by
  classical
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors]; rw [primeFactors]; rw [primeFactors]; rw [Multiset.toFinset_subset]

/--
lemma `radical_dvd_radical` / 引理 `radical_dvd_radical`

English:
lemma radical_dvd_radical
  given: (h : a ∣ b) (hb₀ : b != 0)
  statement: radical a ∣ radical b
  proof: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha₀ hb₀] at h
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors]
  exact Multiset.subset_of_le h

中文:
引理 radical_dvd_radical
  条件: (h : a ∣ b) (hb₀ : b != 0)
  结论: radical a ∣ radical b
  证明: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha₀ hb₀] at h
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors]
  exact Multiset.subset_of_le h

Depends on / 依赖: Multiset, Multiset.subset_of_le, dvd_iff_normalizedFactors_le_normalizedFactors, eq_or_ne, radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors, subset_of_le
-/
lemma radical_dvd_radical (h : a ∣ b) (hb₀ : b != 0) : radical a ∣ radical b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha₀ hb₀] at h
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors]
  exact Multiset.subset_of_le h

/--
lemma `dvd_radical_iff` / 引理 `dvd_radical_iff`

English:
lemma dvd_radical_iff
  given: (ha : IsRadical a) (hb₀ : b != 0)
  statement: a ∣ radical b ↔ a ∣ b
  proof: by
  refine ⟨fun ha' => ha'.trans radical_dvd_self, fun hab => ?_⟩
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  · exact (ha.dvd_radical ha₀).trans (radical_dvd_radical hab hb₀)

中文:
引理 dvd_radical_iff
  条件: (ha : IsRadical a) (hb₀ : b != 0)
  结论: a ∣ radical b ↔ a ∣ b
  证明: by
  refine ⟨fun ha' => ha'.trans radical_dvd_self, fun hab => ?_⟩
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  · exact (ha.dvd_radical ha₀).trans (radical_dvd_radical hab hb₀)

Depends on / 依赖: dvd_radical, eq_or_ne, ha.dvd_radical, radical_dvd_radical, radical_dvd_self
-/
lemma dvd_radical_iff (ha : IsRadical a) (hb₀ : b != 0) : a ∣ radical b ↔ a ∣ b := by
  refine ⟨fun ha' => ha'.trans radical_dvd_self, fun hab => ?_⟩
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  · exact (ha.dvd_radical ha₀).trans (radical_dvd_radical hab hb₀)

/--
theorem `radical_dvd_iff_primeFactors_subset` / 定理 `radical_dvd_iff_primeFactors_subset`

English:
theorem radical_dvd_iff_primeFactors_subset
  given: (hb : b != 0)
  proof: by
  rw [← dvd_radical_iff isRadical_radical hb]; rw [radical_dvd_radical_iff_primeFactors_subset_primeFactors]

中文:
定理 radical_dvd_iff_primeFactors_subset
  条件: (hb : b != 0)
  证明: by
  rw [← dvd_radical_iff isRadical_radical hb]; rw [radical_dvd_radical_iff_primeFactors_subset_primeFactors]

Depends on / 依赖: dvd_radical_iff, isRadical_radical, radical_dvd_radical_iff_primeFactors_subset_primeFactors
-/
theorem radical_dvd_iff_primeFactors_subset (hb : b != 0) :
    radical a ∣ b ↔ primeFactors a subseteq primeFactors b := by
  rw [← dvd_radical_iff isRadical_radical hb]; rw [radical_dvd_radical_iff_primeFactors_subset_primeFactors]

/--
theorem `exists_dvd_pow_iff_radical_dvd` / 定理 `exists_dvd_pow_iff_radical_dvd`

English:
theorem exists_dvd_pow_iff_radical_dvd
  given: (ha : a != 0)
  statement: (exists n, a ∣ b ^ n) ↔ radical a ∣ b
  proof: by
  rcases eq_or_ne b 0 with (rfl | hb)
  · exact ⟨by simp, fun _ => ⟨1, by simp⟩⟩
.card, ?_⟩⟩ refine ⟨fun ⟨n, hdvd⟩ => ?_, fun h => ⟨normalizedFactors a
  · rcases eq_or_ne n 0 with (rfl | hn)
    · simp [radical_of_isUnit <| isUnit_of_dvd_one <| pow_zero b ▸ hdvd]
    grw [radical_dvd_radical hdv

中文:
定理 exists_dvd_pow_iff_radical_dvd
  条件: (ha : a != 0)
  结论: (存在 n, a ∣ b ^ n) ↔ radical a ∣ b
  证明: by
  rcases eq_or_ne b 0 with (rfl | hb)
  · exact ⟨by simp, fun _ => ⟨1, by simp⟩⟩
.card, ?_⟩⟩ refine ⟨fun ⟨n, hdvd⟩ => ?_, fun h => ⟨normalizedFactors a
  · rcases eq_or_ne n 0 with (rfl | hn)
    · simp [radical_of_isUnit <| isUnit_of_dvd_one <| pow_zero b ▸ hdvd]
    grw [radical_dvd_radical hdv

Depends on / 依赖: Multiset, Multiset.le_card_smul_iff_subset, classical, dvd_iff_normalizedFactors_le_normalizedFactors, eq_or_ne, isUnit_of_dvd_one, le_card_smul_iff_subset, normalizedFactors, normalizedFactors_pow, pow_ne_zero, pow_zero, radical_dvd_radical, radical_dvd_self, radical_of_isUnit, radical_pow
-/
theorem exists_dvd_pow_iff_radical_dvd (ha : a != 0) : (exists n, a ∣ b ^ n) ↔ radical a ∣ b := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · exact ⟨by simp, fun _ => ⟨1, by simp⟩⟩
.card, ?_⟩⟩ refine ⟨fun ⟨n, hdvd⟩ => ?_, fun h => ⟨normalizedFactors a
  · rcases eq_or_ne n 0 with (rfl | hn)
    · simp [radical_of_isUnit <| isUnit_of_dvd_one <| pow_zero b ▸ hdvd]
    grw [radical_dvd_radical hdvd <| pow_ne_zero _ hb, radical_pow b hn, radical_dvd_self]
  · classical
    rwa [dvd_iff_normalizedFactors_le_normalizedFactors ha <| pow_ne_zero _ hb,
      normalizedFactors_pow, Multiset.le_card_smul_iff_subset, ← Multiset.toFinset_subset,
      toFinset_normalizedFactors, toFinset_normalizedFactors,
      ← radical_dvd_iff_primeFactors_subset hb]

/--
theorem `exists_dvd_radical_self_pow` / 定理 `exists_dvd_radical_self_pow`

English:
theorem exists_dvd_radical_self_pow
  given: (ha : a != 0)
  statement: exists n, a ∣ radical a ^ n
  proof: by
  rw [exists_dvd_pow_iff_radical_dvd ha]

中文:
定理 exists_dvd_radical_self_pow
  条件: (ha : a != 0)
  结论: 存在 n, a ∣ radical a ^ n
  证明: by
  rw [exists_dvd_pow_iff_radical_dvd ha]

Depends on / 依赖: exists_dvd_pow_iff_radical_dvd
-/
theorem exists_dvd_radical_self_pow (ha : a != 0) : exists n, a ∣ radical a ^ n := by
  rw [exists_dvd_pow_iff_radical_dvd ha]

/--
theorem `radical_mul` / 定理 `radical_mul`

English:
theorem radical_mul
  given: (hc : IsRelPrime a b)
  proof: by
  simp_rw [radical]
  rw [primeFactors_mul_eq_disjUnion hc]; rw [Finset.prod_disjUnion (disjoint_primeFactors hc)]

中文:
定理 radical_mul
  条件: (hc : IsRelPrime a b)
  证明: by
  simp_rw [radical]
  rw [primeFactors_mul_eq_disjUnion hc]; rw [Finset.prod_disjUnion (disjoint_primeFactors hc)]

Depends on / 依赖: Finset, Finset.prod_disjUnion, disjoint_primeFactors, primeFactors_mul_eq_disjUnion, prod_disjUnion, radical, simp_rw
-/
theorem radical_mul (hc : IsRelPrime a b) :
    radical (a * b) = radical a * radical b := by
  simp_rw [radical]
  rw [primeFactors_mul_eq_disjUnion hc]; rw [Finset.prod_disjUnion (disjoint_primeFactors hc)]

/--
theorem `radical_prod` / 定理 `radical_prod`

English:
theorem radical_prod
  statement: {ι : Type*} {f : ι -> M} (s : Finset ι)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih =>
    simp only [Finset.prod_cons]
    rw [Finset.coe_cons]; rw [Set.pairwise_insert_of_symm_of_notMem <| by simpa] at h
    rw [radical_mul]; rw [ih h.1]
    exact IsRelPrime.prod_right h.2

中文:
定理 radical_prod
  结论: {ι : 类型} {f : ι -> M} (s : Finset ι)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih =>
    simp only [Finset.prod_cons]
    rw [Finset.coe_cons]; rw [Set.pairwise_insert_of_symm_of_notMem <| by simpa] at h
    rw [radical_mul]; rw [ih h.1]
    exact IsRelPrime.prod_right h.2

Depends on / 依赖: Finset, Finset.coe_cons, Finset.cons_induction, Finset.prod_cons, IsRelPrime, IsRelPrime.prod_right, Set.pairwise_insert_of_symm_of_notMem, coe_cons, cons_induction, pairwise_insert_of_symm_of_notMem, prod_cons, prod_right, radical_mul
-/
theorem radical_prod {ι : Type*} {f : ι -> M} (s : Finset ι)
    (h : Set.Pairwise (s : Set ι) (Function.onFun IsRelPrime f)) :
    radical (∏ i in s, f i) = ∏ i in s, radical (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih =>
    simp only [Finset.prod_cons]
    rw [Finset.coe_cons]; rw [Set.pairwise_insert_of_symm_of_notMem <| by simpa] at h
    rw [radical_mul]; rw [ih h.1]
    exact IsRelPrime.prod_right h.2

/--
theorem `radical_mul_dvd` / 定理 `radical_mul_dvd`

English:
theorem radical_mul_dvd
  statement: radical (a * b) ∣ radical a * radical b
  proof: by
  classical
  obtain rfl | ha := eq_or_ne a 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  nontriviality M
  simp [radical_dvd_iff_primeFactors_subset, primeFactors_mul_eq_union,
    primeFactors_mul_eq_union ha hb, primeFactors_radical]

中文:
定理 radical_mul_dvd
  结论: radical (a * b) ∣ radical a * radical b
  证明: by
  classical
  obtain rfl | ha := eq_or_ne a 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  nontriviality M
  simp [radical_dvd_iff_primeFactors_subset, primeFactors_mul_eq_union,
    primeFactors_mul_eq_union ha hb, primeFactors_radical]

Depends on / 依赖: classical, eq_or_ne, nontriviality, primeFactors_mul_eq_union, primeFactors_radical, radical_dvd_iff_primeFactors_subset
-/
theorem radical_mul_dvd : radical (a * b) ∣ radical a * radical b := by
  classical
  obtain rfl | ha := eq_or_ne a 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  nontriviality M
  simp [radical_dvd_iff_primeFactors_subset, primeFactors_mul_eq_union,
    primeFactors_mul_eq_union ha hb, primeFactors_radical]

/--
theorem `radical_prod_dvd` / 定理 `radical_prod_dvd`

English:
theorem radical_prod_dvd
  given: {ι : Type*} {s : Finset ι} {f : ι -> M}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s h ih =>
    simp only [Finset.prod_cons]
    exact radical_mul_dvd.trans (mul_dvd_mul_left _ ih)

中文:
定理 radical_prod_dvd
  条件: {ι : 类型} {s : Finset ι} {f : ι -> M}
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s h ih =>
    simp only [Finset.prod_cons]
    exact radical_mul_dvd.trans (mul_dvd_mul_left _ ih)

Depends on / 依赖: Finset, Finset.cons_induction, Finset.prod_cons, cons_induction, mul_dvd_mul_left, prod_cons, radical_mul_dvd, radical_mul_dvd.trans
-/
theorem radical_prod_dvd {ι : Type*} {s : Finset ι} {f : ι -> M} :
    radical (∏ i in s, f i) ∣ ∏ i in s, radical (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s h ih =>
    simp only [Finset.prod_cons]
    exact radical_mul_dvd.trans (mul_dvd_mul_left _ ih)

end UniqueFactorizationMonoid

open UniqueFactorizationMonoid

/-! Theorems for UFDs -/
namespace UniqueFactorizationDomain

variable {R : Type*} [CommRing R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R] {a b : R}

@[simp]
/--
theorem `radical_neg` / 定理 `radical_neg`

English:
theorem radical_neg
  statement: radical (-a) = radical a
  proof: radical_eq_of_associated Associated.rfl.neg_left

中文:
定理 radical_neg
  结论: radical (-a) = radical a
  证明: radical_eq_of_associated Associated.rfl.neg_left

Depends on / 依赖: Associated, Associated.rfl.neg_left, neg_left, radical_eq_of_associated
-/
theorem radical_neg : radical (-a) = radical a :=
  radical_eq_of_associated Associated.rfl.neg_left

/--
theorem `radical_neg_one` / 定理 `radical_neg_one`

English:
theorem radical_neg_one
  statement: radical (-1 : R) = 1
  proof: by simp

中文:
定理 radical_neg_one
  结论: radical (-1 : R) = 1
  证明: by simp
-/
theorem radical_neg_one : radical (-1 : R) = 1 := by simp

end UniqueFactorizationDomain

open UniqueFactorizationDomain
namespace EuclideanDomain

variable {E : Type*} [EuclideanDomain E] [NormalizationMonoid E] [UniqueFactorizationMonoid E]
  {a b u x : E}

/--
Definition of `divRadical` / `divRadical` 的定义

English:
definition divRadical
  signature: (a : E)
  body: a / radical a

中文:
定义 divRadical
  签名: (a : E)
  定义体: a / radical a

Depends on / 依赖: radical
-/
def divRadical (a : E) : E := a / radical a

/--
theorem `radical_mul_divRadical` / 定理 `radical_mul_divRadical`

English:
theorem radical_mul_divRadical
  statement: radical a * divRadical a = a
  proof: by
  rw [divRadical]; rw [← EuclideanDomain.mul_div_assoc _ radical_dvd_self]; rw [mul_div_cancel_left₀ _ radical_ne_zero]

中文:
定理 radical_mul_divRadical
  结论: radical a * divRadical a = a
  证明: by
  rw [divRadical]; rw [← EuclideanDomain.mul_div_assoc _ radical_dvd_self]; rw [mul_div_cancel_left₀ _ radical_ne_zero]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_assoc, divRadical, mul_div_assoc, radical_dvd_self, radical_ne_zero
-/
theorem radical_mul_divRadical : radical a * divRadical a = a := by
  rw [divRadical]; rw [← EuclideanDomain.mul_div_assoc _ radical_dvd_self]; rw [mul_div_cancel_left₀ _ radical_ne_zero]

/--
theorem `divRadical_mul_radical` / 定理 `divRadical_mul_radical`

English:
theorem divRadical_mul_radical
  statement: divRadical a * radical a = a
  proof: by
  rw [mul_comm]
  exact radical_mul_divRadical

中文:
定理 divRadical_mul_radical
  结论: divRadical a * radical a = a
  证明: by
  rw [mul_comm]
  exact radical_mul_divRadical

Depends on / 依赖: mul_comm, radical_mul_divRadical
-/
theorem divRadical_mul_radical : divRadical a * radical a = a := by
  rw [mul_comm]
  exact radical_mul_divRadical

/--
theorem `divRadical_ne_zero` / 定理 `divRadical_ne_zero`

English:
theorem divRadical_ne_zero
  given: (ha : a != 0)
  statement: divRadical a != 0
  proof: by
  rw [← radical_mul_divRadical (a := a)] at ha
  exact right_ne_zero_of_mul ha

中文:
定理 divRadical_ne_zero
  条件: (ha : a != 0)
  结论: divRadical a != 0
  证明: by
  rw [← radical_mul_divRadical (a := a)] at ha
  exact right_ne_zero_of_mul ha

Depends on / 依赖: radical_mul_divRadical, right_ne_zero_of_mul
-/
theorem divRadical_ne_zero (ha : a != 0) : divRadical a != 0 := by
  rw [← radical_mul_divRadical (a := a)] at ha
  exact right_ne_zero_of_mul ha

/--
theorem `divRadical_isUnit` / 定理 `divRadical_isUnit`

English:
theorem divRadical_isUnit
  given: (hu : IsUnit u)
  statement: IsUnit (divRadical u)
  proof: by
  rwa [divRadical, radical_of_isUnit hu, EuclideanDomain.div_one]

中文:
定理 divRadical_isUnit
  条件: (hu : IsUnit u)
  结论: IsUnit (divRadical u)
  证明: by
  rwa [divRadical, radical_of_isUnit hu, EuclideanDomain.div_one]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.div_one, divRadical, div_one, radical_of_isUnit
-/
theorem divRadical_isUnit (hu : IsUnit u) : IsUnit (divRadical u) := by
  rwa [divRadical, radical_of_isUnit hu, EuclideanDomain.div_one]

/--
theorem `eq_divRadical` / 定理 `eq_divRadical`

English:
theorem eq_divRadical
  given: (h : radical a * x = a)
  statement: x = divRadical a
  proof: by
  apply EuclideanDomain.eq_div_of_mul_eq_left radical_ne_zero
  rwa [mul_comm]

中文:
定理 eq_divRadical
  条件: (h : radical a * x = a)
  结论: x = divRadical a
  证明: by
  apply EuclideanDomain.eq_div_of_mul_eq_left radical_ne_zero
  rwa [mul_comm]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.eq_div_of_mul_eq_left, eq_div_of_mul_eq_left, mul_comm, radical_ne_zero
-/
theorem eq_divRadical (h : radical a * x = a) : x = divRadical a := by
  apply EuclideanDomain.eq_div_of_mul_eq_left radical_ne_zero
  rwa [mul_comm]

/--
theorem `divRadical_mul` / 定理 `divRadical_mul`

English:
theorem divRadical_mul
  given: (hab : IsCoprime a b)
  proof: by
  symm; apply eq_divRadical
  rw [UniqueFactorizationMonoid.radical_mul hab.isRelPrime]
  rw [mul_mul_mul_comm]; rw [radical_mul_divRadical]; rw [radical_mul_divRadical]

中文:
定理 divRadical_mul
  条件: (hab : IsCoprime a b)
  证明: by
  symm; apply eq_divRadical
  rw [UniqueFactorizationMonoid.radical_mul hab.isRelPrime]
  rw [mul_mul_mul_comm]; rw [radical_mul_divRadical]; rw [radical_mul_divRadical]

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.radical_mul, eq_divRadical, hab.isRelPrime, isRelPrime, mul_mul_mul_comm, radical_mul, radical_mul_divRadical
-/
theorem divRadical_mul (hab : IsCoprime a b) :
    divRadical (a * b) = divRadical a * divRadical b := by
  symm; apply eq_divRadical
  rw [UniqueFactorizationMonoid.radical_mul hab.isRelPrime]
  rw [mul_mul_mul_comm]; rw [radical_mul_divRadical]; rw [radical_mul_divRadical]

/--
theorem `divRadical_dvd_self` / 定理 `divRadical_dvd_self`

English:
theorem divRadical_dvd_self
  given: (a : E)
  statement: divRadical a ∣ a
  proof: ⟨radical a, divRadical_mul_radical.symm⟩

中文:
定理 divRadical_dvd_self
  条件: (a : E)
  结论: divRadical a ∣ a
  证明: ⟨radical a, divRadical_mul_radical.symm⟩

Depends on / 依赖: divRadical_mul_radical, divRadical_mul_radical.symm, radical
-/
theorem divRadical_dvd_self (a : E) : divRadical a ∣ a :=
  ⟨radical a, divRadical_mul_radical.symm⟩

/--
theorem `_root_.IsCoprime.divRadical` / 定理 `_root_.IsCoprime.divRadical`

English:
theorem _root_.IsCoprime.divRadical
  given: {a b : E} (h : IsCoprime a b)
  proof: by
  rw [← radical_mul_divRadical (a := a)] at h
  rw [← radical_mul_divRadical (a := b)] at h
  exact h.of_mul_left_right.of_mul_right_right

中文:
定理 _root_.IsCoprime.divRadical
  条件: {a b : E} (h : IsCoprime a b)
  证明: by
  rw [← radical_mul_divRadical (a := a)] at h
  rw [← radical_mul_divRadical (a := b)] at h
  exact h.of_mul_left_right.of_mul_right_right

Depends on / 依赖: h.of_mul_left_right.of_mul_right_right, of_mul_left_right, of_mul_right_right, radical_mul_divRadical
-/
theorem _root_.IsCoprime.divRadical {a b : E} (h : IsCoprime a b) :
    IsCoprime (divRadical a) (divRadical b) := by
  rw [← radical_mul_divRadical (a := a)] at h
  rw [← radical_mul_divRadical (a := b)] at h
  exact h.of_mul_left_right.of_mul_right_right

end EuclideanDomain
