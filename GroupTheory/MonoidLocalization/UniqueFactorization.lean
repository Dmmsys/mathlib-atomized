/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Junyan Xu
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # Localization preserves unique factorization

## Main results

* `UniqueFactorizationMonoid.of_isLocalization`: a localization of a unique factorization monoid
  is still a unique factorization monoid. In particular, a localization of a UFD is a UFD provided
  it is nontrivial.
-/

@[expose] public section

variable {M N : Type*}

namespace Submonoid.LocalizationMap

variable [CommMonoidWithZero M] [CommMonoidWithZero N] {S : Submonoid M}

/--
theorem `map_prime` / 定理 `map_prime`

English:
theorem map_prime
  statement: (f : S.LocalizationMap N) {m : M} (prime : Prime m)
  proof: by
  refine ⟨n0, nu, fun n₁ n₂ dvd => ?_⟩
  have ⟨⟨m₁, s₁⟩, eq₁⟩ := f.surj n₁
  have ⟨⟨m₂, s₂⟩, eq₂⟩ := f.surj n₂
  have := (f.map_units (s₁ * s₂)).dvd_mul_right.mpr dvd
  rw [Submonoid.mul_def]; rw [map_mul]; rw [mul_mul_mul_comm]; rw [eq₁]; rw [eq₂]; rw [← map_mul]; rw [f.map_dvd_map] at this
  have ⟨s, hs, dvd⟩ := this
  rw [← mul_assoc] at dvd
  obtain dvd | dvd := prime.dvd_or_dvd dvd
  all_goals have := map_dvd f dvd
  · rw [map_mul, (f.map_units ⟨s, hs⟩).dvd_mul_left, ← eq₁, (f.map_units s₁).dvd_mul_right] at this
    exact .inl this
  · rw [← eq₂, (f.map_units s₂).dvd_mul_right] at this; exact .inr this

中文:
定理 map_prime
  结论: (f : S.Localization映射 N) {m : M} (prime : 素 m)
  证明: by
  refine ⟨n0, nu, fun n₁ n₂ dvd => ?_⟩
  have ⟨⟨m₁, s₁⟩, eq₁⟩ := f.surj n₁
  have ⟨⟨m₂, s₂⟩, eq₂⟩ := f.surj n₂
  have := (f.map_units (s₁ * s₂)).dvd_mul_right.mpr dvd
  rw [Submonoid.mul_def]; rw [map_mul]; rw [mul_mul_mul_comm]; rw [eq₁]; rw [eq₂]; rw [← map_mul]; rw [f.map_dvd_map] at this
  have ⟨s, hs, dvd⟩ := this
  rw [← mul_assoc] at dvd
  obtain dvd | dvd := prime.dvd_or_dvd dvd
  all_goals have := map_dvd f dvd
  · rw [map_mul, (f.map_units ⟨s, hs⟩).dvd_mul_left, ← eq₁, (f.map_units s₁).dvd_mul_right] at this
    exact .inl this
  · rw [← eq₂, (f.map_units s₂).dvd_mul_right] at this; exact .inr this

Depends on / 依赖: Submonoid, Submonoid.mul_def, all_goals, dvd_mul_left, dvd_mul_right, dvd_mul_right.mpr, dvd_or_dvd, f.map_dvd_map, f.map_units, f.surj, map_dvd, map_dvd_map, map_mul, map_units, mul_assoc, mul_def, mul_mul_mul_comm, prime.dvd_or_dvd
-/
theorem map_prime (f : S.LocalizationMap N) {m : M} (prime : Prime m)
    (n0 : f m != 0) (nu : ¬ IsUnit (f m)) : Prime (f m) := by
  refine ⟨n0, nu, fun n₁ n₂ dvd => ?_⟩
  have ⟨⟨m₁, s₁⟩, eq₁⟩ := f.surj n₁
  have ⟨⟨m₂, s₂⟩, eq₂⟩ := f.surj n₂
  have := (f.map_units (s₁ * s₂)).dvd_mul_right.mpr dvd
  rw [Submonoid.mul_def]; rw [map_mul]; rw [mul_mul_mul_comm]; rw [eq₁]; rw [eq₂]; rw [← map_mul]; rw [f.map_dvd_map] at this
  have ⟨s, hs, dvd⟩ := this
  rw [← mul_assoc] at dvd
  obtain dvd | dvd := prime.dvd_or_dvd dvd
  all_goals have := map_dvd f dvd
  · rw [map_mul, (f.map_units ⟨s, hs⟩).dvd_mul_left, ← eq₁, (f.map_units s₁).dvd_mul_right] at this
    exact .inl this
  · rw [← eq₂, (f.map_units s₂).dvd_mul_right] at this; exact .inr this

/--
theorem `eq_isUnit_map_mul_irreducible_of_irreducible_map` / 定理 `eq_isUnit_map_mul_irreducible_of_irreducible_map`

English:
theorem eq_isUnit_map_mul_irreducible_of_irreducible_map
  statement: [WfDvdMonoid M] (f : S.LocalizationMap N)
  proof: by
  induction m using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hm.ne_zero f.map_zero).elim
  | unit u hu => exact (hm.not_isUnit (hu.map f)).elim
  | mul a i ha0 hi ha =>
    rw [map_mul]; rw [irreducible_mul_iff] at hm
    obtain hia | hai := hm
    · exact ⟨a, i, hia.2, hi, mul_comm ..⟩
    · obtain ⟨u, m', hu, hm', rfl⟩ := ha hai.1
      exact ⟨u * i, m', by simpa using hu.mul hai.2, hm', by ac_rfl⟩

中文:
定理 eq_isUnit_map_mul_irreducible_of_irreducible_map
  结论: [WfDvdMonoid M] (f : S.Localization映射 N)
  证明: by
  induction m using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hm.ne_zero f.map_zero).elim
  | unit u hu => exact (hm.not_isUnit (hu.map f)).elim
  | mul a i ha0 hi ha =>
    rw [map_mul]; rw [irreducible_mul_iff] at hm
    obtain hia | hai := hm
    · exact ⟨a, i, hia.2, hi, mul_comm ..⟩
    · obtain ⟨u, m', hu, hm', rfl⟩ := ha hai.1
      exact ⟨u * i, m', by simpa using hu.mul hai.2, hm', by ac_rfl⟩

Depends on / 依赖: WfDvdMonoid, WfDvdMonoid.induction_on_irreducible, f.map_zero, hm.ne_zero, hm.not_isUnit, hu.map, hu.mul, induction_on_irreducible, irreducible_mul_iff, map_mul, map_zero, mul_comm, ne_zero, not_isUnit
-/
theorem eq_isUnit_map_mul_irreducible_of_irreducible_map [WfDvdMonoid M] (f : S.LocalizationMap N)
    {m : M} (hm : Irreducible (f m)) : exists u m' : M, IsUnit (f u) ∧ Irreducible m' ∧ m = u * m' := by
  induction m using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hm.ne_zero f.map_zero).elim
  | unit u hu => exact (hm.not_isUnit (hu.map f)).elim
  | mul a i ha0 hi ha =>
    rw [map_mul]; rw [irreducible_mul_iff] at hm
    obtain hia | hai := hm
    · exact ⟨a, i, hia.2, hi, mul_comm ..⟩
    · obtain ⟨u, m', hu, hm', rfl⟩ := ha hai.1
      exact ⟨u * i, m', by simpa using hu.mul hai.2, hm', by ac_rfl⟩

open UniqueFactorizationMonoid in
/--
theorem `uniqueFactorizationMonoid` / 定理 `uniqueFactorizationMonoid`

English:
theorem uniqueFactorizationMonoid
  statement: (f : S.LocalizationMap N)
  proof: have := f.isCancelMulZero
  .of_exists_prime_factors fun n hn => by
    classical
    have ⟨⟨m, s⟩, eq⟩ := f.surj n
    use ((factors m).map f).filter (¬ IsUnit ·)
    rw [Ne]; rw [← (f.map_units s).mul_left_eq_zero]; rw [eq] at hn
    refine ⟨fun x hx => ?_, .trans (eq ▸ ?_) ((associated_mul_unit_left _ _ (f.map_units s)))⟩
    · rw [Multiset.mem_filter, Multiset.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx.1
      exact f.map_prime (prime_of_factor _ hp)
        (mt (fun h => eq_zero_of_zero_dvd <| h ▸ map_dvd f (dvd_of_mem_factors hp)) hn) hx.2
    · exact .trans (.trans (associated_unit_mul_right _ _ <|
        IsUnit.multisetProd_iff.mpr fun x hx => (Multiset.mem_filter.mp hx).2) <| .of_eq <|
        (Multiset.prod_filter_mul_prod_filter_not _).trans (f.toMonoidHom.map_multiset_prod _).symm)
        ((factors_prod (mt (by simp [·]) hn)).map f)

中文:
定理 uniqueFactorizationMonoid
  结论: (f : S.Localization映射 N)
  证明: have := f.isCancelMulZero
  .of_exists_prime_factors fun n hn => by
    classical
    have ⟨⟨m, s⟩, eq⟩ := f.surj n
    use ((factors m).map f).filter (¬ IsUnit ·)
    rw [Ne]; rw [← (f.map_units s).mul_left_eq_zero]; rw [eq] at hn
    refine ⟨fun x hx => ?_, .trans (eq ▸ ?_) ((associated_mul_unit_left _ _ (f.map_units s)))⟩
    · rw [Multiset.mem_filter, Multiset.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx.1
      exact f.map_prime (prime_of_factor _ hp)
        (mt (fun h => eq_zero_of_zero_dvd <| h ▸ map_dvd f (dvd_of_mem_factors hp)) hn) hx.2
    · exact .trans (.trans (associated_unit_mul_right _ _ <|
        IsUnit.multisetProd_iff.mpr fun x hx => (Multiset.mem_filter.mp hx).2) <| .of_eq <|
        (Multiset.prod_filter_mul_prod_filter_not _).trans (f.toMonoidHom.map_multiset_prod _).symm)
        ((factors_prod (mt (by simp [·]) hn)).map f)

Depends on / 依赖: IsUnit, Multiset, Multiset.mem_filter, Multiset.mem_map, associated_mul_unit_left, classical, dvd_of_mem_factors, eq_zero_of_zero_dvd, f.isCancelMulZero, f.map_prime, f.map_units, f.surj, factors, filter, isCancelMulZero, map_dvd, map_prime, map_units, mem_filter, mem_map
-/
theorem uniqueFactorizationMonoid (f : S.LocalizationMap N)
    [UniqueFactorizationMonoid M] : UniqueFactorizationMonoid N :=
  have := f.isCancelMulZero
  .of_exists_prime_factors fun n hn => by
    classical
    have ⟨⟨m, s⟩, eq⟩ := f.surj n
    use ((factors m).map f).filter (¬ IsUnit ·)
    rw [Ne]; rw [← (f.map_units s).mul_left_eq_zero]; rw [eq] at hn
    refine ⟨fun x hx => ?_, .trans (eq ▸ ?_) ((associated_mul_unit_left _ _ (f.map_units s)))⟩
    · rw [Multiset.mem_filter, Multiset.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx.1
      exact f.map_prime (prime_of_factor _ hp)
        (mt (fun h => eq_zero_of_zero_dvd <| h ▸ map_dvd f (dvd_of_mem_factors hp)) hn) hx.2
    · exact .trans (.trans (associated_unit_mul_right _ _ <|
        IsUnit.multisetProd_iff.mpr fun x hx => (Multiset.mem_filter.mp hx).2) <| .of_eq <|
        (Multiset.prod_filter_mul_prod_filter_not _).trans (f.toMonoidHom.map_multiset_prod _).symm)
        ((factors_prod (mt (by simp [·]) hn)).map f)

end Submonoid.LocalizationMap

variable [CommSemiring M] (S : Submonoid M)

/--
theorem `UniqueFactorizationMonoid.of_isLocalization` / 定理 `UniqueFactorizationMonoid.of_isLocalization`

English:
theorem UniqueFactorizationMonoid.of_isLocalization
  statement: (N : Type*) [CommSemiring N] [Algebra M N]
  proof: (IsLocalization.toLocalizationMap S N).uniqueFactorizationMonoid

中文:
定理 唯一分解幺半群.of_isLocalization
  结论: (N : 类型) [交换半环 N] [代数 M N]
  证明: (IsLocalization.toLocalizationMap S N).uniqueFactorizationMonoid

Depends on / 依赖: IsLocalization, IsLocalization.toLocalizationMap, toLocalizationMap, uniqueFactorizationMonoid
-/
theorem UniqueFactorizationMonoid.of_isLocalization (N : Type*) [CommSemiring N] [Algebra M N]
    [IsLocalization S N] [UniqueFactorizationMonoid M] : UniqueFactorizationMonoid N :=
  (IsLocalization.toLocalizationMap S N).uniqueFactorizationMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UniqueFactorizationMonoid
  signature: M] : UniqueFactorizationMonoid (Localization S)
  body: (Localization.monoidOf S).uniqueFactorizationMonoid

中文:
实例 [唯一分解幺半群
  签名: M] : 唯一分解幺半群 (Localization S)
  定义体: (Localization.monoidOf S).uniqueFactorizationMonoid

Depends on / 依赖: Localization, Localization.monoidOf, monoidOf, uniqueFactorizationMonoid
-/
instance [UniqueFactorizationMonoid M] : UniqueFactorizationMonoid (Localization S) :=
  (Localization.monoidOf S).uniqueFactorizationMonoid
