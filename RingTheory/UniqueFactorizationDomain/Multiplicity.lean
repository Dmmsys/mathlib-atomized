/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Unique factorization and multiplicity

## Main results

* `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`: The multiplicity of an
  irreducible factor of a nonzero element is exactly the number of times the normalized factor
  occurs in the `normalizedFactors`.
-/

public section

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

/--
theorem `WfDvdMonoid.max_power_factor'` / 定理 `WfDvdMonoid.max_power_factor'`

English:
theorem WfDvdMonoid.max_power_factor'
  statement: [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
  proof: by
  obtain ⟨a, ⟨n, rfl⟩, hm⟩ := wellFounded_dvdNotUnit.has_min
    {a | exists n, x ^ n * a = a₀} ⟨a₀, 0, by rw [pow_zero, one_mul]⟩
  refine ⟨n, a, ?_, rfl⟩; rintro ⟨d, rfl⟩
  exact hm d ⟨n + 1, by rw [pow_succ, mul_assoc]⟩
    ⟨(right_ne_zero_of_mul <| right_ne_zero_of_mul h), x, hx, mul_comm _ _

中文:
定理 WfDvdMonoid.max_power_factor'
  结论: [带零交换幺半群 α] [WfDvdMonoid α] {a₀ x : α}
  证明: by
  obtain ⟨a, ⟨n, rfl⟩, hm⟩ := wellFounded_dvdNotUnit.has_min
    {a | exists n, x ^ n * a = a₀} ⟨a₀, 0, by rw [pow_zero, one_mul]⟩
  refine ⟨n, a, ?_, rfl⟩; rintro ⟨d, rfl⟩
  exact hm d ⟨n + 1, by rw [pow_succ, mul_assoc]⟩
    ⟨(right_ne_zero_of_mul <| right_ne_zero_of_mul h), x, hx, mul_comm _ _

Depends on / 依赖: has_min, mul_assoc, mul_comm, one_mul, pow_succ, pow_zero, right_ne_zero_of_mul, wellFounded_dvdNotUnit, wellFounded_dvdNotUnit.has_min
-/
theorem WfDvdMonoid.max_power_factor' [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ != 0) (hx : ¬IsUnit x) : exists (n : Nat) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a := by
  obtain ⟨a, ⟨n, rfl⟩, hm⟩ := wellFounded_dvdNotUnit.has_min
    {a | exists n, x ^ n * a = a₀} ⟨a₀, 0, by rw [pow_zero, one_mul]⟩
  refine ⟨n, a, ?_, rfl⟩; rintro ⟨d, rfl⟩
  exact hm d ⟨n + 1, by rw [pow_succ, mul_assoc]⟩
    ⟨(right_ne_zero_of_mul <| right_ne_zero_of_mul h), x, hx, mul_comm _ _⟩

/--
theorem `WfDvdMonoid.max_power_factor` / 定理 `WfDvdMonoid.max_power_factor`

English:
theorem WfDvdMonoid.max_power_factor
  statement: [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
  proof: max_power_factor' h hx.not_isUnit

中文:
定理 WfDvdMonoid.max_power_factor
  结论: [带零交换幺半群 α] [WfDvdMonoid α] {a₀ x : α}
  证明: max_power_factor' h hx.not_isUnit

Depends on / 依赖: hx.not_isUnit, max_power_factor, not_isUnit
-/
theorem WfDvdMonoid.max_power_factor [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ != 0) (hx : Irreducible x) : exists (n : Nat) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a :=
  max_power_factor' h hx.not_isUnit

/--
theorem `FiniteMultiplicity.of_not_isUnit` / 定理 `FiniteMultiplicity.of_not_isUnit`

English:
theorem FiniteMultiplicity.of_not_isUnit
  statement: [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
  proof: by
  obtain ⟨n, c, ndvd, rfl⟩ := WfDvdMonoid.max_power_factor' hb ha
  exact ⟨n, by rwa [pow_succ, mul_dvd_mul_iff_left (left_ne_zero_of_mul hb)]⟩

中文:
定理 FiniteMultiplicity.of_not_isUnit
  结论: [带零交换幺半群 α] [是乘零消去 α] [WfDvdMonoid α]
  证明: by
  obtain ⟨n, c, ndvd, rfl⟩ := WfDvdMonoid.max_power_factor' hb ha
  exact ⟨n, by rwa [pow_succ, mul_dvd_mul_iff_left (left_ne_zero_of_mul hb)]⟩

Depends on / 依赖: WfDvdMonoid, WfDvdMonoid.max_power_factor, left_ne_zero_of_mul, max_power_factor, mul_dvd_mul_iff_left, pow_succ
-/
theorem FiniteMultiplicity.of_not_isUnit [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    {a b : α} (ha : ¬IsUnit a) (hb : b != 0) : FiniteMultiplicity a b := by
  obtain ⟨n, c, ndvd, rfl⟩ := WfDvdMonoid.max_power_factor' hb ha
  exact ⟨n, by rwa [pow_succ, mul_dvd_mul_iff_left (left_ne_zero_of_mul hb)]⟩

/--
theorem `FiniteMultiplicity.of_prime_left` / 定理 `FiniteMultiplicity.of_prime_left`

English:
theorem FiniteMultiplicity.of_prime_left
  statement: [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
  proof: .of_not_isUnit ha.not_isUnit hb

中文:
定理 FiniteMultiplicity.of_prime_left
  结论: [带零交换幺半群 α] [是乘零消去 α] [WfDvdMonoid α]
  证明: .of_not_isUnit ha.not_isUnit hb

Depends on / 依赖: ha.not_isUnit, not_isUnit, of_not_isUnit
-/
theorem FiniteMultiplicity.of_prime_left [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    {a b : α} (ha : Prime a) (hb : b != 0) : FiniteMultiplicity a b :=
  .of_not_isUnit ha.not_isUnit hb

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

section multiplicity

variable [NormalizationMonoid R]

open Multiset

/--
theorem `le_emultiplicity_iff_replicate_le_normalizedFactors` / 定理 `le_emultiplicity_iff_replicate_le_normalizedFactors`

English:
theorem le_emultiplicity_iff_replicate_le_normalizedFactors
  statement: {a b : R} {n : Nat} (ha : Irreducible a)
  proof: by
  rw [← pow_dvd_iff_le_emultiplicity]
  revert b
  induction n with
  | zero => simp
  | succ n ih => ?_
  intro b hb
  constructor
  · rintro ⟨c, rfl⟩
    rw [Ne]; rw [pow_succ']; rw [mul_assoc]; rw [mul_eq_zero]; rw [not_or] at hb
    rw [pow_succ']; rw [mul_assoc]; rw [normalizedFactors_mul hb

中文:
定理 le_emultiplicity_iff_replicate_le_normalizedFactors
  结论: {a b : R} {n : 自然数} (ha : 不可约 a)
  证明: by
  rw [← pow_dvd_iff_le_emultiplicity]
  revert b
  induction n with
  | zero => simp
  | succ n ih => ?_
  intro b hb
  constructor
  · rintro ⟨c, rfl⟩
    rw [Ne]; rw [pow_succ']; rw [mul_assoc]; rw [mul_eq_zero]; rw [not_or] at hb
    rw [pow_succ']; rw [mul_assoc]; rw [normalizedFactors_mul hb

Depends on / 依赖: Dvd.intro, Multiset, Multiset.le_iff_exists_add, cons_le_cons_iff, le_iff_exists_add, mul_assoc, mul_eq_zero, normalizedFactors_irreducible, normalizedFactors_mul, not_or, pow_dvd_iff_le_emultiplicity, pow_succ, prod_normalizedFac, replicate_succ, revert, singleton_add
-/
theorem le_emultiplicity_iff_replicate_le_normalizedFactors {a b : R} {n : Nat} (ha : Irreducible a)
    (hb : b != 0) :
    ↑n <= emultiplicity a b ↔ replicate n (normalize a) <= normalizedFactors b := by
  rw [← pow_dvd_iff_le_emultiplicity]
  revert b
  induction n with
  | zero => simp
  | succ n ih => ?_
  intro b hb
  constructor
  · rintro ⟨c, rfl⟩
    rw [Ne]; rw [pow_succ']; rw [mul_assoc]; rw [mul_eq_zero]; rw [not_or] at hb
    rw [pow_succ']; rw [mul_assoc]; rw [normalizedFactors_mul hb.1 hb.2]; rw [replicate_succ]; rw [normalizedFactors_irreducible ha]; rw [singleton_add]; rw [cons_le_cons_iff]; rw [← ih hb.2]
    apply Dvd.intro _ rfl
  · rw [Multiset.le_iff_exists_add]
    rintro ⟨u, hu⟩
    rw [← (prod_normalizedFactors hb).dvd_iff_dvd_right]; rw [hu]; rw [prod_add]; rw [prod_replicate]
    exact (Associated.pow_pow <| associated_normalize a).dvd.trans (Dvd.intro u.prod rfl)

variable [DecidableEq R]

/--
theorem `emultiplicity_eq_count_normalizedFactors` / 定理 `emultiplicity_eq_count_normalizedFactors`

English:
theorem emultiplicity_eq_count_normalizedFactors
  given: {a b : R} (ha : Irreducible a) (hb : b != 0)
  proof: by
  apply le_antisymm
  · apply Order.le_of_lt_add_one
    rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [lt_iff_not_ge]; rw [le_emultiplicity_iff_replicate_le_normalizedFactors ha hb]; rw [← le_count_iff_replicate_le]
    simp
  rw [le_emultiplicity_iff_replicate_le_normalizedFactors ha hb]; rw [← 

中文:
定理 emultiplicity_eq_count_normalizedFactors
  条件: {a b : R} (ha : 不可约 a) (hb : b != 0)
  证明: by
  apply le_antisymm
  · apply Order.le_of_lt_add_one
    rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [lt_iff_not_ge]; rw [le_emultiplicity_iff_replicate_le_normalizedFactors ha hb]; rw [← le_count_iff_replicate_le]
    simp
  rw [le_emultiplicity_iff_replicate_le_normalizedFactors ha hb]; rw [← 

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Order.le_of_lt_add_one, cast_add, cast_one, le_antisymm, le_count_iff_replicate_le, le_emultiplicity_iff_replicate_le_normalizedFactors, le_of_lt_add_one, lt_iff_not_ge
-/
theorem emultiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0) :
    emultiplicity a b = (normalizedFactors b).count (normalize a) := by
  apply le_antisymm
  · apply Order.le_of_lt_add_one
    rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [lt_iff_not_ge]; rw [le_emultiplicity_iff_replicate_le_normalizedFactors ha hb]; rw [← le_count_iff_replicate_le]
    simp
  rw [le_emultiplicity_iff_replicate_le_normalizedFactors ha hb]; rw [← le_count_iff_replicate_le]

/--
theorem `multiplicity_eq_count_normalizedFactors` / 定理 `multiplicity_eq_count_normalizedFactors`

English:
theorem multiplicity_eq_count_normalizedFactors
  given: {a b : R} (ha : Irreducible a) (hb : b != 0)
  proof: by
  have := emultiplicity_eq_count_normalizedFactors ha hb
  rwa [(finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity,
    ENat.natCast_inj] at this

中文:
定理 multiplicity_eq_count_normalizedFactors
  条件: {a b : R} (ha : 不可约 a) (hb : b != 0)
  证明: by
  have := emultiplicity_eq_count_normalizedFactors ha hb
  rwa [(finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity,
    ENat.natCast_inj] at this

Depends on / 依赖: ENat.natCast_inj, emultiplicity_eq_count_normalizedFactors, emultiplicity_eq_multiplicity, finiteMultiplicity_of_emultiplicity_eq_natCast, natCast_inj
-/
theorem multiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0) :
    multiplicity a b = (normalizedFactors b).count (normalize a) := by
  have := emultiplicity_eq_count_normalizedFactors ha hb
  rwa [(finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity,
    ENat.natCast_inj] at this

/--
theorem `count_normalizedFactors_eq` / 定理 `count_normalizedFactors_eq`

English:
theorem count_normalizedFactors_eq
  statement: {p x : R} (hp : Irreducible p) (hnorm : normalize p = p) {n : Nat}
  proof: by
  by_cases hx0 : x = 0
  · simp [hx0] at hlt
  apply Nat.cast_injective (R := Nat∞)
  convert! (emultiplicity_eq_count_normalizedFactors hp hx0).symm
  · exact hnorm.symm
  exact (emultiplicity_eq_coe.mpr ⟨hle, hlt⟩).symm

中文:
定理 count_normalizedFactors_eq
  结论: {p x : R} (hp : 不可约 p) (hnorm : normalize p = p) {n : 自然数}
  证明: by
  by_cases hx0 : x = 0
  · simp [hx0] at hlt
  apply Nat.cast_injective (R := Nat∞)
  convert! (emultiplicity_eq_count_normalizedFactors hp hx0).symm
  · exact hnorm.symm
  exact (emultiplicity_eq_coe.mpr ⟨hle, hlt⟩).symm

Depends on / 依赖: Nat.cast_injective, cast_injective, convert, emultiplicity_eq_coe, emultiplicity_eq_coe.mpr, emultiplicity_eq_count_normalizedFactors, hnorm.symm
-/
theorem count_normalizedFactors_eq {p x : R} (hp : Irreducible p) (hnorm : normalize p = p) {n : Nat}
    (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  by_cases hx0 : x = 0
  · simp [hx0] at hlt
  apply Nat.cast_injective (R := Nat∞)
  convert! (emultiplicity_eq_count_normalizedFactors hp hx0).symm
  · exact hnorm.symm
  exact (emultiplicity_eq_coe.mpr ⟨hle, hlt⟩).symm

/--
theorem `count_normalizedFactors_eq'` / 定理 `count_normalizedFactors_eq'`

English:
theorem count_normalizedFactors_eq'
  statement: {p x : R} (hp : p = 0 ∨ Irreducible p) (hnorm : normalize p = p)
  proof: by
  rcases hp with (rfl | hp)
  · cases n
    · exact count_eq_zero.2 (zero_notMem_normalizedFactors _)
    · rw [zero_pow (Nat.succ_ne_zero _)] at hle hlt
      exact absurd hle hlt
  · exact count_normalizedFactors_eq hp hnorm hle hlt

中文:
定理 count_normalizedFactors_eq'
  结论: {p x : R} (hp : p = 0 ∨ 不可约 p) (hnorm : normalize p = p)
  证明: by
  rcases hp with (rfl | hp)
  · cases n
    · exact count_eq_zero.2 (zero_notMem_normalizedFactors _)
    · rw [zero_pow (Nat.succ_ne_zero _)] at hle hlt
      exact absurd hle hlt
  · exact count_normalizedFactors_eq hp hnorm hle hlt

Depends on / 依赖: Nat.succ_ne_zero, absurd, count_eq_zero, count_normalizedFactors_eq, succ_ne_zero, zero_notMem_normalizedFactors, zero_pow
-/
theorem count_normalizedFactors_eq' {p x : R} (hp : p = 0 ∨ Irreducible p) (hnorm : normalize p = p)
    {n : Nat} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  rcases hp with (rfl | hp)
  · cases n
    · exact count_eq_zero.2 (zero_notMem_normalizedFactors _)
    · rw [zero_pow (Nat.succ_ne_zero _)] at hle hlt
      exact absurd hle hlt
  · exact count_normalizedFactors_eq hp hnorm hle hlt

/--
lemma `associated_finprod_pow_count` / 引理 `associated_finprod_pow_count`

English:
lemma associated_finprod_pow_count
  given: {x : R} (hx : x != 0)
  proof: by
  rw [← Multiset.prod_map_eq_finprod]; rw [Multiset.map_id']
  exact prod_normalizedFactors hx

中文:
引理 associated_finprod_pow_count
  条件: {x : R} (hx : x != 0)
  证明: by
  rw [← Multiset.prod_map_eq_finprod]; rw [Multiset.map_id']
  exact prod_normalizedFactors hx

Depends on / 依赖: Multiset, Multiset.map_id, Multiset.prod_map_eq_finprod, map_id, prod_map_eq_finprod, prod_normalizedFactors
-/
lemma associated_finprod_pow_count {x : R} (hx : x != 0) :
    Associated (∏ᶠ p : R, p ^ (normalizedFactors x).count p) x := by
  rw [← Multiset.prod_map_eq_finprod]; rw [Multiset.map_id']
  exact prod_normalizedFactors hx

/--
lemma `finprod_pow_count_eq_of_subsingleton_units` / 引理 `finprod_pow_count_eq_of_subsingleton_units`

English:
lemma finprod_pow_count_eq_of_subsingleton_units
  given: [Subsingleton Rˣ] {x : R} (hx : x != 0)
  proof: associated_iff_eq.mp associated_finprod_pow_count hx

中文:
引理 finprod_pow_count_eq_of_subsingleton_units
  条件: [子单例 Rˣ] {x : R} (hx : x != 0)
  证明: associated_iff_eq.mp associated_finprod_pow_count hx

Depends on / 依赖: associated_finprod_pow_count, associated_iff_eq, associated_iff_eq.mp
-/
lemma finprod_pow_count_eq_of_subsingleton_units [Subsingleton Rˣ] {x : R} (hx : x != 0) :
    ∏ᶠ p : R, p ^ (normalizedFactors x).count p = x :=
associated_iff_eq.mp associated_finprod_pow_count hx

end multiplicity

/--
lemma `dvd_iff_emultiplicity_le` / 引理 `dvd_iff_emultiplicity_le`

English:
lemma dvd_iff_emultiplicity_le
  given: {a b : R} (ha : a != 0)
  proof: by
  classical
  refine ⟨fun h _ _ => emultiplicity_le_emultiplicity_of_dvd_right h, fun h => ?_⟩
  by_cases hb : b = 0
  · simp_all
  let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha hb]; rw [Multiset.le

中文:
引理 dvd_iff_emultiplicity_le
  条件: {a b : R} (ha : a != 0)
  证明: by
  classical
  refine ⟨fun h _ _ => emultiplicity_le_emultiplicity_of_dvd_right h, fun h => ?_⟩
  by_cases hb : b = 0
  · simp_all
  let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha hb]; rw [Multiset.le

Depends on / 依赖: Multiset, Multiset.le_iff_count, StrongNormalizationMonoid, UniqueFactorizationMonoid, UniqueFactorizationMonoid.strongNormalizationMonoid, classical, dvd_iff_normalizedFactors_le_normalizedFactors, emultip, emultiplicity_eq_count_normalizedFactors, emultiplicity_le_emultiplicity_of_dvd_right, hqprime, hqprime.irreducible, irreducible, le_iff_count, normalizedFactors, prime_of_normalized_factor, strongNormalizationMonoid
-/
lemma dvd_iff_emultiplicity_le {a b : R} (ha : a != 0) :
    a ∣ b ↔ forall p : R, Prime p -> emultiplicity p a <= emultiplicity p b := by
  classical
  refine ⟨fun h _ _ => emultiplicity_le_emultiplicity_of_dvd_right h, fun h => ?_⟩
  by_cases hb : b = 0
  · simp_all
  let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha hb]; rw [Multiset.le_iff_count]
  intro q
  by_cases hq : q in normalizedFactors a
  · have hqprime : Prime q := prime_of_normalized_factor q hq
    have h1 := emultiplicity_eq_count_normalizedFactors hqprime.irreducible ha
    have h2 := emultiplicity_eq_count_normalizedFactors hqprime.irreducible hb
    rw [normalize_normalized_factor q hq] at h1 h2
    simpa [h1, h2] using h q hqprime
  · simp [Multiset.count_eq_zero_of_notMem hq]

/--
lemma `pow_dvd_pow_iff_dvd` / 引理 `pow_dvd_pow_iff_dvd`

English:
lemma pow_dvd_pow_iff_dvd
  given: {a b : R} {n : Nat} (hn : n != 0)
  statement: a ^ n ∣ b ^ n ↔ a ∣ b
  proof: by
  by_cases ha : a = 0
  · simp [ha, hn]
  refine ⟨?_, fun h => pow_dvd_pow_of_dvd h n⟩
  rw [dvd_iff_emultiplicity_le (pow_ne_zero n ha)]; rw [dvd_iff_emultiplicity_le ha]
  intro H p hp
  have := H p hp
  rwa [emultiplicity_pow hp, emultiplicity_pow hp,
    ENat.mul_le_mul_left_iff (by exact_mod

中文:
引理 pow_dvd_pow_iff_dvd
  条件: {a b : R} {n : 自然数} (hn : n != 0)
  结论: a ^ n ∣ b ^ n ↔ a ∣ b
  证明: by
  by_cases ha : a = 0
  · simp [ha, hn]
  refine ⟨?_, fun h => pow_dvd_pow_of_dvd h n⟩
  rw [dvd_iff_emultiplicity_le (pow_ne_zero n ha)]; rw [dvd_iff_emultiplicity_le ha]
  intro H p hp
  have := H p hp
  rwa [emultiplicity_pow hp, emultiplicity_pow hp,
    ENat.mul_le_mul_left_iff (by exact_mod

Depends on / 依赖: ENat.mul_le_mul_left_iff, ENat.natCast_ne_top, dvd_iff_emultiplicity_le, emultiplicity_pow, mul_le_mul_left_iff, natCast_ne_top, pow_dvd_pow_of_dvd, pow_ne_zero
-/
lemma pow_dvd_pow_iff_dvd {a b : R} {n : Nat} (hn : n != 0) : a ^ n ∣ b ^ n ↔ a ∣ b := by
  by_cases ha : a = 0
  · simp [ha, hn]
  refine ⟨?_, fun h => pow_dvd_pow_of_dvd h n⟩
  rw [dvd_iff_emultiplicity_le (pow_ne_zero n ha)]; rw [dvd_iff_emultiplicity_le ha]
  intro H p hp
  have := H p hp
  rwa [emultiplicity_pow hp, emultiplicity_pow hp,
    ENat.mul_le_mul_left_iff (by exact_mod_cast hn) (ENat.natCast_ne_top _)] at this

@[fun_prop]
/--
lemma `hasFiniteMulSupport_fun_pow_multiplicity` / 引理 `hasFiniteMulSupport_fun_pow_multiplicity`

English:
lemma hasFiniteMulSupport_fun_pow_multiplicity
  statement: {α M : Type*} [CommMonoid M] [Subsingleton Rˣ]
  proof: by
  classical
  simp only [multiplicity_eq_count_normalizedFactors (hg _) hr, normalize_eq]
  fun_prop

中文:
引理 hasFiniteMulSupport_fun_pow_multiplicity
  结论: {α M : 类型} [交换幺半群 M] [子单例 Rˣ]
  证明: by
  classical
  simp only [multiplicity_eq_count_normalizedFactors (hg _) hr, normalize_eq]
  fun_prop

Depends on / 依赖: classical, fun_prop, multiplicity_eq_count_normalizedFactors, normalize_eq
-/
lemma hasFiniteMulSupport_fun_pow_multiplicity {α M : Type*} [CommMonoid M] [Subsingleton Rˣ]
    (f : α -> M) {g : α -> R} (hgi : g.Injective) (hg : forall s, Irreducible (g s)) {r : R} (hr : r != 0) :
    (fun s : α => f s ^ multiplicity (g s) r).HasFiniteMulSupport := by
  classical
  simp only [multiplicity_eq_count_normalizedFactors (hg _) hr, normalize_eq]
  fun_prop

end UniqueFactorizationMonoid
