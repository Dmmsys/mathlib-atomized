/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.Divisors

/-!
# Results about divisors and factorizations
-/

public section

open Finsupp

namespace Nat

/--
theorem `coe_divisors_eq_prod_pow_le_factorization` / 定理 `coe_divisors_eq_prod_pow_le_factorization`

English:
theorem coe_divisors_eq_prod_pow_le_factorization
  given: {n : Nat} (hn : n != 0)
  proof: by
  refine Set.ext fun k => ⟨fun h => ?_, fun ⟨f, hle, h⟩ => mem_divisors.mpr ⟨?_, hn⟩⟩
  · have hdvd := dvd_of_mem_divisors h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
.mpr hdvd, prod_factorization_pow_eq_self hk⟩ exact ⟨_, factorization_le_iff_dvd hk hn
  · rw [← h, ← prod_factorization_pow_e

中文:
定理 coe_divisors_eq_prod_pow_le_factorization
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  refine Set.ext fun k => ⟨fun h => ?_, fun ⟨f, hle, h⟩ => mem_divisors.mpr ⟨?_, hn⟩⟩
  · have hdvd := dvd_of_mem_divisors h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
.mpr hdvd, prod_factorization_pow_eq_self hk⟩ exact ⟨_, factorization_le_iff_dvd hk hn
  · rw [← h, ← prod_factorization_pow_e

Depends on / 依赖: Nat.pow_dvd_pow, Set.ext, dvd_of_mem_divisors, factorization_le_iff_dvd, mem_divisors, mem_divisors.mpr, ne_zero_of_dvd_ne_zero, pow_dvd_pow, prod_dvd_prod_of_subset_of_dvd, prod_factorization_pow_eq_self, support_mono
-/
theorem coe_divisors_eq_prod_pow_le_factorization {n : Nat} (hn : n != 0) :
    n.divisors = { f.prod (· ^ ·) | f <= n.factorization } := by
  refine Set.ext fun k => ⟨fun h => ?_, fun ⟨f, hle, h⟩ => mem_divisors.mpr ⟨?_, hn⟩⟩
  · have hdvd := dvd_of_mem_divisors h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
.mpr hdvd, prod_factorization_pow_eq_self hk⟩ exact ⟨_, factorization_le_iff_dvd hk hn
  · rw [← h, ← prod_factorization_pow_eq_self hn]
exact prod_dvd_prod_of_subset_of_dvd (support_mono hle) fun p _ => Nat.pow_dvd_pow p hle p

/--
theorem `divisors_eq_image_Iic_factorization_prod_pow` / 定理 `divisors_eq_image_Iic_factorization_prod_pow`

English:
theorem divisors_eq_image_Iic_factorization_prod_pow
  given: {n : Nat} (hn : n != 0)
  proof: by
  apply Finset.coe_inj.mp
  grind [coe_divisors_eq_prod_pow_le_factorization]

中文:
定理 divisors_eq_image_Iic_factorization_prod_pow
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  apply Finset.coe_inj.mp
  grind [coe_divisors_eq_prod_pow_le_factorization]

Depends on / 依赖: Finset, Finset.coe_inj.mp, coe_divisors_eq_prod_pow_le_factorization, coe_inj
-/
theorem divisors_eq_image_Iic_factorization_prod_pow {n : Nat} (hn : n != 0) :
    n.divisors = (Finset.Iic n.factorization).image (·.prod (· ^ ·)) := by
  apply Finset.coe_inj.mp
  grind [coe_divisors_eq_prod_pow_le_factorization]

/--
theorem `Iic_factorization_prod_pow_injective` / 定理 `Iic_factorization_prod_pow_injective`

English:
theorem Iic_factorization_prod_pow_injective
  given: (n : Nat)
  proof: by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]

中文:
定理 Iic_factorization_prod_pow_injective
  条件: (n : 自然数)
  证明: by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]

Depends on / 依赖: Function, Function.Injective, Injective, factorization_prod_pow_eq_self_of_le_factorization
-/
theorem Iic_factorization_prod_pow_injective (n : Nat) :
    (·.val.prod (· ^ ·) : Finset.Iic n.factorization -> _).Injective := by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]

/--
theorem `divisors_eq_map_attach_Iic_factorization_prod_pow` / 定理 `divisors_eq_map_attach_Iic_factorization_prod_pow`

English:
theorem divisors_eq_map_attach_Iic_factorization_prod_pow
  given: {n : Nat} (hn : n != 0)
  proof: by
  rw [Finset.map_eq_image]
  change _ = (Finset.Iic n.factorization).attach.image ((·.prod (· ^ ·)) ∘ Subtype.val)
  rw [← Finset.image_image]; rw [Finset.attach_image_val]
  exact divisors_eq_image_Iic_factorization_prod_pow hn

中文:
定理 divisors_eq_map_attach_Iic_factorization_prod_pow
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  rw [Finset.map_eq_image]
  change _ = (Finset.Iic n.factorization).attach.image ((·.prod (· ^ ·)) ∘ Subtype.val)
  rw [← Finset.image_image]; rw [Finset.attach_image_val]
  exact divisors_eq_image_Iic_factorization_prod_pow hn

Depends on / 依赖: Finset, Finset.Iic, Finset.attach_image_val, Finset.image_image, Finset.map_eq_image, Subtype, Subtype.val, attach, attach.image, attach_image_val, divisors_eq_image_Iic_factorization_prod_pow, factorization, image_image, map_eq_image, n.factorization
-/
theorem divisors_eq_map_attach_Iic_factorization_prod_pow {n : Nat} (hn : n != 0) :
    n.divisors = (Finset.Iic n.factorization).attach.map
      ⟨(·.val.prod (· ^ ·)), Iic_factorization_prod_pow_injective n⟩ := by
  rw [Finset.map_eq_image]
  change _ = (Finset.Iic n.factorization).attach.image ((·.prod (· ^ ·)) ∘ Subtype.val)
  rw [← Finset.image_image]; rw [Finset.attach_image_val]
  exact divisors_eq_image_Iic_factorization_prod_pow hn

/--
theorem `coe_properDivisors_eq_prod_pow_lt_factorization` / 定理 `coe_properDivisors_eq_prod_pow_lt_factorization`

English:
theorem coe_properDivisors_eq_prod_pow_lt_factorization
  given: {n : Nat}
  proof: by
  by_cases hn : n = 0
  · simp [hn]
  refine Set.ext fun k => ⟨fun h => ?_, fun ⟨f, hlt, h⟩ => ?_⟩
  · have ⟨hdvd, hlt⟩ := mem_properDivisors.mp h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
    refine ⟨_, ?_, prod_factorization_pow_eq_self hk⟩
apply lt_of_le_of_ne .mpr hdvd factorization_le_if

中文:
定理 coe_properDivisors_eq_prod_pow_lt_factorization
  条件: {n : 自然数}
  证明: by
  by_cases hn : n = 0
  · simp [hn]
  refine Set.ext fun k => ⟨fun h => ?_, fun ⟨f, hlt, h⟩ => ?_⟩
  · have ⟨hdvd, hlt⟩ := mem_properDivisors.mp h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
    refine ⟨_, ?_, prod_factorization_pow_eq_self hk⟩
apply lt_of_le_of_ne .mpr hdvd factorization_le_if

Depends on / 依赖: Nat.eq_of_factorization_eq, Nat.po, Set.ext, eq_of_factorization_eq, factorization_le_iff_dvd, hlt.le, hlt.ne, lt_of_le_of_ne, mem_properDivisors, mem_properDivisors.mp, ne_zero_of_dvd_ne_zero, prod_dvd_prod_of_subset_of_dvd, prod_factorization_pow_eq_self, support_mono
-/
theorem coe_properDivisors_eq_prod_pow_lt_factorization {n : Nat} :
    n.properDivisors = { f.prod (· ^ ·) | f < n.factorization } := by
  by_cases hn : n = 0
  · simp [hn]
  refine Set.ext fun k => ⟨fun h => ?_, fun ⟨f, hlt, h⟩ => ?_⟩
  · have ⟨hdvd, hlt⟩ := mem_properDivisors.mp h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
    refine ⟨_, ?_, prod_factorization_pow_eq_self hk⟩
apply lt_of_le_of_ne .mpr hdvd factorization_le_iff_dvd hk hn
    exact mt (Nat.eq_of_factorization_eq' hk hn) hlt.ne
  · have : k ∣ n := by
      rw [← h]; rw [← prod_factorization_pow_eq_self hn]
apply prod_dvd_prod_of_subset_of_dvd support_mono hlt.le
exact fun p _ => Nat.pow_dvd_pow p hlt.le p
    refine mem_properDivisors.mpr ⟨this, lt_of_le_of_ne (le_of_dvd (Nat.pos_of_ne_zero hn) this) ?_⟩
    suffices k.factorization = f from (this ▸ hlt.ne <| congrArg _ ·)
    exact h ▸ factorization_prod_pow_eq_self_of_le_factorization hlt.le

/--
theorem `properDivisors_eq_image_Iio_factorization_prod_pow` / 定理 `properDivisors_eq_image_Iio_factorization_prod_pow`

English:
theorem properDivisors_eq_image_Iio_factorization_prod_pow
  given: {n : Nat}
  proof: by
  apply Finset.coe_inj.mp
  grind [coe_properDivisors_eq_prod_pow_lt_factorization]

中文:
定理 properDivisors_eq_image_Iio_factorization_prod_pow
  条件: {n : 自然数}
  证明: by
  apply Finset.coe_inj.mp
  grind [coe_properDivisors_eq_prod_pow_lt_factorization]

Depends on / 依赖: Finset, Finset.coe_inj.mp, coe_inj, coe_properDivisors_eq_prod_pow_lt_factorization
-/
theorem properDivisors_eq_image_Iio_factorization_prod_pow {n : Nat} :
    n.properDivisors = (Finset.Iio n.factorization).image (·.prod (· ^ ·)) := by
  apply Finset.coe_inj.mp
  grind [coe_properDivisors_eq_prod_pow_lt_factorization]

/--
theorem `Iio_factorization_prod_pow_injective` / 定理 `Iio_factorization_prod_pow_injective`

English:
theorem Iio_factorization_prod_pow_injective
  given: (n : Nat)
  proof: by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]

中文:
定理 Iio_factorization_prod_pow_injective
  条件: (n : 自然数)
  证明: by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]

Depends on / 依赖: Function, Function.Injective, Injective, factorization_prod_pow_eq_self_of_le_factorization
-/
theorem Iio_factorization_prod_pow_injective (n : Nat) :
    (·.val.prod (· ^ ·) : Finset.Iio n.factorization -> _).Injective := by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]

/--
theorem `properDivisors_eq_map_attach_Iio_factorization_prod_pow` / 定理 `properDivisors_eq_map_attach_Iio_factorization_prod_pow`

English:
theorem properDivisors_eq_map_attach_Iio_factorization_prod_pow
  given: {n : Nat}
  proof: by
  rw [Finset.map_eq_image]
  change _ = (Finset.Iio n.factorization).attach.image ((·.prod (· ^ ·)) ∘ Subtype.val)
  rw [← Finset.image_image]; rw [Finset.attach_image_val]
  exact properDivisors_eq_image_Iio_factorization_prod_pow

中文:
定理 properDivisors_eq_map_attach_Iio_factorization_prod_pow
  条件: {n : 自然数}
  证明: by
  rw [Finset.map_eq_image]
  change _ = (Finset.Iio n.factorization).attach.image ((·.prod (· ^ ·)) ∘ Subtype.val)
  rw [← Finset.image_image]; rw [Finset.attach_image_val]
  exact properDivisors_eq_image_Iio_factorization_prod_pow

Depends on / 依赖: Finset, Finset.Iio, Finset.attach_image_val, Finset.image_image, Finset.map_eq_image, Subtype, Subtype.val, attach, attach.image, attach_image_val, factorization, image_image, map_eq_image, n.factorization, properDivisors_eq_image_Iio_factorization_prod_pow
-/
theorem properDivisors_eq_map_attach_Iio_factorization_prod_pow {n : Nat} :
    n.properDivisors = (Finset.Iio n.factorization).attach.map
      ⟨(·.val.prod (· ^ ·)), Iio_factorization_prod_pow_injective n⟩ := by
  rw [Finset.map_eq_image]
  change _ = (Finset.Iio n.factorization).attach.image ((·.prod (· ^ ·)) ∘ Subtype.val)
  rw [← Finset.image_image]; rw [Finset.attach_image_val]
  exact properDivisors_eq_image_Iio_factorization_prod_pow

end Nat
