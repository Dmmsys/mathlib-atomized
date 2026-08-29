/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluation of power series in Hahn Series

We describe a class of ring homomorphisms from formal power series to Hahn series,
given by substitution of the generating variable to an element of strictly positive order.

## Main Definitions
* `HahnSeries.SummableFamily.powerSeriesFamily`: A summable family of Hahn series whose elements
  are non-negative powers of a fixed positive-order Hahn series multiplied by the coefficients of a
  formal power series.
* `PowerSeries.heval`: The `R`-algebra homomorphism from `PowerSeries σ R` to `R⟦Γ⟧` that
  takes `X` to a fixed positive-order Hahn Series and extends to formal infinite sums.

## TODO
* `MvPowerSeries.heval`: An `R`-algebra homomorphism from `MvPowerSeries σ R` to `R⟦Γ⟧`
  (for finite σ) taking each `X i` to a positive order Hahn Series.

-/

@[expose] public section

open Finset Function

noncomputable section

variable {Γ Γ' R V α β σ : Type*}

namespace HahnSeries

namespace SummableFamily

section PowerSeriesFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

variable [CommRing V] [Algebra R V]

/--
Definition of `powerSeriesFamily` / `powerSeriesFamily` 的定义

English:
abbreviation powerSeriesFamily
  signature: (x : V⟦Γ⟧) (f : PowerSeries R)
  body: smulFamily (fun n => f.coeff n) (powers x)

中文:
缩写 powerSeriesFamily
  签名: (x : V⟦Γ⟧) (f : 幂级数 R)
  定义体: smulFamily (fun n => f.coeff n) (powers x)

Depends on / 依赖: f.coeff, powers, smulFamily
-/
abbrev powerSeriesFamily (x : V⟦Γ⟧) (f : PowerSeries R) : SummableFamily Γ V Nat :=
  smulFamily (fun n => f.coeff n) (powers x)

/--
theorem `powerSeriesFamily_of_not_orderTop_pos` / 定理 `powerSeriesFamily_of_not_orderTop_pos`

English:
theorem powerSeriesFamily_of_not_orderTop_pos
  statement: {x : V⟦Γ⟧} (hx : ¬ 0 < x.orderTop)
  proof: by
  ext n g
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

中文:
定理 powerSeriesFamily_of_not_orderTop_pos
  结论: {x : V⟦Γ⟧} (hx : ¬ 0 < x.orderTop)
  证明: by
  ext n g
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
theorem powerSeriesFamily_of_not_orderTop_pos {x : V⟦Γ⟧} (hx : ¬ 0 < x.orderTop)
    (f : PowerSeries R) :
    powerSeriesFamily x f = powerSeriesFamily 0 f := by
  ext n g
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

/--
theorem `powerSeriesFamily_of_orderTop_pos` / 定理 `powerSeriesFamily_of_orderTop_pos`

English:
theorem powerSeriesFamily_of_orderTop_pos
  statement: {x : V⟦Γ⟧} (hx : 0 < x.orderTop)
  proof: by
  simp [hx]

中文:
定理 powerSeriesFamily_of_orderTop_pos
  结论: {x : V⟦Γ⟧} (hx : 0 < x.orderTop)
  证明: by
  simp [hx]
-/
theorem powerSeriesFamily_of_orderTop_pos {x : V⟦Γ⟧} (hx : 0 < x.orderTop)
    (f : PowerSeries R) (n : Nat) :
    powerSeriesFamily x f n = f.coeff n • x ^ n := by
  simp [hx]

/--
theorem `powerSeriesFamily_hsum_zero` / 定理 `powerSeriesFamily_hsum_zero`

English:
theorem powerSeriesFamily_hsum_zero
  given: (f : PowerSeries R)
  proof: by
  ext g
  by_cases hg : g = 0
  · simp only [hg, coeff_hsum]
    rw [finsum_eq_single _ 0 (fun n hn => by simp [hn])]
    simp
  · rw [coeff_hsum, finsum_eq_zero_of_forall_eq_zero
      fun n => (by by_cases hn : n = 0 <;> simp [hg, hn])]
    simp [hg]

中文:
定理 powerSeriesFamily_hsum_zero
  条件: (f : 幂级数 R)
  证明: by
  ext g
  by_cases hg : g = 0
  · simp only [hg, coeff_hsum]
    rw [finsum_eq_single _ 0 (fun n hn => by simp [hn])]
    simp
  · rw [coeff_hsum, finsum_eq_zero_of_forall_eq_zero
      fun n => (by by_cases hn : n = 0 <;> simp [hg, hn])]
    simp [hg]

Depends on / 依赖: coeff_hsum, finsum_eq_single, finsum_eq_zero_of_forall_eq_zero
-/
theorem powerSeriesFamily_hsum_zero (f : PowerSeries R) :
    (powerSeriesFamily 0 f).hsum = f.constantCoeff • (1 : V⟦Γ⟧) := by
  ext g
  by_cases hg : g = 0
  · simp only [hg, coeff_hsum]
    rw [finsum_eq_single _ 0 (fun n hn => by simp [hn])]
    simp
  · rw [coeff_hsum, finsum_eq_zero_of_forall_eq_zero
      fun n => (by by_cases hn : n = 0 <;> simp [hg, hn])]
    simp [hg]

/--
theorem `powerSeriesFamily_add` / 定理 `powerSeriesFamily_add`

English:
theorem powerSeriesFamily_add
  given: {x : V⟦Γ⟧} (f g : PowerSeries R)
  proof: by
  ext1 n
  by_cases hx : 0 < x.orderTop <;> · simp [hx, add_smul]

中文:
定理 powerSeriesFamily_add
  条件: {x : V⟦Γ⟧} (f g : 幂级数 R)
  证明: by
  ext1 n
  by_cases hx : 0 < x.orderTop <;> · simp [hx, add_smul]

Depends on / 依赖: add_smul, orderTop, x.orderTop
-/
theorem powerSeriesFamily_add {x : V⟦Γ⟧} (f g : PowerSeries R) :
    powerSeriesFamily x (f + g) = powerSeriesFamily x f + powerSeriesFamily x g := by
  ext1 n
  by_cases hx : 0 < x.orderTop <;> · simp [hx, add_smul]

/--
theorem `powerSeriesFamily_smul` / 定理 `powerSeriesFamily_smul`

English:
theorem powerSeriesFamily_smul
  given: {x : V⟦Γ⟧} (f : PowerSeries R) (r : R)
  proof: by
  ext1 n
  simp [mul_smul]

中文:
定理 powerSeriesFamily_smul
  条件: {x : V⟦Γ⟧} (f : 幂级数 R) (r : R)
  证明: by
  ext1 n
  simp [mul_smul]

Depends on / 依赖: mul_smul
-/
theorem powerSeriesFamily_smul {x : V⟦Γ⟧} (f : PowerSeries R) (r : R) :
    powerSeriesFamily x (r • f) = HahnSeries.single (0 : Γ) r • powerSeriesFamily x f := by
  ext1 n
  simp [mul_smul]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `support_powerSeriesFamily_subset` / 定理 `support_powerSeriesFamily_subset`

English:
theorem support_powerSeriesFamily_subset
  given: {x : V⟦Γ⟧} (a b : PowerSeries R) (g : Γ)
  proof: by
  by_cases h : 0 < x.orderTop
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    have he : exists c in antidiagonal n, (PowerSeries.coeff c.1) a • (PowerSeries.coeff c.2) b •
        ((powers x) n).coeff g != 0 := by
      refine exists_ne_zero_of_sum_ne_zero ?_
      simpa [PowerSeries.coeff_mul, sum_smul, mul_smul, h] using hn
    simp only [powers_of_orderTop_pos h, HasAntidiagonal.mem_antidiagonal] at he
    obtain ⟨c, hcn, hc⟩ := he
    simp only [coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    use c
    simp only [mul_toFun, smulFamily_toFun, Function.mem_support, hcn,
      and_true]
    rw [powers_of_orderTop_pos h c.1]; rw [powers_of_orderTop_pos h c.2]; rw [Algebra.smul_mul_assoc]; rw [Algebra.mul_smul_comm]; rw [← pow_add]; rw [hcn]
    simp [hc]
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    by_cases hz : n = 0
    · have : g = 0 ∧ (a.constantCoeff * b.constantCoeff) • (1 : V) != 0 := by
        simpa [hz, h] using hn
      simp only [coe_image, Set.mem_image]
      use (0, 0)
      simp [this.2, this.1, h, hz, smul_smul, mul_comm]
    · simp [h, hz] at hn

中文:
定理 support_powerSeriesFamily_subset
  条件: {x : V⟦Γ⟧} (a b : 幂级数 R) (g : Γ)
  证明: by
  by_cases h : 0 < x.orderTop
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    have he : exists c in antidiagonal n, (PowerSeries.coeff c.1) a • (PowerSeries.coeff c.2) b •
        ((powers x) n).coeff g != 0 := by
      refine exists_ne_zero_of_sum_ne_zero ?_
      simpa [PowerSeries.coeff_mul, sum_smul, mul_smul, h] using hn
    simp only [powers_of_orderTop_pos h, HasAntidiagonal.mem_antidiagonal] at he
    obtain ⟨c, hcn, hc⟩ := he
    simp only [coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    use c
    simp only [mul_toFun, smulFamily_toFun, Function.mem_support, hcn,
      and_true]
    rw [powers_of_orderTop_pos h c.1]; rw [powers_of_orderTop_pos h c.2]; rw [Algebra.smul_mul_assoc]; rw [Algebra.mul_smul_comm]; rw [← pow_add]; rw [hcn]
    simp [hc]
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    by_cases hz : n = 0
    · have : g = 0 ∧ (a.constantCoeff * b.constantCoeff) • (1 : V) != 0 := by
        simpa [hz, h] using hn
      simp only [coe_image, Set.mem_image]
      use (0, 0)
      simp [this.2, this.1, h, hz, smul_smul, mul_comm]
    · simp [h, hz] at hn

Depends on / 依赖: Finite, HasAntidiagonal, HasAntidiagonal.mem_antidiagonal, PowerSeries, PowerSeries.coeff, PowerSeries.coeff_mul, Set.Finite.coe_toFinset, Set.Finite.toFinset_subset, antidiagonal, coe_image, coe_toFinset, coeff_mul, coeff_support, exists_ne_zero_of_sum_ne_zero, mem_antidiagonal, mul_smul, orderTop, powers, powers_of_orderTop_pos, sum_smul
-/
theorem support_powerSeriesFamily_subset {x : V⟦Γ⟧} (a b : PowerSeries R) (g : Γ) :
    ((powerSeriesFamily x (a * b)).coeff g).support subseteq
    (((powerSeriesFamily x a).mul (powerSeriesFamily x b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  by_cases h : 0 < x.orderTop
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    have he : exists c in antidiagonal n, (PowerSeries.coeff c.1) a • (PowerSeries.coeff c.2) b •
        ((powers x) n).coeff g != 0 := by
      refine exists_ne_zero_of_sum_ne_zero ?_
      simpa [PowerSeries.coeff_mul, sum_smul, mul_smul, h] using hn
    simp only [powers_of_orderTop_pos h, HasAntidiagonal.mem_antidiagonal] at he
    obtain ⟨c, hcn, hc⟩ := he
    simp only [coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    use c
    simp only [mul_toFun, smulFamily_toFun, Function.mem_support, hcn,
      and_true]
    rw [powers_of_orderTop_pos h c.1]; rw [powers_of_orderTop_pos h c.2]; rw [Algebra.smul_mul_assoc]; rw [Algebra.mul_smul_comm]; rw [← pow_add]; rw [hcn]
    simp [hc]
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    by_cases hz : n = 0
    · have : g = 0 ∧ (a.constantCoeff * b.constantCoeff) • (1 : V) != 0 := by
        simpa [hz, h] using hn
      simp only [coe_image, Set.mem_image]
      use (0, 0)
      simp [this.2, this.1, h, hz, smul_smul, mul_comm]
    · simp [h, hz] at hn

/--
theorem `hsum_powerSeriesFamily_mul` / 定理 `hsum_powerSeriesFamily_mul`

English:
theorem hsum_powerSeriesFamily_mul
  given: {x : V⟦Γ⟧} (a b : PowerSeries R)
  proof: by
  by_cases h : 0 < x.orderTop;
  · ext g
    simp only [coeff_hsum_eq_sum, smulFamily_toFun, h, powers_of_orderTop_pos,
      HahnSeries.coeff_smul, mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [sum_subset (support_powerSeriesFamily_subset a b g)
      (fun i hi his => by simpa [h]; rw [PowerSeries.coeff_mul]; rw [sum_smul] using his)]
    simp only [coeff_support, mul_toFun, smulFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, HahnSeries.coeff_smul, PowerSeries.coeff_mul, sum_smul]
    rw [sum_sigma']
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp) ?_ ?_
      (fun _ _ => by simp [smul_smul, mul_comm, pow_add])).symm
    · intro ij hij
      simp only [coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe,
        HasAntidiagonal.mem_antidiagonal, and_true]
      use ij.1, ij.2
      simp_all
    · intro i hi his
      have hisc : forall j k : Nat, ⟨j + k, (j, k)⟩ = i -> (PowerSeries.coeff k) b •
          (PowerSeries.coeff j a • (x ^ j * x ^ k).coeff g) = 0 := by
        intro m n
        contrapose!
        simp only [powers_of_orderTop_pos h, Set.Finite.coe_toFinset, Set.mem_image,
          Function.mem_support, ne_eq, Prod.exists, not_exists, not_and] at his
        exact his m n
      simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hi
      rw [mul_comm ((PowerSeries.coeff i.snd.1) a)]; rw [← hi.2]; rw [mul_smul]; rw [pow_add]
exact hisc i.snd.1 i.snd.2 Sigma.eq hi.2 (by simp)
  · simp only [h, not_false_eq_true, powerSeriesFamily_of_not_orderTop_pos,
      powerSeriesFamily_hsum_zero, map_mul, hsum_mul]
    rw [smul_mul_smul_comm]; rw [mul_one]

中文:
定理 hsum_powerSeriesFamily_mul
  条件: {x : V⟦Γ⟧} (a b : 幂级数 R)
  证明: by
  by_cases h : 0 < x.orderTop;
  · ext g
    simp only [coeff_hsum_eq_sum, smulFamily_toFun, h, powers_of_orderTop_pos,
      HahnSeries.coeff_smul, mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [sum_subset (support_powerSeriesFamily_subset a b g)
      (fun i hi his => by simpa [h]; rw [PowerSeries.coeff_mul]; rw [sum_smul] using his)]
    simp only [coeff_support, mul_toFun, smulFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, HahnSeries.coeff_smul, PowerSeries.coeff_mul, sum_smul]
    rw [sum_sigma']
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp) ?_ ?_
      (fun _ _ => by simp [smul_smul, mul_comm, pow_add])).symm
    · intro ij hij
      simp only [coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe,
        HasAntidiagonal.mem_antidiagonal, and_true]
      use ij.1, ij.2
      simp_all
    · intro i hi his
      have hisc : forall j k : Nat, ⟨j + k, (j, k)⟩ = i -> (PowerSeries.coeff k) b •
          (PowerSeries.coeff j a • (x ^ j * x ^ k).coeff g) = 0 := by
        intro m n
        contrapose!
        simp only [powers_of_orderTop_pos h, Set.Finite.coe_toFinset, Set.mem_image,
          Function.mem_support, ne_eq, Prod.exists, not_exists, not_and] at his
        exact his m n
      simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hi
      rw [mul_comm ((PowerSeries.coeff i.snd.1) a)]; rw [← hi.2]; rw [mul_smul]; rw [pow_add]
exact hisc i.snd.1 i.snd.2 Sigma.eq hi.2 (by simp)
  · simp only [h, not_false_eq_true, powerSeriesFamily_of_not_orderTop_pos,
      powerSeriesFamily_hsum_zero, map_mul, hsum_mul]
    rw [smul_mul_smul_comm]; rw [mul_one]

Depends on / 依赖: Algebra, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, HahnSeries, HahnSeries.coeff_smul, PowerSeries, PowerSeries.coeff_mul, coeff_hsum_eq_sum, coeff_mul, coeff_smul, coeff_support, mul_smul_comm, mul_toFun, orderTop, powers_of_orderTop_pos, smulFamily_toFun, smul_mul_assoc, sum_smul, sum_subset, support_powerSeriesFamily_subset
-/
theorem hsum_powerSeriesFamily_mul {x : V⟦Γ⟧} (a b : PowerSeries R) :
    (powerSeriesFamily x (a * b)).hsum =
    ((powerSeriesFamily x a).mul (powerSeriesFamily x b)).hsum := by
  by_cases h : 0 < x.orderTop;
  · ext g
    simp only [coeff_hsum_eq_sum, smulFamily_toFun, h, powers_of_orderTop_pos,
      HahnSeries.coeff_smul, mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [sum_subset (support_powerSeriesFamily_subset a b g)
      (fun i hi his => by simpa [h]; rw [PowerSeries.coeff_mul]; rw [sum_smul] using his)]
    simp only [coeff_support, mul_toFun, smulFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, HahnSeries.coeff_smul, PowerSeries.coeff_mul, sum_smul]
    rw [sum_sigma']
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp) ?_ ?_
      (fun _ _ => by simp [smul_smul, mul_comm, pow_add])).symm
    · intro ij hij
      simp only [coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe,
        HasAntidiagonal.mem_antidiagonal, and_true]
      use ij.1, ij.2
      simp_all
    · intro i hi his
      have hisc : forall j k : Nat, ⟨j + k, (j, k)⟩ = i -> (PowerSeries.coeff k) b •
          (PowerSeries.coeff j a • (x ^ j * x ^ k).coeff g) = 0 := by
        intro m n
        contrapose!
        simp only [powers_of_orderTop_pos h, Set.Finite.coe_toFinset, Set.mem_image,
          Function.mem_support, ne_eq, Prod.exists, not_exists, not_and] at his
        exact his m n
      simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hi
      rw [mul_comm ((PowerSeries.coeff i.snd.1) a)]; rw [← hi.2]; rw [mul_smul]; rw [pow_add]
exact hisc i.snd.1 i.snd.2 Sigma.eq hi.2 (by simp)
  · simp only [h, not_false_eq_true, powerSeriesFamily_of_not_orderTop_pos,
      powerSeriesFamily_hsum_zero, map_mul, hsum_mul]
    rw [smul_mul_smul_comm]; rw [mul_one]

end PowerSeriesFamily

end SummableFamily

end HahnSeries

namespace PowerSeries

open HahnSeries SummableFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] (x : R⟦Γ⟧)

/-- The `R`-algebra homomorphism from `R⟦X⟧` to `R⟦Γ⟧` given by sending the power series
variable `X` to a positive order element `x` and extending to infinite sums. -/
@[simps]
/--
Definition of `heval` / `heval` 的定义

English:
definition heval
  signature: : PowerSeries R ->ₐ[R] R⟦Γ⟧ where
  body: (powerSeriesFamily x f).hsum
  map_one' := by
    simp only [hsum, smulFamily_toFun, coeff_one, powers_toFun, ite_smul, one_smul, zero_smul]
    ext g
    simp only
    rw [finsum_eq_single _ (0 : Nat) (fun n hn => by simp [hn])]
    simp
  map_mul' a b := by
    simp only [← hsum_mul, hsum_powerSeriesFamily_mul]
  map_zero' := by
    simp only [hsum, smulFamily_toFun, map_zero, zero_smul,
      coeff_zero, finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    simp only [powerSeriesFamily_add, hsum_add]
  commutes' r := by
    simp only [algebraMap_eq]
    ext g
    simp only [coeff_hsum, smulFamily_toFun, coeff_C, powers_toFun, ite_smul, zero_smul]
    rw [finsum_eq_single _ 0 fun n hn => by simp [hn]]
    by_cases hg : g = 0 <;> simp [hg, Algebra.algebraMap_eq_smul_one]

中文:
定义 heval
  签名: : 幂级数 R ->ₐ[R] R⟦Γ⟧ where
  定义体: (powerSeriesFamily x f).hsum
  map_one' := by
    simp only [hsum, smulFamily_toFun, coeff_one, powers_toFun, ite_smul, one_smul, zero_smul]
    ext g
    simp only
    rw [finsum_eq_single _ (0 : Nat) (fun n hn => by simp [hn])]
    simp
  map_mul' a b := by
    simp only [← hsum_mul, hsum_powerSeriesFamily_mul]
  map_zero' := by
    simp only [hsum, smulFamily_toFun, map_zero, zero_smul,
      coeff_zero, finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    simp only [powerSeriesFamily_add, hsum_add]
  commutes' r := by
    simp only [algebraMap_eq]
    ext g
    simp only [coeff_hsum, smulFamily_toFun, coeff_C, powers_toFun, ite_smul, zero_smul]
    rw [finsum_eq_single _ 0 fun n hn => by simp [hn]]
    by_cases hg : g = 0 <;> simp [hg, Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: powerSeriesFamily
-/
def heval : PowerSeries R ->ₐ[R] R⟦Γ⟧ where
  toFun f := (powerSeriesFamily x f).hsum
  map_one' := by
    simp only [hsum, smulFamily_toFun, coeff_one, powers_toFun, ite_smul, one_smul, zero_smul]
    ext g
    simp only
    rw [finsum_eq_single _ (0 : Nat) (fun n hn => by simp [hn])]
    simp
  map_mul' a b := by
    simp only [← hsum_mul, hsum_powerSeriesFamily_mul]
  map_zero' := by
    simp only [hsum, smulFamily_toFun, map_zero, zero_smul,
      coeff_zero, finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    simp only [powerSeriesFamily_add, hsum_add]
  commutes' r := by
    simp only [algebraMap_eq]
    ext g
    simp only [coeff_hsum, smulFamily_toFun, coeff_C, powers_toFun, ite_smul, zero_smul]
    rw [finsum_eq_single _ 0 fun n hn => by simp [hn]]
    by_cases hg : g = 0 <;> simp [hg, Algebra.algebraMap_eq_smul_one]

/--
theorem `heval_mul` / 定理 `heval_mul`

English:
theorem heval_mul
  given: {a b : PowerSeries R}
  statement: heval x (a * b) = heval x a * heval x b
  proof: map_mul (heval x) a b

中文:
定理 heval_mul
  条件: {a b : 幂级数 R}
  结论: heval x (a * b) = heval x a * heval x b
  证明: map_mul (heval x) a b

Depends on / 依赖: map_mul
-/
theorem heval_mul {a b : PowerSeries R} : heval x (a * b) = heval x a * heval x b :=
  map_mul (heval x) a b

/--
theorem `heval_C` / 定理 `heval_C`

English:
theorem heval_C
  given: (r : R)
  statement: heval x (C r) = r • 1
  proof: by
  ext g
  simp only [heval_apply, coeff_hsum, smulFamily_toFun, powers_toFun, HahnSeries.coeff_smul,
    HahnSeries.coeff_one, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ 0 (fun n hn => by simp [coeff_C_of_ne_zero hn])]
  by_cases hg : g = 0 <;> simp

中文:
定理 heval_C
  条件: (r : R)
  结论: heval x (C r) = r • 1
  证明: by
  ext g
  simp only [heval_apply, coeff_hsum, smulFamily_toFun, powers_toFun, HahnSeries.coeff_smul,
    HahnSeries.coeff_one, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ 0 (fun n hn => by simp [coeff_C_of_ne_zero hn])]
  by_cases hg : g = 0 <;> simp

Depends on / 依赖: HahnSeries, HahnSeries.coeff_one, HahnSeries.coeff_smul, coeff_C_of_ne_zero, coeff_hsum, coeff_one, coeff_smul, finsum_eq_single, heval_apply, mul_ite, mul_one, mul_zero, powers_toFun, smulFamily_toFun, smul_eq_mul
-/
theorem heval_C (r : R) : heval x (C r) = r • 1 := by
  ext g
  simp only [heval_apply, coeff_hsum, smulFamily_toFun, powers_toFun, HahnSeries.coeff_smul,
    HahnSeries.coeff_one, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ 0 (fun n hn => by simp [coeff_C_of_ne_zero hn])]
  by_cases hg : g = 0 <;> simp

/--
theorem `heval_X` / 定理 `heval_X`

English:
theorem heval_X
  given: (hx : 0 < x.orderTop)
  statement: heval x X = x
  proof: by
  rw [X_eq]; rw [monomial_eq_mk]; rw [heval_apply]; rw [powerSeriesFamily]; rw [smulFamily]
  simp only [coeff_mk, powers_toFun, hx, ↓reduceIte, ite_smul, one_smul, zero_smul]
  ext g
  rw [coeff_hsum]; rw [finsum_eq_single _ 1 (fun n hn => by simp [hn])]
  simp

中文:
定理 heval_X
  条件: (hx : 0 < x.orderTop)
  结论: heval x X = x
  证明: by
  rw [X_eq]; rw [monomial_eq_mk]; rw [heval_apply]; rw [powerSeriesFamily]; rw [smulFamily]
  simp only [coeff_mk, powers_toFun, hx, ↓reduceIte, ite_smul, one_smul, zero_smul]
  ext g
  rw [coeff_hsum]; rw [finsum_eq_single _ 1 (fun n hn => by simp [hn])]
  simp

Depends on / 依赖: X_eq, coeff_hsum, coeff_mk, finsum_eq_single, heval_apply, ite_smul, monomial_eq_mk, one_smul, powerSeriesFamily, powers_toFun, reduceIte, smulFamily, zero_smul
-/
theorem heval_X (hx : 0 < x.orderTop) : heval x X = x := by
  rw [X_eq]; rw [monomial_eq_mk]; rw [heval_apply]; rw [powerSeriesFamily]; rw [smulFamily]
  simp only [coeff_mk, powers_toFun, hx, ↓reduceIte, ite_smul, one_smul, zero_smul]
  ext g
  rw [coeff_hsum]; rw [finsum_eq_single _ 1 (fun n hn => by simp [hn])]
  simp

/--
theorem `heval_unit` / 定理 `heval_unit`

English:
theorem heval_unit
  given: (u : (PowerSeries R)ˣ)
  statement: IsUnit (heval x u)
  proof: by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval x u.inv
  rw [← heval_mul]; rw [Units.val_inv]; rw [map_one]

中文:
定理 heval_unit
  条件: (u : (幂级数 R)ˣ)
  结论: 是单位 (heval x u)
  证明: by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval x u.inv
  rw [← heval_mul]; rw [Units.val_inv]; rw [map_one]

Depends on / 依赖: Units.val_inv, heval_mul, isUnit_iff_exists_inv, isUnit_iff_exists_inv.mpr, map_one, u.inv, val_inv
-/
theorem heval_unit (u : (PowerSeries R)ˣ) : IsUnit (heval x u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval x u.inv
  rw [← heval_mul]; rw [Units.val_inv]; rw [map_one]

/--
theorem `coeff_heval` / 定理 `coeff_heval`

English:
theorem coeff_heval
  given: (f : PowerSeries R) (g : Γ)
  proof: by
  rw [heval_apply]; rw [coeff_hsum]
  exact rfl

中文:
定理 coeff_heval
  条件: (f : 幂级数 R) (g : Γ)
  证明: by
  rw [heval_apply]; rw [coeff_hsum]
  exact rfl

Depends on / 依赖: coeff_hsum, heval_apply
-/
theorem coeff_heval (f : PowerSeries R) (g : Γ) :
    (heval x f).coeff g = ∑ᶠ n, ((powerSeriesFamily x f).coeff g) n := by
  rw [heval_apply]; rw [coeff_hsum]
  exact rfl

/--
theorem `coeff_heval_zero` / 定理 `coeff_heval_zero`

English:
theorem coeff_heval_zero
  given: (f : PowerSeries R)
  proof: by
  rw [coeff_heval]; rw [finsum_eq_single (fun n => ((powerSeriesFamily x f).coeff 0) n) 0]; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp
  · intro n hn
    simp only [coeff_apply, smulFamily_toFun, HahnSeries.coeff_smul, smul_eq_mul]
    refine mul_eq_zero_of_right (coeff n f) (coeff_eq_zero_of_lt_orderTop ?_)
    by_cases h : 0 < x.orderTop
    · refine (lt_of_lt_of_le ((nsmul_pos_iff hn).mpr h) ?_)
      simp [h, orderTop_nsmul_le_orderTop_pow]
    · simp [h, hn]

中文:
定理 coeff_heval_zero
  条件: (f : 幂级数 R)
  证明: by
  rw [coeff_heval]; rw [finsum_eq_single (fun n => ((powerSeriesFamily x f).coeff 0) n) 0]; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp
  · intro n hn
    simp only [coeff_apply, smulFamily_toFun, HahnSeries.coeff_smul, smul_eq_mul]
    refine mul_eq_zero_of_right (coeff n f) (coeff_eq_zero_of_lt_orderTop ?_)
    by_cases h : 0 < x.orderTop
    · refine (lt_of_lt_of_le ((nsmul_pos_iff hn).mpr h) ?_)
      simp [h, orderTop_nsmul_le_orderTop_pow]
    · simp [h, hn]

Depends on / 依赖: HahnSeries, HahnSeries.coeff_smul, PowerSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_apply, coeff_eq_zero_of_lt_orderTop, coeff_heval, coeff_smul, coeff_zero_eq_constantCoeff_apply, finsum_eq_single, lt_of_lt_of_le, mul_eq_zero_of_right, nsmul_pos_iff, orderTop, orderTop_nsmul_le_orderTop_pow, powerSeriesFamily, smulFamily_toFun, smul_eq_mul, x.orderTop
-/
theorem coeff_heval_zero (f : PowerSeries R) :
    (heval x f).coeff 0 = PowerSeries.constantCoeff f := by
  rw [coeff_heval]; rw [finsum_eq_single (fun n => ((powerSeriesFamily x f).coeff 0) n) 0]; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp
  · intro n hn
    simp only [coeff_apply, smulFamily_toFun, HahnSeries.coeff_smul, smul_eq_mul]
    refine mul_eq_zero_of_right (coeff n f) (coeff_eq_zero_of_lt_orderTop ?_)
    by_cases h : 0 < x.orderTop
    · refine (lt_of_lt_of_le ((nsmul_pos_iff hn).mpr h) ?_)
      simp [h, orderTop_nsmul_le_orderTop_pow]
    · simp [h, hn]

end PowerSeries
