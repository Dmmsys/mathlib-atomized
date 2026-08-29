/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Building GCD out of unique factorization

## Main results
* `UniqueFactorizationMonoid.toGCDMonoid`: choose a GCD monoid structure given unique factorization.
-/

@[expose] public section

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

section

open Associates UniqueFactorizationMonoid

/-- `toGCDMonoid` constructs a GCD monoid out of a unique factorization domain. -/
@[instance_reducible]
/--
Definition of `UniqueFactorizationMonoid.toGCDMonoid` / `UniqueFactorizationMonoid.toGCDMonoid` 的定义

English:
definition UniqueFactorizationMonoid.toGCDMonoid
  signature: (α : Type*) [CommMonoidWithZero α]
  body: Quot.out (Associates.mk a ⊓ Associates.mk b : Associates α)
  lcm a b := Quot.out (Associates.mk a ⊔ Associates.mk b : Associates α)
  gcd_dvd_left a b := by
    rw [← mk_dvd_mk]; rw [Associates.quot_out]; rw [congr_fun₂ dvd_eq_le]
    exact inf_le_left
  gcd_dvd_right a b := by
    rw [← mk_dvd_mk]; rw [Associates.quot_out]; rw [congr_fun₂ dvd_eq_le]
    exact inf_le_right
  dvd_gcd {a b c} hac hab := by
    rw [← mk_dvd_mk]; rw [Associates.quot_out]; rw [congr_fun₂ dvd_eq_le]; rw [le_inf_iff]; rw [mk_le_mk_iff_dvd]; rw [mk_le_mk_iff_dvd]
    exact ⟨hac, hab⟩
  lcm_zero_left a := by simp
  lcm_zero_right a := by simp
  gcd_mul_lcm a b := by
    rw [← mk_eq_mk_iff_associated]; rw [← Associates.mk_mul_mk]; rw [← associated_iff_eq]; rw [Associates.quot_out]; rw [Associates.quot_out]; rw [mul_comm]; rw [sup_mul_inf]; rw [Associates.mk_mul_mk]

中文:
定义 唯一分解幺半群.toGCDMonoid
  签名: (α : 类型) [带零交换幺半群 α]
  定义体: Quot.out (Associates.mk a ⊓ Associates.mk b : Associates α)
  lcm a b := Quot.out (Associates.mk a ⊔ Associates.mk b : Associates α)
  gcd_dvd_left a b := by
    rw [← mk_dvd_mk]; rw [Associates.quot_out]; rw [congr_fun₂ dvd_eq_le]
    exact inf_le_left
  gcd_dvd_right a b := by
    rw [← mk_dvd_mk]; rw [Associates.quot_out]; rw [congr_fun₂ dvd_eq_le]
    exact inf_le_right
  dvd_gcd {a b c} hac hab := by
    rw [← mk_dvd_mk]; rw [Associates.quot_out]; rw [congr_fun₂ dvd_eq_le]; rw [le_inf_iff]; rw [mk_le_mk_iff_dvd]; rw [mk_le_mk_iff_dvd]
    exact ⟨hac, hab⟩
  lcm_zero_left a := by simp
  lcm_zero_right a := by simp
  gcd_mul_lcm a b := by
    rw [← mk_eq_mk_iff_associated]; rw [← Associates.mk_mul_mk]; rw [← associated_iff_eq]; rw [Associates.quot_out]; rw [Associates.quot_out]; rw [mul_comm]; rw [sup_mul_inf]; rw [Associates.mk_mul_mk]

Depends on / 依赖: Associates, Associates.mk, Quot.out
-/
noncomputable def UniqueFactorizationMonoid.toGCDMonoid (α : Type*) [CommMonoidWithZero α]
    [UniqueFactorizationMonoid α] : GCDMonoid α where
  gcd a b := Quot.out (Associates.mk a ⊓ Associates.mk b : Associates α)
  lcm a b := Quot.out (Associates.mk a ⊔ Associates.mk b : Associates α)
  gcd_dvd_left a b := by
    rw [← mk_dvd_mk]; rw [Associates.quot_out]; rw [congr_fun₂ dvd_eq_le]
    exact inf_le_left
  gcd_dvd_right a b := by
    rw [← mk_dvd_mk]; rw [Associates.quot_out]; rw [congr_fun₂ dvd_eq_le]
    exact inf_le_right
  dvd_gcd {a b c} hac hab := by
    rw [← mk_dvd_mk]; rw [Associates.quot_out]; rw [congr_fun₂ dvd_eq_le]; rw [le_inf_iff]; rw [mk_le_mk_iff_dvd]; rw [mk_le_mk_iff_dvd]
    exact ⟨hac, hab⟩
  lcm_zero_left a := by simp
  lcm_zero_right a := by simp
  gcd_mul_lcm a b := by
    rw [← mk_eq_mk_iff_associated]; rw [← Associates.mk_mul_mk]; rw [← associated_iff_eq]; rw [Associates.quot_out]; rw [Associates.quot_out]; rw [mul_comm]; rw [sup_mul_inf]; rw [Associates.mk_mul_mk]

instance (priority := 100) (α) [CommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    IsGCDMonoid α := ⟨toGCDMonoid α⟩

/-- `toNormalizedGCDMonoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
@[instance_reducible]
/--
Definition of `UniqueFactorizationMonoid.toNormalizedGCDMonoid` / `UniqueFactorizationMonoid.toNormalizedGCDMonoid` 的定义

English:
definition UniqueFactorizationMonoid.toNormalizedGCDMonoid
  signature: (α : Type*)
  body: { ‹NormalizationMonoid α› with
    gcd := fun a b => (Associates.mk a ⊓ Associates.mk b).out
    lcm := fun a b => (Associates.mk a ⊔ Associates.mk b).out
gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a ⊓ Associates.mk b)).2 inf_le_left
    gcd_dvd_right := fun a b =>
(out_dvd_iff b (Associates.mk a ⊓ Associates.mk b)).2 inf_le_right
    dvd_gcd := fun {a} {b} {c} hac hab =>
      show a ∣ (Associates.mk c ⊓ Associates.mk b).out by
        rw [dvd_out_iff]; rw [le_inf_iff]; rw [mk_le_mk_iff_dvd]; rw [mk_le_mk_iff_dvd]
        exact ⟨hac, hab⟩
    lcm_zero_left := fun a => show (⊤ ⊔ Associates.mk a).out = 0 by simp
    lcm_zero_right := fun a => show (Associates.mk a ⊔ ⊤).out = 0 by simp
gcd_mul_lcm := fun a b => (out_mul' ..).symm.trans by
      rw [mul_comm]; rw [sup_mul_inf]; rw [mk_mul_mk]; rw [out_mk]
      exact normalize_associated (a * b)
    normalize_gcd := fun a b => by apply normalize_out _
    normalize_lcm := fun a b => by apply normalize_out _ }

中文:
定义 唯一分解幺半群.toNormalizedGCDMonoid
  签名: (α : 类型)
  定义体: { ‹NormalizationMonoid α› with
    gcd := fun a b => (Associates.mk a ⊓ Associates.mk b).out
    lcm := fun a b => (Associates.mk a ⊔ Associates.mk b).out
gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a ⊓ Associates.mk b)).2 inf_le_left
    gcd_dvd_right := fun a b =>
(out_dvd_iff b (Associates.mk a ⊓ Associates.mk b)).2 inf_le_right
    dvd_gcd := fun {a} {b} {c} hac hab =>
      show a ∣ (Associates.mk c ⊓ Associates.mk b).out by
        rw [dvd_out_iff]; rw [le_inf_iff]; rw [mk_le_mk_iff_dvd]; rw [mk_le_mk_iff_dvd]
        exact ⟨hac, hab⟩
    lcm_zero_left := fun a => show (⊤ ⊔ Associates.mk a).out = 0 by simp
    lcm_zero_right := fun a => show (Associates.mk a ⊔ ⊤).out = 0 by simp
gcd_mul_lcm := fun a b => (out_mul' ..).symm.trans by
      rw [mul_comm]; rw [sup_mul_inf]; rw [mk_mul_mk]; rw [out_mk]
      exact normalize_associated (a * b)
    normalize_gcd := fun a b => by apply normalize_out _
    normalize_lcm := fun a b => by apply normalize_out _ }

Depends on / 依赖: Associates, Associates.mk, NormalizationMonoid, dvd_gcd, dvd_out_iff, gcd_dvd_left, gcd_dvd_right, inf_le_left, inf_le_right, le_inf_iff, mk_le_mk_iff_, mk_le_mk_iff_dvd, out_dvd_iff
-/
noncomputable def UniqueFactorizationMonoid.toNormalizedGCDMonoid (α : Type*)
    [CommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] :
    NormalizedGCDMonoid α :=
  { ‹NormalizationMonoid α› with
    gcd := fun a b => (Associates.mk a ⊓ Associates.mk b).out
    lcm := fun a b => (Associates.mk a ⊔ Associates.mk b).out
gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a ⊓ Associates.mk b)).2 inf_le_left
    gcd_dvd_right := fun a b =>
(out_dvd_iff b (Associates.mk a ⊓ Associates.mk b)).2 inf_le_right
    dvd_gcd := fun {a} {b} {c} hac hab =>
      show a ∣ (Associates.mk c ⊓ Associates.mk b).out by
        rw [dvd_out_iff]; rw [le_inf_iff]; rw [mk_le_mk_iff_dvd]; rw [mk_le_mk_iff_dvd]
        exact ⟨hac, hab⟩
    lcm_zero_left := fun a => show (⊤ ⊔ Associates.mk a).out = 0 by simp
    lcm_zero_right := fun a => show (Associates.mk a ⊔ ⊤).out = 0 by simp
gcd_mul_lcm := fun a b => (out_mul' ..).symm.trans by
      rw [mul_comm]; rw [sup_mul_inf]; rw [mk_mul_mk]; rw [out_mk]
      exact normalize_associated (a * b)
    normalize_gcd := fun a b => by apply normalize_out _
    normalize_lcm := fun a b => by apply normalize_out _ }

/--
Definition of `UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid` / `UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid` 的定义

English:
abbreviation UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid
  signature: (α : Type*)
  body: toNormalizedGCDMonoid α
  __ := ‹StrongNormalizationMonoid α›

中文:
缩写 唯一分解幺半群.toStrongNormalizedGCDMonoid
  签名: (α : 类型)
  定义体: toNormalizedGCDMonoid α
  __ := ‹StrongNormalizationMonoid α›

Depends on / 依赖: toNormalizedGCDMonoid
-/
noncomputable abbrev UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid (α : Type*)
    [CommMonoidWithZero α] [UniqueFactorizationMonoid α] [StrongNormalizationMonoid α] :
    StrongNormalizedGCDMonoid α where
  __ := toNormalizedGCDMonoid α
  __ := ‹StrongNormalizationMonoid α›

end
