/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Basic results on integral ideals of a number field

We study results about integral ideals of a number field `K`.

## Main definitions and results

* `Ideal.rootsOfUnityMapQuot` : For `I` an integral ideal of `K`, the group morphism from the
  group of roots of unity of `K` of order `n` to `(𝓞 K ⧸ I)ˣ`.

* `Ideal.rootsOfUnityMapQuot_injective`: If the ideal `I` is nontrivial and its norm is coprime
  with `n`, then the map `Ideal.rootsOfUnityMapQuot` is injective.

* `NumberField.torsionOrder_dvd_absNorm_sub_one`: If the norm of the (nonzero) prime ideal `P` is
  coprime with the order of the torsion of `K`, then the norm of `P` is congruent to `1` modulo
  `torsionOrder K`.

-/

@[expose] public section

open Ideal NumberField Units

variable {K : Type*} [Field K] {I : Ideal (𝓞 K)}

section torsionMapQuot

/--
theorem `IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one` / 定理 `IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one`

English:
theorem IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one
  statement: [NumberField K] (hI : absNorm I != 1) {n : Nat}
  proof: by
  intro h₁
  rw [← map_one (Ideal.Quotient.mk I)]; rw [Ideal.Quotient.eq] at h
  obtain ⟨p, hp, h₂⟩ := Nat.exists_prime_and_dvd hI
  have : Fact (p.Prime) := ⟨hp⟩
refine hp.not_dvd_one h₁ ▸ Nat.dvd_gcd h₂ ?_
exact hζ.prime_dvd_of_dvd_norm_sub_one hn
    Int.dvd_trans (Int.natCast_dvd_natCast.mpr 

中文:
定理 是PrimitiveRoot.not_coprime_norm_of_mk_eq_one
  结论: [数域 K] (hI : absNorm I != 1) {n : 自然数}
  证明: by
  intro h₁
  rw [← map_one (Ideal.Quotient.mk I)]; rw [Ideal.Quotient.eq] at h
  obtain ⟨p, hp, h₂⟩ := Nat.exists_prime_and_dvd hI
  have : Fact (p.Prime) := ⟨hp⟩
refine hp.not_dvd_one h₁ ▸ Nat.dvd_gcd h₂ ?_
exact hζ.prime_dvd_of_dvd_norm_sub_one hn
    Int.dvd_trans (Int.natCast_dvd_natCast.mpr 

Depends on / 依赖: Ideal.Quotient.mk, NeZero, NeZero.of_gt, Quotient, of_gt, toInteger
-/
theorem IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one [NumberField K] (hI : absNorm I != 1) {n : Nat}
    {ζ : K} (hn : 2 <= n) (hζ : IsPrimitiveRoot ζ n)
    (h : letI _ : NeZero n := NeZero.of_gt hn; Ideal.Quotient.mk I hζ.toInteger = 1) :
    ¬ (absNorm I).Coprime n := by
  intro h₁
  rw [← map_one (Ideal.Quotient.mk I)]; rw [Ideal.Quotient.eq] at h
  obtain ⟨p, hp, h₂⟩ := Nat.exists_prime_and_dvd hI
  have : Fact (p.Prime) := ⟨hp⟩
refine hp.not_dvd_one h₁ ▸ Nat.dvd_gcd h₂ ?_
exact hζ.prime_dvd_of_dvd_norm_sub_one hn
    Int.dvd_trans (Int.natCast_dvd_natCast.mpr h₂) (absNorm_dvd_norm_of_mem h)

variable (I)

/--
Definition of `Ideal.rootsOfUnityMapQuot` / `Ideal.rootsOfUnityMapQuot` 的定义

English:
definition Ideal.rootsOfUnityMapQuot
  signature: (n : Nat)
  body: (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict _

@[simp]

中文:
定义 理想.rootsOfUnityMapQuot
  签名: (n : 自然数)
  定义体: (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict _

@[simp]

Depends on / 依赖: Ideal.Quotient.mk, Quotient, Units.map, domRestrict, toMonoidHom
-/
def Ideal.rootsOfUnityMapQuot (n : Nat) : (rootsOfUnity n (𝓞 K)) ->* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict _

@[simp]
/--
theorem `Ideal.rootsOfUnityMapQuot_apply` / 定理 `Ideal.rootsOfUnityMapQuot_apply`

English:
theorem Ideal.rootsOfUnityMapQuot_apply
  given: (n : Nat) {x : (𝓞 K)ˣ} (hx : x in rootsOfUnity n (𝓞 K))
  proof: rfl

中文:
定理 理想.rootsOfUnityMapQuot_apply
  条件: (n : 自然数) {x : (𝓞 K)ˣ} (hx : x in rootsOfUnity n (𝓞 K))
  证明: rfl
-/
theorem Ideal.rootsOfUnityMapQuot_apply (n : Nat) {x : (𝓞 K)ˣ} (hx : x in rootsOfUnity n (𝓞 K)) :
    rootsOfUnityMapQuot I n ⟨x, hx⟩ = Ideal.Quotient.mk I x := rfl

/--
Definition of `Ideal.torsionMapQuot` / `Ideal.torsionMapQuot` 的定义

English:
definition Ideal.torsionMapQuot
  signature: : (Units.torsion K) ->* ((𝓞 K) ⧸ I)ˣ
  body: (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict (torsion K)

@[simp]

中文:
定义 理想.torsionMapQuot
  签名: : (单位群.torsion K) ->* ((𝓞 K) ⧸ I)ˣ
  定义体: (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict (torsion K)

@[simp]

Depends on / 依赖: Ideal.Quotient.mk, Quotient, Units.map, domRestrict, toMonoidHom, torsion
-/
def Ideal.torsionMapQuot : (Units.torsion K) ->* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict (torsion K)

@[simp]
/--
theorem `Ideal.torsionMapQuot_apply` / 定理 `Ideal.torsionMapQuot_apply`

English:
theorem Ideal.torsionMapQuot_apply
  given: {x : (𝓞 K)ˣ} (hx : x in torsion K)
  proof: rfl

中文:
定理 理想.torsionMapQuot_apply
  条件: {x : (𝓞 K)ˣ} (hx : x in torsion K)
  证明: rfl
-/
theorem Ideal.torsionMapQuot_apply {x : (𝓞 K)ˣ} (hx : x in torsion K) :
    torsionMapQuot I ⟨x, hx⟩ = Ideal.Quotient.mk I x := rfl

variable {I} [NumberField K]

/--
theorem `Ideal.rootsOfUnityMapQuot_injective` / 定理 `Ideal.rootsOfUnityMapQuot_injective`

English:
theorem Ideal.rootsOfUnityMapQuot_injective
  statement: (n : Nat) [NeZero n] (hI₁ : absNorm I != 1)
  proof: by
  refine (injective_iff_map_eq_one _).mpr fun ⟨ζ, hζ⟩ h => ?_
  obtain ⟨t, ht₀, ht, hζ⟩ := isPrimitiveRoot_of_mem_rootsOfUnity hζ
  suffices ¬ (2 <= t) by
    simpa [show t = 1 by grind] using hζ
  intro ht'
  let μ : K := ζ.val
  have hμ : IsPrimitiveRoot μ t :=
    (IsPrimitiveRoot.coe_units_if

中文:
定理 理想.rootsOfUnityMapQuot_injective
  结论: (n : 自然数) [NeZero n] (hI₁ : absNorm I != 1)
  证明: by
  refine (injective_iff_map_eq_one _).mpr fun ⟨ζ, hζ⟩ h => ?_
  obtain ⟨t, ht₀, ht, hζ⟩ := isPrimitiveRoot_of_mem_rootsOfUnity hζ
  suffices ¬ (2 <= t) by
    simpa [show t = 1 by grind] using hζ
  intro ht'
  let μ : K := ζ.val
  have hμ : IsPrimitiveRoot μ t :=
    (IsPrimitiveRoot.coe_units_if

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.coe_units_iff.mpr, Nat.dvd_one.mp, Nat.gcd, RingOfIntegers, RingOfIntegers.coe_injective, Units.ext_iff, Units.val_one, coe_injective, coe_units_iff, dvd_one, ext_iff, injective_iff_map_eq_one, isPrimitiveRoot_of_mem_rootsOfUnity, map_of_injective, not_coprime_norm_of_mk_eq_one, rootsOfUnityMapQuot_apply, val_one
-/
theorem Ideal.rootsOfUnityMapQuot_injective (n : Nat) [NeZero n] (hI₁ : absNorm I != 1)
    (hI₂ : (absNorm I).Coprime n) :
    Function.Injective (rootsOfUnityMapQuot I n) := by
  refine (injective_iff_map_eq_one _).mpr fun ⟨ζ, hζ⟩ h => ?_
  obtain ⟨t, ht₀, ht, hζ⟩ := isPrimitiveRoot_of_mem_rootsOfUnity hζ
  suffices ¬ (2 <= t) by
    simpa [show t = 1 by grind] using hζ
  intro ht'
  let μ : K := ζ.val
  have hμ : IsPrimitiveRoot μ t :=
    (IsPrimitiveRoot.coe_units_iff.mpr hζ).map_of_injective RingOfIntegers.coe_injective
  rw [Units.ext_iff]; rw [rootsOfUnityMapQuot_apply]; rw [Units.val_one] at h
  refine hμ.not_coprime_norm_of_mk_eq_one hI₁ ht' h ?_
  exact Nat.dvd_one.mp (hI₂ ▸ Nat.gcd_dvd_gcd_of_dvd_right (absNorm I) ht)

/--
theorem `IsPrimitiveRoot.idealQuotient_mk` / 定理 `IsPrimitiveRoot.idealQuotient_mk`

English:
theorem IsPrimitiveRoot.idealQuotient_mk
  statement: {n : Nat} [NeZero n] {ζ : (𝓞 K)} (hζ : IsPrimitiveRoot ζ n)
  proof: by
  have h : IsPrimitiveRoot hζ.toRootsOfUnity n :=
IsPrimitiveRoot.coe_submonoidClass_iff.mp IsPrimitiveRoot.coe_units_iff.mp hζ
exact IsPrimitiveRoot.coe_units_iff.mpr
h.map_of_injective Ideal.rootsOfUnityMapQuot_injective n hI₁ hI₂

中文:
定理 是PrimitiveRoot.idealQuotient_mk
  结论: {n : 自然数} [NeZero n] {ζ : (𝓞 K)} (hζ : 是PrimitiveRoot ζ n)
  证明: by
  have h : IsPrimitiveRoot hζ.toRootsOfUnity n :=
IsPrimitiveRoot.coe_submonoidClass_iff.mp IsPrimitiveRoot.coe_units_iff.mp hζ
exact IsPrimitiveRoot.coe_units_iff.mpr
h.map_of_injective Ideal.rootsOfUnityMapQuot_injective n hI₁ hI₂

Depends on / 依赖: Ideal.rootsOfUnityMapQuot_injective, IsPrimitiveRoot, IsPrimitiveRoot.coe_submonoidClass_iff.mp, IsPrimitiveRoot.coe_units_iff.mp, IsPrimitiveRoot.coe_units_iff.mpr, coe_submonoidClass_iff, coe_units_iff, h.map_of_injective, map_of_injective, rootsOfUnityMapQuot_injective, toRootsOfUnity
-/
theorem IsPrimitiveRoot.idealQuotient_mk {n : Nat} [NeZero n] {ζ : (𝓞 K)} (hζ : IsPrimitiveRoot ζ n)
    (hI₁ : absNorm I != 1) (hI₂ : (absNorm I).Coprime n) :
    IsPrimitiveRoot (Ideal.Quotient.mk I ζ) n := by
  have h : IsPrimitiveRoot hζ.toRootsOfUnity n :=
IsPrimitiveRoot.coe_submonoidClass_iff.mp IsPrimitiveRoot.coe_units_iff.mp hζ
exact IsPrimitiveRoot.coe_units_iff.mpr
h.map_of_injective Ideal.rootsOfUnityMapQuot_injective n hI₁ hI₂

/--
theorem `Ideal.torsionMapQuot_injective` / 定理 `Ideal.torsionMapQuot_injective`

English:
theorem Ideal.torsionMapQuot_injective
  statement: (hI₁ : absNorm I != 1)
  proof: by
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  rw [← rootsOfUnity_eq_torsion] at hx hy
  rw [Subtype.mk_eq_mk]; rw [← Subtype.mk_eq_mk (h := hx) (h' := hy)]
  exact rootsOfUnityMapQuot_injective (torsionOrder K) hI₁ hI₂ h

中文:
定理 理想.torsionMapQuot_injective
  结论: (hI₁ : absNorm I != 1)
  证明: by
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  rw [← rootsOfUnity_eq_torsion] at hx hy
  rw [Subtype.mk_eq_mk]; rw [← Subtype.mk_eq_mk (h := hx) (h' := hy)]
  exact rootsOfUnityMapQuot_injective (torsionOrder K) hI₁ hI₂ h

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, mk_eq_mk, rootsOfUnityMapQuot_injective, rootsOfUnity_eq_torsion, torsionOrder
-/
theorem Ideal.torsionMapQuot_injective (hI₁ : absNorm I != 1)
    (hI₂ : (absNorm I).Coprime (torsionOrder K)) :
    Function.Injective (torsionMapQuot I) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  rw [← rootsOfUnity_eq_torsion] at hx hy
  rw [Subtype.mk_eq_mk]; rw [← Subtype.mk_eq_mk (h := hx) (h' := hy)]
  exact rootsOfUnityMapQuot_injective (torsionOrder K) hI₁ hI₂ h

/--
theorem `NumberField.torsionOrder_dvd_absNorm_sub_one` / 定理 `NumberField.torsionOrder_dvd_absNorm_sub_one`

English:
theorem NumberField.torsionOrder_dvd_absNorm_sub_one
  statement: {P : Ideal (𝓞 K)} (hP₀ : P != ⊥)
  proof: by
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP₁
  let _ := Ideal.Quotient.field P
have hP₃ : absNorm P != 1 := absNorm_eq_one_iff.not.mpr IsPrime.ne_top hP₁
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective hP₃ hP₂)
  rwa [Nat.card_units] at h

中文:
定理 数域.torsionOrder_dvd_absNorm_sub_one
  结论: {P : 理想 (𝓞 K)} (hP₀ : P != ⊥)
  证明: by
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP₁
  let _ := Ideal.Quotient.field P
have hP₃ : absNorm P != 1 := absNorm_eq_one_iff.not.mpr IsPrime.ne_top hP₁
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective hP₃ hP₂)
  rwa [Nat.card_units] at h

Depends on / 依赖: DimensionLEOne, Ideal.Quotient.field, IsMaximal, IsPrime, IsPrime.ne_top, Nat.card_units, P.IsMaximal, Quotient, Ring.DimensionLEOne.maximalOfPrime, Subgroup, Subgroup.card_dvd_of_injective, absNorm, absNorm_eq_one_iff, absNorm_eq_one_iff.not.mpr, card_dvd_of_injective, card_units, maximalOfPrime, ne_top, torsionMapQuot_injective
-/
theorem NumberField.torsionOrder_dvd_absNorm_sub_one {P : Ideal (𝓞 K)} (hP₀ : P != ⊥)
    (hP₁ : P.IsPrime) (hP₂ : (absNorm P).Coprime (torsionOrder K)) :
    torsionOrder K ∣ absNorm P - 1 := by
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP₁
  let _ := Ideal.Quotient.field P
have hP₃ : absNorm P != 1 := absNorm_eq_one_iff.not.mpr IsPrime.ne_top hP₁
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective hP₃ hP₂)
  rwa [Nat.card_units] at h

end torsionMapQuot

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NumberField
  signature: K] [I.IsMaximal] : Finite (𝓞 K ⧸ I)
  body: I.finiteQuotientOfFreeOfNeBot (I.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'

中文:
实例 [数域
  签名: K] [I.是极大] : 有限 (𝓞 K ⧸ I)
  定义体: I.finiteQuotientOfFreeOfNeBot (I.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
-/
instance [NumberField K] [I.IsMaximal] : Finite (𝓞 K ⧸ I) :=
  I.finiteQuotientOfFreeOfNeBot (I.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
