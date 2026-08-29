/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.Padics.WithVal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Isomorphisms between `adicCompletion ℚ` and `ℚ_[p]`

Let `R` have field of fractions `ℚ`. If `v : HeightOneSpectrum R`, then `v.adicCompletion ℚ` is
the uniform space completion of `ℚ` with respect to the `v`-adic valuation.
On the other hand, `ℚ_[p]` is the `p`-adic numbers, defined as the completion of `ℚ` with respect
to the `p`-adic norm using the completion of Cauchy sequences. This file constructs continuous
`ℚ`-algebra isomorphisms between the two, as well as continuous `ℤ`-algebra isomorphisms for their
respective rings of integers.

Isomorphisms are provided in both directions, allowing traversal of the following diagram:
```
HeightOneSpectrum R <-----------> Nat.Primes
          | |
          | |
          v v
v.adicCompletionIntegers ℚ <-------> ℤ_[p]
          | |
          | |
          v v
v.adicCompletion ℚ <---------------> ℚ_[p]
```

## Main definitions
- `Rat.HeightOneSpectrum.primesEquiv` : the equivalence between height-one prime ideals of
  `R` and prime numbers in `ℕ`.
- `Rat.HeightOneSpectrum.padicEquiv v` : the continuous `ℚ`-algebra isomorphism
  `v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v]`.
- `Padic.adicCompletionEquiv p` : the continuous `ℚ`-algebra isomorphism
  `ℚ_[p] ≃A[ℚ] (primesEquiv.symm p).adicCompletion ℚ`.
- `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v` : the continuous `ℤ`-algebra
  isomorphism `v.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[natGenerator v]`.
- `PadicInt.adicCompletionIntegersEquiv p` : the continuous `ℤ`-algebra isomorphism
  `ℤ_[p] ≃A[ℤ] (primesEquiv.symm p).adicCompletionIntegers ℚ`.

TODO : Abstract the isomorphisms in this file using a universal predicate on adic completions,
along the lines of `IsComplete` + uniformity arises from a valuation + the valuations are
equivalent. It is best to do this after `Valued` has been refactored, or at least after
`adicCompletion` has `IsValuativeTopology` instance.
-/

@[expose] public section

open IsDedekindDomain UniformSpace.Completion NumberField PadicInt

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

variable (R : Type*) [CommRing R] [Algebra R Rat]

/--
theorem `Rat.int_algebraMap_injective` / 定理 `Rat.int_algebraMap_injective`

English:
theorem Rat.int_algebraMap_injective
  statement: Function.Injective (algebraMap Int R)
  proof: .of_comp (IsScalarTower.algebraMap_eq Int R Rat ▸ RingHom.injective_int (algebraMap Int Rat))

中文:
定理 有理数.int_algebraMap_injective
  结论: 函数.单射 (algebraMap 整数 R)
  证明: .of_comp (IsScalarTower.algebraMap_eq Int R Rat ▸ RingHom.injective_int (algebraMap Int Rat))

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, RingHom, RingHom.injective_int, algebraMap, algebraMap_eq, injective_int, of_comp
-/
theorem Rat.int_algebraMap_injective : Function.Injective (algebraMap Int R) :=
  .of_comp (IsScalarTower.algebraMap_eq Int R Rat ▸ RingHom.injective_int (algebraMap Int Rat))

variable [IsIntegralClosure R Int Rat]

/--
theorem `Rat.int_algebraMap_surjective` / 定理 `Rat.int_algebraMap_surjective`

English:
theorem Rat.int_algebraMap_surjective
  given: [IsFractionRing R Rat]
  proof: by
  intro x
obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    IsIntegral.algebraMap (B := Rat) (IsIntegralClosure.isIntegral Int Rat x)
exact ⟨y, IsFractionRing.injective R Rat by simp only [← IsScalarTower.algebraMap_apply, hy]⟩

中文:
定理 有理数.int_algebraMap_surjective
  条件: [IsFractionRing R 有理数]
  证明: by
  intro x
obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    IsIntegral.algebraMap (B := Rat) (IsIntegralClosure.isIntegral Int Rat x)
exact ⟨y, IsFractionRing.injective R Rat by simp only [← IsScalarTower.algebraMap_apply, hy]⟩

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, IsIntegral, IsIntegral.algebraMap, IsIntegralClosure, IsIntegralClosure.isIntegral, IsIntegrallyClosed, IsIntegrallyClosed.isIntegral_iff, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply, injective, isIntegral, isIntegral_iff
-/
theorem Rat.int_algebraMap_surjective [IsFractionRing R Rat] :
    Function.Surjective (algebraMap Int R) := by
  intro x
obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    IsIntegral.algebraMap (B := Rat) (IsIntegralClosure.isIntegral Int Rat x)
exact ⟨y, IsFractionRing.injective R Rat by simp only [← IsScalarTower.algebraMap_apply, hy]⟩

/--
Definition of `Rat.IsIntegralClosure.intEquiv` / `Rat.IsIntegralClosure.intEquiv` 的定义

English:
definition Rat.IsIntegralClosure.intEquiv
  signature: : R ≃+* Int
  body: (NumberField.RingOfIntegers.equiv R).symm.trans ringOfIntegersEquiv

@[simp]

中文:
定义 有理数.是整闭包.intEquiv
  签名: : R ≃+* 整数
  定义体: (NumberField.RingOfIntegers.equiv R).symm.trans ringOfIntegersEquiv

@[simp]

Depends on / 依赖: NumberField, NumberField.RingOfIntegers.equiv, RingOfIntegers, ringOfIntegersEquiv, symm.trans
-/
noncomputable def Rat.IsIntegralClosure.intEquiv : R ≃+* Int :=
  (NumberField.RingOfIntegers.equiv R).symm.trans ringOfIntegersEquiv

@[simp]
/--
theorem `Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv` / 定理 `Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv`

English:
theorem Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv
  given: (x : 𝓞 Rat)
  proof: by
  simp [intEquiv, RingOfIntegers.equiv, IsIntegralClosure.equiv, IsIntegralClosure.lift,
    IsIntegralClosure.mk']

中文:
定理 有理数.是整闭包.intEquiv_apply_eq_ringOf整数egersEquiv
  条件: (x : 𝓞 有理数)
  证明: by
  simp [intEquiv, RingOfIntegers.equiv, IsIntegralClosure.equiv, IsIntegralClosure.lift,
    IsIntegralClosure.mk']

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.equiv, IsIntegralClosure.lift, IsIntegralClosure.mk, RingOfIntegers, RingOfIntegers.equiv, intEquiv
-/
theorem Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv (x : 𝓞 Rat) :
    intEquiv (𝓞 Rat) x = ringOfIntegersEquiv x := by
  simp [intEquiv, RingOfIntegers.equiv, IsIntegralClosure.equiv, IsIntegralClosure.lift,
    IsIntegralClosure.mk']

namespace Rat.HeightOneSpectrum

variable {R : Type*} [CommRing R] [Algebra R Rat] [IsIntegralClosure R Int Rat]

/--
Definition of `natGenerator` / `natGenerator` 的定义

English:
definition natGenerator
  signature: (v : HeightOneSpectrum R)
  body: .natAbs Submodule.IsPrincipal.generator (v.asIdeal.map <| IsIntegralClosure.intEquiv R)

中文:
定义 natGenerator
  签名: (v : 高一谱 R)
  定义体: .natAbs Submodule.IsPrincipal.generator (v.asIdeal.map <| IsIntegralClosure.intEquiv R)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.intEquiv, IsPrincipal, Submodule, Submodule.IsPrincipal.generator, asIdeal, generator, intEquiv, natAbs, v.asIdeal.map
-/
noncomputable def natGenerator (v : HeightOneSpectrum R) : Nat :=
.natAbs Submodule.IsPrincipal.generator (v.asIdeal.map <| IsIntegralClosure.intEquiv R)

/--
theorem `span_natGenerator` / 定理 `span_natGenerator`

English:
theorem span_natGenerator
  given: (v : HeightOneSpectrum R)
  proof: by
  simp [natGenerator]

中文:
定理 span_natGenerator
  条件: (v : 高一谱 R)
  证明: by
  simp [natGenerator]

Depends on / 依赖: natGenerator
-/
theorem span_natGenerator (v : HeightOneSpectrum R) :
    Ideal.span {(natGenerator v : Int)} = v.asIdeal.map (IsIntegralClosure.intEquiv R) := by
  simp [natGenerator]

/--
theorem `natGenerator_dvd_iff` / 定理 `natGenerator_dvd_iff`

English:
theorem natGenerator_dvd_iff
  given: (v : HeightOneSpectrum R) {n : Nat}
  proof: by
  rw [← span_natGenerator]; rw [Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

中文:
定理 natGenerator_dvd_iff
  条件: (v : 高一谱 R) {n : 自然数}
  证明: by
  rw [← span_natGenerator]; rw [Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

Depends on / 依赖: Ideal.mem_span_singleton, Int.ofNat_dvd.symm, mem_span_singleton, ofNat_dvd, span_natGenerator
-/
theorem natGenerator_dvd_iff (v : HeightOneSpectrum R) {n : Nat} :
    natGenerator v ∣ n ↔ ↑n in v.asIdeal.map (IsIntegralClosure.intEquiv R) := by
  rw [← span_natGenerator]; rw [Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

/--
theorem `prime_natGenerator` / 定理 `prime_natGenerator`

English:
theorem prime_natGenerator
  given: (v : HeightOneSpectrum R)
  statement: Nat.Prime (natGenerator v)
  proof: Int.prime_iff_natAbs_prime.1 Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective (IsIntegralClosure.intEquiv R).injective).not.2 v.ne_bot)

中文:
定理 prime_natGenerator
  条件: (v : 高一谱 R)
  结论: 自然数.素 (natGenerator v)
  证明: Int.prime_iff_natAbs_prime.1 Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective (IsIntegralClosure.intEquiv R).injective).not.2 v.ne_bot)

Depends on / 依赖: Ideal.map_eq_bot_iff_of_injective, Int.prime_iff_natAbs_prime, IsIntegralClosure, IsIntegralClosure.intEquiv, IsPrincipal, Submodule, Submodule.IsPrincipal.prime_generator_of_isPrime, injective, intEquiv, map_eq_bot_iff_of_injective, ne_bot, prime_generator_of_isPrime, prime_iff_natAbs_prime, v.ne_bot
-/
theorem prime_natGenerator (v : HeightOneSpectrum R) : Nat.Prime (natGenerator v) :=
Int.prime_iff_natAbs_prime.1 Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective (IsIntegralClosure.intEquiv R).injective).not.2 v.ne_bot)

variable [IsDedekindDomain R] [IsFractionRing R Rat]

/--
Definition of `primesEquiv` / `primesEquiv` 的定义

English:
definition primesEquiv
  signature: : HeightOneSpectrum R ≃ Nat.Primes where
  body: ⟨natGenerator v, prime_natGenerator v⟩
  invFun p :=
    have h : Prime ((Ideal.span {(p.1 : Int)}).map (IsIntegralClosure.intEquiv R).symm) :=
      Ideal.map_prime_of_equiv _ (by simp [← Nat.prime_iff_prime_int, p.2]) (by simp [p.2.ne_zero])
    .ofPrime h
  left_inv v := by
    simp only [Ideal.map_symm]
    congr
    rw [← v.asIdeal.comap_map_of_bijective _ (IsIntegralClosure.intEquiv R).bijective]; rw [← span_natGenerator]
  right_inv p := by
    simp only [Ideal.map_symm, natGenerator, HeightOneSpectrum.ofPrime_asIdeal]
    congr
    simp [Ideal.map_comap_of_surjective _ (IsIntegralClosure.intEquiv R).surjective,
      Int.associated_iff_natAbs.1 (Submodule.IsPrincipal.associated_generator_span_self _)]

中文:
定义 primesEquiv
  签名: : 高一谱 R ≃ 自然数.Primes where
  定义体: ⟨natGenerator v, prime_natGenerator v⟩
  invFun p :=
    have h : Prime ((Ideal.span {(p.1 : Int)}).map (IsIntegralClosure.intEquiv R).symm) :=
      Ideal.map_prime_of_equiv _ (by simp [← Nat.prime_iff_prime_int, p.2]) (by simp [p.2.ne_zero])
    .ofPrime h
  left_inv v := by
    simp only [Ideal.map_symm]
    congr
    rw [← v.asIdeal.comap_map_of_bijective _ (IsIntegralClosure.intEquiv R).bijective]; rw [← span_natGenerator]
  right_inv p := by
    simp only [Ideal.map_symm, natGenerator, HeightOneSpectrum.ofPrime_asIdeal]
    congr
    simp [Ideal.map_comap_of_surjective _ (IsIntegralClosure.intEquiv R).surjective,
      Int.associated_iff_natAbs.1 (Submodule.IsPrincipal.associated_generator_span_self _)]

Depends on / 依赖: natGenerator, prime_natGenerator
-/
noncomputable def primesEquiv : HeightOneSpectrum R ≃ Nat.Primes where
  toFun v := ⟨natGenerator v, prime_natGenerator v⟩
  invFun p :=
    have h : Prime ((Ideal.span {(p.1 : Int)}).map (IsIntegralClosure.intEquiv R).symm) :=
      Ideal.map_prime_of_equiv _ (by simp [← Nat.prime_iff_prime_int, p.2]) (by simp [p.2.ne_zero])
    .ofPrime h
  left_inv v := by
    simp only [Ideal.map_symm]
    congr
    rw [← v.asIdeal.comap_map_of_bijective _ (IsIntegralClosure.intEquiv R).bijective]; rw [← span_natGenerator]
  right_inv p := by
    simp only [Ideal.map_symm, natGenerator, HeightOneSpectrum.ofPrime_asIdeal]
    congr
    simp [Ideal.map_comap_of_surjective _ (IsIntegralClosure.intEquiv R).surjective,
      Int.associated_iff_natAbs.1 (Submodule.IsPrincipal.associated_generator_span_self _)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `valuation_equiv_padicValuation` / 定理 `valuation_equiv_padicValuation`

English:
theorem valuation_equiv_padicValuation
  given: (v : HeightOneSpectrum R)
  proof: by
  simp [primesEquiv, Valuation.isEquiv_iff_val_le_one, valuation_le_one_iff_den,
    padicValuation_le_one_iff, natGenerator_dvd_iff,
    map_natCast (IsIntegralClosure.intEquiv R) _ ▸ Ideal.apply_mem_of_equiv_iff]

中文:
定理 valuation_equiv_padicValuation
  条件: (v : 高一谱 R)
  证明: by
  simp [primesEquiv, Valuation.isEquiv_iff_val_le_one, valuation_le_one_iff_den,
    padicValuation_le_one_iff, natGenerator_dvd_iff,
    map_natCast (IsIntegralClosure.intEquiv R) _ ▸ Ideal.apply_mem_of_equiv_iff]

Depends on / 依赖: Ideal.apply_mem_of_equiv_iff, IsIntegralClosure, IsIntegralClosure.intEquiv, Valuation, Valuation.isEquiv_iff_val_le_one, apply_mem_of_equiv_iff, intEquiv, isEquiv_iff_val_le_one, map_natCast, natGenerator_dvd_iff, padicValuation_le_one_iff, primesEquiv, valuation_le_one_iff_den
-/
theorem valuation_equiv_padicValuation (v : HeightOneSpectrum R) :
    (v.valuation Rat).IsEquiv (padicValuation (primesEquiv v)) := by
  simp [primesEquiv, Valuation.isEquiv_iff_val_le_one, valuation_le_one_iff_den,
    padicValuation_le_one_iff, natGenerator_dvd_iff,
    map_natCast (IsIntegralClosure.intEquiv R) _ ▸ Ideal.apply_mem_of_equiv_iff]

open Valuation

/--
Definition of `withValEquiv` / `withValEquiv` 的定义

English:
definition withValEquiv
  signature: (v : HeightOneSpectrum R)
  body: (valuation_equiv_padicValuation v).uniformEquiv

中文:
定义 withValEquiv
  签名: (v : 高一谱 R)
  定义体: (valuation_equiv_padicValuation v).uniformEquiv

Depends on / 依赖: uniformEquiv, valuation_equiv_padicValuation
-/
noncomputable def withValEquiv (v : HeightOneSpectrum R) :
    WithVal (v.valuation Rat) ≃ᵤ WithVal (padicValuation (primesEquiv v)) :=
  (valuation_equiv_padicValuation v).uniformEquiv

/--
Definition of `adicCompletion.padicEquiv` / `adicCompletion.padicEquiv` 的定义

English:
definition adicCompletion.padicEquiv
  signature: (v : HeightOneSpectrum R)
  body: (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv Rat v).trans
    (mapRingEquiv _ (withValEquiv v).continuous
      (withValEquiv v).symm.continuous).trans Padic.withValRingEquiv
  __ := ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv Rat v).trans <|
    (mapEquiv (withValEquiv v)).trans Padic.withValUniformEquiv).toHomeomorph
  commutes' := by simp

中文:
定义 adicCompletion.padicEquiv
  签名: (v : 高一谱 R)
  定义体: (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv Rat v).trans
    (mapRingEquiv _ (withValEquiv v).continuous
      (withValEquiv v).symm.continuous).trans Padic.withValRingEquiv
  __ := ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv Rat v).trans <|
    (mapEquiv (withValEquiv v)).trans Padic.withValUniformEquiv).toHomeomorph
  commutes' := by simp

Depends on / 依赖: HeightOneSpectrum, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv, adicCompletion
-/
noncomputable def adicCompletion.padicEquiv (v : HeightOneSpectrum R) :
    v.adicCompletion Rat ≃A[Rat] Rat_[primesEquiv v] where
__ := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv Rat v).trans
    (mapRingEquiv _ (withValEquiv v).continuous
      (withValEquiv v).symm.continuous).trans Padic.withValRingEquiv
  __ := ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv Rat v).trans <|
    (mapEquiv (withValEquiv v)).trans Padic.withValUniformEquiv).toHomeomorph
  commutes' := by simp

/--
Definition of `adicCompletionIntegers.padicIntEquiv` / `adicCompletionIntegers.padicIntEquiv` 的定义

English:
definition adicCompletionIntegers.padicIntEquiv
  signature: (v : HeightOneSpectrum R)
  body: let e0 := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv Rat v).restrict
          (v.adicCompletionIntegers Rat)
          (Valued.v (R := (v.valuation Rat).Completion)).valuationSubring
          fun _ => by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; rfl
        let e := (mapRingEquiv _ (withValEquiv v).continuous
          (withValEquiv v).symm.continuous).restrict _ _ fun _ => by
            simpa using! (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        (e0.trans e).trans withValIntegersRingEquiv
  __ := let e0 := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv Rat v).subtype
          fun _ => by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; rfl
        let e := (mapEquiv (withValEquiv v)).subtype fun _ => by
          simpa using! (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        ((e0.trans e).trans withValIntegersUniformEquiv).toHomeomorph
  commutes' := by simp

中文:
定义 adicCompletion整数egers.padic整数Equiv
  签名: (v : 高一谱 R)
  定义体: let e0 := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv Rat v).restrict
          (v.adicCompletionIntegers Rat)
          (Valued.v (R := (v.valuation Rat).Completion)).valuationSubring
          fun _ => by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; rfl
        let e := (mapRingEquiv _ (withValEquiv v).continuous
          (withValEquiv v).symm.continuous).restrict _ _ fun _ => by
            simpa using! (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        (e0.trans e).trans withValIntegersRingEquiv
  __ := let e0 := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv Rat v).subtype
          fun _ => by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; rfl
        let e := (mapEquiv (withValEquiv v)).subtype fun _ => by
          simpa using! (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        ((e0.trans e).trans withValIntegersUniformEquiv).toHomeomorph
  commutes' := by simp

Depends on / 依赖: HeightOneSpectrum, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv, adicCompletion, restrict
-/
noncomputable def adicCompletionIntegers.padicIntEquiv (v : HeightOneSpectrum R) :
    v.adicCompletionIntegers Rat ≃A[Int] Int_[primesEquiv v] where
  __ := let e0 := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv Rat v).restrict
          (v.adicCompletionIntegers Rat)
          (Valued.v (R := (v.valuation Rat).Completion)).valuationSubring
          fun _ => by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; rfl
        let e := (mapRingEquiv _ (withValEquiv v).continuous
          (withValEquiv v).symm.continuous).restrict _ _ fun _ => by
            simpa using! (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        (e0.trans e).trans withValIntegersRingEquiv
  __ := let e0 := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv Rat v).subtype
          fun _ => by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; rfl
        let e := (mapEquiv (withValEquiv v)).subtype fun _ => by
          simpa using! (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        ((e0.trans e).trans withValIntegersUniformEquiv).toHomeomorph
  commutes' := by simp

/--
theorem `adicCompletionIntegers.coe_padicIntEquiv_apply` / 定理 `adicCompletionIntegers.coe_padicIntEquiv_apply`

English:
theorem adicCompletionIntegers.coe_padicIntEquiv_apply
  statement: (v : HeightOneSpectrum R)
  proof: rfl

中文:
定理 adicCompletion整数egers.coe_padic整数Equiv_apply
  结论: (v : 高一谱 R)
  证明: rfl
-/
theorem adicCompletionIntegers.coe_padicIntEquiv_apply (v : HeightOneSpectrum R)
    (x : v.adicCompletionIntegers Rat) : padicIntEquiv v x = adicCompletion.padicEquiv v x := rfl

/--
theorem `adicCompletionIntegers.coe_padicIntEquiv_symm_apply` / 定理 `adicCompletionIntegers.coe_padicIntEquiv_symm_apply`

English:
theorem adicCompletionIntegers.coe_padicIntEquiv_symm_apply
  statement: (v : HeightOneSpectrum R)
  proof: rfl

中文:
定理 adicCompletion整数egers.coe_padic整数Equiv_symm_apply
  结论: (v : 高一谱 R)
  证明: rfl
-/
theorem adicCompletionIntegers.coe_padicIntEquiv_symm_apply (v : HeightOneSpectrum R)
    (x : Int_[primesEquiv v]) : (adicCompletionIntegers.padicIntEquiv v).symm x =
      (adicCompletion.padicEquiv v).symm x := rfl

/--
theorem `adicCompletion.padicEquiv_bijOn` / 定理 `adicCompletion.padicEquiv_bijOn`

English:
theorem adicCompletion.padicEquiv_bijOn
  given: (v : HeightOneSpectrum R)
  proof: by
  refine ⟨fun x hx => ?_, (padicEquiv v).injective.injOn, fun y hy => ?_⟩
  · rw [← adicCompletionIntegers.coe_padicIntEquiv_apply v ⟨x, hx⟩]
    exact norm_le_one ((adicCompletionIntegers.padicIntEquiv v) ⟨x, hx⟩)
  · obtain ⟨x, hx⟩ := (adicCompletionIntegers.padicIntEquiv v).surjective ⟨y, hy⟩
    refine ⟨x, x.2, by rw [← adicCompletionIntegers.coe_padicIntEquiv_apply, hx]⟩

中文:
定理 adicCompletion.padicEquiv_bijOn
  条件: (v : 高一谱 R)
  证明: by
  refine ⟨fun x hx => ?_, (padicEquiv v).injective.injOn, fun y hy => ?_⟩
  · rw [← adicCompletionIntegers.coe_padicIntEquiv_apply v ⟨x, hx⟩]
    exact norm_le_one ((adicCompletionIntegers.padicIntEquiv v) ⟨x, hx⟩)
  · obtain ⟨x, hx⟩ := (adicCompletionIntegers.padicIntEquiv v).surjective ⟨y, hy⟩
    refine ⟨x, x.2, by rw [← adicCompletionIntegers.coe_padicIntEquiv_apply, hx]⟩

Depends on / 依赖: adicCompletionIntegers, adicCompletionIntegers.coe_padicIntEquiv_apply, adicCompletionIntegers.padicIntEquiv, coe_padicIntEquiv_apply, injective, injective.injOn, norm_le_one, padicEquiv, padicIntEquiv, surjective
-/
theorem adicCompletion.padicEquiv_bijOn (v : HeightOneSpectrum R) :
    Set.BijOn (padicEquiv v) (v.adicCompletionIntegers Rat) (subring (primesEquiv v)) := by
  refine ⟨fun x hx => ?_, (padicEquiv v).injective.injOn, fun y hy => ?_⟩
  · rw [← adicCompletionIntegers.coe_padicIntEquiv_apply v ⟨x, hx⟩]
    exact norm_le_one ((adicCompletionIntegers.padicIntEquiv v) ⟨x, hx⟩)
  · obtain ⟨x, hx⟩ := (adicCompletionIntegers.padicIntEquiv v).surjective ⟨y, hy⟩
    refine ⟨x, x.2, by rw [← adicCompletionIntegers.coe_padicIntEquiv_apply, hx]⟩

end Rat.HeightOneSpectrum

open Rat.HeightOneSpectrum

namespace Padic

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R Rat] [IsFractionRing R Rat]
  [IsIntegralClosure R Int Rat]

/--
Definition of `adicCompletionEquiv` / `adicCompletionEquiv` 的定义

English:
definition adicCompletionEquiv
  signature: (p : Nat.Primes)
  body: by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletion.padicEquiv (primesEquiv.symm p)).symm

中文:
定义 adicCompletionEquiv
  签名: (p : 自然数.Primes)
  定义体: by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletion.padicEquiv (primesEquiv.symm p)).symm

Depends on / 依赖: ContinuousAlgEquiv, ContinuousAlgEquiv.cast, adicCompletion, adicCompletion.padicEquiv, apply_symm_apply, padicEquiv, primesEquiv, primesEquiv.apply_symm_apply, primesEquiv.symm
-/
noncomputable def adicCompletionEquiv (p : Nat.Primes) :
    Rat_[p] ≃A[Rat] ((primesEquiv (R := R)).symm p).adicCompletion Rat := by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletion.padicEquiv (primesEquiv.symm p)).symm

end Padic

namespace PadicInt

open Padic

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R Rat] [IsFractionRing R Rat]
  [IsIntegralClosure R Int Rat]

/--
Definition of `adicCompletionIntegersEquiv` / `adicCompletionIntegersEquiv` 的定义

English:
definition adicCompletionIntegersEquiv
  signature: (p : Nat.Primes)
  body: by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletionIntegers.padicIntEquiv (primesEquiv.symm p)).symm

中文:
定义 adicCompletion整数egersEquiv
  签名: (p : 自然数.Primes)
  定义体: by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletionIntegers.padicIntEquiv (primesEquiv.symm p)).symm

Depends on / 依赖: ContinuousAlgEquiv, ContinuousAlgEquiv.cast, adicCompletionIntegers, adicCompletionIntegers.padicIntEquiv, apply_symm_apply, padicIntEquiv, primesEquiv, primesEquiv.apply_symm_apply, primesEquiv.symm
-/
noncomputable def adicCompletionIntegersEquiv (p : Nat.Primes) :
    Int_[p] ≃A[Int] ((primesEquiv (R := R)).symm p).adicCompletionIntegers Rat := by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletionIntegers.padicIntEquiv (primesEquiv.symm p)).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `coe_adicCompletionIntegersEquiv_apply` / 定理 `coe_adicCompletionIntegersEquiv_apply`

English:
theorem coe_adicCompletionIntegersEquiv_apply
  given: (p : Nat.Primes) (x : Int_[p])
  proof: by
  simp only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.trans_apply,
    adicCompletionIntegers.coe_padicIntEquiv_symm_apply,
    adicCompletionEquiv, ContinuousAlgEquiv.trans_apply, ContinuousAlgEquiv.cast_apply,
    EmbeddingLike.apply_eq_iff_eq, Equiv.cast_apply, eq_cast_iff_heq]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

中文:
定理 coe_adicCompletion整数egersEquiv_apply
  条件: (p : 自然数.Primes) (x : 整数_[p])
  证明: by
  simp only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.trans_apply,
    adicCompletionIntegers.coe_padicIntEquiv_symm_apply,
    adicCompletionEquiv, ContinuousAlgEquiv.trans_apply, ContinuousAlgEquiv.cast_apply,
    EmbeddingLike.apply_eq_iff_eq, Equiv.cast_apply, eq_cast_iff_heq]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

Depends on / 依赖: ContinuousAlgEquiv, ContinuousAlgEquiv.cast_apply, ContinuousAlgEquiv.trans_apply, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Equiv.cast_apply, Subtype, Subtype.heq_iff_coe_heq, adicCompletionEquiv, adicCompletionIntegers, adicCompletionIntegers.coe_padicIntEquiv_symm_apply, adicCompletionIntegersEquiv, apply_eq_iff_eq, apply_symm_apply, cast_apply, cast_heq, coe_padicIntEquiv_symm_apply, eq_cast_iff_heq, heq_iff_coe_heq, primesEquiv
-/
theorem coe_adicCompletionIntegersEquiv_apply (p : Nat.Primes) (x : Int_[p]) :
    (adicCompletionIntegersEquiv R p x) = adicCompletionEquiv R p x := by
  simp only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.trans_apply,
    adicCompletionIntegers.coe_padicIntEquiv_symm_apply,
    adicCompletionEquiv, ContinuousAlgEquiv.trans_apply, ContinuousAlgEquiv.cast_apply,
    EmbeddingLike.apply_eq_iff_eq, Equiv.cast_apply, eq_cast_iff_heq]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `coe_adicCompletionIntegersEquiv_symm_apply` / 定理 `coe_adicCompletionIntegersEquiv_symm_apply`

English:
theorem coe_adicCompletionIntegersEquiv_symm_apply
  statement: (p : Nat.Primes)
  proof: by
  simp -implicitDefEqProofs only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.symm_trans_apply,
    ContinuousAlgEquiv.symm_symm, adicCompletionEquiv, Equiv.cast_apply, eq_cast_iff_heq,
    ← adicCompletionIntegers.coe_padicIntEquiv_apply, ContinuousAlgEquiv.cast_symm_apply]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

中文:
定理 coe_adicCompletion整数egersEquiv_symm_apply
  结论: (p : 自然数.Primes)
  证明: by
  simp -implicitDefEqProofs only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.symm_trans_apply,
    ContinuousAlgEquiv.symm_symm, adicCompletionEquiv, Equiv.cast_apply, eq_cast_iff_heq,
    ← adicCompletionIntegers.coe_padicIntEquiv_apply, ContinuousAlgEquiv.cast_symm_apply]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

Depends on / 依赖: ContinuousAlgEquiv, ContinuousAlgEquiv.cast_symm_apply, ContinuousAlgEquiv.symm_symm, ContinuousAlgEquiv.symm_trans_apply, Equiv.cast_apply, Subtype, Subtype.heq_iff_coe_heq, adicCompletionEquiv, adicCompletionIntegers, adicCompletionIntegers.coe_padicIntEquiv_apply, adicCompletionIntegersEquiv, apply_symm_apply, cast_apply, cast_heq, cast_symm_apply, coe_padicIntEquiv_apply, eq_cast_iff_heq, heq_iff_coe_heq, implicitDefEqProofs, primesEquiv
-/
theorem coe_adicCompletionIntegersEquiv_symm_apply (p : Nat.Primes)
    (x : (primesEquiv.symm p).adicCompletionIntegers Rat) :
    (adicCompletionIntegersEquiv R p).symm x = (adicCompletionEquiv R p).symm x := by
  simp -implicitDefEqProofs only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.symm_trans_apply,
    ContinuousAlgEquiv.symm_symm, adicCompletionEquiv, Equiv.cast_apply, eq_cast_iff_heq,
    ← adicCompletionIntegers.coe_padicIntEquiv_apply, ContinuousAlgEquiv.cast_symm_apply]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

end PadicInt
