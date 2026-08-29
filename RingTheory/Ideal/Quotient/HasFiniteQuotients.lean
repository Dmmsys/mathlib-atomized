/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Order.Northcott
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # Rings with finite quotients

A commutative ring is said to have finite quotients if, for any nonzero ideal `I` of `R`, the
quotient `R ⧸ I` is finite.

## Main results
- `Ring.HasFiniteQuotients.instDimensionLEOne`: A ring with finite quotients has dimension `≤ 1`.
- `Ring.HasFiniteQuotients.instIsNoetherianRing` : A ring with finite quotients is noetherian.
- `Ring.HasFiniteQuotients.of_module_finite`: Assume that `R` has finite quotients and that `S` is
  a domain and a finite `R`-module. Then `S` has finite quotients.
- `Ring.HasFiniteQuotients.instOfIsDomainOfFG`: A domain that is also a finite `ℤ`-module
  has finite quotients.

-/

public section

/--
Definition of `Ring.HasFiniteQuotients` / `Ring.HasFiniteQuotients` 的定义

English:
class Ring.HasFiniteQuotients
  parameters: (R : Type*) [CommRing R]
  axioms and operations (1):
    - finiteQuotient({I : Ideal R}) : I != ⊥ -> Finite (R ⧸ I)

中文:
类 环.有FiniteQuotients
  参数: (R : 类型) [交换环 R]
  公理与运算 (1 个):
    - finiteQuotient({I : 理想 R}) : I != ⊥ -> 有限 (R ⧸ I)
-/
class Ring.HasFiniteQuotients (R : Type*) [CommRing R] : Prop where
  finiteQuotient {I : Ideal R} : I != ⊥ -> Finite (R ⧸ I)

namespace Ring.HasFiniteQuotients

variable {R : Type*} [CommRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: R] : Ring.HasFiniteQuotients R where
  body: fun _ => Quotient.finite _

中文:
实例 [有限
  签名: R] : 环.有FiniteQuotients R where
  定义体: fun _ => Quotient.finite _

Depends on / 依赖: Quotient, Quotient.finite, finite
-/
instance [Finite R] : Ring.HasFiniteQuotients R where
  finiteQuotient := fun _ => Quotient.finite _

section properties

variable [HasFiniteQuotients R]

/--
theorem `maximalOfPrime` / 定理 `maximalOfPrime`

English:
theorem maximalOfPrime
  given: {P : Ideal R} [P.IsPrime] (hp : P != ⊥)
  proof: have : Finite (R ⧸ P) := finiteQuotient hp
Ideal.Quotient.maximal_of_isField P Finite.isField_of_domain (R ⧸ P)

中文:
定理 maximalOfPrime
  条件: {P : 理想 R} [P.是素] (hp : P != ⊥)
  证明: have : Finite (R ⧸ P) := finiteQuotient hp
Ideal.Quotient.maximal_of_isField P Finite.isField_of_domain (R ⧸ P)

Depends on / 依赖: Finite, Finite.isField_of_domain, Ideal.Quotient.maximal_of_isField, Quotient, finiteQuotient, isField_of_domain, maximal_of_isField
-/
theorem maximalOfPrime {P : Ideal R} [P.IsPrime] (hp : P != ⊥) :
    P.IsMaximal :=
  have : Finite (R ⧸ P) := finiteQuotient hp
Ideal.Quotient.maximal_of_isField P Finite.isField_of_domain (R ⧸ P)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DimensionLEOne R
  body: fun h _ => maximalOfPrime h

中文:
实例 :
  签名: 维数不超过一 R
  定义体: fun h _ => maximalOfPrime h

Depends on / 依赖: maximalOfPrime
-/
instance : DimensionLEOne R where
  maximalOfPrime := fun h _ => maximalOfPrime h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNoetherianRing R
  body: by
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun I => ?_
  by_cases hI : I = 0
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x, hx₁, hx₂⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {x})) ?_ ?_
  · have := finiteQuotient (I :

中文:
实例 :
  签名: 是Noether环 R
  定义体: by
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun I => ?_
  by_cases hI : I = 0
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x, hx₁, hx₂⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {x})) ?_ ?_
  · have := finiteQuotient (I :

Depends on / 依赖: Ideal.span, Ideal.span_singleton_le_iff_mem, Submodule, Submodule.FG.of_finite, Submodule.exists_mem_ne_zero_of_ne_bot, Submodule.fg_bot, Submodule.fg_of_fg_map_of_fg_inf_ker, Submodule.fg_span_singleton, Submodule.ker_mkQ, Submodule.mkQ, exists_mem_ne_zero_of_ne_bot, fg_bot, fg_of_fg_map_of_fg_inf_ker, fg_span_singleton, finiteQuotient, inf_eq_right, inf_eq_right.mpr, isNoetherianRing_iff_ideal_fg, ker_mkQ, of_finite
-/
instance : IsNoetherianRing R := by
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun I => ?_
  by_cases hI : I = 0
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x, hx₁, hx₂⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {x})) ?_ ?_
  · have := finiteQuotient (I := Ideal.span {x}) (by simp [hx₂])
    exact Submodule.FG.of_finite
  · rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hx₁)]
    exact Submodule.fg_span_singleton x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] [PerfectField (FractionRing R)] (P
  body: by
  rcases eq_or_ne P ⊥ with rfl | hP
  · exact PerfectField.of_ringEquiv (FractionRing.algEquiv R _).toRingEquiv
  · have : Finite (R ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    infer_instance

中文:
实例 [是整环
  签名: R] [完美域 (FractionRing R)] (P
  定义体: by
  rcases eq_or_ne P ⊥ with rfl | hP
  · exact PerfectField.of_ringEquiv (FractionRing.algEquiv R _).toRingEquiv
  · have : Finite (R ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    infer_instance

Depends on / 依赖: Finite, FractionRing, FractionRing.algEquiv, HasFiniteQuotients, PerfectField, PerfectField.of_ringEquiv, Ring.HasFiniteQuotients.finiteQuotient, algEquiv, eq_or_ne, finiteQuotient, infer_instance, of_ringEquiv, toRingEquiv
-/
instance [IsDomain R] [PerfectField (FractionRing R)] (P : Ideal R) [P.IsPrime] :
    PerfectField P.ResidueField := by
  rcases eq_or_ne P ⊥ with rfl | hP
  · exact PerfectField.of_ringEquiv (FractionRing.algEquiv R _).toRingEquiv
  · have : Finite (R ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    infer_instance

/--
theorem `cardQuot_pos` / 定理 `cardQuot_pos`

English:
theorem cardQuot_pos
  given: (I : Ideal R) (hI : I != ⊥)
  statement: 0 < I.cardQuot
  proof: by
  have := finiteQuotient hI
  rw [Submodule.cardQuot_apply]
  exact Nat.card_pos

中文:
定理 cardQuot_pos
  条件: (I : 理想 R) (hI : I != ⊥)
  结论: 0 < I.cardQuot
  证明: by
  have := finiteQuotient hI
  rw [Submodule.cardQuot_apply]
  exact Nat.card_pos

Depends on / 依赖: Nat.card_pos, Submodule, Submodule.cardQuot_apply, cardQuot_apply, card_pos, finiteQuotient
-/
theorem cardQuot_pos (I : Ideal R) (hI : I != ⊥) : 0 < I.cardQuot := by
  have := finiteQuotient hI
  rw [Submodule.cardQuot_apply]
  exact Nat.card_pos

/--
theorem `finite_setOfPred_mem` / 定理 `finite_setOfPred_mem`

English:
theorem finite_setOfPred_mem
  given: (x : R) (hx : x != 0)
  statement: {I : Ideal R | x in I}.Finite
  proof: by
  have := finiteQuotient (mt Ideal.span_singleton_eq_bot.mp hx)
  have : {I | Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) ⊥ <= I}.Finite :=
    .of_equiv _ (Ideal.relIsoOfSurjective _ Ideal.Quotient.mk_surjective).toEquiv
  simpa [← RingHom.ker_eq_comap_bot] using this

@[deprecated (since :

中文:
定理 finite_setOfPred_mem
  条件: (x : R) (hx : x != 0)
  结论: {I : 理想 R | x in I}.有限
  证明: by
  have := finiteQuotient (mt Ideal.span_singleton_eq_bot.mp hx)
  have : {I | Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) ⊥ <= I}.Finite :=
    .of_equiv _ (Ideal.relIsoOfSurjective _ Ideal.Quotient.mk_surjective).toEquiv
  simpa [← RingHom.ker_eq_comap_bot] using this

@[deprecated (since :

Depends on / 依赖: Finite, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.comap, Ideal.relIsoOfSurjective, Ideal.span, Ideal.span_singleton_eq_bot.mp, Quotient, RingHom, RingHom.ker_eq_comap_bot, finiteQuotient, ker_eq_comap_bot, mk_surjective, of_equiv, relIsoOfSurjective, span_singleton_eq_bot, toEquiv
-/
theorem finite_setOfPred_mem (x : R) (hx : x != 0) : {I : Ideal R | x in I}.Finite := by
  have := finiteQuotient (mt Ideal.span_singleton_eq_bot.mp hx)
  have : {I | Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) ⊥ <= I}.Finite :=
    .of_equiv _ (Ideal.relIsoOfSurjective _ Ideal.Quotient.mk_surjective).toEquiv
  simpa [← RingHom.ker_eq_comap_bot] using this

@[deprecated (since := "2026-07-09")] alias finite_setOf_mem := finite_setOfPred_mem

open scoped Pointwise in
/--
theorem `finite_cardQuot_le` / 定理 `finite_cardQuot_le`

English:
theorem finite_cardQuot_le
  given: (B : Nat)
  statement: {I : Ideal R | I.cardQuot <= B}.Finite
  proof: by
  classical
  rcases finite_or_infinite R
  · apply Set.toFinite
  -- if `R` is infinite, then we can pick a finite set `s` of cardinality `B + 1`
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq R (B + 1)
  -- and consider the finite set `t` of nonzero differences
  let t := (s - s) \ {0}
  re

中文:
定理 finite_cardQuot_le
  条件: (B : 自然数)
  结论: {I : 理想 R | I.cardQuot <= B}.有限
  证明: by
  classical
  rcases finite_or_infinite R
  · apply Set.toFinite
  -- if `R` is infinite, then we can pick a finite set `s` of cardinality `B + 1`
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq R (B + 1)
  -- and consider the finite set `t` of nonzero differences
  let t := (s - s) \ {0}
  re

Depends on / 依赖: Set.toFinite, classical, finite_or_infinite, toFinite
-/
theorem finite_cardQuot_le (B : Nat) : {I : Ideal R | I.cardQuot <= B}.Finite := by
  classical
  rcases finite_or_infinite R
  · apply Set.toFinite
  -- if `R` is infinite, then we can pick a finite set `s` of cardinality `B + 1`
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq R (B + 1)
  -- and consider the finite set `t` of nonzero differences
  let t := (s - s) \ {0}
  refine Set.Finite.of_sdiff ?_ (Set.finite_singleton ⊥)
  -- in a ring with finite quotients, each nonzero element is contained in only finitely many ideals
  -- so it is enough to show that each ideal `I` of norm at most `B` contains some element of `t`
  suffices {I | Submodule.cardQuot I <= B} \ {⊥} subseteq ⋃ x in t, {I | x in I} from
    (t.finite_toSet.biUnion fun x hx => finite_setOfPred_mem x (by grind)).subset this
  intro I hI
  rw [Set.mem_sdiff]; rw [Set.mem_ofPred]; rw [Submodule.cardQuot_apply] at hI
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq]
  -- `s` has cardinality `B + 1`, but the quotient `R ⧸ I` has cardinality at most `B`
  replace hs : (s.image (Ideal.Quotient.mk I)).card < s.card := by
    have := finiteQuotient hI.2
    have := Fintype.ofFinite (R ⧸ I)
    grw [Finset.card_le_univ, Fintype.card_eq_nat_card, hI.1, hs, Nat.lt_add_one_iff]
  -- so we can find distinct `x, y ∈ s` with the desired collision `x - y ∈ I`
  obtain ⟨x, hx, y, hy, hxy, h⟩ := Finset.exists_ne_map_eq_of_card_image_lt hs
  refine ⟨x - y, ?_, (Submodule.Quotient.eq I).mp h⟩
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_sub.mpr ⟨x, hx, y, hy, rfl⟩, ?_⟩
  rwa [Finset.notMem_singleton, sub_ne_zero]

/--
theorem `finite_absNorm_le` / 定理 `finite_absNorm_le`

English:
theorem finite_absNorm_le
  given: [IsDedekindDomain R] [Module.Free Int R] (B : Nat)
  proof: finite_cardQuot_le B

中文:
定理 finite_absNorm_le
  条件: [是Dedekind整环 R] [模.自由 整数 R] (B : 自然数)
  证明: finite_cardQuot_le B

Depends on / 依赖: finite_cardQuot_le
-/
theorem finite_absNorm_le [IsDedekindDomain R] [Module.Free Int R] (B : Nat) :
    {I : Ideal R | I.absNorm <= B}.Finite :=
  finite_cardQuot_le B

/--
theorem `finite_cardQuot_heightOneSpectrum_le` / 定理 `finite_cardQuot_heightOneSpectrum_le`

English:
theorem finite_cardQuot_heightOneSpectrum_le
  given: (B : Nat)
  proof: (finite_cardQuot_le B).of_injOn (by simp [Set.MapsTo])
    (Function.Injective.injOn fun _ _ => IsDedekindDomain.HeightOneSpectrum.ext)

中文:
定理 finite_cardQuot_heightOneSpectrum_le
  条件: (B : 自然数)
  证明: (finite_cardQuot_le B).of_injOn (by simp [Set.MapsTo])
    (Function.Injective.injOn fun _ _ => IsDedekindDomain.HeightOneSpectrum.ext)

Depends on / 依赖: Function, Function.Injective.injOn, HeightOneSpectrum, Injective, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum.ext, MapsTo, Set.MapsTo, finite_cardQuot_le, of_injOn
-/
theorem finite_cardQuot_heightOneSpectrum_le (B : Nat) :
    {p : IsDedekindDomain.HeightOneSpectrum R | p.asIdeal.cardQuot <= B}.Finite :=
  (finite_cardQuot_le B).of_injOn (by simp [Set.MapsTo])
    (Function.Injective.injOn fun _ _ => IsDedekindDomain.HeightOneSpectrum.ext)

/--
theorem `finite_absNorm_heightOneSpectrum_le` / 定理 `finite_absNorm_heightOneSpectrum_le`

English:
theorem finite_absNorm_heightOneSpectrum_le
  given: [IsDedekindDomain R] [Module.Free Int R] (B : Nat)
  proof: finite_cardQuot_heightOneSpectrum_le B

中文:
定理 finite_absNorm_heightOneSpectrum_le
  条件: [是Dedekind整环 R] [模.自由 整数 R] (B : 自然数)
  证明: finite_cardQuot_heightOneSpectrum_le B

Depends on / 依赖: finite_cardQuot_heightOneSpectrum_le
-/
theorem finite_absNorm_heightOneSpectrum_le [IsDedekindDomain R] [Module.Free Int R] (B : Nat) :
    {p : IsDedekindDomain.HeightOneSpectrum R | p.asIdeal.absNorm <= B}.Finite :=
  finite_cardQuot_heightOneSpectrum_le B

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Northcott fun p
  body: ⟨Ring.HasFiniteQuotients.finite_cardQuot_le⟩

中文:
实例 :
  签名: Northcott fun p
  定义体: ⟨Ring.HasFiniteQuotients.finite_cardQuot_le⟩

Depends on / 依赖: ExtremallyDisconnected, HasFiniteQuotients, PreirreducibleSpace, Ring.HasFiniteQuotients.finite_cardQuot_le, finite_cardQuot_le
-/
instance : Northcott fun p : Ideal R => p.cardQuot :=
  ⟨Ring.HasFiniteQuotients.finite_cardQuot_le⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDedekindDomain
  signature: R] [Module.Free Int R] :
  body: ⟨Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le⟩

中文:
实例 [是Dedekind整环
  签名: R] [模.自由 整数 R] :
  定义体: ⟨Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le⟩

Depends on / 依赖: HasFiniteQuotients, Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le, finite_absNorm_heightOneSpectrum_le
-/
instance [IsDedekindDomain R] [Module.Free Int R] :
    Northcott fun p : IsDedekindDomain.HeightOneSpectrum R => p.asIdeal.absNorm :=
  ⟨Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le⟩

variable (R) in
/--
theorem `of_module_finite` / 定理 `of_module_finite`

English:
theorem of_module_finite
  statement: (S : Type*) [CommRing S] [IsDomain S]
  proof: by
    obtain hR | hR := subsingleton_or_nontrivial R
    · have : Finite S := Module.finite_of_finite R
      exact Quotient.finite _
    let J : Ideal R := Ideal.under R I
have : Finite (R ⧸ J) := finiteQuotient Ideal.under_ne_bot R hI
    have : Module.Finite (R ⧸ J) (S ⧸ I) := Module.Finite.of_r

中文:
定理 of_module_finite
  结论: (S : 类型) [交换环 S] [是整环 S]
  证明: by
    obtain hR | hR := subsingleton_or_nontrivial R
    · have : Finite S := Module.finite_of_finite R
      exact Quotient.finite _
    let J : Ideal R := Ideal.under R I
have : Finite (R ⧸ J) := finiteQuotient Ideal.under_ne_bot R hI
    have : Module.Finite (R ⧸ J) (S ⧸ I) := Module.Finite.of_r

Depends on / 依赖: Finite, Ideal.under, Ideal.under_ne_bot, Module, Module.Finite, Module.Finite.of_restrictScalars_finite, Module.finite_of_finite, Quotient, Quotient.finite, finite, finiteQuotient, finite_of_finite, of_restrictScalars_finite, subsingleton_or_nontrivial, under_ne_bot
-/
theorem of_module_finite (S : Type*) [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] :
    HasFiniteQuotients S where
  finiteQuotient {I} hI := by
    obtain hR | hR := subsingleton_or_nontrivial R
    · have : Finite S := Module.finite_of_finite R
      exact Quotient.finite _
    let J : Ideal R := Ideal.under R I
have : Finite (R ⧸ J) := finiteQuotient Ideal.under_ne_bot R hI
    have : Module.Finite (R ⧸ J) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R _ _
    exact Module.finite_of_finite (R ⧸ J)

end properties

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteQuotients Int
  body: by
    obtain ⟨n, rfl⟩ := Submodule.IsPrincipal.principal I
    have : NeZero n := ⟨by simpa using hI⟩
exact inferInstanceAs Finite (Int ⧸ Ideal.span {n})

中文:
实例 :
  签名: 有FiniteQuotients 整数
  定义体: by
    obtain ⟨n, rfl⟩ := Submodule.IsPrincipal.principal I
    have : NeZero n := ⟨by simpa using hI⟩
exact inferInstanceAs Finite (Int ⧸ Ideal.span {n})

Depends on / 依赖: Finite, Ideal.span, IsPrincipal, NeZero, Submodule, Submodule.IsPrincipal.principal, principal
-/
instance : HasFiniteQuotients Int where
  finiteQuotient {I} hI := by
    obtain ⟨n, rfl⟩ := Submodule.IsPrincipal.principal I
    have : NeZero n := ⟨by simpa using hI⟩
exact inferInstanceAs Finite (Int ⧸ Ideal.span {n})

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] [Module.Finite Int R] : HasFiniteQuotients R
  body: .of_module_finite Int R

中文:
实例 [是整环
  签名: R] [模.有限 整数 R] : 有FiniteQuotients R
  定义体: .of_module_finite Int R

Depends on / 依赖: of_module_finite
-/
instance [IsDomain R] [Module.Finite Int R] : HasFiniteQuotients R :=
  .of_module_finite Int R

end Ring.HasFiniteQuotients
