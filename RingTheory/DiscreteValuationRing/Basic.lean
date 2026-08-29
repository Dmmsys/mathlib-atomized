/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.Valuation.PrimeMultiplicity
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Discrete valuation rings

This file defines discrete valuation rings (DVRs) and develops a basic interface
for them.

## Important definitions

There are various definitions of a DVR in the literature; we define a DVR to be a local PID
which is not a field (the first definition in Wikipedia) and prove that this is equivalent
to being a PID with a unique non-zero prime ideal (the definition in Serre's
book "Local Fields").

Let R be an integral domain, assumed to be a principal ideal ring and a local ring.

* `IsDiscreteValuationRing R` : a predicate expressing that R is a DVR.

### Definitions

* `addVal R : AddValuation R ℕ∞` : the additive valuation on a DVR.
* `toEuclideanDomain R : EuclideanDomain R` : a non-canonical structure of Euclidean domain on a
  DVR, where `x % y = 0` if `y ∣ x` and `x % y = x` otherwise. The GCD algorithm terminates in two
  steps.

## Implementation notes

It's a theorem that an element of a DVR is a uniformizer if and only if it's irreducible.
We do not hence define `Uniformizer` at all, because we can use `Irreducible` instead.

## Tags

discrete valuation ring
-/

@[expose] public section

universe u

open Ideal IsLocalRing

/--
Definition of `IsDiscreteValuationRing` / `IsDiscreteValuationRing` 的定义

English:
class IsDiscreteValuationRing
  parameters: (R : Type u) [CommRing R] [IsDomain R]
  extends: IsPrincipalIdealRing R, IsLocalRing R
  axioms and operations (1):
    - not_a_field' : maximalIdeal R != ⊥

中文:
类 IsDiscreteValuationRing
  参数: (R : 类型u) [CommRing R] [IsDomain R]
  继承: IsPrincipalIdealRing R, IsLocalRing R
  公理与运算 (1 个):
    - not_a_field' : maximalIdeal R != ⊥
-/
class IsDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R] : Prop
    extends IsPrincipalIdealRing R, IsLocalRing R where
  not_a_field' : maximalIdeal R != ⊥

namespace IsDiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/--
theorem `not_a_field` / 定理 `not_a_field`

English:
theorem not_a_field
  statement: maximalIdeal R != ⊥
  proof: not_a_field'

中文:
定理 not_a_field
  结论: maximalIdeal R != ⊥
  证明: not_a_field'

Depends on / 依赖: not_a_field
-/
theorem not_a_field : maximalIdeal R != ⊥ :=
  not_a_field'

/--
theorem `not_isField` / 定理 `not_isField`

English:
theorem not_isField
  statement: ¬IsField R
  proof: IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr (not_a_field R)

中文:
定理 not_isField
  结论: ¬IsField R
  证明: IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr (not_a_field R)

Depends on / 依赖: IsLocalRing, IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr, isField_iff_maximalIdeal_eq, not_a_field
-/
theorem not_isField : ¬IsField R :=
  IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr (not_a_field R)

variable {R}

open PrincipalIdealRing

/--
theorem `irreducible_of_span_eq_maximalIdeal` / 定理 `irreducible_of_span_eq_maximalIdeal`

English:
theorem irreducible_of_span_eq_maximalIdeal
  statement: {R : Type*} [CommSemiring R] [IsLocalRing R]
  proof: by
  have h2 : ¬IsUnit ϖ := show ϖ in maximalIdeal R from h.symm ▸ Submodule.mem_span_singleton_self ϖ
  refine ⟨h2, ?_⟩
  intro a b hab
  by_contra! ⟨ha : a in maximalIdeal R, hb : b in maximalIdeal R⟩
  rw [h]; rw [mem_span_singleton'] at ha hb
  rcases ha with ⟨a, rfl⟩
  rcases hb with ⟨b, rfl⟩
 

中文:
定理 irreducible_of_span_eq_maximalIdeal
  结论: {R : 类型} [CommSemiring R] [IsLocalRing R]
  证明: by
  have h2 : ¬IsUnit ϖ := show ϖ in maximalIdeal R from h.symm ▸ Submodule.mem_span_singleton_self ϖ
  refine ⟨h2, ?_⟩
  intro a b hab
  by_contra! ⟨ha : a in maximalIdeal R, hb : b in maximalIdeal R⟩
  rw [h]; rw [mem_span_singleton'] at ha hb
  rcases ha with ⟨a, rfl⟩
  rcases hb with ⟨b, rfl⟩
 

Depends on / 依赖: IsUnit, Submodule, Submodule.mem_span_singleton_self, eq_zero_of_mul_eq_self_right, h.symm, hab.symm, hh.symm, isUnit_of_dvd_one, maximalIdeal, mem_span_singleton, mem_span_singleton_self
-/
theorem irreducible_of_span_eq_maximalIdeal {R : Type*} [CommSemiring R] [IsLocalRing R]
    [IsDomain R] (ϖ : R) (hϖ : ϖ != 0) (h : maximalIdeal R = Ideal.span {ϖ}) : Irreducible ϖ := by
  have h2 : ¬IsUnit ϖ := show ϖ in maximalIdeal R from h.symm ▸ Submodule.mem_span_singleton_self ϖ
  refine ⟨h2, ?_⟩
  intro a b hab
  by_contra! ⟨ha : a in maximalIdeal R, hb : b in maximalIdeal R⟩
  rw [h]; rw [mem_span_singleton'] at ha hb
  rcases ha with ⟨a, rfl⟩
  rcases hb with ⟨b, rfl⟩
  rw [show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)) by ring] at hab
  apply hϖ
  apply eq_zero_of_mul_eq_self_right _ hab.symm
  exact fun hh => h2 (isUnit_of_dvd_one ⟨_, hh.symm⟩)

/--
theorem `irreducible_iff_uniformizer` / 定理 `irreducible_iff_uniformizer`

English:
theorem irreducible_iff_uniformizer
  given: (ϖ : R)
  statement: Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ}
  proof: ⟨fun hϖ => (eq_maximalIdeal (isMaximal_of_irreducible hϖ)).symm,
    fun h => irreducible_of_span_eq_maximalIdeal ϖ
      (fun e => not_a_field R <| by rwa [h, span_singleton_eq_bot]) h⟩

中文:
定理 irreducible_iff_uniformizer
  条件: (ϖ : R)
  结论: Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ}
  证明: ⟨fun hϖ => (eq_maximalIdeal (isMaximal_of_irreducible hϖ)).symm,
    fun h => irreducible_of_span_eq_maximalIdeal ϖ
      (fun e => not_a_field R <| by rwa [h, span_singleton_eq_bot]) h⟩

Depends on / 依赖: eq_maximalIdeal, irreducible_of_span_eq_maximalIdeal, isMaximal_of_irreducible, not_a_field, span_singleton_eq_bot
-/
theorem irreducible_iff_uniformizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ} :=
  ⟨fun hϖ => (eq_maximalIdeal (isMaximal_of_irreducible hϖ)).symm,
    fun h => irreducible_of_span_eq_maximalIdeal ϖ
      (fun e => not_a_field R <| by rwa [h, span_singleton_eq_bot]) h⟩

/--
theorem `_root_.Irreducible.maximalIdeal_eq` / 定理 `_root_.Irreducible.maximalIdeal_eq`

English:
theorem _root_.Irreducible.maximalIdeal_eq
  given: {ϖ : R} (h : Irreducible ϖ)
  proof: (irreducible_iff_uniformizer _).mp h

中文:
定理 _root_.Irreducible.maximalIdeal_eq
  条件: {ϖ : R} (h : Irreducible ϖ)
  证明: (irreducible_iff_uniformizer _).mp h

Depends on / 依赖: irreducible_iff_uniformizer
-/
theorem _root_.Irreducible.maximalIdeal_eq {ϖ : R} (h : Irreducible ϖ) :
    maximalIdeal R = Ideal.span {ϖ} :=
  (irreducible_iff_uniformizer _).mp h

variable (R)

/--
theorem `exists_irreducible` / 定理 `exists_irreducible`

English:
theorem exists_irreducible
  statement: exists ϖ : R, Irreducible ϖ
  proof: by
  simp_rw [irreducible_iff_uniformizer]
  exact (IsPrincipalIdealRing.principal <| maximalIdeal R).principal

中文:
定理 exists_irreducible
  结论: 存在 ϖ : R, Irreducible ϖ
  证明: by
  simp_rw [irreducible_iff_uniformizer]
  exact (IsPrincipalIdealRing.principal <| maximalIdeal R).principal

Depends on / 依赖: IsPrincipalIdealRing, IsPrincipalIdealRing.principal, irreducible_iff_uniformizer, maximalIdeal, principal, simp_rw
-/
theorem exists_irreducible : exists ϖ : R, Irreducible ϖ := by
  simp_rw [irreducible_iff_uniformizer]
  exact (IsPrincipalIdealRing.principal <| maximalIdeal R).principal

/--
theorem `exists_prime` / 定理 `exists_prime`

English:
theorem exists_prime
  statement: exists ϖ : R, Prime ϖ
  proof: (exists_irreducible R).imp fun _ => irreducible_iff_prime.1

中文:
定理 exists_prime
  结论: 存在 ϖ : R, Prime ϖ
  证明: (exists_irreducible R).imp fun _ => irreducible_iff_prime.1

Depends on / 依赖: exists_irreducible, irreducible_iff_prime
-/
theorem exists_prime : exists ϖ : R, Prime ϖ :=
  (exists_irreducible R).imp fun _ => irreducible_iff_prime.1

/--
theorem `iff_pid_with_one_nonzero_prime` / 定理 `iff_pid_with_one_nonzero_prime`

English:
theorem iff_pid_with_one_nonzero_prime
  given: (R : Type u) [CommRing R] [IsDomain R]
  proof: by
  constructor
  · intro RDVR
    rcases id RDVR with ⟨Rlocal⟩
    constructor
    · assumption
    use IsLocalRing.maximalIdeal R
    constructor
    · exact ⟨Rlocal, inferInstance⟩
    · rintro Q ⟨hQ1, hQ2⟩
      obtain ⟨q, rfl⟩ := (IsPrincipalIdealRing.principal Q).1
      have hq : q != 0 := b

中文:
定理 iff_pid_with_one_nonzero_prime
  条件: (R : 类型u) [CommRing R] [IsDomain R]
  证明: by
  constructor
  · intro RDVR
    rcases id RDVR with ⟨Rlocal⟩
    constructor
    · assumption
    use IsLocalRing.maximalIdeal R
    constructor
    · exact ⟨Rlocal, inferInstance⟩
    · rintro Q ⟨hQ1, hQ2⟩
      obtain ⟨q, rfl⟩ := (IsPrincipalIdealRing.principal Q).1
      have hq : q != 0 := b

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal, IsLocalRing.of_unique, IsPrincipalIdealRing, IsPrincipalIdealRing.principal, Punique, Rlocal, hQ2.irreducible, hQ2.symm, irreducible, irreducible_iff_uniformizer, maximalIdeal, of_unique, principal, replace, span_singleton_prime, submodule_span_eq
-/
theorem iff_pid_with_one_nonzero_prime (R : Type u) [CommRing R] [IsDomain R] :
    IsDiscreteValuationRing R ↔ IsPrincipalIdealRing R ∧ exists! P : Ideal R, P != ⊥ ∧ IsPrime P := by
  constructor
  · intro RDVR
    rcases id RDVR with ⟨Rlocal⟩
    constructor
    · assumption
    use IsLocalRing.maximalIdeal R
    constructor
    · exact ⟨Rlocal, inferInstance⟩
    · rintro Q ⟨hQ1, hQ2⟩
      obtain ⟨q, rfl⟩ := (IsPrincipalIdealRing.principal Q).1
      have hq : q != 0 := by
        rintro rfl
        apply hQ1
        simp
      rw [submodule_span_eq]; rw [span_singleton_prime hq] at hQ2
      replace hQ2 := hQ2.irreducible
      rw [irreducible_iff_uniformizer] at hQ2
      exact hQ2.symm
  · rintro ⟨RPID, Punique⟩
    have : IsLocalRing R := IsLocalRing.of_unique_nonzero_prime Punique
    refine { not_a_field' := ?_ }
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, _⟩
    have hPM : P <= maximalIdeal R := le_maximalIdeal hP2.1
    order

/--
theorem `associated_of_irreducible` / 定理 `associated_of_irreducible`

English:
theorem associated_of_irreducible
  given: {a b : R} (ha : Irreducible a) (hb : Irreducible b)
  proof: by
  rw [irreducible_iff_uniformizer] at ha hb
  rw [← span_singleton_eq_span_singleton]; rw [← ha]; rw [hb]

中文:
定理 associated_of_irreducible
  条件: {a b : R} (ha : Irreducible a) (hb : Irreducible b)
  证明: by
  rw [irreducible_iff_uniformizer] at ha hb
  rw [← span_singleton_eq_span_singleton]; rw [← ha]; rw [hb]

Depends on / 依赖: irreducible_iff_uniformizer, span_singleton_eq_span_singleton
-/
theorem associated_of_irreducible {a b : R} (ha : Irreducible a) (hb : Irreducible b) :
    Associated a b := by
  rw [irreducible_iff_uniformizer] at ha hb
  rw [← span_singleton_eq_span_singleton]; rw [← ha]; rw [hb]

variable (R : Type*)

/--
Definition of `HasUnitMulPowIrreducibleFactorization` / `HasUnitMulPowIrreducibleFactorization` 的定义

English:
definition HasUnitMulPowIrreducibleFactorization
  signature: [CommRing R]
  body: exists p : R, Irreducible p ∧ forall {x : R}, x != 0 -> exists n : Nat, Associated (p ^ n) x

中文:
定义 HasUnitMulPowIrreducibleFactorization
  签名: [CommRing R]
  定义体: exists p : R, Irreducible p ∧ forall {x : R}, x != 0 -> exists n : Nat, Associated (p ^ n) x

Depends on / 依赖: Associated, Irreducible
-/
def HasUnitMulPowIrreducibleFactorization [CommRing R] : Prop :=
  exists p : R, Irreducible p ∧ forall {x : R}, x != 0 -> exists n : Nat, Associated (p ^ n) x

namespace HasUnitMulPowIrreducibleFactorization

variable {R} [CommRing R]

/--
theorem `unique_irreducible` / 定理 `unique_irreducible`

English:
theorem unique_irreducible
  statement: (hR : HasUnitMulPowIrreducibleFactorization R)
  proof: by
  rcases hR with ⟨ϖ, hϖ, hR⟩
  suffices forall {p : R} (_ : Irreducible p), Associated p ϖ by
    apply Associated.trans (this hp) (this hq).symm
  clear hp hq p q
  intro p hp
  obtain ⟨n, hn⟩ := hR hp.ne_zero
  have : Irreducible (ϖ ^ n) := hn.symm.irreducible hp
  rcases lt_trichotomy n 1 with

中文:
定理 unique_irreducible
  结论: (hR : HasUnitMulPowIrreducibleFactorization R)
  证明: by
  rcases hR with ⟨ϖ, hϖ, hR⟩
  suffices forall {p : R} (_ : Irreducible p), Associated p ϖ by
    apply Associated.trans (this hp) (this hq).symm
  clear hp hq p q
  intro p hp
  obtain ⟨n, hn⟩ := hR hp.ne_zero
  have : Irreducible (ϖ ^ n) := hn.symm.irreducible hp
  rcases lt_trichotomy n 1 with

Depends on / 依赖: Associated, Associated.trans, Irreducible, Nat.exists_eq_a, exists_eq_a, hn.symm, hn.symm.irreducible, hp.ne_zero, irreducible, lt_trichotomy, ne_zero, not_irreducible_one, pow_one, pow_zero, revert
-/
theorem unique_irreducible (hR : HasUnitMulPowIrreducibleFactorization R)
    ⦃p q : R⦄ (hp : Irreducible p) (hq : Irreducible q) :
    Associated p q := by
  rcases hR with ⟨ϖ, hϖ, hR⟩
  suffices forall {p : R} (_ : Irreducible p), Associated p ϖ by
    apply Associated.trans (this hp) (this hq).symm
  clear hp hq p q
  intro p hp
  obtain ⟨n, hn⟩ := hR hp.ne_zero
  have : Irreducible (ϖ ^ n) := hn.symm.irreducible hp
  rcases lt_trichotomy n 1 with (H | rfl | H)
  · obtain rfl : n = 0 := by
      clear hn this
      revert H n
      decide
    simp [not_irreducible_one, pow_zero] at this
  · simpa only [pow_one] using hn.symm
  · obtain ⟨n, rfl⟩ : exists k, n = 1 + k + 1 := Nat.exists_eq_add_of_lt H
    rw [pow_succ'] at this
    rcases this.isUnit_or_isUnit rfl with (H0 | H0)
    · exact (hϖ.not_isUnit H0).elim
    · rw [add_comm, pow_succ'] at H0
      exact (hϖ.not_isUnit (isUnit_of_mul_isUnit_left H0)).elim

/--
theorem `toUniqueFactorizationMonoid` / 定理 `toUniqueFactorizationMonoid`

English:
theorem toUniqueFactorizationMonoid
  statement: [IsCancelMulZero R]
  proof: let p := Classical.choose hR
  let spec := Classical.choose_spec hR
  UniqueFactorizationMonoid.of_exists_prime_factors fun x hx => by
    use Multiset.replicate (Classical.choose (spec.2 hx)) p
    constructor
    · intro q hq
      have hpq := Multiset.eq_of_mem_replicate hq
      rw [hpq]
      r

中文:
定理 toUniqueFactorizationMonoid
  结论: [IsCancelMulZero R]
  证明: let p := Classical.choose hR
  let spec := Classical.choose_spec hR
  UniqueFactorizationMonoid.of_exists_prime_factors fun x hx => by
    use Multiset.replicate (Classical.choose (spec.2 hx)) p
    constructor
    · intro q hq
      have hpq := Multiset.eq_of_mem_replicate hq
      rw [hpq]
      r

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Multiset, Multiset.eq_of_mem_replicate, Multiset.replicate, UniqueFactorizationMonoid, UniqueFactorizationMonoid.of_exists_prime_factors, Units.dvd_mul_left, Units.dvd_mul_r, choose_spec, dvd_mul_left, dvd_mul_r, dvd_zero, eq_of_mem_replicate, mul_assoc, mul_left_comm, ne_zero, not_isUnit, of_exists_prime_factors
-/
theorem toUniqueFactorizationMonoid [IsCancelMulZero R]
    (hR : HasUnitMulPowIrreducibleFactorization R) :
    UniqueFactorizationMonoid R :=
  let p := Classical.choose hR
  let spec := Classical.choose_spec hR
  UniqueFactorizationMonoid.of_exists_prime_factors fun x hx => by
    use Multiset.replicate (Classical.choose (spec.2 hx)) p
    constructor
    · intro q hq
      have hpq := Multiset.eq_of_mem_replicate hq
      rw [hpq]
      refine ⟨spec.1.ne_zero, spec.1.not_isUnit, ?_⟩
      intro a b h
      by_cases ha : a = 0
      · rw [ha]
        simp only [true_or, dvd_zero]
      obtain ⟨m, u, rfl⟩ := spec.2 ha
      rw [mul_assoc]; rw [mul_left_comm]; rw [Units.dvd_mul_left] at h
      rw [Units.dvd_mul_right]
      by_cases hm : m = 0
      · simp only [hm, one_mul, pow_zero] at h ⊢
        right
        exact h
      left
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [pow_succ']
      apply dvd_mul_of_dvd_left dvd_rfl _
    · rw [Multiset.prod_replicate]
      exact Classical.choose_spec (spec.2 hx)

/--
theorem `of_ufd_of_unique_irreducible` / 定理 `of_ufd_of_unique_irreducible`

English:
theorem of_ufd_of_unique_irreducible
  statement: [UniqueFactorizationMonoid R] (h₁ : exists p : R, Irreducible p)
  proof: by
  obtain ⟨p, hp⟩ := h₁
  refine ⟨p, hp, ?_⟩
  intro x hx
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  refine ⟨Multiset.card fx, ?_⟩
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H]; rw [← Associates.prod_mk]; rw [Associates.mk_pow]; rw [← Multiset.prod_re

中文:
定理 of_ufd_of_unique_irreducible
  结论: [UniqueFactorizationMonoid R] (h₁ : 存在 p : R, Irreducible p)
  证明: by
  obtain ⟨p, hp⟩ := h₁
  refine ⟨p, hp, ?_⟩
  intro x hx
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  refine ⟨Multiset.card fx, ?_⟩
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H]; rw [← Associates.prod_mk]; rw [Associates.mk_pow]; rw [← Multiset.prod_re

Depends on / 依赖: Associates, Associates.mk_eq_mk_iff_associated, Associates.mk_pow, Associates.prod_mk, Multiset, Multiset.card, Multiset.card_map, Multiset.eq_replicate, Multiset.mem_map, Multiset.prod_replicate, WfDvdMonoid, WfDvdMonoid.exists_factors, and_imp, card_map, eq_replicate, exists_factors, exists_imp, mem_map, mk_eq_mk_iff_associated, mk_pow
-/
theorem of_ufd_of_unique_irreducible [UniqueFactorizationMonoid R] (h₁ : exists p : R, Irreducible p)
    (h₂ : forall ⦃p q : R⦄, Irreducible p -> Irreducible q -> Associated p q) :
    HasUnitMulPowIrreducibleFactorization R := by
  obtain ⟨p, hp⟩ := h₁
  refine ⟨p, hp, ?_⟩
  intro x hx
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  refine ⟨Multiset.card fx, ?_⟩
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H]; rw [← Associates.prod_mk]; rw [Associates.mk_pow]; rw [← Multiset.prod_replicate]
  congr 1
  symm
  rw [Multiset.eq_replicate]
  simp only [true_and, and_imp, Multiset.card_map, Multiset.mem_map, exists_imp]
  rintro _ q hq rfl
  rw [Associates.mk_eq_mk_iff_associated]
  apply h₂ (hfx.1 _ hq) hp

end HasUnitMulPowIrreducibleFactorization

/--
theorem `aux_pid_of_ufd_of_unique_irreducible` / 定理 `aux_pid_of_ufd_of_unique_irreducible`

English:
theorem aux_pid_of_ufd_of_unique_irreducible
  statement: (R : Type u) [CommRing R]
  proof: by
  classical
  constructor
  intro I
  by_cases I0 : I = ⊥
  · rw [I0]
    use 0
    simp only [Set.singleton_zero, Submodule.span_zero]
  obtain ⟨x, hxI, hx0⟩ : exists x in I, x != (0 : R) := I.ne_bot_iff.mp I0
  obtain ⟨p, _, H⟩ := HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique_irreducib

中文:
定理 aux_pid_of_ufd_of_unique_irreducible
  结论: (R : 类型u) [CommRing R]
  证明: by
  classical
  constructor
  intro I
  by_cases I0 : I = ⊥
  · rw [I0]
    use 0
    simp only [Set.singleton_zero, Submodule.span_zero]
  obtain ⟨x, hxI, hx0⟩ : exists x in I, x != (0 : R) := I.ne_bot_iff.mp I0
  obtain ⟨p, _, H⟩ := HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique_irreducib

Depends on / 依赖: HasUnitMulPowIrreducibleFactorization, HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique_irreducible, I.mul_mem_right, I.ne_bot_iff.mp, Ideal.span, Nat.find, Set.singleton_zero, Submodule, Submodule.span_zero, Units.mul_inv_cancel_right, classical, mul_inv_cancel_right, mul_mem_right, ne_bot_iff, of_ufd_of_unique_irreducible, singleton_zero, span_zero
-/
theorem aux_pid_of_ufd_of_unique_irreducible (R : Type u) [CommRing R]
    [UniqueFactorizationMonoid R] (h₁ : exists p : R, Irreducible p)
    (h₂ : forall ⦃p q : R⦄, Irreducible p -> Irreducible q -> Associated p q) :
    IsPrincipalIdealRing R := by
  classical
  constructor
  intro I
  by_cases I0 : I = ⊥
  · rw [I0]
    use 0
    simp only [Set.singleton_zero, Submodule.span_zero]
  obtain ⟨x, hxI, hx0⟩ : exists x in I, x != (0 : R) := I.ne_bot_iff.mp I0
  obtain ⟨p, _, H⟩ := HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique_irreducible h₁ h₂
  have ex : exists n : Nat, p ^ n in I := by
    obtain ⟨n, u, rfl⟩ := H hx0
    refine ⟨n, ?_⟩
    simpa only [Units.mul_inv_cancel_right] using I.mul_mem_right (↑u⁻¹) hxI
  constructor
  use p ^ Nat.find ex
  change I = Ideal.span _
  apply le_antisymm
  · intro r hr
    by_cases hr0 : r = 0
    · simp only [hr0, Submodule.zero_mem]
    obtain ⟨n, u, rfl⟩ := H hr0
    simp only [mem_span_singleton, Units.isUnit, IsUnit.dvd_mul_right]
    apply pow_dvd_pow
    apply Nat.find_min'
    simpa only [Units.mul_inv_cancel_right] using I.mul_mem_right (↑u⁻¹) hr
  · rw [span_singleton_le_iff_mem]
    exact Nat.find_spec ex

/--
theorem `of_ufd_of_unique_irreducible` / 定理 `of_ufd_of_unique_irreducible`

English:
theorem of_ufd_of_unique_irreducible
  statement: {R : Type u} [CommRing R] [IsDomain R]
  proof: by
  rw [iff_pid_with_one_nonzero_prime]
  have PID : IsPrincipalIdealRing R := aux_pid_of_ufd_of_unique_irreducible R h₁ h₂
  obtain ⟨p, hp⟩ := h₁
  refine ⟨PID, ⟨Ideal.span {p}, ⟨?_, ?_⟩, ?_⟩⟩
  · rw [Submodule.ne_bot_iff]
    exact ⟨p, Ideal.mem_span_singleton.mpr (dvd_refl p), hp.ne_zero⟩
  · rw

中文:
定理 of_ufd_of_unique_irreducible
  结论: {R : 类型u} [CommRing R] [IsDomain R]
  证明: by
  rw [iff_pid_with_one_nonzero_prime]
  have PID : IsPrincipalIdealRing R := aux_pid_of_ufd_of_unique_irreducible R h₁ h₂
  obtain ⟨p, hp⟩ := h₁
  refine ⟨PID, ⟨Ideal.span {p}, ⟨?_, ?_⟩, ?_⟩⟩
  · rw [Submodule.ne_bot_iff]
    exact ⟨p, Ideal.mem_span_singleton.mpr (dvd_refl p), hp.ne_zero⟩
  · rw

Depends on / 依赖: Ideal.mem_span_singleton.mpr, Ideal.span, Ideal.span_singleton_prime, IsPrincipal, IsPrincipalIdealRing, Submodule, Submodule.IsPrincipal.span_singleton_generator, Submodule.ne_bot_iff, UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime, aux_pid_of_ufd_of_unique_irreducible, dvd_refl, hp.ne_zero, iff_pid_with_one_nonzero_prime, irreducible_iff_prime, mem_span_singleton, ne_bot_iff, ne_zero, span_singleton_eq_span_singleton, span_singleton_eq_span_singleton.mp
-/
theorem of_ufd_of_unique_irreducible {R : Type u} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h₁ : exists p : R, Irreducible p)
    (h₂ : forall ⦃p q : R⦄, Irreducible p -> Irreducible q -> Associated p q) :
    IsDiscreteValuationRing R := by
  rw [iff_pid_with_one_nonzero_prime]
  have PID : IsPrincipalIdealRing R := aux_pid_of_ufd_of_unique_irreducible R h₁ h₂
  obtain ⟨p, hp⟩ := h₁
  refine ⟨PID, ⟨Ideal.span {p}, ⟨?_, ?_⟩, ?_⟩⟩
  · rw [Submodule.ne_bot_iff]
    exact ⟨p, Ideal.mem_span_singleton.mpr (dvd_refl p), hp.ne_zero⟩
  · rwa [Ideal.span_singleton_prime hp.ne_zero, ← UniqueFactorizationMonoid.irreducible_iff_prime]
  · intro I
    rw [← Submodule.IsPrincipal.span_singleton_generator I]
    rintro ⟨I0, hI⟩
    apply span_singleton_eq_span_singleton.mpr
    apply h₂ _ hp
    rw [Ne]; rw [Submodule.span_singleton_eq_bot] at I0
    rwa [UniqueFactorizationMonoid.irreducible_iff_prime, ← Ideal.span_singleton_prime I0]

/--
theorem `ofHasUnitMulPowIrreducibleFactorization` / 定理 `ofHasUnitMulPowIrreducibleFactorization`

English:
theorem ofHasUnitMulPowIrreducibleFactorization
  statement: {R : Type u} [CommRing R] [IsDomain R]
  proof: by
  let : UniqueFactorizationMonoid R := hR.toUniqueFactorizationMonoid
  apply of_ufd_of_unique_irreducible _ hR.unique_irreducible
  obtain ⟨p, hp, H⟩ := hR
  exact ⟨p, hp⟩

中文:
定理 ofHasUnitMulPowIrreducibleFactorization
  结论: {R : 类型u} [CommRing R] [IsDomain R]
  证明: by
  let : UniqueFactorizationMonoid R := hR.toUniqueFactorizationMonoid
  apply of_ufd_of_unique_irreducible _ hR.unique_irreducible
  obtain ⟨p, hp, H⟩ := hR
  exact ⟨p, hp⟩

Depends on / 依赖: UniqueFactorizationMonoid, hR.toUniqueFactorizationMonoid, hR.unique_irreducible, of_ufd_of_unique_irreducible, toUniqueFactorizationMonoid, unique_irreducible
-/
theorem ofHasUnitMulPowIrreducibleFactorization {R : Type u} [CommRing R] [IsDomain R]
    (hR : HasUnitMulPowIrreducibleFactorization R) : IsDiscreteValuationRing R := by
  let : UniqueFactorizationMonoid R := hR.toUniqueFactorizationMonoid
  apply of_ufd_of_unique_irreducible _ hR.unique_irreducible
  obtain ⟨p, hp, H⟩ := hR
  exact ⟨p, hp⟩

/--
theorem `RingEquivClass.isDiscreteValuationRing` / 定理 `RingEquivClass.isDiscreteValuationRing`

English:
theorem RingEquivClass.isDiscreteValuationRing
  statement: {A B E : Type*} [CommRing A] [IsDomain A]
  proof: (isPrincipalIdealRing_iff _).1
    .of_surjective _ (EquivLike.surjective e)
  __ : IsLocalRing B := (RingEquivClass.toRingEquiv e).isLocalRing
  not_a_field' := by
    obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr
 IsDiscreteValuationRing.not_a_field A)
    rw [Submodule.

中文:
定理 RingEquivClass.isDiscreteValuationRing
  结论: {A B E : 类型} [CommRing A] [IsDomain A]
  证明: (isPrincipalIdealRing_iff _).1
    .of_surjective _ (EquivLike.surjective e)
  __ : IsLocalRing B := (RingEquivClass.toRingEquiv e).isLocalRing
  not_a_field' := by
    obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr
 IsDiscreteValuationRing.not_a_field A)
    rw [Submodule.

Depends on / 依赖: isPrincipalIdealRing_iff
-/
theorem RingEquivClass.isDiscreteValuationRing {A B E : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing A] [EquivLike E A B] [RingEquivClass E A B]
    (e : E) : IsDiscreteValuationRing B where
principal := (isPrincipalIdealRing_iff _).1
    .of_surjective _ (EquivLike.surjective e)
  __ : IsLocalRing B := (RingEquivClass.toRingEquiv e).isLocalRing
  not_a_field' := by
    obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr
 IsDiscreteValuationRing.not_a_field A)
    rw [Submodule.ne_bot_iff]
    refine ⟨e a, ⟨?_, by simp only [ne_eq, EmbeddingLike.map_eq_zero_iff, ZeroMemClass.coe_eq_zero,
      ha, not_false_eq_true]⟩⟩
    rw [IsLocalRing.mem_maximalIdeal]; rw [map_mem_nonunits_iff e]; rw [← IsLocalRing.mem_maximalIdeal]
    exact a.2

section

variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {R}

/--
theorem `associated_pow_irreducible` / 定理 `associated_pow_irreducible`

English:
theorem associated_pow_irreducible
  given: {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ)
  proof: by
  have : WfDvdMonoid R := IsNoetherianRing.wfDvdMonoid
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  use Multiset.card fx
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H]; rw [← Associates.prod_mk]; rw [Associates.mk_pow]; rw [← Multiset.prod_replicate]
  

中文:
定理 associated_pow_irreducible
  条件: {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ)
  证明: by
  have : WfDvdMonoid R := IsNoetherianRing.wfDvdMonoid
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  use Multiset.card fx
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H]; rw [← Associates.prod_mk]; rw [Associates.mk_pow]; rw [← Multiset.prod_replicate]
  

Depends on / 依赖: Associates, Associates.mk_eq_mk_iff_associated, Associates.mk_pow, Associates.prod_mk, IsNoetherianRing, IsNoetherianRing.wfDvdMonoid, Multiset, Multiset.card, Multiset.card_map, Multiset.eq_replicate, Multiset.mem_map, Multiset.prod_replicate, WfDvdMonoid, WfDvdMonoid.exists_factors, and_imp, associated_of_irreducible, card_map, eq_replicate, exists_factors, exists_imp
-/
theorem associated_pow_irreducible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) :
    exists n : Nat, Associated x (ϖ ^ n) := by
  have : WfDvdMonoid R := IsNoetherianRing.wfDvdMonoid
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  use Multiset.card fx
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H]; rw [← Associates.prod_mk]; rw [Associates.mk_pow]; rw [← Multiset.prod_replicate]
  congr 1
  rw [Multiset.eq_replicate]
  simp only [true_and, and_imp, Multiset.card_map, Multiset.mem_map, exists_imp]
  rintro _ _ _ rfl
  rw [Associates.mk_eq_mk_iff_associated]
  refine associated_of_irreducible _ ?_ hirr
  apply hfx.1
  assumption

/--
theorem `eq_unit_mul_pow_irreducible` / 定理 `eq_unit_mul_pow_irreducible`

English:
theorem eq_unit_mul_pow_irreducible
  given: {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ)
  proof: by
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx hirr
  obtain ⟨u, rfl⟩ := hn.symm
  use n, u
  apply mul_comm

中文:
定理 eq_unit_mul_pow_irreducible
  条件: {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ)
  证明: by
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx hirr
  obtain ⟨u, rfl⟩ := hn.symm
  use n, u
  apply mul_comm

Depends on / 依赖: associated_pow_irreducible, hn.symm, mul_comm
-/
theorem eq_unit_mul_pow_irreducible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) :
    exists (n : Nat) (u : Rˣ), x = u * ϖ ^ n := by
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx hirr
  obtain ⟨u, rfl⟩ := hn.symm
  use n, u
  apply mul_comm

/--
lemma `exists_units_eq_smul_zpow_of_irreducible` / 引理 `exists_units_eq_smul_zpow_of_irreducible`

English:
lemma exists_units_eq_smul_zpow_of_irreducible
  proof: by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible (x := x) (by simp_all) hϖ
  obtain ⟨m, v, rfl⟩ := eq_unit_mul_pow_irreducible (by simpa using hy) hϖ
  have hϖ' : algebraMap R K ϖ != 0 := by simpa using hϖ.ne_zero
  refine ⟨n

中文:
引理 exists_units_eq_smul_zpow_of_irreducible
  证明: by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible (x := x) (by simp_all) hϖ
  obtain ⟨m, v, rfl⟩ := eq_unit_mul_pow_irreducible (by simpa using hy) hϖ
  have hϖ' : algebraMap R K ϖ != 0 := by simpa using hϖ.ne_zero
  refine ⟨n

Depends on / 依赖: Algebra, Algebra.smul_def, IsFractionRing, IsFractionRing.div_surjective, Units.smul_def, algebraMap, div_smul_div_comm, div_surjective, eq_unit_mul_pow_irreducible, ne_zero, smul_def
-/
lemma exists_units_eq_smul_zpow_of_irreducible
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) {x : K} (hx : x != 0) :
    exists (n : Int) (u : Rˣ), x = u • algebraMap R K ϖ ^ n := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible (x := x) (by simp_all) hϖ
  obtain ⟨m, v, rfl⟩ := eq_unit_mul_pow_irreducible (by simpa using hy) hϖ
  have hϖ' : algebraMap R K ϖ != 0 := by simpa using hϖ.ne_zero
  refine ⟨n - m, u / v, ?_⟩
  simp [hϖ', zpow_sub₀, div_smul_div_comm, Units.smul_def u, Units.smul_def v, Algebra.smul_def]

open Submodule.IsPrincipal

/--
theorem `ideal_eq_span_pow_irreducible` / 定理 `ideal_eq_span_pow_irreducible`

English:
theorem ideal_eq_span_pow_irreducible
  given: {s : Ideal R} (hs : s != ⊥) {ϖ : R} (hirr : Irreducible ϖ)
  proof: by
  have gen_ne_zero : generator s != 0 := by
    rw [Ne]; rw [← eq_bot_iff_generator_eq_zero]
    assumption
  rcases associated_pow_irreducible gen_ne_zero hirr with ⟨n, u, hnu⟩
  use n
  have : span _ = _ := Ideal.span_singleton_generator s
  rw [← this]; rw [← hnu]; rw [span_singleton_eq_span_s

中文:
定理 ideal_eq_span_pow_irreducible
  条件: {s : Ideal R} (hs : s != ⊥) {ϖ : R} (hirr : Irreducible ϖ)
  证明: by
  have gen_ne_zero : generator s != 0 := by
    rw [Ne]; rw [← eq_bot_iff_generator_eq_zero]
    assumption
  rcases associated_pow_irreducible gen_ne_zero hirr with ⟨n, u, hnu⟩
  use n
  have : span _ = _ := Ideal.span_singleton_generator s
  rw [← this]; rw [← hnu]; rw [span_singleton_eq_span_s

Depends on / 依赖: Ideal.span_singleton_generator, associated_pow_irreducible, eq_bot_iff_generator_eq_zero, gen_ne_zero, generator, span_singleton_eq_span_singleton, span_singleton_generator
-/
theorem ideal_eq_span_pow_irreducible {s : Ideal R} (hs : s != ⊥) {ϖ : R} (hirr : Irreducible ϖ) :
    exists n : Nat, s = Ideal.span {ϖ ^ n} := by
  have gen_ne_zero : generator s != 0 := by
    rw [Ne]; rw [← eq_bot_iff_generator_eq_zero]
    assumption
  rcases associated_pow_irreducible gen_ne_zero hirr with ⟨n, u, hnu⟩
  use n
  have : span _ = _ := Ideal.span_singleton_generator s
  rw [← this]; rw [← hnu]; rw [span_singleton_eq_span_singleton]
  use u

/--
theorem `unit_mul_pow_congr_pow` / 定理 `unit_mul_pow_congr_pow`

English:
theorem unit_mul_pow_congr_pow
  statement: {p q : R} (hp : Irreducible p) (hq : Irreducible q) (u v : Rˣ)
  proof: by
  have key : Associated (Multiset.replicate m p).prod (Multiset.replicate n q).prod := by
    rw [Multiset.prod_replicate]; rw [Multiset.prod_replicate]; rw [Associated]
    refine ⟨u * v⁻¹, ?_⟩
    simp only [Units.val_mul]
    rw [mul_left_comm]; rw [← mul_assoc]; rw [h]; rw [mul_right_comm]; r

中文:
定理 unit_mul_pow_congr_pow
  结论: {p q : R} (hp : Irreducible p) (hq : Irreducible q) (u v : Rˣ)
  证明: by
  have key : Associated (Multiset.replicate m p).prod (Multiset.replicate n q).prod := by
    rw [Multiset.prod_replicate]; rw [Multiset.prod_replicate]; rw [Associated]
    refine ⟨u * v⁻¹, ?_⟩
    simp only [Units.val_mul]
    rw [mul_left_comm]; rw [← mul_assoc]; rw [h]; rw [mul_right_comm]; r

Depends on / 依赖: Associated, Multiset, Multiset.card_eq_card_of_rel, Multiset.eq_of_mem_replicate, Multiset.prod_replicate, Multiset.replicate, UniqueFactorizationMonoid, UniqueFactorizationMonoid.factors_unique, Units.mul_inv, Units.val_mul, all_goals, card_eq_card_of_rel, eq_of_mem_replicate, factors_unique, mul_assoc, mul_inv, mul_left_comm, mul_right_comm, one_mul, prod_replicate
-/
theorem unit_mul_pow_congr_pow {p q : R} (hp : Irreducible p) (hq : Irreducible q) (u v : Rˣ)
    (m n : Nat) (h : ↑u * p ^ m = v * q ^ n) : m = n := by
  have key : Associated (Multiset.replicate m p).prod (Multiset.replicate n q).prod := by
    rw [Multiset.prod_replicate]; rw [Multiset.prod_replicate]; rw [Associated]
    refine ⟨u * v⁻¹, ?_⟩
    simp only [Units.val_mul]
    rw [mul_left_comm]; rw [← mul_assoc]; rw [h]; rw [mul_right_comm]; rw [Units.mul_inv]; rw [one_mul]
  have := by
    refine Multiset.card_eq_card_of_rel (UniqueFactorizationMonoid.factors_unique ?_ ?_ key)
    all_goals
      intro x hx
      obtain rfl := Multiset.eq_of_mem_replicate hx
      assumption
  simpa only [Multiset.card_replicate]

/--
theorem `unit_mul_pow_congr_unit` / 定理 `unit_mul_pow_congr_unit`

English:
theorem unit_mul_pow_congr_unit
  statement: {ϖ : R} (hirr : Irreducible ϖ) (u v : Rˣ) (m n : Nat)
  proof: by
  obtain rfl : m = n := unit_mul_pow_congr_pow hirr hirr u v m n h
  rw [← sub_eq_zero] at h
  rw [← sub_mul]; rw [mul_eq_zero] at h
  rcases h with h | h
  · rw [sub_eq_zero] at h
    exact mod_cast h
  · apply (hirr.ne_zero (eq_zero_of_pow_eq_zero h)).elim

中文:
定理 unit_mul_pow_congr_unit
  结论: {ϖ : R} (hirr : Irreducible ϖ) (u v : Rˣ) (m n : 自然数)
  证明: by
  obtain rfl : m = n := unit_mul_pow_congr_pow hirr hirr u v m n h
  rw [← sub_eq_zero] at h
  rw [← sub_mul]; rw [mul_eq_zero] at h
  rcases h with h | h
  · rw [sub_eq_zero] at h
    exact mod_cast h
  · apply (hirr.ne_zero (eq_zero_of_pow_eq_zero h)).elim

Depends on / 依赖: eq_zero_of_pow_eq_zero, hirr.ne_zero, mod_cast, mul_eq_zero, ne_zero, sub_eq_zero, sub_mul, unit_mul_pow_congr_pow
-/
theorem unit_mul_pow_congr_unit {ϖ : R} (hirr : Irreducible ϖ) (u v : Rˣ) (m n : Nat)
    (h : ↑u * ϖ ^ m = v * ϖ ^ n) : u = v := by
  obtain rfl : m = n := unit_mul_pow_congr_pow hirr hirr u v m n h
  rw [← sub_eq_zero] at h
  rw [← sub_mul]; rw [mul_eq_zero] at h
  rcases h with h | h
  · rw [sub_eq_zero] at h
    exact mod_cast h
  · apply (hirr.ne_zero (eq_zero_of_pow_eq_zero h)).elim

/-!
## The additive valuation on a DVR
-/

/--
Definition of `addVal` / `addVal` 的定义

English:
definition addVal
  signature: (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  body: multiplicity_addValuation (Classical.choose_spec (exists_prime R))

中文:
定义 addVal
  签名: (R : 类型u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  定义体: multiplicity_addValuation (Classical.choose_spec (exists_prime R))

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_prime, multiplicity_addValuation
-/
noncomputable def addVal (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    AddValuation R Nat∞ :=
  multiplicity_addValuation (Classical.choose_spec (exists_prime R))

/--
theorem `addVal_def` / 定理 `addVal_def`

English:
theorem addVal_def
  given: (r : R) (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : Nat) (hr : r = u * ϖ ^ n)
  proof: by
  rw [addVal]; rw [multiplicity_addValuation_apply]; rw [hr]; rw [emultiplicity_eq_of_associated_left
      (associated_of_irreducible R hϖ (Classical.choose_spec (exists_prime R)).irreducible)]; rw [emultiplicity_eq_of_associated_right (Associated.symm ⟨u]; rw [mul_comm _ _⟩)]; rw [emultiplicity

中文:
定理 addVal_def
  条件: (r : R) (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : 自然数) (hr : r = u * ϖ ^ n)
  证明: by
  rw [addVal]; rw [multiplicity_addValuation_apply]; rw [hr]; rw [emultiplicity_eq_of_associated_left
      (associated_of_irreducible R hϖ (Classical.choose_spec (exists_prime R)).irreducible)]; rw [emultiplicity_eq_of_associated_right (Associated.symm ⟨u]; rw [mul_comm _ _⟩)]; rw [emultiplicity

Depends on / 依赖: Associated, Associated.symm, Classical, Classical.choose_spec, addVal, associated_of_irreducible, choose_spec, emultiplicity_eq_of_associated_left, emultiplicity_eq_of_associated_right, emultiplicity_pow_self_of_prime, exists_prime, irreducible, irreducible_iff_prime, mul_comm, multiplicity_addValuation_apply
-/
theorem addVal_def (r : R) (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : Nat) (hr : r = u * ϖ ^ n) :
    addVal R r = n := by
  rw [addVal]; rw [multiplicity_addValuation_apply]; rw [hr]; rw [emultiplicity_eq_of_associated_left
      (associated_of_irreducible R hϖ (Classical.choose_spec (exists_prime R)).irreducible)]; rw [emultiplicity_eq_of_associated_right (Associated.symm ⟨u]; rw [mul_comm _ _⟩)]; rw [emultiplicity_pow_self_of_prime (irreducible_iff_prime.1 hϖ)]

/--
theorem `addVal_def'` / 定理 `addVal_def'`

English:
theorem addVal_def'
  given: (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : Nat)
  proof: addVal_def _ u hϖ n rfl

中文:
定理 addVal_def'
  条件: (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : 自然数)
  证明: addVal_def _ u hϖ n rfl

Depends on / 依赖: addVal_def
-/
theorem addVal_def' (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : Nat) :
    addVal R ((u : R) * ϖ ^ n) = n :=
  addVal_def _ u hϖ n rfl

/--
theorem `addVal_zero` / 定理 `addVal_zero`

English:
theorem addVal_zero
  statement: addVal R 0 = ⊤
  proof: (addVal R).map_zero

中文:
定理 addVal_zero
  结论: addVal R 0 = ⊤
  证明: (addVal R).map_zero

Depends on / 依赖: addVal, map_zero
-/
theorem addVal_zero : addVal R 0 = ⊤ :=
  (addVal R).map_zero

/--
theorem `addVal_one` / 定理 `addVal_one`

English:
theorem addVal_one
  statement: addVal R 1 = 0
  proof: (addVal R).map_one

@[simp]

中文:
定理 addVal_one
  结论: addVal R 1 = 0
  证明: (addVal R).map_one

@[simp]

Depends on / 依赖: addVal, map_one
-/
theorem addVal_one : addVal R 1 = 0 :=
  (addVal R).map_one

@[simp]
/--
theorem `addVal_uniformizer` / 定理 `addVal_uniformizer`

English:
theorem addVal_uniformizer
  given: {ϖ : R} (hϖ : Irreducible ϖ)
  statement: addVal R ϖ = 1
  proof: by
  simpa only [one_mul, eq_self_iff_true, Units.val_one, pow_one, forall_true_left, Nat.cast_one]
    using addVal_def ϖ 1 hϖ 1

中文:
定理 addVal_uniformizer
  条件: {ϖ : R} (hϖ : Irreducible ϖ)
  结论: addVal R ϖ = 1
  证明: by
  simpa only [one_mul, eq_self_iff_true, Units.val_one, pow_one, forall_true_left, Nat.cast_one]
    using addVal_def ϖ 1 hϖ 1

Depends on / 依赖: Nat.cast_one, Units.val_one, addVal_def, cast_one, eq_self_iff_true, forall_true_left, one_mul, pow_one, val_one
-/
theorem addVal_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) : addVal R ϖ = 1 := by
  simpa only [one_mul, eq_self_iff_true, Units.val_one, pow_one, forall_true_left, Nat.cast_one]
    using addVal_def ϖ 1 hϖ 1

/--
theorem `addVal_mul` / 定理 `addVal_mul`

English:
theorem addVal_mul
  given: {a b : R}
  proof: (addVal R).map_mul _ _

中文:
定理 addVal_mul
  条件: {a b : R}
  证明: (addVal R).map_mul _ _

Depends on / 依赖: addVal, map_mul
-/
theorem addVal_mul {a b : R} :
    addVal R (a * b) = addVal R a + addVal R b :=
  (addVal R).map_mul _ _

/--
theorem `addVal_pow` / 定理 `addVal_pow`

English:
theorem addVal_pow
  given: (a : R) (n : Nat)
  statement: addVal R (a ^ n) = n • addVal R a
  proof: (addVal R).map_pow _ _

nonrec theorem _root_.Irreducible.addVal_pow {ϖ : R} (h : Irreducible ϖ) (n : Nat) :
    addVal R (ϖ ^ n) = n := by
  rw [addVal_pow]; rw [addVal_uniformizer h]; rw [nsmul_one]

中文:
定理 addVal_pow
  条件: (a : R) (n : 自然数)
  结论: addVal R (a ^ n) = n • addVal R a
  证明: (addVal R).map_pow _ _

nonrec theorem _root_.Irreducible.addVal_pow {ϖ : R} (h : Irreducible ϖ) (n : Nat) :
    addVal R (ϖ ^ n) = n := by
  rw [addVal_pow]; rw [addVal_uniformizer h]; rw [nsmul_one]

Depends on / 依赖: addVal, map_pow
-/
theorem addVal_pow (a : R) (n : Nat) : addVal R (a ^ n) = n • addVal R a :=
  (addVal R).map_pow _ _

nonrec theorem _root_.Irreducible.addVal_pow {ϖ : R} (h : Irreducible ϖ) (n : Nat) :
    addVal R (ϖ ^ n) = n := by
  rw [addVal_pow]; rw [addVal_uniformizer h]; rw [nsmul_one]

/--
theorem `addVal_eq_top_iff` / 定理 `addVal_eq_top_iff`

English:
theorem addVal_eq_top_iff
  given: {a : R}
  statement: addVal R a = ⊤ ↔ a = 0
  proof: by
  have hi := (Classical.choose_spec (exists_prime R)).irreducible
  constructor
  · contrapose
    intro h
    obtain ⟨n, ha⟩ := associated_pow_irreducible h hi
    obtain ⟨u, rfl⟩ := ha.symm
    rw [mul_comm]; rw [addVal_def' u hi n]
    nofun
  · rintro rfl
    exact addVal_zero

中文:
定理 addVal_eq_top_iff
  条件: {a : R}
  结论: addVal R a = ⊤ ↔ a = 0
  证明: by
  have hi := (Classical.choose_spec (exists_prime R)).irreducible
  constructor
  · contrapose
    intro h
    obtain ⟨n, ha⟩ := associated_pow_irreducible h hi
    obtain ⟨u, rfl⟩ := ha.symm
    rw [mul_comm]; rw [addVal_def' u hi n]
    nofun
  · rintro rfl
    exact addVal_zero

Depends on / 依赖: Classical, Classical.choose_spec, addVal_def, addVal_zero, associated_pow_irreducible, choose_spec, contrapose, exists_prime, ha.symm, irreducible, mul_comm
-/
theorem addVal_eq_top_iff {a : R} : addVal R a = ⊤ ↔ a = 0 := by
  have hi := (Classical.choose_spec (exists_prime R)).irreducible
  constructor
  · contrapose
    intro h
    obtain ⟨n, ha⟩ := associated_pow_irreducible h hi
    obtain ⟨u, rfl⟩ := ha.symm
    rw [mul_comm]; rw [addVal_def' u hi n]
    nofun
  · rintro rfl
    exact addVal_zero

/--
theorem `addVal_le_iff_dvd` / 定理 `addVal_le_iff_dvd`

English:
theorem addVal_le_iff_dvd
  given: {a b : R}
  statement: addVal R a <= addVal R b ↔ a ∣ b
  proof: by
  have hp := Classical.choose_spec (exists_prime R)
  constructor <;> intro h
  · by_cases ha0 : a = 0
    · rw [ha0, addVal_zero, top_le_iff, addVal_eq_top_iff] at h
      rw [h]
      apply dvd_zero
    obtain ⟨n, ha⟩ := associated_pow_irreducible ha0 hp.irreducible
    rw [addVal]; rw [multipl

中文:
定理 addVal_le_iff_dvd
  条件: {a b : R}
  结论: addVal R a <= addVal R b ↔ a ∣ b
  证明: by
  have hp := Classical.choose_spec (exists_prime R)
  constructor <;> intro h
  · by_cases ha0 : a = 0
    · rw [ha0, addVal_zero, top_le_iff, addVal_eq_top_iff] at h
      rw [h]
      apply dvd_zero
    obtain ⟨n, ha⟩ := associated_pow_irreducible ha0 hp.irreducible
    rw [addVal]; rw [multipl

Depends on / 依赖: Classical, Classical.choose_spec, addVal, addVal_eq_top_iff, addVal_zero, associated_pow_irreducible, choose_spec, dvd_zero, emultiplicity_le_emultiplicity_iff, exists_prime, ha.dvd.trans, ha.symm.dvd, hp.irreducible, irreducible, multiplicity_addValuation_apply, top_le_iff
-/
theorem addVal_le_iff_dvd {a b : R} : addVal R a <= addVal R b ↔ a ∣ b := by
  have hp := Classical.choose_spec (exists_prime R)
  constructor <;> intro h
  · by_cases ha0 : a = 0
    · rw [ha0, addVal_zero, top_le_iff, addVal_eq_top_iff] at h
      rw [h]
      apply dvd_zero
    obtain ⟨n, ha⟩ := associated_pow_irreducible ha0 hp.irreducible
    rw [addVal]; rw [multiplicity_addValuation_apply]; rw [multiplicity_addValuation_apply]; rw [emultiplicity_le_emultiplicity_iff] at h
    exact ha.dvd.trans (h n ha.symm.dvd)
  · rw [addVal, multiplicity_addValuation_apply, multiplicity_addValuation_apply]
    exact emultiplicity_le_emultiplicity_of_dvd_right h

/--
theorem `addVal_add` / 定理 `addVal_add`

English:
theorem addVal_add
  given: {a b : R}
  statement: min (addVal R a) (addVal R b) <= addVal R (a + b)
  proof: (addVal R).map_add _ _

@[simp]

中文:
定理 addVal_add
  条件: {a b : R}
  结论: min (addVal R a) (addVal R b) <= addVal R (a + b)
  证明: (addVal R).map_add _ _

@[simp]

Depends on / 依赖: addVal, map_add
-/
theorem addVal_add {a b : R} : min (addVal R a) (addVal R b) <= addVal R (a + b) :=
  (addVal R).map_add _ _

@[simp]
/--
lemma `addVal_eq_zero_of_unit` / 引理 `addVal_eq_zero_of_unit`

English:
lemma addVal_eq_zero_of_unit
  given: (u : Rˣ)
  proof: by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [addVal_def (u : R) u hϖ 0] <;>
  simp

中文:
引理 addVal_eq_zero_of_unit
  条件: (u : Rˣ)
  证明: by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [addVal_def (u : R) u hϖ 0] <;>
  simp

Depends on / 依赖: addVal_def, exists_irreducible
-/
lemma addVal_eq_zero_of_unit (u : Rˣ) :
    addVal R u = 0 := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [addVal_def (u : R) u hϖ 0] <;>
  simp

/--
lemma `addVal_eq_zero_iff` / 引理 `addVal_eq_zero_iff`

English:
lemma addVal_eq_zero_iff
  given: {x : R}
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  simp [isUnit_pow_iff_of_not_isUnit hϖ.not_isUnit, hϖ]

中文:
引理 addVal_eq_zero_iff
  条件: {x : R}
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  simp [isUnit_pow_iff_of_not_isUnit hϖ.not_isUnit, hϖ]

Depends on / 依赖: eq_or_ne, eq_unit_mul_pow_irreducible, exists_irreducible, isUnit_pow_iff_of_not_isUnit, not_isUnit
-/
lemma addVal_eq_zero_iff {x : R} :
    addVal R x = 0 ↔ IsUnit x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  simp [isUnit_pow_iff_of_not_isUnit hϖ.not_isUnit, hϖ]

/--
lemma `addVal_eq_iff_associated` / 引理 `addVal_eq_iff_associated`

English:
lemma addVal_eq_iff_associated
  given: (x y : R)
  proof: by
  constructor
  · intro h
    by_cases hx : x = 0
    · simp_all only [AddValuation.map_zero]
      rw [addVal_eq_top_iff.mp h.symm]
    by_cases hy : y = 0
    · simp_all only [AddValuation.map_zero, associated_zero_iff_eq_zero]
      exact hx (addVal_eq_top_iff.mp h)
    obtain ⟨ϖ, hϖ⟩ := exist

中文:
引理 addVal_eq_iff_associated
  条件: (x y : R)
  证明: by
  constructor
  · intro h
    by_cases hx : x = 0
    · simp_all only [AddValuation.map_zero]
      rw [addVal_eq_top_iff.mp h.symm]
    by_cases hy : y = 0
    · simp_all only [AddValuation.map_zero, associated_zero_iff_eq_zero]
      exact hx (addVal_eq_top_iff.mp h)
    obtain ⟨ϖ, hϖ⟩ := exist

Depends on / 依赖: AddValuation, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_zero, addVal_eq_top_iff, addVal_eq_top_iff.mp, addVal_eq_zero_of_unit, associated_zero_iff_eq_zero, eq_unit_mul_pow_irreducible, exists_irreducible, h.symm, map_mul, map_pow, map_zero, nsmul_eq_mul, zero_add
-/
lemma addVal_eq_iff_associated (x y : R) :
    addVal R x = addVal R y ↔ Associated x y := by
  constructor
  · intro h
    by_cases hx : x = 0
    · simp_all only [AddValuation.map_zero]
      rw [addVal_eq_top_iff.mp h.symm]
    by_cases hy : y = 0
    · simp_all only [AddValuation.map_zero, associated_zero_iff_eq_zero]
      exact hx (addVal_eq_top_iff.mp h)
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    obtain ⟨m, α, hx'⟩ := eq_unit_mul_pow_irreducible hx hϖ
    obtain ⟨n, β, hy'⟩ := eq_unit_mul_pow_irreducible hy hϖ
    simp only [hx', AddValuation.map_mul, addVal_eq_zero_of_unit, AddValuation.map_pow,
      nsmul_eq_mul, zero_add, hy', associated_unit_mul_right_iff,
      associated_unit_mul_left_iff] at h ⊢
    simp only [addVal_uniformizer hϖ, mul_one, ENat.natCast_inj] at h
    rw [h]
    exact Associates.mk_eq_mk_iff_associated.mp rfl
  · rintro ⟨u, rfl⟩
    simp_all

variable (R)

set_option backward.isDefEq.respectTransparency.types false in
/-- The ideals of a discrete valuation ring are exactly the powers of the maximal ideal. -/
@[simps apply]
/--
Definition of `idealOrderIsoENat` / `idealOrderIsoENat` 的定义

English:
definition idealOrderIsoENat
  signature: : Ideal R ≃o ENatᵒᵈ where
  body: .toDual (addVal R (generator I))
  invFun n := n.ofDual.recTopCoe ⊥ (fun n => maximalIdeal R ^ n)
  left_inv I := by
    let x := generator I
    suffices (addVal R x).recTopCoe ⊥ (fun n => maximalIdeal R ^ n) = span {x} by
      rwa [Ideal.span_singleton_generator] at this
    by_cases hx0 : x = 0


中文:
定义 idealOrderIsoENat
  签名: : Ideal R ≃o E自然数ᵒᵈ where
  定义体: .toDual (addVal R (generator I))
  invFun n := n.ofDual.recTopCoe ⊥ (fun n => maximalIdeal R ^ n)
  left_inv I := by
    let x := generator I
    suffices (addVal R x).recTopCoe ⊥ (fun n => maximalIdeal R ^ n) = span {x} by
      rwa [Ideal.span_singleton_generator] at this
    by_cases hx0 : x = 0


Depends on / 依赖: addVal, generator, toDual
-/
noncomputable def idealOrderIsoENat : Ideal R ≃o ENatᵒᵈ where
  toFun I := .toDual (addVal R (generator I))
  invFun n := n.ofDual.recTopCoe ⊥ (fun n => maximalIdeal R ^ n)
  left_inv I := by
    let x := generator I
    suffices (addVal R x).recTopCoe ⊥ (fun n => maximalIdeal R ^ n) = span {x} by
      rwa [Ideal.span_singleton_generator] at this
    by_cases hx0 : x = 0
    · simp [hx0]
    · obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
      obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hx0 hϖ
      rw [hu]; rw [addVal_def' u hϖ]; rw [span_singleton_mul_left_unit u.isUnit]; rw [ENat.recTopCoe_natCast]; rw [hϖ.maximalIdeal_eq]; rw [span_singleton_pow]
  right_inv n := by
    obtain ⟨k, rfl⟩ := OrderDual.toDual.surjective n
    dsimp
    induction k with
    | top => simp
    | coe k =>
      obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
      rw [OrderDual.toDual_inj]; rw [ENat.recTopCoe_natCast]; rw [hϖ.maximalIdeal_eq]; rw [span_singleton_pow]; rw [← hϖ.addVal_pow k]; rw [addVal_eq_iff_associated]
      exact associated_generator_span_self (ϖ ^ k)
  map_rel_iff' {I J} := by
    simp [addVal_le_iff_dvd, ← span_singleton_le_span_singleton]

@[simp]
/--
theorem `idealOrderIsoENat_symm_apply_coe` / 定理 `idealOrderIsoENat_symm_apply_coe`

English:
theorem idealOrderIsoENat_symm_apply_coe
  given: (n : Nat)
  proof: rfl

中文:
定理 idealOrderIsoENat_symm_apply_coe
  条件: (n : 自然数)
  证明: rfl
-/
theorem idealOrderIsoENat_symm_apply_coe (n : Nat) :
    (idealOrderIsoENat R).symm n = maximalIdeal R ^ n :=
  rfl

variable {R} in
/--
theorem `idealOrderIsoENat_symm_apply_coe_of_irreducible` / 定理 `idealOrderIsoENat_symm_apply_coe_of_irreducible`

English:
theorem idealOrderIsoENat_symm_apply_coe_of_irreducible
  given: (n : Nat) {ϖ : R} (hϖ : Irreducible ϖ)
  proof: by
  rw [idealOrderIsoENat_symm_apply_coe]; rw [hϖ.maximalIdeal_eq]; rw [span_singleton_pow]

中文:
定理 idealOrderIsoENat_symm_apply_coe_of_irreducible
  条件: (n : 自然数) {ϖ : R} (hϖ : Irreducible ϖ)
  证明: by
  rw [idealOrderIsoENat_symm_apply_coe]; rw [hϖ.maximalIdeal_eq]; rw [span_singleton_pow]

Depends on / 依赖: idealOrderIsoENat_symm_apply_coe, maximalIdeal_eq, span_singleton_pow
-/
theorem idealOrderIsoENat_symm_apply_coe_of_irreducible (n : Nat) {ϖ : R} (hϖ : Irreducible ϖ) :
    (idealOrderIsoENat R).symm n = Ideal.span {ϖ ^ n} := by
  rw [idealOrderIsoENat_symm_apply_coe]; rw [hϖ.maximalIdeal_eq]; rw [span_singleton_pow]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `coheight_pow_maximalIdeal` / 定理 `coheight_pow_maximalIdeal`

English:
theorem coheight_pow_maximalIdeal
  given: (n : Nat)
  statement: Order.coheight (maximalIdeal R ^ n) = n
  proof: by
  simpa only [Order.coheight_toDual, Order.height_enat] using!
    Order.coheight_orderIso (idealOrderIsoENat R).symm (.toDual n)

中文:
定理 coheight_pow_maximalIdeal
  条件: (n : 自然数)
  结论: Order.coheight (maximalIdeal R ^ n) = n
  证明: by
  simpa only [Order.coheight_toDual, Order.height_enat] using!
    Order.coheight_orderIso (idealOrderIsoENat R).symm (.toDual n)

Depends on / 依赖: Order.coheight_orderIso, Order.coheight_toDual, Order.height_enat, coheight_orderIso, coheight_toDual, height_enat, idealOrderIsoENat, toDual
-/
theorem coheight_pow_maximalIdeal (n : Nat) : Order.coheight (maximalIdeal R ^ n) = n := by
  simpa only [Order.coheight_toDual, Order.height_enat] using!
    Order.coheight_orderIso (idealOrderIsoENat R).symm (.toDual n)

/--
theorem `length_quotient_pow_maximalIdeal` / 定理 `length_quotient_pow_maximalIdeal`

English:
theorem length_quotient_pow_maximalIdeal
  given: (n : Nat)
  proof: by
  rw [Module.length_quotient]; rw [coheight_pow_maximalIdeal]

中文:
定理 length_quotient_pow_maximalIdeal
  条件: (n : 自然数)
  证明: by
  rw [Module.length_quotient]; rw [coheight_pow_maximalIdeal]

Depends on / 依赖: Module, Module.length_quotient, coheight_pow_maximalIdeal, length_quotient
-/
theorem length_quotient_pow_maximalIdeal (n : Nat) :
    Module.length R (R ⧸ maximalIdeal R ^ n) = n := by
  rw [Module.length_quotient]; rw [coheight_pow_maximalIdeal]

end

instance (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsHausdorff (maximalIdeal R) R where
  haus' x hx := by
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow] at hx
    rwa [← addVal_eq_top_iff, ENat.eq_top_iff_forall_ge]

noncomputable section toEuclideanDomain
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/--
Definition of `quotient` / `quotient` 的定义

English:
definition quotient
  signature: (x y : R)
  body: open scoped Classical in if y = 0 then 0 else if h : y ∣ x then h.choose else 0

中文:
定义 quotient
  签名: (x y : R)
  定义体: open scoped Classical in if y = 0 then 0 else if h : y ∣ x then h.choose else 0

Depends on / 依赖: Classical, h.choose, scoped
-/
def quotient (x y : R) : R :=
  open scoped Classical in if y = 0 then 0 else if h : y ∣ x then h.choose else 0

/--
Definition of `remainder` / `remainder` 的定义

English:
definition remainder
  signature: (x y : R)
  body: open scoped Classical in if y ∣ x then 0 else x

中文:
定义 remainder
  签名: (x y : R)
  定义体: open scoped Classical in if y ∣ x then 0 else x

Depends on / 依赖: Classical, scoped
-/
def remainder (x y : R) : R :=
  open scoped Classical in if y ∣ x then 0 else x

/--
Definition of `toWithBotNat` / `toWithBotNat` 的定义

English:
definition toWithBotNat
  signature: (x : R)
  body: addVal R x

中文:
定义 toWithBotNat
  签名: (x : R)
  定义体: addVal R x

Depends on / 依赖: addVal
-/
def toWithBotNat (x : R) : WithBot Nat :=
  addVal R x

/--
lemma `toWithBotNat_zero` / 引理 `toWithBotNat_zero`

English:
lemma toWithBotNat_zero
  statement: toWithBotNat (R := R) 0 = ⊥
  proof: addVal_zero

中文:
引理 toWithBotNat_zero
  结论: toWithBot自然数 (R := R) 0 = ⊥
  证明: addVal_zero
-/
@[simp] lemma toWithBotNat_zero : toWithBotNat (R := R) 0 = ⊥ :=
  addVal_zero

/--
lemma `toWithBotNat_eq_bot_iff` / 引理 `toWithBotNat_eq_bot_iff`

English:
lemma toWithBotNat_eq_bot_iff
  given: (x : R)
  statement: toWithBotNat x = ⊥ ↔ x = 0
  proof: addVal_eq_top_iff

中文:
引理 toWithBotNat_eq_bot_iff
  条件: (x : R)
  结论: toWithBot自然数 x = ⊥ ↔ x = 0
  证明: addVal_eq_top_iff
-/
@[simp] lemma toWithBotNat_eq_bot_iff (x : R) : toWithBotNat x = ⊥ ↔ x = 0 :=
  addVal_eq_top_iff

/--
lemma `bot_lt_toWithBotNat_iff` / 引理 `bot_lt_toWithBotNat_iff`

English:
lemma bot_lt_toWithBotNat_iff
  given: (x : R)
  statement: ⊥ < toWithBotNat x ↔ x != 0
  proof: by
  rw [bot_lt_iff_ne_bot]; simp

中文:
引理 bot_lt_toWithBotNat_iff
  条件: (x : R)
  结论: ⊥ < toWithBot自然数 x ↔ x != 0
  证明: by
  rw [bot_lt_iff_ne_bot]; simp
-/
@[simp] lemma bot_lt_toWithBotNat_iff (x : R) : ⊥ < toWithBotNat x ↔ x != 0 := by
  rw [bot_lt_iff_ne_bot]; simp

/--
lemma `toWithBotNat_le_toWithBotNat_iff` / 引理 `toWithBotNat_le_toWithBotNat_iff`

English:
lemma toWithBotNat_le_toWithBotNat_iff
  given: {x y : R} (hx : x != 0) (hy : y != 0)
  proof: by
  unfold toWithBotNat
  generalize hvx : addVal R x = vx
  generalize hvy : addVal R y = vy
  cases vx with
  | top => rw [addVal_eq_top_iff] at hvx; tauto
  | coe vx =>
    cases vy with
    | top => rw [addVal_eq_top_iff] at hvy; tauto
    | coe vy =>
      rw [← addVal_le_iff_dvd]; rw [hvx]; r

中文:
引理 toWithBotNat_le_toWithBotNat_iff
  条件: {x y : R} (hx : x != 0) (hy : y != 0)
  证明: by
  unfold toWithBotNat
  generalize hvx : addVal R x = vx
  generalize hvy : addVal R y = vy
  cases vx with
  | top => rw [addVal_eq_top_iff] at hvx; tauto
  | coe vx =>
    cases vy with
    | top => rw [addVal_eq_top_iff] at hvy; tauto
    | coe vy =>
      rw [← addVal_le_iff_dvd]; rw [hvx]; r

Depends on / 依赖: WithBot, WithBot.coe_le_coe.trans, WithTop, WithTop.coe_le_coe.symm, addVal, addVal_eq_top_iff, addVal_le_iff_dvd, coe_le_coe, generalize, toWithBotNat
-/
lemma toWithBotNat_le_toWithBotNat_iff {x y : R} (hx : x != 0) (hy : y != 0) :
    toWithBotNat x <= toWithBotNat y ↔ x ∣ y := by
  unfold toWithBotNat
  generalize hvx : addVal R x = vx
  generalize hvy : addVal R y = vy
  cases vx with
  | top => rw [addVal_eq_top_iff] at hvx; tauto
  | coe vx =>
    cases vy with
    | top => rw [addVal_eq_top_iff] at hvy; tauto
    | coe vy =>
      rw [← addVal_le_iff_dvd]; rw [hvx]; rw [hvy]
      exact WithBot.coe_le_coe.trans WithTop.coe_le_coe.symm

/--
lemma `dvd_of_toWithBotNat_le_toWithBotNat` / 引理 `dvd_of_toWithBotNat_le_toWithBotNat`

English:
lemma dvd_of_toWithBotNat_le_toWithBotNat
  statement: (x y : R) (hx : x != 0)
  proof: by
  by_cases hy : y = 0
  · simp [hy, hx] at hle
  exact (toWithBotNat_le_toWithBotNat_iff hx hy).mp hle

中文:
引理 dvd_of_toWithBotNat_le_toWithBotNat
  结论: (x y : R) (hx : x != 0)
  证明: by
  by_cases hy : y = 0
  · simp [hy, hx] at hle
  exact (toWithBotNat_le_toWithBotNat_iff hx hy).mp hle

Depends on / 依赖: toWithBotNat_le_toWithBotNat_iff
-/
lemma dvd_of_toWithBotNat_le_toWithBotNat (x y : R) (hx : x != 0)
    (hle : toWithBotNat x <= toWithBotNat y) : x ∣ y := by
  by_cases hy : y = 0
  · simp [hy, hx] at hle
  exact (toWithBotNat_le_toWithBotNat_iff hx hy).mp hle

variable (R) in
/-- A noncomputable Euclidean domain structure on a discrete valuation ring, where the GCD algorithm
only takes two steps to terminate. Given `GCD(x,y)`, if `x ∣ y` then `y%x = 0` so we're done in one
step; otherwise `y%x = y` and then `GCD(x,y) = GCD(y,x)` which brings us back to the first case.
See `EuclideanDomain.to_principal_ideal_domain` for EuclideanDomain ⇒ PID. -/
@[instance_reducible]
/--
Definition of `toEuclideanDomain` / `toEuclideanDomain` 的定义

English:
definition toEuclideanDomain
  signature: : EuclideanDomain R where
  body: quotient
  quotient_zero x := by simp [quotient]
  remainder := remainder
  quotient_mul_add_remainder_eq x y := by
    rw [remainder]; rw [quotient]
    split_ifs with h₁ h₂ h₂
    · rw [h₁, zero_dvd_iff] at h₂; rw [h₁, h₂]; ring
    · rw [h₁]; ring
    · rw [← h₂.choose_spec]; ring
    · ring
  r 

中文:
定义 toEuclideanDomain
  签名: : EuclideanDomain R where
  定义体: quotient
  quotient_zero x := by simp [quotient]
  remainder := remainder
  quotient_mul_add_remainder_eq x y := by
    rw [remainder]; rw [quotient]
    split_ifs with h₁ h₂ h₂
    · rw [h₁, zero_dvd_iff] at h₂; rw [h₁, h₂]; ring
    · rw [h₁]; ring
    · rw [← h₂.choose_spec]; ring
    · ring
  r 

Depends on / 依赖: quotient
-/
def toEuclideanDomain : EuclideanDomain R where
  quotient := quotient
  quotient_zero x := by simp [quotient]
  remainder := remainder
  quotient_mul_add_remainder_eq x y := by
    rw [remainder]; rw [quotient]
    split_ifs with h₁ h₂ h₂
    · rw [h₁, zero_dvd_iff] at h₂; rw [h₁, h₂]; ring
    · rw [h₁]; ring
    · rw [← h₂.choose_spec]; ring
    · ring
  r x y := toWithBotNat x < toWithBotNat y
  r_wellFounded := WellFounded.onFun wellFounded_lt
  remainder_lt x y hy := by
    rw [remainder]
    split_ifs with hyx
    · rwa [toWithBotNat_zero, bot_lt_toWithBotNat_iff]
    · exact lt_iff_not_ge.mpr (mt (dvd_of_toWithBotNat_le_toWithBotNat _ _ hy) hyx)
  mul_left_not_lt x y hy := by
    by_cases hx : x = 0
    · simp [hx]
    rw [not_lt]; rw [toWithBotNat_le_toWithBotNat_iff hx (mul_ne_zero hx hy)]
    exact dvd_mul_right _ _

end toEuclideanDomain

end IsDiscreteValuationRing


section

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- A DVR is a valuation ring. -/
instance (priority := 100) of_isDiscreteValuationRing : ValuationRing A := inferInstance

end

namespace Valuation.Integers

variable {K Γ₀ O : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [CommRing O]
    [Algebra O K] {v : Valuation K Γ₀} (hv : v.Integers O)
include hv

/--
lemma `maximalIdeal_eq_setOfPred_le_v_algebraMap` / 引理 `maximalIdeal_eq_setOfPred_le_v_algebraMap`

English:
lemma maximalIdeal_eq_setOfPred_le_v_algebraMap
  proof: hv.hom_inj.isDomain
    forall [IsDiscreteValuationRing O] {ϖ : O} (_h : Irreducible ϖ),
    (IsLocalRing.maximalIdeal O : Set O) =
      {y : O | v (algebraMap O K y) <= v (algebraMap O K ϖ)} := by
  let : IsDomain O := hv.hom_inj.isDomain
  intro _ _ h
  rw [← hv.coe_span_singleton_eq_setOfPred_le

中文:
引理 maximalIdeal_eq_setOfPred_le_v_algebraMap
  证明: hv.hom_inj.isDomain
    forall [IsDiscreteValuationRing O] {ϖ : O} (_h : Irreducible ϖ),
    (IsLocalRing.maximalIdeal O : Set O) =
      {y : O | v (algebraMap O K y) <= v (algebraMap O K ϖ)} := by
  let : IsDomain O := hv.hom_inj.isDomain
  intro _ _ h
  rw [← hv.coe_span_singleton_eq_setOfPred_le

Depends on / 依赖: hom_inj, hv.hom_inj.isDomain, isDomain
-/
lemma maximalIdeal_eq_setOfPred_le_v_algebraMap :
    letI : IsDomain O := hv.hom_inj.isDomain
    forall [IsDiscreteValuationRing O] {ϖ : O} (_h : Irreducible ϖ),
    (IsLocalRing.maximalIdeal O : Set O) =
      {y : O | v (algebraMap O K y) <= v (algebraMap O K ϖ)} := by
  let : IsDomain O := hv.hom_inj.isDomain
  intro _ _ h
  rw [← hv.coe_span_singleton_eq_setOfPred_le_v_algebraMap]; rw [← h.maximalIdeal_eq]

@[deprecated (since := "2026-07-09")]
alias maximalIdeal_eq_setOf_le_v_algebraMap := maximalIdeal_eq_setOfPred_le_v_algebraMap

/--
lemma `maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow` / 引理 `maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow`

English:
lemma maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
  proof: hv.hom_inj.isDomain
    forall [IsDiscreteValuationRing O] {ϖ : O} (_h : Irreducible ϖ) (n : Nat),
    ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) =
      {y : O | v (algebraMap O K y) <= v (algebraMap O K ϖ) ^ n} := by
  let : IsDomain O := hv.hom_inj.isDomain
  intro _ ϖ h n
  have : (v (

中文:
引理 maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
  证明: hv.hom_inj.isDomain
    forall [IsDiscreteValuationRing O] {ϖ : O} (_h : Irreducible ϖ) (n : Nat),
    ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) =
      {y : O | v (algebraMap O K y) <= v (algebraMap O K ϖ) ^ n} := by
  let : IsDomain O := hv.hom_inj.isDomain
  intro _ ϖ h n
  have : (v (

Depends on / 依赖: hom_inj, hv.hom_inj.isDomain, isDomain
-/
lemma maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow :
    letI : IsDomain O := hv.hom_inj.isDomain
    forall [IsDiscreteValuationRing O] {ϖ : O} (_h : Irreducible ϖ) (n : Nat),
    ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) =
      {y : O | v (algebraMap O K y) <= v (algebraMap O K ϖ) ^ n} := by
  let : IsDomain O := hv.hom_inj.isDomain
  intro _ ϖ h n
  have : (v (algebraMap O K ϖ)) ^ n = v (algebraMap O K (ϖ ^ n)) := by simp
  rw [this]; rw [← hv.coe_span_singleton_eq_setOfPred_le_v_algebraMap]; rw [← Ideal.span_singleton_pow]; rw [← h.maximalIdeal_eq]

@[deprecated (since := "2026-07-09")]
alias maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow :=
  maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow

end Valuation.Integers

section Valuation.integer

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/--
lemma `_root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe` / 引理 `_root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe`

English:
lemma _root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe
  proof: (Valuation.integer.integers v).maximalIdeal_eq_setOfPred_le_v_algebraMap h

@[deprecated (since := "2026-07-09")]
alias _root_.Irreducible.maximalIdeal_eq_setOf_le_v_coe :=
  _root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe

中文:
引理 _root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe
  证明: (Valuation.integer.integers v).maximalIdeal_eq_setOfPred_le_v_algebraMap h

@[deprecated (since := "2026-07-09")]
alias _root_.Irreducible.maximalIdeal_eq_setOf_le_v_coe :=
  _root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers, maximalIdeal_eq_setOfPred_le_v_algebraMap
-/
lemma _root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe
    [IsDiscreteValuationRing v.integer] {ϖ : v.integer} (h : Irreducible ϖ) :
    (IsLocalRing.maximalIdeal v.integer : Set v.integer) = {y : v.integer | v y <= v ϖ} :=
  (Valuation.integer.integers v).maximalIdeal_eq_setOfPred_le_v_algebraMap h

@[deprecated (since := "2026-07-09")]
alias _root_.Irreducible.maximalIdeal_eq_setOf_le_v_coe :=
  _root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe

/--
lemma `_root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow` / 引理 `_root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow`

English:
lemma _root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
  proof: (Valuation.integer.integers v).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow h _

@[deprecated (since := "2026-07-09")]
alias _root_.Irreducible.maximalIdeal_pow_eq_setOf_le_v_coe_pow :=
  _root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow

中文:
引理 _root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
  证明: (Valuation.integer.integers v).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow h _

@[deprecated (since := "2026-07-09")]
alias _root_.Irreducible.maximalIdeal_pow_eq_setOf_le_v_coe_pow :=
  _root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers, maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
-/
lemma _root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    [IsDiscreteValuationRing v.integer] {ϖ : v.integer} (h : Irreducible ϖ) (n : Nat) :
    ((IsLocalRing.maximalIdeal v.integer ^ n : Ideal v.integer) : Set v.integer) =
      {y : v.integer | v y <= v (ϖ : K) ^ n} :=
  (Valuation.integer.integers v).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow h _

@[deprecated (since := "2026-07-09")]
alias _root_.Irreducible.maximalIdeal_pow_eq_setOf_le_v_coe_pow :=
  _root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow

end Valuation.integer
