/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Frobenius elements

In algebraic number theory, if `L/K` is a finite Galois extension of number fields, with rings of
integers `𝓞L/𝓞K`, and if `q` is prime ideal of `𝓞L` lying over a prime ideal `p` of `𝓞K`, then
there exists a **Frobenius element** `Frob p` in `Gal(L/K)` with the property that
`Frob p x ≡ x ^ #(𝓞K/p) (mod q)` for all `x ∈ 𝓞L`.

Following `Mathlib/RingTheory/Invariant/Basic.lean`, we develop the theory in the setting that
there is a finite group `G` acting on a ring `S`, and `R` is the fixed subring of `S`.

## Main results

Let `S/R` be an extension of rings, `Q` be a prime of `S`,
and `P := R ∩ Q` with finite residue field of cardinality `q`.

- `AlgHom.IsArithFrobAt`: We say that a `φ : S →ₐ[R] S` is an (arithmetic) Frobenius at `Q`
  if `φ x ≡ x ^ q (mod Q)` for all `x : S`.
- `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`:
  Suppose `S` is a domain and `φ` is a Frobenius at `Q`,
  then `φ ζ = ζ ^ q` for any `m`-th root of unity `ζ` with `q ∤ m`.
- `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`:
  Suppose `S` is Noetherian, `Q` contains all zero-divisors, and the extension is unramified at `Q`.
  Then the Frobenius is unique (if exists).

Let `G` be a finite group acting on a ring `S`, and `R` is the fixed subring of `S`.

- `IsArithFrobAt`: We say that a `σ : G` is an (arithmetic) Frobenius at `Q`
  if `σ • x ≡ x ^ q (mod Q)` for all `x : S`.
- `IsArithFrobAt.mul_inv_mem_inertia`:
  Two Frobenius elements at `Q` differ by an element in the inertia subgroup of `Q`.
- `IsArithFrobAt.conj`: If `σ` is a Frobenius at `Q`, then `τστ⁻¹` is a Frobenius at `σ • Q`.
- `IsArithFrobAt.exists_of_isInvariant`: Frobenius element exists.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/--
Definition of `AlgHom.IsArithFrobAt` / `AlgHom.IsArithFrobAt` 的定义

English:
definition AlgHom.IsArithFrobAt
  signature: (φ : S ->ₐ[R] S) (Q : Ideal S)
  body: forall x, φ x - x ^ Nat.card (R ⧸ Q.under R) in Q

中文:
定义 AlgHom.IsArithFrobAt
  签名: (φ : S ->ₐ[R] S) (Q : Ideal S)
  定义体: forall x, φ x - x ^ Nat.card (R ⧸ Q.under R) in Q

Depends on / 依赖: Nat.card, Q.under
-/
def AlgHom.IsArithFrobAt (φ : S ->ₐ[R] S) (Q : Ideal S) : Prop :=
  forall x, φ x - x ^ Nat.card (R ⧸ Q.under R) in Q

namespace AlgHom.IsArithFrobAt

variable {φ ψ : S ->ₐ[R] S} {Q : Ideal S} (H : φ.IsArithFrobAt Q)

include H

/--
lemma `mk_apply` / 引理 `mk_apply`

English:
lemma mk_apply
  given: (x)
  statement: Ideal.Quotient.mk Q (φ x) = x ^ Nat.card (R ⧸ Q.under R)
  proof: by
  rw [← map_pow]; rw [Ideal.Quotient.eq]
  exact H x

中文:
引理 mk_apply
  条件: (x)
  结论: Ideal.Quotient.mk Q (φ x) = x ^ 自然数.card (R ⧸ Q.under R)
  证明: by
  rw [← map_pow]; rw [Ideal.Quotient.eq]
  exact H x

Depends on / 依赖: Ideal.Quotient.eq, Quotient, map_pow
-/
lemma mk_apply (x) : Ideal.Quotient.mk Q (φ x) = x ^ Nat.card (R ⧸ Q.under R) := by
  rw [← map_pow]; rw [Ideal.Quotient.eq]
  exact H x

/--
lemma `finite_quotient` / 引理 `finite_quotient`

English:
lemma finite_quotient
  statement: _root_.Finite (R ⧸ Q.under R)
  proof: by
  by_contra! h
  obtain rfl : Q = ⊤ := by simpa [Nat.card_eq_zero_of_infinite, ← Ideal.eq_top_iff_one] using H 0
  simp only [Ideal.comap_top] at h
  exact not_finite (R ⧸ (⊤ : Ideal R))

中文:
引理 finite_quotient
  结论: _root_.Finite (R ⧸ Q.under R)
  证明: by
  by_contra! h
  obtain rfl : Q = ⊤ := by simpa [Nat.card_eq_zero_of_infinite, ← Ideal.eq_top_iff_one] using H 0
  simp only [Ideal.comap_top] at h
  exact not_finite (R ⧸ (⊤ : Ideal R))

Depends on / 依赖: Ideal.comap_top, Ideal.eq_top_iff_one, Nat.card_eq_zero_of_infinite, card_eq_zero_of_infinite, comap_top, eq_top_iff_one, not_finite
-/
lemma finite_quotient : _root_.Finite (R ⧸ Q.under R) := by
  by_contra! h
  obtain rfl : Q = ⊤ := by simpa [Nat.card_eq_zero_of_infinite, ← Ideal.eq_top_iff_one] using H 0
  simp only [Ideal.comap_top] at h
  exact not_finite (R ⧸ (⊤ : Ideal R))

/--
lemma `card_pos` / 引理 `card_pos`

English:
lemma card_pos
  statement: 0 < Nat.card (R ⧸ Q.under R)
  proof: have := H.finite_quotient
  Nat.card_pos

中文:
引理 card_pos
  结论: 0 < 自然数.card (R ⧸ Q.under R)
  证明: have := H.finite_quotient
  Nat.card_pos

Depends on / 依赖: H.finite_quotient, Nat.card_pos, card_pos, finite_quotient
-/
lemma card_pos : 0 < Nat.card (R ⧸ Q.under R) :=
  have := H.finite_quotient
  Nat.card_pos

/--
lemma `le_comap` / 引理 `le_comap`

English:
lemma le_comap
  statement: Q <= Q.comap φ
  proof: by
  intro x hx
  simp_all only [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem (I := Q), H.mk_apply,
    zero_pow_eq, ite_eq_right_iff, H.card_pos.ne', false_implies]

中文:
引理 le_comap
  结论: Q <= Q.comap φ
  证明: by
  intro x hx
  simp_all only [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem (I := Q), H.mk_apply,
    zero_pow_eq, ite_eq_right_iff, H.card_pos.ne', false_implies]

Depends on / 依赖: H.card_pos.ne, H.mk_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap, Quotient, card_pos, eq_zero_iff_mem, false_implies, ite_eq_right_iff, mem_comap, mk_apply, zero_pow_eq
-/
lemma le_comap : Q <= Q.comap φ := by
  intro x hx
  simp_all only [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem (I := Q), H.mk_apply,
    zero_pow_eq, ite_eq_right_iff, H.card_pos.ne', false_implies]

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: : S ⧸ Q ->ₐ[R ⧸ Q.under R] S ⧸ Q where
  body: Ideal.quotientMap Q φ H.le_comap
  commutes' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_arg (Ideal.Quotient.mk Q) (φ.commutes x)

中文:
定义 restrict
  签名: : S ⧸ Q ->ₐ[R ⧸ Q.under R] S ⧸ Q where
  定义体: Ideal.quotientMap Q φ H.le_comap
  commutes' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_arg (Ideal.Quotient.mk Q) (φ.commutes x)

Depends on / 依赖: H.le_comap, Ideal.quotientMap, le_comap, quotientMap
-/
def restrict : S ⧸ Q ->ₐ[R ⧸ Q.under R] S ⧸ Q where
  toRingHom := Ideal.quotientMap Q φ H.le_comap
  commutes' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_arg (Ideal.Quotient.mk Q) (φ.commutes x)

/--
lemma `restrict_apply` / 引理 `restrict_apply`

English:
lemma restrict_apply
  given: (x : S ⧸ Q)
  proof: by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact H.mk_apply x

中文:
引理 restrict_apply
  条件: (x : S ⧸ Q)
  证明: by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact H.mk_apply x

Depends on / 依赖: H.mk_apply, Ideal.Quotient.mk_surjective, Quotient, mk_apply, mk_surjective
-/
lemma restrict_apply (x : S ⧸ Q) :
    H.restrict x = x ^ Nat.card (R ⧸ Q.under R) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact H.mk_apply x

/--
lemma `restrict_mk` / 引理 `restrict_mk`

English:
lemma restrict_mk
  given: (x : S)
  statement: H.restrict ↑x = ↑(φ x)
  proof: rfl

中文:
引理 restrict_mk
  条件: (x : S)
  结论: H.restrict ↑x = ↑(φ x)
  证明: rfl
-/
lemma restrict_mk (x : S) : H.restrict ↑x = ↑(φ x) := rfl

/--
lemma `restrict_injective` / 引理 `restrict_injective`

English:
lemma restrict_injective
  given: [Q.IsPrime]
  proof: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  simpa [restrict_apply, H.card_pos.ne'] using hx

中文:
引理 restrict_injective
  条件: [Q.IsPrime]
  证明: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  simpa [restrict_apply, H.card_pos.ne'] using hx

Depends on / 依赖: H.card_pos.ne, card_pos, injective_iff_map_eq_zero, restrict_apply
-/
lemma restrict_injective [Q.IsPrime] :
    Function.Injective H.restrict := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  simpa [restrict_apply, H.card_pos.ne'] using hx

/--
lemma `comap_eq` / 引理 `comap_eq`

English:
lemma comap_eq
  given: [Q.IsPrime]
  statement: Q.comap φ = Q
  proof: by
  refine le_antisymm (fun x hx => ?_) H.le_comap
  rwa [← Ideal.Quotient.eq_zero_iff_mem, ← H.restrict_injective.eq_iff, map_zero, restrict_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]

中文:
引理 comap_eq
  条件: [Q.IsPrime]
  结论: Q.comap φ = Q
  证明: by
  refine le_antisymm (fun x hx => ?_) H.le_comap
  rwa [← Ideal.Quotient.eq_zero_iff_mem, ← H.restrict_injective.eq_iff, map_zero, restrict_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]

Depends on / 依赖: H.le_comap, H.restrict_injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap, Quotient, eq_iff, eq_zero_iff_mem, le_antisymm, le_comap, map_zero, mem_comap, restrict_injective, restrict_mk
-/
lemma comap_eq [Q.IsPrime] : Q.comap φ = Q := by
  refine le_antisymm (fun x hx => ?_) H.le_comap
  rwa [← Ideal.Quotient.eq_zero_iff_mem, ← H.restrict_injective.eq_iff, map_zero, restrict_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]

/--
lemma `apply_of_pow_eq_one` / 引理 `apply_of_pow_eq_one`

English:
lemma apply_of_pow_eq_one
  given: [IsDomain S] {ζ : S} {m : Nat} (hζ : ζ ^ m = 1) (hk' : ↑m ∉ Q)
  proof: by
  set q := Nat.card (R ⧸ Q.under R)
  have hm : m != 0 := by rintro rfl; exact hk' (by simp)
  obtain ⟨k, hk, hζ⟩ := IsPrimitiveRoot.exists_pos hζ hm
  have hk' : ↑k ∉ Q := fun h => hk' (Q.mem_of_dvd (Nat.cast_dvd_cast (hζ.2 m ‹_›)) h)
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, hi, e⟩ := hζ.eq_po

中文:
引理 apply_of_pow_eq_one
  条件: [IsDomain S] {ζ : S} {m : 自然数} (hζ : ζ ^ m = 1) (hk' : ↑m ∉ Q)
  证明: by
  set q := Nat.card (R ⧸ Q.under R)
  have hm : m != 0 := by rintro rfl; exact hk' (by simp)
  obtain ⟨k, hk, hζ⟩ := IsPrimitiveRoot.exists_pos hζ hm
  have hk' : ↑k ∉ Q := fun h => hk' (Q.mem_of_dvd (Nat.cast_dvd_cast (hζ.2 m ‹_›)) h)
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, hi, e⟩ := hζ.eq_po

Depends on / 依赖: Ideal.mul_unit_mem_iff_mem, IsPrimitiveRoot, IsPrimitiveRoot.exists_pos, Nat.card, Nat.cast_dvd_cast, NeZero, NeZero.out, Q.mem_of_dvd, Q.under, cast_dvd_cast, eq_pow_of_pow_eq_one, exists_pos, hk.ne, isUnit, map_one, map_pow, mem_of_dvd, mul_unit_mem_iff_mem, one_mu, sub_mul
-/
lemma apply_of_pow_eq_one [IsDomain S] {ζ : S} {m : Nat} (hζ : ζ ^ m = 1) (hk' : ↑m ∉ Q) :
    φ ζ = ζ ^ Nat.card (R ⧸ Q.under R) := by
  set q := Nat.card (R ⧸ Q.under R)
  have hm : m != 0 := by rintro rfl; exact hk' (by simp)
  obtain ⟨k, hk, hζ⟩ := IsPrimitiveRoot.exists_pos hζ hm
  have hk' : ↑k ∉ Q := fun h => hk' (Q.mem_of_dvd (Nat.cast_dvd_cast (hζ.2 m ‹_›)) h)
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one (ξ := φ ζ) (by rw [← map_pow, hζ.1, map_one])
  have (j : _) : 1 - ζ ^ ((q + k - i) * j) in Q := by
    rw [← Ideal.mul_unit_mem_iff_mem _ ((hζ.isUnit NeZero.out).pow (i * j))]; rw [sub_mul]; rw [one_mul]; rw [← pow_add]; rw [← add_mul]; rw [tsub_add_cancel_of_le (by linarith)]; rw [add_mul]; rw [pow_add]; rw [pow_mul _ k]; rw [hζ.1]; rw [one_pow]; rw [mul_one]; rw [pow_mul]; rw [e]; rw [← map_pow]; rw [mul_comm]; rw [pow_mul]
    exact H _
  have h₁ := sum_mem (t := Finset.range k) fun j _ => this j
  have h₂ := geom_sum_mul (ζ ^ (q + k - i)) k
  rw [pow_right_comm]; rw [hζ.1]; rw [one_pow]; rw [sub_self]; rw [mul_eq_zero]; rw [sub_eq_zero] at h₂
  rcases h₂ with h₂ | h₂
  · simp [h₂, pow_mul, hk'] at h₁
  replace h₂ := congr($h₂ * ζ ^ i)
  rw [one_mul]; rw [← pow_add]; rw [tsub_add_cancel_of_le (by linarith)]; rw [pow_add]; rw [hζ.1]; rw [mul_one] at h₂
  rw [h₂]; rw [e]

set_option backward.isDefEq.respectTransparency.types false in
/-- A Frobenius element at `Q` restricts to an automorphism of `S_Q`. -/
noncomputable
/--
Definition of `localize` / `localize` 的定义

English:
definition localize
  signature: [Q.IsPrime]
  body: Localization.localRingHom _ _ φ H.comap_eq.symm
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q),
      Localization.localRingHom_to_map]

@[simp]

中文:
定义 localize
  签名: [Q.IsPrime]
  定义体: Localization.localRingHom _ _ φ H.comap_eq.symm
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q),
      Localization.localRingHom_to_map]

@[simp]

Depends on / 依赖: H.comap_eq.symm, Localization, Localization.localRingHom, comap_eq, localRingHom
-/
def localize [Q.IsPrime] : Localization.AtPrime Q ->ₐ[R] Localization.AtPrime Q where
  toRingHom := Localization.localRingHom _ _ φ H.comap_eq.symm
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q),
      Localization.localRingHom_to_map]

@[simp]
/--
lemma `localize_algebraMap` / 引理 `localize_algebraMap`

English:
lemma localize_algebraMap
  given: [Q.IsPrime] (x : S)
  proof: Localization.localRingHom_to_map _ _ _ H.comap_eq.symm _

中文:
引理 localize_algebraMap
  条件: [Q.IsPrime] (x : S)
  证明: Localization.localRingHom_to_map _ _ _ H.comap_eq.symm _

Depends on / 依赖: H.comap_eq.symm, Localization, Localization.localRingHom_to_map, comap_eq, localRingHom_to_map
-/
lemma localize_algebraMap [Q.IsPrime] (x : S) :
    H.localize (algebraMap _ _ x) = algebraMap _ _ (φ x) :=
  Localization.localRingHom_to_map _ _ _ H.comap_eq.symm _

open IsLocalRing nonZeroDivisors

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isArithFrobAt_localize` / 引理 `isArithFrobAt_localize`

English:
lemma isArithFrobAt_localize
  given: [Q.IsPrime]
  statement: H.localize.IsArithFrobAt (maximalIdeal _)
  proof: by
  have h : Nat.card (R ⧸ (maximalIdeal _).comap (algebraMap R (Localization.AtPrime Q))) =
      Nat.card (R ⧸ Q.under R) := by
    congr 2
    rw [← Ideal.under_def]; rw [← Ideal.under_under (B := S)]; rw [Localization.AtPrime.under_maximalIdeal]
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.

中文:
引理 isArithFrobAt_localize
  条件: [Q.IsPrime]
  结论: H.localize.IsArithFrobAt (maximalIdeal _)
  证明: by
  have h : Nat.card (R ⧸ (maximalIdeal _).comap (algebraMap R (Localization.AtPrime Q))) =
      Nat.card (R ⧸ Q.under R) := by
    congr 2
    rw [← Ideal.under_def]; rw [← Ideal.under_under (B := S)]; rw [Localization.AtPrime.under_maximalIdeal]
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.

Depends on / 依赖: AtPrime, Ideal.under_def, Ideal.under_under, IsLocalization, IsLocalization.AtPrime.mk, IsLocalization.exists_mk, IsLocalization.mk, Locali, Localization, Localization.AtPrime, Localization.AtPrime.under_maximalIdeal, Localization.localRingHom_mk, Nat.card, Q.primeCompl, Q.under, RingHom, RingHom.coe_coe, _mem_maximal_iff, _pow, _sub
-/
lemma isArithFrobAt_localize [Q.IsPrime] : H.localize.IsArithFrobAt (maximalIdeal _) := by
  have h : Nat.card (R ⧸ (maximalIdeal _).comap (algebraMap R (Localization.AtPrime Q))) =
      Nat.card (R ⧸ Q.under R) := by
    congr 2
    rw [← Ideal.under_def]; rw [← Ideal.under_under (B := S)]; rw [Localization.AtPrime.under_maximalIdeal]
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq Q.primeCompl x
  simp only [localize, coe_mk, Localization.localRingHom_mk', RingHom.coe_coe, h,
    ← IsLocalization.mk'_pow]
  rw [← IsLocalization.mk'_sub]; rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime Q) Q]
  simp only [SubmonoidClass.coe_pow, ← Ideal.Quotient.eq_zero_iff_mem]
  simp [H.mk_apply]

/--
lemma `eq_of_isUnramifiedAt` / 引理 `eq_of_isUnramifiedAt`

English:
lemma eq_of_isUnramifiedAt
  proof: by
  have : H.localize = H'.localize := by
    apply Algebra.FormallyUnramified.ext_of_iInf _
      (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal _) Ideal.IsPrime.ne_top')
    intro x
    rw [H.isArithFrobAt_localize.mk_apply]; rw [H'.isArithFrobAt_localize.mk_apply]
  ext x
  apply IsLocaliza

中文:
引理 eq_of_isUnramifiedAt
  证明: by
  have : H.localize = H'.localize := by
    apply Algebra.FormallyUnramified.ext_of_iInf _
      (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal _) Ideal.IsPrime.ne_top')
    intro x
    rw [H.isArithFrobAt_localize.mk_apply]; rw [H'.isArithFrobAt_localize.mk_apply]
  ext x
  apply IsLocaliza

Depends on / 依赖: Algebra, Algebra.FormallyUnramified.ext_of_iInf, AtPrime, FormallyUnramified, H.isArithFrobAt_localize.mk_apply, H.localize, H.localize_algebraMap, Ideal.IsPrime.ne_top, Ideal.iInf_pow_eq_bot_of_isLocalRing, IsLocalization, IsLocalization.injective, IsPrime, Localization, Localization.AtPrime, ext_of_iInf, iInf_pow_eq_bot_of_isLocalRing, injective, isArithFrobAt_localize, isArithFrobAt_localize.mk_apply, localize
-/
lemma eq_of_isUnramifiedAt
    (H' : ψ.IsArithFrobAt Q) [Q.IsPrime] (hQ : Q.primeCompl <= S⁰)
    [Algebra.IsUnramifiedAt R Q] [IsNoetherianRing S] : φ = ψ := by
  have : H.localize = H'.localize := by
    apply Algebra.FormallyUnramified.ext_of_iInf _
      (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal _) Ideal.IsPrime.ne_top')
    intro x
    rw [H.isArithFrobAt_localize.mk_apply]; rw [H'.isArithFrobAt_localize.mk_apply]
  ext x
  apply IsLocalization.injective (Localization.AtPrime Q) hQ
  rw [← H.localize_algebraMap]; rw [← H'.localize_algebraMap]; rw [this]

end AlgHom.IsArithFrobAt

variable (R) in
/--
Definition of `IsArithFrobAt` / `IsArithFrobAt` 的定义

English:
abbreviation IsArithFrobAt
  signature: {M : Type*} [Monoid M] [MulSemiringAction M S] [SMulCommClass M R S]
  body: (MulSemiringAction.toAlgHom R S σ).IsArithFrobAt Q

中文:
缩写 IsArithFrobAt
  签名: {M : 类型} [Monoid M] [MulSemiringAction M S] [SMulCommClass M R S]
  定义体: (MulSemiringAction.toAlgHom R S σ).IsArithFrobAt Q

Depends on / 依赖: IsArithFrobAt, MulSemiringAction, MulSemiringAction.toAlgHom, toAlgHom
-/
abbrev IsArithFrobAt {M : Type*} [Monoid M] [MulSemiringAction M S] [SMulCommClass M R S]
    (σ : M) (Q : Ideal S) : Prop :=
  (MulSemiringAction.toAlgHom R S σ).IsArithFrobAt Q

namespace IsArithFrobAt

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
variable {Q : Ideal S} {σ σ' : G}

/--
theorem `mem_stabilizer` / 定理 `mem_stabilizer`

English:
theorem mem_stabilizer
  given: [Q.IsPrime] (h : IsArithFrobAt R σ Q)
  statement: σ in MulAction.stabilizer G Q
  proof: by
  rw [MulAction.mem_stabilizer_iff]
  conv_lhs => rw [← h.comap_eq]
  rw [Ideal.pointwise_smul_def]
  exact Q.map_comap_eq_self_of_equiv (MulSemiringAction.toRingEquiv G S σ)

中文:
定理 mem_stabilizer
  条件: [Q.IsPrime] (h : IsArithFrobAt R σ Q)
  结论: σ in MulAction.stabilizer G Q
  证明: by
  rw [MulAction.mem_stabilizer_iff]
  conv_lhs => rw [← h.comap_eq]
  rw [Ideal.pointwise_smul_def]
  exact Q.map_comap_eq_self_of_equiv (MulSemiringAction.toRingEquiv G S σ)

Depends on / 依赖: HashSet, Ideal.pointwise_smul_def, MulAction, MulAction.mem_stabilizer_iff, MulSemiringAction, MulSemiringAction.toRingEquiv, Q.map_comap_eq_self_of_equiv, Stained, Std.HashSet, comap_eq, conv_lhs, h.comap_eq, map_comap_eq_self_of_equiv, mem_stabilizer_iff, pointwise_smul_def, toRingEquiv
-/
theorem mem_stabilizer [Q.IsPrime] (h : IsArithFrobAt R σ Q) : σ in MulAction.stabilizer G Q := by
  rw [MulAction.mem_stabilizer_iff]
  conv_lhs => rw [← h.comap_eq]
  rw [Ideal.pointwise_smul_def]
  exact Q.map_comap_eq_self_of_equiv (MulSemiringAction.toRingEquiv G S σ)

/--
lemma `mul_inv_mem_inertia` / 引理 `mul_inv_mem_inertia`

English:
lemma mul_inv_mem_inertia
  given: (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q)
  proof: by
  intro x
  simpa [mul_smul] using sub_mem (H (σ'⁻¹ • x)) (H' (σ'⁻¹ • x))

中文:
引理 mul_inv_mem_inertia
  条件: (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q)
  证明: by
  intro x
  simpa [mul_smul] using sub_mem (H (σ'⁻¹ • x)) (H' (σ'⁻¹ • x))

Depends on / 依赖: mul_smul, sub_mem
-/
lemma mul_inv_mem_inertia (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q) :
    σ * σ'⁻¹ in Q.inertia G := by
  intro x
  simpa [mul_smul] using sub_mem (H (σ'⁻¹ • x)) (H' (σ'⁻¹ • x))

/--
lemma `conj` / 引理 `conj`

English:
lemma conj
  given: (H : IsArithFrobAt R σ Q) (τ : G)
  statement: IsArithFrobAt R (τ * σ * τ⁻¹) (τ • Q)
  proof: by
  intro x
  have : (Q.map (MulSemiringAction.toRingEquiv G S τ)).under R = Q.under R := by
    rw [← Ideal.comap_symm]; rw [← Ideal.comap_coe]; rw [Ideal.under]; rw [Ideal.comap_comap]
    congr 1
    exact (MulSemiringAction.toAlgEquiv R S τ).symm.toAlgHom.comp_algebraMap
  rw [Ideal.pointwise_s

中文:
引理 conj
  条件: (H : IsArithFrobAt R σ Q) (τ : G)
  结论: IsArithFrobAt R (τ * σ * τ⁻¹) (τ • Q)
  证明: by
  intro x
  have : (Q.map (MulSemiringAction.toRingEquiv G S τ)).under R = Q.under R := by
    rw [← Ideal.comap_symm]; rw [← Ideal.comap_coe]; rw [Ideal.under]; rw [Ideal.comap_comap]
    congr 1
    exact (MulSemiringAction.toAlgEquiv R S τ).symm.toAlgHom.comp_algebraMap
  rw [Ideal.pointwise_s

Depends on / 依赖: Ideal.comap_coe, Ideal.comap_comap, Ideal.comap_symm, Ideal.mem_comap, Ideal.pointwise_smul_eq_comap, Ideal.under, MulSemiringAction, MulSemiringAction.toAlgEquiv, MulSemiringAction.toRingEquiv, Q.map, Q.under, comap_coe, comap_comap, comap_symm, comp_algebraMap, mem_comap, mul_smul, pointwise_smul_eq_comap, smul_sub, symm.toAlgHom.comp_algebraMap
-/
lemma conj (H : IsArithFrobAt R σ Q) (τ : G) : IsArithFrobAt R (τ * σ * τ⁻¹) (τ • Q) := by
  intro x
  have : (Q.map (MulSemiringAction.toRingEquiv G S τ)).under R = Q.under R := by
    rw [← Ideal.comap_symm]; rw [← Ideal.comap_coe]; rw [Ideal.under]; rw [Ideal.comap_comap]
    congr 1
    exact (MulSemiringAction.toAlgEquiv R S τ).symm.toAlgHom.comp_algebraMap
  rw [Ideal.pointwise_smul_eq_comap]; rw [Ideal.mem_comap]
  simpa [smul_sub, mul_smul, this] using H (τ⁻¹ • x)

variable [Finite G] [Algebra.IsInvariant R S G]

variable (R G Q) in
attribute [local instance] Ideal.Quotient.field in
/--
lemma `exists_of_isInvariant` / 引理 `exists_of_isInvariant`

English:
lemma exists_of_isInvariant
  given: [Q.IsPrime] [Finite (S ⧸ Q)]
  statement: exists σ : G, IsArithFrobAt R σ Q
  proof: by
  let P := Q.under R
  have := Algebra.IsInvariant.isIntegral R S G
  have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (S ⧸ Q))
  obtain ⟨p, hc⟩ := CharP.exists (R ⧸ P)
  have : Finite (R ⧸ P) := .of_injective _ Ideal.algebraMap_quotient_injective
  cases nonemp

中文:
引理 exists_of_isInvariant
  条件: [Q.IsPrime] [Finite (S ⧸ Q)]
  结论: 存在 σ : G, IsArithFrobAt R σ Q
  证明: by
  let P := Q.under R
  have := Algebra.IsInvariant.isIntegral R S G
  have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (S ⧸ Q))
  obtain ⟨p, hc⟩ := CharP.exists (R ⧸ P)
  have : Finite (R ⧸ P) := .of_injective _ Ideal.algebraMap_quotient_injective
  cases nonemp

Depends on / 依赖: Algebra, Algebra.IsInvariant.isIntegral, CharP.exists, CharP.of_ringHom_of_ne_zero, ExpChar, Finite, Finite.isField_of_domain, FiniteField, FiniteField.card, Ideal.Quotient.maximal_of_isField, Ideal.algebraMap_quotient_injective, IsInvariant, IsMaximal, Q.IsMaximal, Q.under, Quotient, algebraMap, algebraMap_quotient_injective, hp.ne_zero, isField_of_domain
-/
lemma exists_of_isInvariant [Q.IsPrime] [Finite (S ⧸ Q)] : exists σ : G, IsArithFrobAt R σ Q := by
  let P := Q.under R
  have := Algebra.IsInvariant.isIntegral R S G
  have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (S ⧸ Q))
  obtain ⟨p, hc⟩ := CharP.exists (R ⧸ P)
  have : Finite (R ⧸ P) := .of_injective _ Ideal.algebraMap_quotient_injective
  cases nonempty_fintype (R ⧸ P)
  obtain ⟨k, hp, hk⟩ := FiniteField.card (R ⧸ P) p
  have := CharP.of_ringHom_of_ne_zero (algebraMap (R ⧸ P) (S ⧸ Q)) p hp.ne_zero
  have : ExpChar (S ⧸ Q) p := .prime hp
  let l : (S ⧸ Q) ≃ₐ[R ⧸ P] S ⧸ Q :=
    { __ := iterateFrobeniusEquiv (S ⧸ Q) p k,
      commutes' r := by
        dsimp [iterateFrobenius_def]
        rw [← map_pow]; rw [← hk]; rw [FiniteField.pow_card] }
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q l
  refine ⟨σ, fun x => ?_⟩
  rw [← Ideal.Quotient.eq]; rw [Nat.card_eq_fintype_card]; rw [hk]
  exact DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)

variable (S G) in
/--
lemma `exists_primesOver_isConj` / 引理 `exists_primesOver_isConj`

English:
lemma exists_primesOver_isConj
  statement: (P : Ideal R)
  proof: by
  obtain ⟨⟨Q, hQ₁, hQ₂⟩, hQ₃⟩ := hP
  have (Q' : Ideal.primesOver P S) : exists σ : G, Q'.1 = σ • Q :=
    Algebra.IsInvariant.exists_smul_of_under_eq R S G _ _ (hQ₂.over.symm.trans Q'.2.2.over)
  choose τ hτ using this
  obtain ⟨σ, hσ⟩ := exists_of_isInvariant R G Q
  refine ⟨fun Q' => τ Q' * σ 

中文:
引理 exists_primesOver_isConj
  结论: (P : Ideal R)
  证明: by
  obtain ⟨⟨Q, hQ₁, hQ₂⟩, hQ₃⟩ := hP
  have (Q' : Ideal.primesOver P S) : exists σ : G, Q'.1 = σ • Q :=
    Algebra.IsInvariant.exists_smul_of_under_eq R S G _ _ (hQ₂.over.symm.trans Q'.2.2.over)
  choose τ hτ using this
  obtain ⟨σ, hσ⟩ := exists_of_isInvariant R G Q
  refine ⟨fun Q' => τ Q' * σ 

Depends on / 依赖: Algebra, Algebra.IsInvariant.exists_smul_of_under_eq, Ideal.primesOver, IsInvariant, exists_of_isInvariant, exists_smul_of_under_eq, isConj_iff, isConj_iff.mpr, over.symm.trans, primesOver
-/
lemma exists_primesOver_isConj (P : Ideal R)
    (hP : exists Q : Ideal.primesOver P S, Finite (S ⧸ Q.1)) :
    exists σ : Ideal.primesOver P S -> G, (forall Q, IsArithFrobAt R (σ Q) Q.1) ∧
      (forall Q₁ Q₂, IsConj (σ Q₁) (σ Q₂)) := by
  obtain ⟨⟨Q, hQ₁, hQ₂⟩, hQ₃⟩ := hP
  have (Q' : Ideal.primesOver P S) : exists σ : G, Q'.1 = σ • Q :=
    Algebra.IsInvariant.exists_smul_of_under_eq R S G _ _ (hQ₂.over.symm.trans Q'.2.2.over)
  choose τ hτ using this
  obtain ⟨σ, hσ⟩ := exists_of_isInvariant R G Q
  refine ⟨fun Q' => τ Q' * σ * (τ Q')⁻¹, fun Q' => hτ Q' ▸ hσ.conj (τ Q'), fun Q₁ Q₂ =>
    .trans (.symm (isConj_iff.mpr ⟨τ Q₁, rfl⟩)) (isConj_iff.mpr ⟨τ Q₂, rfl⟩)⟩

variable (R G Q)

/-- Let `G` be a finite group acting on `S`, `R` be the fixed subring, and `Q` be a prime of `S`
with finite residue field. This is an arbitrary choice of a Frobenius over `Q`. It is chosen so that
the Frobenius elements of `Q₁` and `Q₂` are conjugate if they lie over the same prime. -/
noncomputable
/--
Definition of `_root_.arithFrobAt` / `_root_.arithFrobAt` 的定义

English:
definition _root_.arithFrobAt
  signature: [Q.IsPrime] [Finite (S ⧸ Q)]
  body: (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

中文:
定义 _root_.arithFrobAt
  签名: [Q.IsPrime] [Finite (S ⧸ Q)]
  定义体: (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

Depends on / 依赖: Finite, Q.under, exists_primesOver_isConj
-/
def _root_.arithFrobAt [Q.IsPrime] [Finite (S ⧸ Q)] : G :=
  (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

/--
lemma `arithFrobAt` / 引理 `arithFrobAt`

English:
lemma arithFrobAt
  given: [Q.IsPrime] [Finite (S ⧸ Q)]
  statement: IsArithFrobAt R (arithFrobAt R G Q) Q
  proof: (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.1 ⟨Q, ‹_›, ⟨rfl⟩⟩

中文:
引理 arithFrobAt
  条件: [Q.IsPrime] [Finite (S ⧸ Q)]
  结论: IsArithFrobAt R (arithFrobAt R G Q) Q
  证明: (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.1 ⟨Q, ‹_›, ⟨rfl⟩⟩
-/
protected lemma arithFrobAt [Q.IsPrime] [Finite (S ⧸ Q)] : IsArithFrobAt R (arithFrobAt R G Q) Q :=
  (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.1 ⟨Q, ‹_›, ⟨rfl⟩⟩

/--
theorem `arithFrobAt_mem_stabilizer` / 定理 `arithFrobAt_mem_stabilizer`

English:
theorem arithFrobAt_mem_stabilizer
  given: [Q.IsPrime] [Finite (S ⧸ Q)]
  proof: mem_stabilizer (.arithFrobAt R G Q)

中文:
定理 arithFrobAt_mem_stabilizer
  条件: [Q.IsPrime] [Finite (S ⧸ Q)]
  证明: mem_stabilizer (.arithFrobAt R G Q)

Depends on / 依赖: arithFrobAt, mem_stabilizer
-/
theorem arithFrobAt_mem_stabilizer [Q.IsPrime] [Finite (S ⧸ Q)] :
    arithFrobAt R G Q in MulAction.stabilizer G Q :=
  mem_stabilizer (.arithFrobAt R G Q)

/--
lemma `_root_.isConj_arithFrobAt` / 引理 `_root_.isConj_arithFrobAt`

English:
lemma _root_.isConj_arithFrobAt
  proof: by
  obtain ⟨P, hP, h₁, h₂⟩ : exists P : Ideal R, P.IsPrime ∧ P = Q.under R ∧ P = Q'.under R :=
    ⟨Q.under R, inferInstance, rfl, H⟩
  convert!
    (exists_primesOver_isConj S G P ⟨⟨Q, ‹_›, ⟨h₁⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.2 ⟨Q, ‹_›, ⟨h₁⟩⟩
      ⟨Q', ‹_›, ⟨h₂⟩⟩
  · subst h₁; rfl
  · subst h₂;

中文:
引理 _root_.isConj_arithFrobAt
  证明: by
  obtain ⟨P, hP, h₁, h₂⟩ : exists P : Ideal R, P.IsPrime ∧ P = Q.under R ∧ P = Q'.under R :=
    ⟨Q.under R, inferInstance, rfl, H⟩
  convert!
    (exists_primesOver_isConj S G P ⟨⟨Q, ‹_›, ⟨h₁⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.2 ⟨Q, ‹_›, ⟨h₁⟩⟩
      ⟨Q', ‹_›, ⟨h₂⟩⟩
  · subst h₁; rfl
  · subst h₂;

Depends on / 依赖: Finite, IsPrime, P.IsPrime, Q.under, choose_spec, convert, exists_primesOver_isConj
-/
lemma _root_.isConj_arithFrobAt
    [Q.IsPrime] [Finite (S ⧸ Q)] (Q' : Ideal S) [Q'.IsPrime] [Finite (S ⧸ Q')]
    (H : Q.under R = Q'.under R) : IsConj (arithFrobAt R G Q) (arithFrobAt R G Q') := by
  obtain ⟨P, hP, h₁, h₂⟩ : exists P : Ideal R, P.IsPrime ∧ P = Q.under R ∧ P = Q'.under R :=
    ⟨Q.under R, inferInstance, rfl, H⟩
  convert!
    (exists_primesOver_isConj S G P ⟨⟨Q, ‹_›, ⟨h₁⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.2 ⟨Q, ‹_›, ⟨h₁⟩⟩
      ⟨Q', ‹_›, ⟨h₂⟩⟩
  · subst h₁; rfl
  · subst h₂; rfl

end IsArithFrobAt
