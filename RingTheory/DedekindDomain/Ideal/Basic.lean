/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Pointwise
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Dedekind domains and invertible ideals

In this file, we show a ring is a Dedekind domain iff all fractional ideals are invertible,
and prove instances such as the unique factorization of ideals.
Further results on the structure of ideals in a Dedekind domain are found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`.

## Main definitions

- `isDedekindDomain_iff_mul_inv_cancel` shows an integral domain is
  a Dedekind domain iff every nonzero fractional ideal is invertible.

## Main results:

- `isDedekindDomain_iff_mul_inv_cancel`
- `Ideal.uniqueFactorizationMonoid`

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

public section Inverse

variable [Algebra A K] [IsFractionRing A K]

variable {A K}

variable {R} [IsDomain A] in
/--
theorem `FractionalIdeal.adjoinIntegral_eq_one_of_isUnit` / 定理 `FractionalIdeal.adjoinIntegral_eq_one_of_isUnit`

English:
theorem FractionalIdeal.adjoinIntegral_eq_one_of_isUnit
  statement: (x : K)
  proof: by
  set I := adjoinIntegral A⁰ x hx
  have mul_self : IsIdempotentElem I := by
    apply coeToSubmodule_injective
    simp only [coe_mul, adjoinIntegral_coe, I]
    rw [(Algebra.adjoin A {x}).isIdempotentElem_toSubmodule]
  convert! congr_arg (· * I⁻¹) mul_self <;>
    simp only [(mul_inv_cancel_if

中文:
定理 FractionalIdeal.adjoin整数egral_eq_one_of_isUnit
  结论: (x : K)
  证明: by
  set I := adjoinIntegral A⁰ x hx
  have mul_self : IsIdempotentElem I := by
    apply coeToSubmodule_injective
    simp only [coe_mul, adjoinIntegral_coe, I]
    rw [(Algebra.adjoin A {x}).isIdempotentElem_toSubmodule]
  convert! congr_arg (· * I⁻¹) mul_self <;>
    simp only [(mul_inv_cancel_if

Depends on / 依赖: Algebra, Algebra.adjoin, IsIdempotentElem, adjoin, adjoinIntegral, adjoinIntegral_coe, coeToSubmodule_injective, coe_mul, congr_arg, convert, isIdempotentElem_toSubmodule, mul_assoc, mul_inv_cancel_iff_isUnit, mul_one, mul_self
-/
theorem FractionalIdeal.adjoinIntegral_eq_one_of_isUnit (x : K)
    (hx : IsIntegral A x) (hI : IsUnit (adjoinIntegral A⁰ x hx)) : adjoinIntegral A⁰ x hx = 1 := by
  set I := adjoinIntegral A⁰ x hx
  have mul_self : IsIdempotentElem I := by
    apply coeToSubmodule_injective
    simp only [coe_mul, adjoinIntegral_coe, I]
    rw [(Algebra.adjoin A {x}).isIdempotentElem_toSubmodule]
  convert! congr_arg (· * I⁻¹) mul_self <;>
    simp only [(mul_inv_cancel_iff_isUnit K).mpr hI, mul_assoc, mul_one]

/--
theorem `FractionalIdeal.one_mem_inv_coe_ideal` / 定理 `FractionalIdeal.one_mem_inv_coe_ideal`

English:
theorem FractionalIdeal.one_mem_inv_coe_ideal
  given: [IsDomain A] {I : Ideal A} (hI : I != ⊥)
  proof: by
  rw [mem_inv_iff (coeIdeal_ne_zero.mpr hI)]
  intro y hy
  rw [one_mul]
  exact coeIdeal_le_one hy

@[deprecated (since := "2026-04-16")]
alias one_mem_inv_coe_ideal := FractionalIdeal.one_mem_inv_coe_ideal

中文:
定理 FractionalIdeal.one_mem_inv_coe_ideal
  条件: [是整环 A] {I : 理想 A} (hI : I != ⊥)
  证明: by
  rw [mem_inv_iff (coeIdeal_ne_zero.mpr hI)]
  intro y hy
  rw [one_mul]
  exact coeIdeal_le_one hy

@[deprecated (since := "2026-04-16")]
alias one_mem_inv_coe_ideal := FractionalIdeal.one_mem_inv_coe_ideal

Depends on / 依赖: coeIdeal_le_one, coeIdeal_ne_zero, coeIdeal_ne_zero.mpr, mem_inv_iff, one_mul
-/
theorem FractionalIdeal.one_mem_inv_coe_ideal [IsDomain A] {I : Ideal A} (hI : I != ⊥) :
    (1 : K) in (I : FractionalIdeal A⁰ K)⁻¹ := by
  rw [mem_inv_iff (coeIdeal_ne_zero.mpr hI)]
  intro y hy
  rw [one_mul]
  exact coeIdeal_le_one hy

@[deprecated (since := "2026-04-16")]
alias one_mem_inv_coe_ideal := FractionalIdeal.one_mem_inv_coe_ideal

/--
theorem `PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le` / 定理 `PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le`

English:
theorem PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le
  statement: [IsDedekindDomain A]
  proof: by
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := exists_primeSpectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    wellFounded_lt.has_min
      {Z | (Z.map asIdeal).prod <= I ∧ (Z.map asIdeal).pro

中文:
定理 素谱.存在_multiset_prod_cons_le_and_prod_not_le
  结论: [是Dedekind整环 A]
  证明: by
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := exists_primeSpectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    wellFounded_lt.has_min
      {Z | (Z.map asIdeal).prod <= I ∧ (Z.map asIdeal).pro
-/
theorem PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDomain A]
    (hNF : ¬IsField A) {I M : Ideal A} (hI0 : I != ⊥) (hIM : I <= M) [hM : M.IsMaximal] :
    exists Z : Multiset (PrimeSpectrum A),
      (M ::ₘ Z.map asIdeal).prod <= I ∧
        ¬Multiset.prod (Z.map asIdeal) <= I := by
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := exists_primeSpectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    wellFounded_lt.has_min
      {Z | (Z.map asIdeal).prod <= I ∧ (Z.map asIdeal).prod != ⊥}
      ⟨Z₀, hZ₀.1, hZ₀.2⟩
  obtain ⟨_, hPZ', hPM⟩ := hM.isPrime.multiset_prod_le.mp (hZI.trans hIM)
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := Multiset.mem_map.mp hPZ'
  classical
    have := Multiset.map_erase asIdeal (fun _ _ => PrimeSpectrum.ext) P Z
    obtain ⟨hP0, hZP0⟩ : P.asIdeal != ⊥ ∧ ((Z.erase P).map asIdeal).prod != ⊥ := by
      rwa [Ne, ← Multiset.cons_erase hPZ', Multiset.prod_cons, Ideal.mul_eq_bot, not_or, ←
        this] at hprodZ
    -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
    have hPM' := (P.isPrime.isMaximal hP0).eq_of_le hM.ne_top hPM
    subst hPM'
    -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
    refine ⟨Z.erase P, ?_, ?_⟩
    · convert! hZI
      rw [this]; rw [Multiset.cons_erase hPZ']
    · refine fun h => h_eraseZ (Z.erase P) ⟨h, ?_⟩ (Multiset.erase_lt.mpr hPZ)
      exact hZP0

@[deprecated (since := "2026-04-16")]
alias exists_multiset_prod_cons_le_and_prod_not_le :=
  PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le

namespace FractionalIdeal
variable [IsDedekindDomain A] {I : Ideal A}

open Ideal

/--
lemma `not_inv_le_one_of_ne_bot` / 引理 `not_inv_le_one_of_ne_bot`

English:
lemma not_inv_le_one_of_ne_bot
  given: (hI0 : I != ⊥) (hI1 : I != ⊤)
  proof: by
  have hNF : ¬IsField A := fun h => letI := h.toField; (eq_bot_or_eq_top I).elim hI0 hI1
  wlog hM : I.IsMaximal generalizing I
  · rcases I.exists_le_maximal hI1 with ⟨M, hmax, hIM⟩
    have hMbot : M != ⊥ := (M.bot_lt_of_maximal hNF).ne'
    refine mt (le_trans <| inv_anti_mono ?_ ?_ ?_) (this 

中文:
引理 not_inv_le_one_of_ne_bot
  条件: (hI0 : I != ⊥) (hI1 : I != ⊤)
  证明: by
  have hNF : ¬IsField A := fun h => letI := h.toField; (eq_bot_or_eq_top I).elim hI0 hI1
  wlog hM : I.IsMaximal generalizing I
  · rcases I.exists_le_maximal hI1 with ⟨M, hmax, hIM⟩
    have hMbot : M != ⊥ := (M.bot_lt_of_maximal hNF).ne'
    refine mt (le_trans <| inv_anti_mono ?_ ?_ ?_) (this 

Depends on / 依赖: I.IsMaximal, I.bot_lt_of_maximal, I.exists_le_maximal, IsField, IsMaximal, M.bot_lt_of_maximal, Submodule, Submodule.nonzero_mem_of_bot_lt, bot_lt_of_maximal, coeIdeal_le_coeIdeal, coeIdeal_ne_zero, eq_bot_or_eq_top, exists_le_maximal, generalizing, h.toField, hmax.ne_top, inv_anti_mono, le_trans, ne_top, nonzero_mem_of_bot_lt
-/
lemma not_inv_le_one_of_ne_bot (hI0 : I != ⊥) (hI1 : I != ⊤) :
    ¬(I⁻¹ : FractionalIdeal A⁰ K) <= 1 := by
  have hNF : ¬IsField A := fun h => letI := h.toField; (eq_bot_or_eq_top I).elim hI0 hI1
  wlog hM : I.IsMaximal generalizing I
  · rcases I.exists_le_maximal hI1 with ⟨M, hmax, hIM⟩
    have hMbot : M != ⊥ := (M.bot_lt_of_maximal hNF).ne'
    refine mt (le_trans <| inv_anti_mono ?_ ?_ ?_) (this hMbot hmax.ne_top hmax) <;>
      simpa only [coeIdeal_ne_zero, coeIdeal_le_coeIdeal]
  have hI0 : ⊥ < I := I.bot_lt_of_maximal hNF
  obtain ⟨⟨a, haI⟩, ha0⟩ := Submodule.nonzero_mem_of_bot_lt hI0
  replace ha0 : a != 0 := Subtype.coe_injective.ne ha0
  let J : Ideal A := Ideal.span {a}
  have hJ0 : J != ⊥ := mt Ideal.span_singleton_eq_bot.mp ha0
  have hJI : J <= I := I.span_singleton_le_iff_mem.2 haI
  -- Then we can find a product of prime (hence maximal) ideals contained in `J`,
  -- such that removing element `M` from the product is not contained in `J`.
  obtain ⟨Z, hle, hnle⟩ := PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJI
  -- Choose an element `b` of the product that is not in `J`.
  obtain ⟨b, hbZ, hbJ⟩ := SetLike.not_le_iff_exists.mp hnle
  have hnz_fa : algebraMap A K a != 0 :=
    mt ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) a) ha0
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine Set.not_subset.2 ⟨algebraMap A K b * (algebraMap A K a)⁻¹, (mem_inv_iff ?_).mpr ?_, ?_⟩
  · exact coeIdeal_ne_zero.mpr hI0.ne'
  · rintro y₀ hy₀
    obtain ⟨y, h_Iy, rfl⟩ := (mem_coeIdeal _).mp hy₀
    rw [mul_comm]; rw [← mul_assoc]; rw [← map_mul]
    have h_yb : y * b in J := by
      apply hle
      rw [Multiset.prod_cons]
      exact Submodule.smul_mem_smul h_Iy hbZ
    rw [Ideal.mem_span_singleton'] at h_yb
    rcases h_yb with ⟨c, hc⟩
    rw [← hc]; rw [map_mul]; rw [mul_assoc]; rw [mul_inv_cancel₀ hnz_fa]; rw [mul_one]
    apply coe_mem_one
  · refine mt (mem_one_iff _).mp ?_
    rintro ⟨x', h₂_abs⟩
    rw [← div_eq_mul_inv]; rw [eq_div_iff_mul_eq hnz_fa]; rw [← map_mul] at h₂_abs
    have := Ideal.mem_span_singleton'.mpr ⟨x', IsFractionRing.injective A K h₂_abs⟩
    contradiction

/--
theorem `mul_inv_cancel_of_le_one` / 定理 `mul_inv_cancel_of_le_one`

English:
theorem mul_inv_cancel_of_le_one
  given: (hI0 : I != ⊥) (hI : (I * (I : FractionalIdeal A⁰ K)⁻¹)⁻¹ <= 1)
  proof: by
  -- We'll show a contradiction with `exists_notMem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : exists J : Ideal A, (J : FractionalIdeal A⁰ K) = I * (I : FractionalIdeal A⁰ K)⁻¹ :=
    le_one_iff_exists_coeIdeal.mp mul_one_div_

中文:
定理 mul_inv_cancel_of_le_one
  条件: (hI0 : I != ⊥) (hI : (I * (I : FractionalIdeal A⁰ K)⁻¹)⁻¹ <= 1)
  证明: by
  -- We'll show a contradiction with `exists_notMem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : exists J : Ideal A, (J : FractionalIdeal A⁰ K) = I * (I : FractionalIdeal A⁰ K)⁻¹ :=
    le_one_iff_exists_coeIdeal.mp mul_one_div_
-/
theorem mul_inv_cancel_of_le_one (hI0 : I != ⊥) (hI : (I * (I : FractionalIdeal A⁰ K)⁻¹)⁻¹ <= 1) :
    I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show a contradiction with `exists_notMem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : exists J : Ideal A, (J : FractionalIdeal A⁰ K) = I * (I : FractionalIdeal A⁰ K)⁻¹ :=
    le_one_iff_exists_coeIdeal.mp mul_one_div_le_one
  by_cases hJ0 : J = ⊥
  · subst hJ0
    refine absurd ?_ hI0
    rw [eq_bot_iff]; rw [← coeIdeal_le_coeIdeal K]; rw [hJ]
    exact coe_ideal_le_self_mul_inv K I
  by_cases hJ1 : J = ⊤
  · rw [← hJ, hJ1, coeIdeal_top]
  exact (not_inv_le_one_of_ne_bot (K := K) hJ0 hJ1 (hJ ▸ hI)).elim

/--
theorem `coe_ideal_mul_inv` / 定理 `coe_ideal_mul_inv`

English:
theorem coe_ideal_mul_inv
  given: (I : Ideal A) (hI0 : I != ⊥)
  statement: I * (I : FractionalIdeal A⁰ K)⁻¹ = 1
  proof: by
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0
  by_cases hJ0 : I * (I : FractionalIdeal A⁰ K)⁻¹ = 0
  · rw [hJ0, inv_zero']; exact zero_le _
  intro x hx
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices x in integralClosure A K by
    rwa [

中文:
定理 coe_ideal_mul_inv
  条件: (I : 理想 A) (hI0 : I != ⊥)
  结论: I * (I : FractionalIdeal A⁰ K)⁻¹ = 1
  证明: by
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0
  by_cases hJ0 : I * (I : FractionalIdeal A⁰ K)⁻¹ = 0
  · rw [hJ0, inv_zero']; exact zero_le _
  intro x hx
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices x in integralClosure A K by
    rwa [
-/
theorem coe_ideal_mul_inv (I : Ideal A) (hI0 : I != ⊥) : I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0
  by_cases hJ0 : I * (I : FractionalIdeal A⁰ K)⁻¹ = 0
  · rw [hJ0, inv_zero']; exact zero_le _
  intro x hx
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices x in integralClosure A K by
    rwa [IsIntegrallyClosed.integralClosure_eq_bot, Algebra.mem_bot, Set.mem_range,
      ← mem_one_iff] at this
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a Noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw [mem_integralClosure_iff_mem_fg]
  have x_mul_mem : forall b in (I⁻¹ : FractionalIdeal A⁰ K), x * b in (I⁻¹ : FractionalIdeal A⁰ K) := by
    intro b hb
    rw [mem_inv_iff (coeIdeal_ne_zero.mpr hI0)]
    rw [mem_inv_iff hJ0] at hx
    simp_rw [mul_assoc, mul_comm b]
    exact fun y hy => hx _ (mul_mem_mul hy hb)
  -- It turns out the subalgebra consisting of all `p(x)` for `p : A[X]` works.
  refine ⟨AlgHom.range (Polynomial.aeval x : A[X] ->ₐ[A] K),
    isNoetherian_submodule.mp (isNoetherian (I : FractionalIdeal A⁰ K)⁻¹) _ fun y hy => ?_,
    ⟨Polynomial.X, Polynomial.aeval_X x⟩⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  rw [Polynomial.aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  clear hi
  induction i with
  | zero => rw [pow_zero]; exact one_mem_inv_coe_ideal hI0
  | succ i ih => rw [pow_succ']; exact x_mul_mem _ ih

end FractionalIdeal

end Inverse

section IsDedekindDomainInv

/--
Definition of `IsDedekindDomainInv` / `IsDedekindDomainInv` 的定义

English:
definition IsDedekindDomainInv
  signature: [IsDomain A]
  body: forall I != (⊥ : FractionalIdeal A⁰ (FractionRing A)), I * I⁻¹ = 1

中文:
定义 IsDedekindDomainInv
  签名: [是整环 A]
  定义体: forall I != (⊥ : FractionalIdeal A⁰ (FractionRing A)), I * I⁻¹ = 1

Depends on / 依赖: FractionRing, FractionalIdeal
-/
def IsDedekindDomainInv [IsDomain A] : Prop :=
  forall I != (⊥ : FractionalIdeal A⁰ (FractionRing A)), I * I⁻¹ = 1

open FractionalIdeal

variable {A K} [Algebra A K] [IsFractionRing A K]

variable {R} in
/--
theorem `isDedekindDomainInv_iff` / 定理 `isDedekindDomainInv_iff`

English:
theorem isDedekindDomainInv_iff
  given: [IsDomain A]
  proof: by
  let h : FractionalIdeal A⁰ (FractionRing A) ≃+* FractionalIdeal A⁰ K :=
    FractionalIdeal.mapEquiv (FractionRing.algEquiv A K)
  refine h.toEquiv.forall_congr (fun {x} => ?_)
  rw [← h.toEquiv.apply_eq_iff_eq]
  simp [h]

中文:
定理 isDedekindDomainInv_iff
  条件: [是整环 A]
  证明: by
  let h : FractionalIdeal A⁰ (FractionRing A) ≃+* FractionalIdeal A⁰ K :=
    FractionalIdeal.mapEquiv (FractionRing.algEquiv A K)
  refine h.toEquiv.forall_congr (fun {x} => ?_)
  rw [← h.toEquiv.apply_eq_iff_eq]
  simp [h]

Depends on / 依赖: FractionRing, FractionRing.algEquiv, FractionalIdeal, FractionalIdeal.mapEquiv, algEquiv, apply_eq_iff_eq, forall_congr, h.toEquiv.apply_eq_iff_eq, h.toEquiv.forall_congr, mapEquiv, toEquiv
-/
theorem isDedekindDomainInv_iff [IsDomain A] :
    IsDedekindDomainInv A ↔ forall I != (⊥ : FractionalIdeal A⁰ K), I * I⁻¹ = 1 := by
  let h : FractionalIdeal A⁰ (FractionRing A) ≃+* FractionalIdeal A⁰ K :=
    FractionalIdeal.mapEquiv (FractionRing.algEquiv A K)
  refine h.toEquiv.forall_congr (fun {x} => ?_)
  rw [← h.toEquiv.apply_eq_iff_eq]
  simp [h]

namespace IsDedekindDomainInv

variable (K) [IsDomain A] (h : IsDedekindDomainInv A) {I J : FractionalIdeal A⁰ K}
include h

/--
Definition of `commGroupWithZero` / `commGroupWithZero` 的定义

English:
abbreviation commGroupWithZero
  signature: : CommGroupWithZero (FractionalIdeal A⁰ K) where
  body: inv_zero' _
  mul_inv_cancel := isDedekindDomainInv_iff.mp h
  div_eq_mul_inv I J := by
    obtain rfl | hJ := eq_or_ne J 0
    · simp [inv_zero']
    refine le_antisymm ?_ ((FractionalIdeal.le_div_iff_mul_le hJ).2 ?_)
    · suffices I / J * J <= I by
        simpa [mul_assoc, isDedekindDomainInv_if

中文:
缩写 commGroupWithZero
  签名: : 带零交换群 (FractionalIdeal A⁰ K) where
  定义体: inv_zero' _
  mul_inv_cancel := isDedekindDomainInv_iff.mp h
  div_eq_mul_inv I J := by
    obtain rfl | hJ := eq_or_ne J 0
    · simp [inv_zero']
    refine le_antisymm ?_ ((FractionalIdeal.le_div_iff_mul_le hJ).2 ?_)
    · suffices I / J * J <= I by
        simpa [mul_assoc, isDedekindDomainInv_if

Depends on / 依赖: inv_zero
-/
noncomputable abbrev commGroupWithZero : CommGroupWithZero (FractionalIdeal A⁰ K) where
  inv_zero := inv_zero' _
  mul_inv_cancel := isDedekindDomainInv_iff.mp h
  div_eq_mul_inv I J := by
    obtain rfl | hJ := eq_or_ne J 0
    · simp [inv_zero']
    refine le_antisymm ?_ ((FractionalIdeal.le_div_iff_mul_le hJ).2 ?_)
    · suffices I / J * J <= I by
        simpa [mul_assoc, isDedekindDomainInv_iff.mp h _ hJ] using mul_left_mono (a := J⁻¹) this
      simp [FractionalIdeal.mul_le, mem_div_iff_of_ne_zero hJ]
    · rw [mul_assoc, mul_comm _ J, isDedekindDomainInv_iff.mp h _ hJ, mul_one]

/--
theorem `isNoetherianRing` / 定理 `isNoetherianRing`

English:
theorem isNoetherianRing
  statement: IsNoetherianRing A
  proof: by
  let := h.commGroupWithZero (FractionRing A)
  refine isNoetherianRing_iff.mpr ⟨fun I : Ideal A => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; apply Submodule.fg_bot
  have hI : (I : FractionalIdeal A⁰ (FractionRing A)) != 0 := coeIdeal_ne_zero.mpr hI
  exact I.fg_of_isUnit (IsFractionRing.injective 

中文:
定理 isNoetherianRing
  结论: 是Noether环 A
  证明: by
  let := h.commGroupWithZero (FractionRing A)
  refine isNoetherianRing_iff.mpr ⟨fun I : Ideal A => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; apply Submodule.fg_bot
  have hI : (I : FractionalIdeal A⁰ (FractionRing A)) != 0 := coeIdeal_ne_zero.mpr hI
  exact I.fg_of_isUnit (IsFractionRing.injective 

Depends on / 依赖: FractionRing, FractionalIdeal, I.fg_of_isUnit, IsFractionRing, IsFractionRing.injective, Submodule, Submodule.fg_bot, coeIdeal_ne_zero, coeIdeal_ne_zero.mpr, commGroupWithZero, fg_bot, fg_of_isUnit, h.commGroupWithZero, hI.isUnit, injective, isNoetherianRing_iff, isNoetherianRing_iff.mpr, isUnit
-/
theorem isNoetherianRing : IsNoetherianRing A := by
  let := h.commGroupWithZero (FractionRing A)
  refine isNoetherianRing_iff.mpr ⟨fun I : Ideal A => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; apply Submodule.fg_bot
  have hI : (I : FractionalIdeal A⁰ (FractionRing A)) != 0 := coeIdeal_ne_zero.mpr hI
  exact I.fg_of_isUnit (IsFractionRing.injective A (FractionRing A)) hI.isUnit

/--
theorem `integrallyClosed` / 定理 `integrallyClosed`

English:
theorem integrallyClosed
  statement: IsIntegrallyClosed A
  proof: by
  let := h.commGroupWithZero (FractionRing A)
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr (fun {x hx} => ?_)
  rw [← Set.mem_range]; rw [← Algebra.mem_bot]; rw [← Subalgeb

中文:
定理 integrallyClosed
  结论: 是整闭 A
  证明: by
  let := h.commGroupWithZero (FractionRing A)
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr (fun {x hx} => ?_)
  rw [← Set.mem_range]; rw [← Algebra.mem_bot]; rw [← Subalgeb

Depends on / 依赖: FractionRing, commGroupWithZero, h.commGroupWithZero
-/
theorem integrallyClosed : IsIntegrallyClosed A := by
  let := h.commGroupWithZero (FractionRing A)
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr (fun {x hx} => ?_)
  rw [← Set.mem_range]; rw [← Algebra.mem_bot]; rw [← Subalgebra.mem_toSubmodule]; rw [Algebra.toSubmodule_bot]; rw [Submodule.one_eq_span]; rw [← coe_spanSingleton A⁰ (1 : FractionRing A)]; rw [spanSingleton_one]; rw [←
    FractionalIdeal.adjoinIntegral_eq_one_of_isUnit x hx (Ne.isUnit _)]
  · exact mem_adjoinIntegral_self A⁰ x hx
  · exact fun h => one_ne_zero (eq_zero_iff.mp h 1 (Algebra.adjoin A {x}).one_mem)

open Ring

/--
theorem `dimensionLEOne` / 定理 `dimensionLEOne`

English:
theorem dimensionLEOne
  statement: DimensionLEOne A
  proof: by
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  let := h.commGroupWithZero (K := FractionRing A)
  constructor
  rintro P P_ne hP
  refine Ideal.isMaximal_def.mpr ⟨hP.ne_top, fun M hM => ?_⟩
  -- We may assume `P` and `M` (

中文:
定理 dimensionLEOne
  结论: 维数不超过一 A
  证明: by
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  let := h.commGroupWithZero (K := FractionRing A)
  constructor
  rintro P P_ne hP
  refine Ideal.isMaximal_def.mpr ⟨hP.ne_top, fun M hM => ?_⟩
  -- We may assume `P` and `M` (
-/
theorem dimensionLEOne : DimensionLEOne A := by
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  let := h.commGroupWithZero (K := FractionRing A)
  constructor
  rintro P P_ne hP
  refine Ideal.isMaximal_def.mpr ⟨hP.ne_top, fun M hM => ?_⟩
  -- We may assume `P` and `M` (as fractional ideals) are nonzero.
  have P'_ne : (P : FractionalIdeal A⁰ (FractionRing A)) != 0 := coeIdeal_ne_zero.mpr P_ne
  have M'_ne : (M : FractionalIdeal A⁰ (FractionRing A)) != 0 := coeIdeal_ne_zero.mpr hM.ne_bot
  -- In particular, we'll show `M⁻¹ * P ≤ P`
  suffices (M⁻¹ : FractionalIdeal A⁰ (FractionRing A)) * P <= P by
    rw [eq_top_iff]; rw [← coeIdeal_le_coeIdeal (FractionRing A)]; rw [coeIdeal_top]
    calc
      (1 : FractionalIdeal A⁰ (FractionRing A)) = (↑M)⁻¹ * P * ((↑P)⁻¹ * M) := by
        simp [mul_assoc, *]
      _ <= P * ((↑P)⁻¹ * M) := by gcongr
      _ = M := by simp [*]
  -- Suppose we have `x ∈ M⁻¹ * P`, then in fact `x = algebraMap _ _ y` for some `y`.
  intro x hx
  have le_one : (M⁻¹ : FractionalIdeal A⁰ (FractionRing A)) * P <= 1 := by
    rw [← inv_mul_cancel₀ M'_ne]; gcongr
  obtain ⟨y, _hy, rfl⟩ := (mem_coeIdeal _).mp (le_one hx)
  -- Since `M` is strictly greater than `P`, let `z ∈ M \ P`.
  obtain ⟨z, hzM, hzp⟩ := SetLike.exists_of_lt hM
  -- We have `z * y ∈ M * (M⁻¹ * P) = P`.
  have zy_mem := mul_mem_mul (mem_coeIdeal_of_mem A⁰ hzM) hx
  rw [← map_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀ M'_ne]; rw [one_mul] at zy_mem
  obtain ⟨zy, hzy, zy_eq⟩ := (mem_coeIdeal A⁰).mp zy_mem
  rw [IsFractionRing.injective A (FractionRing A) zy_eq] at hzy
  -- But `P` is a prime ideal, so `z ∉ P` implies `y ∈ P`, as desired.
  exact mem_coeIdeal_of_mem A⁰ (Or.resolve_left (hP.mem_or_mem hzy) hzp)

end IsDedekindDomainInv

/--
theorem `isDedekindDomain_iff_isDedekindDomainInv` / 定理 `isDedekindDomain_iff_isDedekindDomainInv`

English:
theorem isDedekindDomain_iff_isDedekindDomainInv
  given: [IsDomain A]
  proof: by
  refine ⟨fun _ I hI => ?_, fun h =>
    { h.isNoetherianRing, h.dimensionLEOne, h.integrallyClosed with }⟩
  obtain ⟨a, J, ha, hJ⟩ := exists_eq_spanSingleton_mul (K := FractionRing A) I
  suffices h₂ : I * (spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ _)⁻¹) = 1 by
    rw [mul_in

中文:
定理 isDedekindDomain_iff_isDedekindDomainInv
  条件: [是整环 A]
  证明: by
  refine ⟨fun _ I hI => ?_, fun h =>
    { h.isNoetherianRing, h.dimensionLEOne, h.integrallyClosed with }⟩
  obtain ⟨a, J, ha, hJ⟩ := exists_eq_spanSingleton_mul (K := FractionRing A) I
  suffices h₂ : I * (spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ _)⁻¹) = 1 by
    rw [mul_in

Depends on / 依赖: FractionRing, FractionalIdeal, algebraMap, coe_ideal_mul_inv, dimensionLEOne, exists_eq_spanSingleton_mul, h.dimensionLEOne, h.integrallyClosed, h.isNoetherianRing, integrallyClosed, isNoetherianRing, mul_assoc, mul_inv_cancel_iff, mul_left_comm, mul_one, spanSin, spanSingleton
-/
theorem isDedekindDomain_iff_isDedekindDomainInv [IsDomain A] :
    IsDedekindDomain A ↔ IsDedekindDomainInv A := by
  refine ⟨fun _ I hI => ?_, fun h =>
    { h.isNoetherianRing, h.dimensionLEOne, h.integrallyClosed with }⟩
  obtain ⟨a, J, ha, hJ⟩ := exists_eq_spanSingleton_mul (K := FractionRing A) I
  suffices h₂ : I * (spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ _)⁻¹) = 1 by
    rw [mul_inv_cancel_iff]
    exact ⟨spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ _)⁻¹, h₂⟩
  subst hJ
  rw [mul_assoc]; rw [mul_left_comm (J : FractionalIdeal A⁰ _)]; rw [coe_ideal_mul_inv]; rw [mul_one]; rw [spanSingleton_mul_spanSingleton]; rw [inv_mul_cancel₀]; rw [spanSingleton_one]
  · exact mt ((injective_iff_map_eq_zero (algebraMap A _)).mp (IsFractionRing.injective A _) _) ha
  · exact coeIdeal_ne_zero.mp (right_ne_zero_of_mul hI)

public theorem isDedekindDomain_iff_mul_inv_cancel [IsDomain A] :
    IsDedekindDomain A ↔ forall I != (⊥ : FractionalIdeal A⁰ K), I * I⁻¹ = 1 :=
  isDedekindDomain_iff_isDedekindDomainInv.trans isDedekindDomainInv_iff

end IsDedekindDomainInv

public section IsDedekindDomain

variable {R A}
variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal Ideal

namespace FractionalIdeal

/--
Instance `semifield` / 实例 `semifield`

English:
instance semifield
  signature: : Semifield (FractionalIdeal A⁰ K) where
  body: coeIdeal_injective.nontrivial
  __ : CommSemiring (FractionalIdeal A⁰ K) := inferInstance
  inv_zero := inv_zero' K
  mul_inv_cancel := isDedekindDomain_iff_mul_inv_cancel.mp ‹_›
  div_eq_mul_inv := by
    let := (isDedekindDomain_iff_isDedekindDomainInv.mp ‹_›).commGroupWithZero K
    exact div_eq_

中文:
实例 semifield
  签名: : 半域 (FractionalIdeal A⁰ K) where
  定义体: coeIdeal_injective.nontrivial
  __ : CommSemiring (FractionalIdeal A⁰ K) := inferInstance
  inv_zero := inv_zero' K
  mul_inv_cancel := isDedekindDomain_iff_mul_inv_cancel.mp ‹_›
  div_eq_mul_inv := by
    let := (isDedekindDomain_iff_isDedekindDomainInv.mp ‹_›).commGroupWithZero K
    exact div_eq_

Depends on / 依赖: coeIdeal_injective, coeIdeal_injective.nontrivial, nontrivial
-/
noncomputable instance semifield : Semifield (FractionalIdeal A⁰ K) where
  __ := coeIdeal_injective.nontrivial
  __ : CommSemiring (FractionalIdeal A⁰ K) := inferInstance
  inv_zero := inv_zero' K
  mul_inv_cancel := isDedekindDomain_iff_mul_inv_cancel.mp ‹_›
  div_eq_mul_inv := by
    let := (isDedekindDomain_iff_isDedekindDomainInv.mp ‹_›).commGroupWithZero K
    exact div_eq_mul_inv
  nnqsmul := _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PosMulStrictMono (FractionalIdeal A⁰ K)
  body: PosMulMono.toPosMulStrictMono

中文:
实例 :
  签名: 正乘严格递增 (FractionalIdeal A⁰ K)
  定义体: PosMulMono.toPosMulStrictMono

Depends on / 依赖: PosMulMono, PosMulMono.toPosMulStrictMono, toPosMulStrictMono
-/
instance : PosMulStrictMono (FractionalIdeal A⁰ K) := PosMulMono.toPosMulStrictMono
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulPosStrictMono (FractionalIdeal A⁰ K)
  body: MulPosMono.toMulPosStrictMono

中文:
实例 :
  签名: 乘正严格递增 (FractionalIdeal A⁰ K)
  定义体: MulPosMono.toMulPosStrictMono

Depends on / 依赖: MulPosMono, MulPosMono.toMulPosStrictMono, toMulPosStrictMono
-/
instance : MulPosStrictMono (FractionalIdeal A⁰ K) := MulPosMono.toMulPosStrictMono

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PosMulReflectLE (FractionalIdeal A⁰ K)
  body: by simpa [I.2.ne'] using mul_right_mono (a := I.1⁻¹) hJK

中文:
实例 :
  签名: 正乘反映偏序 (FractionalIdeal A⁰ K)
  定义体: by simpa [I.2.ne'] using mul_right_mono (a := I.1⁻¹) hJK

Depends on / 依赖: mul_right_mono
-/
instance : PosMulReflectLE (FractionalIdeal A⁰ K) where
  elim I J K hJK := by simpa [I.2.ne'] using mul_right_mono (a := I.1⁻¹) hJK

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulPosReflectLE (FractionalIdeal A⁰ K)
  body: by simpa [I.2.ne'] using mul_left_mono (a := I.1⁻¹) hJK

中文:
实例 :
  签名: 乘正反映偏序 (FractionalIdeal A⁰ K)
  定义体: by simpa [I.2.ne'] using mul_left_mono (a := I.1⁻¹) hJK

Depends on / 依赖: mul_left_mono
-/
instance : MulPosReflectLE (FractionalIdeal A⁰ K) where
  elim I J K hJK := by simpa [I.2.ne'] using mul_left_mono (a := I.1⁻¹) hJK

/--
lemma `mul_left_strictMono` / 引理 `mul_left_strictMono`

English:
lemma mul_left_strictMono
  given: {I : FractionalIdeal A⁰ K} (hI : I != 0)
  statement: StrictMono (· * I)
  proof: fun _J _K hJK => mul_lt_mul_of_pos_right hJK pos_iff_ne_zero.2 hI

中文:
引理 mul_left_strictMono
  条件: {I : FractionalIdeal A⁰ K} (hI : I != 0)
  结论: 严格递增 (· * I)
  证明: fun _J _K hJK => mul_lt_mul_of_pos_right hJK pos_iff_ne_zero.2 hI

Depends on / 依赖: mul_lt_mul_of_pos_right, pos_iff_ne_zero
-/
lemma mul_left_strictMono {I : FractionalIdeal A⁰ K} (hI : I != 0) : StrictMono (· * I) :=
fun _J _K hJK => mul_lt_mul_of_pos_right hJK pos_iff_ne_zero.2 hI

/--
lemma `mul_right_strictMono` / 引理 `mul_right_strictMono`

English:
lemma mul_right_strictMono
  given: {I : FractionalIdeal A⁰ K} (hI : I != 0)
  statement: StrictMono (I * ·)
  proof: fun _J _K hJK => mul_lt_mul_of_pos_left hJK pos_iff_ne_zero.2 hI

中文:
引理 mul_right_strictMono
  条件: {I : FractionalIdeal A⁰ K} (hI : I != 0)
  结论: 严格递增 (I * ·)
  证明: fun _J _K hJK => mul_lt_mul_of_pos_left hJK pos_iff_ne_zero.2 hI

Depends on / 依赖: mul_lt_mul_of_pos_left, pos_iff_ne_zero
-/
lemma mul_right_strictMono {I : FractionalIdeal A⁰ K} (hI : I != 0) : StrictMono (I * ·) :=
fun _J _K hJK => mul_lt_mul_of_pos_left hJK pos_iff_ne_zero.2 hI

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PosMulReflectLE (Ideal A)
  body: by
    dsimp
    rwa [← FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing A),
      ← mul_le_mul_iff_right₀ (α := FractionalIdeal A⁰ (FractionRing A)) (a := I.1)
        (by simpa [pos_iff_ne_zero] using I.2.ne'),
      ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
      Fractiona

中文:
实例 :
  签名: 正乘反映偏序 (理想 A)
  定义体: by
    dsimp
    rwa [← FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing A),
      ← mul_le_mul_iff_right₀ (α := FractionalIdeal A⁰ (FractionRing A)) (a := I.1)
        (by simpa [pos_iff_ne_zero] using I.2.ne'),
      ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
      Fractiona

Depends on / 依赖: FractionRing, FractionalIdeal, FractionalIdeal.coeIdeal_le_coeIdeal, FractionalIdeal.coeIdeal_mul, coeIdeal_le_coeIdeal, coeIdeal_mul, pos_iff_ne_zero
-/
instance : PosMulReflectLE (Ideal A) where
  elim I J K e := by
    dsimp
    rwa [← FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing A),
      ← mul_le_mul_iff_right₀ (α := FractionalIdeal A⁰ (FractionRing A)) (a := I.1)
        (by simpa [pos_iff_ne_zero] using I.2.ne'),
      ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_le_coeIdeal]

end FractionalIdeal

/--
Instance `Ideal.isCancelMulZero` / 实例 `Ideal.isCancelMulZero`

English:
instance Ideal.isCancelMulZero
  signature: : IsCancelMulZero (Ideal A)
  body: Function.Injective.isCancelMulZero (coeIdealHom A⁰ (FractionRing A)) coeIdeal_injective
    (map_zero _) (map_mul _)

中文:
实例 理想.isCancelMulZero
  签名: : 是乘零消去 (理想 A)
  定义体: Function.Injective.isCancelMulZero (coeIdealHom A⁰ (FractionRing A)) coeIdeal_injective
    (map_zero _) (map_mul _)

Depends on / 依赖: Definable, Definable.out, FractionRing, Function, Function.Injective.isCancelMulZero, Injective, coeIdealHom, coeIdeal_injective, isCancelMulZero, map_mul, map_zero
-/
noncomputable instance Ideal.isCancelMulZero : IsCancelMulZero (Ideal A) :=
  Function.Injective.isCancelMulZero (coeIdealHom A⁰ (FractionRing A)) coeIdeal_injective
    (map_zero _) (map_mul _)

/--
Instance `Ideal.isDomain` / 实例 `Ideal.isDomain`

English:
instance Ideal.isDomain
  signature: : IsDomain (Ideal A) where

中文:
实例 理想.isDomain
  签名: : 是整环 (理想 A) where

Depends on / 依赖: Definable, Definable.out
-/
instance Ideal.isDomain : IsDomain (Ideal A) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PosMulStrictMono (Ideal A)
  body: PosMulMono.toPosMulStrictMono

中文:
实例 :
  签名: 正乘严格递增 (理想 A)
  定义体: PosMulMono.toPosMulStrictMono

Depends on / 依赖: PosMulMono, PosMulMono.toPosMulStrictMono, toPosMulStrictMono
-/
instance : PosMulStrictMono (Ideal A) := PosMulMono.toPosMulStrictMono

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulPosStrictMono (Ideal A)
  body: MulPosMono.toMulPosStrictMono

中文:
实例 :
  签名: 乘正严格递增 (理想 A)
  定义体: MulPosMono.toMulPosStrictMono
-/
instance : MulPosStrictMono (Ideal A) := MulPosMono.toMulPosStrictMono

/--
theorem `Ideal.dvd_iff_le` / 定理 `Ideal.dvd_iff_le`

English:
theorem Ideal.dvd_iff_le
  given: {I J : Ideal A}
  statement: I ∣ J ↔ J <= I
  proof: ⟨Ideal.le_of_dvd, fun h => by
    by_cases hI : I = ⊥
    · have hJ : J = ⊥ := by rwa [hI, ← eq_bot_iff] at h
      rw [hI]; rw [hJ]
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) != 0 := coeIdeal_ne_zero.mpr hI
    have : (I : FractionalIdeal A⁰ (FractionRing A))⁻¹ * J <= 1 := by
      rw

中文:
定理 理想.dvd_iff_le
  条件: {I J : 理想 A}
  结论: I ∣ J ↔ J <= I
  证明: ⟨Ideal.le_of_dvd, fun h => by
    by_cases hI : I = ⊥
    · have hJ : J = ⊥ := by rwa [hI, ← eq_bot_iff] at h
      rw [hI]; rw [hJ]
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) != 0 := coeIdeal_ne_zero.mpr hI
    have : (I : FractionalIdeal A⁰ (FractionRing A))⁻¹ * J <= 1 := by
      rw

Depends on / 依赖: FractionRing, FractionalIdeal, Ideal.le_of_dvd, coeIdeal_injective, coeIdeal_mul, coeIdeal_ne_zero, coeIdeal_ne_zero.mpr, eq_bot_iff, le_of_dvd, le_one_iff_exists_coeIdeal, le_one_iff_exists_coeIdeal.mp, mul_asso
-/
theorem Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I :=
  ⟨Ideal.le_of_dvd, fun h => by
    by_cases hI : I = ⊥
    · have hJ : J = ⊥ := by rwa [hI, ← eq_bot_iff] at h
      rw [hI]; rw [hJ]
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) != 0 := coeIdeal_ne_zero.mpr hI
    have : (I : FractionalIdeal A⁰ (FractionRing A))⁻¹ * J <= 1 := by
      rw [← inv_mul_cancel₀ hI']; gcongr
    obtain ⟨H, hH⟩ := le_one_iff_exists_coeIdeal.mp this
    use H
    refine coeIdeal_injective (show (J : FractionalIdeal A⁰ (FractionRing A)) = ↑(I * H) from ?_)
    rw [coeIdeal_mul]; rw [hH]; rw [← mul_assoc]; rw [mul_inv_cancel₀ hI']; rw [one_mul]⟩

/--
theorem `Ideal.liesOver_iff_dvd_map` / 定理 `Ideal.liesOver_iff_dvd_map`

English:
theorem Ideal.liesOver_iff_dvd_map
  statement: [Algebra R A] {p : Ideal R} {P : Ideal A} (hP : P != ⊤)
  proof: by
  rw [liesOver_iff]; rw [dvd_iff_le]; rw [under_def]; rw [map_le_iff_le_comap]; rw [IsCoatom.le_iff_eq (by rwa [← isMaximal_def]) (comap_ne_top _ hP), eq_comm]

中文:
定理 理想.liesOver_iff_dvd_map
  结论: [代数 R A] {p : 理想 R} {P : 理想 A} (hP : P != ⊤)
  证明: by
  rw [liesOver_iff]; rw [dvd_iff_le]; rw [under_def]; rw [map_le_iff_le_comap]; rw [IsCoatom.le_iff_eq (by rwa [← isMaximal_def]) (comap_ne_top _ hP), eq_comm]

Depends on / 依赖: IsCoatom, IsCoatom.le_iff_eq, comap_ne_top, dvd_iff_le, eq_comm, isMaximal_def, le_iff_eq, liesOver_iff, map_le_iff_le_comap, under_def
-/
theorem Ideal.liesOver_iff_dvd_map [Algebra R A] {p : Ideal R} {P : Ideal A} (hP : P != ⊤)
    [p.IsMaximal] :
    P.LiesOver p ↔ P ∣ Ideal.map (algebraMap R A) p := by
  rw [liesOver_iff]; rw [dvd_iff_le]; rw [under_def]; rw [map_le_iff_le_comap]; rw [IsCoatom.le_iff_eq (by rwa [← isMaximal_def]) (comap_ne_top _ hP), eq_comm]

/--
theorem `Ideal.dvdNotUnit_iff_lt` / 定理 `Ideal.dvdNotUnit_iff_lt`

English:
theorem Ideal.dvdNotUnit_iff_lt
  given: {I J : Ideal A}
  statement: DvdNotUnit I J ↔ J < I
  proof: ⟨fun ⟨hI, H, hunit, hmul⟩ =>
    lt_of_le_of_ne (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
      (mt
        (fun h =>
          have : H = 1 := mul_left_cancel₀ hI (by rw [← hmul, h, mul_one])
          show IsUnit H from this.symm ▸ isUnit_one)
        hunit),
    fun h =>
    dvdNotUnit_of_dvd_of_not_dvd (I

中文:
定理 理想.dvdNotUnit_iff_lt
  条件: {I J : 理想 A}
  结论: DvdNotUnit I J ↔ J < I
  证明: ⟨fun ⟨hI, H, hunit, hmul⟩ =>
    lt_of_le_of_ne (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
      (mt
        (fun h =>
          have : H = 1 := mul_left_cancel₀ hI (by rw [← hmul, h, mul_one])
          show IsUnit H from this.symm ▸ isUnit_one)
        hunit),
    fun h =>
    dvdNotUnit_of_dvd_of_not_dvd (I

Depends on / 依赖: Ideal.dvd_iff_le.mp, Ideal.dvd_iff_le.mpr, IsUnit, dvdNotUnit_of_dvd_of_not_dvd, dvd_iff_le, isUnit_one, le_of_lt, lt_of_le_of_ne, mul_one, not_le_of_gt, this.symm
-/
theorem Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNotUnit I J ↔ J < I :=
  ⟨fun ⟨hI, H, hunit, hmul⟩ =>
    lt_of_le_of_ne (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
      (mt
        (fun h =>
          have : H = 1 := mul_left_cancel₀ hI (by rw [← hmul, h, mul_one])
          show IsUnit H from this.symm ▸ isUnit_one)
        hunit),
    fun h =>
    dvdNotUnit_of_dvd_of_not_dvd (Ideal.dvd_iff_le.mpr (le_of_lt h))
      (mt Ideal.dvd_iff_le.mp (not_le_of_gt h))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WfDvdMonoid (Ideal A)
  body: by
    have : WellFoundedGT (Ideal A) := inferInstance
    convert! this.wf using 3
    exact Ideal.dvdNotUnit_iff_lt

中文:
实例 :
  签名: WfDvdMonoid (理想 A)
  定义体: by
    have : WellFoundedGT (Ideal A) := inferInstance
    convert! this.wf using 3
    exact Ideal.dvdNotUnit_iff_lt
-/
instance : WfDvdMonoid (Ideal A) where
  wf := by
    have : WellFoundedGT (Ideal A) := inferInstance
    convert! this.wf using 3
    exact Ideal.dvdNotUnit_iff_lt

/--
Instance `Ideal.uniqueFactorizationMonoid` / 实例 `Ideal.uniqueFactorizationMonoid`

English:
instance Ideal.uniqueFactorizationMonoid
  signature: : UniqueFactorizationMonoid (Ideal A)
  body: { irreducible_iff_prime := by
      intro P
      exact ⟨fun hirr => ⟨hirr.ne_zero, hirr.not_isUnit, fun I J => by
        have : P.IsMaximal := by
          refine ⟨⟨mt Ideal.isUnit_iff.mpr hirr.not_isUnit, ?_⟩⟩
          intro J hJ
          obtain ⟨_J_ne, H, hunit, P_eq⟩ := Ideal.dvdNotUnit_iff_l

中文:
实例 理想.uniqueFactorizationMonoid
  签名: : 唯一分解幺半群 (理想 A)
  定义体: { irreducible_iff_prime := by
      intro P
      exact ⟨fun hirr => ⟨hirr.ne_zero, hirr.not_isUnit, fun I J => by
        have : P.IsMaximal := by
          refine ⟨⟨mt Ideal.isUnit_iff.mpr hirr.not_isUnit, ?_⟩⟩
          intro J hJ
          obtain ⟨_J_ne, H, hunit, P_eq⟩ := Ideal.dvdNotUnit_iff_l

Depends on / 依赖: Ideal.dvdNotUnit_iff_lt.mpr, Ideal.dvd_iff_le, Ideal.isUnit_iff.mp, Ideal.isUnit_iff.mpr, IsMaximal, P.IsMaximal, P_eq, SetLike, SetLike.le_def, _J_ne, contrapose, dvdNotUnit_iff_lt, dvd_iff_le, hirr.isUnit_or_isUnit, hirr.ne_zero, hirr.not_isUnit, irreducible_iff_prime, isUnit_iff, isUnit_or_isUnit, le_def
-/
instance Ideal.uniqueFactorizationMonoid : UniqueFactorizationMonoid (Ideal A) :=
  { irreducible_iff_prime := by
      intro P
      exact ⟨fun hirr => ⟨hirr.ne_zero, hirr.not_isUnit, fun I J => by
        have : P.IsMaximal := by
          refine ⟨⟨mt Ideal.isUnit_iff.mpr hirr.not_isUnit, ?_⟩⟩
          intro J hJ
          obtain ⟨_J_ne, H, hunit, P_eq⟩ := Ideal.dvdNotUnit_iff_lt.mpr hJ
          exact Ideal.isUnit_iff.mp ((hirr.isUnit_or_isUnit P_eq).resolve_right hunit)
        rw [Ideal.dvd_iff_le]; rw [Ideal.dvd_iff_le]; rw [Ideal.dvd_iff_le]; rw [SetLike.le_def]; rw [SetLike.le_def]; rw [SetLike.le_def]
        contrapose!
        rintro ⟨⟨x, x_mem, x_notMem⟩, ⟨y, y_mem, y_notMem⟩⟩
        exact
          ⟨x * y, Ideal.mul_mem_mul x_mem y_mem,
            mt this.isPrime.mem_or_mem (not_or_intro x_notMem y_notMem)⟩⟩, Prime.irreducible⟩ }

/--
Instance `Ideal.strongNormalizationMonoid` / 实例 `Ideal.strongNormalizationMonoid`

English:
instance Ideal.strongNormalizationMonoid
  signature: : StrongNormalizationMonoid (Ideal A)
  body: inferInstance

@[deprecated (since := "2026-07-08")]
alias Ideal.normalizationMonoid := Ideal.strongNormalizationMonoid

中文:
实例 理想.strongNormalizationMonoid
  签名: : StrongNormalization幺半群 (理想 A)
  定义体: inferInstance

@[deprecated (since := "2026-07-08")]
alias Ideal.normalizationMonoid := Ideal.strongNormalizationMonoid
-/
noncomputable instance Ideal.strongNormalizationMonoid : StrongNormalizationMonoid (Ideal A) :=
  inferInstance

@[deprecated (since := "2026-07-08")]
alias Ideal.normalizationMonoid := Ideal.strongNormalizationMonoid

end IsDedekindDomain
