/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!

# Minimal primes and localization

We provide various results concerning the minimal primes above an ideal that require the theory
of localizations.

## Main results
- `Ideal.exists_minimalPrimes_comap_eq` If `p` is a minimal prime over `f ⁻¹ I`, then it is the
  preimage of some minimal prime over `I`.
- `Ideal.minimalPrimes_eq_comap`: The minimal primes over `I` are precisely the preimages of
  minimal primes of `R ⧸ I`.
- `IsLocalization.minimalPrimes_comap`: If `A` is a localization of `R` with respect to the
  submonoid `S`, `J` is an ideal of `A`, then the minimal primes over the preimage of `J`
  (under `R →+* A`) are exactly the preimages of the minimal primes over `J`.
- `IsLocalization.minimalPrimes_map`: If `A` is a localization of `R` with respect to the
  submonoid `S`, `J` is an ideal of `R`, then the minimal primes over the span of the image of `J`
  (under `R →+* A`) are exactly the ideals of `A` such that the preimage of which is a minimal prime
  over `J`.
- `Localization.AtPrime.prime_unique_of_minimal`: When localizing at a minimal prime ideal `I`,
  the resulting ring only has a single prime ideal.
-/

public section


section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {I J : Ideal R}

/--
theorem `Ideal.iUnion_minimalPrimes` / 定理 `Ideal.iUnion_minimalPrimes`

English:
theorem Ideal.iUnion_minimalPrimes
  proof: by
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨⟨hp₁, hp₂⟩, hp₃⟩, hxp⟩
    have : p.map (algebraMap R (Localization.AtPrime p)) <= (I.map (algebraMap _ _)).radical := by
      rw [Ideal.radical_eq_sInf]; rw [le_sInf_iff]
      rintro q ⟨hq', hq⟩
      obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
      rw [Ideal.map_le_iff_le_comap] at hq' ⊢
      exact hp₃ ⟨h₁, hq'⟩ h₂
    obtain ⟨n, hn⟩ := this (Ideal.mem_map_of_mem _ hxp)
    rw [IsLocalization.mem_map_algebraMap_iff (M := p.primeCompl)] at hn
    obtain ⟨⟨a, b⟩, hn⟩ := hn
    rw [← map_pow]; rw [← map_mul]; rw [IsLocalization.eq_iff_exists p.primeCompl] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨t * b, fun h => (t * b).2 (hp₁.radical_le_iff.mpr hp₂ h), n + 1, ?_⟩
    simp only at ht
    have : (x * (t.1 * b.1)) ^ (n + 1) = (t.1 ^ n * b.1 ^ n * x * t.1) * a := by
      rw [mul_assoc]; rw [← ht]; ring
    rw [this]
    exact I.mul_mem_left _ a.2
  · rintro ⟨y, hy, hx⟩
    obtain ⟨p, hp, hyp⟩ : exists p in I.minimalPrimes, y ∉ p := by
      simpa [← Ideal.sInf_minimalPrimes] using hy
    refine ⟨p, hp, (hp.isPrime.mem_or_mem ?_).resolve_right hyp⟩
    exact hp.isPrime.radical_le_iff.mpr hp.le hx

中文:
定理 理想.iUnion_minimalPrimes
  证明: by
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨⟨hp₁, hp₂⟩, hp₃⟩, hxp⟩
    have : p.map (algebraMap R (Localization.AtPrime p)) <= (I.map (algebraMap _ _)).radical := by
      rw [Ideal.radical_eq_sInf]; rw [le_sInf_iff]
      rintro q ⟨hq', hq⟩
      obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
      rw [Ideal.map_le_iff_le_comap] at hq' ⊢
      exact hp₃ ⟨h₁, hq'⟩ h₂
    obtain ⟨n, hn⟩ := this (Ideal.mem_map_of_mem _ hxp)
    rw [IsLocalization.mem_map_algebraMap_iff (M := p.primeCompl)] at hn
    obtain ⟨⟨a, b⟩, hn⟩ := hn
    rw [← map_pow]; rw [← map_mul]; rw [IsLocalization.eq_iff_exists p.primeCompl] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨t * b, fun h => (t * b).2 (hp₁.radical_le_iff.mpr hp₂ h), n + 1, ?_⟩
    simp only at ht
    have : (x * (t.1 * b.1)) ^ (n + 1) = (t.1 ^ n * b.1 ^ n * x * t.1) * a := by
      rw [mul_assoc]; rw [← ht]; ring
    rw [this]
    exact I.mul_mem_left _ a.2
  · rintro ⟨y, hy, hx⟩
    obtain ⟨p, hp, hyp⟩ : exists p in I.minimalPrimes, y ∉ p := by
      simpa [← Ideal.sInf_minimalPrimes] using hy
    refine ⟨p, hp, (hp.isPrime.mem_or_mem ?_).resolve_right hyp⟩
    exact hp.isPrime.radical_le_iff.mpr hp.le hx

Depends on / 依赖: AtPrime, I.map, Ideal.map_le_iff_le_comap, Ideal.mem_map_of_mem, Ideal.radical_eq_sInf, IsLocalizati, IsLocalization, IsLocalization.AtPrime.orderIsoOfPrime, Localization, Localization.AtPrime, Set.mem_iUnion, Set.mem_ofPred_eq, SetLike, SetLike.mem_coe, algebraMap, exists_prop, le_sInf_iff, map_le_iff_le_comap, mem_coe, mem_iUnion
-/
theorem Ideal.iUnion_minimalPrimes :
    ⋃ p in I.minimalPrimes, p = { x | exists y ∉ I.radical, x * y in I.radical } := by
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨⟨hp₁, hp₂⟩, hp₃⟩, hxp⟩
    have : p.map (algebraMap R (Localization.AtPrime p)) <= (I.map (algebraMap _ _)).radical := by
      rw [Ideal.radical_eq_sInf]; rw [le_sInf_iff]
      rintro q ⟨hq', hq⟩
      obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
      rw [Ideal.map_le_iff_le_comap] at hq' ⊢
      exact hp₃ ⟨h₁, hq'⟩ h₂
    obtain ⟨n, hn⟩ := this (Ideal.mem_map_of_mem _ hxp)
    rw [IsLocalization.mem_map_algebraMap_iff (M := p.primeCompl)] at hn
    obtain ⟨⟨a, b⟩, hn⟩ := hn
    rw [← map_pow]; rw [← map_mul]; rw [IsLocalization.eq_iff_exists p.primeCompl] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨t * b, fun h => (t * b).2 (hp₁.radical_le_iff.mpr hp₂ h), n + 1, ?_⟩
    simp only at ht
    have : (x * (t.1 * b.1)) ^ (n + 1) = (t.1 ^ n * b.1 ^ n * x * t.1) * a := by
      rw [mul_assoc]; rw [← ht]; ring
    rw [this]
    exact I.mul_mem_left _ a.2
  · rintro ⟨y, hy, hx⟩
    obtain ⟨p, hp, hyp⟩ : exists p in I.minimalPrimes, y ∉ p := by
      simpa [← Ideal.sInf_minimalPrimes] using hy
    refine ⟨p, hp, (hp.isPrime.mem_or_mem ?_).resolve_right hyp⟩
    exact hp.isPrime.radical_le_iff.mpr hp.le hx

/--
theorem `Ideal.exists_mul_mem_of_mem_minimalPrimes` / 定理 `Ideal.exists_mul_mem_of_mem_minimalPrimes`

English:
theorem Ideal.exists_mul_mem_of_mem_minimalPrimes
  proof: by
  classical
  obtain ⟨y, hy, n, hx⟩ := Ideal.iUnion_minimalPrimes.subset (Set.mem_biUnion hp hx)
  have H : exists m, x ^ m * y ^ n in I := ⟨n, mul_pow x y n ▸ hx⟩
  have : Nat.find H != 0 :=
    fun h => hy ⟨n, by simpa only [h, pow_zero, one_mul] using Nat.find_spec H⟩
  refine ⟨x ^ (Nat.find H - 1) * y ^ n, Nat.find_min H (Nat.sub_one_lt this), ?_⟩
  rw [← mul_assoc]; rw [← pow_succ']; rw [tsub_add_cancel_of_le (Nat.one_le_iff_ne_zero.mpr this)]
  exact Nat.find_spec H

中文:
定理 理想.存在_mul_mem_of_mem_minimalPrimes
  证明: by
  classical
  obtain ⟨y, hy, n, hx⟩ := Ideal.iUnion_minimalPrimes.subset (Set.mem_biUnion hp hx)
  have H : exists m, x ^ m * y ^ n in I := ⟨n, mul_pow x y n ▸ hx⟩
  have : Nat.find H != 0 :=
    fun h => hy ⟨n, by simpa only [h, pow_zero, one_mul] using Nat.find_spec H⟩
  refine ⟨x ^ (Nat.find H - 1) * y ^ n, Nat.find_min H (Nat.sub_one_lt this), ?_⟩
  rw [← mul_assoc]; rw [← pow_succ']; rw [tsub_add_cancel_of_le (Nat.one_le_iff_ne_zero.mpr this)]
  exact Nat.find_spec H

Depends on / 依赖: Ideal.iUnion_minimalPrimes.subset, Nat.find, Nat.find_min, Nat.find_spec, Nat.one_le_iff_ne_zero.mpr, Nat.sub_one_lt, Set.mem_biUnion, classical, find_min, find_spec, iUnion_minimalPrimes, mem_biUnion, mul_assoc, mul_pow, one_le_iff_ne_zero, one_mul, pow_succ, pow_zero, sub_one_lt, subset
-/
theorem Ideal.exists_mul_mem_of_mem_minimalPrimes
    {p : Ideal R} (hp : p in I.minimalPrimes) {x : R} (hx : x in p) :
    exists y ∉ I, x * y in I := by
  classical
  obtain ⟨y, hy, n, hx⟩ := Ideal.iUnion_minimalPrimes.subset (Set.mem_biUnion hp hx)
  have H : exists m, x ^ m * y ^ n in I := ⟨n, mul_pow x y n ▸ hx⟩
  have : Nat.find H != 0 :=
    fun h => hy ⟨n, by simpa only [h, pow_zero, one_mul] using Nat.find_spec H⟩
  refine ⟨x ^ (Nat.find H - 1) * y ^ n, Nat.find_min H (Nat.sub_one_lt this), ?_⟩
  rw [← mul_assoc]; rw [← pow_succ']; rw [tsub_add_cancel_of_le (Nat.one_le_iff_ne_zero.mpr this)]
  exact Nat.find_spec H

/--
theorem `IsSMulRegular.notMem_of_mem_minimalPrimes` / 定理 `IsSMulRegular.notMem_of_mem_minimalPrimes`

English:
theorem IsSMulRegular.notMem_of_mem_minimalPrimes
  proof: by
  intro hx
  rcases Ideal.exists_mul_mem_of_mem_minimalPrimes hp hx with ⟨y, hy, hxy⟩
  rcases not_forall.mp (Module.mem_annihilator.not.mp hy) with ⟨m, hm⟩
  exact hm (reg.right_eq_zero_of_smul ((smul_smul x y m).trans (Module.mem_annihilator.mp hxy m)))

中文:
定理 IsSMulRegular.notMem_of_mem_minimalPrimes
  证明: by
  intro hx
  rcases Ideal.exists_mul_mem_of_mem_minimalPrimes hp hx with ⟨y, hy, hxy⟩
  rcases not_forall.mp (Module.mem_annihilator.not.mp hy) with ⟨m, hm⟩
  exact hm (reg.right_eq_zero_of_smul ((smul_smul x y m).trans (Module.mem_annihilator.mp hxy m)))

Depends on / 依赖: Ideal.exists_mul_mem_of_mem_minimalPrimes, Module, Module.mem_annihilator.mp, Module.mem_annihilator.not.mp, exists_mul_mem_of_mem_minimalPrimes, mem_annihilator, not_forall, not_forall.mp, reg.right_eq_zero_of_smul, right_eq_zero_of_smul, smul_smul
-/
theorem IsSMulRegular.notMem_of_mem_minimalPrimes
    {M : Type*} [AddCommMonoid M] [Module R M] {x : R} (reg : IsSMulRegular M x)
    {p : Ideal R} (hp : p in (Module.annihilator R M).minimalPrimes) : x ∉ p := by
  intro hx
  rcases Ideal.exists_mul_mem_of_mem_minimalPrimes hp hx with ⟨y, hy, hxy⟩
  rcases not_forall.mp (Module.mem_annihilator.not.mp hy) with ⟨m, hm⟩
  exact hm (reg.right_eq_zero_of_smul ((smul_smul x y m).trans (Module.mem_annihilator.mp hxy m)))

/--
lemma `Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes` / 引理 `Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes`

English:
lemma Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes
  given: {p : Ideal R} (hp : p in minimalPrimes R)
  proof: by
  simp_rw [Set.disjoint_left, SetLike.mem_coe, mem_nonZeroDivisors_iff_right, not_forall,
    exists_prop, @and_comm (_ * _ = _), ← mul_comm]
  exact fun _ => Ideal.exists_mul_mem_of_mem_minimalPrimes hp

中文:
引理 理想.disjoint_nonZeroDivisors_of_mem_minimalPrimes
  条件: {p : 理想 R} (hp : p in minimalPrimes R)
  证明: by
  simp_rw [Set.disjoint_left, SetLike.mem_coe, mem_nonZeroDivisors_iff_right, not_forall,
    exists_prop, @and_comm (_ * _ = _), ← mul_comm]
  exact fun _ => Ideal.exists_mul_mem_of_mem_minimalPrimes hp

Depends on / 依赖: Ideal.exists_mul_mem_of_mem_minimalPrimes, Set.disjoint_left, SetLike, SetLike.mem_coe, and_comm, disjoint_left, exists_mul_mem_of_mem_minimalPrimes, exists_prop, mem_coe, mem_nonZeroDivisors_iff_right, mul_comm, not_forall, simp_rw
-/
lemma Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes {p : Ideal R} (hp : p in minimalPrimes R) :
    Disjoint (p : Set R) (nonZeroDivisors R) := by
  simp_rw [Set.disjoint_left, SetLike.mem_coe, mem_nonZeroDivisors_iff_right, not_forall,
    exists_prop, @and_comm (_ * _ = _), ← mul_comm]
  exact fun _ => Ideal.exists_mul_mem_of_mem_minimalPrimes hp

/--
lemma `notMem_nonZeroDivisors_of_mem_mem_minimalPrimes` / 引理 `notMem_nonZeroDivisors_of_mem_mem_minimalPrimes`

English:
lemma notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
  proof: Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) hx

中文:
引理 notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
  证明: Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) hx

Depends on / 依赖: Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes, Set.disjoint_left.mp, disjoint_left, disjoint_nonZeroDivisors_of_mem_minimalPrimes
-/
lemma notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    {x : R} {q : Ideal R} (hx : x in q) (hq : q in minimalPrimes R) :
    x ∉ nonZeroDivisors R :=
  Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) hx

/--
theorem `Ideal.exists_comap_eq_of_mem_minimalPrimes` / 定理 `Ideal.exists_comap_eq_of_mem_minimalPrimes`

English:
theorem Ideal.exists_comap_eq_of_mem_minimalPrimes
  statement: {I : Ideal S} (f : R ->+* S) (p)
  proof: have := H.isPrime
  have ⟨p', hIp', hp', le⟩ := exists_ideal_comap_le_prime p I H.le
  ⟨p', hp', hIp', le.antisymm (H.2 ⟨inferInstance, comap_mono hIp'⟩ le)⟩

中文:
定理 理想.存在_comap_eq_of_mem_minimalPrimes
  结论: {I : 理想 S} (f : R ->+* S) (p)
  证明: have := H.isPrime
  have ⟨p', hIp', hp', le⟩ := exists_ideal_comap_le_prime p I H.le
  ⟨p', hp', hIp', le.antisymm (H.2 ⟨inferInstance, comap_mono hIp'⟩ le)⟩

Depends on / 依赖: H.isPrime, H.le, antisymm, comap_mono, exists_ideal_comap_le_prime, isPrime, le.antisymm
-/
theorem Ideal.exists_comap_eq_of_mem_minimalPrimes {I : Ideal S} (f : R ->+* S) (p)
    (H : p in (I.comap f).minimalPrimes) : exists p' : Ideal S, p'.IsPrime ∧ I <= p' ∧ p'.comap f = p :=
  have := H.isPrime
  have ⟨p', hIp', hp', le⟩ := exists_ideal_comap_le_prime p I H.le
  ⟨p', hp', hIp', le.antisymm (H.2 ⟨inferInstance, comap_mono hIp'⟩ le)⟩

/--
theorem `Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective` / 定理 `Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`

English:
theorem Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
  statement: {f : R ->+* S}
  proof: have ⟨p', hp', _, eq⟩ := exists_comap_eq_of_mem_minimalPrimes f (I := ⊥) p by
    rwa [comap_bot_of_injective f hf]
  ⟨p', hp', eq⟩

中文:
定理 理想.存在_comap_eq_of_mem_minimalPrimes_of_injective
  结论: {f : R ->+* S}
  证明: have ⟨p', hp', _, eq⟩ := exists_comap_eq_of_mem_minimalPrimes f (I := ⊥) p by
    rwa [comap_bot_of_injective f hf]
  ⟨p', hp', eq⟩
-/
@[stacks 00FK] theorem Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective {f : R ->+* S}
    (hf : Function.Injective f) (p) (H : p in minimalPrimes R) :
    exists p' : Ideal S, p'.IsPrime ∧ p'.comap f = p :=
have ⟨p', hp', _, eq⟩ := exists_comap_eq_of_mem_minimalPrimes f (I := ⊥) p by
    rwa [comap_bot_of_injective f hf]
  ⟨p', hp', eq⟩

/--
theorem `Ideal.exists_minimalPrimes_comap_eq` / 定理 `Ideal.exists_minimalPrimes_comap_eq`

English:
theorem Ideal.exists_minimalPrimes_comap_eq
  statement: {I : Ideal S} (f : R ->+* S) (p)
  proof: by
  obtain ⟨p', h₁, h₂, h₃⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f p H
  obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le h₂
  refine ⟨q, hq, Eq.symm ?_⟩
  have := hq.isPrime
  have := (Ideal.comap_mono hq').trans_eq h₃
  exact (H.2 ⟨inferInstance, Ideal.comap_mono hq.le⟩ this).antisymm this

中文:
定理 理想.存在_minimalPrimes_comap_eq
  结论: {I : 理想 S} (f : R ->+* S) (p)
  证明: by
  obtain ⟨p', h₁, h₂, h₃⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f p H
  obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le h₂
  refine ⟨q, hq, Eq.symm ?_⟩
  have := hq.isPrime
  have := (Ideal.comap_mono hq').trans_eq h₃
  exact (H.2 ⟨inferInstance, Ideal.comap_mono hq.le⟩ this).antisymm this

Depends on / 依赖: Eq.symm, Ideal.comap_mono, Ideal.exists_comap_eq_of_mem_minimalPrimes, Ideal.exists_minimalPrimes_le, antisymm, comap_mono, exists_comap_eq_of_mem_minimalPrimes, exists_minimalPrimes_le, hq.isPrime, hq.le, isPrime, trans_eq
-/
theorem Ideal.exists_minimalPrimes_comap_eq {I : Ideal S} (f : R ->+* S) (p)
    (H : p in (I.comap f).minimalPrimes) : exists p' in I.minimalPrimes, Ideal.comap f p' = p := by
  obtain ⟨p', h₁, h₂, h₃⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f p H
  obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le h₂
  refine ⟨q, hq, Eq.symm ?_⟩
  have := hq.isPrime
  have := (Ideal.comap_mono hq').trans_eq h₃
  exact (H.2 ⟨inferInstance, Ideal.comap_mono hq.le⟩ this).antisymm this

/--
theorem `Ideal.minimalPrimes_comap_subset` / 定理 `Ideal.minimalPrimes_comap_subset`

English:
theorem Ideal.minimalPrimes_comap_subset
  given: (f : R ->+* S) (J : Ideal S)
  proof: fun p hp => Ideal.exists_minimalPrimes_comap_eq f p hp

中文:
定理 理想.minimalPrimes_comap_subset
  条件: (f : R ->+* S) (J : 理想 S)
  证明: fun p hp => Ideal.exists_minimalPrimes_comap_eq f p hp

Depends on / 依赖: Ideal.exists_minimalPrimes_comap_eq, exists_minimalPrimes_comap_eq
-/
theorem Ideal.minimalPrimes_comap_subset (f : R ->+* S) (J : Ideal S) :
    (J.comap f).minimalPrimes subseteq Ideal.comap f '' J.minimalPrimes :=
  fun p hp => Ideal.exists_minimalPrimes_comap_eq f p hp

end

section

variable {R S : Type*} [CommRing R] [CommRing S] {I J : Ideal R}

/--
theorem `Ideal.minimalPrimes_comap_of_surjective` / 定理 `Ideal.minimalPrimes_comap_of_surjective`

English:
theorem Ideal.minimalPrimes_comap_of_surjective
  statement: {f : R ->+* S} (hf : Function.Surjective f)
  proof: by
  have := h.isPrime
  refine ⟨⟨inferInstance, Ideal.comap_mono h.le⟩, ?_⟩
  rintro K ⟨hK, e₁⟩ e₂
  have : RingHom.ker f <= K := (Ideal.comap_mono bot_le).trans e₁
  rw [← sup_eq_left.mpr this]; rw [RingHom.ker_eq_comap_bot]; rw [← Ideal.comap_map_of_surjective f hf]
  apply Ideal.comap_mono _
  apply h.2 _ _
  · exact ⟨Ideal.map_isPrime_of_surjective hf this, Ideal.le_map_of_comap_le_of_surjective f hf e₁⟩
  · exact Ideal.map_le_of_le_comap e₂

@[deprecated (since := "2026-04-01")] alias Ideal.minimal_primes_comap_of_surjective :=
    Ideal.minimalPrimes_comap_of_surjective

中文:
定理 理想.minimalPrimes_comap_of_surjective
  结论: {f : R ->+* S} (hf : 函数.满射 f)
  证明: by
  have := h.isPrime
  refine ⟨⟨inferInstance, Ideal.comap_mono h.le⟩, ?_⟩
  rintro K ⟨hK, e₁⟩ e₂
  have : RingHom.ker f <= K := (Ideal.comap_mono bot_le).trans e₁
  rw [← sup_eq_left.mpr this]; rw [RingHom.ker_eq_comap_bot]; rw [← Ideal.comap_map_of_surjective f hf]
  apply Ideal.comap_mono _
  apply h.2 _ _
  · exact ⟨Ideal.map_isPrime_of_surjective hf this, Ideal.le_map_of_comap_le_of_surjective f hf e₁⟩
  · exact Ideal.map_le_of_le_comap e₂

@[deprecated (since := "2026-04-01")] alias Ideal.minimal_primes_comap_of_surjective :=
    Ideal.minimalPrimes_comap_of_surjective

Depends on / 依赖: Ideal.comap_map_of_surjective, Ideal.comap_mono, Ideal.le_map_of_comap_le_of_surjective, Ideal.map_isPrime_of_surjective, Ideal.map_le_of_le_comap, RingHom, RingHom.ker, RingHom.ker_eq_comap_bot, bot_le, comap_map_of_surjective, comap_mono, h.isPrime, h.le, isPrime, ker_eq_comap_bot, le_map_of_comap_le_of_surjective, map_isPrime_of_surjective, map_le_of_le_comap, sup_eq_left, sup_eq_left.mpr
-/
theorem Ideal.minimalPrimes_comap_of_surjective {f : R ->+* S} (hf : Function.Surjective f)
    {I J : Ideal S} (h : J in I.minimalPrimes) : J.comap f in (I.comap f).minimalPrimes := by
  have := h.isPrime
  refine ⟨⟨inferInstance, Ideal.comap_mono h.le⟩, ?_⟩
  rintro K ⟨hK, e₁⟩ e₂
  have : RingHom.ker f <= K := (Ideal.comap_mono bot_le).trans e₁
  rw [← sup_eq_left.mpr this]; rw [RingHom.ker_eq_comap_bot]; rw [← Ideal.comap_map_of_surjective f hf]
  apply Ideal.comap_mono _
  apply h.2 _ _
  · exact ⟨Ideal.map_isPrime_of_surjective hf this, Ideal.le_map_of_comap_le_of_surjective f hf e₁⟩
  · exact Ideal.map_le_of_le_comap e₂

@[deprecated (since := "2026-04-01")] alias Ideal.minimal_primes_comap_of_surjective :=
    Ideal.minimalPrimes_comap_of_surjective

/--
theorem `Ideal.comap_minimalPrimes_eq_of_surjective` / 定理 `Ideal.comap_minimalPrimes_eq_of_surjective`

English:
theorem Ideal.comap_minimalPrimes_eq_of_surjective
  statement: {f : R ->+* S} (hf : Function.Surjective f)
  proof: by
  ext J
  constructor
  · intro H
    obtain ⟨p, h, rfl⟩ := Ideal.exists_minimalPrimes_comap_eq f J H
    exact ⟨p, h, rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    exact Ideal.minimalPrimes_comap_of_surjective hf hJ

中文:
定理 理想.comap_minimalPrimes_eq_of_surjective
  结论: {f : R ->+* S} (hf : 函数.满射 f)
  证明: by
  ext J
  constructor
  · intro H
    obtain ⟨p, h, rfl⟩ := Ideal.exists_minimalPrimes_comap_eq f J H
    exact ⟨p, h, rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    exact Ideal.minimalPrimes_comap_of_surjective hf hJ

Depends on / 依赖: Ideal.exists_minimalPrimes_comap_eq, Ideal.minimalPrimes_comap_of_surjective, exists_minimalPrimes_comap_eq, minimalPrimes_comap_of_surjective
-/
theorem Ideal.comap_minimalPrimes_eq_of_surjective {f : R ->+* S} (hf : Function.Surjective f)
    (I : Ideal S) : (I.comap f).minimalPrimes = Ideal.comap f '' I.minimalPrimes := by
  ext J
  constructor
  · intro H
    obtain ⟨p, h, rfl⟩ := Ideal.exists_minimalPrimes_comap_eq f J H
    exact ⟨p, h, rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    exact Ideal.minimalPrimes_comap_of_surjective hf hJ

/--
lemma `Ideal.minimalPrimes_map_of_surjective` / 引理 `Ideal.minimalPrimes_map_of_surjective`

English:
lemma Ideal.minimalPrimes_map_of_surjective
  statement: {S : Type*} [CommRing S] {f : R ->+* S}
  proof: by
  apply Set.image_injective.mpr (Ideal.comap_injective_of_surjective f hf)
  rw [← Ideal.comap_minimalPrimes_eq_of_surjective hf]; rw [← Set.image_comp]; rw [Ideal.comap_map_of_surjective f hf]; rw [Set.image_congr]; rw [Set.image_id]; rw [RingHom.ker]
  intro x hx
  exact (Ideal.comap_map_of_surjective f hf _).trans (sup_eq_left.mpr <| le_sup_right.trans hx.le)

中文:
引理 理想.minimalPrimes_map_of_surjective
  结论: {S : 类型} [交换环 S] {f : R ->+* S}
  证明: by
  apply Set.image_injective.mpr (Ideal.comap_injective_of_surjective f hf)
  rw [← Ideal.comap_minimalPrimes_eq_of_surjective hf]; rw [← Set.image_comp]; rw [Ideal.comap_map_of_surjective f hf]; rw [Set.image_congr]; rw [Set.image_id]; rw [RingHom.ker]
  intro x hx
  exact (Ideal.comap_map_of_surjective f hf _).trans (sup_eq_left.mpr <| le_sup_right.trans hx.le)

Depends on / 依赖: Ideal.comap_injective_of_surjective, Ideal.comap_map_of_surjective, Ideal.comap_minimalPrimes_eq_of_surjective, RingHom, RingHom.ker, Set.image_comp, Set.image_congr, Set.image_id, Set.image_injective.mpr, comap_injective_of_surjective, comap_map_of_surjective, comap_minimalPrimes_eq_of_surjective, hx.le, image_comp, image_congr, image_id, image_injective, le_sup_right, le_sup_right.trans, sup_eq_left
-/
lemma Ideal.minimalPrimes_map_of_surjective {S : Type*} [CommRing S] {f : R ->+* S}
    (hf : Function.Surjective f) (I : Ideal R) :
    (I.map f).minimalPrimes = Ideal.map f '' (I ⊔ (RingHom.ker f)).minimalPrimes := by
  apply Set.image_injective.mpr (Ideal.comap_injective_of_surjective f hf)
  rw [← Ideal.comap_minimalPrimes_eq_of_surjective hf]; rw [← Set.image_comp]; rw [Ideal.comap_map_of_surjective f hf]; rw [Set.image_congr]; rw [Set.image_id]; rw [RingHom.ker]
  intro x hx
  exact (Ideal.comap_map_of_surjective f hf _).trans (sup_eq_left.mpr <| le_sup_right.trans hx.le)

/--
theorem `Ideal.minimalPrimes_eq_comap` / 定理 `Ideal.minimalPrimes_eq_comap`

English:
theorem Ideal.minimalPrimes_eq_comap
  proof: by
  rw [minimalPrimes]; rw [← Ideal.comap_minimalPrimes_eq_of_surjective Ideal.Quotient.mk_surjective]; rw [← RingHom.ker_eq_comap_bot]; rw [Ideal.mk_ker]

中文:
定理 理想.minimalPrimes_eq_comap
  证明: by
  rw [minimalPrimes]; rw [← Ideal.comap_minimalPrimes_eq_of_surjective Ideal.Quotient.mk_surjective]; rw [← RingHom.ker_eq_comap_bot]; rw [Ideal.mk_ker]

Depends on / 依赖: Ideal.Quotient.mk_surjective, Ideal.comap_minimalPrimes_eq_of_surjective, Ideal.mk_ker, Quotient, RingHom, RingHom.ker_eq_comap_bot, comap_minimalPrimes_eq_of_surjective, ker_eq_comap_bot, minimalPrimes, mk_ker, mk_surjective
-/
theorem Ideal.minimalPrimes_eq_comap :
    I.minimalPrimes = Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I) := by
  rw [minimalPrimes]; rw [← Ideal.comap_minimalPrimes_eq_of_surjective Ideal.Quotient.mk_surjective]; rw [← RingHom.ker_eq_comap_bot]; rw [Ideal.mk_ker]

end

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A]

/--
theorem `IsLocalization.minimalPrimes_map` / 定理 `IsLocalization.minimalPrimes_map`

English:
theorem IsLocalization.minimalPrimes_map
  given: [IsLocalization S A] (J : Ideal R)
  proof: by
  ext p
  constructor
  · intro hp
    have := hp.isPrime
    refine ⟨⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hp.le⟩, ?_⟩
    rintro I hI e
    have hI' : Disjoint (S : Set R) I := Set.disjoint_of_subset_right e
      ((IsLocalization.isPrime_iff_isPrime_disjoint S A _).mp hp.isPrime).2
    refine (Ideal.comap_mono <|
      hp.2 ⟨?_, Ideal.map_mono hI.2⟩ (Ideal.map_le_iff_le_comap.mpr e)).trans_eq ?_
    · exact IsLocalization.isPrime_of_isPrime_disjoint S A I hI.1 hI'
    · exact IsLocalization.under_map_of_isPrime_disjoint S A hI.1 hI'
  · intro hp
    refine ⟨⟨?_, Ideal.map_le_iff_le_comap.mpr hp.le⟩, ?_⟩
    · rw [IsLocalization.isPrime_iff_isPrime_disjoint S A, IsLocalization.disjoint_under_iff S]
      refine ⟨hp.isPrime, ?_⟩
      rintro rfl
      exact hp.isPrime.ne_top rfl
    · intro I hI e
      rw [← IsLocalization.map_under S A I]; rw [← IsLocalization.map_under S A p]
      exact Ideal.map_mono (hp.2 ⟨hI.1.comap _, Ideal.map_le_iff_le_comap.mp hI.2⟩
        (Ideal.comap_mono e))

中文:
定理 是Localization.minimalPrimes_map
  条件: [是Localization S A] (J : 理想 R)
  证明: by
  ext p
  constructor
  · intro hp
    have := hp.isPrime
    refine ⟨⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hp.le⟩, ?_⟩
    rintro I hI e
    have hI' : Disjoint (S : Set R) I := Set.disjoint_of_subset_right e
      ((IsLocalization.isPrime_iff_isPrime_disjoint S A _).mp hp.isPrime).2
    refine (Ideal.comap_mono <|
      hp.2 ⟨?_, Ideal.map_mono hI.2⟩ (Ideal.map_le_iff_le_comap.mpr e)).trans_eq ?_
    · exact IsLocalization.isPrime_of_isPrime_disjoint S A I hI.1 hI'
    · exact IsLocalization.under_map_of_isPrime_disjoint S A hI.1 hI'
  · intro hp
    refine ⟨⟨?_, Ideal.map_le_iff_le_comap.mpr hp.le⟩, ?_⟩
    · rw [IsLocalization.isPrime_iff_isPrime_disjoint S A, IsLocalization.disjoint_under_iff S]
      refine ⟨hp.isPrime, ?_⟩
      rintro rfl
      exact hp.isPrime.ne_top rfl
    · intro I hI e
      rw [← IsLocalization.map_under S A I]; rw [← IsLocalization.map_under S A p]
      exact Ideal.map_mono (hp.2 ⟨hI.1.comap _, Ideal.map_le_iff_le_comap.mp hI.2⟩
        (Ideal.comap_mono e))

Depends on / 依赖: Disjoint, Ideal.IsPrime.comap, Ideal.comap_mono, Ideal.map_le_iff_le_comap.mp, Ideal.map_le_iff_le_comap.mpr, Ideal.map_mono, IsLocalization, IsLocalization.isPrime_iff_isPrime_disjoint, IsLocalization.isPrime_of_isPrime_disjoint, IsLocalization.under_map_of_isPrime_disjoint, IsPrime, Set.disjoint_of_subset_right, comap_mono, disjoint_of_subset_right, hp.isPrime, hp.le, isPrime, isPrime_iff_isPrime_disjoint, isPrime_of_isPrime_disjoint, map_le_iff_le_comap
-/
theorem IsLocalization.minimalPrimes_map [IsLocalization S A] (J : Ideal R) :
    (J.map (algebraMap R A)).minimalPrimes = Ideal.under R ⁻¹' J.minimalPrimes := by
  ext p
  constructor
  · intro hp
    have := hp.isPrime
    refine ⟨⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hp.le⟩, ?_⟩
    rintro I hI e
    have hI' : Disjoint (S : Set R) I := Set.disjoint_of_subset_right e
      ((IsLocalization.isPrime_iff_isPrime_disjoint S A _).mp hp.isPrime).2
    refine (Ideal.comap_mono <|
      hp.2 ⟨?_, Ideal.map_mono hI.2⟩ (Ideal.map_le_iff_le_comap.mpr e)).trans_eq ?_
    · exact IsLocalization.isPrime_of_isPrime_disjoint S A I hI.1 hI'
    · exact IsLocalization.under_map_of_isPrime_disjoint S A hI.1 hI'
  · intro hp
    refine ⟨⟨?_, Ideal.map_le_iff_le_comap.mpr hp.le⟩, ?_⟩
    · rw [IsLocalization.isPrime_iff_isPrime_disjoint S A, IsLocalization.disjoint_under_iff S]
      refine ⟨hp.isPrime, ?_⟩
      rintro rfl
      exact hp.isPrime.ne_top rfl
    · intro I hI e
      rw [← IsLocalization.map_under S A I]; rw [← IsLocalization.map_under S A p]
      exact Ideal.map_mono (hp.2 ⟨hI.1.comap _, Ideal.map_le_iff_le_comap.mp hI.2⟩
        (Ideal.comap_mono e))

/--
theorem `IsLocalization.minimalPrimes_comap` / 定理 `IsLocalization.minimalPrimes_comap`

English:
theorem IsLocalization.minimalPrimes_comap
  given: [IsLocalization S A] (J : Ideal A)
  proof: by
  conv_rhs => rw [← map_under S A J, minimalPrimes_map S]
  refine (Set.image_preimage_eq_iff.mpr ?_).symm
  exact subset_trans (Ideal.minimalPrimes_comap_subset (algebraMap R A) J) (by simp)

中文:
定理 是Localization.minimalPrimes_comap
  条件: [是Localization S A] (J : 理想 A)
  证明: by
  conv_rhs => rw [← map_under S A J, minimalPrimes_map S]
  refine (Set.image_preimage_eq_iff.mpr ?_).symm
  exact subset_trans (Ideal.minimalPrimes_comap_subset (algebraMap R A) J) (by simp)

Depends on / 依赖: Ideal.minimalPrimes_comap_subset, Set.image_preimage_eq_iff.mpr, algebraMap, conv_rhs, image_preimage_eq_iff, map_under, minimalPrimes_comap_subset, minimalPrimes_map, subset_trans
-/
theorem IsLocalization.minimalPrimes_comap [IsLocalization S A] (J : Ideal A) :
    (J.comap (algebraMap R A)).minimalPrimes = Ideal.comap (algebraMap R A) '' J.minimalPrimes := by
  conv_rhs => rw [← map_under S A J, minimalPrimes_map S]
  refine (Set.image_preimage_eq_iff.mpr ?_).symm
  exact subset_trans (Ideal.minimalPrimes_comap_subset (algebraMap R A) J) (by simp)

/--
theorem `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes` / 定理 `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`

English:
theorem IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
  proof: by
  have : IsLocalRing A := AtPrime.isLocalRing A q
  rw [← Ideal.sInf_minimalPrimes]; rw [IsLocalization.minimalPrimes_map q.primeCompl A I]
  refine le_antisymm (sInf_le ?_) (le_sInf fun J hJ => ?_)
  · rwa [Set.mem_preimage, map_eq_maximalIdeal q A, under_maximalIdeal A q]
  · rw [← IsLocalization.under_le_under_iff q.primeCompl A,
      AtPrime.map_eq_maximalIdeal q A, AtPrime.under_maximalIdeal A q]
    apply hIq.2 hJ.1
    have := hJ.isPrime.ne_top
    rw [ne_eq]; rw [Ideal.comap_eq_top_iff]; rw [← ne_eq]; rw [← disjoint_under_iff q.primeCompl A J] at this
    exact Set.disjoint_compl_left_iff_subset.mp this

中文:
定理 是Localization.AtPrime.radical_map_of_mem_minimalPrimes
  证明: by
  have : IsLocalRing A := AtPrime.isLocalRing A q
  rw [← Ideal.sInf_minimalPrimes]; rw [IsLocalization.minimalPrimes_map q.primeCompl A I]
  refine le_antisymm (sInf_le ?_) (le_sInf fun J hJ => ?_)
  · rwa [Set.mem_preimage, map_eq_maximalIdeal q A, under_maximalIdeal A q]
  · rw [← IsLocalization.under_le_under_iff q.primeCompl A,
      AtPrime.map_eq_maximalIdeal q A, AtPrime.under_maximalIdeal A q]
    apply hIq.2 hJ.1
    have := hJ.isPrime.ne_top
    rw [ne_eq]; rw [Ideal.comap_eq_top_iff]; rw [← ne_eq]; rw [← disjoint_under_iff q.primeCompl A J] at this
    exact Set.disjoint_compl_left_iff_subset.mp this

Depends on / 依赖: AtPrime, AtPrime.isLocalRing, AtPrime.map_eq_maximalIdeal, AtPrime.under_maximalIdeal, Ideal.comap_eq_top_iff, Ideal.sInf_minimalPrimes, IsLocalRing, IsLocalization, IsLocalization.minimalPrimes_map, IsLocalization.under_le_under_iff, Set.mem_preimage, comap_eq_top_iff, hJ.isPrime.ne_top, isLocalRing, isPrime, le_antisymm, le_sInf, map_eq_maximalIdeal, mem_preimage, minimalPrimes_map
-/
theorem IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (q : Ideal R) [hqp : q.IsPrime] [IsLocalization.AtPrime A q]
    (I : Ideal R) (hIq : q in I.minimalPrimes) :
    (I.map (algebraMap R A)).radical = q.map (algebraMap R A) := by
  have : IsLocalRing A := AtPrime.isLocalRing A q
  rw [← Ideal.sInf_minimalPrimes]; rw [IsLocalization.minimalPrimes_map q.primeCompl A I]
  refine le_antisymm (sInf_le ?_) (le_sInf fun J hJ => ?_)
  · rwa [Set.mem_preimage, map_eq_maximalIdeal q A, under_maximalIdeal A q]
  · rw [← IsLocalization.under_le_under_iff q.primeCompl A,
      AtPrime.map_eq_maximalIdeal q A, AtPrime.under_maximalIdeal A q]
    apply hIq.2 hJ.1
    have := hJ.isPrime.ne_top
    rw [ne_eq]; rw [Ideal.comap_eq_top_iff]; rw [← ne_eq]; rw [← disjoint_under_iff q.primeCompl A J] at this
    exact Set.disjoint_compl_left_iff_subset.mp this

end
