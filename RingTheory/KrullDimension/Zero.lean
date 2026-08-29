/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# Zero-dimensional rings

We provide further API for zero-dimensional rings.
Basic definitions and lemmas are provided in `Mathlib/RingTheory/KrullDimension/Basic.lean`.

-/

public section

section CommSemiring

variable {R : Type*} [CommSemiring R] [Ring.KrullDimLE 0 R] (I : Ideal R)

/--
lemma `Ring.KrullDimLE.mem_minimalPrimes_iff` / 引理 `Ring.KrullDimLE.mem_minimalPrimes_iff`

English:
lemma Ring.KrullDimLE.mem_minimalPrimes_iff
  given: {I J : Ideal R}
  proof: ⟨fun H => H.1, fun H => ⟨H, fun _ h e => (h.1.isMaximal'.eq_of_le H.1.ne_top e).ge⟩⟩

中文:
引理 环.Krull维数不超过.mem_minimalPrimes_iff
  条件: {I J : 理想 R}
  证明: ⟨fun H => H.1, fun H => ⟨H, fun _ h e => (h.1.isMaximal'.eq_of_le H.1.ne_top e).ge⟩⟩

Depends on / 依赖: eq_of_le, isMaximal, ne_top
-/
lemma Ring.KrullDimLE.mem_minimalPrimes_iff {I J : Ideal R} :
    I in J.minimalPrimes ↔ I.IsPrime ∧ J <= I :=
  ⟨fun H => H.1, fun H => ⟨H, fun _ h e => (h.1.isMaximal'.eq_of_le H.1.ne_top e).ge⟩⟩

/--
lemma `Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime` / 引理 `Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime`

English:
lemma Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime
  given: {I J : Ideal R} [I.IsPrime]
  proof: by
  rwa [mem_minimalPrimes_iff, and_iff_right]

中文:
引理 环.Krull维数不超过.mem_minimalPrimes_iff_le_of_isPrime
  条件: {I J : 理想 R} [I.是素]
  证明: by
  rwa [mem_minimalPrimes_iff, and_iff_right]

Depends on / 依赖: and_iff_right, mem_minimalPrimes_iff
-/
lemma Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime {I J : Ideal R} [I.IsPrime] :
    I in J.minimalPrimes ↔ J <= I := by
  rwa [mem_minimalPrimes_iff, and_iff_right]

variable (R) in
/--
lemma `Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime` / 引理 `Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime`

English:
lemma Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime
  proof: by
  ext
  exact Ideal.mem_minimalPrimes_iff_isPrime

@[deprecated (since := "2026-07-09")]
alias Ring.KrullDimLE.minimalPrimes_eq_setOf_isPrime :=
  Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime

中文:
引理 环.Krull维数不超过.minimalPrimes_eq_setOfPred_isPrime
  证明: by
  ext
  exact Ideal.mem_minimalPrimes_iff_isPrime

@[deprecated (since := "2026-07-09")]
alias Ring.KrullDimLE.minimalPrimes_eq_setOf_isPrime :=
  Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime

Depends on / 依赖: Ideal.mem_minimalPrimes_iff_isPrime, mem_minimalPrimes_iff_isPrime
-/
lemma Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime :
    minimalPrimes R = { I | I.IsPrime } := by
  ext
  exact Ideal.mem_minimalPrimes_iff_isPrime

@[deprecated (since := "2026-07-09")]
alias Ring.KrullDimLE.minimalPrimes_eq_setOf_isPrime :=
  Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime

variable (R) in
/--
lemma `Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal` / 引理 `Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal`

English:
lemma Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal
  proof: by
  ext; simp [minimalPrimes_eq_setOfPred_isPrime, Ideal.isMaximal_iff_isPrime]

@[deprecated (since := "2026-07-09")]
alias Ring.KrullDimLE.minimalPrimes_eq_setOf_isMaximal :=
  Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal

中文:
引理 环.Krull维数不超过.minimalPrimes_eq_setOfPred_isMaximal
  证明: by
  ext; simp [minimalPrimes_eq_setOfPred_isPrime, Ideal.isMaximal_iff_isPrime]

@[deprecated (since := "2026-07-09")]
alias Ring.KrullDimLE.minimalPrimes_eq_setOf_isMaximal :=
  Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal

Depends on / 依赖: Ideal.isMaximal_iff_isPrime, isMaximal_iff_isPrime, minimalPrimes_eq_setOfPred_isPrime
-/
lemma Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal :
    minimalPrimes R = { I | I.IsMaximal } := by
  ext; simp [minimalPrimes_eq_setOfPred_isPrime, Ideal.isMaximal_iff_isPrime]

@[deprecated (since := "2026-07-09")]
alias Ring.KrullDimLE.minimalPrimes_eq_setOf_isMaximal :=
  Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isMaximal

/-- Note that the `ringKrullDim` of the trivial ring is `⊥` and not `0`. -/
example [Subsingleton R] : Ring.KrullDimLE 0 R := inferInstance

/--
lemma `Ring.KrullDimLE.isField_of_isDomain` / 引理 `Ring.KrullDimLE.isField_of_isDomain`

English:
lemma Ring.KrullDimLE.isField_of_isDomain
  given: [IsDomain R]
  statement: IsField R
  proof: by
  by_contra h
  obtain ⟨p, hp, h⟩ := Ring.not_isField_iff_exists_prime.mp h
  exact hp.symm (Ideal.isPrime_bot.isMaximal'.eq_of_le h.ne_top bot_le)

omit [Ring.KrullDimLE 0 R] in

中文:
引理 环.Krull维数不超过.isField_of_isDomain
  条件: [是整环 R]
  结论: 是域 R
  证明: by
  by_contra h
  obtain ⟨p, hp, h⟩ := Ring.not_isField_iff_exists_prime.mp h
  exact hp.symm (Ideal.isPrime_bot.isMaximal'.eq_of_le h.ne_top bot_le)

omit [Ring.KrullDimLE 0 R] in

Depends on / 依赖: Ideal.isPrime_bot.isMaximal, Ring.not_isField_iff_exists_prime.mp, bot_le, eq_of_le, h.ne_top, hp.symm, isMaximal, isPrime_bot, ne_top, not_isField_iff_exists_prime
-/
lemma Ring.KrullDimLE.isField_of_isDomain [IsDomain R] : IsField R := by
  by_contra h
  obtain ⟨p, hp, h⟩ := Ring.not_isField_iff_exists_prime.mp h
  exact hp.symm (Ideal.isPrime_bot.isMaximal'.eq_of_le h.ne_top bot_le)

omit [Ring.KrullDimLE 0 R] in
/--
lemma `ringKrullDimZero_iff_ringKrullDim_eq_zero` / 引理 `ringKrullDimZero_iff_ringKrullDim_eq_zero`

English:
lemma ringKrullDimZero_iff_ringKrullDim_eq_zero
  given: [Nontrivial R]
  proof: by
  rw [Ring.KrullDimLE]; rw [Order.krullDimLE_iff]; rw [le_antisymm_iff]; rw [← ringKrullDim]; rw [Nat.cast_zero]; rw [iff_self_and]
  exact fun _ => ringKrullDim_nonneg_of_nontrivial

中文:
引理 ringKrullDimZero_iff_ringKrullDim_eq_zero
  条件: [非平凡 R]
  证明: by
  rw [Ring.KrullDimLE]; rw [Order.krullDimLE_iff]; rw [le_antisymm_iff]; rw [← ringKrullDim]; rw [Nat.cast_zero]; rw [iff_self_and]
  exact fun _ => ringKrullDim_nonneg_of_nontrivial

Depends on / 依赖: KrullDimLE, Nat.cast_zero, Order.krullDimLE_iff, Ring.KrullDimLE, cast_zero, iff_self_and, krullDimLE_iff, le_antisymm_iff, ringKrullDim, ringKrullDim_nonneg_of_nontrivial
-/
lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
    Ring.KrullDimLE 0 R ↔ ringKrullDim R = 0 := by
  rw [Ring.KrullDimLE]; rw [Order.krullDimLE_iff]; rw [le_antisymm_iff]; rw [← ringKrullDim]; rw [Nat.cast_zero]; rw [iff_self_and]
  exact fun _ => ringKrullDim_nonneg_of_nontrivial

/--
theorem `Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal` / 定理 `Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal`

English:
theorem Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal
  proof: by
  rw [Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal]; rw [minimalPrimes_eq_comap]; rw [Set.forall_mem_image]
  refine forall₂_congr fun J hJ => ⟨fun h => ?_, fun h => ?_⟩
  · exact comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective
  · have := map_eq_top_or_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective h
    rw [map_comap_of_surjective (Quotient.mk I) Quotient.mk_surjective] at this
    exact this.resolve_left hJ.1.1.ne_top

中文:
定理 理想.krullDimLE_zero_quotient_iff_对任意_minimalPrimes_isMaximal
  证明: by
  rw [Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal]; rw [minimalPrimes_eq_comap]; rw [Set.forall_mem_image]
  refine forall₂_congr fun J hJ => ⟨fun h => ?_, fun h => ?_⟩
  · exact comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective
  · have := map_eq_top_or_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective h
    rw [map_comap_of_surjective (Quotient.mk I) Quotient.mk_surjective] at this
    exact this.resolve_left hJ.1.1.ne_top

Depends on / 依赖: Quotient, Quotient.mk, Quotient.mk_surjective, Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal, Set.forall_mem_image, comap_isMaximal_of_surjective, forall_mem_image, krullDimLE_zero_iff_forall_minimalPrimes_isMaximal, map_comap_of_surjective, map_eq_top_or_isMaximal_of_surjective, minimalPrimes_eq_comap, mk_surjective, ne_top, resolve_left, this.resolve_left
-/
theorem Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal
    {R : Type*} [CommRing R] {I : Ideal R} :
    Ring.KrullDimLE 0 (R ⧸ I) ↔ forall J in I.minimalPrimes, J.IsMaximal := by
  rw [Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal]; rw [minimalPrimes_eq_comap]; rw [Set.forall_mem_image]
  refine forall₂_congr fun J hJ => ⟨fun h => ?_, fun h => ?_⟩
  · exact comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective
  · have := map_eq_top_or_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective h
    rw [map_comap_of_surjective (Quotient.mk I) Quotient.mk_surjective] at this
    exact this.resolve_left hJ.1.1.ne_top

section IsLocalRing

omit [Ring.KrullDimLE 0 R] in
variable (R) in
/--
lemma `Ring.krullDimLE_zero_and_isLocalRing_tfae` / 引理 `Ring.krullDimLE_zero_and_isLocalRing_tfae`

English:
lemma Ring.krullDimLE_zero_and_isLocalRing_tfae
  proof: by
  tfae_have 1 -> 3 := by
    intro ⟨h₁, h₂⟩ x
    change x in nilradical R ↔ x in IsLocalRing.maximalIdeal R
    rw [nilradical]; rw [Ideal.radical_eq_sInf]
    simp [← Ideal.isMaximal_iff_isPrime, IsLocalRing.isMaximal_iff]
  tfae_have 3 -> 4 := by
    refine fun H => ⟨fun e => ?_, fun I hI => ?_⟩
    · obtain ⟨n, hn⟩ := (Ideal.eq_top_iff_one _).mp e
      exact (H 0).mp .zero ((show (1 : R) = 0 by simpa using hn) ▸ isUnit_one)
    · obtain ⟨x, hx, hx'⟩ := (SetLike.lt_iff_le_and_exists.mp hI).2
      exact Ideal.eq_top_of_isUnit_mem _ hx (not_not.mp ((H x).not.mp hx'))
  tfae_have 4 -> 2 := fun H => ⟨_, H.isPrime, fun p (hp : p.IsPrime) =>
      (H.eq_of_le hp.ne_top (nilradical_le_prime p)).symm⟩
  tfae_have 2 -> 1 := by
    rintro ⟨P, hP₁, hP₂⟩
    obtain ⟨P, hP₃, -⟩ := P.exists_le_maximal hP₁.ne_top
    obtain rfl := hP₂ P hP₃.isPrime
    exact ⟨.mk₀ fun Q h => hP₂ Q h ▸ hP₃, .of_unique_max_ideal ⟨P, hP₃, fun Q h => hP₂ Q h.isPrime⟩⟩
  tfae_finish

@[simp]

中文:
引理 环.krullDimLE_zero_and_isLocalRing_tfae
  证明: by
  tfae_have 1 -> 3 := by
    intro ⟨h₁, h₂⟩ x
    change x in nilradical R ↔ x in IsLocalRing.maximalIdeal R
    rw [nilradical]; rw [Ideal.radical_eq_sInf]
    simp [← Ideal.isMaximal_iff_isPrime, IsLocalRing.isMaximal_iff]
  tfae_have 3 -> 4 := by
    refine fun H => ⟨fun e => ?_, fun I hI => ?_⟩
    · obtain ⟨n, hn⟩ := (Ideal.eq_top_iff_one _).mp e
      exact (H 0).mp .zero ((show (1 : R) = 0 by simpa using hn) ▸ isUnit_one)
    · obtain ⟨x, hx, hx'⟩ := (SetLike.lt_iff_le_and_exists.mp hI).2
      exact Ideal.eq_top_of_isUnit_mem _ hx (not_not.mp ((H x).not.mp hx'))
  tfae_have 4 -> 2 := fun H => ⟨_, H.isPrime, fun p (hp : p.IsPrime) =>
      (H.eq_of_le hp.ne_top (nilradical_le_prime p)).symm⟩
  tfae_have 2 -> 1 := by
    rintro ⟨P, hP₁, hP₂⟩
    obtain ⟨P, hP₃, -⟩ := P.exists_le_maximal hP₁.ne_top
    obtain rfl := hP₂ P hP₃.isPrime
    exact ⟨.mk₀ fun Q h => hP₂ Q h ▸ hP₃, .of_unique_max_ideal ⟨P, hP₃, fun Q h => hP₂ Q h.isPrime⟩⟩
  tfae_finish

@[simp]

Depends on / 依赖: Ideal.eq_top_iff_one, Ideal.eq_top_of_isUnit_mem, Ideal.isMaximal_iff_isPrime, Ideal.radical_eq_sInf, IsLocalRing, IsLocalRing.isMaximal_iff, IsLocalRing.maximalIdeal, SetLike, SetLike.lt_iff_le_and_exists.mp, eq_top_iff_one, eq_top_of_isUnit_mem, isMaximal_iff, isMaximal_iff_isPrime, isUnit_one, lt_iff_le_and_exists, maximalIdeal, nilradical, radical_eq_sInf, tfae_have
-/
lemma Ring.krullDimLE_zero_and_isLocalRing_tfae :
    List.TFAE
    [ Ring.KrullDimLE 0 R ∧ IsLocalRing R,
      exists! I : Ideal R, I.IsPrime,
      forall x : R, IsNilpotent x ↔ ¬ IsUnit x,
      (nilradical R).IsMaximal ] := by
  tfae_have 1 -> 3 := by
    intro ⟨h₁, h₂⟩ x
    change x in nilradical R ↔ x in IsLocalRing.maximalIdeal R
    rw [nilradical]; rw [Ideal.radical_eq_sInf]
    simp [← Ideal.isMaximal_iff_isPrime, IsLocalRing.isMaximal_iff]
  tfae_have 3 -> 4 := by
    refine fun H => ⟨fun e => ?_, fun I hI => ?_⟩
    · obtain ⟨n, hn⟩ := (Ideal.eq_top_iff_one _).mp e
      exact (H 0).mp .zero ((show (1 : R) = 0 by simpa using hn) ▸ isUnit_one)
    · obtain ⟨x, hx, hx'⟩ := (SetLike.lt_iff_le_and_exists.mp hI).2
      exact Ideal.eq_top_of_isUnit_mem _ hx (not_not.mp ((H x).not.mp hx'))
  tfae_have 4 -> 2 := fun H => ⟨_, H.isPrime, fun p (hp : p.IsPrime) =>
      (H.eq_of_le hp.ne_top (nilradical_le_prime p)).symm⟩
  tfae_have 2 -> 1 := by
    rintro ⟨P, hP₁, hP₂⟩
    obtain ⟨P, hP₃, -⟩ := P.exists_le_maximal hP₁.ne_top
    obtain rfl := hP₂ P hP₃.isPrime
    exact ⟨.mk₀ fun Q h => hP₂ Q h ▸ hP₃, .of_unique_max_ideal ⟨P, hP₃, fun Q h => hP₂ Q h.isPrime⟩⟩
  tfae_finish

@[simp]
/--
lemma `le_isUnit_iff_zero_notMem` / 引理 `le_isUnit_iff_zero_notMem`

English:
lemma le_isUnit_iff_zero_notMem
  statement: [IsLocalRing R]
  proof: by
  have := ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩
  exact ⟨fun h₁ h₂ => not_isUnit_zero (h₁ h₂),
    fun H x hx => (this x).not_left.mp fun ⟨n, hn⟩ => H (hn ▸ pow_mem hx n)⟩

中文:
引理 le_isUnit_iff_zero_notMem
  结论: [是局部环 R]
  证明: by
  have := ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩
  exact ⟨fun h₁ h₂ => not_isUnit_zero (h₁ h₂),
    fun H x hx => (this x).not_left.mp fun ⟨n, hn⟩ => H (hn ▸ pow_mem hx n)⟩

Depends on / 依赖: Ring.krullDimLE_zero_and_isLocalRing_tfae, krullDimLE_zero_and_isLocalRing_tfae, not_isUnit_zero, not_left, not_left.mp, pow_mem
-/
lemma le_isUnit_iff_zero_notMem [IsLocalRing R]
    {M : Submonoid R} : M <= IsUnit.submonoid R ↔ 0 ∉ M := by
  have := ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩
  exact ⟨fun h₁ h₂ => not_isUnit_zero (h₁ h₂),
    fun H x hx => (this x).not_left.mp fun ⟨n, hn⟩ => H (hn ▸ pow_mem hx n)⟩

variable (R) in
/--
theorem `Ring.KrullDimLE.existsUnique_isPrime` / 定理 `Ring.KrullDimLE.existsUnique_isPrime`

English:
theorem Ring.KrullDimLE.existsUnique_isPrime
  given: [IsLocalRing R]
  proof: ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩

中文:
定理 环.Krull维数不超过.存在Unique_isPrime
  条件: [是局部环 R]
  证明: ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩

Depends on / 依赖: Ring.krullDimLE_zero_and_isLocalRing_tfae, krullDimLE_zero_and_isLocalRing_tfae
-/
theorem Ring.KrullDimLE.existsUnique_isPrime [IsLocalRing R] :
    exists! I : Ideal R, I.IsPrime :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩

/--
theorem `Ring.KrullDimLE.eq_maximalIdeal_of_isPrime` / 定理 `Ring.KrullDimLE.eq_maximalIdeal_of_isPrime`

English:
theorem Ring.KrullDimLE.eq_maximalIdeal_of_isPrime
  given: [IsLocalRing R] (J : Ideal R) [J.IsPrime]
  proof: (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩).unique
    ‹_› inferInstance

中文:
定理 环.Krull维数不超过.eq_maximalIdeal_of_isPrime
  条件: [是局部环 R] (J : 理想 R) [J.是素]
  证明: (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩).unique
    ‹_› inferInstance

Depends on / 依赖: Ring.krullDimLE_zero_and_isLocalRing_tfae, krullDimLE_zero_and_isLocalRing_tfae, unique
-/
theorem Ring.KrullDimLE.eq_maximalIdeal_of_isPrime [IsLocalRing R] (J : Ideal R) [J.IsPrime] :
    J = IsLocalRing.maximalIdeal R :=
  (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩).unique
    ‹_› inferInstance

/--
lemma `Ring.KrullDimLE.radical_eq_maximalIdeal` / 引理 `Ring.KrullDimLE.radical_eq_maximalIdeal`

English:
lemma Ring.KrullDimLE.radical_eq_maximalIdeal
  given: [IsLocalRing R] (I : Ideal R) (hI : I != ⊤)
  proof: by
  rw [Ideal.radical_eq_sInf]
  refine (sInf_le ?_).antisymm (le_sInf ?_)
  · exact ⟨IsLocalRing.le_maximalIdeal hI, inferInstance⟩
  · rintro J ⟨h₁, h₂⟩
    exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime J).ge

中文:
引理 环.Krull维数不超过.radical_eq_maximalIdeal
  条件: [是局部环 R] (I : 理想 R) (hI : I != ⊤)
  证明: by
  rw [Ideal.radical_eq_sInf]
  refine (sInf_le ?_).antisymm (le_sInf ?_)
  · exact ⟨IsLocalRing.le_maximalIdeal hI, inferInstance⟩
  · rintro J ⟨h₁, h₂⟩
    exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime J).ge

Depends on / 依赖: Ideal.radical_eq_sInf, IsLocalRing, IsLocalRing.le_maximalIdeal, KrullDimLE, Ring.KrullDimLE.eq_maximalIdeal_of_isPrime, antisymm, eq_maximalIdeal_of_isPrime, le_maximalIdeal, le_sInf, radical_eq_sInf, sInf_le
-/
lemma Ring.KrullDimLE.radical_eq_maximalIdeal [IsLocalRing R] (I : Ideal R) (hI : I != ⊤) :
    I.radical = IsLocalRing.maximalIdeal R := by
  rw [Ideal.radical_eq_sInf]
  refine (sInf_le ?_).antisymm (le_sInf ?_)
  · exact ⟨IsLocalRing.le_maximalIdeal hI, inferInstance⟩
  · rintro J ⟨h₁, h₂⟩
    exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime J).ge

variable (R) in
/--
theorem `Ring.KrullDimLE.subsingleton_primeSpectrum` / 定理 `Ring.KrullDimLE.subsingleton_primeSpectrum`

English:
theorem Ring.KrullDimLE.subsingleton_primeSpectrum
  given: [IsLocalRing R]
  proof: ⟨fun x y => PrimeSpectrum.ext
    (eq_maximalIdeal_of_isPrime x.1).trans (eq_maximalIdeal_of_isPrime y.1).symm⟩

中文:
定理 环.Krull维数不超过.subsingleton_primeSpectrum
  条件: [是局部环 R]
  证明: ⟨fun x y => PrimeSpectrum.ext
    (eq_maximalIdeal_of_isPrime x.1).trans (eq_maximalIdeal_of_isPrime y.1).symm⟩

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.ext, eq_maximalIdeal_of_isPrime
-/
theorem Ring.KrullDimLE.subsingleton_primeSpectrum [IsLocalRing R] :
    Subsingleton (PrimeSpectrum R) :=
⟨fun x y => PrimeSpectrum.ext
    (eq_maximalIdeal_of_isPrime x.1).trans (eq_maximalIdeal_of_isPrime y.1).symm⟩

/--
theorem `Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal` / 定理 `Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal`

English:
theorem Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal
  given: [IsLocalRing R] {x}
  proof: ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩ x

中文:
定理 环.Krull维数不超过.isNilpotent_iff_mem_maximalIdeal
  条件: [是局部环 R] {x}
  证明: ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩ x

Depends on / 依赖: Ring.krullDimLE_zero_and_isLocalRing_tfae, krullDimLE_zero_and_isLocalRing_tfae
-/
theorem Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal [IsLocalRing R] {x} :
    IsNilpotent x ↔ x in IsLocalRing.maximalIdeal R :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩ x

/--
theorem `Ring.KrullDimLE.isNilpotent_iff_mem_nonunits` / 定理 `Ring.KrullDimLE.isNilpotent_iff_mem_nonunits`

English:
theorem Ring.KrullDimLE.isNilpotent_iff_mem_nonunits
  given: [IsLocalRing R] {x}
  proof: isNilpotent_iff_mem_maximalIdeal

中文:
定理 环.Krull维数不超过.isNilpotent_iff_mem_nonunits
  条件: [是局部环 R] {x}
  证明: isNilpotent_iff_mem_maximalIdeal

Depends on / 依赖: isNilpotent_iff_mem_maximalIdeal
-/
theorem Ring.KrullDimLE.isNilpotent_iff_mem_nonunits [IsLocalRing R] {x} :
    IsNilpotent x ↔ x in nonunits R :=
  isNilpotent_iff_mem_maximalIdeal

variable (R) in
/--
theorem `Ring.KrullDimLE.nilradical_eq_maximalIdeal` / 定理 `Ring.KrullDimLE.nilradical_eq_maximalIdeal`

English:
theorem Ring.KrullDimLE.nilradical_eq_maximalIdeal
  given: [IsLocalRing R]
  proof: Ideal.ext fun _ => isNilpotent_iff_mem_maximalIdeal

omit [Ring.KrullDimLE 0 R] in

中文:
定理 环.Krull维数不超过.nilradical_eq_maximalIdeal
  条件: [是局部环 R]
  证明: Ideal.ext fun _ => isNilpotent_iff_mem_maximalIdeal

omit [Ring.KrullDimLE 0 R] in

Depends on / 依赖: Ideal.ext, isNilpotent_iff_mem_maximalIdeal
-/
theorem Ring.KrullDimLE.nilradical_eq_maximalIdeal [IsLocalRing R] :
    nilradical R = IsLocalRing.maximalIdeal R :=
  Ideal.ext fun _ => isNilpotent_iff_mem_maximalIdeal

omit [Ring.KrullDimLE 0 R] in
variable (R) in
/--
theorem `IsLocalRing.of_isMaximal_nilradical` / 定理 `IsLocalRing.of_isMaximal_nilradical`

English:
theorem IsLocalRing.of_isMaximal_nilradical
  given: [(nilradical R).IsMaximal]
  proof: (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).2

omit [Ring.KrullDimLE 0 R] in

中文:
定理 是局部环.of_isMaximal_nilradical
  条件: [(nilradical R).是极大]
  证明: (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).2

omit [Ring.KrullDimLE 0 R] in

Depends on / 依赖: Ring.krullDimLE_zero_and_isLocalRing_tfae, krullDimLE_zero_and_isLocalRing_tfae
-/
theorem IsLocalRing.of_isMaximal_nilradical [(nilradical R).IsMaximal] :
    IsLocalRing R :=
  (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).2

omit [Ring.KrullDimLE 0 R] in
variable (R) in
/--
theorem `Ring.KrullDimLE.of_isMaximal_nilradical` / 定理 `Ring.KrullDimLE.of_isMaximal_nilradical`

English:
theorem Ring.KrullDimLE.of_isMaximal_nilradical
  given: [(nilradical R).IsMaximal]
  proof: (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).1

omit [Ring.KrullDimLE 0 R] in

中文:
定理 环.Krull维数不超过.of_isMaximal_nilradical
  条件: [(nilradical R).是极大]
  证明: (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).1

omit [Ring.KrullDimLE 0 R] in

Depends on / 依赖: Ring.krullDimLE_zero_and_isLocalRing_tfae, krullDimLE_zero_and_isLocalRing_tfae
-/
theorem Ring.KrullDimLE.of_isMaximal_nilradical [(nilradical R).IsMaximal] :
    Ring.KrullDimLE 0 R :=
  (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).1

omit [Ring.KrullDimLE 0 R] in
/--
lemma `Ring.KrullDimLE.of_isLocalization` / 引理 `Ring.KrullDimLE.of_isLocalization`

English:
lemma Ring.KrullDimLE.of_isLocalization
  statement: (p : Ideal R) (hp : p in minimalPrimes R)
  proof: have := IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p hp S
  ⟨Order.krullDim_nonpos_of_subsingleton⟩

中文:
引理 环.Krull维数不超过.of_isLocalization
  结论: (p : 理想 R) (hp : p in minimalPrimes R)
  证明: have := IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p hp S
  ⟨Order.krullDim_nonpos_of_subsingleton⟩

Depends on / 依赖: FirstCountableTopology, FirstCountableTopology.frechetUrysohnSpace, frechetUrysohnSpace
-/
lemma Ring.KrullDimLE.of_isLocalization (p : Ideal R) (hp : p in minimalPrimes R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    Ring.KrullDimLE 0 S :=
  have := IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p hp S
  ⟨Order.krullDim_nonpos_of_subsingleton⟩

/--
lemma `Ring.KrullDimLE.isField_of_isReduced` / 引理 `Ring.KrullDimLE.isField_of_isReduced`

English:
lemma Ring.KrullDimLE.isField_of_isReduced
  given: [IsReduced R] [IsLocalRing R]
  statement: IsField R
  proof: by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]; rw [← nilradical_eq_maximalIdeal]; rw [nilradical_eq_zero]; rw [Ideal.zero_eq_bot]

中文:
引理 环.Krull维数不超过.isField_of_isReduced
  条件: [是既约 R] [是局部环 R]
  结论: 是域 R
  证明: by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]; rw [← nilradical_eq_maximalIdeal]; rw [nilradical_eq_zero]; rw [Ideal.zero_eq_bot]

Depends on / 依赖: FrechetUrysohnSpace, FrechetUrysohnSpace.to_sequentialSpace, Ideal.zero_eq_bot, IsLocalRing, IsLocalRing.isField_iff_maximalIdeal_eq, isField_iff_maximalIdeal_eq, nilradical_eq_maximalIdeal, nilradical_eq_zero, to_sequentialSpace, zero_eq_bot
-/
lemma Ring.KrullDimLE.isField_of_isReduced [IsReduced R] [IsLocalRing R] : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]; rw [← nilradical_eq_maximalIdeal]; rw [nilradical_eq_zero]; rw [Ideal.zero_eq_bot]

/--
Instance `PrimeSpectrum.unique_of_ringKrullDimLE_zero` / 实例 `PrimeSpectrum.unique_of_ringKrullDimLE_zero`

English:
instance PrimeSpectrum.unique_of_ringKrullDimLE_zero
  signature: [IsLocalRing R]
  body: ⟨⟨IsLocalRing.closedPoint _⟩,
    fun _ => PrimeSpectrum.ext (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime _)⟩

中文:
实例 素谱.unique_of_ringKrullDimLE_zero
  签名: [是局部环 R]
  定义体: ⟨⟨IsLocalRing.closedPoint _⟩,
    fun _ => PrimeSpectrum.ext (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime _)⟩

Depends on / 依赖: IsLocalRing, IsLocalRing.closedPoint, KrullDimLE, PrimeSpectrum, PrimeSpectrum.ext, Ring.KrullDimLE.eq_maximalIdeal_of_isPrime, closedPoint, eq_maximalIdeal_of_isPrime
-/
instance PrimeSpectrum.unique_of_ringKrullDimLE_zero [IsLocalRing R] : Unique (PrimeSpectrum R) :=
  ⟨⟨IsLocalRing.closedPoint _⟩,
    fun _ => PrimeSpectrum.ext (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime _)⟩

/--
lemma `PrimeSpectrum.subsingleton_iff_isField_of_isReduced` / 引理 `PrimeSpectrum.subsingleton_iff_isField_of_isReduced`

English:
lemma PrimeSpectrum.subsingleton_iff_isField_of_isReduced
  proof: by
  refine ⟨fun H => ?_, fun H => letI := H.toField; inferInstance⟩
  have : Subsingleton (MaximalSpectrum R) := MaximalSpectrum.toPrimeSpectrum_injective.subsingleton
  have : IsLocalRing R := .of_singleton_maximalSpectrum
  exact Ring.KrullDimLE.isField_of_isReduced

中文:
引理 素谱.subsingleton_iff_isField_of_isReduced
  证明: by
  refine ⟨fun H => ?_, fun H => letI := H.toField; inferInstance⟩
  have : Subsingleton (MaximalSpectrum R) := MaximalSpectrum.toPrimeSpectrum_injective.subsingleton
  have : IsLocalRing R := .of_singleton_maximalSpectrum
  exact Ring.KrullDimLE.isField_of_isReduced

Depends on / 依赖: H.toField, IsLocalRing, KrullDimLE, MaximalSpectrum, MaximalSpectrum.toPrimeSpectrum_injective.subsingleton, Ring.KrullDimLE.isField_of_isReduced, Subsingleton, isField_of_isReduced, of_singleton_maximalSpectrum, subsingleton, toField, toPrimeSpectrum_injective
-/
lemma PrimeSpectrum.subsingleton_iff_isField_of_isReduced
    {R : Type*} [CommRing R] [IsReduced R] [Nontrivial R] :
    Subsingleton (PrimeSpectrum R) ↔ IsField R := by
  refine ⟨fun H => ?_, fun H => letI := H.toField; inferInstance⟩
  have : Subsingleton (MaximalSpectrum R) := MaximalSpectrum.toPrimeSpectrum_injective.subsingleton
  have : IsLocalRing R := .of_singleton_maximalSpectrum
  exact Ring.KrullDimLE.isField_of_isReduced

end IsLocalRing

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (I : Ideal R)

/--
lemma `Ideal.jacobson_eq_radical` / 引理 `Ideal.jacobson_eq_radical`

English:
lemma Ideal.jacobson_eq_radical
  given: [Ring.KrullDimLE 0 R]
  statement: I.jacobson = I.radical
  proof: by
  simp [jacobson, radical_eq_sInf, Ideal.isMaximal_iff_isPrime]

中文:
引理 理想.jacobson_eq_radical
  条件: [环.Krull维数不超过 0 R]
  结论: I.jacobson = I.radical
  证明: by
  simp [jacobson, radical_eq_sInf, Ideal.isMaximal_iff_isPrime]

Depends on / 依赖: Ideal.isMaximal_iff_isPrime, isMaximal_iff_isPrime, jacobson, radical_eq_sInf
-/
lemma Ideal.jacobson_eq_radical [Ring.KrullDimLE 0 R] : I.jacobson = I.radical := by
  simp [jacobson, radical_eq_sInf, Ideal.isMaximal_iff_isPrime]

instance (priority := 100) [Ring.KrullDimLE 0 R] : IsJacobsonRing R :=
  ⟨fun I hI => by rw [I.jacobson_eq_radical, hI.radical]⟩

end CommRing
