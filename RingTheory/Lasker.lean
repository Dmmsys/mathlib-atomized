/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Order.Irreducible
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Lasker ring

## Main declarations

- `IsLasker`: An `R`-module `M` satisfies `IsLasker R M` when any `N : Submodule R M` can be
  decomposed into finitely many primary submodules.
- `IsLasker.exists_isMinimalPrimaryDecomposition`: Any `N : Submodule R N` in an `R`-module `M`
  satisfying `IsLasker R M` can be decomposed into finitely many primary submodules `Nᵢ`, such
  that the decomposition is minimal: each `Nᵢ` is necessary, and the `√Ann(M/Nᵢ)` are distinct.
- `IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes`: The first uniqueness theorem
  for primary decomposition, Theorem 4.5 in Atiyah-Macdonald: In any minimal primary decomposition
  `I = ⨅ i, q_i`, the ideals `radical (q_i.colon M)` are exactly the associated primes of `I`.
- `Submodule.isLasker`: Every Noetherian module is Lasker.

-/

@[expose] public section

section IsLasker

open Ideal

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `IsLasker` / `IsLasker` 的定义

English:
definition IsLasker
  signature: : Prop
  body: forall N : Submodule R M, exists s : Finset (Submodule R M), s.inf id = N ∧ forall ⦃J⦄, J in s -> J.IsPrimary

中文:
定义 IsLasker
  签名: : 命题
  定义体: forall N : Submodule R M, exists s : Finset (Submodule R M), s.inf id = N ∧ forall ⦃J⦄, J in s -> J.IsPrimary

Depends on / 依赖: Finset, IsPrimary, J.IsPrimary, Submodule, s.inf
-/
def IsLasker : Prop :=
  forall N : Submodule R M, exists s : Finset (Submodule R M), s.inf id = N ∧ forall ⦃J⦄, J in s -> J.IsPrimary

variable {R M}

namespace Submodule

/--
lemma `decomposition_erase_inf` / 引理 `decomposition_erase_inf`

English:
lemma decomposition_erase_inf
  statement: {N : Submodule R M}
  proof: by
  induction s using Finset.eraseInduction with
  | H s IH =>
    by_cases! H : forall J in s, ¬ (s.erase J).inf id <= J
    · exact ⟨s, Finset.Subset.rfl, hs, H⟩
    obtain ⟨J, hJ, hJ'⟩ := H
    refine (IH _ hJ ?_).imp
      fun t => And.imp_left (fun ht => ht.trans (Finset.erase_subset _ _))
   

中文:
引理 decomposition_erase_inf
  结论: {N : 子模 R M}
  证明: by
  induction s using Finset.eraseInduction with
  | H s IH =>
    by_cases! H : forall J in s, ¬ (s.erase J).inf id <= J
    · exact ⟨s, Finset.Subset.rfl, hs, H⟩
    obtain ⟨J, hJ, hJ'⟩ := H
    refine (IH _ hJ ?_).imp
      fun t => And.imp_left (fun ht => ht.trans (Finset.erase_subset _ _))
   

Depends on / 依赖: And.imp_left, Finset, Finset.Subset.rfl, Finset.eraseInduction, Finset.erase_subset, Finset.insert_erase, Subset, eraseInduction, erase_subset, ht.trans, imp_left, insert_erase, s.erase
-/
lemma decomposition_erase_inf {N : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = N) :
    exists t : Finset (Submodule R M), t subseteq s ∧ t.inf id = N ∧
      forall ⦃J⦄, J in t -> ¬ (t.erase J).inf id <= J := by
  induction s using Finset.eraseInduction with
  | H s IH =>
    by_cases! H : forall J in s, ¬ (s.erase J).inf id <= J
    · exact ⟨s, Finset.Subset.rfl, hs, H⟩
    obtain ⟨J, hJ, hJ'⟩ := H
    refine (IH _ hJ ?_).imp
      fun t => And.imp_left (fun ht => ht.trans (Finset.erase_subset _ _))
    rw [← Finset.insert_erase hJ] at hs
    simp [← hs, hJ']

open scoped Function -- required for scoped `on` notation

/--
lemma `isPrimary_decomposition_pairwise_ne_radical` / 引理 `isPrimary_decomposition_pairwise_ne_radical`

English:
lemma isPrimary_decomposition_pairwise_ne_radical
  statement: {N : Submodule R M}
  proof: by
  refine ⟨(s.image fun J => {I in s | (I.colon .univ).radical = (J.colon .univ).radical}).image
    fun t => t.inf id, ?_, ?_, ?_⟩
  · ext
    grind [Finset.inf_image, Submodule.mem_finsetInf]
  · simp only [Finset.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_appl

中文:
引理 isPrimary_decomposition_pairwise_ne_radical
  结论: {N : 子模 R M}
  证明: by
  refine ⟨(s.image fun J => {I in s | (I.colon .univ).radical = (J.colon .univ).radical}).image
    fun t => t.inf id, ?_, ?_, ?_⟩
  · ext
    grind [Finset.inf_image, Submodule.mem_finsetInf]
  · simp only [Finset.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_appl

Depends on / 依赖: Finset, Finset.coe_image, Finset.inf_image, Finset.mem_filter, Finset.mem_image, I.colon, J.colon, Submodule, Submodule.mem_finsetInf, and_imp, coe_image, exists_exists_and_eq_and, forall_exists_index, id_eq, inf_image, isPrimary_finsetInf, mem_filter, mem_finsetInf, mem_image, radical
-/
lemma isPrimary_decomposition_pairwise_ne_radical {N : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = N) (hs' : forall ⦃J⦄, J in s -> J.IsPrimary) :
    exists t : Finset (Submodule R M), t.inf id = N ∧ (forall ⦃J⦄, J in t -> J.IsPrimary) ∧
      (t : Set (Submodule R M)).Pairwise ((· != ·) on fun J => (J.colon Set.univ).radical) := by
  refine ⟨(s.image fun J => {I in s | (I.colon .univ).radical = (J.colon .univ).radical}).image
    fun t => t.inf id, ?_, ?_, ?_⟩
  · ext
    grind [Finset.inf_image, Submodule.mem_finsetInf]
  · simp only [Finset.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    intro J hJ
    refine isPrimary_finsetInf (i := J) ?_ ?_ (by simp)
    · simp [hJ]
    · simp only [Finset.mem_filter, id_eq, and_imp]
      intro y hy
      simp [hs' hy]
  · intro I hI J hJ hIJ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and] at hI hJ
    obtain ⟨I', hI', hI⟩ := hI
    obtain ⟨J', hJ', hJ⟩ := hJ
    simp only [Function.onFun, ne_eq]
    contrapose hIJ
    suffices (I'.colon Set.univ).radical = (J'.colon Set.univ).radical by
      rw [← hI]; rw [← hJ]; rw [this]
    · rw [← hI, colon_finsetInf,
        radical_finset_inf (i := I') (by simp [hI']) (by simp), id_eq] at hIJ
      rw [hIJ]; rw [← hJ]; rw [colon_finsetInf]; rw [radical_finset_inf (i := J') (by simp [hJ']) (by simp), id_eq]

/--
lemma `exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition` / 引理 `exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition`

English:
lemma exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition
  proof: by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi => ht' (hut hi), ht''.mono hut, hu'⟩

中文:
引理 存在_minimal_isPrimary_decomposition_of_isPrimary_decomposition
  证明: by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi => ht' (hut hi), ht''.mono hut, hu'⟩

Depends on / 依赖: decomposition_erase_inf, isPrimary_decomposition_pairwise_ne_radical
-/
lemma exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition
    {N : Submodule R M} {s : Finset (Submodule R M)}
    (hs : s.inf id = N) (hs' : forall ⦃J⦄, J in s -> J.IsPrimary) :
    exists t : Finset (Submodule R M), t.inf id = N ∧ (forall ⦃J⦄, J in t -> J.IsPrimary) ∧
      ((t : Set (Submodule R M)).Pairwise ((· != ·) on fun J => (J.colon Set.univ).radical)) ∧
      (forall ⦃J⦄, J in t -> ¬ (t.erase J).inf id <= J) := by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi => ht' (hut hi), ht''.mono hut, hu'⟩

/--
Definition of `IsMinimalPrimaryDecomposition` / `IsMinimalPrimaryDecomposition` 的定义

English:
structure IsMinimalPrimaryDecomposition
  axioms and operations (4):
    - inf_eq : t.inf id = N
    - primary : forall ⦃J⦄, J in t -> J.IsPrimary
    - distinct : (t : Set (Submodule R M)).Pairwise ((· != ·) on fun J => (J.colon Set.univ).radical)
    - minimal : forall ⦃J⦄, J in t -> ¬ (t.erase J).inf id <= J

中文:
结构 是MinimalPrimaryDecomposition
  公理与运算 (4 个):
    - inf_eq : t.下确界 id = N
    - primary : 对任意 ⦃J⦄, J in t -> J.是准素
    - distinct : (t : 集合 (子模 R M)).两两 ((· != ·) on fun J => (J.colon 集合.univ).radical)
    - minimal : 对任意 ⦃J⦄, J in t -> ¬ (t.erase J).下确界 id <= J
-/
structure IsMinimalPrimaryDecomposition
    (N : Submodule R M) (t : Finset (Submodule R M)) where
  inf_eq : t.inf id = N
  primary : forall ⦃J⦄, J in t -> J.IsPrimary
  distinct : (t : Set (Submodule R M)).Pairwise ((· != ·) on fun J => (J.colon Set.univ).radical)
  minimal : forall ⦃J⦄, J in t -> ¬ (t.erase J).inf id <= J

/--
lemma `IsLasker.exists_isMinimalPrimaryDecomposition` / 引理 `IsLasker.exists_isMinimalPrimaryDecomposition`

English:
lemma IsLasker.exists_isMinimalPrimaryDecomposition
  proof: by
  obtain ⟨s, hs1, hs2⟩ := h N
  obtain ⟨t, h1, h2, h3, h4⟩ :=
    exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs1 hs2
  exact ⟨t, h1, h2, h3, h4⟩

中文:
引理 IsLasker.存在_isMinimalPrimaryDecomposition
  证明: by
  obtain ⟨s, hs1, hs2⟩ := h N
  obtain ⟨t, h1, h2, h3, h4⟩ :=
    exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs1 hs2
  exact ⟨t, h1, h2, h3, h4⟩

Depends on / 依赖: exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition
-/
lemma IsLasker.exists_isMinimalPrimaryDecomposition
    (h : IsLasker R M) (N : Submodule R M) :
    exists t : Finset (Submodule R M), N.IsMinimalPrimaryDecomposition t := by
  obtain ⟨s, hs1, hs2⟩ := h N
  obtain ⟨t, h1, h2, h3, h4⟩ :=
    exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs1 hs2
  exact ⟨t, h1, h2, h3, h4⟩

namespace IsMinimalPrimaryDecomposition

/--
lemma `injOn` / 引理 `injOn`

English:
lemma injOn
  statement: (N : Submodule R M)
  proof: Set.injOn_iff_pairwise_ne.mpr ht.distinct

中文:
引理 injOn
  结论: (N : 子模 R M)
  证明: Set.injOn_iff_pairwise_ne.mpr ht.distinct

Depends on / 依赖: Set.injOn_iff_pairwise_ne.mpr, distinct, ht.distinct, injOn_iff_pairwise_ne
-/
lemma injOn (N : Submodule R M)
    (t : Finset (Submodule R M)) (ht : N.IsMinimalPrimaryDecomposition t) :
    Set.InjOn (fun J => (J.colon Set.univ).radical) (t : Set (Submodule R M)) :=
  Set.injOn_iff_pairwise_ne.mpr ht.distinct

/--
lemma `image_radical_eq_associated_primes` / 引理 `image_radical_eq_associated_primes`

English:
lemma image_radical_eq_associated_primes
  proof: by
  classical
  replace h x : radical (N.colon {x}) = (t.filter (x ∉ ·)).inf fun q => radical (q.colon .univ) := by
    simp_rw [← ht.inf_eq, colon_finsetInf, ← radicalInfTopHom_apply, map_finset_inf,
      Function.comp_def, radicalInfTopHom_apply, id_eq]
    rw [Finset.inf_congr rfl (fun q hq => 

中文:
引理 image_radical_eq_associated_primes
  证明: by
  classical
  replace h x : radical (N.colon {x}) = (t.filter (x ∉ ·)).inf fun q => radical (q.colon .univ) := by
    simp_rw [← ht.inf_eq, colon_finsetInf, ← radicalInfTopHom_apply, map_finset_inf,
      Function.comp_def, radicalInfTopHom_apply, id_eq]
    rw [Finset.inf_congr rfl (fun q hq => 

Depends on / 依赖: Finset, Finset.inf_congr, Finset.inf_ite, Finset.inf_top, Function, Function.comp_def, N.colon, SetLike, SetLike.not_le_iff_exists.mp, classical, colon_finsetInf, comp_def, filter, ht.inf_eq, ht.minimal, ht.primary, id_eq, inf_congr, inf_eq, inf_ite
-/
lemma image_radical_eq_associated_primes
    {N : Submodule R M} {t : Finset (Submodule R M)} (ht : IsMinimalPrimaryDecomposition N t) :
    (fun J : Submodule R M => (J.colon Set.univ).radical) '' t = N.associatedPrimes := by
  classical
  replace h x : radical (N.colon {x}) = (t.filter (x ∉ ·)).inf fun q => radical (q.colon .univ) := by
    simp_rw [← ht.inf_eq, colon_finsetInf, ← radicalInfTopHom_apply, map_finset_inf,
      Function.comp_def, radicalInfTopHom_apply, id_eq]
    rw [Finset.inf_congr rfl (fun q hq => (ht.primary hq).radical_colon_singleton_eq_ite x)]; rw [Finset.inf_ite]; rw [Finset.inf_top]; rw [top_inf_eq]
  ext p
  constructor
  · rintro ⟨q, hqt, rfl⟩
    obtain ⟨x, hxt, hxq⟩ := SetLike.not_le_iff_exists.mp (ht.minimal hqt)
    use (ht.primary hqt).isPrime_radical_colon, x
    rw [h]; rw [← Finset.insert_erase (Finset.mem_filter.mpr ⟨hqt]; rw [hxq⟩)]; rw [Finset.inf_insert]; rw [eq_comm]; rw [inf_eq_left]; rw [Finset.le_inf_iff]
    simp only [mem_finsetInf, Finset.mem_erase] at hxt
    grind
  · rintro ⟨hp, x, rfl⟩
    rw [h] at hp ⊢
    obtain ⟨q, hq1, hq2⟩ := eq_inf_of_isPrime_inf hp
    exact ⟨q, Finset.mem_of_mem_filter q hq1, hq2⟩

@[deprecated (since := "2026-01-19")]
alias mem_image_radical_colon_iff := image_radical_eq_associated_primes

/--
lemma `mem_associatedPrimes` / 引理 `mem_associatedPrimes`

English:
lemma mem_associatedPrimes
  statement: {N : Submodule R M} {t : Finset (Submodule R M)}
  proof: by
  rw [← ht.image_radical_eq_associated_primes]
  exact Set.mem_image_of_mem _ hq

中文:
引理 mem_associatedPrimes
  结论: {N : 子模 R M} {t : 有限集 (子模 R M)}
  证明: by
  rw [← ht.image_radical_eq_associated_primes]
  exact Set.mem_image_of_mem _ hq

Depends on / 依赖: Set.mem_image_of_mem, ht.image_radical_eq_associated_primes, image_radical_eq_associated_primes, mem_image_of_mem
-/
lemma mem_associatedPrimes {N : Submodule R M} {t : Finset (Submodule R M)}
    (ht : IsMinimalPrimaryDecomposition N t) {q : Submodule R M} (hq : q in t) :
    (q.colon Set.univ).radical in N.associatedPrimes := by
  rw [← ht.image_radical_eq_associated_primes]
  exact Set.mem_image_of_mem _ hq

section CommRing

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M] {N : Submodule R M}

open LocalizedModule in
/--
lemma `comap_localized₀_eq_ite` / 引理 `comap_localized₀_eq_ite`

English:
lemma comap_localized₀_eq_ite
  proof: ⨅ q in s₀, q.1.primeCompl
    letI f := mkLinearMap S M
    (localized₀ S f q).comap f = if p in s₀ then q else ⊤ := by
  set S := ⨅ q in s₀, q.1.primeCompl
  set f := mkLinearMap S M
  split_ifs with hp
  · refine le_antisymm (fun x hx => ?_) (map_le_iff_le_comap.mp (map_le_localized₀ S f q))
    o

中文:
引理 comap_localized₀_eq_ite
  证明: ⨅ q in s₀, q.1.primeCompl
    letI f := mkLinearMap S M
    (localized₀ S f q).comap f = if p in s₀ then q else ⊤ := by
  set S := ⨅ q in s₀, q.1.primeCompl
  set f := mkLinearMap S M
  split_ifs with hp
  · refine le_antisymm (fun x hx => ?_) (map_le_iff_le_comap.mp (map_le_localized₀ S f q))
    o

Depends on / 依赖: primeCompl
-/
lemma comap_localized₀_eq_ite
    (s₀ : Finset N.associatedPrimes) (hs₀ : IsLowerSet (s₀ : Set N.associatedPrimes))
    (q : Submodule R M) (hqp : q.IsPrimary)
    (p : N.associatedPrimes) (hq : (q.colon Set.univ).radical = p) :
    letI S := ⨅ q in s₀, q.1.primeCompl
    letI f := mkLinearMap S M
    (localized₀ S f q).comap f = if p in s₀ then q else ⊤ := by
  set S := ⨅ q in s₀, q.1.primeCompl
  set f := mkLinearMap S M
  split_ifs with hp
  · refine le_antisymm (fun x hx => ?_) (map_le_iff_le_comap.mp (map_le_localized₀ S f q))
    obtain ⟨b, hb, a, ha⟩ := hx
    rw [IsLocalizedModule.mk'_eq_iff]; rw [← LinearMap.map_smul_of_tower] at ha
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S f).mp ha
    replace hb := q.smul_mem c hb
    rw [← Submonoid.smul_def]; rw [hc]; rw [smul_smul] at hb
    apply (hqp.mem_or_mem hb).resolve_right
    grind [Submonoid.mem_iInf, mem_primeCompl_iff]
  · replace hq : ¬ (q.colon Set.univ : Set R) subseteq ⋃ r in s₀, r := by
      contrapose hp
      obtain ⟨r, hrs, h⟩ := (subset_union_prime p p fun i _ _ _ => i.2.1).mp hp
      rw [← r.2.1.radical_le_iff]; rw [hq] at h
      exact hs₀ h hrs
    obtain ⟨y, hy1, hy2⟩ := Set.not_subset_iff_exists_mem_notMem.mp hq
    replace hy2 : y in S := by
      simp only [Submonoid.mem_iInf, Ideal.mem_primeCompl_iff, Subtype.forall, S]
      intro r hrI hrs
      contrapose hy2
      exact Set.mem_biUnion hrs hy2
    rw [eq_top_iff]; rw [← map_le_iff_le_comap]; rw [map_top]
    rintro - ⟨x, rfl⟩
    simp_rw [mem_localized₀, IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower]
    exact ⟨y • x, hy1 (Set.smul_mem_smul_set (Set.mem_univ x)), ⟨y, hy2⟩, rfl⟩

open LocalizedModule Submodule.IsLocalizedModule in
/--
lemma `comap_localized₀_eq_iInf` / 引理 `comap_localized₀_eq_iInf`

English:
lemma comap_localized₀_eq_iInf
  proof: ⨅ q in s₀, q.1.primeCompl
    letI f := mkLinearMap S M
    (N.localized₀ S f).comap f = ⨅ q in s, q := by
  set S := ⨅ q in s₀, q.1.primeCompl
  set f := mkLinearMap S M
  rw [← ht.inf_eq]; rw [← localized₀FrameHom_apply]; rw [map_finset_inf]; rw [Submodule.comap_finsetInf]
  simp_rw [Function.comp

中文:
引理 comap_localized₀_eq_iInf
  证明: ⨅ q in s₀, q.1.primeCompl
    letI f := mkLinearMap S M
    (N.localized₀ S f).comap f = ⨅ q in s, q := by
  set S := ⨅ q in s₀, q.1.primeCompl
  set f := mkLinearMap S M
  rw [← ht.inf_eq]; rw [← localized₀FrameHom_apply]; rw [map_finset_inf]; rw [Submodule.comap_finsetInf]
  simp_rw [Function.comp

Depends on / 依赖: primeCompl
-/
lemma comap_localized₀_eq_iInf
    {t : Finset (Submodule R M)} (ht : N.IsMinimalPrimaryDecomposition t)
    (s₀ : Finset N.associatedPrimes) (hs₀ : IsLowerSet (s₀ : Set N.associatedPrimes))
    (s : Finset (Submodule R M)) (hs : s subseteq t)
    (hs' : (s.image fun q => (q.colon Set.univ).radical) = s₀.image (↑)) :
    letI S := ⨅ q in s₀, q.1.primeCompl
    letI f := mkLinearMap S M
    (N.localized₀ S f).comap f = ⨅ q in s, q := by
  set S := ⨅ q in s₀, q.1.primeCompl
  set f := mkLinearMap S M
  rw [← ht.inf_eq]; rw [← localized₀FrameHom_apply]; rw [map_finset_inf]; rw [Submodule.comap_finsetInf]
  simp_rw [Function.comp_def, id_eq, localized₀FrameHom_apply]
  suffices forall q in t, (localized₀ S f q).comap f = if q in s then q else ⊤ by
    rw [Finset.inf_congr rfl this]; rw [Finset.inf_ite]; rw [Finset.inf_top]; rw [inf_top_eq]; rw [Finset.filter_mem_eq_inter]; rw [Finset.inter_eq_right.mpr hs]; rw [Finset.inf_eq_iInf]
  refine fun q hqt => (IsMinimalPrimaryDecomposition.comap_localized₀_eq_ite s₀ hs₀ q
    (ht.primary hqt) ⟨(q.colon Set.univ).radical, ht.mem_associatedPrimes hqt⟩ rfl).trans
    (ite_cond_congr (Iff.trans ?_ (ht.injOn.mem_image_iff hs hqt)).eq)
  grind [Finset.mem_image_of_mem]

end CommRing

end Submodule.IsMinimalPrimaryDecomposition

/--
lemma `Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical` / 引理 `Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical`

English:
lemma Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical
  proof: by
  intro p hp
  have htp : t.inf radical <= p := by
    rw [← hp.1.1.radical]
    refine le_trans ?_ (radical_mono hp.1.2)
    rw [← ht.inf_eq]; rw [← radicalInfTopHom_apply]; rw [map_finset_inf]
    rfl
  obtain ⟨q, hqt, hqp⟩ := (IsPrime.inf_le' hp.1.1).mp htp
  exact ⟨q, hqt, le_antisymm hqp (hp

中文:
引理 理想.是MinimalPrimaryDecomposition.minimalPrimes_subset_image_radical
  证明: by
  intro p hp
  have htp : t.inf radical <= p := by
    rw [← hp.1.1.radical]
    refine le_trans ?_ (radical_mono hp.1.2)
    rw [← ht.inf_eq]; rw [← radicalInfTopHom_apply]; rw [map_finset_inf]
    rfl
  obtain ⟨q, hqt, hqp⟩ := (IsPrime.inf_le' hp.1.1).mp htp
  exact ⟨q, hqt, le_antisymm hqp (hp

Depends on / 依赖: Finset, Finset.inf_le, IsPrime, IsPrime.inf_le, ht.inf_eq, ht.inf_eq.symm.trans_le, ht.primary, inf_eq, inf_le, isPrime_radical, le_antisymm, le_radical, le_trans, map_finset_inf, primary, radical, radicalInfTopHom_apply, radical_mono, t.inf, trans_le
-/
lemma Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical
    {I : Ideal R} {t : Finset (Ideal R)} (ht : I.IsMinimalPrimaryDecomposition t) :
    I.minimalPrimes subseteq radical '' t := by
  intro p hp
  have htp : t.inf radical <= p := by
    rw [← hp.1.1.radical]
    refine le_trans ?_ (radical_mono hp.1.2)
    rw [← ht.inf_eq]; rw [← radicalInfTopHom_apply]; rw [map_finset_inf]
    rfl
  obtain ⟨q, hqt, hqp⟩ := (IsPrime.inf_le' hp.1.1).mp htp
  exact ⟨q, hqt, le_antisymm hqp (hp.2 ⟨isPrime_radical (ht.primary hqt),
    ht.inf_eq.symm.trans_le ((Finset.inf_le hqt).trans le_radical)⟩ hqp)⟩

@[deprecated (since := "2026-01-19")]
alias Ideal.decomposition_erase_inf := Submodule.decomposition_erase_inf

@[deprecated (since := "2026-01-19")]
alias Ideal.isPrimary_decomposition_pairwise_ne_radical :=
  Submodule.isPrimary_decomposition_pairwise_ne_radical

@[deprecated (since := "2026-01-19")]
alias Ideal.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition :=
  Submodule.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition

@[deprecated (since := "2026-01-19")]
alias Ideal.IsMinimalPrimaryDecomposition := Submodule.IsMinimalPrimaryDecomposition

@[deprecated (since := "2026-01-19")]
alias Ideal.IsLasker.exists_isMinimalPrimaryDecomposition :=
  Submodule.IsLasker.exists_isMinimalPrimaryDecomposition

@[deprecated (since := "2026-01-19")]
alias Ideal.IsLasker.minimal := Submodule.IsLasker.exists_isMinimalPrimaryDecomposition

end IsLasker

namespace Submodule

section Noetherian

open scoped Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M]

/--
lemma `_root_.InfIrred.isPrimary` / 引理 `_root_.InfIrred.isPrimary`

English:
lemma _root_.InfIrred.isPrimary
  given: {N : Submodule R M} (h : InfIrred N)
  statement: N.IsPrimary
  proof: by
  rw [Submodule.IsPrimary]
  refine ⟨h.ne_top, fun {a b} hab => ?_⟩
  let f : Nat -> Submodule R M := fun n =>
  { carrier := {x | a ^ n • x in N}
    add_mem' hx hy := by simp [N.add_mem hx hy]
    zero_mem' := by simp
    smul_mem' x y h := by simp [smul_comm _ x, N.smul_mem x h] }
  have hf : 

中文:
引理 _root_.InfIrred.isPrimary
  条件: {N : 子模 R M} (h : InfIrred N)
  结论: N.是准素
  证明: by
  rw [Submodule.IsPrimary]
  refine ⟨h.ne_top, fun {a b} hab => ?_⟩
  let f : Nat -> Submodule R M := fun n =>
  { carrier := {x | a ^ n • x in N}
    add_mem' hx hy := by simp [N.add_mem hx hy]
    zero_mem' := by simp
    smul_mem' x y h := by simp [smul_comm _ x, N.smul_mem x h] }
  have hf : 

Depends on / 依赖: IsPrimary, Monotone, N.add_mem, N.smul_mem, Submodule, Submodule.IsPrimary, add_mem, carrier, h.ne_top, monotone_stabilizes_iff_noetherian, monotone_stabilizes_iff_noetherian.mpr, ne_top, pow_add, smul_comm, smul_mem, smul_smul, specialize, zero_mem
-/
lemma _root_.InfIrred.isPrimary {N : Submodule R M} (h : InfIrred N) : N.IsPrimary := by
  rw [Submodule.IsPrimary]
  refine ⟨h.ne_top, fun {a b} hab => ?_⟩
  let f : Nat -> Submodule R M := fun n =>
  { carrier := {x | a ^ n • x in N}
    add_mem' hx hy := by simp [N.add_mem hx hy]
    zero_mem' := by simp
    smul_mem' x y h := by simp [smul_comm _ x, N.smul_mem x h] }
  have hf : Monotone f := by
    intro n m hnm x hx
    simpa [hnm, smul_smul, ← pow_add] using! N.smul_mem (a ^ (m - n)) hx
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹_› ⟨f, hf⟩
  rcases h with ⟨-, h⟩
  specialize @h (f n) (N + a ^ n • ⊤) ?_
  · refine le_antisymm (fun r ⟨h1, h2⟩ => ?_) (le_inf (fun x => N.smul_mem (a ^ n)) (by simp))
    simp only [add_eq_sup, SetLike.mem_coe, mem_sup, mem_smul_pointwise_iff_exists] at h2
    obtain ⟨x, hx, -, ⟨y, -, rfl⟩, rfl⟩ := h2
    have h : (a ^ n • y in N) = (a ^ (n + n) • y in N) := congr_arg (y in ·) (hn (n + n) le_add_self)
    rw [pow_add]; rw [mul_smul] at h
    rwa [N.add_mem_iff_right hx, h, ← N.add_mem_iff_right (N.smul_mem (a ^ n) hx), ← smul_add]
  rw [add_eq_sup]; rw [sup_eq_left] at h
  refine h.imp (fun h => ?_) (fun h => ⟨n, h⟩)
  replace hn : f n = f (n + 1) := hn (n + 1) n.le_succ
  rw [← h]; rw [hn]
  rw [← h] at hab
  simpa [f, pow_succ, mul_smul] using! hab

variable (R M) in
/--
lemma `isLasker` / 引理 `isLasker`

English:
lemma isLasker
  statement: IsLasker R M
  proof: fun I =>
  (exists_infIrred_decomposition I).imp fun _ h => h.imp_right fun h' _ ht => (h' ht).isPrimary

中文:
引理 isLasker
  结论: IsLasker R M
  证明: fun I =>
  (exists_infIrred_decomposition I).imp fun _ h => h.imp_right fun h' _ ht => (h' ht).isPrimary

Depends on / 依赖: CompactSpace, FirstCountableTopology, FirstCountableTopology.seq_compact_of_compact, seq_compact_of_compact
-/
lemma isLasker : IsLasker R M := fun I =>
  (exists_infIrred_decomposition I).imp fun _ h => h.imp_right fun h' _ ht => (h' ht).isPrimary

end Noetherian

end Submodule

@[deprecated (since := "2026-01-19")]
alias Ideal.isLasker := Submodule.isLasker
