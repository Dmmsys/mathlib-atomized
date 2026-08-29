/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!

# Support of a module

## Main results
- `Module.support`: The support of an `R`-module as a subset of `Spec R`.
- `Module.mem_support_iff_exists_annihilator`: `p ∈ Supp M ↔ ∃ m, Ann(m) ≤ p`.
- `Module.support_eq_empty_iff`: `Supp M = ∅ ↔ M = 0`
- `Module.support_of_exact`: `Supp N = Supp M ∪ Supp P` for an exact sequence `0 → M → N → P → 0`.
- `Module.support_eq_zeroLocus`: If `M` is `R`-finite, then `Supp M = Z(Ann(M))`.
- `LocalizedModule.exists_subsingleton_away`:
  If `M` is `R`-finite and `Mₚ = 0`, then `M[1/f] = 0` for some `p ∈ D(f)`.

Also see `Mathlib/RingTheory/Spectrum/Prime/Module.lean` for other results
depending on the Zariski topology.

## TODO
- Connect to associated primes once we have them in mathlib.
- Given an `R`-algebra `f : R → A` and a finite `R`-module `M`,
  `Supp_A (A ⊗ M) = f♯ ⁻¹ Supp M` where `f♯ : Spec A → Spec R`. (stacks#0BUR)
-/

@[expose] public section

-- Basic files in `RingTheory` should avoid depending on the Zariski topology
-- See `Mathlib/RingTheory/Spectrum/Prime/Module.lean`
assert_not_exists TopologicalSpace

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : PrimeSpectrum R}

variable (R M) in
/-- The support of a module, defined as the set of primes `p` such that `Mₚ ≠ 0`. -/
@[stacks 00L1]
/--
Definition of `Module.support` / `Module.support` 的定义

English:
definition Module.support
  signature: : Set (PrimeSpectrum R)
  body: { p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M) }

中文:
定义 Module.support
  签名: : Set (PrimeSpectrum R)
  定义体: { p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M) }

Depends on / 依赖: LocalizedModule, Nontrivial, asIdeal, p.asIdeal.primeCompl, primeCompl
-/
def Module.support : Set (PrimeSpectrum R) :=
  { p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M) }

/--
lemma `Module.mem_support_iff` / 引理 `Module.mem_support_iff`

English:
lemma Module.mem_support_iff
  proof: Iff.rfl

中文:
引理 Module.mem_support_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma Module.mem_support_iff :
    p in Module.support R M ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M) := Iff.rfl

/--
lemma `Module.notMem_support_iff` / 引理 `Module.notMem_support_iff`

English:
lemma Module.notMem_support_iff
  proof: not_nontrivial_iff_subsingleton

中文:
引理 Module.notMem_support_iff
  证明: not_nontrivial_iff_subsingleton

Depends on / 依赖: not_nontrivial_iff_subsingleton
-/
lemma Module.notMem_support_iff :
    p ∉ Module.support R M ↔ Subsingleton (LocalizedModule p.asIdeal.primeCompl M) :=
  not_nontrivial_iff_subsingleton

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Module.notMem_support_iff'` / 引理 `Module.notMem_support_iff'`

English:
lemma Module.notMem_support_iff'
  proof: by
  simp only [notMem_support_iff, Ideal.primeCompl, LocalizedModule.subsingleton_iff,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe]

中文:
引理 Module.notMem_support_iff'
  证明: by
  simp only [notMem_support_iff, Ideal.primeCompl, LocalizedModule.subsingleton_iff,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe]

Depends on / 依赖: Ideal.primeCompl, LocalizedModule, LocalizedModule.subsingleton_iff, Set.mem_compl_iff, SetLike, SetLike.mem_coe, Submonoid, Submonoid.mem_mk, Subsemigroup, Subsemigroup.mem_mk, mem_coe, mem_compl_iff, mem_mk, notMem_support_iff, primeCompl, subsingleton_iff
-/
lemma Module.notMem_support_iff' :
    p ∉ Module.support R M ↔ forall m : M, exists r ∉ p.asIdeal, r • m = 0 := by
  simp only [notMem_support_iff, Ideal.primeCompl, LocalizedModule.subsingleton_iff,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe]

/--
lemma `Module.mem_support_iff'` / 引理 `Module.mem_support_iff'`

English:
lemma Module.mem_support_iff'
  proof: by
  rw [← @not_not (_ in _)]; rw [notMem_support_iff']
  push Not
  rfl

中文:
引理 Module.mem_support_iff'
  证明: by
  rw [← @not_not (_ in _)]; rw [notMem_support_iff']
  push Not
  rfl

Depends on / 依赖: notMem_support_iff, not_not
-/
lemma Module.mem_support_iff' :
    p in Module.support R M ↔ exists m : M, forall r ∉ p.asIdeal, r • m != 0 := by
  rw [← @not_not (_ in _)]; rw [notMem_support_iff']
  push Not
  rfl

/--
lemma `Module.mem_support_iff_exists_annihilator` / 引理 `Module.mem_support_iff_exists_annihilator`

English:
lemma Module.mem_support_iff_exists_annihilator
  proof: by
  rw [Module.mem_support_iff']
  simp_rw [not_imp_not, SetLike.le_def, Submodule.mem_annihilator_span_singleton]

中文:
引理 Module.mem_support_iff_exists_annihilator
  证明: by
  rw [Module.mem_support_iff']
  simp_rw [not_imp_not, SetLike.le_def, Submodule.mem_annihilator_span_singleton]

Depends on / 依赖: Module, Module.mem_support_iff, SetLike, SetLike.le_def, Submodule, Submodule.mem_annihilator_span_singleton, le_def, mem_annihilator_span_singleton, mem_support_iff, not_imp_not, simp_rw
-/
lemma Module.mem_support_iff_exists_annihilator :
    p in Module.support R M ↔ exists m : M, (R ∙ m).annihilator <= p.asIdeal := by
  rw [Module.mem_support_iff']
  simp_rw [not_imp_not, SetLike.le_def, Submodule.mem_annihilator_span_singleton]

/--
lemma `Module.mem_support_mono` / 引理 `Module.mem_support_mono`

English:
lemma Module.mem_support_mono
  given: {p q : PrimeSpectrum R} (H : p <= q) (hp : p in Module.support R M)
  proof: by
  rw [Module.mem_support_iff_exists_annihilator] at hp ⊢
  exact ⟨_, hp.choose_spec.trans H⟩

中文:
引理 Module.mem_support_mono
  条件: {p q : PrimeSpectrum R} (H : p <= q) (hp : p in Module.support R M)
  证明: by
  rw [Module.mem_support_iff_exists_annihilator] at hp ⊢
  exact ⟨_, hp.choose_spec.trans H⟩

Depends on / 依赖: Module, Module.mem_support_iff_exists_annihilator, choose_spec, hp.choose_spec.trans, mem_support_iff_exists_annihilator
-/
lemma Module.mem_support_mono {p q : PrimeSpectrum R} (H : p <= q) (hp : p in Module.support R M) :
    q in Module.support R M := by
  rw [Module.mem_support_iff_exists_annihilator] at hp ⊢
  exact ⟨_, hp.choose_spec.trans H⟩

/--
lemma `Module.mem_support_iff_of_span_eq_top` / 引理 `Module.mem_support_iff_of_span_eq_top`

English:
lemma Module.mem_support_iff_of_span_eq_top
  given: {s : Set M} (hs : Submodule.span R s = ⊤)
  proof: by
  constructor
  · contrapose
    rw [notMem_support_iff]; rw [LocalizedModule.subsingleton_iff_ker_eq_top]; rw [← top_le_iff]; rw [← hs]; rw [Submodule.span_le]; rw [Set.subset_def]
    simp_rw [SetLike.le_def, Submodule.mem_annihilator_span_singleton, SetLike.mem_coe,
      LocalizedModule.mem_k

中文:
引理 Module.mem_support_iff_of_span_eq_top
  条件: {s : Set M} (hs : Submodule.span R s = ⊤)
  证明: by
  constructor
  · contrapose
    rw [notMem_support_iff]; rw [LocalizedModule.subsingleton_iff_ker_eq_top]; rw [← top_le_iff]; rw [← hs]; rw [Submodule.span_le]; rw [Set.subset_def]
    simp_rw [SetLike.le_def, Submodule.mem_annihilator_span_singleton, SetLike.mem_coe,
      LocalizedModule.mem_k

Depends on / 依赖: LocalizedModule, LocalizedModule.mem_ker_mkLinearMap_iff, LocalizedModule.subsingleton_iff_ker_eq_top, Set.subset_def, SetLike, SetLike.le_def, SetLike.mem_coe, Submodule, Submodule.mem_annihilator_span_singleton, Submodule.span_le, and_comm, contrapose, le_def, mem_annihilator_span_singleton, mem_coe, mem_ker_mkLinearMap_iff, mem_support_iff_exists_annihilator, mem_support_iff_exists_annihilator.mpr, notMem_support_iff, simp_rw
-/
lemma Module.mem_support_iff_of_span_eq_top {s : Set M} (hs : Submodule.span R s = ⊤) :
    p in Module.support R M ↔ exists m in s, (R ∙ m).annihilator <= p.asIdeal := by
  constructor
  · contrapose
    rw [notMem_support_iff]; rw [LocalizedModule.subsingleton_iff_ker_eq_top]; rw [← top_le_iff]; rw [← hs]; rw [Submodule.span_le]; rw [Set.subset_def]
    simp_rw [SetLike.le_def, Submodule.mem_annihilator_span_singleton, SetLike.mem_coe,
      LocalizedModule.mem_ker_mkLinearMap_iff]
    push Not
    simp_rw [and_comm]
    exact id
  · intro ⟨m, _, hm⟩
    exact mem_support_iff_exists_annihilator.mpr ⟨m, hm⟩

/--
lemma `Module.annihilator_le_of_mem_support` / 引理 `Module.annihilator_le_of_mem_support`

English:
lemma Module.annihilator_le_of_mem_support
  given: (hp : p in Module.support R M)
  proof: by
  obtain ⟨m, hm⟩ := mem_support_iff_exists_annihilator.mp hp
  exact le_trans ((Submodule.subtype _).annihilator_le_of_injective Subtype.val_injective) hm

中文:
引理 Module.annihilator_le_of_mem_support
  条件: (hp : p in Module.support R M)
  证明: by
  obtain ⟨m, hm⟩ := mem_support_iff_exists_annihilator.mp hp
  exact le_trans ((Submodule.subtype _).annihilator_le_of_injective Subtype.val_injective) hm

Depends on / 依赖: Submodule, Submodule.subtype, Subtype, Subtype.val_injective, annihilator_le_of_injective, le_trans, mem_support_iff_exists_annihilator, mem_support_iff_exists_annihilator.mp, subtype, val_injective
-/
lemma Module.annihilator_le_of_mem_support (hp : p in Module.support R M) :
    Module.annihilator R M <= p.asIdeal := by
  obtain ⟨m, hm⟩ := mem_support_iff_exists_annihilator.mp hp
  exact le_trans ((Submodule.subtype _).annihilator_le_of_injective Subtype.val_injective) hm

/--
lemma `LocalizedModule.subsingleton_iff_support_subset` / 引理 `LocalizedModule.subsingleton_iff_support_subset`

English:
lemma LocalizedModule.subsingleton_iff_support_subset
  given: {f : R}
  proof: by
  rw [LocalizedModule.subsingleton_iff]
  constructor
  · rintro H x hx' f rfl
    obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hx'
    obtain ⟨_, ⟨n, rfl⟩, e⟩ := H m
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n
      (hm ((Submodule.mem_annihilator_span_singleton _ _)

中文:
引理 LocalizedModule.subsingleton_iff_support_subset
  条件: {f : R}
  证明: by
  rw [LocalizedModule.subsingleton_iff]
  constructor
  · rintro H x hx' f rfl
    obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hx'
    obtain ⟨_, ⟨n, rfl⟩, e⟩ := H m
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n
      (hm ((Submodule.mem_annihilator_span_singleton _ _)

Depends on / 依赖: Ideal.IsPrime.mem_of_pow_mem, IsPrime, LocalizedModule, LocalizedModule.subsingleton_iff, Module, Module.mem_support_iff_exists_annihilator.mp, Submodule, Submodule.annihilator_eq_top_iff, Submodule.mem_annihilator_span_singleton, Submodule.s, Submodule.span, Submodule.span_singleton_eq_bot, annihilator, annihilator_eq_top_iff, mem_annihilator_span_singleton, mem_of_pow_mem, mem_support_iff_exists_annihilator, one_mem, span_singleton_eq_bot, subsingleton_iff
-/
lemma LocalizedModule.subsingleton_iff_support_subset {f : R} :
    Subsingleton (LocalizedModule.Away f M) ↔
      Module.support R M subseteq PrimeSpectrum.zeroLocus {f} := by
  rw [LocalizedModule.subsingleton_iff]
  constructor
  · rintro H x hx' f rfl
    obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hx'
    obtain ⟨_, ⟨n, rfl⟩, e⟩ := H m
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n
      (hm ((Submodule.mem_annihilator_span_singleton _ _).mpr e))
  · intro H m
    by_cases h : (Submodule.span R {m}).annihilator = ⊤
    · rw [Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot] at h
      exact ⟨1, one_mem _, by simpa using h⟩
    obtain ⟨n, hn⟩ : f in (Submodule.span R {m}).annihilator.radical := by
      rw [Ideal.radical_eq_sInf]; rw [Ideal.mem_sInf]
      rintro p ⟨hp, hp'⟩
      simpa using H (Module.mem_support_iff_exists_annihilator (p := ⟨p, hp'⟩).mpr ⟨_, hp⟩)
    exact ⟨_, ⟨n, rfl⟩, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩

/--
lemma `Module.support_eq_empty_iff` / 引理 `Module.support_eq_empty_iff`

English:
lemma Module.support_eq_empty_iff
  proof: by
  rw [← Set.subset_empty_iff]; rw [← PrimeSpectrum.zeroLocus_singleton_one]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [LocalizedModule.subsingleton_iff]; rw [subsingleton_iff_forall_eq 0]
  simp only [Submonoid.powers_one, Submonoid.mem_bot, exists_eq_left, one_smul]

中文:
引理 Module.support_eq_empty_iff
  证明: by
  rw [← Set.subset_empty_iff]; rw [← PrimeSpectrum.zeroLocus_singleton_one]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [LocalizedModule.subsingleton_iff]; rw [subsingleton_iff_forall_eq 0]
  simp only [Submonoid.powers_one, Submonoid.mem_bot, exists_eq_left, one_smul]

Depends on / 依赖: LocalizedModule, LocalizedModule.subsingleton_iff, LocalizedModule.subsingleton_iff_support_subset, PrimeSpectrum, PrimeSpectrum.zeroLocus_singleton_one, Set.subset_empty_iff, Submonoid, Submonoid.mem_bot, Submonoid.powers_one, exists_eq_left, mem_bot, one_smul, powers_one, subset_empty_iff, subsingleton_iff, subsingleton_iff_forall_eq, subsingleton_iff_support_subset, zeroLocus_singleton_one
-/
lemma Module.support_eq_empty_iff :
    Module.support R M = ∅ ↔ Subsingleton M := by
  rw [← Set.subset_empty_iff]; rw [← PrimeSpectrum.zeroLocus_singleton_one]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [LocalizedModule.subsingleton_iff]; rw [subsingleton_iff_forall_eq 0]
  simp only [Submonoid.powers_one, Submonoid.mem_bot, exists_eq_left, one_smul]

/--
lemma `Module.nonempty_support_iff` / 引理 `Module.nonempty_support_iff`

English:
lemma Module.nonempty_support_iff
  proof: by
  rw [Set.nonempty_iff_ne_empty]; rw [ne_eq]; rw [Module.support_eq_empty_iff]; rw [← not_subsingleton_iff_nontrivial]

中文:
引理 Module.nonempty_support_iff
  证明: by
  rw [Set.nonempty_iff_ne_empty]; rw [ne_eq]; rw [Module.support_eq_empty_iff]; rw [← not_subsingleton_iff_nontrivial]

Depends on / 依赖: Module, Module.support_eq_empty_iff, Set.nonempty_iff_ne_empty, ne_eq, nonempty_iff_ne_empty, not_subsingleton_iff_nontrivial, support_eq_empty_iff
-/
lemma Module.nonempty_support_iff :
    (Module.support R M).Nonempty ↔ Nontrivial M := by
  rw [Set.nonempty_iff_ne_empty]; rw [ne_eq]; rw [Module.support_eq_empty_iff]; rw [← not_subsingleton_iff_nontrivial]

/--
lemma `Module.nonempty_support_of_nontrivial` / 引理 `Module.nonempty_support_of_nontrivial`

English:
lemma Module.nonempty_support_of_nontrivial
  given: [Nontrivial M]
  statement: (Module.support R M).Nonempty
  proof: Module.nonempty_support_iff.mpr ‹_›

中文:
引理 Module.nonempty_support_of_nontrivial
  条件: [Nontrivial M]
  结论: (Module.support R M).Nonempty
  证明: Module.nonempty_support_iff.mpr ‹_›

Depends on / 依赖: Module, Module.nonempty_support_iff.mpr, nonempty_support_iff
-/
lemma Module.nonempty_support_of_nontrivial [Nontrivial M] : (Module.support R M).Nonempty :=
  Module.nonempty_support_iff.mpr ‹_›

/--
lemma `Module.support_eq_empty` / 引理 `Module.support_eq_empty`

English:
lemma Module.support_eq_empty
  given: [Subsingleton M]
  proof: Module.support_eq_empty_iff.mpr ‹_›

中文:
引理 Module.support_eq_empty
  条件: [Subsingleton M]
  证明: Module.support_eq_empty_iff.mpr ‹_›

Depends on / 依赖: Module, Module.support_eq_empty_iff.mpr, support_eq_empty_iff
-/
lemma Module.support_eq_empty [Subsingleton M] :
    Module.support R M = ∅ :=
  Module.support_eq_empty_iff.mpr ‹_›

/--
lemma `Module.support_of_algebra` / 引理 `Module.support_of_algebra`

English:
lemma Module.support_of_algebra
  given: {A : Type*} [Ring A] [Algebra R A]
  proof: by
  ext p
  simp only [mem_support_iff', ne_eq, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  refine ⟨fun ⟨m, hm⟩ x hx => not_not.mp fun hx' => ?_, fun H => ⟨1, fun r hr e => ?_⟩⟩
  · simpa [Algebra.smul_def, (show _ = _ from hx)] using hm _ hx'
  · exact hr (H ((Algebra.algebraMap_eq_smul

中文:
引理 Module.support_of_algebra
  条件: {A : 类型} [Ring A] [Algebra R A]
  证明: by
  ext p
  simp only [mem_support_iff', ne_eq, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  refine ⟨fun ⟨m, hm⟩ x hx => not_not.mp fun hx' => ?_, fun H => ⟨1, fun r hr e => ?_⟩⟩
  · simpa [Algebra.smul_def, (show _ = _ from hx)] using hm _ hx'
  · exact hr (H ((Algebra.algebraMap_eq_smul

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Algebra.smul_def, PrimeSpectrum, PrimeSpectrum.mem_zeroLocus, SetLike, SetLike.coe_subset_coe, algebraMap_eq_smul_one, coe_subset_coe, mem_support_iff, mem_zeroLocus, ne_eq, not_not, not_not.mp, smul_def
-/
lemma Module.support_of_algebra {A : Type*} [Ring A] [Algebra R A] :
    Module.support R A = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R A)) := by
  ext p
  simp only [mem_support_iff', ne_eq, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  refine ⟨fun ⟨m, hm⟩ x hx => not_not.mp fun hx' => ?_, fun H => ⟨1, fun r hr e => ?_⟩⟩
  · simpa [Algebra.smul_def, (show _ = _ from hx)] using hm _ hx'
  · exact hr (H ((Algebra.algebraMap_eq_smul_one _).trans e))

/--
lemma `Module.support_of_noZeroSMulDivisors` / 引理 `Module.support_of_noZeroSMulDivisors`

English:
lemma Module.support_of_noZeroSMulDivisors
  given: [IsDomain R] [IsTorsionFree R M] [Nontrivial M]
  proof: by
  simp only [Set.eq_univ_iff_forall, mem_support_iff', ne_eq, smul_eq_zero, not_or]
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact fun p => ⟨x, fun r hr => ⟨fun e => hr (e ▸ p.asIdeal.zero_mem), hx⟩⟩

中文:
引理 Module.support_of_noZeroSMulDivisors
  条件: [IsDomain R] [IsTorsionFree R M] [Nontrivial M]
  证明: by
  simp only [Set.eq_univ_iff_forall, mem_support_iff', ne_eq, smul_eq_zero, not_or]
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact fun p => ⟨x, fun r hr => ⟨fun e => hr (e ▸ p.asIdeal.zero_mem), hx⟩⟩

Depends on / 依赖: Set.eq_univ_iff_forall, asIdeal, eq_univ_iff_forall, exists_ne, mem_support_iff, ne_eq, not_or, p.asIdeal.zero_mem, smul_eq_zero, zero_mem
-/
lemma Module.support_of_noZeroSMulDivisors [IsDomain R] [IsTorsionFree R M] [Nontrivial M] :
    Module.support R M = Set.univ := by
  simp only [Set.eq_univ_iff_forall, mem_support_iff', ne_eq, smul_eq_zero, not_or]
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact fun p => ⟨x, fun r hr => ⟨fun e => hr (e ▸ p.asIdeal.zero_mem), hx⟩⟩

variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)

@[stacks 00L3 "(2)"]
/--
lemma `Module.support_subset_of_injective` / 引理 `Module.support_subset_of_injective`

English:
lemma Module.support_subset_of_injective
  given: (hf : Function.Injective f)
  proof: by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  exact ⟨f m, fun r hr => by simpa using hf.ne (hm r hr)⟩

@[stacks 00L3 "(3)"]

中文:
引理 Module.support_subset_of_injective
  条件: (hf : Function.Injective f)
  证明: by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  exact ⟨f m, fun r hr => by simpa using hf.ne (hm r hr)⟩

@[stacks 00L3 "(3)"]

Depends on / 依赖: Set.subset_def, hf.ne, mem_support_iff, simp_rw, subset_def
-/
lemma Module.support_subset_of_injective (hf : Function.Injective f) :
    Module.support R M subseteq Module.support R N := by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  exact ⟨f m, fun r hr => by simpa using hf.ne (hm r hr)⟩

@[stacks 00L3 "(3)"]
/--
lemma `Module.support_subset_of_surjective` / 引理 `Module.support_subset_of_surjective`

English:
lemma Module.support_subset_of_surjective
  given: (hf : Function.Surjective f)
  proof: by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  obtain ⟨m, rfl⟩ := hf m
  exact ⟨m, fun r hr e => hm r hr (by simpa using congr(f $e))⟩

中文:
引理 Module.support_subset_of_surjective
  条件: (hf : Function.Surjective f)
  证明: by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  obtain ⟨m, rfl⟩ := hf m
  exact ⟨m, fun r hr e => hm r hr (by simpa using congr(f $e))⟩

Depends on / 依赖: Set.subset_def, mem_support_iff, simp_rw, subset_def
-/
lemma Module.support_subset_of_surjective (hf : Function.Surjective f) :
    Module.support R N subseteq Module.support R M := by
  simp_rw [Set.subset_def, mem_support_iff']
  rintro x ⟨m, hm⟩
  obtain ⟨m, rfl⟩ := hf m
  exact ⟨m, fun r hr e => hm r hr (by simpa using congr(f $e))⟩

variable {f g} in
/-- Given an exact sequence `0 → M → N → P → 0` of `R`-modules, `Supp N = Supp M ∪ Supp P`. -/
@[stacks 00L3 "(4)"]
/--
lemma `Module.support_of_exact` / 引理 `Module.support_of_exact`

English:
lemma Module.support_of_exact
  statement: (h : Function.Exact f g)
  proof: by
  refine subset_antisymm ?_ (Set.union_subset (Module.support_subset_of_injective f hf)
    (Module.support_subset_of_surjective g hg))
  intro x
  contrapose
  simp only [Set.mem_union, not_or, and_imp, notMem_support_iff']
  intro H₁ H₂ m
  obtain ⟨r, hr, e₁⟩ := H₂ (g m)
  rw [← map_smul]; rw [

中文:
引理 Module.support_of_exact
  结论: (h : Function.Exact f g)
  证明: by
  refine subset_antisymm ?_ (Set.union_subset (Module.support_subset_of_injective f hf)
    (Module.support_subset_of_surjective g hg))
  intro x
  contrapose
  simp only [Set.mem_union, not_or, and_imp, notMem_support_iff']
  intro H₁ H₂ m
  obtain ⟨r, hr, e₁⟩ := H₂ (g m)
  rw [← map_smul]; rw [

Depends on / 依赖: Module, Module.support_subset_of_injective, Module.support_subset_of_surjective, Set.mem_union, Set.union_subset, and_imp, asIdeal, contrapose, map_smul, map_zero, mem_union, mul_mem, mul_smul, notMem_support_iff, not_or, primeCompl, subset_antisymm, support_subset_of_injective, support_subset_of_surjective, union_subset
-/
lemma Module.support_of_exact (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.support R N = Module.support R M union Module.support R P := by
  refine subset_antisymm ?_ (Set.union_subset (Module.support_subset_of_injective f hf)
    (Module.support_subset_of_surjective g hg))
  intro x
  contrapose
  simp only [Set.mem_union, not_or, and_imp, notMem_support_iff']
  intro H₁ H₂ m
  obtain ⟨r, hr, e₁⟩ := H₂ (g m)
  rw [← map_smul]; rw [h] at e₁
  obtain ⟨m', hm'⟩ := e₁
  obtain ⟨s, hs, e₁⟩ := H₁ m'
  exact ⟨_, x.asIdeal.primeCompl.mul_mem hs hr, by rw [mul_smul, ← hm', ← map_smul, e₁, map_zero]⟩

/--
lemma `LinearEquiv.support_eq` / 引理 `LinearEquiv.support_eq`

English:
lemma LinearEquiv.support_eq
  given: (e : M ≃ₗ[R] N)
  proof: (Module.support_subset_of_injective e.toLinearMap e.injective).antisymm
    (Module.support_subset_of_surjective e.toLinearMap e.surjective)

中文:
引理 LinearEquiv.support_eq
  条件: (e : M ≃ₗ[R] N)
  证明: (Module.support_subset_of_injective e.toLinearMap e.injective).antisymm
    (Module.support_subset_of_surjective e.toLinearMap e.surjective)

Depends on / 依赖: Module, Module.support_subset_of_injective, Module.support_subset_of_surjective, antisymm, e.injective, e.surjective, e.toLinearMap, injective, support_subset_of_injective, support_subset_of_surjective, surjective, toLinearMap
-/
lemma LinearEquiv.support_eq (e : M ≃ₗ[R] N) :
    Module.support R M = Module.support R N :=
  (Module.support_subset_of_injective e.toLinearMap e.injective).antisymm
    (Module.support_subset_of_surjective e.toLinearMap e.surjective)

section Finite

variable [Module.Finite R M]

open PrimeSpectrum

/--
lemma `Module.mem_support_iff_of_finite` / 引理 `Module.mem_support_iff_of_finite`

English:
lemma Module.mem_support_iff_of_finite
  proof: by
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  refine ⟨annihilator_le_of_mem_support, fun H => (mem_support_iff_of_span_eq_top hs).mpr ?_⟩
  simp only [SetLike.le_def, Submodule.mem_annihilator_span_singleton] at H ⊢
  contrapose! H
  choose x hx hx' using Subtype.forall'.mp H
  refine ⟨s.attach.prod 

中文:
引理 Module.mem_support_iff_of_finite
  证明: by
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  refine ⟨annihilator_le_of_mem_support, fun H => (mem_support_iff_of_span_eq_top hs).mpr ?_⟩
  simp only [SetLike.le_def, Submodule.mem_annihilator_span_singleton] at H ⊢
  contrapose! H
  choose x hx hx' using Subtype.forall'.mp H
  refine ⟨s.attach.prod 

Depends on / 依赖: Finite, Finset, Finset.dvd_prod_of_mem, Finset.mem_attach, Module, Module.Finite, SetLike, SetLike.le_def, Submodule, Submodule.annihilator_top, Submodule.mem_annihilator_span, Submodule.mem_annihilator_span_singleton, Subtype, Subtype.forall, annihilator_le_of_mem_support, annihilator_top, attach, contrapose, dvd_prod_of_mem, le_def
-/
lemma Module.mem_support_iff_of_finite :
    p in Module.support R M ↔ Module.annihilator R M <= p.asIdeal := by
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  refine ⟨annihilator_le_of_mem_support, fun H => (mem_support_iff_of_span_eq_top hs).mpr ?_⟩
  simp only [SetLike.le_def, Submodule.mem_annihilator_span_singleton] at H ⊢
  contrapose! H
  choose x hx hx' using Subtype.forall'.mp H
  refine ⟨s.attach.prod x, ?_, ?_⟩
  · rw [← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
    intro m
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem x (Finset.mem_attach _ m)
    rw [hk]; rw [mul_comm]; rw [mul_smul]; rw [hx]; rw [smul_zero]
  · exact p.asIdeal.primeCompl.prod_mem (fun x _ => hx' x)

/-- If `M` is `R`-finite, then `Supp M = Z(Ann(M))`. -/
@[stacks 00L2]
/--
lemma `Module.support_eq_zeroLocus` / 引理 `Module.support_eq_zeroLocus`

English:
lemma Module.support_eq_zeroLocus
  proof: Set.ext fun _ => mem_support_iff_of_finite

中文:
引理 Module.support_eq_zeroLocus
  证明: Set.ext fun _ => mem_support_iff_of_finite

Depends on / 依赖: Set.ext, mem_support_iff_of_finite
-/
lemma Module.support_eq_zeroLocus :
    Module.support R M = zeroLocus (Module.annihilator R M) :=
  Set.ext fun _ => mem_support_iff_of_finite

/--
lemma `LocalizedModule.exists_subsingleton_away` / 引理 `LocalizedModule.exists_subsingleton_away`

English:
lemma LocalizedModule.exists_subsingleton_away
  statement: (p : Ideal R) [p.IsPrime]
  proof: by
  have : ⟨p, inferInstance⟩ in (Module.support R M)ᶜ := by
    simpa [Module.notMem_support_iff]
  rw [Module.support_eq_zeroLocus]; rw [← Set.biUnion_of_singleton (Module.annihilator R M : Set R)]; rw [PrimeSpectrum.zeroLocus_iUnion₂]; rw [Set.compl_iInter₂]; rw [Set.mem_iUnion₂] at this
  obtai

中文:
引理 LocalizedModule.exists_subsingleton_away
  结论: (p : Ideal R) [p.IsPrime]
  证明: by
  have : ⟨p, inferInstance⟩ in (Module.support R M)ᶜ := by
    simpa [Module.notMem_support_iff]
  rw [Module.support_eq_zeroLocus]; rw [← Set.biUnion_of_singleton (Module.annihilator R M : Set R)]; rw [PrimeSpectrum.zeroLocus_iUnion₂]; rw [Set.compl_iInter₂]; rw [Set.mem_iUnion₂] at this
  obtai

Depends on / 依赖: Module, Module.annihilator, Module.mem_annihilator.mp, Module.notMem_support_iff, Module.support, Module.support_eq_zeroLocus, PrimeSpectrum, PrimeSpectrum.zeroLocus_iUnion, Set.biUnion_of_singleton, Set.compl_iInter, Set.mem_iUnion, Submonoid, Submonoid.mem_powers, annihilator, biUnion_of_singleton, mem_annihilator, mem_powers, notMem_support_iff, subsingleton_iff, subsingleton_iff.mpr
-/
lemma LocalizedModule.exists_subsingleton_away (p : Ideal R) [p.IsPrime]
    [Subsingleton (LocalizedModule p.primeCompl M)] :
    exists f ∉ p, Subsingleton (LocalizedModule.Away f M) := by
  have : ⟨p, inferInstance⟩ in (Module.support R M)ᶜ := by
    simpa [Module.notMem_support_iff]
  rw [Module.support_eq_zeroLocus]; rw [← Set.biUnion_of_singleton (Module.annihilator R M : Set R)]; rw [PrimeSpectrum.zeroLocus_iUnion₂]; rw [Set.compl_iInter₂]; rw [Set.mem_iUnion₂] at this
  obtain ⟨f, hf, hf'⟩ := this
  exact ⟨f, by simpa using hf', subsingleton_iff.mpr
    fun m => ⟨f, Submonoid.mem_powers f, Module.mem_annihilator.mp hf _⟩⟩

/--
lemma `IsLocalizedModule.exists_subsingleton_away` / 引理 `IsLocalizedModule.exists_subsingleton_away`

English:
lemma IsLocalizedModule.exists_subsingleton_away
  statement: {M' : Type*} [AddCommMonoid M'] [Module R M']
  proof: by
  let e := IsLocalizedModule.iso p.primeCompl l
  have : Subsingleton (LocalizedModule p.primeCompl M) := e.subsingleton
  exact LocalizedModule.exists_subsingleton_away p

中文:
引理 IsLocalizedModule.exists_subsingleton_away
  结论: {M' : 类型} [AddCommMonoid M'] [Module R M']
  证明: by
  let e := IsLocalizedModule.iso p.primeCompl l
  have : Subsingleton (LocalizedModule p.primeCompl M) := e.subsingleton
  exact LocalizedModule.exists_subsingleton_away p

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.iso, LocalizedModule, LocalizedModule.exists_subsingleton_away, Subsingleton, e.subsingleton, exists_subsingleton_away, p.primeCompl, primeCompl, subsingleton
-/
lemma IsLocalizedModule.exists_subsingleton_away {M' : Type*} [AddCommMonoid M'] [Module R M']
    (l : M ->ₗ[R] M') (p : Ideal R) [p.IsPrime] [IsLocalizedModule p.primeCompl l]
    [Subsingleton M'] :
    exists f ∉ p, Subsingleton (LocalizedModule.Away f M) := by
  let e := IsLocalizedModule.iso p.primeCompl l
  have : Subsingleton (LocalizedModule p.primeCompl M) := e.subsingleton
  exact LocalizedModule.exists_subsingleton_away p

/--
lemma `Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective` / 引理 `Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective`

English:
lemma Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective
  statement: (p : Ideal R)
  proof: by
  simp_rw [φ.localizedMap_surjective_iff_subsingleton_localized_coker] at hφ ⊢
  exact LocalizedModule.exists_subsingleton_away p

中文:
引理 Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective
  结论: (p : Ideal R)
  证明: by
  simp_rw [φ.localizedMap_surjective_iff_subsingleton_localized_coker] at hφ ⊢
  exact LocalizedModule.exists_subsingleton_away p

Depends on / 依赖: LocalizedModule, LocalizedModule.exists_subsingleton_away, exists_subsingleton_away, localizedMap_surjective_iff_subsingleton_localized_coker, simp_rw
-/
lemma Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective (p : Ideal R)
    [p.IsPrime] (φ : N ->ₗ[R] M) (hφ : Function.Surjective (LocalizedModule.map p.primeCompl φ)) :
    exists a ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ) := by
  simp_rw [φ.localizedMap_surjective_iff_subsingleton_localized_coker] at hφ ⊢
  exact LocalizedModule.exists_subsingleton_away p

/-- `Supp(M/IM) = Supp(M) ∩ Z(I)`. -/
@[stacks 00L3 "(1)"]
/--
theorem `Module.support_quotient` / 定理 `Module.support_quotient`

English:
theorem Module.support_quotient
  given: (I : Ideal R)
  proof: by
  apply subset_antisymm
  · refine Set.subset_inter ?_ ?_
    · exact Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)
    · rw [support_eq_zeroLocus]
      apply PrimeSpectrum.zeroLocus_anti_mono_ideal
      rw [Submodule.annihilator_quotient]
      exact fun x hx => Submodule.

中文:
定理 Module.support_quotient
  条件: (I : Ideal R)
  证明: by
  apply subset_antisymm
  · refine Set.subset_inter ?_ ?_
    · exact Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)
    · rw [support_eq_zeroLocus]
      apply PrimeSpectrum.zeroLocus_anti_mono_ideal
      rw [Submodule.annihilator_quotient]
      exact fun x hx => Submodule.

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, LocalizedModul, LocalizedModule, Module, Module.mem_support_iff, Module.support_subset_of_surjective, PrimeSpectrum, PrimeSpectrum.zeroLocus_anti_mono_ideal, Set.subset_inter, Submodule, Submodule.annihilator_quotient, Submodule.mem_colon.mpr, Submodule.mkQ_surjective, Submodule.smul_mem_smul, annihilator_quotient, asIdeal, mem_colon, mem_support_iff
-/
theorem Module.support_quotient (I : Ideal R) :
    support R (M ⧸ (I • ⊤ : Submodule R M)) = support R M inter zeroLocus I := by
  apply subset_antisymm
  · refine Set.subset_inter ?_ ?_
    · exact Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)
    · rw [support_eq_zeroLocus]
      apply PrimeSpectrum.zeroLocus_anti_mono_ideal
      rw [Submodule.annihilator_quotient]
      exact fun x hx => Submodule.mem_colon.mpr fun p hp => Submodule.smul_mem_smul hx hp
  · rintro p ⟨hp₁, hp₂⟩
    rw [Module.mem_support_iff] at hp₁ ⊢
    let Rₚ := Localization.AtPrime p.asIdeal
    let Mₚ := LocalizedModule p.asIdeal.primeCompl M
    set Mₚ' := LocalizedModule p.asIdeal.primeCompl (M ⧸ (I • ⊤ : Submodule R M))
    let Mₚ'' := Mₚ ⧸ I.map (algebraMap R Rₚ) • (⊤ : Submodule Rₚ Mₚ)
    let e : Mₚ' ≃ₗ[Rₚ] Mₚ'' := (localizedQuotientEquiv _ _).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (by rw [Submodule.localized,
        Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top])
    have : Nontrivial Mₚ'' := by
      rw [Submodule.Quotient.nontrivial_iff]; rw [ne_comm]
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      refine trans ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hp₂
    exact e.nontrivial

open scoped Pointwise in
@[simp]
/--
theorem `Module.support_quotSMulTop` / 定理 `Module.support_quotSMulTop`

English:
theorem Module.support_quotSMulTop
  given: (x : R)
  proof: (x • (⊤ : Submodule R M)).quotEquivOfEq (Ideal.span {x} • ⊤)
.support_eq.trans ((⊤ : Submodule R M).ideal_span_singleton_smul x).symm
(support_quotient _).trans by rw [zeroLocus_span]

中文:
定理 Module.support_quotSMulTop
  条件: (x : R)
  证明: (x • (⊤ : Submodule R M)).quotEquivOfEq (Ideal.span {x} • ⊤)
.support_eq.trans ((⊤ : Submodule R M).ideal_span_singleton_smul x).symm
(support_quotient _).trans by rw [zeroLocus_span]

Depends on / 依赖: Ideal.span, Submodule, ideal_span_singleton_smul, quotEquivOfEq, support_eq, support_eq.trans, support_quotient, zeroLocus_span
-/
theorem Module.support_quotSMulTop (x : R) :
    support R (QuotSMulTop x M) = support R M inter zeroLocus {x} :=
  (x • (⊤ : Submodule R M)).quotEquivOfEq (Ideal.span {x} • ⊤)
.support_eq.trans ((⊤ : Submodule R M).ideal_span_singleton_smul x).symm
(support_quotient _).trans by rw [zeroLocus_span]

end Finite
