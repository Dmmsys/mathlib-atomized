/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic

/-!

# Weakly Quasi-finite primes

The definition `Algebra.QuasiFiniteAt` is equivalent to the usual definition "isolated in fibers"
mathematically for algebras of finite type, but this requires Zariski's main theorem to prove.
Hence we introduce a weaker notion of being `Algebra.WeaklyQuasiFiniteAt` that we shall state
Zariski's main theorem in terms of, and deduce from this that `Algebra.WeaklyQuasiFiniteAt` is
equivalent to `Algebra.QuasiFiniteAt` under all relevant scenarios.

This class should only be used in stating (and proving) Zariski's main theorem and should not be
used elsewhere, and all public API shall have a `Algebra.QuasiFiniteAt` version.

## Implementation details

The definition of `Algebra.QuasiFiniteAt R q` as is says that the whole `S_q` is quasi-finite,
which requires not only `q` to be quasi-finite, but also all primes below it (i.e. all generic
points that specialize to it) to also be quasi-finite.
This is fine mathematically because the set of quasi-finite primes is open
(according to Zariski's Main theorem). But this requires the statement of Zariski's main
to be stated with an a priori weaker notion of quasi-finite.
Hence we introduce `Algebra.WeaklyQuasiFiniteAt` where we mod out all the primes that lie in a
different fiber.

-/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T]
variable (p : Ideal R) (q : Ideal S) [q.IsPrime]

variable (R) in
/--
Definition of `Algebra.WeaklyQuasiFiniteAt` / `Algebra.WeaklyQuasiFiniteAt` 的定义

English:
abbreviation Algebra.WeaklyQuasiFiniteAt
  body: Algebra.QuasiFiniteAt R (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S))))

中文:
缩写 代数.WeaklyQuasiFiniteAt
  定义体: Algebra.QuasiFiniteAt R (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S))))

Depends on / 依赖: Algebra, Algebra.QuasiFiniteAt, Ideal.Quotient.mk, QuasiFiniteAt, Quotient, algebraMap, q.map, q.under
-/
abbrev Algebra.WeaklyQuasiFiniteAt :=
  Algebra.QuasiFiniteAt R (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S))))

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Algebra.weaklyQuasiFiniteAt_iff` / 引理 `Algebra.weaklyQuasiFiniteAt_iff`

English:
lemma Algebra.weaklyQuasiFiniteAt_iff
  proof: by
  let q' := q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))
  have hq' : q = q'.comap (Ideal.Quotient.mk _) := .trans
    (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
    (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  let φ₁ : Localization.AtPrime q ->ₐ[R] Localization.AtPrime q' :=
    Localization.localAlgHom _ _ (Ideal.Quotient.mkₐ _ _) hq'
  have hφ₁ : Function.Surjective φ₁ :=
    (RingHom.surjectiveOnStalks_of_surjective
      Ideal.Quotient.mk_surjective).localRingHom_surjective _ _ hq'
  refine Algebra.QuasiFinite.iff_of_algEquiv ((Ideal.quotientEquivAlg _ _ (.refl) ?_).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ₁)).symm
  ext x
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  simp [φ₁, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map,
    IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_eq_zero_iff,
    Ideal.Quotient.mk_surjective.exists, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    ← Ideal.mem_comap, ← hq']

中文:
引理 代数.weaklyQuasiFiniteAt_iff
  证明: by
  let q' := q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))
  have hq' : q = q'.comap (Ideal.Quotient.mk _) := .trans
    (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
    (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  let φ₁ : Localization.AtPrime q ->ₐ[R] Localization.AtPrime q' :=
    Localization.localAlgHom _ _ (Ideal.Quotient.mkₐ _ _) hq'
  have hφ₁ : Function.Surjective φ₁ :=
    (RingHom.surjectiveOnStalks_of_surjective
      Ideal.Quotient.mk_surjective).localRingHom_surjective _ _ hq'
  refine Algebra.QuasiFinite.iff_of_algEquiv ((Ideal.quotientEquivAlg _ _ (.refl) ?_).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ₁)).symm
  ext x
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  simp [φ₁, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map,
    IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_eq_zero_iff,
    Ideal.Quotient.mk_surjective.exists, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    ← Ideal.mem_comap, ← hq']

Depends on / 依赖: AtPrime, Function, Function.Surjective, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.comap_map_of_surjective, Ideal.map_comap_le, Localization, Localization.AtPrime, Localization.localAlgHom, Quotient, RingHom, RingHom.ker_eq_comap_bot, RingHom.surjectiveOnStalks_of_surjective, Surjective, algebraMap, comap_map_of_surjective, ker_eq_comap_bot, localAlgHom, localRin
-/
lemma Algebra.weaklyQuasiFiniteAt_iff :
    Algebra.WeaklyQuasiFiniteAt R q ↔
      Algebra.QuasiFinite R (Localization.AtPrime q ⧸
        (q.under R).map (algebraMap R (Localization.AtPrime q))) := by
  let q' := q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))
  have hq' : q = q'.comap (Ideal.Quotient.mk _) := .trans
    (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
    (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  let φ₁ : Localization.AtPrime q ->ₐ[R] Localization.AtPrime q' :=
    Localization.localAlgHom _ _ (Ideal.Quotient.mkₐ _ _) hq'
  have hφ₁ : Function.Surjective φ₁ :=
    (RingHom.surjectiveOnStalks_of_surjective
      Ideal.Quotient.mk_surjective).localRingHom_surjective _ _ hq'
  refine Algebra.QuasiFinite.iff_of_algEquiv ((Ideal.quotientEquivAlg _ _ (.refl) ?_).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ₁)).symm
  ext x
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  simp [φ₁, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map,
    IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_eq_zero_iff,
    Ideal.Quotient.mk_surjective.exists, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    ← Ideal.mem_comap, ← hq']

namespace Algebra.WeaklyQuasiFiniteAt

instance (priority := low) [QuasiFiniteAt R q] : WeaklyQuasiFiniteAt R q := by
  rw [weaklyQuasiFiniteAt_iff]
  exact .of_surjective_algHom (Ideal.Quotient.mkₐ _ _) Ideal.Quotient.mk_surjective

/--
lemma `of_algHom_localization` / 引理 `of_algHom_localization`

English:
lemma of_algHom_localization
  statement: (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p]
  proof: by
  rw [weaklyQuasiFiniteAt_iff] at *
  have H : (p.under R).map (algebraMap R _) <=
      ((q.under R).map (algebraMap R _)).comap f.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]; rw [Ideal.comap_comap]; rw [AlgHom.toRingHom_eq_coe]; rw [AlgHom.comp_algebraMap_of_tower]
    grw [← Ideal.le_comap_map]
    intro x hx
    by_contra hx'
    have : IsLocalHom f.toRingHom := .of_surjective _ hf
    have := this.1 (algebraMap _ _ x) (by
      suffices IsUnit (IsLocalization.mk' (M := q.primeCompl) (Localization.AtPrime q)
        (algebraMap _ _ x) 1) by simpa [IsLocalization.mk'_one] using! this
      simpa [IsLocalization.AtPrime.isUnit_mk'_iff])
    exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime p) p
      (algebraMap _ _ x) 1).mp (by simpa [IsLocalization.mk'_one]) hx
  exact .of_surjective_algHom (S := Localization.AtPrime p ⧸
    (p.under R).map (algebraMap R (Localization.AtPrime p))) (Ideal.quotientMapₐ _ f H)
    (Ideal.quotientMap_surjective (H := H) hf)

中文:
引理 of_algHom_localization
  结论: (p : 理想 S) [p.是素] [WeaklyQuasiFiniteAt R p]
  证明: by
  rw [weaklyQuasiFiniteAt_iff] at *
  have H : (p.under R).map (algebraMap R _) <=
      ((q.under R).map (algebraMap R _)).comap f.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]; rw [Ideal.comap_comap]; rw [AlgHom.toRingHom_eq_coe]; rw [AlgHom.comp_algebraMap_of_tower]
    grw [← Ideal.le_comap_map]
    intro x hx
    by_contra hx'
    have : IsLocalHom f.toRingHom := .of_surjective _ hf
    have := this.1 (algebraMap _ _ x) (by
      suffices IsUnit (IsLocalization.mk' (M := q.primeCompl) (Localization.AtPrime q)
        (algebraMap _ _ x) 1) by simpa [IsLocalization.mk'_one] using! this
      simpa [IsLocalization.AtPrime.isUnit_mk'_iff])
    exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime p) p
      (algebraMap _ _ x) 1).mp (by simpa [IsLocalization.mk'_one]) hx
  exact .of_surjective_algHom (S := Localization.AtPrime p ⧸
    (p.under R).map (algebraMap R (Localization.AtPrime p))) (Ideal.quotientMapₐ _ f H)
    (Ideal.quotientMap_surjective (H := H) hf)

Depends on / 依赖: AlgHom, AlgHom.comp_algebraMap_of_tower, AlgHom.toRingHom_eq_coe, AtPrime, Ideal.comap_comap, Ideal.le_comap_map, Ideal.map_le_iff_le_comap, IsLocalHom, IsLocalization, IsLocalization.mk, IsUnit, Localization, Localization.AtPrime, algebraMap, comap_comap, comp_algebraMap_of_tower, f.toRingHom, le_comap_map, map_le_iff_le_comap, of_surjective
-/
lemma of_algHom_localization (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p]
    (q : Ideal T) [q.IsPrime]
    (f : Localization.AtPrime p ->ₐ[R] Localization.AtPrime q) (hf : Function.Surjective f) :
    WeaklyQuasiFiniteAt R q := by
  rw [weaklyQuasiFiniteAt_iff] at *
  have H : (p.under R).map (algebraMap R _) <=
      ((q.under R).map (algebraMap R _)).comap f.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]; rw [Ideal.comap_comap]; rw [AlgHom.toRingHom_eq_coe]; rw [AlgHom.comp_algebraMap_of_tower]
    grw [← Ideal.le_comap_map]
    intro x hx
    by_contra hx'
    have : IsLocalHom f.toRingHom := .of_surjective _ hf
    have := this.1 (algebraMap _ _ x) (by
      suffices IsUnit (IsLocalization.mk' (M := q.primeCompl) (Localization.AtPrime q)
        (algebraMap _ _ x) 1) by simpa [IsLocalization.mk'_one] using! this
      simpa [IsLocalization.AtPrime.isUnit_mk'_iff])
    exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime p) p
      (algebraMap _ _ x) 1).mp (by simpa [IsLocalization.mk'_one]) hx
  exact .of_surjective_algHom (S := Localization.AtPrime p ⧸
    (p.under R).map (algebraMap R (Localization.AtPrime p))) (Ideal.quotientMapₐ _ f H)
    (Ideal.quotientMap_surjective (H := H) hf)

/--
lemma `of_surjectiveOnStalks` / 引理 `of_surjectiveOnStalks`

English:
lemma of_surjectiveOnStalks
  proof: by
  subst hq
  exact of_algHom_localization _ _ (Localization.localAlgHom _ _ f rfl) (hf _ _)

中文:
引理 of_surjectiveOnStalks
  证明: by
  subst hq
  exact of_algHom_localization _ _ (Localization.localAlgHom _ _ f rfl) (hf _ _)

Depends on / 依赖: Localization, Localization.localAlgHom, localAlgHom, of_algHom_localization
-/
lemma of_surjectiveOnStalks
    (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p] (q : Ideal T) [q.IsPrime]
    (f : S ->ₐ[R] T) (hf : f.SurjectiveOnStalks) (hq : p = Ideal.comap f q) :
    WeaklyQuasiFiniteAt R q := by
  subst hq
  exact of_algHom_localization _ _ (Localization.localAlgHom _ _ f rfl) (hf _ _)

/--
Instance `comap_algEquiv` / 实例 `comap_algEquiv`

English:
instance comap_algEquiv
  signature: (p : Ideal S) [p.IsPrime]
  body: .of_surjectiveOnStalks p _ f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) (by ext; simp)

中文:
实例 comap_algEquiv
  签名: (p : 理想 S) [p.是素]
  定义体: .of_surjectiveOnStalks p _ f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) (by ext; simp)

Depends on / 依赖: RingHom, RingHom.surjectiveOnStalks_of_surjective, f.symm.surjective, f.symm.toAlgHom, of_surjectiveOnStalks, surjective, surjectiveOnStalks_of_surjective, toAlgHom
-/
instance comap_algEquiv (p : Ideal S) [p.IsPrime]
    [Algebra.WeaklyQuasiFiniteAt R p]
    (f : T ≃ₐ[R] S) : WeaklyQuasiFiniteAt R (p.comap f.toRingHom) :=
  .of_surjectiveOnStalks p _ f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) (by ext; simp)

/--
lemma `finite_residueField` / 引理 `finite_residueField`

English:
lemma finite_residueField
  proof: by
  let r := q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))
  have : r.LiesOver q :=
    ⟨.trans (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
    (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver q r
  have : r.LiesOver p := .trans _ q _
  let := Localization.AtPrime.algebraOfLiesOver p r
  exact .of_injective (IsScalarTower.toAlgHom _ _ r.ResidueField).toLinearMap (RingHom.injective _)

中文:
引理 finite_residueField
  证明: by
  let r := q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))
  have : r.LiesOver q :=
    ⟨.trans (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
    (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver q r
  have : r.LiesOver p := .trans _ q _
  let := Localization.AtPrime.algebraOfLiesOver p r
  exact .of_injective (IsScalarTower.toAlgHom _ _ r.ResidueField).toLinearMap (RingHom.injective _)

Depends on / 依赖: AtPrime, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.comap_map_of_surjective, Ideal.map_comap_le, IsScalarTower, IsScalarTower.toAlgHom, LiesOver, Localization, Localization.AtPrime.algebraOfLiesOver, Quotient, ResidueField, RingHom, RingHom.injective, RingHom.ker_eq_comap_bot, algebraMap, algebraOfLiesOver, comap_map_of_surjective, injective, ker_eq_comap_bot
-/
lemma finite_residueField
    [p.IsPrime] [q.LiesOver p] [WeaklyQuasiFiniteAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Module.Finite p.ResidueField q.ResidueField := by
  let r := q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))
  have : r.LiesOver q :=
    ⟨.trans (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
    (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver q r
  have : r.LiesOver p := .trans _ q _
  let := Localization.AtPrime.algebraOfLiesOver p r
  exact .of_injective (IsScalarTower.toAlgHom _ _ r.ResidueField).toLinearMap (RingHom.injective _)

/--
lemma `finite_locoalization` / 引理 `finite_locoalization`

English:
lemma finite_locoalization
  given: {K : Type*} [Field K] [Algebra K S] [WeaklyQuasiFiniteAt K q]
  proof: by
  have H : Algebra.WeaklyQuasiFiniteAt K q := ‹_›
  rw [Algebra.weaklyQuasiFiniteAt_iff]; rw [← Ideal.over_def q ⊥]; rw [Ideal.map_bot] at H
  have : QuasiFinite K (Localization.AtPrime q) := .of_surjective_algHom
    (AlgEquiv.quotientBot K _).toAlgHom (AlgEquiv.quotientBot K _).surjective
  exact .of_quasiFinite

中文:
引理 finite_locoalization
  条件: {K : 类型} [域 K] [代数 K S] [WeaklyQuasiFiniteAt K q]
  证明: by
  have H : Algebra.WeaklyQuasiFiniteAt K q := ‹_›
  rw [Algebra.weaklyQuasiFiniteAt_iff]; rw [← Ideal.over_def q ⊥]; rw [Ideal.map_bot] at H
  have : QuasiFinite K (Localization.AtPrime q) := .of_surjective_algHom
    (AlgEquiv.quotientBot K _).toAlgHom (AlgEquiv.quotientBot K _).surjective
  exact .of_quasiFinite

Depends on / 依赖: AlgEquiv, AlgEquiv.quotientBot, Algebra, Algebra.WeaklyQuasiFiniteAt, Algebra.weaklyQuasiFiniteAt_iff, AtPrime, Ideal.map_bot, Ideal.over_def, Localization, Localization.AtPrime, QuasiFinite, WeaklyQuasiFiniteAt, map_bot, of_quasiFinite, of_surjective_algHom, over_def, quotientBot, surjective, toAlgHom, weaklyQuasiFiniteAt_iff
-/
lemma finite_locoalization {K : Type*} [Field K] [Algebra K S] [WeaklyQuasiFiniteAt K q] :
    Module.Finite K (Localization.AtPrime q) := by
  have H : Algebra.WeaklyQuasiFiniteAt K q := ‹_›
  rw [Algebra.weaklyQuasiFiniteAt_iff]; rw [← Ideal.over_def q ⊥]; rw [Ideal.map_bot] at H
  have : QuasiFinite K (Localization.AtPrime q) := .of_surjective_algHom
    (AlgEquiv.quotientBot K _).toAlgHom (AlgEquiv.quotientBot K _).surjective
  exact .of_quasiFinite

/--
lemma `eq_of_le_of_under_eq` / 引理 `eq_of_le_of_under_eq`

English:
lemma eq_of_le_of_under_eq
  statement: {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
  proof: by
  have : (P.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa [← h₂] using Ideal.map_comap_le)
  have := QuasiFiniteAt.eq_of_le_of_under_eq (R := R)
    (P := P.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S))))
    (Q := Q.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S))))
    (Ideal.map_mono h₁) (by
      rw [← Ideal.under_under (B := S)]; rw [← Ideal.under_under (A := R) (B := S) (C := S ⧸ _)]
      dsimp [Ideal.under] at h₂ ⊢
      simp [Ideal.map_comap_le]
      simp [Ideal.map_comap_le, ← h₂])
  replace this := (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm.trans
    congr($(this).comap _)
  simp [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.map_comap_le] at this
  simpa [Ideal.map_comap_le, ← h₂] using this

中文:
引理 eq_of_le_of_under_eq
  结论: {P Q : 理想 S} [P.是素] [Q.是素]
  证明: by
  have : (P.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa [← h₂] using Ideal.map_comap_le)
  have := QuasiFiniteAt.eq_of_le_of_under_eq (R := R)
    (P := P.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S))))
    (Q := Q.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S))))
    (Ideal.map_mono h₁) (by
      rw [← Ideal.under_under (B := S)]; rw [← Ideal.under_under (A := R) (B := S) (C := S ⧸ _)]
      dsimp [Ideal.under] at h₂ ⊢
      simp [Ideal.map_comap_le]
      simp [Ideal.map_comap_le, ← h₂])
  replace this := (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm.trans
    congr($(this).comap _)
  simp [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.map_comap_le] at this
  simpa [Ideal.map_comap_le, ← h₂] using this

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.map_comap_le, Ideal.map_isPrime_of_surjective, Ideal.map_mono, Ideal.under_under, IsPrime, P.map, Q.map, Q.under, QuasiFiniteAt, QuasiFiniteAt.eq_of_le_of_under_eq, Quotient, algebraMap, eq_of_le_of_under_eq, map_comap_le, map_isPrime_of_surjective, map_mono, mk_surjective, under_under
-/
lemma eq_of_le_of_under_eq {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
    (h₁ : P <= Q) (h₂ : P.under R = Q.under R) [WeaklyQuasiFiniteAt R Q] :
    P = Q := by
  have : (P.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa [← h₂] using Ideal.map_comap_le)
  have := QuasiFiniteAt.eq_of_le_of_under_eq (R := R)
    (P := P.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S))))
    (Q := Q.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S))))
    (Ideal.map_mono h₁) (by
      rw [← Ideal.under_under (B := S)]; rw [← Ideal.under_under (A := R) (B := S) (C := S ⧸ _)]
      dsimp [Ideal.under] at h₂ ⊢
      simp [Ideal.map_comap_le]
      simp [Ideal.map_comap_le, ← h₂])
  replace this := (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm.trans
    congr($(this).comap _)
  simp [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.map_comap_le] at this
  simpa [Ideal.map_comap_le, ← h₂] using this

open _root_.TensorProduct in
/--
lemma `baseChange` / 引理 `baseChange`

English:
lemma baseChange
  statement: (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p]
  proof: by
  delta WeaklyQuasiFiniteAt at *
  let φ : A otimes[R] S ->ₐ[A] (A ⧸ q.under A) otimes[R] (S ⧸ (p.under R).map (algebraMap R S)) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ _ _) (Ideal.Quotient.mkₐ _ _)
  have hφ₁ : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective
  have hφ₂ : RingHom.ker φ.toRingHom = (q.under A).map (algebraMap _ _) := by
    refine (Algebra.TensorProduct.map_ker _ _
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective).trans ?_
    rw [← RingHom.ker_coe_toRingHom]; rw [← RingHom.ker_coe_toRingHom (F := AlgHom _ _ _)]; rw [← Ideal.map_coe]; rw [← Ideal.map_coe (F := AlgHom _ _ _)]
    simp only [Ideal.under, Ideal.Quotient.mkₐ_ker, hq, AlgHom.toRingHom_eq_coe, Ideal.comap_comap,
      AlgHom.comp_algebraMap_of_tower, Ideal.map_map]
    refine sup_eq_left.mpr ?_
    simp only [← TensorProduct.includeLeft.comp_algebraMap, ← Ideal.map_map, ← Ideal.comap_comap]
    exact Ideal.map_mono Ideal.map_comap_le
  have hφ₃ : φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (Ideal.Quotient.mk _) := rfl
  have : (Ideal.map φ.toRingHom q).IsPrime :=
Ideal.map_isPrime_of_surjective ‹_› hφ₂.trans_le Ideal.map_comap_le
  have := QuasiFiniteAt.baseChange (R := R) (S := _) (A := A ⧸ q.under A)
    (p.map (Ideal.Quotient.mk ((p.under R).map (algebraMap R S)))) (q.map φ.toRingHom) (by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_comap,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr Ideal.map_comap_le,
      ← hφ₃, ← Ideal.comap_comap, Ideal.comap_map_of_surjective _ (by exact hφ₁),
      ← RingHom.ker_eq_comap_bot, hφ₂, sup_eq_left.mpr Ideal.map_comap_le])
  have : QuasiFiniteAt A (q.map φ.toRingHom) := .trans _ (A ⧸ q.under A) _
  let e := (Ideal.quotientEquivAlg ((q.under A).map (algebraMap _ _)) _ (.refl) (by simpa)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ₁)
  refine .of_surjectiveOnStalks (q.map φ.toRingHom) e.symm.toAlgHom
    e.symm.toRingEquiv.surjectiveOnStalks _ ?_
  erw [Ideal.comap_symm] -- This should be fixed once `Ideal.map` does not take homclasses.
  rw [← Ideal.map_coe e.toRingEquiv]; rw [Ideal.map_map]
  rfl

中文:
引理 baseChange
  结论: (p : 理想 S) [p.是素] [WeaklyQuasiFiniteAt R p]
  证明: by
  delta WeaklyQuasiFiniteAt at *
  let φ : A otimes[R] S ->ₐ[A] (A ⧸ q.under A) otimes[R] (S ⧸ (p.under R).map (algebraMap R S)) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ _ _) (Ideal.Quotient.mkₐ _ _)
  have hφ₁ : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective
  have hφ₂ : RingHom.ker φ.toRingHom = (q.under A).map (algebraMap _ _) := by
    refine (Algebra.TensorProduct.map_ker _ _
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective).trans ?_
    rw [← RingHom.ker_coe_toRingHom]; rw [← RingHom.ker_coe_toRingHom (F := AlgHom _ _ _)]; rw [← Ideal.map_coe]; rw [← Ideal.map_coe (F := AlgHom _ _ _)]
    simp only [Ideal.under, Ideal.Quotient.mkₐ_ker, hq, AlgHom.toRingHom_eq_coe, Ideal.comap_comap,
      AlgHom.comp_algebraMap_of_tower, Ideal.map_map]
    refine sup_eq_left.mpr ?_
    simp only [← TensorProduct.includeLeft.comp_algebraMap, ← Ideal.map_map, ← Ideal.comap_comap]
    exact Ideal.map_mono Ideal.map_comap_le
  have hφ₃ : φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (Ideal.Quotient.mk _) := rfl
  have : (Ideal.map φ.toRingHom q).IsPrime :=
Ideal.map_isPrime_of_surjective ‹_› hφ₂.trans_le Ideal.map_comap_le
  have := QuasiFiniteAt.baseChange (R := R) (S := _) (A := A ⧸ q.under A)
    (p.map (Ideal.Quotient.mk ((p.under R).map (algebraMap R S)))) (q.map φ.toRingHom) (by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_comap,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr Ideal.map_comap_le,
      ← hφ₃, ← Ideal.comap_comap, Ideal.comap_map_of_surjective _ (by exact hφ₁),
      ← RingHom.ker_eq_comap_bot, hφ₂, sup_eq_left.mpr Ideal.map_comap_le])
  have : QuasiFiniteAt A (q.map φ.toRingHom) := .trans _ (A ⧸ q.under A) _
  let e := (Ideal.quotientEquivAlg ((q.under A).map (algebraMap _ _)) _ (.refl) (by simpa)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ₁)
  refine .of_surjectiveOnStalks (q.map φ.toRingHom) e.symm.toAlgHom
    e.symm.toRingEquiv.surjectiveOnStalks _ ?_
  erw [Ideal.comap_symm] -- This should be fixed once `Ideal.map` does not take homclasses.
  rw [← Ideal.map_coe e.toRingEquiv]; rw [Ideal.map_map]
  rfl

Depends on / 依赖: Algebra, Algebra.TensorProduct.map, Algebra.TensorProduct.map_ker, Algebra.TensorProduct.map_surjective, Function, Function.Surjective, Ideal.Quoti, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Quotient, RingHom, RingHom.ker, Surjective, TensorProduct, WeaklyQuasiFiniteAt, algebraMap, map_ker, map_surjective, mk_surjective, otimes
-/
lemma baseChange (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p]
    {A : Type*} [CommRing A] [Algebra R A] (q : Ideal (A otimes[R] S)) [q.IsPrime]
    (hq : p = q.comap TensorProduct.includeRight.toRingHom) :
    WeaklyQuasiFiniteAt A q := by
  delta WeaklyQuasiFiniteAt at *
  let φ : A otimes[R] S ->ₐ[A] (A ⧸ q.under A) otimes[R] (S ⧸ (p.under R).map (algebraMap R S)) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ _ _) (Ideal.Quotient.mkₐ _ _)
  have hφ₁ : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective
  have hφ₂ : RingHom.ker φ.toRingHom = (q.under A).map (algebraMap _ _) := by
    refine (Algebra.TensorProduct.map_ker _ _
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective).trans ?_
    rw [← RingHom.ker_coe_toRingHom]; rw [← RingHom.ker_coe_toRingHom (F := AlgHom _ _ _)]; rw [← Ideal.map_coe]; rw [← Ideal.map_coe (F := AlgHom _ _ _)]
    simp only [Ideal.under, Ideal.Quotient.mkₐ_ker, hq, AlgHom.toRingHom_eq_coe, Ideal.comap_comap,
      AlgHom.comp_algebraMap_of_tower, Ideal.map_map]
    refine sup_eq_left.mpr ?_
    simp only [← TensorProduct.includeLeft.comp_algebraMap, ← Ideal.map_map, ← Ideal.comap_comap]
    exact Ideal.map_mono Ideal.map_comap_le
  have hφ₃ : φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (Ideal.Quotient.mk _) := rfl
  have : (Ideal.map φ.toRingHom q).IsPrime :=
Ideal.map_isPrime_of_surjective ‹_› hφ₂.trans_le Ideal.map_comap_le
  have := QuasiFiniteAt.baseChange (R := R) (S := _) (A := A ⧸ q.under A)
    (p.map (Ideal.Quotient.mk ((p.under R).map (algebraMap R S)))) (q.map φ.toRingHom) (by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_comap,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr Ideal.map_comap_le,
      ← hφ₃, ← Ideal.comap_comap, Ideal.comap_map_of_surjective _ (by exact hφ₁),
      ← RingHom.ker_eq_comap_bot, hφ₂, sup_eq_left.mpr Ideal.map_comap_le])
  have : QuasiFiniteAt A (q.map φ.toRingHom) := .trans _ (A ⧸ q.under A) _
  let e := (Ideal.quotientEquivAlg ((q.under A).map (algebraMap _ _)) _ (.refl) (by simpa)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ₁)
  refine .of_surjectiveOnStalks (q.map φ.toRingHom) e.symm.toAlgHom
    e.symm.toRingEquiv.surjectiveOnStalks _ ?_
  erw [Ideal.comap_symm] -- This should be fixed once `Ideal.map` does not take homclasses.
  rw [← Ideal.map_coe e.toRingEquiv]; rw [Ideal.map_map]
  rfl

open _root_.TensorProduct in
variable (R S) in
/--
lemma `of_restrictScalars` / 引理 `of_restrictScalars`

English:
lemma of_restrictScalars
  statement: [Algebra S T] [IsScalarTower R S T]
  proof: by
  have : Algebra.QuasiFiniteAt S (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T)))) :=
    .of_restrictScalars R _ _
  have H : (q.under R).map (algebraMap R T) <= (q.under S).map (algebraMap S T) := by
    simpa [Ideal.under, IsScalarTower.algebraMap_eq R S T, ← Ideal.map_map,
      ← Ideal.comap_comap, -Ideal.under_under] using Ideal.map_mono Ideal.map_comap_le
  delta WeaklyQuasiFiniteAt
  refine .of_surjectiveOnStalks (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T))))
    (Ideal.quotientMapₐ _ (.id _ _) (by exact H)) (RingHom.surjectiveOnStalks_of_surjective
      (Ideal.quotientMap_surjective (H := by exact H) Function.surjective_id)) _ ?_
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  rw [Ideal.comap_comap]; rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  refine .trans ?_ (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le]

中文:
引理 of_restrictScalars
  结论: [代数 S T] [标量塔 R S T]
  证明: by
  have : Algebra.QuasiFiniteAt S (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T)))) :=
    .of_restrictScalars R _ _
  have H : (q.under R).map (algebraMap R T) <= (q.under S).map (algebraMap S T) := by
    simpa [Ideal.under, IsScalarTower.algebraMap_eq R S T, ← Ideal.map_map,
      ← Ideal.comap_comap, -Ideal.under_under] using Ideal.map_mono Ideal.map_comap_le
  delta WeaklyQuasiFiniteAt
  refine .of_surjectiveOnStalks (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T))))
    (Ideal.quotientMapₐ _ (.id _ _) (by exact H)) (RingHom.surjectiveOnStalks_of_surjective
      (Ideal.quotientMap_surjective (H := by exact H) Function.surjective_id)) _ ?_
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  rw [Ideal.comap_comap]; rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  refine .trans ?_ (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le]

Depends on / 依赖: Algebra, Algebra.QuasiFiniteAt, Ideal.Quotient.mk, Ideal.comap_comap, Ideal.map_comap_le, Ideal.map_map, Ideal.map_mono, Ideal.quotientMap, Ideal.under, Ideal.under_under, IsScalarTower, IsScalarTower.algebraMap_eq, QuasiFiniteAt, Quotient, WeaklyQuasiFiniteAt, algebraMap, algebraMap_eq, comap_comap, map_comap_le, map_map
-/
lemma of_restrictScalars [Algebra S T] [IsScalarTower R S T]
    (q : Ideal T) [q.IsPrime] [WeaklyQuasiFiniteAt R q] :
    WeaklyQuasiFiniteAt S q := by
  have : Algebra.QuasiFiniteAt S (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T)))) :=
    .of_restrictScalars R _ _
  have H : (q.under R).map (algebraMap R T) <= (q.under S).map (algebraMap S T) := by
    simpa [Ideal.under, IsScalarTower.algebraMap_eq R S T, ← Ideal.map_map,
      ← Ideal.comap_comap, -Ideal.under_under] using Ideal.map_mono Ideal.map_comap_le
  delta WeaklyQuasiFiniteAt
  refine .of_surjectiveOnStalks (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T))))
    (Ideal.quotientMapₐ _ (.id _ _) (by exact H)) (RingHom.surjectiveOnStalks_of_surjective
      (Ideal.quotientMap_surjective (H := by exact H) Function.surjective_id)) _ ?_
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  rw [Ideal.comap_comap]; rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  refine .trans ?_ (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le]

/--
lemma `of_quasiFiniteAt_residueField` / 引理 `of_quasiFiniteAt_residueField`

English:
lemma of_quasiFiniteAt_residueField
  statement: [p.IsPrime] [q.LiesOver p]
  proof: by
  rw [Algebra.weaklyQuasiFiniteAt_iff]
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let φ₁ : p.ResidueField ->ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
    Ideal.quotientMapₐ _ (IsScalarTower.toAlgHom _ _ _) (by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p]; rw [Ideal.map_le_iff_le_comap]; rw [← Ideal.comap_coe (F := AlgHom _ _ _)]; rw [Ideal.comap_comap]
    simpa [← IsScalarTower.algebraMap_eq] using Ideal.le_comap_map)
  let φ₂ : p.Fiber S ->ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
    Algebra.TensorProduct.lift φ₁ (IsScalarTower.toAlgHom _ _ _) fun _ _ => .all _ _
  let φ₃ : Localization.AtPrime Q ->ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
IsLocalization.liftAlgHom (M := Q.primeCompl) (f := φ₂) by
      rintro ⟨y, hy⟩
      obtain ⟨r, hrp, s, H⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ y
      suffices IsUnit (φ₂ (1 otimesₜ s)) by
        rw [← H]; rw [map_smul]; rw [Algebra.smul_def]; rw [IsUnit.mul_iff] at this
        exact this.2
      suffices s ∉ q by
        have := (IsLocalization.map_units (M := q.primeCompl) Sq ⟨_, this⟩).map
          (algebraMap _ (Sq ⧸ p.map (algebraMap R Sq)))
        simpa [φ₂, ← IsScalarTower.algebraMap_apply] using this
      suffices algebraMap _ _ r * y ∉ Q by simpa [← hQ, ← H, Algebra.smul_def]
      refine Q.primeCompl.mul_mem ?_ hy
      simpa only [Ideal.mem_primeCompl_iff, ← Ideal.mem_comap, ← Q.over_def p]
  have : Function.Surjective φ₃ := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
    refine ⟨IsLocalization.mk' (M := Q.primeCompl) _ (1 otimesₜ x) ⟨1 otimesₜ s, ?_⟩, ?_⟩
    · simpa [← hQ] using hs
    · simp [φ₃, IsLocalization.lift_mk'_spec, φ₂, IsScalarTower.algebraMap_apply S Sq (Sq ⧸ _),
        -Ideal.Quotient.mk_algebraMap, ← map_mul]
  have inst : QuasiFiniteAt R Q := .trans _ p.ResidueField _
  obtain rfl := q.over_def p
  exact .of_surjective_algHom φ₃ this

中文:
引理 of_quasiFiniteAt_residueField
  结论: [p.是素] [q.LiesOver p]
  证明: by
  rw [Algebra.weaklyQuasiFiniteAt_iff]
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let φ₁ : p.ResidueField ->ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
    Ideal.quotientMapₐ _ (IsScalarTower.toAlgHom _ _ _) (by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p]; rw [Ideal.map_le_iff_le_comap]; rw [← Ideal.comap_coe (F := AlgHom _ _ _)]; rw [Ideal.comap_comap]
    simpa [← IsScalarTower.algebraMap_eq] using Ideal.le_comap_map)
  let φ₂ : p.Fiber S ->ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
    Algebra.TensorProduct.lift φ₁ (IsScalarTower.toAlgHom _ _ _) fun _ _ => .all _ _
  let φ₃ : Localization.AtPrime Q ->ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
IsLocalization.liftAlgHom (M := Q.primeCompl) (f := φ₂) by
      rintro ⟨y, hy⟩
      obtain ⟨r, hrp, s, H⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ y
      suffices IsUnit (φ₂ (1 otimesₜ s)) by
        rw [← H]; rw [map_smul]; rw [Algebra.smul_def]; rw [IsUnit.mul_iff] at this
        exact this.2
      suffices s ∉ q by
        have := (IsLocalization.map_units (M := q.primeCompl) Sq ⟨_, this⟩).map
          (algebraMap _ (Sq ⧸ p.map (algebraMap R Sq)))
        simpa [φ₂, ← IsScalarTower.algebraMap_apply] using this
      suffices algebraMap _ _ r * y ∉ Q by simpa [← hQ, ← H, Algebra.smul_def]
      refine Q.primeCompl.mul_mem ?_ hy
      simpa only [Ideal.mem_primeCompl_iff, ← Ideal.mem_comap, ← Q.over_def p]
  have : Function.Surjective φ₃ := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
    refine ⟨IsLocalization.mk' (M := Q.primeCompl) _ (1 otimesₜ x) ⟨1 otimesₜ s, ?_⟩, ?_⟩
    · simpa [← hQ] using hs
    · simp [φ₃, IsLocalization.lift_mk'_spec, φ₂, IsScalarTower.algebraMap_apply S Sq (Sq ⧸ _),
        -Ideal.Quotient.mk_algebraMap, ← map_mul]
  have inst : QuasiFiniteAt R Q := .trans _ p.ResidueField _
  obtain rfl := q.over_def p
  exact .of_surjective_algHom φ₃ this

Depends on / 依赖: AlgHom, Algebra, Algebra.weaklyQuasiFiniteAt_iff, AtPrime, Ideal.comap_coe, Ideal.comap_comap, Ideal.le_comap_map, Ideal.map_le_iff_le_comap, Ideal.quotientMap, IsLocalization, IsLocalization.AtPrime.map_eq_maximalIdeal, IsScalarTower, IsScalarTower.algebraMap_eq, IsScalarTower.toAlgHom, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, ResidueField, algebraMap, algebraMap_eq
-/
lemma of_quasiFiniteAt_residueField [p.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = q)
    [Algebra.QuasiFiniteAt p.ResidueField Q] :
    Algebra.WeaklyQuasiFiniteAt R q := by
  rw [Algebra.weaklyQuasiFiniteAt_iff]
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let φ₁ : p.ResidueField ->ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
    Ideal.quotientMapₐ _ (IsScalarTower.toAlgHom _ _ _) (by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p]; rw [Ideal.map_le_iff_le_comap]; rw [← Ideal.comap_coe (F := AlgHom _ _ _)]; rw [Ideal.comap_comap]
    simpa [← IsScalarTower.algebraMap_eq] using Ideal.le_comap_map)
  let φ₂ : p.Fiber S ->ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
    Algebra.TensorProduct.lift φ₁ (IsScalarTower.toAlgHom _ _ _) fun _ _ => .all _ _
  let φ₃ : Localization.AtPrime Q ->ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
IsLocalization.liftAlgHom (M := Q.primeCompl) (f := φ₂) by
      rintro ⟨y, hy⟩
      obtain ⟨r, hrp, s, H⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ y
      suffices IsUnit (φ₂ (1 otimesₜ s)) by
        rw [← H]; rw [map_smul]; rw [Algebra.smul_def]; rw [IsUnit.mul_iff] at this
        exact this.2
      suffices s ∉ q by
        have := (IsLocalization.map_units (M := q.primeCompl) Sq ⟨_, this⟩).map
          (algebraMap _ (Sq ⧸ p.map (algebraMap R Sq)))
        simpa [φ₂, ← IsScalarTower.algebraMap_apply] using this
      suffices algebraMap _ _ r * y ∉ Q by simpa [← hQ, ← H, Algebra.smul_def]
      refine Q.primeCompl.mul_mem ?_ hy
      simpa only [Ideal.mem_primeCompl_iff, ← Ideal.mem_comap, ← Q.over_def p]
  have : Function.Surjective φ₃ := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
    refine ⟨IsLocalization.mk' (M := Q.primeCompl) _ (1 otimesₜ x) ⟨1 otimesₜ s, ?_⟩, ?_⟩
    · simpa [← hQ] using hs
    · simp [φ₃, IsLocalization.lift_mk'_spec, φ₂, IsScalarTower.algebraMap_apply S Sq (Sq ⧸ _),
        -Ideal.Quotient.mk_algebraMap, ← map_mul]
  have inst : QuasiFiniteAt R Q := .trans _ p.ResidueField _
  obtain rfl := q.over_def p
  exact .of_surjective_algHom φ₃ this

end Algebra.WeaklyQuasiFiniteAt
