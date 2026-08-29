/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.Regular.Opposite
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Artinian rings and modules

A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main results

* `IsArtinianRing.primeSpectrum_finite`, `IsArtinianRing.isMaximal_of_isPrime`: there are only
  finitely prime ideals in a commutative Artinian ring, and each of them is maximal.

* `IsArtinianRing.equivPi`: a reduced commutative Artinian ring `R` is isomorphic to a finite
  product of fields (and therefore is a semisimple ring and a decomposition monoid; moreover
  `R[X]` is also a decomposition monoid).

* `IsArtinian.isSemisimpleModule_iff_jacobson`: an Artinian module is semisimple
  iff its Jacobson radical is zero.

* `instIsSemiprimaryRingOfIsArtinianRing`: an Artinian ring `R` is semiprimary, in particular
  the Jacobson radical of `R` is a nilpotent ideal (`IsArtinianRing.isNilpotent_jacobson_bot`).

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/

@[expose] public section

open Set Filter Pointwise

section Semiring

variable {R M P N : Type*}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P] [AddCommMonoid N]
variable [Module R M] [Module R P] [Module R N]

/--
theorem `LinearMap.isArtinian_iff_of_bijective` / 定理 `LinearMap.isArtinian_iff_of_bijective`

English:
theorem LinearMap.isArtinian_iff_of_bijective
  statement: {S P} [Semiring S] [AddCommMonoid P] [Module S P]
  proof: let e := Submodule.orderIsoMapComapOfBijective l hl
  ⟨fun _ => e.symm.strictMono.wellFoundedLT, fun _ => e.strictMono.wellFoundedLT⟩

中文:
定理 线性映射.isArtinian_iff_of_bijective
  结论: {S P} [半环 S] [加法交换幺半群 P] [模 S P]
  证明: let e := Submodule.orderIsoMapComapOfBijective l hl
  ⟨fun _ => e.symm.strictMono.wellFoundedLT, fun _ => e.strictMono.wellFoundedLT⟩

Depends on / 依赖: Submodule, Submodule.orderIsoMapComapOfBijective, e.strictMono.wellFoundedLT, e.symm.strictMono.wellFoundedLT, orderIsoMapComapOfBijective, strictMono, wellFoundedLT
-/
theorem LinearMap.isArtinian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R ->+* S} [RingHomSurjective σ] (l : M ->ₛₗ[σ] P) (hl : Function.Bijective l) :
    IsArtinian R M ↔ IsArtinian S P :=
  let e := Submodule.orderIsoMapComapOfBijective l hl
  ⟨fun _ => e.symm.strictMono.wellFoundedLT, fun _ => e.strictMono.wellFoundedLT⟩

/--
theorem `isArtinian_of_injective` / 定理 `isArtinian_of_injective`

English:
theorem isArtinian_of_injective
  given: (f : M ->ₗ[R] P) (h : Function.Injective f) [IsArtinian R P]
  proof: ⟨Subrelation.wf
    (fun {A B} hAB => show A.map f < B.map f from Submodule.map_strictMono_of_injective h hAB)
    (InvImage.wf (Submodule.map f) IsWellFounded.wf)⟩

中文:
定理 isArtinian_of_injective
  条件: (f : M ->ₗ[R] P) (h : 函数.单射 f) [是Artin R P]
  证明: ⟨Subrelation.wf
    (fun {A B} hAB => show A.map f < B.map f from Submodule.map_strictMono_of_injective h hAB)
    (InvImage.wf (Submodule.map f) IsWellFounded.wf)⟩

Depends on / 依赖: A.map, B.map, InvImage, InvImage.wf, IsWellFounded, IsWellFounded.wf, Submodule, Submodule.map, Submodule.map_strictMono_of_injective, Subrelation, Subrelation.wf, map_strictMono_of_injective
-/
theorem isArtinian_of_injective (f : M ->ₗ[R] P) (h : Function.Injective f) [IsArtinian R P] :
    IsArtinian R M :=
  ⟨Subrelation.wf
    (fun {A B} hAB => show A.map f < B.map f from Submodule.map_strictMono_of_injective h hAB)
    (InvImage.wf (Submodule.map f) IsWellFounded.wf)⟩

/--
Instance `isArtinian_submodule'` / 实例 `isArtinian_submodule'`

English:
instance isArtinian_submodule'
  signature: [IsArtinian R M] (N : Submodule R M)
  body: isArtinian_of_injective N.subtype Subtype.val_injective

中文:
实例 isArtinian_submodule'
  签名: [是Artin R M] (N : 子模 R M)
  定义体: isArtinian_of_injective N.subtype Subtype.val_injective

Depends on / 依赖: N.subtype, Subtype, Subtype.val_injective, isArtinian_of_injective, subtype, val_injective
-/
instance isArtinian_submodule' [IsArtinian R M] (N : Submodule R M) : IsArtinian R N :=
  isArtinian_of_injective N.subtype Subtype.val_injective

/--
theorem `isArtinian_of_le` / 定理 `isArtinian_of_le`

English:
theorem isArtinian_of_le
  given: {s t : Submodule R M} [IsArtinian R t] (h : s <= t)
  statement: IsArtinian R s
  proof: isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

中文:
定理 isArtinian_of_le
  条件: {s t : 子模 R M} [是Artin R t] (h : s <= t)
  结论: 是Artin R s
  证明: isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

Depends on / 依赖: Submodule, Submodule.inclusion, Submodule.inclusion_injective, inclusion, inclusion_injective, isArtinian_of_injective
-/
theorem isArtinian_of_le {s t : Submodule R M} [IsArtinian R t] (h : s <= t) : IsArtinian R s :=
  isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

variable (M) in
/--
theorem `isArtinian_of_surjective` / 定理 `isArtinian_of_surjective`

English:
theorem isArtinian_of_surjective
  given: (f : M ->ₗ[R] P) (hf : Function.Surjective f) [IsArtinian R M]
  proof: ⟨Subrelation.wf
    (fun {A B} hAB =>
      show A.comap f < B.comap f from Submodule.comap_strictMono_of_surjective hf hAB)
    (InvImage.wf (Submodule.comap f) IsWellFounded.wf)⟩

中文:
定理 isArtinian_of_surjective
  条件: (f : M ->ₗ[R] P) (hf : 函数.满射 f) [是Artin R M]
  证明: ⟨Subrelation.wf
    (fun {A B} hAB =>
      show A.comap f < B.comap f from Submodule.comap_strictMono_of_surjective hf hAB)
    (InvImage.wf (Submodule.comap f) IsWellFounded.wf)⟩

Depends on / 依赖: A.comap, B.comap, InvImage, InvImage.wf, IsWellFounded, IsWellFounded.wf, Submodule, Submodule.comap, Submodule.comap_strictMono_of_surjective, Subrelation, Subrelation.wf, comap_strictMono_of_surjective
-/
theorem isArtinian_of_surjective (f : M ->ₗ[R] P) (hf : Function.Surjective f) [IsArtinian R M] :
    IsArtinian R P :=
  ⟨Subrelation.wf
    (fun {A B} hAB =>
      show A.comap f < B.comap f from Submodule.comap_strictMono_of_surjective hf hAB)
    (InvImage.wf (Submodule.comap f) IsWellFounded.wf)⟩

/--
theorem `isArtinian_of_surjective_algebraMap` / 定理 `isArtinian_of_surjective_algebraMap`

English:
theorem isArtinian_of_surjective_algebraMap
  statement: {S : Type*} [CommSemiring S] [Algebra S R]
  proof: by
  apply (OrderEmbedding.wellFoundedLT (β := Submodule R M))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro N
    refine { toAddSubmonoid := N.toAddSubmonoid, smul_mem' := ?_ }
    intro c x hx
    obtain ⟨r, rfl⟩ := H c
    suffices r • x in N by simpa [Algebra.algebraMap_eq_smul_one, smul_assoc]
    apply N.smul_mem _ hx
  · intro N1 N2 h
    rwa [Submodule.ext_iff] at h ⊢
  · intro N1 N2
    rfl

中文:
定理 isArtinian_of_surjective_algebraMap
  结论: {S : 类型} [交换半环 S] [代数 S R]
  证明: by
  apply (OrderEmbedding.wellFoundedLT (β := Submodule R M))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro N
    refine { toAddSubmonoid := N.toAddSubmonoid, smul_mem' := ?_ }
    intro c x hx
    obtain ⟨r, rfl⟩ := H c
    suffices r • x in N by simpa [Algebra.algebraMap_eq_smul_one, smul_assoc]
    apply N.smul_mem _ hx
  · intro N1 N2 h
    rwa [Submodule.ext_iff] at h ⊢
  · intro N1 N2
    rfl

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, N.smul_mem, N.toAddSubmonoid, OrderEmbedding, OrderEmbedding.wellFoundedLT, Submodule, Submodule.ext_iff, algebraMap_eq_smul_one, ext_iff, smul_assoc, smul_mem, toAddSubmonoid, wellFoundedLT
-/
theorem isArtinian_of_surjective_algebraMap {S : Type*} [CommSemiring S] [Algebra S R]
    [Module S M] [IsArtinian R M] [IsScalarTower S R M]
    (H : Function.Surjective (algebraMap S R)) : IsArtinian S M := by
  apply (OrderEmbedding.wellFoundedLT (β := Submodule R M))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro N
    refine { toAddSubmonoid := N.toAddSubmonoid, smul_mem' := ?_ }
    intro c x hx
    obtain ⟨r, rfl⟩ := H c
    suffices r • x in N by simpa [Algebra.algebraMap_eq_smul_one, smul_assoc]
    apply N.smul_mem _ hx
  · intro N1 N2 h
    rwa [Submodule.ext_iff] at h ⊢
  · intro N1 N2
    rfl

/--
Instance `isArtinian_range` / 实例 `isArtinian_range`

English:
instance isArtinian_range
  signature: (f : M ->ₗ[R] P) [IsArtinian R M]
  body: isArtinian_of_surjective _ _ f.surjective_rangeRestrict

中文:
实例 isArtinian_range
  签名: (f : M ->ₗ[R] P) [是Artin R M]
  定义体: isArtinian_of_surjective _ _ f.surjective_rangeRestrict

Depends on / 依赖: f.surjective_rangeRestrict, isArtinian_of_surjective, surjective_rangeRestrict
-/
instance isArtinian_range (f : M ->ₗ[R] P) [IsArtinian R M] : IsArtinian R (LinearMap.range f) :=
  isArtinian_of_surjective _ _ f.surjective_rangeRestrict

/--
theorem `isArtinian_of_linearEquiv` / 定理 `isArtinian_of_linearEquiv`

English:
theorem isArtinian_of_linearEquiv
  given: (f : M ≃ₗ[R] P) [IsArtinian R M]
  statement: IsArtinian R P
  proof: isArtinian_of_surjective _ f.toLinearMap f.toEquiv.surjective

中文:
定理 isArtinian_of_linearEquiv
  条件: (f : M ≃ₗ[R] P) [是Artin R M]
  结论: 是Artin R P
  证明: isArtinian_of_surjective _ f.toLinearMap f.toEquiv.surjective

Depends on / 依赖: f.toEquiv.surjective, f.toLinearMap, isArtinian_of_surjective, surjective, toEquiv, toLinearMap
-/
theorem isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [IsArtinian R M] : IsArtinian R P :=
  isArtinian_of_surjective _ f.toLinearMap f.toEquiv.surjective

/--
theorem `LinearEquiv.isArtinian_iff` / 定理 `LinearEquiv.isArtinian_iff`

English:
theorem LinearEquiv.isArtinian_iff
  given: (f : M ≃ₗ[R] P)
  statement: IsArtinian R M ↔ IsArtinian R P
  proof: ⟨fun _ => isArtinian_of_linearEquiv f, fun _ => isArtinian_of_linearEquiv f.symm⟩

中文:
定理 线性等价.isArtinian_iff
  条件: (f : M ≃ₗ[R] P)
  结论: 是Artin R M ↔ 是Artin R P
  证明: ⟨fun _ => isArtinian_of_linearEquiv f, fun _ => isArtinian_of_linearEquiv f.symm⟩

Depends on / 依赖: f.symm, isArtinian_of_linearEquiv
-/
theorem LinearEquiv.isArtinian_iff (f : M ≃ₗ[R] P) : IsArtinian R M ↔ IsArtinian R P :=
  ⟨fun _ => isArtinian_of_linearEquiv f, fun _ => isArtinian_of_linearEquiv f.symm⟩

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
/--
lemma `isArtinian_of_finite` / 引理 `isArtinian_of_finite`

English:
lemma isArtinian_of_finite
  given: [Finite M]
  statement: IsArtinian R M
  proof: ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

中文:
引理 isArtinian_of_finite
  条件: [有限 M]
  结论: 是Artin R M
  证明: ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

Depends on / 依赖: Finite, Finite.wellFounded_of_trans_of_irrefl, wellFounded_of_trans_of_irrefl
-/
lemma isArtinian_of_finite [Finite M] : IsArtinian R M :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

open Submodule

/--
theorem `IsArtinian.finite_of_linearIndependent` / 定理 `IsArtinian.finite_of_linearIndependent`

English:
theorem IsArtinian.finite_of_linearIndependent
  statement: [Nontrivial R] [h : IsArtinian R M] {s : Set M}
  proof: WellFoundedLT.finite_of_iSupIndep hs.iSupIndep_span_singleton fun i _ => hs.ne_zero i (by simp_all)

中文:
定理 是Artin.finite_of_linearIndependent
  结论: [非平凡 R] [h : 是Artin R M] {s : 集合 M}
  证明: WellFoundedLT.finite_of_iSupIndep hs.iSupIndep_span_singleton fun i _ => hs.ne_zero i (by simp_all)

Depends on / 依赖: WellFoundedLT, WellFoundedLT.finite_of_iSupIndep, finite_of_iSupIndep, hs.iSupIndep_span_singleton, hs.ne_zero, iSupIndep_span_singleton, ne_zero
-/
theorem IsArtinian.finite_of_linearIndependent [Nontrivial R] [h : IsArtinian R M] {s : Set M}
    (hs : LinearIndependent R ((↑) : s -> M)) : s.Finite :=
  WellFoundedLT.finite_of_iSupIndep hs.iSupIndep_span_singleton fun i _ => hs.ne_zero i (by simp_all)

/--
theorem `set_has_minimal_iff_artinian` / 定理 `set_has_minimal_iff_artinian`

English:
theorem set_has_minimal_iff_artinian
  proof: by
  rw [isArtinian_iff]; rw [WellFounded.wellFounded_iff_has_min]

中文:
定理 set_has_minimal_iff_artinian
  证明: by
  rw [isArtinian_iff]; rw [WellFounded.wellFounded_iff_has_min]

Depends on / 依赖: WellFounded, WellFounded.wellFounded_iff_has_min, isArtinian_iff, wellFounded_iff_has_min
-/
theorem set_has_minimal_iff_artinian :
    (forall a : Set <| Submodule R M, a.Nonempty -> exists M' in a, forall I in a, ¬I < M') ↔ IsArtinian R M := by
  rw [isArtinian_iff]; rw [WellFounded.wellFounded_iff_has_min]

/--
theorem `IsArtinian.set_has_minimal` / 定理 `IsArtinian.set_has_minimal`

English:
theorem IsArtinian.set_has_minimal
  given: [IsArtinian R M] (a : Set <| Submodule R M) (ha : a.Nonempty)
  proof: set_has_minimal_iff_artinian.mpr ‹_› a ha

中文:
定理 是Artin.set_has_minimal
  条件: [是Artin R M] (a : 集合 <| 子模 R M) (ha : a.非空)
  证明: set_has_minimal_iff_artinian.mpr ‹_› a ha

Depends on / 依赖: set_has_minimal_iff_artinian, set_has_minimal_iff_artinian.mpr
-/
theorem IsArtinian.set_has_minimal [IsArtinian R M] (a : Set <| Submodule R M) (ha : a.Nonempty) :
    exists M' in a, forall I in a, ¬I < M' :=
  set_has_minimal_iff_artinian.mpr ‹_› a ha

/--
theorem `monotone_stabilizes_iff_artinian` / 定理 `monotone_stabilizes_iff_artinian`

English:
theorem monotone_stabilizes_iff_artinian
  proof: wellFoundedGT_iff_monotone_chain_condition.symm

中文:
定理 monotone_stabilizes_iff_artinian
  证明: wellFoundedGT_iff_monotone_chain_condition.symm

Depends on / 依赖: wellFoundedGT_iff_monotone_chain_condition, wellFoundedGT_iff_monotone_chain_condition.symm
-/
theorem monotone_stabilizes_iff_artinian :
    (forall f : Nat ->o (Submodule R M)ᵒᵈ, exists n, forall m, n <= m -> f n = f m) ↔ IsArtinian R M :=
  wellFoundedGT_iff_monotone_chain_condition.symm

namespace IsArtinian

variable [IsArtinian R M]

/--
theorem `monotone_stabilizes` / 定理 `monotone_stabilizes`

English:
theorem monotone_stabilizes
  given: (f : Nat ->o (Submodule R M)ᵒᵈ)
  statement: exists n, forall m, n <= m -> f n = f m
  proof: monotone_stabilizes_iff_artinian.mpr ‹_› f

中文:
定理 monotone_stabilizes
  条件: (f : 自然数 ->o (子模 R M)ᵒᵈ)
  结论: 存在 n, 对任意 m, n <= m -> f n = f m
  证明: monotone_stabilizes_iff_artinian.mpr ‹_› f

Depends on / 依赖: monotone_stabilizes_iff_artinian, monotone_stabilizes_iff_artinian.mpr
-/
theorem monotone_stabilizes (f : Nat ->o (Submodule R M)ᵒᵈ) : exists n, forall m, n <= m -> f n = f m :=
  monotone_stabilizes_iff_artinian.mpr ‹_› f

/--
theorem `eventuallyConst_of_isArtinian` / 定理 `eventuallyConst_of_isArtinian`

English:
theorem eventuallyConst_of_isArtinian
  given: (f : Nat ->o (Submodule R M)ᵒᵈ)
  proof: by
  simp_rw [eventuallyConst_atTop, eq_comm]
  exact monotone_stabilizes f

中文:
定理 eventuallyConst_of_isArtinian
  条件: (f : 自然数 ->o (子模 R M)ᵒᵈ)
  证明: by
  simp_rw [eventuallyConst_atTop, eq_comm]
  exact monotone_stabilizes f

Depends on / 依赖: eq_comm, eventuallyConst_atTop, monotone_stabilizes, simp_rw
-/
theorem eventuallyConst_of_isArtinian (f : Nat ->o (Submodule R M)ᵒᵈ) :
    atTop.EventuallyConst f := by
  simp_rw [eventuallyConst_atTop, eq_comm]
  exact monotone_stabilizes f

open Function

/--
theorem `surjective_of_injective_endomorphism` / 定理 `surjective_of_injective_endomorphism`

English:
theorem surjective_of_injective_endomorphism
  given: (f : M ->ₗ[R] M) (s : Injective f)
  statement: Surjective f
  proof: by
  have h := ‹IsArtinian R M›; contrapose h
  rw [IsArtinian]; rw [WellFoundedLT]; rw [isWellFounded_iff]
  refine (RelEmbedding.natGT (LinearMap.range <| f ^ ·) ?_).not_wellFounded
  intro n
  simp_rw [pow_succ, Module.End.mul_eq_comp, LinearMap.range_comp, ← Submodule.map_top (f ^ n)]
  refine Submodule.map_strictMono_of_injective (Module.End.iterate_injective s n) (Ne.lt_top ?_)
  rwa [Ne, LinearMap.range_eq_top]

中文:
定理 surjective_of_injective_endomorphism
  条件: (f : M ->ₗ[R] M) (s : 单射 f)
  结论: 满射 f
  证明: by
  have h := ‹IsArtinian R M›; contrapose h
  rw [IsArtinian]; rw [WellFoundedLT]; rw [isWellFounded_iff]
  refine (RelEmbedding.natGT (LinearMap.range <| f ^ ·) ?_).not_wellFounded
  intro n
  simp_rw [pow_succ, Module.End.mul_eq_comp, LinearMap.range_comp, ← Submodule.map_top (f ^ n)]
  refine Submodule.map_strictMono_of_injective (Module.End.iterate_injective s n) (Ne.lt_top ?_)
  rwa [Ne, LinearMap.range_eq_top]

Depends on / 依赖: IsArtinian, LinearMap, LinearMap.range, LinearMap.range_comp, LinearMap.range_eq_top, Module, Module.End.iterate_injective, Module.End.mul_eq_comp, Ne.lt_top, RelEmbedding, RelEmbedding.natGT, Submodule, Submodule.map_strictMono_of_injective, Submodule.map_top, WellFoundedLT, contrapose, isWellFounded_iff, iterate_injective, lt_top, map_strictMono_of_injective
-/
theorem surjective_of_injective_endomorphism (f : M ->ₗ[R] M) (s : Injective f) : Surjective f := by
  have h := ‹IsArtinian R M›; contrapose h
  rw [IsArtinian]; rw [WellFoundedLT]; rw [isWellFounded_iff]
  refine (RelEmbedding.natGT (LinearMap.range <| f ^ ·) ?_).not_wellFounded
  intro n
  simp_rw [pow_succ, Module.End.mul_eq_comp, LinearMap.range_comp, ← Submodule.map_top (f ^ n)]
  refine Submodule.map_strictMono_of_injective (Module.End.iterate_injective s n) (Ne.lt_top ?_)
  rwa [Ne, LinearMap.range_eq_top]

/--
theorem `bijective_of_injective_endomorphism` / 定理 `bijective_of_injective_endomorphism`

English:
theorem bijective_of_injective_endomorphism
  given: (f : M ->ₗ[R] M) (s : Injective f)
  statement: Bijective f
  proof: ⟨s, surjective_of_injective_endomorphism f s⟩

中文:
定理 bijective_of_injective_endomorphism
  条件: (f : M ->ₗ[R] M) (s : 单射 f)
  结论: 双射 f
  证明: ⟨s, surjective_of_injective_endomorphism f s⟩

Depends on / 依赖: surjective_of_injective_endomorphism
-/
theorem bijective_of_injective_endomorphism (f : M ->ₗ[R] M) (s : Injective f) : Bijective f :=
  ⟨s, surjective_of_injective_endomorphism f s⟩

/--
theorem `disjoint_partial_infs_eventually_top` / 定理 `disjoint_partial_infs_eventually_top`

English:
theorem disjoint_partial_infs_eventually_top
  statement: (f : Nat -> Submodule R M)
  proof: by
  -- A little off-by-one cleanup first:
  rsuffices ⟨n, w⟩ : exists n : Nat, forall m, n <= m -> OrderDual.toDual f (m + 1) = ⊤
  · use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes (partialSups (OrderDual.toDual ∘ f))
refine ⟨n, fun m p => (h m).eq_bot_of_ge sup_eq_left.mp ?_⟩
simpa only [partialSups_add_one] using! (w (m + 1) <| le_add_right p).symm.trans w m p

中文:
定理 disjoint_partial_infs_eventually_top
  结论: (f : 自然数 -> 子模 R M)
  证明: by
  -- A little off-by-one cleanup first:
  rsuffices ⟨n, w⟩ : exists n : Nat, forall m, n <= m -> OrderDual.toDual f (m + 1) = ⊤
  · use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes (partialSups (OrderDual.toDual ∘ f))
refine ⟨n, fun m p => (h m).eq_bot_of_ge sup_eq_left.mp ?_⟩
simpa only [partialSups_add_one] using! (w (m + 1) <| le_add_right p).symm.trans w m p
-/
theorem disjoint_partial_infs_eventually_top (f : Nat -> Submodule R M)
    (h : forall n, Disjoint (partialSups (OrderDual.toDual ∘ f) n) (OrderDual.toDual (f (n + 1)))) :
    exists n : Nat, forall m, n <= m -> f m = ⊤ := by
  -- A little off-by-one cleanup first:
  rsuffices ⟨n, w⟩ : exists n : Nat, forall m, n <= m -> OrderDual.toDual f (m + 1) = ⊤
  · use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes (partialSups (OrderDual.toDual ∘ f))
refine ⟨n, fun m p => (h m).eq_bot_of_ge sup_eq_left.mp ?_⟩
simpa only [partialSups_add_one] using! (w (m + 1) <| le_add_right p).symm.trans w m p

end IsArtinian

/--
lemma `IsArtinian.subsingleton_of_injective` / 引理 `IsArtinian.subsingleton_of_injective`

English:
lemma IsArtinian.subsingleton_of_injective
  statement: [IsArtinian R N] {f : P × N ->ₗ[R] N}
  proof: subsingleton_of_forall_eq 0 fun p =>
    have ⟨_, eq⟩ := IsArtinian.surjective_of_injective_endomorphism (f ∘ₗ .inr ..)
      (inj.comp (Prod.mk_right_injective _)) (f (p, 0))
    congr($(inj eq).1).symm

中文:
引理 是Artin.subsingleton_of_injective
  结论: [是Artin R N] {f : P × N ->ₗ[R] N}
  证明: subsingleton_of_forall_eq 0 fun p =>
    have ⟨_, eq⟩ := IsArtinian.surjective_of_injective_endomorphism (f ∘ₗ .inr ..)
      (inj.comp (Prod.mk_right_injective _)) (f (p, 0))
    congr($(inj eq).1).symm

Depends on / 依赖: IsArtinian, IsArtinian.surjective_of_injective_endomorphism, Prod.mk_right_injective, inj.comp, mk_right_injective, subsingleton_of_forall_eq, surjective_of_injective_endomorphism
-/
lemma IsArtinian.subsingleton_of_injective [IsArtinian R N] {f : P × N ->ₗ[R] N}
    (inj : Function.Injective f) : Subsingleton P :=
  subsingleton_of_forall_eq 0 fun p =>
    have ⟨_, eq⟩ := IsArtinian.surjective_of_injective_endomorphism (f ∘ₗ .inr ..)
      (inj.comp (Prod.mk_right_injective _)) (f (p, 0))
    congr($(inj eq).1).symm

namespace LinearMap

variable [IsArtinian R M]

/--
lemma `eventually_iInf_range_pow_eq` / 引理 `eventually_iInf_range_pow_eq`

English:
lemma eventually_iInf_range_pow_eq
  given: (f : Module.End R M)
  proof: by
  obtain ⟨n, hn : forall m, n <= m -> LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun l hl => le_antisymm (iInf_le _ _) (le_iInf fun m => ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ (hl.trans h), hn _ hl]
  · exact f.iterateRange.monotone h.le

中文:
引理 eventually_iInf_range_pow_eq
  条件: (f : 模.End R M)
  证明: by
  obtain ⟨n, hn : forall m, n <= m -> LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun l hl => le_antisymm (iInf_le _ _) (le_iInf fun m => ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ (hl.trans h), hn _ hl]
  · exact f.iterateRange.monotone h.le

Depends on / 依赖: IsArtinian, IsArtinian.monotone_stabilizes, LinearMap, LinearMap.range, eventually_atTop, eventually_atTop.mpr, f.iterateRange, f.iterateRange.monotone, h.le, hl.trans, iInf_le, iterateRange, le_antisymm, le_iInf, le_or_gt, monotone, monotone_stabilizes
-/
lemma eventually_iInf_range_pow_eq (f : Module.End R M) :
    forallᶠ n in atTop, ⨅ m, LinearMap.range (f ^ m) = LinearMap.range (f ^ n) := by
  obtain ⟨n, hn : forall m, n <= m -> LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun l hl => le_antisymm (iInf_le _ _) (le_iInf fun m => ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ (hl.trans h), hn _ hl]
  · exact f.iterateRange.monotone h.le

end LinearMap

end Semiring

section Ring

variable {R M P N : Type*}
variable [Ring R] [AddCommGroup M] [AddCommGroup P] [AddCommGroup N]
variable [Module R M] [Module R P] [Module R N]

/--
Instance `isArtinian_of_quotient_of_artinian` / 实例 `isArtinian_of_quotient_of_artinian`

English:
instance isArtinian_of_quotient_of_artinian
  body: isArtinian_of_surjective M (Submodule.mkQ N) (Submodule.Quotient.mk_surjective N)

中文:
实例 isArtinian_of_quotient_of_artinian
  定义体: isArtinian_of_surjective M (Submodule.mkQ N) (Submodule.Quotient.mk_surjective N)

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk_surjective, Submodule.mkQ, isArtinian_of_surjective, mk_surjective
-/
instance isArtinian_of_quotient_of_artinian
    (N : Submodule R M) [IsArtinian R M] : IsArtinian R (M ⧸ N) :=
  isArtinian_of_surjective M (Submodule.mkQ N) (Submodule.Quotient.mk_surjective N)

/--
theorem `isArtinian_of_range_eq_ker` / 定理 `isArtinian_of_range_eq_ker`

English:
theorem isArtinian_of_range_eq_ker
  statement: [IsArtinian R M] [IsArtinian R P] (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  proof: wellFounded_lt_exact_sequence (LinearMap.range f)
    (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
    (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
    (Submodule.giMapComap g.surjective_rangeRestrict)
    (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
    (by simp [Submodule.comap_map_eq, h])

中文:
定理 isArtinian_of_range_eq_ker
  结论: [是Artin R M] [是Artin R P] (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  证明: wellFounded_lt_exact_sequence (LinearMap.range f)
    (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
    (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
    (Submodule.giMapComap g.surjective_rangeRestrict)
    (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
    (by simp [Submodule.comap_map_eq, h])

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.ker_eq_bot.mp, LinearMap.range, Submodule, Submodule.comap, Submodule.comap_map_eq, Submodule.gciMapComap, Submodule.giMapComap, Submodule.ker_liftQ_eq_bot, Submodule.map, Submodule.map_comap_eq, Submodule.range_liftQ, comap_map_eq, g.rangeRestrict, g.surjective_rangeRestrict, gciMapComap, giMapComap, inf_comm, ker_eq_bot
-/
theorem isArtinian_of_range_eq_ker [IsArtinian R M] [IsArtinian R P] (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
    (h : LinearMap.range f = LinearMap.ker g) : IsArtinian R N :=
  wellFounded_lt_exact_sequence (LinearMap.range f)
    (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
    (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
    (Submodule.giMapComap g.surjective_rangeRestrict)
    (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
    (by simp [Submodule.comap_map_eq, h])

/--
theorem `isArtinian_iff_submodule_quotient` / 定理 `isArtinian_iff_submodule_quotient`

English:
theorem isArtinian_iff_submodule_quotient
  given: (S : Submodule R P)
  proof: by
  refine ⟨fun h => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ?_⟩
  apply isArtinian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype]

中文:
定理 isArtinian_iff_submodule_quotient
  条件: (S : 子模 R P)
  证明: by
  refine ⟨fun h => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ?_⟩
  apply isArtinian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype]

Depends on / 依赖: S.mkQ, S.subtype, Submodule, Submodule.ker_mkQ, Submodule.range_subtype, isArtinian_of_range_eq_ker, ker_mkQ, range_subtype, subtype
-/
theorem isArtinian_iff_submodule_quotient (S : Submodule R P) :
    IsArtinian R P ↔ IsArtinian R S ∧ IsArtinian R (P ⧸ S) := by
  refine ⟨fun h => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ?_⟩
  apply isArtinian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype]

/--
Instance `isArtinian_prod` / 实例 `isArtinian_prod`

English:
instance isArtinian_prod
  signature: [IsArtinian R M] [IsArtinian R P]
  body: isArtinian_of_range_eq_ker (LinearMap.inl R M P) (LinearMap.snd R M P) (LinearMap.range_inl R M P)

中文:
实例 isArtinian_prod
  签名: [是Artin R M] [是Artin R P]
  定义体: isArtinian_of_range_eq_ker (LinearMap.inl R M P) (LinearMap.snd R M P) (LinearMap.range_inl R M P)

Depends on / 依赖: LinearMap, LinearMap.inl, LinearMap.range_inl, LinearMap.snd, isArtinian_of_range_eq_ker, range_inl
-/
instance isArtinian_prod [IsArtinian R M] [IsArtinian R P] : IsArtinian R (M × P) :=
  isArtinian_of_range_eq_ker (LinearMap.inl R M P) (LinearMap.snd R M P) (LinearMap.range_inl R M P)

/--
Instance `isArtinian_sup` / 实例 `isArtinian_sup`

English:
instance isArtinian_sup
  signature: (M₁ M₂ : Submodule R P) [IsArtinian R M₁] [IsArtinian R M₂]
  body: by
  have := isArtinian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

中文:
实例 isArtinian_sup
  签名: (M₁ M₂ : 子模 R P) [是Artin R M₁] [是Artin R M₂]
  定义体: by
  have := isArtinian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

Depends on / 依赖: LinearMap, LinearMap.range_coprod, Submodule, Submodule.range_subtype, coprod, isArtinian_range, range_coprod, range_subtype, subtype, subtype.coprod
-/
instance isArtinian_sup (M₁ M₂ : Submodule R P) [IsArtinian R M₁] [IsArtinian R M₂] :
    IsArtinian R ↥(M₁ ⊔ M₂) := by
  have := isArtinian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

variable {ι : Type*} [Finite ι]

/--
Instance `isArtinian_pi` / 实例 `isArtinian_pi`

English:
instance isArtinian_pi
  signature: :
  body: by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h => isArtinian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih => isArtinian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

中文:
实例 isArtinian_pi
  签名: :
  定义体: by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h => isArtinian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih => isArtinian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

Depends on / 依赖: Finite, Finite.induction_empty_option, LinearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piOptionEquivProd, induction_empty_option, infer_instance, isArtinian_of_linearEquiv, piCongrLeft, piOptionEquivProd
-/
instance isArtinian_pi :
    forall {M : ι -> Type*} [Π i, AddCommGroup (M i)]
      [Π i, Module R (M i)] [forall i, IsArtinian R (M i)], IsArtinian R (Π i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h => isArtinian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih => isArtinian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

/--
Instance `isArtinian_pi'` / 实例 `isArtinian_pi'`

English:
instance isArtinian_pi'
  signature: [IsArtinian R M]
  body: isArtinian_pi

中文:
实例 isArtinian_pi'
  签名: [是Artin R M]
  定义体: isArtinian_pi

Depends on / 依赖: isArtinian_pi
-/
instance isArtinian_pi' [IsArtinian R M] : IsArtinian R (ι -> M) :=
  isArtinian_pi

/--
Instance `isArtinian_finsupp` / 实例 `isArtinian_finsupp`

English:
instance isArtinian_finsupp
  signature: [IsArtinian R M]
  body: isArtinian_of_linearEquiv (Finsupp.linearEquivFunOnFinite _ _ _).symm

中文:
实例 isArtinian_finsupp
  签名: [是Artin R M]
  定义体: isArtinian_of_linearEquiv (Finsupp.linearEquivFunOnFinite _ _ _).symm

Depends on / 依赖: Finsupp, Finsupp.linearEquivFunOnFinite, isArtinian_of_linearEquiv, linearEquivFunOnFinite
-/
instance isArtinian_finsupp [IsArtinian R M] : IsArtinian R (ι ->₀ M) :=
  isArtinian_of_linearEquiv (Finsupp.linearEquivFunOnFinite _ _ _).symm

/--
Instance `isArtinian_iSup` / 实例 `isArtinian_iSup`

English:
instance isArtinian_iSup
  signature: :
  body: by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

中文:
实例 isArtinian_iSup
  签名: :
  定义体: by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

Depends on / 依赖: Finite, Finite.induction_empty_option, e.iSup_comp, iSup_comp, iSup_of_empty, iSup_option, induction_empty_option, infer_instance, intros
-/
instance isArtinian_iSup :
    forall {M : ι -> Submodule R P} [forall i, IsArtinian R (M i)], IsArtinian R ↥(⨆ i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

variable (R M) in
/--
theorem `IsArtinian.isSemisimpleModule_iff_jacobson` / 定理 `IsArtinian.isSemisimpleModule_iff_jacobson`

English:
theorem IsArtinian.isSemisimpleModule_iff_jacobson
  given: [IsArtinian R M]
  proof: ⟨fun _ => IsSemisimpleModule.jacobson_eq_bot R M, fun h =>
    have ⟨s, hs⟩ := Finset.exists_inf_le (Subtype.val (p := fun m : Submodule R M => IsCoatom m))
    have _ (m : s) : IsSimpleModule R (M ⧸ m.1.1) := isSimpleModule_iff_isCoatom.mpr m.1.2
    let f : M ->ₗ[R] forall m : s, M ⧸ m.1.1 := LinearMap.pi fun m => m.1.1.mkQ
.of_injective f LinearMap.ker_eq_bot.mp le_bot_iff.mp fun x hx => by
      rw [← h]; rw [Module.jacobson]; rw [Submodule.mem_sInf]
exact fun m hm => hs ⟨m, hm⟩ Submodule.mem_finsetInf.mpr fun i hi =>
(Submodule.Quotient.mk_eq_zero i.1).mp congr_fun hx ⟨i, hi⟩⟩

中文:
定理 是Artin.isSemisimpleModule_iff_jacobson
  条件: [是Artin R M]
  证明: ⟨fun _ => IsSemisimpleModule.jacobson_eq_bot R M, fun h =>
    have ⟨s, hs⟩ := Finset.exists_inf_le (Subtype.val (p := fun m : Submodule R M => IsCoatom m))
    have _ (m : s) : IsSimpleModule R (M ⧸ m.1.1) := isSimpleModule_iff_isCoatom.mpr m.1.2
    let f : M ->ₗ[R] forall m : s, M ⧸ m.1.1 := LinearMap.pi fun m => m.1.1.mkQ
.of_injective f LinearMap.ker_eq_bot.mp le_bot_iff.mp fun x hx => by
      rw [← h]; rw [Module.jacobson]; rw [Submodule.mem_sInf]
exact fun m hm => hs ⟨m, hm⟩ Submodule.mem_finsetInf.mpr fun i hi =>
(Submodule.Quotient.mk_eq_zero i.1).mp congr_fun hx ⟨i, hi⟩⟩

Depends on / 依赖: Finset, Finset.exists_inf_le, IsCoatom, IsSemisimpleModule, IsSemisimpleModule.jacobson_eq_bot, IsSimpleModule, LinearMap, LinearMap.ker_eq_bot.mp, LinearMap.pi, Module, Module.jacobson, Submodule, Submodule.mem_finsetInf.mpr, Submodule.mem_sInf, Subtype, Subtype.val, exists_inf_le, isSimpleModule_iff_isCoatom, isSimpleModule_iff_isCoatom.mpr, jacobson
-/
theorem IsArtinian.isSemisimpleModule_iff_jacobson [IsArtinian R M] :
    IsSemisimpleModule R M ↔ Module.jacobson R M = ⊥ :=
  ⟨fun _ => IsSemisimpleModule.jacobson_eq_bot R M, fun h =>
    have ⟨s, hs⟩ := Finset.exists_inf_le (Subtype.val (p := fun m : Submodule R M => IsCoatom m))
    have _ (m : s) : IsSimpleModule R (M ⧸ m.1.1) := isSimpleModule_iff_isCoatom.mpr m.1.2
    let f : M ->ₗ[R] forall m : s, M ⧸ m.1.1 := LinearMap.pi fun m => m.1.1.mkQ
.of_injective f LinearMap.ker_eq_bot.mp le_bot_iff.mp fun x hx => by
      rw [← h]; rw [Module.jacobson]; rw [Submodule.mem_sInf]
exact fun m hm => hs ⟨m, hm⟩ Submodule.mem_finsetInf.mpr fun i hi =>
(Submodule.Quotient.mk_eq_zero i.1).mp congr_fun hx ⟨i, hi⟩⟩

open Submodule Function

namespace LinearMap

variable [IsArtinian R M]

/--
theorem `eventually_codisjoint_ker_pow_range_pow` / 定理 `eventually_codisjoint_ker_pow_range_pow`

English:
theorem eventually_codisjoint_ker_pow_range_pow
  given: (f : Module.End R M)
  proof: by
  obtain ⟨n, hn : forall m, n <= m -> LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun m hm => codisjoint_iff.mpr ?_⟩
  simp_rw [← hn _ hm, Submodule.eq_top_iff', Submodule.mem_sup]
  intro x
  rsuffices ⟨y, hy⟩ : exists y, (f ^ m) ((f ^ n) y) = (f ^ m) x
  · exact ⟨x - (f ^ n) y, by simp [hy], (f ^ n) y, by simp⟩
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `mem_range` into `mem_range (f := _)`
  simp_rw [f.pow_apply n, f.pow_apply m, ← iterate_add_apply, ← f.pow_apply (m + n),
    ← f.pow_apply m, ← mem_range (f := _), ← hn _ (n.le_add_left m), hn _ hm]
  exact LinearMap.mem_range_self (f ^ m) x

中文:
定理 eventually_codisjoint_ker_pow_range_pow
  条件: (f : 模.End R M)
  证明: by
  obtain ⟨n, hn : forall m, n <= m -> LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun m hm => codisjoint_iff.mpr ?_⟩
  simp_rw [← hn _ hm, Submodule.eq_top_iff', Submodule.mem_sup]
  intro x
  rsuffices ⟨y, hy⟩ : exists y, (f ^ m) ((f ^ n) y) = (f ^ m) x
  · exact ⟨x - (f ^ n) y, by simp [hy], (f ^ n) y, by simp⟩
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `mem_range` into `mem_range (f := _)`
  simp_rw [f.pow_apply n, f.pow_apply m, ← iterate_add_apply, ← f.pow_apply (m + n),
    ← f.pow_apply m, ← mem_range (f := _), ← hn _ (n.le_add_left m), hn _ hm]
  exact LinearMap.mem_range_self (f ^ m) x

Depends on / 依赖: IsArtinian, IsArtinian.monotone_stabilizes, LinearMap, LinearMap.range, Submodule, Submodule.eq_top_iff, Submodule.mem_sup, codisjoint_iff, codisjoint_iff.mpr, eq_top_iff, eventually_atTop, eventually_atTop.mpr, f.iterateRange, iterateRange, mem_sup, monotone_stabilizes, rsuffices, simp_rw
-/
theorem eventually_codisjoint_ker_pow_range_pow (f : Module.End R M) :
    forallᶠ n in atTop, Codisjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn : forall m, n <= m -> LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun m hm => codisjoint_iff.mpr ?_⟩
  simp_rw [← hn _ hm, Submodule.eq_top_iff', Submodule.mem_sup]
  intro x
  rsuffices ⟨y, hy⟩ : exists y, (f ^ m) ((f ^ n) y) = (f ^ m) x
  · exact ⟨x - (f ^ n) y, by simp [hy], (f ^ n) y, by simp⟩
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `mem_range` into `mem_range (f := _)`
  simp_rw [f.pow_apply n, f.pow_apply m, ← iterate_add_apply, ← f.pow_apply (m + n),
    ← f.pow_apply m, ← mem_range (f := _), ← hn _ (n.le_add_left m), hn _ hm]
  exact LinearMap.mem_range_self (f ^ m) x

/--
theorem `eventually_isCompl_ker_pow_range_pow` / 定理 `eventually_isCompl_ker_pow_range_pow`

English:
theorem eventually_isCompl_ker_pow_range_pow
  given: [IsNoetherian R M] (f : Module.End R M)
  proof: by
  filter_upwards [f.eventually_disjoint_ker_pow_range_pow.and
    f.eventually_codisjoint_ker_pow_range_pow] with n hn
  simpa only [isCompl_iff]

中文:
定理 eventually_isCompl_ker_pow_range_pow
  条件: [是Noether R M] (f : 模.End R M)
  证明: by
  filter_upwards [f.eventually_disjoint_ker_pow_range_pow.and
    f.eventually_codisjoint_ker_pow_range_pow] with n hn
  simpa only [isCompl_iff]

Depends on / 依赖: eventually_codisjoint_ker_pow_range_pow, eventually_disjoint_ker_pow_range_pow, f.eventually_codisjoint_ker_pow_range_pow, f.eventually_disjoint_ker_pow_range_pow.and, filter_upwards, isCompl_iff
-/
theorem eventually_isCompl_ker_pow_range_pow [IsNoetherian R M] (f : Module.End R M) :
    forallᶠ n in atTop, IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  filter_upwards [f.eventually_disjoint_ker_pow_range_pow.and
    f.eventually_codisjoint_ker_pow_range_pow] with n hn
  simpa only [isCompl_iff]

/--
theorem `isCompl_iSup_ker_pow_iInf_range_pow` / 定理 `isCompl_iSup_ker_pow_iInf_range_pow`

English:
theorem isCompl_iSup_ker_pow_iInf_range_pow
  given: [IsNoetherian R M] (f : M ->ₗ[R] M)
  proof: by
obtain ⟨k, hk⟩ := eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow.and
    f.eventually_iInf_range_pow_eq.and f.eventually_iSup_ker_pow_eq
  obtain ⟨h₁, h₂, h₃⟩ := hk k (le_refl k)
  rwa [h₂, h₃]

中文:
定理 isCompl_iSup_ker_pow_iInf_range_pow
  条件: [是Noether R M] (f : M ->ₗ[R] M)
  证明: by
obtain ⟨k, hk⟩ := eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow.and
    f.eventually_iInf_range_pow_eq.and f.eventually_iSup_ker_pow_eq
  obtain ⟨h₁, h₂, h₃⟩ := hk k (le_refl k)
  rwa [h₂, h₃]

Depends on / 依赖: eventually_atTop, eventually_atTop.mp, eventually_iInf_range_pow_eq, eventually_iSup_ker_pow_eq, eventually_isCompl_ker_pow_range_pow, f.eventually_iInf_range_pow_eq.and, f.eventually_iSup_ker_pow_eq, f.eventually_isCompl_ker_pow_range_pow.and, le_refl
-/
theorem isCompl_iSup_ker_pow_iInf_range_pow [IsNoetherian R M] (f : M ->ₗ[R] M) :
    IsCompl (⨆ n, LinearMap.ker (f ^ n)) (⨅ n, LinearMap.range (f ^ n)) := by
obtain ⟨k, hk⟩ := eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow.and
    f.eventually_iInf_range_pow_eq.and f.eventually_iSup_ker_pow_eq
  obtain ⟨h₁, h₂, h₃⟩ := hk k (le_refl k)
  rwa [h₂, h₃]

end LinearMap

end Ring

section CommSemiring

variable {R : Type*} (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] [IsArtinian R M]

namespace IsArtinian

/--
theorem `range_smul_pow_stabilizes` / 定理 `range_smul_pow_stabilizes`

English:
theorem range_smul_pow_stabilizes
  given: (r : R)
  proof: monotone_stabilizes
    ⟨fun n => LinearMap.range (r ^ n • LinearMap.id : M ->ₗ[R] M), fun n m h x ⟨y, hy⟩ =>
      ⟨r ^ (m - n) • y, by
        dsimp at hy ⊢
        rw [← smul_assoc]; rw [smul_eq_mul]; rw [← pow_add]; rw [← hy]; rw [add_tsub_cancel_of_le h]⟩⟩

中文:
定理 range_smul_pow_stabilizes
  条件: (r : R)
  证明: monotone_stabilizes
    ⟨fun n => LinearMap.range (r ^ n • LinearMap.id : M ->ₗ[R] M), fun n m h x ⟨y, hy⟩ =>
      ⟨r ^ (m - n) • y, by
        dsimp at hy ⊢
        rw [← smul_assoc]; rw [smul_eq_mul]; rw [← pow_add]; rw [← hy]; rw [add_tsub_cancel_of_le h]⟩⟩

Depends on / 依赖: LinearMap, LinearMap.id, LinearMap.range, add_tsub_cancel_of_le, monotone_stabilizes, pow_add, smul_assoc, smul_eq_mul
-/
theorem range_smul_pow_stabilizes (r : R) :
    exists n : Nat, forall m, n <= m ->
      LinearMap.range (r ^ n • LinearMap.id : M ->ₗ[R] M) =
      LinearMap.range (r ^ m • LinearMap.id : M ->ₗ[R] M) :=
  monotone_stabilizes
    ⟨fun n => LinearMap.range (r ^ n • LinearMap.id : M ->ₗ[R] M), fun n m h x ⟨y, hy⟩ =>
      ⟨r ^ (m - n) • y, by
        dsimp at hy ⊢
        rw [← smul_assoc]; rw [smul_eq_mul]; rw [← pow_add]; rw [← hy]; rw [add_tsub_cancel_of_le h]⟩⟩

variable {M}

/--
theorem `exists_pow_succ_smul_dvd` / 定理 `exists_pow_succ_smul_dvd`

English:
theorem exists_pow_succ_smul_dvd
  given: (r : R) (x : M)
  proof: by
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M r
  simp_rw [SetLike.ext_iff] at hn
  exact ⟨n, by simpa using hn n.succ n.le_succ (r ^ n • x)⟩

中文:
定理 存在_pow_succ_smul_dvd
  条件: (r : R) (x : M)
  证明: by
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M r
  simp_rw [SetLike.ext_iff] at hn
  exact ⟨n, by simpa using hn n.succ n.le_succ (r ^ n • x)⟩

Depends on / 依赖: IsArtinian, IsArtinian.range_smul_pow_stabilizes, SetLike, SetLike.ext_iff, ext_iff, le_succ, n.le_succ, n.succ, range_smul_pow_stabilizes, simp_rw
-/
theorem exists_pow_succ_smul_dvd (r : R) (x : M) :
    exists (n : Nat) (y : M), r ^ n.succ • y = r ^ n • x := by
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M r
  simp_rw [SetLike.ext_iff] at hn
  exact ⟨n, by simpa using hn n.succ n.le_succ (r ^ n • x)⟩

end IsArtinian

end CommSemiring

/--
theorem `isArtinian_of_submodule_of_artinian` / 定理 `isArtinian_of_submodule_of_artinian`

English:
theorem isArtinian_of_submodule_of_artinian
  statement: (R M) [Semiring R] [AddCommMonoid M] [Module R M]
  proof: inferInstance

中文:
定理 isArtinian_of_submodule_of_artinian
  结论: (R M) [半环 R] [加法交换幺半群 M] [模 R M]
  证明: inferInstance
-/
theorem isArtinian_of_submodule_of_artinian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (_ : IsArtinian R M) : IsArtinian R N := inferInstance

/--
theorem `isArtinian_of_tower` / 定理 `isArtinian_of_tower`

English:
theorem isArtinian_of_tower
  statement: (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
  proof: ⟨(Submodule.restrictScalarsEmbedding R S M).wellFounded h.wf⟩

中文:
定理 isArtinian_of_tower
  结论: (R) {S M} [半环 R] [半环 S] [加法交换幺半群 M] [标量乘法 R S]
  证明: ⟨(Submodule.restrictScalarsEmbedding R S M).wellFounded h.wf⟩

Depends on / 依赖: Submodule, Submodule.restrictScalarsEmbedding, h.wf, restrictScalarsEmbedding, wellFounded
-/
theorem isArtinian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsArtinian R M) : IsArtinian S M :=
  ⟨(Submodule.restrictScalarsEmbedding R S M).wellFounded h.wf⟩

/--
Instance `DivisionSemiring.instIsArtinianRing` / 实例 `DivisionSemiring.instIsArtinianRing`

English:
instance DivisionSemiring.instIsArtinianRing
  signature: {K : Type*} [DivisionSemiring K]
  body: ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

中文:
实例 除半环.instIsArtinianRing
  签名: {K : 类型} [除半环 K]
  定义体: ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

Depends on / 依赖: Finite, Finite.wellFounded_of_trans_of_irrefl, wellFounded_of_trans_of_irrefl
-/
instance DivisionSemiring.instIsArtinianRing {K : Type*} [DivisionSemiring K] : IsArtinianRing K :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

/--
Instance `DivisionRing.instIsArtinianRing` / 实例 `DivisionRing.instIsArtinianRing`

English:
instance DivisionRing.instIsArtinianRing
  signature: {K : Type*} [DivisionRing K]
  body: inferInstance

中文:
实例 除环.instIsArtinianRing
  签名: {K : 类型} [除环 K]
  定义体: inferInstance
-/
instance DivisionRing.instIsArtinianRing {K : Type*} [DivisionRing K] : IsArtinianRing K :=
  inferInstance

/--
theorem `Ring.isArtinian_of_zero_eq_one` / 定理 `Ring.isArtinian_of_zero_eq_one`

English:
theorem Ring.isArtinian_of_zero_eq_one
  given: {R} [Semiring R] (h01 : (0 : R) = 1)
  statement: IsArtinianRing R
  proof: have := subsingleton_of_zero_eq_one h01
  inferInstance

中文:
定理 环.isArtinian_of_zero_eq_one
  条件: {R} [半环 R] (h01 : (0 : R) = 1)
  结论: 是Artin环 R
  证明: have := subsingleton_of_zero_eq_one h01
  inferInstance

Depends on / 依赖: subsingleton_of_zero_eq_one
-/
theorem Ring.isArtinian_of_zero_eq_one {R} [Semiring R] (h01 : (0 : R) = 1) : IsArtinianRing R :=
  have := subsingleton_of_zero_eq_one h01
  inferInstance

instance (R) [Ring R] [IsArtinianRing R] (I : Ideal R) [I.IsTwoSided] : IsArtinianRing (R ⧸ I) :=
  isArtinian_of_tower R inferInstance

instance (priority := low) (R) [Semiring R] [IsArtinianRing R] : IsDedekindFiniteMonoid R where
  mul_eq_one_symm {a b} hab := by
    have ⟨c, hca⟩ := IsArtinian.surjective_of_injective_endomorphism
      (.toSpanSingleton R R a) (isRightRegular_of_mul_eq_one hab) 1
    rwa [← left_inv_eq_right_inv hca hab]

open Submodule Function

/--
Instance `isArtinian_of_fg_of_artinian'` / 实例 `isArtinian_of_fg_of_artinian'`

English:
instance isArtinian_of_fg_of_artinian'
  signature: {R M} [Ring R] [AddCommGroup M] [Module R M]
  body: have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isArtinian_of_surjective _ _ h

中文:
实例 isArtinian_of_fg_of_artinian'
  签名: {R M} [环 R] [加法交换群 M] [模 R M]
  定义体: have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isArtinian_of_surjective _ _ h

Depends on / 依赖: Finite, Module, Module.Finite.exists_fin, exists_fin, isArtinian_of_surjective
-/
instance isArtinian_of_fg_of_artinian' {R M} [Ring R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] [Module.Finite R M] : IsArtinian R M :=
  have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isArtinian_of_surjective _ _ h

/--
theorem `isArtinian_of_fg_of_artinian` / 定理 `isArtinian_of_fg_of_artinian`

English:
theorem isArtinian_of_fg_of_artinian
  statement: {R M} [Ring R] [AddCommGroup M] [Module R M]
  proof: by
  rw [← Module.Finite.iff_fg] at hN; infer_instance

中文:
定理 isArtinian_of_fg_of_artinian
  结论: {R M} [环 R] [加法交换群 M] [模 R M]
  证明: by
  rw [← Module.Finite.iff_fg] at hN; infer_instance

Depends on / 依赖: Finite, Module, Module.Finite.iff_fg, iff_fg, infer_instance
-/
theorem isArtinian_of_fg_of_artinian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsArtinianRing R] (hN : N.FG) : IsArtinian R N := by
  rw [← Module.Finite.iff_fg] at hN; infer_instance

/--
theorem `IsArtinianRing.of_finite` / 定理 `IsArtinianRing.of_finite`

English:
theorem IsArtinianRing.of_finite
  statement: (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
  proof: isArtinian_of_tower R isArtinian_of_fg_of_artinian'

中文:
定理 是Artin环.of_finite
  结论: (R S) [环 R] [环 S] [模 R S] [标量塔 R S S]
  证明: isArtinian_of_tower R isArtinian_of_fg_of_artinian'

Depends on / 依赖: isArtinian_of_fg_of_artinian, isArtinian_of_tower
-/
theorem IsArtinianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
    [IsArtinianRing R] [Module.Finite R S] : IsArtinianRing S :=
  isArtinian_of_tower R isArtinian_of_fg_of_artinian'

instance (n R) [Fintype n] [DecidableEq n] [Ring R] [IsNoetherianRing R] :
    IsNoetherianRing (Matrix n n R) := .of_finite R _

instance (n R) [Fintype n] [DecidableEq n] [Ring R] [IsArtinianRing R] :
    IsArtinianRing (Matrix n n R) := .of_finite R _

/--
theorem `isArtinian_span_of_finite` / 定理 `isArtinian_span_of_finite`

English:
theorem isArtinian_span_of_finite
  statement: (R) {M} [Ring R] [AddCommGroup M] [Module R M] [IsArtinianRing R]
  proof: isArtinian_of_fg_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

中文:
定理 isArtinian_span_of_finite
  结论: (R) {M} [环 R] [加法交换群 M] [模 R M] [是Artin环 R]
  证明: isArtinian_of_fg_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

Depends on / 依赖: Submodule, Submodule.fg_def.mpr, fg_def, isArtinian_of_fg_of_artinian
-/
theorem isArtinian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M] [IsArtinianRing R]
    {A : Set M} (hA : A.Finite) : IsArtinian R (Submodule.span R A) :=
  isArtinian_of_fg_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

/--
theorem `Function.Surjective.isArtinianRing` / 定理 `Function.Surjective.isArtinianRing`

English:
theorem Function.Surjective.isArtinianRing
  statement: {R} [Semiring R] {S} [Semiring S] {F}
  proof: by
  rw [isArtinianRing_iff] at H ⊢
  exact ⟨(Ideal.orderEmbeddingOfSurjective f hf).wellFounded H.wf⟩

中文:
定理 函数.满射.isArtinianRing
  结论: {R} [半环 R] {S} [半环 S] {F}
  证明: by
  rw [isArtinianRing_iff] at H ⊢
  exact ⟨(Ideal.orderEmbeddingOfSurjective f hf).wellFounded H.wf⟩

Depends on / 依赖: H.wf, Ideal.orderEmbeddingOfSurjective, isArtinianRing_iff, orderEmbeddingOfSurjective, wellFounded
-/
theorem Function.Surjective.isArtinianRing {R} [Semiring R] {S} [Semiring S] {F}
    [FunLike F R S] [RingHomClass F R S]
    {f : F} (hf : Function.Surjective f) [H : IsArtinianRing R] : IsArtinianRing S := by
  rw [isArtinianRing_iff] at H ⊢
  exact ⟨(Ideal.orderEmbeddingOfSurjective f hf).wellFounded H.wf⟩

/--
Instance `isArtinianRing_rangeS` / 实例 `isArtinianRing_rangeS`

English:
instance isArtinianRing_rangeS
  signature: {R} [Semiring R] {S} [Semiring S] (f : R ->+* S) [IsArtinianRing R]
  body: f.rangeSRestrict_surjective.isArtinianRing

中文:
实例 isArtinianRing_rangeS
  签名: {R} [半环 R] {S} [半环 S] (f : R ->+* S) [是Artin环 R]
  定义体: f.rangeSRestrict_surjective.isArtinianRing

Depends on / 依赖: f.rangeSRestrict_surjective.isArtinianRing, isArtinianRing, rangeSRestrict_surjective
-/
instance isArtinianRing_rangeS {R} [Semiring R] {S} [Semiring S] (f : R ->+* S) [IsArtinianRing R] :
    IsArtinianRing f.rangeS :=
  f.rangeSRestrict_surjective.isArtinianRing

/--
Instance `isArtinianRing_range` / 实例 `isArtinianRing_range`

English:
instance isArtinianRing_range
  signature: {R} [Ring R] {S} [Ring S] (f : R ->+* S) [IsArtinianRing R]
  body: isArtinianRing_rangeS f

中文:
实例 isArtinianRing_range
  签名: {R} [环 R] {S} [环 S] (f : R ->+* S) [是Artin环 R]
  定义体: isArtinianRing_rangeS f

Depends on / 依赖: isArtinianRing_rangeS
-/
instance isArtinianRing_range {R} [Ring R] {S} [Ring S] (f : R ->+* S) [IsArtinianRing R] :
    IsArtinianRing f.range :=
  isArtinianRing_rangeS f

/--
theorem `RingEquiv.isArtinianRing` / 定理 `RingEquiv.isArtinianRing`

English:
theorem RingEquiv.isArtinianRing
  statement: {R S} [Semiring R] [Semiring S] (f : R ≃+* S)
  proof: f.surjective.isArtinianRing

中文:
定理 环等价.isArtinianRing
  结论: {R S} [半环 R] [半环 S] (f : R ≃+* S)
  证明: f.surjective.isArtinianRing

Depends on / 依赖: f.surjective.isArtinianRing, isArtinianRing, surjective
-/
theorem RingEquiv.isArtinianRing {R S} [Semiring R] [Semiring S] (f : R ≃+* S)
    [IsArtinianRing R] : IsArtinianRing S :=
  f.surjective.isArtinianRing

instance {R S} [Semiring R] [Semiring S] [IsArtinianRing R] [IsArtinianRing S] :
    IsArtinianRing (R × S) :=
  Ideal.idealProdEquiv.toOrderEmbedding.wellFoundedLT

instance {ι} [Finite ι] : forall {R : ι -> Type*} [Π i, Semiring (R i)] [forall i, IsArtinianRing (R i)],
    IsArtinianRing (Π i, R i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h => RingEquiv.isArtinianRing (.piCongrLeft _ e)
  · infer_instance
  · exact fun ih => RingEquiv.isArtinianRing (.symm .piOptionEquivProd)

namespace IsArtinianRing

section Semiring

variable {R : Type*} [Semiring R]

/--
theorem `isUnit_iff_isRightRegular` / 定理 `isUnit_iff_isRightRegular`

English:
theorem isUnit_iff_isRightRegular
  given: [IsArtinianRing R] {x : R}
  statement: IsUnit x ↔ IsRightRegular x
  proof: by
  rw [IsRightRegular]; rw [IsUnit.isUnit_iff_mulRight_bijective]; rw [Bijective]; rw [and_iff_left_of_imp]
  exact IsArtinian.surjective_of_injective_endomorphism (.toSpanSingleton R R x)

中文:
定理 isUnit_iff_isRightRegular
  条件: [是Artin环 R] {x : R}
  结论: 是单位 x ↔ IsRightRegular x
  证明: by
  rw [IsRightRegular]; rw [IsUnit.isUnit_iff_mulRight_bijective]; rw [Bijective]; rw [and_iff_left_of_imp]
  exact IsArtinian.surjective_of_injective_endomorphism (.toSpanSingleton R R x)

Depends on / 依赖: Bijective, IsArtinian, IsArtinian.surjective_of_injective_endomorphism, IsRightRegular, IsUnit, IsUnit.isUnit_iff_mulRight_bijective, and_iff_left_of_imp, isUnit_iff_mulRight_bijective, surjective_of_injective_endomorphism, toSpanSingleton
-/
theorem isUnit_iff_isRightRegular [IsArtinianRing R] {x : R} : IsUnit x ↔ IsRightRegular x := by
  rw [IsRightRegular]; rw [IsUnit.isUnit_iff_mulRight_bijective]; rw [Bijective]; rw [and_iff_left_of_imp]
  exact IsArtinian.surjective_of_injective_endomorphism (.toSpanSingleton R R x)

/--
theorem `isUnit_iff_isRegular` / 定理 `isUnit_iff_isRegular`

English:
theorem isUnit_iff_isRegular
  given: [IsArtinianRing R] {x : R}
  statement: IsUnit x ↔ IsRegular x
  proof: by
  rw [isRegular_iff]; rw [← isUnit_iff_isRightRegular]; rw [and_iff_right_of_imp (·.isRegular.1)]

中文:
定理 isUnit_iff_isRegular
  条件: [是Artin环 R] {x : R}
  结论: 是单位 x ↔ 是正则 x
  证明: by
  rw [isRegular_iff]; rw [← isUnit_iff_isRightRegular]; rw [and_iff_right_of_imp (·.isRegular.1)]

Depends on / 依赖: and_iff_right_of_imp, isRegular, isRegular_iff, isUnit_iff_isRightRegular
-/
theorem isUnit_iff_isRegular [IsArtinianRing R] {x : R} : IsUnit x ↔ IsRegular x := by
  rw [isRegular_iff]; rw [← isUnit_iff_isRightRegular]; rw [and_iff_right_of_imp (·.isRegular.1)]

/--
theorem `isUnit_iff_isLeftRegular` / 定理 `isUnit_iff_isLeftRegular`

English:
theorem isUnit_iff_isLeftRegular
  given: [IsArtinianRing Rᵐᵒᵖ] {x : R}
  statement: IsUnit x ↔ IsLeftRegular x
  proof: by
  rw [← isRightRegular_op]; rw [← isUnit_op]; rw [isUnit_iff_isRightRegular]

中文:
定理 isUnit_iff_isLeftRegular
  条件: [是Artin环 Rᵐᵒᵖ] {x : R}
  结论: 是单位 x ↔ IsLeftRegular x
  证明: by
  rw [← isRightRegular_op]; rw [← isUnit_op]; rw [isUnit_iff_isRightRegular]

Depends on / 依赖: isRightRegular_op, isUnit_iff_isRightRegular, isUnit_op
-/
theorem isUnit_iff_isLeftRegular [IsArtinianRing Rᵐᵒᵖ] {x : R} : IsUnit x ↔ IsLeftRegular x := by
  rw [← isRightRegular_op]; rw [← isUnit_op]; rw [isUnit_iff_isRightRegular]

/--
theorem `isUnit_iff_isRegular_of_mulOpposite` / 定理 `isUnit_iff_isRegular_of_mulOpposite`

English:
theorem isUnit_iff_isRegular_of_mulOpposite
  given: [IsArtinianRing Rᵐᵒᵖ] {x : R}
  proof: by
  rw [isRegular_iff]; rw [← isUnit_iff_isLeftRegular]; rw [and_iff_left_of_imp (·.isRegular.2)]

中文:
定理 isUnit_iff_isRegular_of_mulOpposite
  条件: [是Artin环 Rᵐᵒᵖ] {x : R}
  证明: by
  rw [isRegular_iff]; rw [← isUnit_iff_isLeftRegular]; rw [and_iff_left_of_imp (·.isRegular.2)]

Depends on / 依赖: and_iff_left_of_imp, isRegular, isRegular_iff, isUnit_iff_isLeftRegular
-/
theorem isUnit_iff_isRegular_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {x : R} :
    IsUnit x ↔ IsRegular x := by
  rw [isRegular_iff]; rw [← isUnit_iff_isLeftRegular]; rw [and_iff_left_of_imp (·.isRegular.2)]

end Semiring

section Ring

variable {R : Type*} [Ring R]

open nonZeroDivisors

/--
theorem `isUnit_of_mem_nonZeroDivisors` / 定理 `isUnit_of_mem_nonZeroDivisors`

English:
theorem isUnit_of_mem_nonZeroDivisors
  given: [IsArtinianRing R] {a : R} (ha : a in R⁰)
  statement: IsUnit a
  proof: by
  rwa [isUnit_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]

中文:
定理 isUnit_of_mem_nonZeroDivisors
  条件: [是Artin环 R] {a : R} (ha : a in R⁰)
  结论: 是单位 a
  证明: by
  rwa [isUnit_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]

Depends on / 依赖: isRegular_iff_mem_nonZeroDivisors, isUnit_iff_isRegular
-/
theorem isUnit_of_mem_nonZeroDivisors [IsArtinianRing R] {a : R} (ha : a in R⁰) : IsUnit a := by
  rwa [isUnit_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]

/--
theorem `isUnit_of_mem_nonZeroDivisors_of_mulOpposite` / 定理 `isUnit_of_mem_nonZeroDivisors_of_mulOpposite`

English:
theorem isUnit_of_mem_nonZeroDivisors_of_mulOpposite
  statement: [IsArtinianRing Rᵐᵒᵖ] {a : R}
  proof: by
  rwa [isUnit_iff_isRegular_of_mulOpposite, isRegular_iff_mem_nonZeroDivisors]

中文:
定理 isUnit_of_mem_nonZeroDivisors_of_mulOpposite
  结论: [是Artin环 Rᵐᵒᵖ] {a : R}
  证明: by
  rwa [isUnit_iff_isRegular_of_mulOpposite, isRegular_iff_mem_nonZeroDivisors]

Depends on / 依赖: isRegular_iff_mem_nonZeroDivisors, isUnit_iff_isRegular_of_mulOpposite
-/
theorem isUnit_of_mem_nonZeroDivisors_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {a : R}
    (ha : a in R⁰) : IsUnit a := by
  rwa [isUnit_iff_isRegular_of_mulOpposite, isRegular_iff_mem_nonZeroDivisors]

/--
theorem `isUnit_iff_mem_nonZeroDivisors` / 定理 `isUnit_iff_mem_nonZeroDivisors`

English:
theorem isUnit_iff_mem_nonZeroDivisors
  given: [IsArtinianRing R] {a : R}
  statement: IsUnit a ↔ a in R⁰
  proof: by
  rw [isUnit_iff_isRegular]; rw [isRegular_iff_mem_nonZeroDivisors]

中文:
定理 isUnit_iff_mem_nonZeroDivisors
  条件: [是Artin环 R] {a : R}
  结论: 是单位 a ↔ a in R⁰
  证明: by
  rw [isUnit_iff_isRegular]; rw [isRegular_iff_mem_nonZeroDivisors]

Depends on / 依赖: isRegular_iff_mem_nonZeroDivisors, isUnit_iff_isRegular
-/
theorem isUnit_iff_mem_nonZeroDivisors [IsArtinianRing R] {a : R} : IsUnit a ↔ a in R⁰ := by
  rw [isUnit_iff_isRegular]; rw [isRegular_iff_mem_nonZeroDivisors]

/--
theorem `isUnit_iff_mem_nonZeroDivisors_of_mulOpposite` / 定理 `isUnit_iff_mem_nonZeroDivisors_of_mulOpposite`

English:
theorem isUnit_iff_mem_nonZeroDivisors_of_mulOpposite
  given: [IsArtinianRing Rᵐᵒᵖ] {a : R}
  proof: by
  rw [isUnit_iff_isRegular_of_mulOpposite]; rw [isRegular_iff_mem_nonZeroDivisors]

中文:
定理 isUnit_iff_mem_nonZeroDivisors_of_mulOpposite
  条件: [是Artin环 Rᵐᵒᵖ] {a : R}
  证明: by
  rw [isUnit_iff_isRegular_of_mulOpposite]; rw [isRegular_iff_mem_nonZeroDivisors]

Depends on / 依赖: isRegular_iff_mem_nonZeroDivisors, isUnit_iff_isRegular_of_mulOpposite
-/
theorem isUnit_iff_mem_nonZeroDivisors_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {a : R} :
    IsUnit a ↔ a in R⁰ := by
  rw [isUnit_iff_isRegular_of_mulOpposite]; rw [isRegular_iff_mem_nonZeroDivisors]

variable (R)

/--
theorem `isUnitSubmonoid_eq` / 定理 `isUnitSubmonoid_eq`

English:
theorem isUnitSubmonoid_eq
  given: [IsArtinianRing R]
  statement: IsUnit.submonoid R = R⁰
  proof: by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors]

中文:
定理 isUnitSubmonoid_eq
  条件: [是Artin环 R]
  结论: 是单位.submonoid R = R⁰
  证明: by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors]

Depends on / 依赖: IsUnit, IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors, mem_submonoid_iff
-/
theorem isUnitSubmonoid_eq [IsArtinianRing R] : IsUnit.submonoid R = R⁰ := by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors]

/--
theorem `isUnitSubmonoid_eq_of_mulOpposite` / 定理 `isUnitSubmonoid_eq_of_mulOpposite`

English:
theorem isUnitSubmonoid_eq_of_mulOpposite
  given: [IsArtinianRing Rᵐᵒᵖ]
  proof: by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors_of_mulOpposite]

中文:
定理 isUnitSubmonoid_eq_of_mulOpposite
  条件: [是Artin环 Rᵐᵒᵖ]
  证明: by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors_of_mulOpposite]

Depends on / 依赖: IsUnit, IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors_of_mulOpposite, mem_submonoid_iff
-/
theorem isUnitSubmonoid_eq_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] :
    IsUnit.submonoid R = R⁰ := by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors_of_mulOpposite]

/--
theorem `isUnitSubmonoid_eq_nonZeroDivisorsRight` / 定理 `isUnitSubmonoid_eq_nonZeroDivisorsRight`

English:
theorem isUnitSubmonoid_eq_nonZeroDivisorsRight
  given: [IsArtinianRing R]
  proof: by
  ext; rw [← isRightRegular_iff_mem_nonZeroDivisorsRight]; exact isUnit_iff_isRightRegular

中文:
定理 isUnitSubmonoid_eq_nonZeroDivisorsRight
  条件: [是Artin环 R]
  证明: by
  ext; rw [← isRightRegular_iff_mem_nonZeroDivisorsRight]; exact isUnit_iff_isRightRegular

Depends on / 依赖: isRightRegular_iff_mem_nonZeroDivisorsRight, isUnit_iff_isRightRegular
-/
theorem isUnitSubmonoid_eq_nonZeroDivisorsRight [IsArtinianRing R] :
    IsUnit.submonoid R = nonZeroDivisorsRight R := by
  ext; rw [← isRightRegular_iff_mem_nonZeroDivisorsRight]; exact isUnit_iff_isRightRegular

/--
theorem `nonZeroDivisorsLeft_eq_isUnitSubmonoid` / 定理 `nonZeroDivisorsLeft_eq_isUnitSubmonoid`

English:
theorem nonZeroDivisorsLeft_eq_isUnitSubmonoid
  given: [IsArtinianRing Rᵐᵒᵖ]
  proof: by
  ext; rw [← isLeftRegular_iff_mem_nonZeroDivisorsLeft]; exact isUnit_iff_isLeftRegular

中文:
定理 nonZeroDivisorsLeft_eq_isUnitSubmonoid
  条件: [是Artin环 Rᵐᵒᵖ]
  证明: by
  ext; rw [← isLeftRegular_iff_mem_nonZeroDivisorsLeft]; exact isUnit_iff_isLeftRegular

Depends on / 依赖: isLeftRegular_iff_mem_nonZeroDivisorsLeft, isUnit_iff_isLeftRegular
-/
theorem nonZeroDivisorsLeft_eq_isUnitSubmonoid [IsArtinianRing Rᵐᵒᵖ] :
    IsUnit.submonoid R = nonZeroDivisorsLeft R := by
  ext; rw [← isLeftRegular_iff_mem_nonZeroDivisorsLeft]; exact isUnit_iff_isLeftRegular

end Ring

section CommSemiring

variable (R : Type*) [CommSemiring R] [IsArtinianRing R]

@[stacks 00J7]
/--
lemma `setOfPred_isMaximal_finite` / 引理 `setOfPred_isMaximal_finite`

English:
lemma setOfPred_isMaximal_finite
  statement: {I : Ideal R | I.IsMaximal}.Finite
  proof: by
  have ⟨s, H⟩ := Finset.exists_inf_le (Subtype.val (p := fun I : Ideal R => I.IsMaximal))
  refine Set.finite_def.2 ⟨s, fun p => ?_⟩
  have ⟨q, hq1, hq2⟩ := p.2.isPrime.inf_le'.mp (H p)
  rwa [← Subtype.ext <| q.2.eq_of_le p.2.ne_top hq2]

@[deprecated (since := "2026-07-09")] alias setOf_isMaximal_finite := setOfPred_isMaximal_finite

中文:
引理 setOfPred_isMaximal_finite
  结论: {I : 理想 R | I.是极大}.有限
  证明: by
  have ⟨s, H⟩ := Finset.exists_inf_le (Subtype.val (p := fun I : Ideal R => I.IsMaximal))
  refine Set.finite_def.2 ⟨s, fun p => ?_⟩
  have ⟨q, hq1, hq2⟩ := p.2.isPrime.inf_le'.mp (H p)
  rwa [← Subtype.ext <| q.2.eq_of_le p.2.ne_top hq2]

@[deprecated (since := "2026-07-09")] alias setOf_isMaximal_finite := setOfPred_isMaximal_finite

Depends on / 依赖: Finset, Finset.exists_inf_le, I.IsMaximal, IsMaximal, Set.finite_def, Subtype, Subtype.ext, Subtype.val, eq_of_le, exists_inf_le, finite_def, inf_le, isPrime, isPrime.inf_le, ne_top
-/
lemma setOfPred_isMaximal_finite : {I : Ideal R | I.IsMaximal}.Finite := by
  have ⟨s, H⟩ := Finset.exists_inf_le (Subtype.val (p := fun I : Ideal R => I.IsMaximal))
  refine Set.finite_def.2 ⟨s, fun p => ?_⟩
  have ⟨q, hq1, hq2⟩ := p.2.isPrime.inf_le'.mp (H p)
  rwa [← Subtype.ext <| q.2.eq_of_le p.2.ne_top hq2]

@[deprecated (since := "2026-07-09")] alias setOf_isMaximal_finite := setOfPred_isMaximal_finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Finite (MaximalSpectrum R)
  body: haveI : Finite {I : Ideal R // I.IsMaximal} := (setOfPred_isMaximal_finite R).to_subtype
  .of_equiv _ (MaximalSpectrum.equivSubtype _).symm

中文:
实例 :
  签名: 有限 (极大谱 R)
  定义体: haveI : Finite {I : Ideal R // I.IsMaximal} := (setOfPred_isMaximal_finite R).to_subtype
  .of_equiv _ (MaximalSpectrum.equivSubtype _).symm

Depends on / 依赖: Finite, I.IsMaximal, IsMaximal, MaximalSpectrum, MaximalSpectrum.equivSubtype, equivSubtype, of_equiv, setOfPred_isMaximal_finite, to_subtype
-/
instance : Finite (MaximalSpectrum R) :=
  haveI : Finite {I : Ideal R // I.IsMaximal} := (setOfPred_isMaximal_finite R).to_subtype
  .of_equiv _ (MaximalSpectrum.equivSubtype _).symm

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [IsArtinianRing R]

variable (R) in
/--
lemma `isField_of_isDomain` / 引理 `isField_of_isDomain`

English:
lemma isField_of_isDomain
  given: [IsDomain R]
  statement: IsField R
  proof: by
  refine ⟨Nontrivial.exists_pair_ne, mul_comm, fun {x} hx => ?_⟩
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R)
  replace hy : x ^ n * (x * y - 1) = 0 := by
    rw [mul_sub]; rw [sub_eq_zero]
    convert! hy using 1
    simp [Nat.succ_eq_add_one, pow_add, mul_assoc]
  rw [mul_eq_zero]; rw [sub_eq_zero] at hy
exact ⟨_, hy.resolve_left pow_ne_zero _ hx⟩

中文:
引理 isField_of_isDomain
  条件: [是整环 R]
  结论: 是域 R
  证明: by
  refine ⟨Nontrivial.exists_pair_ne, mul_comm, fun {x} hx => ?_⟩
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R)
  replace hy : x ^ n * (x * y - 1) = 0 := by
    rw [mul_sub]; rw [sub_eq_zero]
    convert! hy using 1
    simp [Nat.succ_eq_add_one, pow_add, mul_assoc]
  rw [mul_eq_zero]; rw [sub_eq_zero] at hy
exact ⟨_, hy.resolve_left pow_ne_zero _ hx⟩

Depends on / 依赖: IsArtinian, IsArtinian.exists_pow_succ_smul_dvd, Nat.succ_eq_add_one, Nontrivial, Nontrivial.exists_pair_ne, convert, exists_pair_ne, exists_pow_succ_smul_dvd, hy.resolve_left, mul_assoc, mul_comm, mul_eq_zero, mul_sub, pow_add, pow_ne_zero, replace, resolve_left, sub_eq_zero, succ_eq_add_one
-/
lemma isField_of_isDomain [IsDomain R] : IsField R := by
  refine ⟨Nontrivial.exists_pair_ne, mul_comm, fun {x} hx => ?_⟩
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R)
  replace hy : x ^ n * (x * y - 1) = 0 := by
    rw [mul_sub]; rw [sub_eq_zero]
    convert! hy using 1
    simp [Nat.succ_eq_add_one, pow_add, mul_assoc]
  rw [mul_eq_zero]; rw [sub_eq_zero] at hy
exact ⟨_, hy.resolve_left pow_ne_zero _ hx⟩

-- Note: type class synthesis should try to synthesize `p.IsPrime` before `IsArtinianRing R`,
-- hence the argument order.
/--
Instance `isMaximal_of_isPrime` / 实例 `isMaximal_of_isPrime`

English:
instance isMaximal_of_isPrime
  signature: {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
  body: Ideal.Quotient.maximal_of_isField _ (isField_of_isDomain _)

中文:
实例 isMaximal_of_isPrime
  签名: {R : 类型} [交换环 R] (p : 理想 R) [p.是素]
  定义体: Ideal.Quotient.maximal_of_isField _ (isField_of_isDomain _)

Depends on / 依赖: Ideal.Quotient.maximal_of_isField, Quotient, isField_of_isDomain, maximal_of_isField
-/
instance isMaximal_of_isPrime {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    [IsArtinianRing R] : p.IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (isField_of_isDomain _)

/--
lemma `isPrime_iff_isMaximal` / 引理 `isPrime_iff_isMaximal`

English:
lemma isPrime_iff_isMaximal
  given: (p : Ideal R)
  statement: p.IsPrime ↔ p.IsMaximal
  proof: ⟨fun _ => isMaximal_of_isPrime p, fun h => h.isPrime⟩

中文:
引理 isPrime_iff_isMaximal
  条件: (p : 理想 R)
  结论: p.是素 ↔ p.是极大
  证明: ⟨fun _ => isMaximal_of_isPrime p, fun h => h.isPrime⟩

Depends on / 依赖: h.isPrime, isMaximal_of_isPrime, isPrime
-/
lemma isPrime_iff_isMaximal (p : Ideal R) : p.IsPrime ↔ p.IsMaximal :=
  ⟨fun _ => isMaximal_of_isPrime p, fun h => h.isPrime⟩

/--
theorem `mem_minimalPrimes` / 定理 `mem_minimalPrimes`

English:
theorem mem_minimalPrimes
  given: {I p : Ideal R} [hp : p.IsPrime] (hIp : I <= p)
  statement: p in I.minimalPrimes
  proof: ⟨⟨hp, hIp⟩, fun q ⟨_, _⟩ hqp => ((isMaximal_of_isPrime q).eq_of_le hp.ne_top hqp).ge⟩

中文:
定理 mem_minimalPrimes
  条件: {I p : 理想 R} [hp : p.是素] (hIp : I <= p)
  结论: p in I.minimalPrimes
  证明: ⟨⟨hp, hIp⟩, fun q ⟨_, _⟩ hqp => ((isMaximal_of_isPrime q).eq_of_le hp.ne_top hqp).ge⟩

Depends on / 依赖: eq_of_le, hp.ne_top, isMaximal_of_isPrime, ne_top
-/
theorem mem_minimalPrimes {I p : Ideal R} [hp : p.IsPrime] (hIp : I <= p) : p in I.minimalPrimes :=
  ⟨⟨hp, hIp⟩, fun q ⟨_, _⟩ hqp => ((isMaximal_of_isPrime q).eq_of_le hp.ne_top hqp).ge⟩

/-- The prime spectrum is in bijection with the maximal spectrum. -/
@[simps]
/--
Definition of `primeSpectrumEquivMaximalSpectrum` / `primeSpectrumEquivMaximalSpectrum` 的定义

English:
definition primeSpectrumEquivMaximalSpectrum
  signature: : PrimeSpectrum R ≃ MaximalSpectrum R where
  body: ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal
.mpr I.isMaximal⟩ invFun I := ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal

中文:
定义 primeSpectrumEquivMaximalSpectrum
  签名: : 素谱 R ≃ 极大谱 R where
  定义体: ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal
.mpr I.isMaximal⟩ invFun I := ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal

Depends on / 依赖: I.asIdeal, asIdeal, isPrime_iff_isMaximal
-/
def primeSpectrumEquivMaximalSpectrum : PrimeSpectrum R ≃ MaximalSpectrum R where
.mp I.isPrime⟩ toFun I := ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal
.mpr I.isMaximal⟩ invFun I := ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal

/--
lemma `primeSpectrumEquivMaximalSpectrum_comp_asIdeal` / 引理 `primeSpectrumEquivMaximalSpectrum_comp_asIdeal`

English:
lemma primeSpectrumEquivMaximalSpectrum_comp_asIdeal
  proof: rfl

中文:
引理 primeSpectrumEquivMaximalSpectrum_comp_asIdeal
  证明: rfl
-/
lemma primeSpectrumEquivMaximalSpectrum_comp_asIdeal :
    MaximalSpectrum.asIdeal ∘ primeSpectrumEquivMaximalSpectrum =
      PrimeSpectrum.asIdeal (R := R) := rfl

/--
lemma `primeSpectrumEquivMaximalSpectrum_symm_comp_asIdeal` / 引理 `primeSpectrumEquivMaximalSpectrum_symm_comp_asIdeal`

English:
lemma primeSpectrumEquivMaximalSpectrum_symm_comp_asIdeal
  proof: rfl

中文:
引理 primeSpectrumEquivMaximalSpectrum_symm_comp_asIdeal
  证明: rfl
-/
lemma primeSpectrumEquivMaximalSpectrum_symm_comp_asIdeal :
    PrimeSpectrum.asIdeal ∘ primeSpectrumEquivMaximalSpectrum.symm =
      MaximalSpectrum.asIdeal (R := R) := rfl

/--
lemma `primeSpectrum_asIdeal_range_eq` / 引理 `primeSpectrum_asIdeal_range_eq`

English:
lemma primeSpectrum_asIdeal_range_eq
  proof: by
  simp only [PrimeSpectrum.range_asIdeal, MaximalSpectrum.range_asIdeal,
    isPrime_iff_isMaximal]

中文:
引理 primeSpectrum_asIdeal_range_eq
  证明: by
  simp only [PrimeSpectrum.range_asIdeal, MaximalSpectrum.range_asIdeal,
    isPrime_iff_isMaximal]

Depends on / 依赖: MaximalSpectrum, MaximalSpectrum.range_asIdeal, PrimeSpectrum, PrimeSpectrum.range_asIdeal, isPrime_iff_isMaximal, range_asIdeal
-/
lemma primeSpectrum_asIdeal_range_eq :
    range PrimeSpectrum.asIdeal = (range <| MaximalSpectrum.asIdeal (R := R)) := by
  simp only [PrimeSpectrum.range_asIdeal, MaximalSpectrum.range_asIdeal,
    isPrime_iff_isMaximal]

variable (R)

/--
theorem `nilradical_pow_eq_iInf` / 定理 `nilradical_pow_eq_iInf`

English:
theorem nilradical_pow_eq_iInf
  given: (n : Nat)
  proof: by
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  rw [← iInf_univ]; rw [← Finset.coe_univ]; rw [PrimeSpectrum.nilradical_eq_iInf]
  simp only [Finset.mem_coe]
  rw [← Ideal.prod_eq_iInf_of_pairwise_isCoprime fun I _ _ _ => .pow ∘ I.isCoprime_of_ne]; rw [Finset.prod_pow]; rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime fun I _ _ _ => I.isCoprime_of_ne]
  simp [Finset.mem_univ, iInf, IsArtinianRing.primeSpectrum_asIdeal_range_eq]

中文:
定理 nilradical_pow_eq_iInf
  条件: (n : 自然数)
  证明: by
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  rw [← iInf_univ]; rw [← Finset.coe_univ]; rw [PrimeSpectrum.nilradical_eq_iInf]
  simp only [Finset.mem_coe]
  rw [← Ideal.prod_eq_iInf_of_pairwise_isCoprime fun I _ _ _ => .pow ∘ I.isCoprime_of_ne]; rw [Finset.prod_pow]; rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime fun I _ _ _ => I.isCoprime_of_ne]
  simp [Finset.mem_univ, iInf, IsArtinianRing.primeSpectrum_asIdeal_range_eq]

Depends on / 依赖: Finset, Finset.coe_univ, Finset.mem_coe, Finset.mem_univ, Finset.prod_pow, Fintype, Fintype.ofFinite, I.isCoprime_of_ne, Ideal.prod_eq_iInf_of_pairwise_isCoprime, IsArtinianRing, IsArtinianRing.primeSpectrum_asIdeal_range_eq, MaximalSpectrum, PrimeSpectrum, PrimeSpectrum.nilradical_eq_iInf, coe_univ, iInf_univ, isCoprime_of_ne, mem_coe, mem_univ, nilradical_eq_iInf
-/
theorem nilradical_pow_eq_iInf (n : Nat) :
    nilradical R ^ n = iInf fun I : MaximalSpectrum R => I.1 ^ n := by
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  rw [← iInf_univ]; rw [← Finset.coe_univ]; rw [PrimeSpectrum.nilradical_eq_iInf]
  simp only [Finset.mem_coe]
  rw [← Ideal.prod_eq_iInf_of_pairwise_isCoprime fun I _ _ _ => .pow ∘ I.isCoprime_of_ne]; rw [Finset.prod_pow]; rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime fun I _ _ _ => I.isCoprime_of_ne]
  simp [Finset.mem_univ, iInf, IsArtinianRing.primeSpectrum_asIdeal_range_eq]

/--
theorem `nilradical_eq_iInf` / 定理 `nilradical_eq_iInf`

English:
theorem nilradical_eq_iInf
  statement: nilradical R = iInf MaximalSpectrum.asIdeal
  proof: by
  simpa using nilradical_pow_eq_iInf R 1

中文:
定理 nilradical_eq_iInf
  结论: nilradical R = iInf 极大谱.asIdeal
  证明: by
  simpa using nilradical_pow_eq_iInf R 1

Depends on / 依赖: nilradical_pow_eq_iInf
-/
theorem nilradical_eq_iInf : nilradical R = iInf MaximalSpectrum.asIdeal := by
  simpa using nilradical_pow_eq_iInf R 1

/--
lemma `setOfPred_isPrime_finite` / 引理 `setOfPred_isPrime_finite`

English:
lemma setOfPred_isPrime_finite
  statement: {I : Ideal R | I.IsPrime}.Finite
  proof: by
  simpa only [isPrime_iff_isMaximal] using setOfPred_isMaximal_finite R

@[deprecated (since := "2026-07-09")] alias setOf_isPrime_finite := setOfPred_isPrime_finite

中文:
引理 setOfPred_isPrime_finite
  结论: {I : 理想 R | I.是素}.有限
  证明: by
  simpa only [isPrime_iff_isMaximal] using setOfPred_isMaximal_finite R

@[deprecated (since := "2026-07-09")] alias setOf_isPrime_finite := setOfPred_isPrime_finite

Depends on / 依赖: isPrime_iff_isMaximal, setOfPred_isMaximal_finite
-/
lemma setOfPred_isPrime_finite : {I : Ideal R | I.IsPrime}.Finite := by
  simpa only [isPrime_iff_isMaximal] using setOfPred_isMaximal_finite R

@[deprecated (since := "2026-07-09")] alias setOf_isPrime_finite := setOfPred_isPrime_finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Finite (PrimeSpectrum R)
  body: haveI : Finite {I : Ideal R // I.IsPrime} := (setOfPred_isPrime_finite R).to_subtype
  .of_equiv _ (PrimeSpectrum.equivSubtype _).symm.toEquiv

中文:
实例 :
  签名: 有限 (素谱 R)
  定义体: haveI : Finite {I : Ideal R // I.IsPrime} := (setOfPred_isPrime_finite R).to_subtype
  .of_equiv _ (PrimeSpectrum.equivSubtype _).symm.toEquiv

Depends on / 依赖: Finite, I.IsPrime, IsPrime, PrimeSpectrum, PrimeSpectrum.equivSubtype, equivSubtype, of_equiv, setOfPred_isPrime_finite, symm.toEquiv, toEquiv, to_subtype
-/
instance : Finite (PrimeSpectrum R) :=
  haveI : Finite {I : Ideal R // I.IsPrime} := (setOfPred_isPrime_finite R).to_subtype
  .of_equiv _ (PrimeSpectrum.equivSubtype _).symm.toEquiv

/--
Definition of `fieldOfSubtypeIsMaximal` / `fieldOfSubtypeIsMaximal` 的定义

English:
definition fieldOfSubtypeIsMaximal
  body: Ideal.Quotient.field I.asIdeal

#adaptation_note

中文:
定义 fieldOfSubtypeIsMaximal
  定义体: Ideal.Quotient.field I.asIdeal

#adaptation_note
-/
@[instance_reducible, local instance] noncomputable def fieldOfSubtypeIsMaximal
    (I : MaximalSpectrum R) : Field (R ⧸ I.asIdeal) :=
  Ideal.Quotient.field I.asIdeal

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient of a commutative Artinian ring by its nilradical is isomorphic to
a finite product of fields, namely the quotients by the maximal ideals. -/
@[simps!]
/--
Definition of `quotNilradicalEquivPi` / `quotNilradicalEquivPi` 的定义

English:
definition quotNilradicalEquivPi
  signature: :
  body: (Ideal.quotientEquivAlgOfEq R (nilradical_eq_iInf R)).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient _ fun I _ => I.isCoprime_of_ne
      commutes' _ := rfl}

#adaptation_note

中文:
定义 quotNilradicalEquivPi
  签名: :
  定义体: (Ideal.quotientEquivAlgOfEq R (nilradical_eq_iInf R)).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient _ fun I _ => I.isCoprime_of_ne
      commutes' _ := rfl}

#adaptation_note

Depends on / 依赖: I.isCoprime_of_ne, Ideal.quotientEquivAlgOfEq, Ideal.quotientInfRingEquivPiQuotient, commutes, isCoprime_of_ne, nilradical_eq_iInf, quotientEquivAlgOfEq, quotientInfRingEquivPiQuotient
-/
noncomputable def quotNilradicalEquivPi :
    (R ⧸ nilradical R) ≃ₐ[R] forall I : MaximalSpectrum R, R ⧸ I.asIdeal :=
  (Ideal.quotientEquivAlgOfEq R (nilradical_eq_iInf R)).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient _ fun I _ => I.isCoprime_of_ne
      commutes' _ := rfl}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient of a commutative Artinian ring by a power of its nilradical is isomorphic to
a finite product of local rings, namely the quotients by the powers of the maximal ideals. -/
@[simps!]
/--
Definition of `quotNilradicalPowEquivPi` / `quotNilradicalPowEquivPi` 的定义

English:
definition quotNilradicalPowEquivPi
  signature: (n : Nat)
  body: (Ideal.quotientEquivAlgOfEq R (nilradical_pow_eq_iInf R n)).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient _ fun I _ => .pow ∘ I.isCoprime_of_ne
      commutes' _ := rfl}

中文:
定义 quotNilradicalPowEquivPi
  签名: (n : 自然数)
  定义体: (Ideal.quotientEquivAlgOfEq R (nilradical_pow_eq_iInf R n)).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient _ fun I _ => .pow ∘ I.isCoprime_of_ne
      commutes' _ := rfl}

Depends on / 依赖: I.isCoprime_of_ne, Ideal.quotientEquivAlgOfEq, Ideal.quotientInfRingEquivPiQuotient, commutes, isCoprime_of_ne, nilradical_pow_eq_iInf, quotientEquivAlgOfEq, quotientInfRingEquivPiQuotient
-/
noncomputable def quotNilradicalPowEquivPi (n : Nat) :
    (R ⧸ nilradical R ^ n) ≃ₐ[R] forall I : MaximalSpectrum R, R ⧸ I.asIdeal ^ n :=
  (Ideal.quotientEquivAlgOfEq R (nilradical_pow_eq_iInf R n)).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient _ fun I _ => .pow ∘ I.isCoprime_of_ne
      commutes' _ := rfl}

/--
Definition of `equivPi` / `equivPi` 的定义

English:
definition equivPi
  signature: [IsReduced R]
  body: .trans (.symm <| .quotientBot R R) .trans
    (Ideal.quotientEquivAlgOfEq R (nilradical_eq_zero R).symm) (quotNilradicalEquivPi R)

@[simp]

中文:
定义 equivPi
  签名: [是既约 R]
  定义体: .trans (.symm <| .quotientBot R R) .trans
    (Ideal.quotientEquivAlgOfEq R (nilradical_eq_zero R).symm) (quotNilradicalEquivPi R)

@[simp]

Depends on / 依赖: Ideal.quotientEquivAlgOfEq, nilradical_eq_zero, quotNilradicalEquivPi, quotientBot, quotientEquivAlgOfEq
-/
noncomputable def equivPi [IsReduced R] : R ≃ₐ[R] forall I : MaximalSpectrum R, R ⧸ I.asIdeal :=
.trans (.symm <| .quotientBot R R) .trans
    (Ideal.quotientEquivAlgOfEq R (nilradical_eq_zero R).symm) (quotNilradicalEquivPi R)

@[simp]
/--
lemma `equivPi_apply` / 引理 `equivPi_apply`

English:
lemma equivPi_apply
  given: [IsReduced R] (x : R) (m : MaximalSpectrum R)
  statement: equivPi R x m = x
  proof: rfl

中文:
引理 equivPi_apply
  条件: [是既约 R] (x : R) (m : 极大谱 R)
  结论: equivPi R x m = x
  证明: rfl
-/
lemma equivPi_apply [IsReduced R] (x : R) (m : MaximalSpectrum R) : equivPi R x m = x :=
  rfl

/--
theorem `isSemisimpleRing_of_isReduced` / 定理 `isSemisimpleRing_of_isReduced`

English:
theorem isSemisimpleRing_of_isReduced
  given: [IsReduced R]
  statement: IsSemisimpleRing R
  proof: (equivPi R).symm.isSemisimpleRing

中文:
定理 isSemisimpleRing_of_isReduced
  条件: [是既约 R]
  结论: IsSemisimpleRing R
  证明: (equivPi R).symm.isSemisimpleRing

Depends on / 依赖: equivPi, isSemisimpleRing, symm.isSemisimpleRing
-/
theorem isSemisimpleRing_of_isReduced [IsReduced R] : IsSemisimpleRing R :=
  (equivPi R).symm.isSemisimpleRing

end CommRing

section Ring

variable {R : Type*} [Ring R] [IsArtinianRing R]

/--
theorem `isSemisimpleRing_iff_jacobson` / 定理 `isSemisimpleRing_iff_jacobson`

English:
theorem isSemisimpleRing_iff_jacobson
  statement: IsSemisimpleRing R ↔ Ring.jacobson R = ⊥
  proof: IsArtinian.isSemisimpleModule_iff_jacobson R R

中文:
定理 isSemisimpleRing_iff_jacobson
  结论: IsSemisimpleRing R ↔ 环.jacobson R = ⊥
  证明: IsArtinian.isSemisimpleModule_iff_jacobson R R

Depends on / 依赖: IsArtinian, IsArtinian.isSemisimpleModule_iff_jacobson, isSemisimpleModule_iff_jacobson
-/
theorem isSemisimpleRing_iff_jacobson : IsSemisimpleRing R ↔ Ring.jacobson R = ⊥ :=
  IsArtinian.isSemisimpleModule_iff_jacobson R R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSemiprimaryRing R
  body: IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (Ring.jacobson_quotient_jacobson R)
  isNilpotent := by
    let Jac := Ring.jacobson R
    have ⟨n, hn⟩ := IsArtinian.monotone_stabilizes ⟨(Jac ^ ·), @Ideal.pow_le_pow_right _ _ _⟩
    have hn : Jac * Jac ^ n = Jac ^ n := by
      rw [← Ideal.IsTwoSided.pow_succ]; exact (hn _ n.le_succ).symm
    use n; by_contra ne
    have ⟨N, ⟨eq, ne⟩, min⟩ := wellFounded_lt.has_min {N | Jac * N = N ∧ N != ⊥} ⟨_, hn, ne⟩
    have : Jac ^ n * N = N := n.rec (by rw [Jac.pow_zero, N.one_mul])
      fun n hn => by rwa [Jac.pow_succ, mul_assoc, eq]
    let I x := Submodule.map (LinearMap.toSpanSingleton R R x) (Jac ^ n)
    have hI x : I x <= Ideal.span {x} := by
      rw [Ideal.span]; rw [LinearMap.span_singleton_eq_range]; exact LinearMap.map_le_range
    have ⟨x, hx⟩ : exists x in N, I x != ⊥ := by
      contrapose! ne
      rw [← this]; rw [← le_bot_iff]; rw [Ideal.mul_le]
      refine fun ri hi rn hn => ?_
      rw [← ne rn hn]
      exact ⟨ri, hi, rfl⟩
    rw [← Ideal.span_singleton_le_iff_mem] at hx
    have : I x = N := by
      refine ((hI x).trans hx.1).eq_of_not_lt (min _ ⟨?_, hx.2⟩)
      rw [← smul_eq_mul]; rw [← Submodule.map_smul'']; rw [smul_eq_mul]; rw [hn]
    have : Ideal.span {x} = N := le_antisymm hx.1 (this.symm.trans_le <| hI x)
    refine (this ▸ ne) ((Submodule.fg_span <| Set.finite_singleton x).eq_bot_of_le_jacobson_smul ?_)
    rw [← Ideal.span]; rw [this]; rw [smul_eq_mul]; rw [eq]

中文:
实例 :
  签名: 是Semiprimary环 R
  定义体: IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (Ring.jacobson_quotient_jacobson R)
  isNilpotent := by
    let Jac := Ring.jacobson R
    have ⟨n, hn⟩ := IsArtinian.monotone_stabilizes ⟨(Jac ^ ·), @Ideal.pow_le_pow_right _ _ _⟩
    have hn : Jac * Jac ^ n = Jac ^ n := by
      rw [← Ideal.IsTwoSided.pow_succ]; exact (hn _ n.le_succ).symm
    use n; by_contra ne
    have ⟨N, ⟨eq, ne⟩, min⟩ := wellFounded_lt.has_min {N | Jac * N = N ∧ N != ⊥} ⟨_, hn, ne⟩
    have : Jac ^ n * N = N := n.rec (by rw [Jac.pow_zero, N.one_mul])
      fun n hn => by rwa [Jac.pow_succ, mul_assoc, eq]
    let I x := Submodule.map (LinearMap.toSpanSingleton R R x) (Jac ^ n)
    have hI x : I x <= Ideal.span {x} := by
      rw [Ideal.span]; rw [LinearMap.span_singleton_eq_range]; exact LinearMap.map_le_range
    have ⟨x, hx⟩ : exists x in N, I x != ⊥ := by
      contrapose! ne
      rw [← this]; rw [← le_bot_iff]; rw [Ideal.mul_le]
      refine fun ri hi rn hn => ?_
      rw [← ne rn hn]
      exact ⟨ri, hi, rfl⟩
    rw [← Ideal.span_singleton_le_iff_mem] at hx
    have : I x = N := by
      refine ((hI x).trans hx.1).eq_of_not_lt (min _ ⟨?_, hx.2⟩)
      rw [← smul_eq_mul]; rw [← Submodule.map_smul'']; rw [smul_eq_mul]; rw [hn]
    have : Ideal.span {x} = N := le_antisymm hx.1 (this.symm.trans_le <| hI x)
    refine (this ▸ ne) ((Submodule.fg_span <| Set.finite_singleton x).eq_bot_of_le_jacobson_smul ?_)
    rw [← Ideal.span]; rw [this]; rw [smul_eq_mul]; rw [eq]

Depends on / 依赖: Ideal.IsTwoSided.pow_succ, Ideal.pow_le_pow_right, IsArtinian, IsArtinian.monotone_stabilizes, IsArtinianRing, IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr, IsTwoSided, Jac.pow_zero, N.one_mul, Ring.jacobson, Ring.jacobson_quotient_jacobson, has_min, isNilpotent, isSemisimpleRing_iff_jacobson, jacobson, jacobson_quotient_jacobson, le_succ, monotone_stabilizes, n.le_succ, n.rec
-/
instance : IsSemiprimaryRing R where
  isSemisimpleRing :=
    IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (Ring.jacobson_quotient_jacobson R)
  isNilpotent := by
    let Jac := Ring.jacobson R
    have ⟨n, hn⟩ := IsArtinian.monotone_stabilizes ⟨(Jac ^ ·), @Ideal.pow_le_pow_right _ _ _⟩
    have hn : Jac * Jac ^ n = Jac ^ n := by
      rw [← Ideal.IsTwoSided.pow_succ]; exact (hn _ n.le_succ).symm
    use n; by_contra ne
    have ⟨N, ⟨eq, ne⟩, min⟩ := wellFounded_lt.has_min {N | Jac * N = N ∧ N != ⊥} ⟨_, hn, ne⟩
    have : Jac ^ n * N = N := n.rec (by rw [Jac.pow_zero, N.one_mul])
      fun n hn => by rwa [Jac.pow_succ, mul_assoc, eq]
    let I x := Submodule.map (LinearMap.toSpanSingleton R R x) (Jac ^ n)
    have hI x : I x <= Ideal.span {x} := by
      rw [Ideal.span]; rw [LinearMap.span_singleton_eq_range]; exact LinearMap.map_le_range
    have ⟨x, hx⟩ : exists x in N, I x != ⊥ := by
      contrapose! ne
      rw [← this]; rw [← le_bot_iff]; rw [Ideal.mul_le]
      refine fun ri hi rn hn => ?_
      rw [← ne rn hn]
      exact ⟨ri, hi, rfl⟩
    rw [← Ideal.span_singleton_le_iff_mem] at hx
    have : I x = N := by
      refine ((hI x).trans hx.1).eq_of_not_lt (min _ ⟨?_, hx.2⟩)
      rw [← smul_eq_mul]; rw [← Submodule.map_smul'']; rw [smul_eq_mul]; rw [hn]
    have : Ideal.span {x} = N := le_antisymm hx.1 (this.symm.trans_le <| hI x)
    refine (this ▸ ne) ((Submodule.fg_span <| Set.finite_singleton x).eq_bot_of_le_jacobson_smul ?_)
    rw [← Ideal.span]; rw [this]; rw [smul_eq_mul]; rw [eq]

end Ring

end IsArtinianRing
