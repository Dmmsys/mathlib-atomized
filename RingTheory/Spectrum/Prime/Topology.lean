/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Order.Ring.Idempotent
public import Mathlib.Order.Heyting.Hom
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Spectrum.Maximal.Localization
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Spectral.Basic

/-!
# The Zariski topology on the prime spectrum of a commutative (semi)ring

## Conventions

We denote subsets of (semi)rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

## Main definitions

* `PrimeSpectrum.zariskiTopology`: the Zariski topology on the prime spectrum, whose closed sets
  are zero loci (`zeroLocus`).

* `PrimeSpectrum.basicOpen`: the complement of the zero locus of a single element.
  The `basicOpen`s form a topological basis of the Zariski topology:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`.

* `PrimeSpectrum.comap`: the continuous map between prime spectra induced by a ring homomorphism.

* `IsLocalRing.closedPoint`: the maximal ideal of a local ring is the unique closed point in its
  prime spectrum.

## Main results

* `PrimeSpectrum.instSpectralSpace`: every prime spectrum is a spectral space, i.e. it is
  quasi-compact, sober (in particular T0), quasi-separated, and its compact open subsets form
  a topological basis.

* `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`: the prime spectrum of a
  commutative semiring is discrete iff it is finite and the semiring has zero Krull dimension
  or is trivial.

* `PrimeSpectrum.localization_comap_range`, `PrimeSpectrum.localization_comap_isEmbedding`:
  localization at a submonoid of a commutative semiring induces an embedding between the prime
  spectra, with range consisting of prime ideals disjoint from the submonoid.

* `PrimeSpectrum.localization_away_comap_range`: for localization away from an element, the
  range of the embedding is the `basicOpen` associated to the element.

* `PrimeSpectrum.comap_isEmbedding_of_surjective`: a surjective ring homomorphism between
  commutative semirings induces an embedding between the prime spectra.

* `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`: a surjective ring homomorphism between
  commutative rings induces a closed embedding between the prime spectra.

* `PrimeSpectrum.primeSpectrumProdHomeo`: the prime spectrum of a product semiring is homeomorphic
  to the disjoint union of the prime spectra.

* `PrimeSpectrum.stableUnderSpecialization_range_iff`: the range of `PrimeSpectrum.comap _` is
  closed iff it is stable under specialization.

* `PrimeSpectrum.denseRange_comap_iff_minimalPrimes`,
  `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`: the range of `comap f` is dense
  iff it contains all minimal primes, iff the kernel of `f` is contained in the nilradical.

* `PrimeSpectrum.isClosedMap_comap_of_isIntegral`: `comap f` is a closed map if `f` is integral.

* `PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom`: `f : R →+* S` is integral if
  `comap (Polynomial.mapRingHom f : R[X] →+* S[X])` is a closed map.

In the prime spectrum of a commutative semiring:

* `PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal`, `PrimeSpectrum.isRadical_vanishingIdeal`,
  `PrimeSpectrum.zeroLocus_eq_iff`, `PrimeSpectrum.vanishingIdeal_anti_mono_iff`:
  closed subsets correspond to radical ideals.

* `PrimeSpectrum.isClosed_singleton_iff_isMaximal`: closed points correspond to maximal ideals.

* `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`: irreducible closed subsets correspond
  to prime ideals.

* `minimalPrimes.equivIrreducibleComponents`: irreducible components correspond to minimal primes.

* `PrimeSpectrum.mulZeroAddOneEquivClopens`: clopen subsets correspond to pairs of elements
  that add up to 1 and multiply to 0 in the semiring.

* `PrimeSpectrum.isIdempotentElemEquivClopens`: (if the semiring is a ring) clopen subsets
  correspond to idempotents in the ring.

-/

@[expose] public section

open Topology

noncomputable section

universe u v

variable (R : Type u) (S : Type v)

namespace PrimeSpectrum

section CommSemiring

variable [CommSemiring R] [CommSemiring S]
variable {R S}

/--
Instance `zariskiTopology` / 实例 `zariskiTopology`

English:
instance zariskiTopology
  signature: : TopologicalSpace (PrimeSpectrum R)
  body: TopologicalSpace.ofClosed (Set.range PrimeSpectrum.zeroLocus) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      choose f hf using fun i : Zs => h i.prop
      simp only [← hf]
      exact ⟨_, zeroLocus_iUnion _⟩)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus s t).symm⟩)

中文:
实例 zariskiTopology
  签名: : 拓扑空间 (素谱 R)
  定义体: TopologicalSpace.ofClosed (Set.range PrimeSpectrum.zeroLocus) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      choose f hf using fun i : Zs => h i.prop
      simp only [← hf]
      exact ⟨_, zeroLocus_iUnion _⟩)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus s t).symm⟩)

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.zeroLocus, Set.range, Set.sInter_eq_iInter, Set.univ, TopologicalSpace, TopologicalSpace.ofClosed, i.prop, ofClosed, sInter_eq_iInter, union_zeroLocus, zeroLocus, zeroLocus_iUnion
-/
instance zariskiTopology : TopologicalSpace (PrimeSpectrum R) :=
  TopologicalSpace.ofClosed (Set.range PrimeSpectrum.zeroLocus) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      choose f hf using fun i : Zs => h i.prop
      simp only [← hf]
      exact ⟨_, zeroLocus_iUnion _⟩)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus s t).symm⟩)

/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: (U : Set (PrimeSpectrum R))
  statement: IsOpen U ↔ exists s, Uᶜ = zeroLocus s
  proof: by
  simp only [@eq_comm _ Uᶜ]; rfl

中文:
定理 isOpen_iff
  条件: (U : 集合 (素谱 R))
  结论: 是开集 U ↔ 存在 s, Uᶜ = zeroLocus s
  证明: by
  simp only [@eq_comm _ Uᶜ]; rfl

Depends on / 依赖: eq_comm
-/
theorem isOpen_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ exists s, Uᶜ = zeroLocus s := by
  simp only [@eq_comm _ Uᶜ]; rfl

/--
theorem `isClosed_iff_zeroLocus` / 定理 `isClosed_iff_zeroLocus`

English:
theorem isClosed_iff_zeroLocus
  given: (Z : Set (PrimeSpectrum R))
  statement: IsClosed Z ↔ exists s, Z = zeroLocus s
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff]; rw [compl_compl]

中文:
定理 isClosed_iff_zeroLocus
  条件: (Z : 集合 (素谱 R))
  结论: 是闭集 Z ↔ 存在 s, Z = zeroLocus s
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff]; rw [compl_compl]

Depends on / 依赖: compl_compl, isOpen_compl_iff, isOpen_iff
-/
theorem isClosed_iff_zeroLocus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ exists s, Z = zeroLocus s := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff]; rw [compl_compl]

/--
theorem `isClosed_iff_zeroLocus_ideal` / 定理 `isClosed_iff_zeroLocus_ideal`

English:
theorem isClosed_iff_zeroLocus_ideal
  given: (Z : Set (PrimeSpectrum R))
  proof: (isClosed_iff_zeroLocus _).trans
    ⟨fun ⟨s, hs⟩ => ⟨_, (zeroLocus_span s).substr hs⟩, fun ⟨I, hI⟩ => ⟨I, hI⟩⟩

中文:
定理 isClosed_iff_zeroLocus_ideal
  条件: (Z : 集合 (素谱 R))
  证明: (isClosed_iff_zeroLocus _).trans
    ⟨fun ⟨s, hs⟩ => ⟨_, (zeroLocus_span s).substr hs⟩, fun ⟨I, hI⟩ => ⟨I, hI⟩⟩

Depends on / 依赖: isClosed_iff_zeroLocus, substr, zeroLocus_span
-/
theorem isClosed_iff_zeroLocus_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ exists I : Ideal R, Z = zeroLocus I :=
  (isClosed_iff_zeroLocus _).trans
    ⟨fun ⟨s, hs⟩ => ⟨_, (zeroLocus_span s).substr hs⟩, fun ⟨I, hI⟩ => ⟨I, hI⟩⟩

/--
theorem `isClosed_iff_zeroLocus_radical_ideal` / 定理 `isClosed_iff_zeroLocus_radical_ideal`

English:
theorem isClosed_iff_zeroLocus_radical_ideal
  given: (Z : Set (PrimeSpectrum R))
  proof: (isClosed_iff_zeroLocus_ideal _).trans
    ⟨fun ⟨I, hI⟩ => ⟨_, I.radical_isRadical, (zeroLocus_radical I).substr hI⟩, fun ⟨I, _, hI⟩ =>
      ⟨I, hI⟩⟩

中文:
定理 isClosed_iff_zeroLocus_radical_ideal
  条件: (Z : 集合 (素谱 R))
  证明: (isClosed_iff_zeroLocus_ideal _).trans
    ⟨fun ⟨I, hI⟩ => ⟨_, I.radical_isRadical, (zeroLocus_radical I).substr hI⟩, fun ⟨I, _, hI⟩ =>
      ⟨I, hI⟩⟩

Depends on / 依赖: I.radical_isRadical, isClosed_iff_zeroLocus_ideal, radical_isRadical, substr, zeroLocus_radical
-/
theorem isClosed_iff_zeroLocus_radical_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ exists I : Ideal R, I.IsRadical ∧ Z = zeroLocus I :=
  (isClosed_iff_zeroLocus_ideal _).trans
    ⟨fun ⟨I, hI⟩ => ⟨_, I.radical_isRadical, (zeroLocus_radical I).substr hI⟩, fun ⟨I, _, hI⟩ =>
      ⟨I, hI⟩⟩

/--
theorem `isClosed_zeroLocus` / 定理 `isClosed_zeroLocus`

English:
theorem isClosed_zeroLocus
  given: (s : Set R)
  statement: IsClosed (zeroLocus s)
  proof: by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

中文:
定理 isClosed_zeroLocus
  条件: (s : 集合 R)
  结论: 是闭集 (zeroLocus s)
  证明: by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

Depends on / 依赖: isClosed_iff_zeroLocus
-/
theorem isClosed_zeroLocus (s : Set R) : IsClosed (zeroLocus s) := by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `zeroLocus_vanishingIdeal_eq_closure` / 定理 `zeroLocus_vanishingIdeal_eq_closure`

English:
theorem zeroLocus_vanishingIdeal_eq_closure
  given: (t : Set (PrimeSpectrum R))
  proof: by
.mp isClosed_closure with ⟨I, hI⟩ rcases isClosed_iff_zeroLocus (closure t)
  rw [subset_antisymm_iff]; rw [(isClosed_zeroLocus _).closure_subset_iff]; rw [hI]; rw [subset_zeroLocus_iff_subset_vanishingIdeal]; rw [(gc R).u_l_u_eq_u]; rw [← subset_zeroLocus_iff_subset_vanishingIdeal]; rw [← hI]
  exact ⟨subset_closure, subset_zeroLocus_vanishingIdeal t⟩

中文:
定理 zeroLocus_vanishingIdeal_eq_closure
  条件: (t : 集合 (素谱 R))
  证明: by
.mp isClosed_closure with ⟨I, hI⟩ rcases isClosed_iff_zeroLocus (closure t)
  rw [subset_antisymm_iff]; rw [(isClosed_zeroLocus _).closure_subset_iff]; rw [hI]; rw [subset_zeroLocus_iff_subset_vanishingIdeal]; rw [(gc R).u_l_u_eq_u]; rw [← subset_zeroLocus_iff_subset_vanishingIdeal]; rw [← hI]
  exact ⟨subset_closure, subset_zeroLocus_vanishingIdeal t⟩

Depends on / 依赖: closure, closure_subset_iff, isClosed_closure, isClosed_iff_zeroLocus, isClosed_zeroLocus, subset_antisymm_iff, subset_closure, subset_zeroLocus_iff_subset_vanishingIdeal, subset_zeroLocus_vanishingIdeal, u_l_u_eq_u
-/
theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (PrimeSpectrum R)) :
    zeroLocus (vanishingIdeal t : Set R) = closure t := by
.mp isClosed_closure with ⟨I, hI⟩ rcases isClosed_iff_zeroLocus (closure t)
  rw [subset_antisymm_iff]; rw [(isClosed_zeroLocus _).closure_subset_iff]; rw [hI]; rw [subset_zeroLocus_iff_subset_vanishingIdeal]; rw [(gc R).u_l_u_eq_u]; rw [← subset_zeroLocus_iff_subset_vanishingIdeal]; rw [← hI]
  exact ⟨subset_closure, subset_zeroLocus_vanishingIdeal t⟩

/--
theorem `vanishingIdeal_closure` / 定理 `vanishingIdeal_closure`

English:
theorem vanishingIdeal_closure
  given: (t : Set (PrimeSpectrum R))
  proof: zeroLocus_vanishingIdeal_eq_closure t ▸ (gc R).u_l_u_eq_u t

中文:
定理 vanishingIdeal_closure
  条件: (t : 集合 (素谱 R))
  证明: zeroLocus_vanishingIdeal_eq_closure t ▸ (gc R).u_l_u_eq_u t

Depends on / 依赖: u_l_u_eq_u, zeroLocus_vanishingIdeal_eq_closure
-/
theorem vanishingIdeal_closure (t : Set (PrimeSpectrum R)) :
    vanishingIdeal (closure t) = vanishingIdeal t :=
  zeroLocus_vanishingIdeal_eq_closure t ▸ (gc R).u_l_u_eq_u t

/--
theorem `closure_singleton` / 定理 `closure_singleton`

English:
theorem closure_singleton
  given: (x)
  statement: closure ({x} : Set (PrimeSpectrum R)) = zeroLocus x.asIdeal
  proof: by
  rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_singleton]

中文:
定理 closure_singleton
  条件: (x)
  结论: closure ({x} : 集合 (素谱 R)) = zeroLocus x.asIdeal
  证明: by
  rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_singleton]

Depends on / 依赖: vanishingIdeal_singleton, zeroLocus_vanishingIdeal_eq_closure
-/
theorem closure_singleton (x) : closure ({x} : Set (PrimeSpectrum R)) = zeroLocus x.asIdeal := by
  rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_singleton]

/--
theorem `isClosed_singleton_iff_isMaximal` / 定理 `isClosed_singleton_iff_isMaximal`

English:
theorem isClosed_singleton_iff_isMaximal
  given: (x : PrimeSpectrum R)
  proof: by
  rw [← closure_subset_iff_isClosed]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_singleton]
  constructor <;> intro H
  · rcases x.asIdeal.exists_le_maximal x.2.1 with ⟨m, hm, hxm⟩
    exact (congr_arg asIdeal (@H ⟨m, hm.isPrime⟩ hxm)) ▸ hm
  · exact fun p hp => PrimeSpectrum.ext (H.eq_of_le p.2.1 hp).symm

中文:
定理 isClosed_singleton_iff_isMaximal
  条件: (x : 素谱 R)
  证明: by
  rw [← closure_subset_iff_isClosed]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_singleton]
  constructor <;> intro H
  · rcases x.asIdeal.exists_le_maximal x.2.1 with ⟨m, hm, hxm⟩
    exact (congr_arg asIdeal (@H ⟨m, hm.isPrime⟩ hxm)) ▸ hm
  · exact fun p hp => PrimeSpectrum.ext (H.eq_of_le p.2.1 hp).symm

Depends on / 依赖: H.eq_of_le, PrimeSpectrum, PrimeSpectrum.ext, asIdeal, closure_subset_iff_isClosed, congr_arg, eq_of_le, exists_le_maximal, hm.isPrime, isPrime, vanishingIdeal_singleton, x.asIdeal.exists_le_maximal, zeroLocus_vanishingIdeal_eq_closure
-/
theorem isClosed_singleton_iff_isMaximal (x : PrimeSpectrum R) :
    IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal := by
  rw [← closure_subset_iff_isClosed]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_singleton]
  constructor <;> intro H
  · rcases x.asIdeal.exists_le_maximal x.2.1 with ⟨m, hm, hxm⟩
    exact (congr_arg asIdeal (@H ⟨m, hm.isPrime⟩ hxm)) ▸ hm
  · exact fun p hp => PrimeSpectrum.ext (H.eq_of_le p.2.1 hp).symm

/--
theorem `isRadical_vanishingIdeal` / 定理 `isRadical_vanishingIdeal`

English:
theorem isRadical_vanishingIdeal
  given: (s : Set (PrimeSpectrum R))
  statement: (vanishingIdeal s).IsRadical
  proof: by
  rw [← vanishingIdeal_closure]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_zeroLocus_eq_radical]
  apply Ideal.radical_isRadical

中文:
定理 isRadical_vanishingIdeal
  条件: (s : 集合 (素谱 R))
  结论: (vanishingIdeal s).IsRadical
  证明: by
  rw [← vanishingIdeal_closure]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_zeroLocus_eq_radical]
  apply Ideal.radical_isRadical

Depends on / 依赖: Ideal.radical_isRadical, radical_isRadical, vanishingIdeal_closure, vanishingIdeal_zeroLocus_eq_radical, zeroLocus_vanishingIdeal_eq_closure
-/
theorem isRadical_vanishingIdeal (s : Set (PrimeSpectrum R)) : (vanishingIdeal s).IsRadical := by
  rw [← vanishingIdeal_closure]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_zeroLocus_eq_radical]
  apply Ideal.radical_isRadical

/--
theorem `zeroLocus_eq_iff` / 定理 `zeroLocus_eq_iff`

English:
theorem zeroLocus_eq_iff
  given: {I J : Ideal R}
  proof: by
  constructor
  · intro h; simp_rw [← vanishingIdeal_zeroLocus_eq_radical, h]
  · intro h; rw [← zeroLocus_radical, h, zeroLocus_radical]

中文:
定理 zeroLocus_eq_iff
  条件: {I J : 理想 R}
  证明: by
  constructor
  · intro h; simp_rw [← vanishingIdeal_zeroLocus_eq_radical, h]
  · intro h; rw [← zeroLocus_radical, h, zeroLocus_radical]

Depends on / 依赖: simp_rw, vanishingIdeal_zeroLocus_eq_radical, zeroLocus_radical
-/
theorem zeroLocus_eq_iff {I J : Ideal R} :
    zeroLocus (I : Set R) = zeroLocus J ↔ I.radical = J.radical := by
  constructor
  · intro h; simp_rw [← vanishingIdeal_zeroLocus_eq_radical, h]
  · intro h; rw [← zeroLocus_radical, h, zeroLocus_radical]

/--
theorem `vanishingIdeal_anti_mono_iff` / 定理 `vanishingIdeal_anti_mono_iff`

English:
theorem vanishingIdeal_anti_mono_iff
  given: {s t : Set (PrimeSpectrum R)} (ht : IsClosed t)
  proof: ⟨vanishingIdeal_anti_mono, fun h => by
    rw [← ht.closure_subset_iff]; rw [← ht.closure_eq]
    convert! ← zeroLocus_anti_mono_ideal h <;> apply zeroLocus_vanishingIdeal_eq_closure⟩

中文:
定理 vanishingIdeal_anti_mono_iff
  条件: {s t : 集合 (素谱 R)} (ht : 是闭集 t)
  证明: ⟨vanishingIdeal_anti_mono, fun h => by
    rw [← ht.closure_subset_iff]; rw [← ht.closure_eq]
    convert! ← zeroLocus_anti_mono_ideal h <;> apply zeroLocus_vanishingIdeal_eq_closure⟩

Depends on / 依赖: closure_eq, closure_subset_iff, convert, ht.closure_eq, ht.closure_subset_iff, vanishingIdeal_anti_mono, zeroLocus_anti_mono_ideal, zeroLocus_vanishingIdeal_eq_closure
-/
theorem vanishingIdeal_anti_mono_iff {s t : Set (PrimeSpectrum R)} (ht : IsClosed t) :
    s subseteq t ↔ vanishingIdeal t <= vanishingIdeal s :=
  ⟨vanishingIdeal_anti_mono, fun h => by
    rw [← ht.closure_subset_iff]; rw [← ht.closure_eq]
    convert! ← zeroLocus_anti_mono_ideal h <;> apply zeroLocus_vanishingIdeal_eq_closure⟩

/--
theorem `vanishingIdeal_strict_anti_mono_iff` / 定理 `vanishingIdeal_strict_anti_mono_iff`

English:
theorem vanishingIdeal_strict_anti_mono_iff
  statement: {s t : Set (PrimeSpectrum R)} (hs : IsClosed s)
  proof: by
  rw [Set.ssubset_def]; rw [vanishingIdeal_anti_mono_iff hs]; rw [vanishingIdeal_anti_mono_iff ht]; rw [lt_iff_le_not_ge]

中文:
定理 vanishingIdeal_strict_anti_mono_iff
  结论: {s t : 集合 (素谱 R)} (hs : 是闭集 s)
  证明: by
  rw [Set.ssubset_def]; rw [vanishingIdeal_anti_mono_iff hs]; rw [vanishingIdeal_anti_mono_iff ht]; rw [lt_iff_le_not_ge]

Depends on / 依赖: Set.ssubset_def, lt_iff_le_not_ge, ssubset_def, vanishingIdeal_anti_mono_iff
-/
theorem vanishingIdeal_strict_anti_mono_iff {s t : Set (PrimeSpectrum R)} (hs : IsClosed s)
    (ht : IsClosed t) : s ⊂ t ↔ vanishingIdeal t < vanishingIdeal s := by
  rw [Set.ssubset_def]; rw [vanishingIdeal_anti_mono_iff hs]; rw [vanishingIdeal_anti_mono_iff ht]; rw [lt_iff_le_not_ge]

/--
Definition of `closedsEmbedding` / `closedsEmbedding` 的定义

English:
definition closedsEmbedding
  signature: (R : Type*) [CommSemiring R]
  body: OrderEmbedding.ofMapLEIff (fun s => vanishingIdeal ↑(OrderDual.ofDual s)) fun s _ =>
    (vanishingIdeal_anti_mono_iff s.2).symm

中文:
定义 closedsEmbedding
  签名: (R : 类型) [交换半环 R]
  定义体: OrderEmbedding.ofMapLEIff (fun s => vanishingIdeal ↑(OrderDual.ofDual s)) fun s _ =>
    (vanishingIdeal_anti_mono_iff s.2).symm

Depends on / 依赖: OrderDual, OrderDual.ofDual, OrderEmbedding, OrderEmbedding.ofMapLEIff, ofDual, ofMapLEIff, vanishingIdeal, vanishingIdeal_anti_mono_iff
-/
def closedsEmbedding (R : Type*) [CommSemiring R] :
    (TopologicalSpace.Closeds <| PrimeSpectrum R)ᵒᵈ ↪o Ideal R :=
  OrderEmbedding.ofMapLEIff (fun s => vanishingIdeal ↑(OrderDual.ofDual s)) fun s _ =>
    (vanishingIdeal_anti_mono_iff s.2).symm

/--
theorem `t1Space_iff_isField` / 定理 `t1Space_iff_isField`

English:
theorem t1Space_iff_isField
  given: [IsDomain R]
  statement: T1Space (PrimeSpectrum R) ↔ IsField R
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · intro h
    exact
      Classical.not_not.1
        (mt
          (Ring.ne_bot_of_isMaximal_of_not_isField <|
            (isClosed_singleton_iff_isMaximal _).1 (T1Space.t1 ⟨⊥, inferInstance⟩))
          (by simp))
  · refine ⟨fun x => (isClosed_singleton_iff_isMaximal x).2 ?_⟩
    by_cases hx : x.asIdeal = ⊥
    · let := h.toSemifield
      exact hx.symm ▸ Ideal.bot_isMaximal
    · exact absurd h (Ring.not_isField_iff_exists_prime.2 ⟨x.asIdeal, ⟨hx, x.2⟩⟩)

local notation "Z(" a ")" => zeroLocus (a : Set R)

中文:
定理 t1Space_iff_isField
  条件: [是整环 R]
  结论: T1空间 (素谱 R) ↔ 是域 R
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · intro h
    exact
      Classical.not_not.1
        (mt
          (Ring.ne_bot_of_isMaximal_of_not_isField <|
            (isClosed_singleton_iff_isMaximal _).1 (T1Space.t1 ⟨⊥, inferInstance⟩))
          (by simp))
  · refine ⟨fun x => (isClosed_singleton_iff_isMaximal x).2 ?_⟩
    by_cases hx : x.asIdeal = ⊥
    · let := h.toSemifield
      exact hx.symm ▸ Ideal.bot_isMaximal
    · exact absurd h (Ring.not_isField_iff_exists_prime.2 ⟨x.asIdeal, ⟨hx, x.2⟩⟩)

local notation "Z(" a ")" => zeroLocus (a : Set R)

Depends on / 依赖: Classical, Classical.not_not, Ideal.bot_isMaximal, Ring.ne_bot_of_isMaximal_of_not_isField, Ring.not_isField_iff_exists_prime, T1Space, T1Space.t1, absurd, asIdeal, bot_isMaximal, h.toSemifield, hx.symm, isClosed_singleton_iff_isMaximal, ne_bot_of_isMaximal_of_not_isField, not_isField_iff_exists_prime, not_not, toSemifield, x.asIdeal
-/
theorem t1Space_iff_isField [IsDomain R] : T1Space (PrimeSpectrum R) ↔ IsField R := by
  refine ⟨?_, fun h => ?_⟩
  · intro h
    exact
      Classical.not_not.1
        (mt
          (Ring.ne_bot_of_isMaximal_of_not_isField <|
            (isClosed_singleton_iff_isMaximal _).1 (T1Space.t1 ⟨⊥, inferInstance⟩))
          (by simp))
  · refine ⟨fun x => (isClosed_singleton_iff_isMaximal x).2 ?_⟩
    by_cases hx : x.asIdeal = ⊥
    · let := h.toSemifield
      exact hx.symm ▸ Ideal.bot_isMaximal
    · exact absurd h (Ring.not_isField_iff_exists_prime.2 ⟨x.asIdeal, ⟨hx, x.2⟩⟩)

local notation "Z(" a ")" => zeroLocus (a : Set R)

/--
theorem `isIrreducible_zeroLocus_iff_of_radical` / 定理 `isIrreducible_zeroLocus_iff_of_radical`

English:
theorem isIrreducible_zeroLocus_iff_of_radical
  given: (I : Ideal R) (hI : I.IsRadical)
  proof: by
  rw [Ideal.isPrime_iff]; rw [IsIrreducible]
  apply and_congr
  · rw [Set.nonempty_iff_ne_empty, Ne, zeroLocus_empty_iff_eq_top]
  · trans forall x y : Ideal R, Z(I) subseteq Z(x) union Z(y) -> Z(I) subseteq Z(x) ∨ Z(I) subseteq Z(y)
    · simp_rw [isPreirreducible_iff_isClosed_union_isClosed, isClosed_iff_zeroLocus_ideal]
      constructor
      · rintro h x y
        exact h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      · rintro h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact h x y
    · simp_rw [← zeroLocus_inf, subset_zeroLocus_iff_le_vanishingIdeal,
        vanishingIdeal_zeroLocus_eq_radical, hI.radical]
      constructor
      · simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ←
          Ideal.span_singleton_mul_span_singleton]
        refine fun h x y h' => h _ _ ?_
        rw [← hI.radical_le_iff] at h' ⊢
        simpa only [Ideal.radical_inf, Ideal.radical_mul] using h'
      · simp_rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
        rintro h s t h' ⟨x, hx, hx'⟩ y hy
        exact h (h' ⟨Ideal.mul_mem_right _ _ hx, Ideal.mul_mem_left _ _ hy⟩) hx'

中文:
定理 isIrreducible_zeroLocus_iff_of_radical
  条件: (I : 理想 R) (hI : I.IsRadical)
  证明: by
  rw [Ideal.isPrime_iff]; rw [IsIrreducible]
  apply and_congr
  · rw [Set.nonempty_iff_ne_empty, Ne, zeroLocus_empty_iff_eq_top]
  · trans forall x y : Ideal R, Z(I) subseteq Z(x) union Z(y) -> Z(I) subseteq Z(x) ∨ Z(I) subseteq Z(y)
    · simp_rw [isPreirreducible_iff_isClosed_union_isClosed, isClosed_iff_zeroLocus_ideal]
      constructor
      · rintro h x y
        exact h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      · rintro h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact h x y
    · simp_rw [← zeroLocus_inf, subset_zeroLocus_iff_le_vanishingIdeal,
        vanishingIdeal_zeroLocus_eq_radical, hI.radical]
      constructor
      · simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ←
          Ideal.span_singleton_mul_span_singleton]
        refine fun h x y h' => h _ _ ?_
        rw [← hI.radical_le_iff] at h' ⊢
        simpa only [Ideal.radical_inf, Ideal.radical_mul] using h'
      · simp_rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
        rintro h s t h' ⟨x, hx, hx'⟩ y hy
        exact h (h' ⟨Ideal.mul_mem_right _ _ hx, Ideal.mul_mem_left _ _ hy⟩) hx'

Depends on / 依赖: Ideal.isPrime_iff, IsIrreducible, Set.nonempty_iff_ne_empty, and_congr, isClosed_iff_zeroLocus_ideal, isPreirreducible_iff_isClosed_union_isClosed, isPrime_iff, nonempty_iff_ne_empty, simp_rw, subset_zeroLocus_iff_le_vanishingIdeal, subseteq, vanishingIdea, zeroLocus_empty_iff_eq_top, zeroLocus_inf
-/
theorem isIrreducible_zeroLocus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.IsPrime := by
  rw [Ideal.isPrime_iff]; rw [IsIrreducible]
  apply and_congr
  · rw [Set.nonempty_iff_ne_empty, Ne, zeroLocus_empty_iff_eq_top]
  · trans forall x y : Ideal R, Z(I) subseteq Z(x) union Z(y) -> Z(I) subseteq Z(x) ∨ Z(I) subseteq Z(y)
    · simp_rw [isPreirreducible_iff_isClosed_union_isClosed, isClosed_iff_zeroLocus_ideal]
      constructor
      · rintro h x y
        exact h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      · rintro h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact h x y
    · simp_rw [← zeroLocus_inf, subset_zeroLocus_iff_le_vanishingIdeal,
        vanishingIdeal_zeroLocus_eq_radical, hI.radical]
      constructor
      · simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ←
          Ideal.span_singleton_mul_span_singleton]
        refine fun h x y h' => h _ _ ?_
        rw [← hI.radical_le_iff] at h' ⊢
        simpa only [Ideal.radical_inf, Ideal.radical_mul] using h'
      · simp_rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
        rintro h s t h' ⟨x, hx, hx'⟩ y hy
        exact h (h' ⟨Ideal.mul_mem_right _ _ hx, Ideal.mul_mem_left _ _ hy⟩) hx'

/--
theorem `isIrreducible_zeroLocus_iff` / 定理 `isIrreducible_zeroLocus_iff`

English:
theorem isIrreducible_zeroLocus_iff
  given: (I : Ideal R)
  proof: zeroLocus_radical I ▸ isIrreducible_zeroLocus_iff_of_radical _ I.radical_isRadical

中文:
定理 isIrreducible_zeroLocus_iff
  条件: (I : 理想 R)
  证明: zeroLocus_radical I ▸ isIrreducible_zeroLocus_iff_of_radical _ I.radical_isRadical

Depends on / 依赖: I.radical_isRadical, TotallySeparatedSpace, TotallySeparatedSpace.totallyDisconnectedSpace, isIrreducible_zeroLocus_iff_of_radical, radical_isRadical, totallyDisconnectedSpace, zeroLocus_radical
-/
theorem isIrreducible_zeroLocus_iff (I : Ideal R) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.radical.IsPrime :=
  zeroLocus_radical I ▸ isIrreducible_zeroLocus_iff_of_radical _ I.radical_isRadical

/--
theorem `isIrreducible_iff_vanishingIdeal_isPrime` / 定理 `isIrreducible_iff_vanishingIdeal_isPrime`

English:
theorem isIrreducible_iff_vanishingIdeal_isPrime
  given: {s : Set (PrimeSpectrum R)}
  proof: by
  rw [← isIrreducible_iff_closure]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [isIrreducible_zeroLocus_iff_of_radical _ (isRadical_vanishingIdeal s)]

中文:
定理 isIrreducible_iff_vanishingIdeal_isPrime
  条件: {s : 集合 (素谱 R)}
  证明: by
  rw [← isIrreducible_iff_closure]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [isIrreducible_zeroLocus_iff_of_radical _ (isRadical_vanishingIdeal s)]

Depends on / 依赖: TopologicalSpace, TotallySeparatedSpace, TotallySeparatedSpace.of_discrete, isIrreducible_iff_closure, isIrreducible_zeroLocus_iff_of_radical, isRadical_vanishingIdeal, of_discrete, zeroLocus_vanishingIdeal_eq_closure
-/
theorem isIrreducible_iff_vanishingIdeal_isPrime {s : Set (PrimeSpectrum R)} :
    IsIrreducible s ↔ (vanishingIdeal s).IsPrime := by
  rw [← isIrreducible_iff_closure]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [isIrreducible_zeroLocus_iff_of_radical _ (isRadical_vanishingIdeal s)]

/--
lemma `vanishingIdeal_isIrreducible` / 引理 `vanishingIdeal_isIrreducible`

English:
lemma vanishingIdeal_isIrreducible
  proof: Set.ext fun I => ⟨fun ⟨_, hs, e⟩ => e ▸ isIrreducible_iff_vanishingIdeal_isPrime.mp hs,
    fun h => ⟨zeroLocus I, (isIrreducible_zeroLocus_iff_of_radical _ h.isRadical).mpr h,
      (vanishingIdeal_zeroLocus_eq_radical I).trans h.radical⟩⟩

中文:
引理 vanishingIdeal_isIrreducible
  证明: Set.ext fun I => ⟨fun ⟨_, hs, e⟩ => e ▸ isIrreducible_iff_vanishingIdeal_isPrime.mp hs,
    fun h => ⟨zeroLocus I, (isIrreducible_zeroLocus_iff_of_radical _ h.isRadical).mpr h,
      (vanishingIdeal_zeroLocus_eq_radical I).trans h.radical⟩⟩

Depends on / 依赖: IsIrreducible, IsPrime, P.IsPrime
-/
lemma vanishingIdeal_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsIrreducible s} = {P | P.IsPrime} :=
  Set.ext fun I => ⟨fun ⟨_, hs, e⟩ => e ▸ isIrreducible_iff_vanishingIdeal_isPrime.mp hs,
    fun h => ⟨zeroLocus I, (isIrreducible_zeroLocus_iff_of_radical _ h.isRadical).mpr h,
      (vanishingIdeal_zeroLocus_eq_radical I).trans h.radical⟩⟩

/--
lemma `vanishingIdeal_isClosed_isIrreducible` / 引理 `vanishingIdeal_isClosed_isIrreducible`

English:
lemma vanishingIdeal_isClosed_isIrreducible
  proof: by
  refine (subset_antisymm ?_ ?_).trans vanishingIdeal_isIrreducible
  · exact Set.image_mono fun _ => And.right
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨closure s, ⟨isClosed_closure, hs.closure⟩, vanishingIdeal_closure s⟩

中文:
引理 vanishingIdeal_isClosed_isIrreducible
  证明: by
  refine (subset_antisymm ?_ ?_).trans vanishingIdeal_isIrreducible
  · exact Set.image_mono fun _ => And.right
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨closure s, ⟨isClosed_closure, hs.closure⟩, vanishingIdeal_closure s⟩

Depends on / 依赖: And.right, IsClosed, IsIrreducible, IsPrime, P.IsPrime, Set.image_mono, closure, hs.closure, image_mono, isClosed_closure, subset_antisymm, vanishingIdeal_closure, vanishingIdeal_isIrreducible
-/
lemma vanishingIdeal_isClosed_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsClosed s ∧ IsIrreducible s} = {P | P.IsPrime} := by
  refine (subset_antisymm ?_ ?_).trans vanishingIdeal_isIrreducible
  · exact Set.image_mono fun _ => And.right
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨closure s, ⟨isClosed_closure, hs.closure⟩, vanishingIdeal_closure s⟩

/--
lemma `irreducibleSpace_iff_isPrime_nilradical` / 引理 `irreducibleSpace_iff_isPrime_nilradical`

English:
lemma irreducibleSpace_iff_isPrime_nilradical
  proof: by
  simp [irreducibleSpace_def, isIrreducible_iff_vanishingIdeal_isPrime]

中文:
引理 irreducibleSpace_iff_isPrime_nilradical
  证明: by
  simp [irreducibleSpace_def, isIrreducible_iff_vanishingIdeal_isPrime]

Depends on / 依赖: irreducibleSpace_def, isIrreducible_iff_vanishingIdeal_isPrime
-/
lemma irreducibleSpace_iff_isPrime_nilradical :
    IrreducibleSpace (PrimeSpectrum R) ↔ (nilradical R).IsPrime := by
  simp [irreducibleSpace_def, isIrreducible_iff_vanishingIdeal_isPrime]

/--
Instance `irreducibleSpace` / 实例 `irreducibleSpace`

English:
instance irreducibleSpace
  signature: [IsDomain R]
  body: by
  simpa [irreducibleSpace_iff_isPrime_nilradical] using Ideal.isPrime_bot

中文:
实例 irreducibleSpace
  签名: [是整环 R]
  定义体: by
  simpa [irreducibleSpace_iff_isPrime_nilradical] using Ideal.isPrime_bot

Depends on / 依赖: Ideal.isPrime_bot, irreducibleSpace_iff_isPrime_nilradical, isPrime_bot
-/
instance irreducibleSpace [IsDomain R] : IrreducibleSpace (PrimeSpectrum R) := by
  simpa [irreducibleSpace_iff_isPrime_nilradical] using Ideal.isPrime_bot

/--
Instance `quasiSober` / 实例 `quasiSober`

English:
instance quasiSober
  signature: : QuasiSober (PrimeSpectrum R)
  body: ⟨fun {S} h₁ h₂ =>
    ⟨⟨_, isIrreducible_iff_vanishingIdeal_isPrime.1 h₁⟩, by
      rw [IsGenericPoint]; rw [closure_singleton]; rw [zeroLocus_vanishingIdeal_eq_closure]; rw [h₂.closure_eq]⟩⟩

中文:
实例 quasiSober
  签名: : 拟醇 (素谱 R)
  定义体: ⟨fun {S} h₁ h₂ =>
    ⟨⟨_, isIrreducible_iff_vanishingIdeal_isPrime.1 h₁⟩, by
      rw [IsGenericPoint]; rw [closure_singleton]; rw [zeroLocus_vanishingIdeal_eq_closure]; rw [h₂.closure_eq]⟩⟩

Depends on / 依赖: IsGenericPoint, closure_eq, closure_singleton, isIrreducible_iff_vanishingIdeal_isPrime, zeroLocus_vanishingIdeal_eq_closure
-/
instance quasiSober : QuasiSober (PrimeSpectrum R) :=
  ⟨fun {S} h₁ h₂ =>
    ⟨⟨_, isIrreducible_iff_vanishingIdeal_isPrime.1 h₁⟩, by
      rw [IsGenericPoint]; rw [closure_singleton]; rw [zeroLocus_vanishingIdeal_eq_closure]; rw [h₂.closure_eq]⟩⟩

instance (I : Set R) : QuasiSober (zeroLocus I) :=
  (isClosed_zeroLocus I).isClosedEmbedding_subtypeVal.quasiSober

/--
Instance `compactSpace` / 实例 `compactSpace`

English:
instance compactSpace
  signature: : CompactSpace (PrimeSpectrum R)
  body: by
  refine compactSpace_of_finite_subfamily_closed fun S S_closed S_empty => ?_
  choose I hI using fun i => (isClosed_iff_zeroLocus_ideal (S i)).mp (S_closed i)
  simp_rw [hI, ← zeroLocus_iSup, zeroLocus_empty_iff_eq_top, ← top_le_iff] at S_empty ⊢
  exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _
    Ideal.isCompactElement_top _ S_empty

中文:
实例 compactSpace
  签名: : 紧空间 (素谱 R)
  定义体: by
  refine compactSpace_of_finite_subfamily_closed fun S S_closed S_empty => ?_
  choose I hI using fun i => (isClosed_iff_zeroLocus_ideal (S i)).mp (S_closed i)
  simp_rw [hI, ← zeroLocus_iSup, zeroLocus_empty_iff_eq_top, ← top_le_iff] at S_empty ⊢
  exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _
    Ideal.isCompactElement_top _ S_empty

Depends on / 依赖: CompleteLattice, CompleteLattice.IsCompactElement.exists_finset_of_le_iSup, Ideal.isCompactElement_top, IsCompactElement, S_closed, S_empty, compactSpace_of_finite_subfamily_closed, exists_finset_of_le_iSup, isClosed_iff_zeroLocus_ideal, isCompactElement_top, simp_rw, top_le_iff, zeroLocus_empty_iff_eq_top, zeroLocus_iSup
-/
instance compactSpace : CompactSpace (PrimeSpectrum R) := by
  refine compactSpace_of_finite_subfamily_closed fun S S_closed S_empty => ?_
  choose I hI using fun i => (isClosed_iff_zeroLocus_ideal (S i)).mp (S_closed i)
  simp_rw [hI, ← zeroLocus_iSup, zeroLocus_empty_iff_eq_top, ← top_le_iff] at S_empty ⊢
  exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _
    Ideal.isCompactElement_top _ S_empty

/--
theorem `discreteTopology_iff_finite_and_krullDimLE_zero` / 定理 `discreteTopology_iff_finite_and_krullDimLE_zero`

English:
theorem discreteTopology_iff_finite_and_krullDimLE_zero
  statement: DiscreteTopology (PrimeSpectrum R) ↔
  proof: ⟨fun _ => ⟨finite_of_compact_of_discrete, .mk₀ fun I h => isClosed_singleton_iff_isMaximal ⟨I, h⟩
.mp discreteTopology_iff_forall_isClosed.mp ‹_› _⟩, fun ⟨_, _⟩ =>
    .of_finite_of_isClosed_singleton fun p => (isClosed_singleton_iff_isMaximal p).mpr inferInstance⟩

中文:
定理 discreteTopology_iff_finite_and_krullDimLE_zero
  结论: 离散拓扑 (素谱 R) ↔
  证明: ⟨fun _ => ⟨finite_of_compact_of_discrete, .mk₀ fun I h => isClosed_singleton_iff_isMaximal ⟨I, h⟩
.mp discreteTopology_iff_forall_isClosed.mp ‹_› _⟩, fun ⟨_, _⟩ =>
    .of_finite_of_isClosed_singleton fun p => (isClosed_singleton_iff_isMaximal p).mpr inferInstance⟩

Depends on / 依赖: discreteTopology_iff_forall_isClosed, discreteTopology_iff_forall_isClosed.mp, finite_of_compact_of_discrete, isClosed_singleton_iff_isMaximal, of_finite_of_isClosed_singleton
-/
theorem discreteTopology_iff_finite_and_krullDimLE_zero : DiscreteTopology (PrimeSpectrum R) ↔
    Finite (PrimeSpectrum R) ∧ Ring.KrullDimLE 0 R :=
  ⟨fun _ => ⟨finite_of_compact_of_discrete, .mk₀ fun I h => isClosed_singleton_iff_isMaximal ⟨I, h⟩
.mp discreteTopology_iff_forall_isClosed.mp ‹_› _⟩, fun ⟨_, _⟩ =>
    .of_finite_of_isClosed_singleton fun p => (isClosed_singleton_iff_isMaximal p).mpr inferInstance⟩

/--
theorem `discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical` / 定理 `discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical`

English:
theorem discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical
  proof: {I : Ideal R | I.IsMaximal}
    DiscreteTopology (PrimeSpectrum R) ↔ Finite s ∧ sInf s <= nilradical R := by
  rw [discreteTopology_iff_finite_and_krullDimLE_zero]; rw [Ring.krullDimLE_zero_iff]; rw [(equivSubtype R).finite_iff]; rw [← Set.coe_ofPred]; rw [Set.finite_coe_iff]; rw [Set.finite_coe_iff]
  refine ⟨fun h => ⟨h.1.subset fun _ h => h.isPrime, nilradical_eq_sInf R ▸ sInf_le_sInf h.2⟩,
    fun ⟨fin, le⟩ => ?_⟩
  have hpm (I : Ideal R) (hI : I.IsPrime) : I.IsMaximal := by
    replace le := le.trans (nilradical_le_prime I)
    rw [← fin.coe_toFinset]; rw [← Finset.inf_id_eq_sInf]; rw [hI.inf_le'] at le
    have ⟨M, hM, hMI⟩ := le
    rw [fin.mem_toFinset] at hM
    rwa [← hM.eq_of_le hI.1 hMI]
  exact ⟨fin.subset hpm, hpm⟩

中文:
定理 discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical
  证明: {I : Ideal R | I.IsMaximal}
    DiscreteTopology (PrimeSpectrum R) ↔ Finite s ∧ sInf s <= nilradical R := by
  rw [discreteTopology_iff_finite_and_krullDimLE_zero]; rw [Ring.krullDimLE_zero_iff]; rw [(equivSubtype R).finite_iff]; rw [← Set.coe_ofPred]; rw [Set.finite_coe_iff]; rw [Set.finite_coe_iff]
  refine ⟨fun h => ⟨h.1.subset fun _ h => h.isPrime, nilradical_eq_sInf R ▸ sInf_le_sInf h.2⟩,
    fun ⟨fin, le⟩ => ?_⟩
  have hpm (I : Ideal R) (hI : I.IsPrime) : I.IsMaximal := by
    replace le := le.trans (nilradical_le_prime I)
    rw [← fin.coe_toFinset]; rw [← Finset.inf_id_eq_sInf]; rw [hI.inf_le'] at le
    have ⟨M, hM, hMI⟩ := le
    rw [fin.mem_toFinset] at hM
    rwa [← hM.eq_of_le hI.1 hMI]
  exact ⟨fin.subset hpm, hpm⟩

Depends on / 依赖: I.IsMaximal, IsMaximal
-/
theorem discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical :
    letI s := {I : Ideal R | I.IsMaximal}
    DiscreteTopology (PrimeSpectrum R) ↔ Finite s ∧ sInf s <= nilradical R := by
  rw [discreteTopology_iff_finite_and_krullDimLE_zero]; rw [Ring.krullDimLE_zero_iff]; rw [(equivSubtype R).finite_iff]; rw [← Set.coe_ofPred]; rw [Set.finite_coe_iff]; rw [Set.finite_coe_iff]
  refine ⟨fun h => ⟨h.1.subset fun _ h => h.isPrime, nilradical_eq_sInf R ▸ sInf_le_sInf h.2⟩,
    fun ⟨fin, le⟩ => ?_⟩
  have hpm (I : Ideal R) (hI : I.IsPrime) : I.IsMaximal := by
    replace le := le.trans (nilradical_le_prime I)
    rw [← fin.coe_toFinset]; rw [← Finset.inf_id_eq_sInf]; rw [hI.inf_le'] at le
    have ⟨M, hM, hMI⟩ := le
    rw [fin.mem_toFinset] at hM
    rwa [← hM.eq_of_le hI.1 hMI]
  exact ⟨fin.subset hpm, hpm⟩

/--
theorem `discreteTopology_of_toLocalization_surjective` / 定理 `discreteTopology_of_toLocalization_surjective`

English:
theorem discreteTopology_of_toLocalization_surjective
  proof: discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨finite_of_toPiLocalization_surjective
    surj, .mk₀ fun I prime => isMaximal_of_toPiLocalization_surjective surj ⟨I, prime⟩⟩

中文:
定理 discreteTopology_of_toLocalization_surjective
  证明: discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨finite_of_toPiLocalization_surjective
    surj, .mk₀ fun I prime => isMaximal_of_toPiLocalization_surjective surj ⟨I, prime⟩⟩

Depends on / 依赖: discreteTopology_iff_finite_and_krullDimLE_zero, discreteTopology_iff_finite_and_krullDimLE_zero.mpr, finite_of_toPiLocalization_surjective, isMaximal_of_toPiLocalization_surjective
-/
theorem discreteTopology_of_toLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    DiscreteTopology (PrimeSpectrum R) :=
  discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨finite_of_toPiLocalization_surjective
    surj, .mk₀ fun I prime => isMaximal_of_toPiLocalization_surjective surj ⟨I, prime⟩⟩

section Comap

variable {S' : Type*} [CommSemiring S']

@[fun_prop]
/--
lemma `continuous_comap` / 引理 `continuous_comap`

English:
lemma continuous_comap
  given: (f : R ->+* S)
  statement: Continuous (comap f)
  proof: by
  simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
  rintro _ ⟨s, rfl⟩
  exact ⟨_, preimage_comap_zeroLocus_aux f s⟩

中文:
引理 continuous_comap
  条件: (f : R ->+* S)
  结论: 连续 (comap f)
  证明: by
  simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
  rintro _ ⟨s, rfl⟩
  exact ⟨_, preimage_comap_zeroLocus_aux f s⟩

Depends on / 依赖: continuous_iff_isClosed, isClosed_iff_zeroLocus, preimage_comap_zeroLocus_aux
-/
lemma continuous_comap (f : R ->+* S) : Continuous (comap f) := by
  simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
  rintro _ ⟨s, rfl⟩
  exact ⟨_, preimage_comap_zeroLocus_aux f s⟩

variable (f : R ->+* S)

variable (S)

/--
theorem `localization_comap_injective` / 定理 `localization_comap_injective`

English:
theorem localization_comap_injective
  given: [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  proof: by
  intro p q h
  replace h := _root_.congr_arg (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  dsimp only [comap] at h
  rw [IsLocalization.map_under M S]; rw [IsLocalization.map_under M S] at h
  ext1
  exact h

中文:
定理 localization_comap_injective
  条件: [代数 R S] (M : 子幺半群 R) [是Localization M S]
  证明: by
  intro p q h
  replace h := _root_.congr_arg (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  dsimp only [comap] at h
  rw [IsLocalization.map_under M S]; rw [IsLocalization.map_under M S] at h
  ext1
  exact h

Depends on / 依赖: Ideal.map, IsLocalization, IsLocalization.map_under, PrimeSpectrum, _root_, _root_.congr_arg, algebraMap, asIdeal, congr_arg, map_under, replace, x.asIdeal
-/
theorem localization_comap_injective [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Function.Injective (comap (algebraMap R S)) := by
  intro p q h
  replace h := _root_.congr_arg (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  dsimp only [comap] at h
  rw [IsLocalization.map_under M S]; rw [IsLocalization.map_under M S] at h
  ext1
  exact h

/--
theorem `localization_comap_range` / 定理 `localization_comap_range`

English:
theorem localization_comap_range
  given: [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  proof: by
  refine Set.ext fun x => ⟨?_, fun h => ?_⟩
  · rintro ⟨p, rfl⟩
    exact ((IsLocalization.isPrime_iff_isPrime_disjoint ..).mp p.2).2
  · use ⟨x.asIdeal.map (algebraMap R S), IsLocalization.isPrime_of_isPrime_disjoint M S _ x.2 h⟩
    ext1
    exact IsLocalization.under_map_of_isPrime_disjoint M S x.2 h

中文:
定理 localization_comap_range
  条件: [代数 R S] (M : 子幺半群 R) [是Localization M S]
  证明: by
  refine Set.ext fun x => ⟨?_, fun h => ?_⟩
  · rintro ⟨p, rfl⟩
    exact ((IsLocalization.isPrime_iff_isPrime_disjoint ..).mp p.2).2
  · use ⟨x.asIdeal.map (algebraMap R S), IsLocalization.isPrime_of_isPrime_disjoint M S _ x.2 h⟩
    ext1
    exact IsLocalization.under_map_of_isPrime_disjoint M S x.2 h

Depends on / 依赖: IsLocalization, IsLocalization.isPrime_iff_isPrime_disjoint, IsLocalization.isPrime_of_isPrime_disjoint, IsLocalization.under_map_of_isPrime_disjoint, Set.ext, algebraMap, asIdeal, isPrime_iff_isPrime_disjoint, isPrime_of_isPrime_disjoint, under_map_of_isPrime_disjoint, x.asIdeal.map
-/
theorem localization_comap_range [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Set.range (comap (algebraMap R S)) = { p | Disjoint (M : Set R) p.asIdeal } := by
  refine Set.ext fun x => ⟨?_, fun h => ?_⟩
  · rintro ⟨p, rfl⟩
    exact ((IsLocalization.isPrime_iff_isPrime_disjoint ..).mp p.2).2
  · use ⟨x.asIdeal.map (algebraMap R S), IsLocalization.isPrime_of_isPrime_disjoint M S _ x.2 h⟩
    ext1
    exact IsLocalization.under_map_of_isPrime_disjoint M S x.2 h

/--
theorem `localization_comap_isInducing` / 定理 `localization_comap_isInducing`

English:
theorem localization_comap_isInducing
  given: [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  proof: by
  refine ⟨TopologicalSpace.ext_isClosed fun Z => ?_⟩
  simp_rw [isClosed_induced_iff, isClosed_iff_zeroLocus, @eq_comm _ _ (zeroLocus _),
    exists_exists_eq_and, preimage_comap_zeroLocus]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(Ideal.span s).comap (algebraMap R S), ?_⟩
    rw [← zeroLocus_span]; rw [← zeroLocus_span s]; rw [← Ideal.map]; rw [IsLocalization.map_under M S]
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩

中文:
定理 localization_comap_isInducing
  条件: [代数 R S] (M : 子幺半群 R) [是Localization M S]
  证明: by
  refine ⟨TopologicalSpace.ext_isClosed fun Z => ?_⟩
  simp_rw [isClosed_induced_iff, isClosed_iff_zeroLocus, @eq_comm _ _ (zeroLocus _),
    exists_exists_eq_and, preimage_comap_zeroLocus]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(Ideal.span s).comap (algebraMap R S), ?_⟩
    rw [← zeroLocus_span]; rw [← zeroLocus_span s]; rw [← Ideal.map]; rw [IsLocalization.map_under M S]
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩

Depends on / 依赖: Ideal.map, Ideal.span, IsLocalization, IsLocalization.map_under, TopologicalSpace, TopologicalSpace.ext_isClosed, algebraMap, eq_comm, exists_exists_eq_and, ext_isClosed, isClosed_iff_zeroLocus, isClosed_induced_iff, map_under, preimage_comap_zeroLocus, simp_rw, zeroLocus, zeroLocus_span
-/
theorem localization_comap_isInducing [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    IsInducing (comap (algebraMap R S)) := by
  refine ⟨TopologicalSpace.ext_isClosed fun Z => ?_⟩
  simp_rw [isClosed_induced_iff, isClosed_iff_zeroLocus, @eq_comm _ _ (zeroLocus _),
    exists_exists_eq_and, preimage_comap_zeroLocus]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(Ideal.span s).comap (algebraMap R S), ?_⟩
    rw [← zeroLocus_span]; rw [← zeroLocus_span s]; rw [← Ideal.map]; rw [IsLocalization.map_under M S]
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩

/--
theorem `localization_comap_isEmbedding` / 定理 `localization_comap_isEmbedding`

English:
theorem localization_comap_isEmbedding
  given: [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  proof: ⟨localization_comap_isInducing S M, localization_comap_injective S M⟩

中文:
定理 localization_comap_isEmbedding
  条件: [代数 R S] (M : 子幺半群 R) [是Localization M S]
  证明: ⟨localization_comap_isInducing S M, localization_comap_injective S M⟩

Depends on / 依赖: localization_comap_injective, localization_comap_isInducing
-/
theorem localization_comap_isEmbedding [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    IsEmbedding (comap (algebraMap R S)) :=
  ⟨localization_comap_isInducing S M, localization_comap_injective S M⟩

open Function RingHom

/--
theorem `comap_isInducing_of_surjective` / 定理 `comap_isInducing_of_surjective`

English:
theorem comap_isInducing_of_surjective
  given: (hf : Surjective f)
  statement: IsInducing (comap f) where
  proof: by
    simp only [TopologicalSpace.ext_iff, ← isClosed_compl_iff, isClosed_iff_zeroLocus,
      isClosed_induced_iff]
    refine fun s =>
      ⟨fun ⟨F, hF⟩ =>
        ⟨zeroLocus (f ⁻¹' F), ⟨f ⁻¹' F, rfl⟩, by
          rw [preimage_comap_zeroLocus]; rw [Function.Surjective.image_preimage hf]; rw [hF]⟩,
        ?_⟩
    rintro ⟨-, ⟨F, rfl⟩, hF⟩
    exact ⟨f '' F, hF.symm.trans (preimage_comap_zeroLocus f F)⟩

中文:
定理 comap_isInducing_of_surjective
  条件: (hf : 满射 f)
  结论: 是Inducing (comap f) where
  证明: by
    simp only [TopologicalSpace.ext_iff, ← isClosed_compl_iff, isClosed_iff_zeroLocus,
      isClosed_induced_iff]
    refine fun s =>
      ⟨fun ⟨F, hF⟩ =>
        ⟨zeroLocus (f ⁻¹' F), ⟨f ⁻¹' F, rfl⟩, by
          rw [preimage_comap_zeroLocus]; rw [Function.Surjective.image_preimage hf]; rw [hF]⟩,
        ?_⟩
    rintro ⟨-, ⟨F, rfl⟩, hF⟩
    exact ⟨f '' F, hF.symm.trans (preimage_comap_zeroLocus f F)⟩

Depends on / 依赖: Function, Function.Surjective.image_preimage, Surjective, TopologicalSpace, TopologicalSpace.ext_iff, ext_iff, hF.symm.trans, image_preimage, isClosed_compl_iff, isClosed_iff_zeroLocus, isClosed_induced_iff, preimage_comap_zeroLocus, zeroLocus
-/
theorem comap_isInducing_of_surjective (hf : Surjective f) : IsInducing (comap f) where
  eq_induced := by
    simp only [TopologicalSpace.ext_iff, ← isClosed_compl_iff, isClosed_iff_zeroLocus,
      isClosed_induced_iff]
    refine fun s =>
      ⟨fun ⟨F, hF⟩ =>
        ⟨zeroLocus (f ⁻¹' F), ⟨f ⁻¹' F, rfl⟩, by
          rw [preimage_comap_zeroLocus]; rw [Function.Surjective.image_preimage hf]; rw [hF]⟩,
        ?_⟩
    rintro ⟨-, ⟨F, rfl⟩, hF⟩
    exact ⟨f '' F, hF.symm.trans (preimage_comap_zeroLocus f F)⟩

/--
theorem `isEmbedding_comap_of_surjective` / 定理 `isEmbedding_comap_of_surjective`

English:
theorem isEmbedding_comap_of_surjective
  given: (hf : Surjective f)
  statement: IsEmbedding (comap f)
  proof: (isEmbedding_iff _).2 ⟨comap_isInducing_of_surjective _ _ hf, comap_injective_of_surjective f hf⟩

中文:
定理 isEmbedding_comap_of_surjective
  条件: (hf : 满射 f)
  结论: 是嵌入 (comap f)
  证明: (isEmbedding_iff _).2 ⟨comap_isInducing_of_surjective _ _ hf, comap_injective_of_surjective f hf⟩

Depends on / 依赖: comap_injective_of_surjective, comap_isInducing_of_surjective, isEmbedding_iff
-/
theorem isEmbedding_comap_of_surjective (hf : Surjective f) : IsEmbedding (comap f) :=
  (isEmbedding_iff _).2 ⟨comap_isInducing_of_surjective _ _ hf, comap_injective_of_surjective f hf⟩

end Comap

/--
Definition of `homeomorphOfRingEquiv` / `homeomorphOfRingEquiv` 的定义

English:
definition homeomorphOfRingEquiv
  signature: (e : R ≃+* S)
  body: comap (e.symm : S ->+* R)
  invFun := comap (e : R ->+* S)
  left_inv _ := (comap_comp_apply ..).symm.trans (by simp)
  right_inv _ := (comap_comp_apply ..).symm.trans (by simp)

中文:
定义 homeomorphOfRingEquiv
  签名: (e : R ≃+* S)
  定义体: comap (e.symm : S ->+* R)
  invFun := comap (e : R ->+* S)
  left_inv _ := (comap_comp_apply ..).symm.trans (by simp)
  right_inv _ := (comap_comp_apply ..).symm.trans (by simp)

Depends on / 依赖: e.symm
-/
def homeomorphOfRingEquiv (e : R ≃+* S) : PrimeSpectrum R ≃ₜ PrimeSpectrum S where
  toFun := comap (e.symm : S ->+* R)
  invFun := comap (e : R ->+* S)
  left_inv _ := (comap_comp_apply ..).symm.trans (by simp)
  right_inv _ := (comap_comp_apply ..).symm.trans (by simp)

/--
lemma `isHomeomorph_comap_of_bijective` / 引理 `isHomeomorph_comap_of_bijective`

English:
lemma isHomeomorph_comap_of_bijective
  given: {f : R ->+* S} (hf : Function.Bijective f)
  proof: (homeomorphOfRingEquiv (.ofBijective f hf)).symm.isHomeomorph

中文:
引理 isHomeomorph_comap_of_bijective
  条件: {f : R ->+* S} (hf : 函数.双射 f)
  证明: (homeomorphOfRingEquiv (.ofBijective f hf)).symm.isHomeomorph

Depends on / 依赖: homeomorphOfRingEquiv, isHomeomorph, ofBijective, symm.isHomeomorph
-/
lemma isHomeomorph_comap_of_bijective {f : R ->+* S} (hf : Function.Bijective f) :
    IsHomeomorph (comap f) := (homeomorphOfRingEquiv (.ofBijective f hf)).symm.isHomeomorph

end CommSemiring

section SpecOfSurjective

/-! The comap of a surjective ring homomorphism is a closed embedding between the prime spectra. -/


open Function RingHom

variable [CommRing R] [CommRing S]
variable (f : R ->+* S)
variable {R}

/--
theorem `comap_singleton_isClosed_of_surjective` / 定理 `comap_singleton_isClosed_of_surjective`

English:
theorem comap_singleton_isClosed_of_surjective
  statement: (f : R ->+* S) (hf : Function.Surjective f)
  proof: haveI : x.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal x).1 hx
  (isClosed_singleton_iff_isMaximal _).2 (Ideal.comap_isMaximal_of_surjective f hf)

中文:
定理 comap_singleton_isClosed_of_surjective
  结论: (f : R ->+* S) (hf : 函数.满射 f)
  证明: haveI : x.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal x).1 hx
  (isClosed_singleton_iff_isMaximal _).2 (Ideal.comap_isMaximal_of_surjective f hf)

Depends on / 依赖: Ideal.comap_isMaximal_of_surjective, IsMaximal, asIdeal, comap_isMaximal_of_surjective, isClosed_singleton_iff_isMaximal, x.asIdeal.IsMaximal
-/
theorem comap_singleton_isClosed_of_surjective (f : R ->+* S) (hf : Function.Surjective f)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  haveI : x.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal x).1 hx
  (isClosed_singleton_iff_isMaximal _).2 (Ideal.comap_isMaximal_of_surjective f hf)

/--
lemma `comap_quotientMk_bijective_of_le_nilradical` / 引理 `comap_quotientMk_bijective_of_le_nilradical`

English:
lemma comap_quotientMk_bijective_of_le_nilradical
  given: {I : Ideal R} (hle : I <= nilradical R)
  proof: by
  refine ⟨comap_injective_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  simpa [← Set.range_eq_univ, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    zeroLocus_eq_univ_iff]

中文:
引理 comap_quotientMk_bijective_of_le_nilradical
  条件: {I : 理想 R} (hle : I <= nilradical R)
  证明: by
  refine ⟨comap_injective_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  simpa [← Set.range_eq_univ, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    zeroLocus_eq_univ_iff]

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, Set.range_eq_univ, comap_injective_of_surjective, mk_surjective, range_comap_of_surjective, range_eq_univ, zeroLocus_eq_univ_iff
-/
lemma comap_quotientMk_bijective_of_le_nilradical {I : Ideal R} (hle : I <= nilradical R) :
    Function.Bijective (comap <| Ideal.Quotient.mk I) := by
  refine ⟨comap_injective_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  simpa [← Set.range_eq_univ, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    zeroLocus_eq_univ_iff]

/--
theorem `isClosed_range_comap_of_surjective` / 定理 `isClosed_range_comap_of_surjective`

English:
theorem isClosed_range_comap_of_surjective
  given: (hf : Surjective f)
  proof: by
  rw [range_comap_of_surjective _ f hf]
  exact isClosed_zeroLocus _

中文:
定理 isClosed_range_comap_of_surjective
  条件: (hf : 满射 f)
  证明: by
  rw [range_comap_of_surjective _ f hf]
  exact isClosed_zeroLocus _

Depends on / 依赖: isClosed_zeroLocus, range_comap_of_surjective
-/
theorem isClosed_range_comap_of_surjective (hf : Surjective f) :
    IsClosed (Set.range (comap f)) := by
  rw [range_comap_of_surjective _ f hf]
  exact isClosed_zeroLocus _

/--
lemma `isClosedEmbedding_comap_of_surjective` / 引理 `isClosedEmbedding_comap_of_surjective`

English:
lemma isClosedEmbedding_comap_of_surjective
  given: (hf : Surjective f)
  statement: IsClosedEmbedding (comap f) where
  proof: comap_isInducing_of_surjective S f hf
  injective := comap_injective_of_surjective f hf
  isClosed_range := isClosed_range_comap_of_surjective S f hf

中文:
引理 isClosedEmbedding_comap_of_surjective
  条件: (hf : 满射 f)
  结论: 是闭嵌入 (comap f) where
  证明: comap_isInducing_of_surjective S f hf
  injective := comap_injective_of_surjective f hf
  isClosed_range := isClosed_range_comap_of_surjective S f hf

Depends on / 依赖: comap_isInducing_of_surjective
-/
lemma isClosedEmbedding_comap_of_surjective (hf : Surjective f) : IsClosedEmbedding (comap f) where
  toIsInducing := comap_isInducing_of_surjective S f hf
  injective := comap_injective_of_surjective f hf
  isClosed_range := isClosed_range_comap_of_surjective S f hf

end SpecOfSurjective

section SpecProd

variable {R S} [CommSemiring R] [CommSemiring S]

/--
lemma `primeSpectrumProd_symm_inl` / 引理 `primeSpectrumProd_symm_inl`

English:
lemma primeSpectrumProd_symm_inl
  given: (x)
  proof: by
  ext; simp [Ideal.prod]

中文:
引理 primeSpectrumProd_symm_inl
  条件: (x)
  证明: by
  ext; simp [Ideal.prod]

Depends on / 依赖: Ideal.prod
-/
lemma primeSpectrumProd_symm_inl (x) :
    (primeSpectrumProd R S).symm (.inl x) = comap (RingHom.fst R S) x := by
  ext; simp [Ideal.prod]

/--
lemma `primeSpectrumProd_symm_inr` / 引理 `primeSpectrumProd_symm_inr`

English:
lemma primeSpectrumProd_symm_inr
  given: (x)
  proof: by
  ext; simp [Ideal.prod]

中文:
引理 primeSpectrumProd_symm_inr
  条件: (x)
  证明: by
  ext; simp [Ideal.prod]

Depends on / 依赖: Ideal.prod
-/
lemma primeSpectrumProd_symm_inr (x) :
    (primeSpectrumProd R S).symm (.inr x) = comap (RingHom.snd R S) x := by
  ext; simp [Ideal.prod]

/--
lemma `range_comap_fst` / 引理 `range_comap_fst`

English:
lemma range_comap_fst
  proof: by
  refine Set.ext fun p => ⟨?_, fun h => ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
· exact ⟨⟨p, hp⟩, PrimeSpectrum.ext by simpa [Ideal.prod] using eq.symm⟩
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (0, 1) in RingHom.ker (RingHom.fst R S) by simp)

中文:
引理 range_comap_fst
  证明: by
  refine Set.ext fun p => ⟨?_, fun h => ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
· exact ⟨⟨p, hp⟩, PrimeSpectrum.ext by simpa [Ideal.prod] using eq.symm⟩
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (0, 1) in RingHom.ker (RingHom.fst R S) by simp)

Depends on / 依赖: Ideal.comap_mono, Ideal.eq_top_iff_one, Ideal.prod, PrimeSpectrum, PrimeSpectrum.ext, RingHom, RingHom.fst, RingHom.ker, Set.ext, bot_le, comap_mono, continuous_id, continuous_prodMk, eq.symm, eq_top_iff_one, hp.ne_top, ideal_prod_prime, ideal_prod_prime.mp, ne_top
-/
lemma range_comap_fst :
    Set.range (comap (RingHom.fst R S)) = zeroLocus (RingHom.ker (RingHom.fst R S)) := by
  refine Set.ext fun p => ⟨?_, fun h => ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
· exact ⟨⟨p, hp⟩, PrimeSpectrum.ext by simpa [Ideal.prod] using eq.symm⟩
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (0, 1) in RingHom.ker (RingHom.fst R S) by simp)

/--
lemma `range_comap_snd` / 引理 `range_comap_snd`

English:
lemma range_comap_snd
  proof: by
  refine Set.ext fun p => ⟨?_, fun h => ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (1, 0) in RingHom.ker (RingHom.snd R S) by simp)
· exact ⟨⟨p, hp⟩, PrimeSpectrum.ext by simpa [Ideal.prod] using eq.symm⟩

中文:
引理 range_comap_snd
  证明: by
  refine Set.ext fun p => ⟨?_, fun h => ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (1, 0) in RingHom.ker (RingHom.snd R S) by simp)
· exact ⟨⟨p, hp⟩, PrimeSpectrum.ext by simpa [Ideal.prod] using eq.symm⟩

Depends on / 依赖: Ideal.comap_mono, Ideal.eq_top_iff_one, Ideal.prod, PrimeSpectrum, PrimeSpectrum.ext, RingHom, RingHom.ker, RingHom.snd, Set.ext, bot_le, comap_mono, eq.symm, eq_top_iff_one, hp.ne_top, ideal_prod_prime, ideal_prod_prime.mp, ne_top
-/
lemma range_comap_snd :
    Set.range (comap (RingHom.snd R S)) = zeroLocus (RingHom.ker (RingHom.snd R S)) := by
  refine Set.ext fun p => ⟨?_, fun h => ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (1, 0) in RingHom.ker (RingHom.snd R S) by simp)
· exact ⟨⟨p, hp⟩, PrimeSpectrum.ext by simpa [Ideal.prod] using eq.symm⟩

/--
lemma `isClosedEmbedding_comap_fst` / 引理 `isClosedEmbedding_comap_fst`

English:
lemma isClosedEmbedding_comap_fst
  statement: IsClosedEmbedding (comap (RingHom.fst R S))
  proof: (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.fst_surjective, by
    simp_rw [range_comap_fst, isClosed_zeroLocus]⟩

中文:
引理 isClosedEmbedding_comap_fst
  结论: 是闭嵌入 (comap (环态射.fst R S))
  证明: (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.fst_surjective, by
    simp_rw [range_comap_fst, isClosed_zeroLocus]⟩

Depends on / 依赖: Prod.fst_surjective, fst_surjective, isClosedEmbedding_iff, isClosed_zeroLocus, isEmbedding_comap_of_surjective, range_comap_fst, simp_rw
-/
lemma isClosedEmbedding_comap_fst : IsClosedEmbedding (comap (RingHom.fst R S)) :=
  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.fst_surjective, by
    simp_rw [range_comap_fst, isClosed_zeroLocus]⟩

/--
lemma `isClosedEmbedding_comap_snd` / 引理 `isClosedEmbedding_comap_snd`

English:
lemma isClosedEmbedding_comap_snd
  statement: IsClosedEmbedding (comap (RingHom.snd R S))
  proof: (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.snd_surjective, by
    simp_rw [range_comap_snd, isClosed_zeroLocus]⟩

中文:
引理 isClosedEmbedding_comap_snd
  结论: 是闭嵌入 (comap (环态射.snd R S))
  证明: (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.snd_surjective, by
    simp_rw [range_comap_snd, isClosed_zeroLocus]⟩

Depends on / 依赖: Prod.snd_surjective, isClosedEmbedding_iff, isClosed_zeroLocus, isEmbedding_comap_of_surjective, range_comap_snd, simp_rw, snd_surjective
-/
lemma isClosedEmbedding_comap_snd : IsClosedEmbedding (comap (RingHom.snd R S)) :=
  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.snd_surjective, by
    simp_rw [range_comap_snd, isClosed_zeroLocus]⟩

/-- The prime spectrum of `R × S` is homeomorphic
to the disjoint union of `PrimeSpectrum R` and `PrimeSpectrum S`. -/
noncomputable
/--
Definition of `primeSpectrumProdHomeo` / `primeSpectrumProdHomeo` 的定义

English:
definition primeSpectrumProdHomeo
  signature: :
  body: by
  refine ((primeSpectrumProd R S).symm.toHomeomorphOfIsInducing ?_).symm
  refine (IsClosedEmbedding.of_continuous_injective_isClosedMap ?_
    (Equiv.injective _) ?_).isInducing
  · rw [continuous_sum_dom]
    simp only [Function.comp_def, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨continuous_comap _, continuous_comap _⟩
  · simp_rw [isClosedMap_sum, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨isClosedEmbedding_comap_fst.isClosedMap, isClosedEmbedding_comap_snd.isClosedMap⟩

中文:
定义 primeSpectrumProdHomeo
  签名: :
  定义体: by
  refine ((primeSpectrumProd R S).symm.toHomeomorphOfIsInducing ?_).symm
  refine (IsClosedEmbedding.of_continuous_injective_isClosedMap ?_
    (Equiv.injective _) ?_).isInducing
  · rw [continuous_sum_dom]
    simp only [Function.comp_def, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨continuous_comap _, continuous_comap _⟩
  · simp_rw [isClosedMap_sum, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨isClosedEmbedding_comap_fst.isClosedMap, isClosedEmbedding_comap_snd.isClosedMap⟩

Depends on / 依赖: Equiv.injective, Function, Function.comp_def, IsClosedEmbedding, IsClosedEmbedding.of_continuous_injective_isClosedMap, comp_def, continuous_comap, continuous_sum_dom, injective, isClose, isClosedEmbedding_comap_fst, isClosedEmbedding_comap_fst.isClosedMap, isClosedEmbedding_comap_snd, isClosedEmbedding_comap_snd.isClose, isClosedMap, isClosedMap_sum, isInducing, of_continuous_injective_isClosedMap, primeSpectrumProd, primeSpectrumProd_symm_inl
-/
def primeSpectrumProdHomeo :
    PrimeSpectrum (R × S) ≃ₜ PrimeSpectrum R oplus PrimeSpectrum S := by
  refine ((primeSpectrumProd R S).symm.toHomeomorphOfIsInducing ?_).symm
  refine (IsClosedEmbedding.of_continuous_injective_isClosedMap ?_
    (Equiv.injective _) ?_).isInducing
  · rw [continuous_sum_dom]
    simp only [Function.comp_def, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨continuous_comap _, continuous_comap _⟩
  · simp_rw [isClosedMap_sum, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨isClosedEmbedding_comap_fst.isClosedMap, isClosedEmbedding_comap_snd.isClosedMap⟩

end SpecProd

section CommSemiring

variable [CommSemiring R] [CommSemiring S]
variable {R S}

section BasicOpen

/--
Definition of `basicOpen` / `basicOpen` 的定义

English:
definition basicOpen
  signature: (r : R)
  body: { x | r ∉ x.asIdeal }
is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans Classical.not_not.symm⟩

@[simp]

中文:
定义 basicOpen
  签名: (r : R)
  定义体: { x | r ∉ x.asIdeal }
is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans Classical.not_not.symm⟩

@[simp]

Depends on / 依赖: asIdeal, x.asIdeal
-/
def basicOpen (r : R) : TopologicalSpace.Opens (PrimeSpectrum R) where
  carrier := { x | r ∉ x.asIdeal }
is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans Classical.not_not.symm⟩

@[simp]
/--
theorem `mem_basicOpen` / 定理 `mem_basicOpen`

English:
theorem mem_basicOpen
  given: (f : R) (x : PrimeSpectrum R)
  statement: x in basicOpen f ↔ f ∉ x.asIdeal
  proof: Iff.rfl

中文:
定理 mem_basicOpen
  条件: (f : R) (x : 素谱 R)
  结论: x in basicOpen f ↔ f ∉ x.asIdeal
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_basicOpen (f : R) (x : PrimeSpectrum R) : x in basicOpen f ↔ f ∉ x.asIdeal :=
  Iff.rfl

/--
theorem `isOpen_basicOpen` / 定理 `isOpen_basicOpen`

English:
theorem isOpen_basicOpen
  given: {a : R}
  statement: IsOpen (basicOpen a : Set (PrimeSpectrum R))
  proof: (basicOpen a).isOpen

@[simp]

中文:
定理 isOpen_basicOpen
  条件: {a : R}
  结论: 是开集 (basicOpen a : 集合 (素谱 R))
  证明: (basicOpen a).isOpen

@[simp]

Depends on / 依赖: basicOpen, isOpen
-/
theorem isOpen_basicOpen {a : R} : IsOpen (basicOpen a : Set (PrimeSpectrum R)) :=
  (basicOpen a).isOpen

@[simp]
/--
theorem `basicOpen_eq_zeroLocus_compl` / 定理 `basicOpen_eq_zeroLocus_compl`

English:
theorem basicOpen_eq_zeroLocus_compl
  given: (r : R)
  proof: Set.ext fun x => by simp only [SetLike.mem_coe, mem_basicOpen, Set.mem_compl_iff, mem_zeroLocus,
    Set.singleton_subset_iff]

@[simp]

中文:
定理 basicOpen_eq_zeroLocus_compl
  条件: (r : R)
  证明: Set.ext fun x => by simp only [SetLike.mem_coe, mem_basicOpen, Set.mem_compl_iff, mem_zeroLocus,
    Set.singleton_subset_iff]

@[simp]

Depends on / 依赖: Set.ext, Set.mem_compl_iff, Set.singleton_subset_iff, SetLike, SetLike.mem_coe, continuous_id, continuous_prodMk, mem_basicOpen, mem_coe, mem_compl_iff, mem_zeroLocus, singleton_subset_iff
-/
theorem basicOpen_eq_zeroLocus_compl (r : R) :
    (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ :=
  Set.ext fun x => by simp only [SetLike.mem_coe, mem_basicOpen, Set.mem_compl_iff, mem_zeroLocus,
    Set.singleton_subset_iff]

@[simp]
/--
theorem `basicOpen_one` / 定理 `basicOpen_one`

English:
theorem basicOpen_one
  statement: basicOpen (1 : R) = ⊤
  proof: TopologicalSpace.Opens.ext by simp

@[simp]

中文:
定理 basicOpen_one
  结论: basicOpen (1 : R) = ⊤
  证明: TopologicalSpace.Opens.ext by simp

@[simp]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.ext
-/
theorem basicOpen_one : basicOpen (1 : R) = ⊤ :=
TopologicalSpace.Opens.ext by simp

@[simp]
/--
theorem `basicOpen_zero` / 定理 `basicOpen_zero`

English:
theorem basicOpen_zero
  statement: basicOpen (0 : R) = ⊥
  proof: TopologicalSpace.Opens.ext by simp

中文:
定理 basicOpen_zero
  结论: basicOpen (0 : R) = ⊥
  证明: TopologicalSpace.Opens.ext by simp

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.ext
-/
theorem basicOpen_zero : basicOpen (0 : R) = ⊥ :=
TopologicalSpace.Opens.ext by simp

/--
theorem `basicOpen_le_basicOpen_iff` / 定理 `basicOpen_le_basicOpen_iff`

English:
theorem basicOpen_le_basicOpen_iff
  given: (f g : R)
  proof: by
  rw [← SetLike.coe_subset_coe]; rw [basicOpen_eq_zeroLocus_compl]; rw [basicOpen_eq_zeroLocus_compl]; rw [Set.compl_subset_compl]; rw [zeroLocus_subset_zeroLocus_singleton_iff]

中文:
定理 basicOpen_le_basicOpen_iff
  条件: (f g : R)
  证明: by
  rw [← SetLike.coe_subset_coe]; rw [basicOpen_eq_zeroLocus_compl]; rw [basicOpen_eq_zeroLocus_compl]; rw [Set.compl_subset_compl]; rw [zeroLocus_subset_zeroLocus_singleton_iff]

Depends on / 依赖: Set.compl_subset_compl, SetLike, SetLike.coe_subset_coe, basicOpen_eq_zeroLocus_compl, coe_subset_coe, compl_subset_compl, zeroLocus_subset_zeroLocus_singleton_iff
-/
theorem basicOpen_le_basicOpen_iff (f g : R) :
    basicOpen f <= basicOpen g ↔ f in (Ideal.span ({g} : Set R)).radical := by
  rw [← SetLike.coe_subset_coe]; rw [basicOpen_eq_zeroLocus_compl]; rw [basicOpen_eq_zeroLocus_compl]; rw [Set.compl_subset_compl]; rw [zeroLocus_subset_zeroLocus_singleton_iff]

/--
theorem `basicOpen_le_basicOpen_iff_algebraMap_isUnit` / 定理 `basicOpen_le_basicOpen_iff_algebraMap_isUnit`

English:
theorem basicOpen_le_basicOpen_iff_algebraMap_isUnit
  statement: {f g : R} [Algebra R S]
  proof: by
  simp_rw [basicOpen_le_basicOpen_iff, Ideal.mem_radical_iff, Ideal.mem_span_singleton,
    IsLocalization.Away.algebraMap_isUnit_iff f]

中文:
定理 basicOpen_le_basicOpen_iff_algebraMap_isUnit
  结论: {f g : R} [代数 R S]
  证明: by
  simp_rw [basicOpen_le_basicOpen_iff, Ideal.mem_radical_iff, Ideal.mem_span_singleton,
    IsLocalization.Away.algebraMap_isUnit_iff f]

Depends on / 依赖: Ideal.mem_radical_iff, Ideal.mem_span_singleton, IsLocalization, IsLocalization.Away.algebraMap_isUnit_iff, algebraMap_isUnit_iff, basicOpen_le_basicOpen_iff, mem_radical_iff, mem_span_singleton, simp_rw
-/
theorem basicOpen_le_basicOpen_iff_algebraMap_isUnit {f g : R} [Algebra R S]
    [IsLocalization.Away f S] : basicOpen f <= basicOpen g ↔ IsUnit (algebraMap R S g) := by
  simp_rw [basicOpen_le_basicOpen_iff, Ideal.mem_radical_iff, Ideal.mem_span_singleton,
    IsLocalization.Away.algebraMap_isUnit_iff f]

/--
theorem `basicOpen_mul` / 定理 `basicOpen_mul`

English:
theorem basicOpen_mul
  given: (f g : R)
  statement: basicOpen (f * g) = basicOpen f ⊓ basicOpen g
  proof: TopologicalSpace.Opens.ext by simp [zeroLocus_singleton_mul]

中文:
定理 basicOpen_mul
  条件: (f g : R)
  结论: basicOpen (f * g) = basicOpen f ⊓ basicOpen g
  证明: TopologicalSpace.Opens.ext by simp [zeroLocus_singleton_mul]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.ext, zeroLocus_singleton_mul
-/
theorem basicOpen_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g :=
TopologicalSpace.Opens.ext by simp [zeroLocus_singleton_mul]

/--
theorem `basicOpen_mul_le_left` / 定理 `basicOpen_mul_le_left`

English:
theorem basicOpen_mul_le_left
  given: (f g : R)
  statement: basicOpen (f * g) <= basicOpen f
  proof: by
  rw [basicOpen_mul f g]
  exact inf_le_left

中文:
定理 basicOpen_mul_le_left
  条件: (f g : R)
  结论: basicOpen (f * g) <= basicOpen f
  证明: by
  rw [basicOpen_mul f g]
  exact inf_le_left

Depends on / 依赖: basicOpen_mul, inf_le_left
-/
theorem basicOpen_mul_le_left (f g : R) : basicOpen (f * g) <= basicOpen f := by
  rw [basicOpen_mul f g]
  exact inf_le_left

/--
theorem `basicOpen_mul_le_right` / 定理 `basicOpen_mul_le_right`

English:
theorem basicOpen_mul_le_right
  given: (f g : R)
  statement: basicOpen (f * g) <= basicOpen g
  proof: by
  rw [basicOpen_mul f g]
  exact inf_le_right

@[simp]

中文:
定理 basicOpen_mul_le_right
  条件: (f g : R)
  结论: basicOpen (f * g) <= basicOpen g
  证明: by
  rw [basicOpen_mul f g]
  exact inf_le_right

@[simp]

Depends on / 依赖: basicOpen_mul, inf_le_right
-/
theorem basicOpen_mul_le_right (f g : R) : basicOpen (f * g) <= basicOpen g := by
  rw [basicOpen_mul f g]
  exact inf_le_right

@[simp]
/--
theorem `basicOpen_pow` / 定理 `basicOpen_pow`

English:
theorem basicOpen_pow
  given: (f : R) (n : Nat) (hn : 0 < n)
  statement: basicOpen (f ^ n) = basicOpen f
  proof: TopologicalSpace.Opens.ext by simpa using zeroLocus_singleton_pow f n hn

中文:
定理 basicOpen_pow
  条件: (f : R) (n : 自然数) (hn : 0 < n)
  结论: basicOpen (f ^ n) = basicOpen f
  证明: TopologicalSpace.Opens.ext by simpa using zeroLocus_singleton_pow f n hn

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.ext, zeroLocus_singleton_pow
-/
theorem basicOpen_pow (f : R) (n : Nat) (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f :=
TopologicalSpace.Opens.ext by simpa using zeroLocus_singleton_pow f n hn

/--
lemma `le_basicOpen_pow` / 引理 `le_basicOpen_pow`

English:
lemma le_basicOpen_pow
  given: (r : R) (n : Nat)
  statement: basicOpen r <= basicOpen (r ^ n)
  proof: by
  cases n <;> simp

中文:
引理 le_basicOpen_pow
  条件: (r : R) (n : 自然数)
  结论: basicOpen r <= basicOpen (r ^ n)
  证明: by
  cases n <;> simp
-/
lemma le_basicOpen_pow (r : R) (n : Nat) : basicOpen r <= basicOpen (r ^ n) := by
  cases n <;> simp

/--
theorem `isTopologicalBasis_basic_opens` / 定理 `isTopologicalBasis_basic_opens`

English:
theorem isTopologicalBasis_basic_opens
  proof: by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U]; rw [Set.mem_compl_iff]; rw [← hs]; rw [mem_zeroLocus]; rw [Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl]; rw [← hs]; rw [basicOpen_eq_zeroLocus_compl]; rw [compl_compl]
    exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hfs)

中文:
定理 isTopologicalBasis_basic_opens
  证明: by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U]; rw [Set.mem_compl_iff]; rw [← hs]; rw [mem_zeroLocus]; rw [Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl]; rw [← hs]; rw [basicOpen_eq_zeroLocus_compl]; rw [compl_compl]
    exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hfs)

Depends on / 依赖: Set.compl_subset_compl, Set.mem_compl_iff, Set.not_subset, Set.singleton_subset_iff.mpr, TopologicalSpace, TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds, basicOpen, basicOpen_eq_zeroLocus_compl, compl_compl, compl_subset_compl, isOpen_basicOpen, isTopologicalBasis_of_isOpen_of_nhds, mem_compl_iff, mem_zeroLocus, not_subset, singleton_subset_iff, zeroLocus_anti_mono
-/
theorem isTopologicalBasis_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun r : R => (basicOpen r : Set (PrimeSpectrum R))) := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U]; rw [Set.mem_compl_iff]; rw [← hs]; rw [mem_zeroLocus]; rw [Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl]; rw [← hs]; rw [basicOpen_eq_zeroLocus_compl]; rw [compl_compl]
    exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hfs)

/--
theorem `eq_biUnion_of_isOpen` / 定理 `eq_biUnion_of_isOpen`

English:
theorem eq_biUnion_of_isOpen
  given: {s : Set (PrimeSpectrum R)} (hs : IsOpen s)
  proof: (isTopologicalBasis_basic_opens.open_eq_sUnion' hs).trans by aesop

中文:
定理 eq_biUnion_of_isOpen
  条件: {s : 集合 (素谱 R)} (hs : 是开集 s)
  证明: (isTopologicalBasis_basic_opens.open_eq_sUnion' hs).trans by aesop

Depends on / 依赖: isTopologicalBasis_basic_opens, isTopologicalBasis_basic_opens.open_eq_sUnion, open_eq_sUnion
-/
theorem eq_biUnion_of_isOpen {s : Set (PrimeSpectrum R)} (hs : IsOpen s) :
    s = ⋃ (r : R) (_ : ↑(basicOpen r) subseteq s), basicOpen r :=
(isTopologicalBasis_basic_opens.open_eq_sUnion' hs).trans by aesop

/--
theorem `isBasis_basic_opens` / 定理 `isBasis_basic_opens`

English:
theorem isBasis_basic_opens
  statement: TopologicalSpace.Opens.IsBasis (Set.range (@basicOpen R _))
  proof: by
  unfold TopologicalSpace.Opens.IsBasis
  convert! isTopologicalBasis_basic_opens (R := R)
  rw [← Set.range_comp]
  rfl

@[simp]

中文:
定理 isBasis_basic_opens
  结论: 拓扑空间.Opens.是基 (集合.range (@basicOpen R _))
  证明: by
  unfold TopologicalSpace.Opens.IsBasis
  convert! isTopologicalBasis_basic_opens (R := R)
  rw [← Set.range_comp]
  rfl

@[simp]

Depends on / 依赖: IsBasis, Set.range_comp, TopologicalSpace, TopologicalSpace.Opens.IsBasis, convert, isTopologicalBasis_basic_opens, range_comp
-/
theorem isBasis_basic_opens : TopologicalSpace.Opens.IsBasis (Set.range (@basicOpen R _)) := by
  unfold TopologicalSpace.Opens.IsBasis
  convert! isTopologicalBasis_basic_opens (R := R)
  rw [← Set.range_comp]
  rfl

@[simp]
/--
theorem `basicOpen_eq_bot_iff` / 定理 `basicOpen_eq_bot_iff`

English:
theorem basicOpen_eq_bot_iff
  given: (f : R)
  statement: basicOpen f = ⊥ ↔ IsNilpotent f
  proof: by
  rw [← TopologicalSpace.Opens.coe_inj]; rw [basicOpen_eq_zeroLocus_compl]
  simp only [Set.eq_univ_iff_forall, Set.singleton_subset_iff, TopologicalSpace.Opens.coe_bot,
    nilpotent_iff_mem_prime, Set.compl_empty_iff, mem_zeroLocus, SetLike.mem_coe]
  exact ⟨fun h I hI => h ⟨I, hI⟩, fun h ⟨I, hI⟩ => h I hI⟩

中文:
定理 basicOpen_eq_bot_iff
  条件: (f : R)
  结论: basicOpen f = ⊥ ↔ 是幂零 f
  证明: by
  rw [← TopologicalSpace.Opens.coe_inj]; rw [basicOpen_eq_zeroLocus_compl]
  simp only [Set.eq_univ_iff_forall, Set.singleton_subset_iff, TopologicalSpace.Opens.coe_bot,
    nilpotent_iff_mem_prime, Set.compl_empty_iff, mem_zeroLocus, SetLike.mem_coe]
  exact ⟨fun h I hI => h ⟨I, hI⟩, fun h ⟨I, hI⟩ => h I hI⟩

Depends on / 依赖: Set.compl_empty_iff, Set.eq_univ_iff_forall, Set.singleton_subset_iff, SetLike, SetLike.mem_coe, TopologicalSpace, TopologicalSpace.Opens.coe_bot, TopologicalSpace.Opens.coe_inj, basicOpen_eq_zeroLocus_compl, coe_bot, coe_inj, compl_empty_iff, eq_univ_iff_forall, mem_coe, mem_zeroLocus, nilpotent_iff_mem_prime, singleton_subset_iff
-/
theorem basicOpen_eq_bot_iff (f : R) : basicOpen f = ⊥ ↔ IsNilpotent f := by
  rw [← TopologicalSpace.Opens.coe_inj]; rw [basicOpen_eq_zeroLocus_compl]
  simp only [Set.eq_univ_iff_forall, Set.singleton_subset_iff, TopologicalSpace.Opens.coe_bot,
    nilpotent_iff_mem_prime, Set.compl_empty_iff, mem_zeroLocus, SetLike.mem_coe]
  exact ⟨fun h I hI => h ⟨I, hI⟩, fun h ⟨I, hI⟩ => h I hI⟩

/--
theorem `localization_away_comap_range` / 定理 `localization_away_comap_range`

English:
theorem localization_away_comap_range
  statement: (S : Type v) [CommSemiring S] [Algebra R S] (r : R)
  proof: by
  rw [localization_comap_range S (Submonoid.powers r)]
  ext x
  simp only [mem_zeroLocus, basicOpen_eq_zeroLocus_compl, SetLike.mem_coe, Set.mem_ofPred_eq,
    Set.singleton_subset_iff, Set.mem_compl_iff, disjoint_iff_inf_le]
  constructor
  · intro h₁ h₂
    exact h₁ ⟨Submonoid.mem_powers r, h₂⟩
  · rintro h₁ _ ⟨⟨n, rfl⟩, h₃⟩
    exact h₁ (x.2.mem_of_pow_mem _ h₃)

中文:
定理 localization_away_comap_range
  结论: (S : 类型v) [交换半环 S] [代数 R S] (r : R)
  证明: by
  rw [localization_comap_range S (Submonoid.powers r)]
  ext x
  simp only [mem_zeroLocus, basicOpen_eq_zeroLocus_compl, SetLike.mem_coe, Set.mem_ofPred_eq,
    Set.singleton_subset_iff, Set.mem_compl_iff, disjoint_iff_inf_le]
  constructor
  · intro h₁ h₂
    exact h₁ ⟨Submonoid.mem_powers r, h₂⟩
  · rintro h₁ _ ⟨⟨n, rfl⟩, h₃⟩
    exact h₁ (x.2.mem_of_pow_mem _ h₃)

Depends on / 依赖: Set.mem_compl_iff, Set.mem_ofPred_eq, Set.singleton_subset_iff, SetLike, SetLike.mem_coe, Submonoid, Submonoid.mem_powers, Submonoid.powers, basicOpen_eq_zeroLocus_compl, disjoint_iff_inf_le, localization_comap_range, mem_coe, mem_compl_iff, mem_ofPred_eq, mem_of_pow_mem, mem_powers, mem_zeroLocus, powers, singleton_subset_iff
-/
theorem localization_away_comap_range (S : Type v) [CommSemiring S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : Set.range (comap (algebraMap R S)) = basicOpen r := by
  rw [localization_comap_range S (Submonoid.powers r)]
  ext x
  simp only [mem_zeroLocus, basicOpen_eq_zeroLocus_compl, SetLike.mem_coe, Set.mem_ofPred_eq,
    Set.singleton_subset_iff, Set.mem_compl_iff, disjoint_iff_inf_le]
  constructor
  · intro h₁ h₂
    exact h₁ ⟨Submonoid.mem_powers r, h₂⟩
  · rintro h₁ _ ⟨⟨n, rfl⟩, h₃⟩
    exact h₁ (x.2.mem_of_pow_mem _ h₃)

/--
theorem `localization_away_isOpenEmbedding` / 定理 `localization_away_isOpenEmbedding`

English:
theorem localization_away_isOpenEmbedding
  statement: (S : Type v) [CommSemiring S] [Algebra R S] (r : R)
  proof: localization_comap_isEmbedding S (Submonoid.powers r)
  isOpen_range := by
    rw [localization_away_comap_range S r]
    exact isOpen_basicOpen

中文:
定理 localization_away_isOpenEmbedding
  结论: (S : 类型v) [交换半环 S] [代数 R S] (r : R)
  证明: localization_comap_isEmbedding S (Submonoid.powers r)
  isOpen_range := by
    rw [localization_away_comap_range S r]
    exact isOpen_basicOpen

Depends on / 依赖: Submonoid, Submonoid.powers, localization_comap_isEmbedding, powers
-/
theorem localization_away_isOpenEmbedding (S : Type v) [CommSemiring S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : IsOpenEmbedding (comap (algebraMap R S)) where
  toIsEmbedding := localization_comap_isEmbedding S (Submonoid.powers r)
  isOpen_range := by
    rw [localization_away_comap_range S r]
    exact isOpen_basicOpen

/--
theorem `isCompact_basicOpen` / 定理 `isCompact_basicOpen`

English:
theorem isCompact_basicOpen
  given: (f : R)
  statement: IsCompact (basicOpen f : Set (PrimeSpectrum R))
  proof: by
  rw [← localization_away_comap_range (Localization (Submonoid.powers f))]
  exact isCompact_range (continuous_comap _)

中文:
定理 isCompact_basicOpen
  条件: (f : R)
  结论: 是紧集 (basicOpen f : 集合 (素谱 R))
  证明: by
  rw [← localization_away_comap_range (Localization (Submonoid.powers f))]
  exact isCompact_range (continuous_comap _)

Depends on / 依赖: Localization, Submonoid, Submonoid.powers, continuous_comap, isCompact_range, localization_away_comap_range, powers
-/
theorem isCompact_basicOpen (f : R) : IsCompact (basicOpen f : Set (PrimeSpectrum R)) := by
  rw [← localization_away_comap_range (Localization (Submonoid.powers f))]
  exact isCompact_range (continuous_comap _)

/--
lemma `comap_basicOpen` / 引理 `comap_basicOpen`

English:
lemma comap_basicOpen
  given: (f : R ->+* S) (x : R)
  proof: rfl

中文:
引理 comap_basicOpen
  条件: (f : R ->+* S) (x : R)
  证明: rfl
-/
lemma comap_basicOpen (f : R ->+* S) (x : R) :
    TopologicalSpace.Opens.comap ⟨comap f, continuous_comap f⟩ (basicOpen x) = basicOpen (f x) :=
  rfl

open TopologicalSpace in
/--
lemma `iSup_basicOpen_eq_top_iff` / 引理 `iSup_basicOpen_eq_top_iff`

English:
lemma iSup_basicOpen_eq_top_iff
  given: {ι : Type*} {f : ι -> R}
  proof: by
  rw [SetLike.ext'_iff]; rw [Opens.coe_iSup]
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Opens.coe_top, ← Set.compl_iInter,
    ← PrimeSpectrum.zeroLocus_iUnion]
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top]; rw [compl_involutive.eq_iff]
  simp only [Set.iUnion_singleton_eq_range, Set.compl_univ, PrimeSpectrum.zeroLocus_span]

中文:
引理 iSup_basicOpen_eq_top_iff
  条件: {ι : 类型} {f : ι -> R}
  证明: by
  rw [SetLike.ext'_iff]; rw [Opens.coe_iSup]
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Opens.coe_top, ← Set.compl_iInter,
    ← PrimeSpectrum.zeroLocus_iUnion]
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top]; rw [compl_involutive.eq_iff]
  simp only [Set.iUnion_singleton_eq_range, Set.compl_univ, PrimeSpectrum.zeroLocus_span]

Depends on / 依赖: Opens.coe_iSup, Opens.coe_top, PrimeSpectrum, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_iUnion, PrimeSpectrum.zeroLocus_span, Set.compl_iInter, Set.compl_univ, Set.iUnion_singleton_eq_range, SetLike, SetLike.ext, _iff, basicOpen_eq_zeroLocus_compl, coe_iSup, coe_top, compl_iInter, compl_involutive, compl_involutive.eq_iff, compl_univ
-/
lemma iSup_basicOpen_eq_top_iff {ι : Type*} {f : ι -> R} :
    (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span (Set.range f) = ⊤ := by
  rw [SetLike.ext'_iff]; rw [Opens.coe_iSup]
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Opens.coe_top, ← Set.compl_iInter,
    ← PrimeSpectrum.zeroLocus_iUnion]
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top]; rw [compl_involutive.eq_iff]
  simp only [Set.iUnion_singleton_eq_range, Set.compl_univ, PrimeSpectrum.zeroLocus_span]

/--
lemma `iSup_basicOpen_eq_top_iff'` / 引理 `iSup_basicOpen_eq_top_iff'`

English:
lemma iSup_basicOpen_eq_top_iff'
  given: {s : Set R}
  proof: by
  conv_rhs => rw [← Subtype.range_val (s := s), ← iSup_basicOpen_eq_top_iff]
  simp

中文:
引理 iSup_basicOpen_eq_top_iff'
  条件: {s : 集合 R}
  证明: by
  conv_rhs => rw [← Subtype.range_val (s := s), ← iSup_basicOpen_eq_top_iff]
  simp

Depends on / 依赖: Subtype, Subtype.range_val, conv_rhs, iSup_basicOpen_eq_top_iff, range_val
-/
lemma iSup_basicOpen_eq_top_iff' {s : Set R} :
    (⨆ i in s, PrimeSpectrum.basicOpen i) = ⊤ ↔ Ideal.span s = ⊤ := by
  conv_rhs => rw [← Subtype.range_val (s := s), ← iSup_basicOpen_eq_top_iff]
  simp

/--
theorem `isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton` / 定理 `isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`

English:
theorem isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton
  statement: [Algebra R S]
  proof: have : IsLocalization.AtPrime (Localization.Away f) p.1 := by
    refine .of_le_of_exists_dvd (.powers f) _
      (Submonoid.powers_le.mpr <| by apply h ▸ Set.mem_singleton p) fun r hr => ?_
    contrapose! hr
    simp_rw [← Ideal.mem_span_singleton] at hr
    have ⟨q, prime, le, disj⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {r})
      (.powers f) (Set.disjoint_right.mpr hr)
    have : ⟨q, prime⟩ in (basicOpen f).1 := Set.disjoint_right.mp disj (Submonoid.mem_powers f)
    rw [h]; rw [Set.mem_singleton_iff] at this
    rw [← this]
    exact not_not.mpr (q.span_singleton_le_iff_mem.mp le)
  IsLocalization.isLocalization_iff_of_isLocalization _ _ (Localization.Away f)

中文:
定理 isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton
  结论: [代数 R S]
  证明: have : IsLocalization.AtPrime (Localization.Away f) p.1 := by
    refine .of_le_of_exists_dvd (.powers f) _
      (Submonoid.powers_le.mpr <| by apply h ▸ Set.mem_singleton p) fun r hr => ?_
    contrapose! hr
    simp_rw [← Ideal.mem_span_singleton] at hr
    have ⟨q, prime, le, disj⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {r})
      (.powers f) (Set.disjoint_right.mpr hr)
    have : ⟨q, prime⟩ in (basicOpen f).1 := Set.disjoint_right.mp disj (Submonoid.mem_powers f)
    rw [h]; rw [Set.mem_singleton_iff] at this
    rw [← this]
    exact not_not.mpr (q.span_singleton_le_iff_mem.mp le)
  IsLocalization.isLocalization_iff_of_isLocalization _ _ (Localization.Away f)

Depends on / 依赖: AtPrime, Ideal.exists_le_prime_disjoint, Ideal.mem_span_singleton, Ideal.span, IsLocalization, IsLocalization.AtPrime, Localization, Localization.Away, Set.disjoint_right.mp, Set.disjoint_right.mpr, Set.mem_singleton, Set.mem_singleton_iff, Submonoid, Submonoid.mem_powers, Submonoid.powers_le.mpr, basicOpen, contrapose, disjoint_right, exists_le_prime_disjoint, mem_powers
-/
theorem isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton [Algebra R S]
    {f : R} {p : PrimeSpectrum R} (h : (basicOpen f).1 = {p}) :
    IsLocalization.Away f S ↔ IsLocalization.AtPrime S p.1 :=
  have : IsLocalization.AtPrime (Localization.Away f) p.1 := by
    refine .of_le_of_exists_dvd (.powers f) _
      (Submonoid.powers_le.mpr <| by apply h ▸ Set.mem_singleton p) fun r hr => ?_
    contrapose! hr
    simp_rw [← Ideal.mem_span_singleton] at hr
    have ⟨q, prime, le, disj⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {r})
      (.powers f) (Set.disjoint_right.mpr hr)
    have : ⟨q, prime⟩ in (basicOpen f).1 := Set.disjoint_right.mp disj (Submonoid.mem_powers f)
    rw [h]; rw [Set.mem_singleton_iff] at this
    rw [← this]
    exact not_not.mpr (q.span_singleton_le_iff_mem.mp le)
  IsLocalization.isLocalization_iff_of_isLocalization _ _ (Localization.Away f)

open Localization Polynomial Set in
/--
lemma `range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk` / 引理 `range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk`

English:
lemma range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk
  proof: (mapRingHom (algebraMap R (Away c))).toAlgebra
    (range (comap (algebraMap R[X] (Away c)[X])))ᶜ
      = range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) := by
  let := (mapRingHom (algebraMap R (Away c))).toAlgebra
  have := Polynomial.isLocalization (.powers c) (Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj]; rw [localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom, Ideal.map_span]

中文:
引理 range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk
  证明: (mapRingHom (algebraMap R (Away c))).toAlgebra
    (range (comap (algebraMap R[X] (Away c)[X])))ᶜ
      = range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) := by
  let := (mapRingHom (algebraMap R (Away c))).toAlgebra
  have := Polynomial.isLocalization (.powers c) (Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj]; rw [localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom, Ideal.map_span]

Depends on / 依赖: algebraMap, mapRingHom, toAlgebra
-/
lemma range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk
    {R : Type*} [CommRing R] (c : R) :
    letI := (mapRingHom (algebraMap R (Away c))).toAlgebra
    (range (comap (algebraMap R[X] (Away c)[X])))ᶜ
      = range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) := by
  let := (mapRingHom (algebraMap R (Away c))).toAlgebra
  have := Polynomial.isLocalization (.powers c) (Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj]; rw [localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom, Ideal.map_span]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiSeparatedSpace (PrimeSpectrum R)
  body: .of_isTopologicalBasis isTopologicalBasis_basic_opens fun i j => by
    simpa [← TopologicalSpace.Opens.coe_inf, ← basicOpen_mul, -basicOpen_eq_zeroLocus_compl]
      using isCompact_basicOpen _

中文:
实例 :
  签名: 拟分离空间 (素谱 R)
  定义体: .of_isTopologicalBasis isTopologicalBasis_basic_opens fun i j => by
    simpa [← TopologicalSpace.Opens.coe_inf, ← basicOpen_mul, -basicOpen_eq_zeroLocus_compl]
      using isCompact_basicOpen _

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.coe_inf, basicOpen_eq_zeroLocus_compl, basicOpen_mul, coe_inf, isCompact_basicOpen, isTopologicalBasis_basic_opens, of_isTopologicalBasis
-/
instance : QuasiSeparatedSpace (PrimeSpectrum R) :=
  .of_isTopologicalBasis isTopologicalBasis_basic_opens fun i j => by
    simpa [← TopologicalSpace.Opens.coe_inf, ← basicOpen_mul, -basicOpen_eq_zeroLocus_compl]
      using isCompact_basicOpen _

end BasicOpen

section Pi

variable {ι : Type*} {R : ι -> Type*} [forall i, CommRing (R i)]

/--
lemma `comap_evalRingHom_basicOpen` / 引理 `comap_evalRingHom_basicOpen`

English:
lemma comap_evalRingHom_basicOpen
  given: [DecidableEq ι] (i : ι) (f : R i)
  proof: by
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    simpa
  · intro hp
    have : p in Set.range (PrimeSpectrum.comap (Pi.evalRingHom R i)) := by
      rw [range_comap_of_surjective _ _ (RingHom.surjective _)]; rw [mem_zeroLocus]; rw [SetLike.coe_subset_coe]
      intro x hx
      rw [RingHom.mem_ker]; rw [Pi.evalRingHom_apply] at hx
      have : Pi.single i f * x = 0 := by
        ext j
        by_cases h : i = j
        · subst h
          simp [hx]
        · simp [h]
      obtain (h | h) := Ideal.IsPrime.mem_or_mem_of_mul_eq_zero p.isPrime this <;> tauto
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, by simpa using hp, by ext; simp⟩

中文:
引理 comap_evalRingHom_basicOpen
  条件: [DecidableEq ι] (i : ι) (f : R i)
  证明: by
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    simpa
  · intro hp
    have : p in Set.range (PrimeSpectrum.comap (Pi.evalRingHom R i)) := by
      rw [range_comap_of_surjective _ _ (RingHom.surjective _)]; rw [mem_zeroLocus]; rw [SetLike.coe_subset_coe]
      intro x hx
      rw [RingHom.mem_ker]; rw [Pi.evalRingHom_apply] at hx
      have : Pi.single i f * x = 0 := by
        ext j
        by_cases h : i = j
        · subst h
          simp [hx]
        · simp [h]
      obtain (h | h) := Ideal.IsPrime.mem_or_mem_of_mul_eq_zero p.isPrime this <;> tauto
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, by simpa using hp, by ext; simp⟩

Depends on / 依赖: Ideal.IsPrime.mem_or_mem_of_mul_eq_zero, IsPrime, Pi.evalRingHom, Pi.evalRingHom_apply, Pi.single, PrimeSpectrum, PrimeSpectrum.comap, RingHom, RingHom.mem_ker, RingHom.surjective, Set.range, SetLike, SetLike.coe_subset_coe, coe_subset_coe, evalRingHom, evalRingHom_apply, isPrime, mem_ker, mem_or_mem_of_mul_eq_zero, mem_zeroLocus
-/
lemma comap_evalRingHom_basicOpen [DecidableEq ι] (i : ι) (f : R i) :
    comap (Pi.evalRingHom R i) '' basicOpen f = basicOpen (Pi.single i f) := by
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    simpa
  · intro hp
    have : p in Set.range (PrimeSpectrum.comap (Pi.evalRingHom R i)) := by
      rw [range_comap_of_surjective _ _ (RingHom.surjective _)]; rw [mem_zeroLocus]; rw [SetLike.coe_subset_coe]
      intro x hx
      rw [RingHom.mem_ker]; rw [Pi.evalRingHom_apply] at hx
      have : Pi.single i f * x = 0 := by
        ext j
        by_cases h : i = j
        · subst h
          simp [hx]
        · simp [h]
      obtain (h | h) := Ideal.IsPrime.mem_or_mem_of_mul_eq_zero p.isPrime this <;> tauto
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, by simpa using hp, by ext; simp⟩

/--
lemma `sigmaToPi_mk_basicOpen` / 引理 `sigmaToPi_mk_basicOpen`

English:
lemma sigmaToPi_mk_basicOpen
  given: [DecidableEq ι] (i : ι) (f : R i)
  proof: by
  simp only [Set.image_image, sigmaToPi_apply]
  exact PrimeSpectrum.comap_evalRingHom_basicOpen _ _

中文:
引理 sigmaToPi_mk_basicOpen
  条件: [DecidableEq ι] (i : ι) (f : R i)
  证明: by
  simp only [Set.image_image, sigmaToPi_apply]
  exact PrimeSpectrum.comap_evalRingHom_basicOpen _ _

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.comap_evalRingHom_basicOpen, Set.image_image, comap_evalRingHom_basicOpen, image_image, sigmaToPi_apply
-/
lemma sigmaToPi_mk_basicOpen [DecidableEq ι] (i : ι) (f : R i) :
    sigmaToPi R '' Sigma.mk i '' basicOpen f = basicOpen (Pi.single i f) := by
  simp only [Set.image_image, sigmaToPi_apply]
  exact PrimeSpectrum.comap_evalRingHom_basicOpen _ _

variable (R) in
/--
lemma `isOpenEmbedding_sigmaToPi` / 引理 `isOpenEmbedding_sigmaToPi`

English:
lemma isOpenEmbedding_sigmaToPi
  statement: Topology.IsOpenEmbedding (sigmaToPi R)
  proof: by
  classical
  refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
  · rw [continuous_sigma_iff]
    intro i
    exact continuous_comap (Pi.evalRingHom R i)
  · exact sigmaToPi_injective R
  · rw [isOpenMap_sigma]
    intro i
    simp only [sigmaToPi_apply, PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff]
    rintro - ⟨f, rfl⟩
    rw [PrimeSpectrum.comap_evalRingHom_basicOpen]
    exact isOpen_basicOpen

中文:
引理 isOpenEmbedding_sigmaToPi
  结论: 拓扑.是开嵌入 (sigmaToPi R)
  证明: by
  classical
  refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
  · rw [continuous_sigma_iff]
    intro i
    exact continuous_comap (Pi.evalRingHom R i)
  · exact sigmaToPi_injective R
  · rw [isOpenMap_sigma]
    intro i
    simp only [sigmaToPi_apply, PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff]
    rintro - ⟨f, rfl⟩
    rw [PrimeSpectrum.comap_evalRingHom_basicOpen]
    exact isOpen_basicOpen

Depends on / 依赖: Pi.evalRingHom, PrimeSpectrum, PrimeSpectrum.comap_evalRingHom_basicOpen, PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff, classical, comap_evalRingHom_basicOpen, continuous_comap, continuous_sigma_iff, evalRingHom, isOpenMap_iff, isOpenMap_sigma, isOpen_basicOpen, isTopologicalBasis_basic_opens, of_continuous_injective_isOpenMap, sigmaToPi_apply, sigmaToPi_injective
-/
lemma isOpenEmbedding_sigmaToPi : Topology.IsOpenEmbedding (sigmaToPi R) := by
  classical
  refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
  · rw [continuous_sigma_iff]
    intro i
    exact continuous_comap (Pi.evalRingHom R i)
  · exact sigmaToPi_injective R
  · rw [isOpenMap_sigma]
    intro i
    simp only [sigmaToPi_apply, PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff]
    rintro - ⟨f, rfl⟩
    rw [PrimeSpectrum.comap_evalRingHom_basicOpen]
    exact isOpen_basicOpen

/--
Definition of `sigmaToPiHomeo` / `sigmaToPiHomeo` 的定义

English:
definition sigmaToPiHomeo
  signature: {ι : Type*} (R : ι -> Type*) [forall i, CommRing (R i)] [Finite ι]
  body: (isOpenEmbedding_sigmaToPi R).toHomeomorphOfSurjective (sigmaToPi_bijective R).surjective

@[simp]

中文:
定义 sigmaToPiHomeo
  签名: {ι : 类型} (R : ι -> 类型) [对任意 i, 交换环 (R i)] [有限 ι]
  定义体: (isOpenEmbedding_sigmaToPi R).toHomeomorphOfSurjective (sigmaToPi_bijective R).surjective

@[simp]

Depends on / 依赖: isOpenEmbedding_sigmaToPi, sigmaToPi_bijective, surjective, toHomeomorphOfSurjective
-/
noncomputable def sigmaToPiHomeo {ι : Type*} (R : ι -> Type*) [forall i, CommRing (R i)] [Finite ι] :
    (Σ i, PrimeSpectrum (R i)) ≃ₜ PrimeSpectrum (Π i, R i) :=
  (isOpenEmbedding_sigmaToPi R).toHomeomorphOfSurjective (sigmaToPi_bijective R).surjective

@[simp]
/--
lemma `sigmaToPiHomeo_apply` / 引理 `sigmaToPiHomeo_apply`

English:
lemma sigmaToPiHomeo_apply
  given: [Finite ι] (p : Σ i, PrimeSpectrum (R i))
  proof: rfl

中文:
引理 sigmaToPiHomeo_apply
  条件: [有限 ι] (p : Σ i, 素谱 (R i))
  证明: rfl
-/
lemma sigmaToPiHomeo_apply [Finite ι] (p : Σ i, PrimeSpectrum (R i)) :
    sigmaToPiHomeo R p = sigmaToPi R p :=
  rfl

end Pi

section DiscreteTopology

variable (R) [DiscreteTopology (PrimeSpectrum R)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toPiLocalization_surjective_of_discreteTopology` / 定理 `toPiLocalization_surjective_of_discreteTopology`

English:
theorem toPiLocalization_surjective_of_discreteTopology
  proof: fun x => by
  have (p : PrimeSpectrum R) : exists f, (basicOpen f : Set _) = {p} :=
    have ⟨_, ⟨f, rfl⟩, hpf, hfp⟩ := isTopologicalBasis_basic_opens.isOpen_iff.mp
      (isOpen_discrete {p}) p rfl
⟨f, hfp.antisymm Set.singleton_subset_iff.mpr hpf⟩
  choose f hf using this
  let e := Equiv.ofInjective f fun p q eq => Set.singleton_injective (hf p ▸ eq ▸ hf q)
  have loc a : IsLocalization.AtPrime (Localization.Away a.1) (e.symm a).1 :=
(isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton <| hf _).mp by
      simp_rw [e, Equiv.apply_ofInjective_symm]; infer_instance
  let algE a := IsLocalization.algEquiv (e.symm a).1.primeCompl
    (Localization.AtPrime (e.symm a).1) (Localization.Away a.1)
have span_eq : Ideal.span (Set.range f) = ⊤ := iSup_basicOpen_eq_top_iff.mp top_unique
    fun p _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨p, (hf p).ge rfl⟩
  replace hf a : (basicOpen a.1 : Set _) = {e.symm a} := by
    simp_rw [e, ← hf, Equiv.apply_ofInjective_symm]
  obtain ⟨r, eq, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top _ span_eq
    (fun a => algE a (x _)) fun a b => by
      obtain rfl | ne := eq_or_ne a b; · rfl
have nil : IsNilpotent (a * b : R) := (basicOpen_eq_bot_iff _).mp by
        simp_rw [basicOpen_mul, SetLike.ext'_iff, TopologicalSpace.Opens.coe_inf, hf]
        exact bot_unique (fun _ ⟨ha, hb⟩ => ne <| e.symm.injective (ha.symm.trans hb))
      apply (IsLocalization.subsingleton (M := .powers (a * b : R)) nil).elim
  refine ⟨r, funext fun I => ?_⟩
  have := eq (e I)
  rwa [← AlgEquiv.symm_apply_eq, AlgEquiv.commutes, e.symm_apply_apply] at this

中文:
定理 toPiLocalization_surjective_of_discreteTopology
  证明: fun x => by
  have (p : PrimeSpectrum R) : exists f, (basicOpen f : Set _) = {p} :=
    have ⟨_, ⟨f, rfl⟩, hpf, hfp⟩ := isTopologicalBasis_basic_opens.isOpen_iff.mp
      (isOpen_discrete {p}) p rfl
⟨f, hfp.antisymm Set.singleton_subset_iff.mpr hpf⟩
  choose f hf using this
  let e := Equiv.ofInjective f fun p q eq => Set.singleton_injective (hf p ▸ eq ▸ hf q)
  have loc a : IsLocalization.AtPrime (Localization.Away a.1) (e.symm a).1 :=
(isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton <| hf _).mp by
      simp_rw [e, Equiv.apply_ofInjective_symm]; infer_instance
  let algE a := IsLocalization.algEquiv (e.symm a).1.primeCompl
    (Localization.AtPrime (e.symm a).1) (Localization.Away a.1)
have span_eq : Ideal.span (Set.range f) = ⊤ := iSup_basicOpen_eq_top_iff.mp top_unique
    fun p _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨p, (hf p).ge rfl⟩
  replace hf a : (basicOpen a.1 : Set _) = {e.symm a} := by
    simp_rw [e, ← hf, Equiv.apply_ofInjective_symm]
  obtain ⟨r, eq, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top _ span_eq
    (fun a => algE a (x _)) fun a b => by
      obtain rfl | ne := eq_or_ne a b; · rfl
have nil : IsNilpotent (a * b : R) := (basicOpen_eq_bot_iff _).mp by
        simp_rw [basicOpen_mul, SetLike.ext'_iff, TopologicalSpace.Opens.coe_inf, hf]
        exact bot_unique (fun _ ⟨ha, hb⟩ => ne <| e.symm.injective (ha.symm.trans hb))
      apply (IsLocalization.subsingleton (M := .powers (a * b : R)) nil).elim
  refine ⟨r, funext fun I => ?_⟩
  have := eq (e I)
  rwa [← AlgEquiv.symm_apply_eq, AlgEquiv.commutes, e.symm_apply_apply] at this

Depends on / 依赖: AtPrime, Equiv.ofInjective, IsLocalization, IsLocalization.AtPrime, Localization, Localization.Away, PrimeSpectrum, Set.singleton_injective, Set.singleton_subset_iff.mpr, antisymm, basicOpen, e.symm, hfp.antisymm, isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton, isOpen_discrete, isOpen_iff, isTopologicalBasis_basic_opens, isTopologicalBasis_basic_opens.isOpen_iff.mp, ofInjective, singleton_injective
-/
theorem toPiLocalization_surjective_of_discreteTopology :
    Function.Surjective (toPiLocalization R) := fun x => by
  have (p : PrimeSpectrum R) : exists f, (basicOpen f : Set _) = {p} :=
    have ⟨_, ⟨f, rfl⟩, hpf, hfp⟩ := isTopologicalBasis_basic_opens.isOpen_iff.mp
      (isOpen_discrete {p}) p rfl
⟨f, hfp.antisymm Set.singleton_subset_iff.mpr hpf⟩
  choose f hf using this
  let e := Equiv.ofInjective f fun p q eq => Set.singleton_injective (hf p ▸ eq ▸ hf q)
  have loc a : IsLocalization.AtPrime (Localization.Away a.1) (e.symm a).1 :=
(isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton <| hf _).mp by
      simp_rw [e, Equiv.apply_ofInjective_symm]; infer_instance
  let algE a := IsLocalization.algEquiv (e.symm a).1.primeCompl
    (Localization.AtPrime (e.symm a).1) (Localization.Away a.1)
have span_eq : Ideal.span (Set.range f) = ⊤ := iSup_basicOpen_eq_top_iff.mp top_unique
    fun p _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨p, (hf p).ge rfl⟩
  replace hf a : (basicOpen a.1 : Set _) = {e.symm a} := by
    simp_rw [e, ← hf, Equiv.apply_ofInjective_symm]
  obtain ⟨r, eq, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top _ span_eq
    (fun a => algE a (x _)) fun a b => by
      obtain rfl | ne := eq_or_ne a b; · rfl
have nil : IsNilpotent (a * b : R) := (basicOpen_eq_bot_iff _).mp by
        simp_rw [basicOpen_mul, SetLike.ext'_iff, TopologicalSpace.Opens.coe_inf, hf]
        exact bot_unique (fun _ ⟨ha, hb⟩ => ne <| e.symm.injective (ha.symm.trans hb))
      apply (IsLocalization.subsingleton (M := .powers (a * b : R)) nil).elim
  refine ⟨r, funext fun I => ?_⟩
  have := eq (e I)
  rwa [← AlgEquiv.symm_apply_eq, AlgEquiv.commutes, e.symm_apply_apply] at this

/--
theorem `maximalSpectrumToPiLocalization_surjective_of_discreteTopology` / 定理 `maximalSpectrumToPiLocalization_surjective_of_discreteTopology`

English:
theorem maximalSpectrumToPiLocalization_surjective_of_discreteTopology
  proof: by
  rw [← piLocalizationToMaximal_comp_toPiLocalization]
  exact (piLocalizationToMaximal_surjective R).comp
    (toPiLocalization_surjective_of_discreteTopology R)

中文:
定理 maximalSpectrumToPiLocalization_surjective_of_discreteTopology
  证明: by
  rw [← piLocalizationToMaximal_comp_toPiLocalization]
  exact (piLocalizationToMaximal_surjective R).comp
    (toPiLocalization_surjective_of_discreteTopology R)

Depends on / 依赖: piLocalizationToMaximal_comp_toPiLocalization, piLocalizationToMaximal_surjective, toPiLocalization_surjective_of_discreteTopology
-/
theorem maximalSpectrumToPiLocalization_surjective_of_discreteTopology :
    Function.Surjective (MaximalSpectrum.toPiLocalization R) := by
  rw [← piLocalizationToMaximal_comp_toPiLocalization]
  exact (piLocalizationToMaximal_surjective R).comp
    (toPiLocalization_surjective_of_discreteTopology R)

/-- If the prime spectrum of a commutative semiring R has discrete Zariski topology, then R is
canonically isomorphic to the product of its localizations at the (finitely many) maximal ideals. -/
@[stacks 00JA
"See also `PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical`."]
/--
Definition of `_root_.MaximalSpectrum.toPiLocalizationEquiv` / `_root_.MaximalSpectrum.toPiLocalizationEquiv` 的定义

English:
definition _root_.MaximalSpectrum.toPiLocalizationEquiv
  signature: :
  body: .ofBijective _ ⟨MaximalSpectrum.toPiLocalization_injective R,
    maximalSpectrumToPiLocalization_surjective_of_discreteTopology R⟩

@[simp]

中文:
定义 _root_.极大谱.toPiLocalizationEquiv
  签名: :
  定义体: .ofBijective _ ⟨MaximalSpectrum.toPiLocalization_injective R,
    maximalSpectrumToPiLocalization_surjective_of_discreteTopology R⟩

@[simp]

Depends on / 依赖: MaximalSpectrum, MaximalSpectrum.toPiLocalization_injective, maximalSpectrumToPiLocalization_surjective_of_discreteTopology, ofBijective, toPiLocalization_injective
-/
def _root_.MaximalSpectrum.toPiLocalizationEquiv :
    R ≃ₐ[R] MaximalSpectrum.PiLocalization R :=
  .ofBijective _ ⟨MaximalSpectrum.toPiLocalization_injective R,
    maximalSpectrumToPiLocalization_surjective_of_discreteTopology R⟩

@[simp]
/--
theorem `_root_.MaximalSpectrum.toPiLocalizationEquiv_apply` / 定理 `_root_.MaximalSpectrum.toPiLocalizationEquiv_apply`

English:
theorem _root_.MaximalSpectrum.toPiLocalizationEquiv_apply
  given: (x : R)
  proof: rfl

@[simp]

中文:
定理 _root_.极大谱.toPiLocalizationEquiv_apply
  条件: (x : R)
  证明: rfl

@[simp]
-/
theorem _root_.MaximalSpectrum.toPiLocalizationEquiv_apply (x : R) :
    MaximalSpectrum.toPiLocalizationEquiv R x = algebraMap R _ x :=
  rfl

@[simp]
/--
theorem `_root_.MaximalSpectrum.toPiLocalizationEquiv_apply_apply` / 定理 `_root_.MaximalSpectrum.toPiLocalizationEquiv_apply_apply`

English:
theorem _root_.MaximalSpectrum.toPiLocalizationEquiv_apply_apply
  given: (x : R) (I : MaximalSpectrum R)
  proof: rfl

中文:
定理 _root_.极大谱.toPiLocalizationEquiv_apply_apply
  条件: (x : R) (I : 极大谱 R)
  证明: rfl
-/
theorem _root_.MaximalSpectrum.toPiLocalizationEquiv_apply_apply (x : R) (I : MaximalSpectrum R) :
    MaximalSpectrum.toPiLocalizationEquiv R x I = algebraMap R _ x :=
  rfl

/--
theorem `discreteTopology_iff_toPiLocalization_surjective` / 定理 `discreteTopology_iff_toPiLocalization_surjective`

English:
theorem discreteTopology_iff_toPiLocalization_surjective
  given: {R} [CommSemiring R]
  proof: ⟨fun _ => toPiLocalization_surjective_of_discreteTopology _,
    discreteTopology_of_toLocalization_surjective⟩

中文:
定理 discreteTopology_iff_toPiLocalization_surjective
  条件: {R} [交换半环 R]
  证明: ⟨fun _ => toPiLocalization_surjective_of_discreteTopology _,
    discreteTopology_of_toLocalization_surjective⟩

Depends on / 依赖: discreteTopology_of_toLocalization_surjective, toPiLocalization_surjective_of_discreteTopology
-/
theorem discreteTopology_iff_toPiLocalization_surjective {R} [CommSemiring R] :
    DiscreteTopology (PrimeSpectrum R) ↔ Function.Surjective (toPiLocalization R) :=
  ⟨fun _ => toPiLocalization_surjective_of_discreteTopology _,
    discreteTopology_of_toLocalization_surjective⟩

/--
theorem `discreteTopology_iff_toPiLocalization_bijective` / 定理 `discreteTopology_iff_toPiLocalization_bijective`

English:
theorem discreteTopology_iff_toPiLocalization_bijective
  given: {R} [CommSemiring R]
  proof: discreteTopology_iff_toPiLocalization_surjective.trans
    (and_iff_right <| toPiLocalization_injective _).symm

中文:
定理 discreteTopology_iff_toPiLocalization_bijective
  条件: {R} [交换半环 R]
  证明: discreteTopology_iff_toPiLocalization_surjective.trans
    (and_iff_right <| toPiLocalization_injective _).symm

Depends on / 依赖: and_iff_right, discreteTopology_iff_toPiLocalization_surjective, discreteTopology_iff_toPiLocalization_surjective.trans, toPiLocalization_injective
-/
theorem discreteTopology_iff_toPiLocalization_bijective {R} [CommSemiring R] :
    DiscreteTopology (PrimeSpectrum R) ↔ Function.Bijective (toPiLocalization R) :=
  discreteTopology_iff_toPiLocalization_surjective.trans
    (and_iff_right <| toPiLocalization_injective _).symm

variable {R} in
/--
lemma `toPiLocalization_bijective` / 引理 `toPiLocalization_bijective`

English:
lemma toPiLocalization_bijective
  statement: Function.Bijective (toPiLocalization R)
  proof: discreteTopology_iff_toPiLocalization_bijective.mp inferInstance

中文:
引理 toPiLocalization_bijective
  结论: 函数.双射 (toPiLocalization R)
  证明: discreteTopology_iff_toPiLocalization_bijective.mp inferInstance

Depends on / 依赖: discreteTopology_iff_toPiLocalization_bijective, discreteTopology_iff_toPiLocalization_bijective.mp
-/
lemma toPiLocalization_bijective : Function.Bijective (toPiLocalization R) :=
  discreteTopology_iff_toPiLocalization_bijective.mp inferInstance

/--
Definition of `toPiLocalizationEquiv` / `toPiLocalizationEquiv` 的定义

English:
definition toPiLocalizationEquiv
  signature: : R ≃ₐ[R] PiLocalization R
  body: .ofBijective _ toPiLocalization_bijective

@[simp]

中文:
定义 toPiLocalizationEquiv
  签名: : R ≃ₐ[R] PiLocalization R
  定义体: .ofBijective _ toPiLocalization_bijective

@[simp]

Depends on / 依赖: ofBijective, toPiLocalization_bijective
-/
def toPiLocalizationEquiv : R ≃ₐ[R] PiLocalization R :=
  .ofBijective _ toPiLocalization_bijective

@[simp]
/--
theorem `toPiLocalizationEquiv_apply` / 定理 `toPiLocalizationEquiv_apply`

English:
theorem toPiLocalizationEquiv_apply
  given: (x : R)
  statement: toPiLocalizationEquiv R x = algebraMap R _ x
  proof: rfl

@[simp]

中文:
定理 toPiLocalizationEquiv_apply
  条件: (x : R)
  结论: toPiLocalizationEquiv R x = algebraMap R _ x
  证明: rfl

@[simp]
-/
theorem toPiLocalizationEquiv_apply (x : R) : toPiLocalizationEquiv R x = algebraMap R _ x :=
  rfl

@[simp]
/--
theorem `toPiLocalizationEquiv_apply_apply` / 定理 `toPiLocalizationEquiv_apply_apply`

English:
theorem toPiLocalizationEquiv_apply_apply
  given: (x : R) (I : PrimeSpectrum R)
  proof: rfl

中文:
定理 toPiLocalizationEquiv_apply_apply
  条件: (x : R) (I : 素谱 R)
  证明: rfl
-/
theorem toPiLocalizationEquiv_apply_apply (x : R) (I : PrimeSpectrum R) :
    toPiLocalizationEquiv R x I = algebraMap R _ x :=
  rfl

end DiscreteTopology

section Order


/--
theorem `le_iff_mem_closure` / 定理 `le_iff_mem_closure`

English:
theorem le_iff_mem_closure
  given: (x y : PrimeSpectrum R)
  proof: by
  rw [← asIdeal_le_asIdeal]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [mem_zeroLocus]; rw [vanishingIdeal_singleton]; rw [SetLike.coe_subset_coe]

中文:
定理 le_iff_mem_closure
  条件: (x y : 素谱 R)
  证明: by
  rw [← asIdeal_le_asIdeal]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [mem_zeroLocus]; rw [vanishingIdeal_singleton]; rw [SetLike.coe_subset_coe]

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, asIdeal_le_asIdeal, coe_subset_coe, mem_zeroLocus, vanishingIdeal_singleton, zeroLocus_vanishingIdeal_eq_closure
-/
theorem le_iff_mem_closure (x y : PrimeSpectrum R) :
    x <= y ↔ y in closure ({x} : Set (PrimeSpectrum R)) := by
  rw [← asIdeal_le_asIdeal]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [mem_zeroLocus]; rw [vanishingIdeal_singleton]; rw [SetLike.coe_subset_coe]

/--
theorem `le_iff_specializes` / 定理 `le_iff_specializes`

English:
theorem le_iff_specializes
  given: (x y : PrimeSpectrum R)
  statement: x <= y ↔ x ⤳ y
  proof: (le_iff_mem_closure x y).trans specializes_iff_mem_closure.symm

中文:
定理 le_iff_specializes
  条件: (x y : 素谱 R)
  结论: x <= y ↔ x ⤳ y
  证明: (le_iff_mem_closure x y).trans specializes_iff_mem_closure.symm

Depends on / 依赖: le_iff_mem_closure, specializes_iff_mem_closure, specializes_iff_mem_closure.symm
-/
theorem le_iff_specializes (x y : PrimeSpectrum R) : x <= y ↔ x ⤳ y :=
  (le_iff_mem_closure x y).trans specializes_iff_mem_closure.symm

/-- `nhds` as an order embedding. -/
@[simps!]
/--
Definition of `nhdsOrderEmbedding` / `nhdsOrderEmbedding` 的定义

English:
definition nhdsOrderEmbedding
  signature: : PrimeSpectrum R ↪o Filter (PrimeSpectrum R)
  body: OrderEmbedding.ofMapLEIff nhds fun a b => (le_iff_specializes a b).symm

中文:
定义 nhdsOrderEmbedding
  签名: : 素谱 R ↪o 滤子 (素谱 R)
  定义体: OrderEmbedding.ofMapLEIff nhds fun a b => (le_iff_specializes a b).symm

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofMapLEIff, le_iff_specializes, ofMapLEIff
-/
def nhdsOrderEmbedding : PrimeSpectrum R ↪o Filter (PrimeSpectrum R) :=
  OrderEmbedding.ofMapLEIff nhds fun a b => (le_iff_specializes a b).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T0Space (PrimeSpectrum R)
  body: ⟨nhdsOrderEmbedding.inj'⟩

中文:
实例 :
  签名: T0空间 (素谱 R)
  定义体: ⟨nhdsOrderEmbedding.inj'⟩

Depends on / 依赖: nhdsOrderEmbedding, nhdsOrderEmbedding.inj
-/
instance : T0Space (PrimeSpectrum R) :=
  ⟨nhdsOrderEmbedding.inj'⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PrespectralSpace (PrimeSpectrum R)
  body: .of_isTopologicalBasis' isTopologicalBasis_basic_opens isCompact_basicOpen

中文:
实例 :
  签名: Prespectral空间 (素谱 R)
  定义体: .of_isTopologicalBasis' isTopologicalBasis_basic_opens isCompact_basicOpen

Depends on / 依赖: isCompact_basicOpen, isTopologicalBasis_basic_opens, of_isTopologicalBasis
-/
instance : PrespectralSpace (PrimeSpectrum R) :=
  .of_isTopologicalBasis' isTopologicalBasis_basic_opens isCompact_basicOpen

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SpectralSpace (PrimeSpectrum R)

中文:
实例 :
  签名: 谱空间 (素谱 R)
-/
instance : SpectralSpace (PrimeSpectrum R) where

end Order

/--
Definition of `localizationMapOfSpecializes` / `localizationMapOfSpecializes` 的定义

English:
definition localizationMapOfSpecializes
  signature: {x y : PrimeSpectrum R} (h : x ⤳ y)
  body: @IsLocalization.lift _ _ _ _ _ _ _ _ Localization.isLocalization
    (algebraMap R (Localization.AtPrime x.asIdeal))
    (by
      rintro ⟨a, ha⟩
      rw [← PrimeSpectrum.le_iff_specializes]; rw [← asIdeal_le_asIdeal]; rw [← SetLike.coe_subset_coe]; rw [←
        Set.compl_subset_compl] at h
      exact (IsLocalization.map_units (Localization.AtPrime x.asIdeal)
        ⟨a, show a in x.asIdeal.primeCompl from h ha⟩ :))

中文:
定义 localizationMapOfSpecializes
  签名: {x y : 素谱 R} (h : x ⤳ y)
  定义体: @IsLocalization.lift _ _ _ _ _ _ _ _ Localization.isLocalization
    (algebraMap R (Localization.AtPrime x.asIdeal))
    (by
      rintro ⟨a, ha⟩
      rw [← PrimeSpectrum.le_iff_specializes]; rw [← asIdeal_le_asIdeal]; rw [← SetLike.coe_subset_coe]; rw [←
        Set.compl_subset_compl] at h
      exact (IsLocalization.map_units (Localization.AtPrime x.asIdeal)
        ⟨a, show a in x.asIdeal.primeCompl from h ha⟩ :))

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.lift, IsLocalization.map_units, Localization, Localization.AtPrime, Localization.isLocalization, PrimeSpectrum, PrimeSpectrum.le_iff_specializes, Set.compl_subset_compl, SetLike, SetLike.coe_subset_coe, algebraMap, asIdeal, asIdeal_le_asIdeal, coe_subset_coe, compl_subset_compl, isLocalization, le_iff_specializes, map_units
-/
def localizationMapOfSpecializes {x y : PrimeSpectrum R} (h : x ⤳ y) :
    Localization.AtPrime y.asIdeal ->+* Localization.AtPrime x.asIdeal :=
  @IsLocalization.lift _ _ _ _ _ _ _ _ Localization.isLocalization
    (algebraMap R (Localization.AtPrime x.asIdeal))
    (by
      rintro ⟨a, ha⟩
      rw [← PrimeSpectrum.le_iff_specializes]; rw [← asIdeal_le_asIdeal]; rw [← SetLike.coe_subset_coe]; rw [←
        Set.compl_subset_compl] at h
      exact (IsLocalization.map_units (Localization.AtPrime x.asIdeal)
        ⟨a, show a in x.asIdeal.primeCompl from h ha⟩ :))

section stableUnderSpecialization

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R ->+* S)

/--
lemma `isClosed_image_of_stableUnderSpecialization` / 引理 `isClosed_image_of_stableUnderSpecialization`

English:
lemma isClosed_image_of_stableUnderSpecialization
  proof: by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  refine (isClosed_iff_zeroLocus _).mpr ⟨I.comap f, le_antisymm ?_ fun p hp => ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact Ideal.comap_mono hq
  · obtain ⟨q, hqI, hq, hqle⟩ := p.asIdeal.exists_ideal_comap_le_prime I hp
    exact hf ((le_iff_specializes ⟨q.comap f, inferInstance⟩ p).mp hqle) ⟨⟨q, hq⟩, hqI, rfl⟩

@[stacks 00HY]

中文:
引理 isClosed_image_of_stableUnderSpecialization
  证明: by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  refine (isClosed_iff_zeroLocus _).mpr ⟨I.comap f, le_antisymm ?_ fun p hp => ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact Ideal.comap_mono hq
  · obtain ⟨q, hqI, hq, hqle⟩ := p.asIdeal.exists_ideal_comap_le_prime I hp
    exact hf ((le_iff_specializes ⟨q.comap f, inferInstance⟩ p).mp hqle) ⟨⟨q, hq⟩, hqI, rfl⟩

@[stacks 00HY]

Depends on / 依赖: I.comap, Ideal.comap_mono, PrimeSpectrum, PrimeSpectrum.isClosed_iff_zeroLocus_ideal, asIdeal, comap_mono, exists_ideal_comap_le_prime, isClosed_iff_zeroLocus, isClosed_iff_zeroLocus_ideal, le_antisymm, le_iff_specializes, p.asIdeal.exists_ideal_comap_le_prime, q.comap
-/
lemma isClosed_image_of_stableUnderSpecialization
    (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z)
    (hf : StableUnderSpecialization (comap f '' Z)) :
    IsClosed (comap f '' Z) := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  refine (isClosed_iff_zeroLocus _).mpr ⟨I.comap f, le_antisymm ?_ fun p hp => ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact Ideal.comap_mono hq
  · obtain ⟨q, hqI, hq, hqle⟩ := p.asIdeal.exists_ideal_comap_le_prime I hp
    exact hf ((le_iff_specializes ⟨q.comap f, inferInstance⟩ p).mp hqle) ⟨⟨q, hq⟩, hqI, rfl⟩

@[stacks 00HY]
/--
lemma `isClosed_range_of_stableUnderSpecialization` / 引理 `isClosed_range_of_stableUnderSpecialization`

English:
lemma isClosed_range_of_stableUnderSpecialization
  proof: by
  rw [← Set.image_univ] at hf ⊢
  exact isClosed_image_of_stableUnderSpecialization _ _ isClosed_univ hf

中文:
引理 isClosed_range_of_stableUnderSpecialization
  证明: by
  rw [← Set.image_univ] at hf ⊢
  exact isClosed_image_of_stableUnderSpecialization _ _ isClosed_univ hf

Depends on / 依赖: Set.image_univ, image_univ, isClosed_image_of_stableUnderSpecialization, isClosed_univ
-/
lemma isClosed_range_of_stableUnderSpecialization
    (hf : StableUnderSpecialization (Set.range (comap f))) :
    IsClosed (Set.range (comap f)) := by
  rw [← Set.image_univ] at hf ⊢
  exact isClosed_image_of_stableUnderSpecialization _ _ isClosed_univ hf

variable {f} in
@[stacks 00HY]
/--
lemma `stableUnderSpecialization_range_iff` / 引理 `stableUnderSpecialization_range_iff`

English:
lemma stableUnderSpecialization_range_iff
  proof: ⟨isClosed_range_of_stableUnderSpecialization f, fun h => h.stableUnderSpecialization⟩

中文:
引理 stableUnderSpecialization_range_iff
  证明: ⟨isClosed_range_of_stableUnderSpecialization f, fun h => h.stableUnderSpecialization⟩

Depends on / 依赖: h.stableUnderSpecialization, isClosed_range_of_stableUnderSpecialization, stableUnderSpecialization
-/
lemma stableUnderSpecialization_range_iff :
    StableUnderSpecialization (Set.range (comap f)) ↔ IsClosed (Set.range (comap f)) :=
  ⟨isClosed_range_of_stableUnderSpecialization f, fun h => h.stableUnderSpecialization⟩

/--
lemma `stableUnderSpecialization_image_iff` / 引理 `stableUnderSpecialization_image_iff`

English:
lemma stableUnderSpecialization_image_iff
  proof: ⟨isClosed_image_of_stableUnderSpecialization f Z hZ, fun h => h.stableUnderSpecialization⟩

中文:
引理 stableUnderSpecialization_image_iff
  证明: ⟨isClosed_image_of_stableUnderSpecialization f Z hZ, fun h => h.stableUnderSpecialization⟩

Depends on / 依赖: h.stableUnderSpecialization, isClosed_image_of_stableUnderSpecialization, stableUnderSpecialization
-/
lemma stableUnderSpecialization_image_iff
    (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z) :
    StableUnderSpecialization (comap f '' Z) ↔ IsClosed (comap f '' Z) :=
  ⟨isClosed_image_of_stableUnderSpecialization f Z hZ, fun h => h.stableUnderSpecialization⟩

end stableUnderSpecialization

section IsQuotientMap

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R ->+* S}
  (h₁ : Function.Surjective (comap f))

include h₁

/--
lemma `isQuotientMap_of_specializingMap` / 引理 `isQuotientMap_of_specializingMap`

English:
lemma isQuotientMap_of_specializingMap
  given: (h₂ : SpecializingMap (comap f))
  proof: by
  rw [Topology.isQuotientMap_iff_isClosed]
  exact ⟨h₁, fun s => ⟨fun hs => hs.preimage (continuous_comap f),
    fun hsc => Set.image_preimage_eq s h₁ ▸ isClosed_image_of_stableUnderSpecialization _ _ hsc
      (h₂.stableUnderSpecialization_image hsc.stableUnderSpecialization)⟩⟩

中文:
引理 isQuotientMap_of_specializingMap
  条件: (h₂ : SpecializingMap (comap f))
  证明: by
  rw [Topology.isQuotientMap_iff_isClosed]
  exact ⟨h₁, fun s => ⟨fun hs => hs.preimage (continuous_comap f),
    fun hsc => Set.image_preimage_eq s h₁ ▸ isClosed_image_of_stableUnderSpecialization _ _ hsc
      (h₂.stableUnderSpecialization_image hsc.stableUnderSpecialization)⟩⟩

Depends on / 依赖: Set.image_preimage_eq, Topology, Topology.isQuotientMap_iff_isClosed, continuous_comap, hs.preimage, hsc.stableUnderSpecialization, image_preimage_eq, isClosed_image_of_stableUnderSpecialization, isQuotientMap_iff_isClosed, preimage, stableUnderSpecialization, stableUnderSpecialization_image
-/
lemma isQuotientMap_of_specializingMap (h₂ : SpecializingMap (comap f)) :
    Topology.IsQuotientMap (comap f) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  exact ⟨h₁, fun s => ⟨fun hs => hs.preimage (continuous_comap f),
    fun hsc => Set.image_preimage_eq s h₁ ▸ isClosed_image_of_stableUnderSpecialization _ _ hsc
      (h₂.stableUnderSpecialization_image hsc.stableUnderSpecialization)⟩⟩

/--
lemma `isQuotientMap_of_generalizingMap` / 引理 `isQuotientMap_of_generalizingMap`

English:
lemma isQuotientMap_of_generalizingMap
  given: (h₂ : GeneralizingMap (comap f))
  proof: by
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨h₁, fun s => ⟨fun hs => hs.preimage (continuous_comap f),
    fun hsc => Set.image_preimage_eq s h₁ ▸ ?_⟩⟩
  apply isClosed_image_of_stableUnderSpecialization _ _ hsc
  rw [Set.image_preimage_eq s h₁]; rw [← stableUnderGeneralization_compl_iff]
  convert! h₂.stableUnderGeneralization_image hsc.isOpen_compl.stableUnderGeneralization
  rw [← Set.preimage_compl]; rw [Set.image_preimage_eq _ h₁]

中文:
引理 isQuotientMap_of_generalizingMap
  条件: (h₂ : GeneralizingMap (comap f))
  证明: by
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨h₁, fun s => ⟨fun hs => hs.preimage (continuous_comap f),
    fun hsc => Set.image_preimage_eq s h₁ ▸ ?_⟩⟩
  apply isClosed_image_of_stableUnderSpecialization _ _ hsc
  rw [Set.image_preimage_eq s h₁]; rw [← stableUnderGeneralization_compl_iff]
  convert! h₂.stableUnderGeneralization_image hsc.isOpen_compl.stableUnderGeneralization
  rw [← Set.preimage_compl]; rw [Set.image_preimage_eq _ h₁]

Depends on / 依赖: Set.image_preimage_eq, Set.preimage_compl, Topology, Topology.isQuotientMap_iff_isClosed, continuous_comap, convert, hs.preimage, hsc.isOpen_compl.stableUnderGeneralization, image_preimage_eq, isClosed_image_of_stableUnderSpecialization, isOpen_compl, isQuotientMap_iff_isClosed, preimage, preimage_compl, stableUnderGeneralization, stableUnderGeneralization_compl_iff, stableUnderGeneralization_image
-/
lemma isQuotientMap_of_generalizingMap (h₂ : GeneralizingMap (comap f)) :
    Topology.IsQuotientMap (comap f) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨h₁, fun s => ⟨fun hs => hs.preimage (continuous_comap f),
    fun hsc => Set.image_preimage_eq s h₁ ▸ ?_⟩⟩
  apply isClosed_image_of_stableUnderSpecialization _ _ hsc
  rw [Set.image_preimage_eq s h₁]; rw [← stableUnderGeneralization_compl_iff]
  convert! h₂.stableUnderGeneralization_image hsc.isOpen_compl.stableUnderGeneralization
  rw [← Set.preimage_compl]; rw [Set.image_preimage_eq _ h₁]

end IsQuotientMap

section denseRange

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R ->+* S)

/--
lemma `vanishingIdeal_range_comap` / 引理 `vanishingIdeal_range_comap`

English:
lemma vanishingIdeal_range_comap
  proof: by
  ext x
  rw [RingHom.ker_eq_comap_bot]; rw [← Ideal.comap_radical]; rw [Ideal.radical_eq_sInf]
  simp only [mem_vanishingIdeal, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    comap_asIdeal, Ideal.mem_comap, bot_le, true_and, Submodule.mem_sInf, Set.mem_ofPred_eq]
  exact ⟨fun H I hI => H ⟨I, hI⟩, fun H I => H I.1 I.2⟩

中文:
引理 vanishingIdeal_range_comap
  证明: by
  ext x
  rw [RingHom.ker_eq_comap_bot]; rw [← Ideal.comap_radical]; rw [Ideal.radical_eq_sInf]
  simp only [mem_vanishingIdeal, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    comap_asIdeal, Ideal.mem_comap, bot_le, true_and, Submodule.mem_sInf, Set.mem_ofPred_eq]
  exact ⟨fun H I hI => H ⟨I, hI⟩, fun H I => H I.1 I.2⟩

Depends on / 依赖: Ideal.comap_radical, Ideal.mem_comap, Ideal.radical_eq_sInf, RingHom, RingHom.ker_eq_comap_bot, Set.mem_ofPred_eq, Set.mem_range, Submodule, Submodule.mem_sInf, bot_le, comap_asIdeal, comap_radical, forall_apply_eq_imp_iff, forall_exists_index, ker_eq_comap_bot, mem_comap, mem_ofPred_eq, mem_range, mem_sInf, mem_vanishingIdeal
-/
lemma vanishingIdeal_range_comap :
    vanishingIdeal (Set.range (comap f)) = (RingHom.ker f).radical := by
  ext x
  rw [RingHom.ker_eq_comap_bot]; rw [← Ideal.comap_radical]; rw [Ideal.radical_eq_sInf]
  simp only [mem_vanishingIdeal, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    comap_asIdeal, Ideal.mem_comap, bot_le, true_and, Submodule.mem_sInf, Set.mem_ofPred_eq]
  exact ⟨fun H I hI => H ⟨I, hI⟩, fun H I => H I.1 I.2⟩

/--
lemma `closure_range_comap` / 引理 `closure_range_comap`

English:
lemma closure_range_comap
  proof: by
  rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_range_comap]; rw [zeroLocus_radical]

中文:
引理 closure_range_comap
  证明: by
  rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_range_comap]; rw [zeroLocus_radical]

Depends on / 依赖: vanishingIdeal_range_comap, zeroLocus_radical, zeroLocus_vanishingIdeal_eq_closure
-/
lemma closure_range_comap :
    closure (Set.range (comap f)) = zeroLocus (RingHom.ker f) := by
  rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [vanishingIdeal_range_comap]; rw [zeroLocus_radical]

/--
lemma `denseRange_comap_iff_ker_le_nilRadical` / 引理 `denseRange_comap_iff_ker_le_nilRadical`

English:
lemma denseRange_comap_iff_ker_le_nilRadical
  proof: by
  rw [denseRange_iff_closure_range]; rw [closure_range_comap]; rw [zeroLocus_eq_univ_iff]; rw [SetLike.coe_subset_coe]

@[stacks 00FL]

中文:
引理 denseRange_comap_iff_ker_le_nilRadical
  证明: by
  rw [denseRange_iff_closure_range]; rw [closure_range_comap]; rw [zeroLocus_eq_univ_iff]; rw [SetLike.coe_subset_coe]

@[stacks 00FL]

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, closure_range_comap, coe_subset_coe, denseRange_iff_closure_range, zeroLocus_eq_univ_iff
-/
lemma denseRange_comap_iff_ker_le_nilRadical :
    DenseRange (comap f) ↔ RingHom.ker f <= nilradical R := by
  rw [denseRange_iff_closure_range]; rw [closure_range_comap]; rw [zeroLocus_eq_univ_iff]; rw [SetLike.coe_subset_coe]

@[stacks 00FL]
/--
lemma `denseRange_comap_iff_minimalPrimes` / 引理 `denseRange_comap_iff_minimalPrimes`

English:
lemma denseRange_comap_iff_minimalPrimes
  proof: by
  constructor
  · intro H I hI
    have : I in (RingHom.ker f).minimalPrimes := by
      rw [denseRange_comap_iff_ker_le_nilRadical] at H
      simp only [Set.mem_ofPred, Ideal.IsMinimalPrime] at hI ⊢
      convert! hI using 2 with p
      exact ⟨fun h => ⟨h.1, bot_le⟩, fun h => ⟨h.1, H.trans (h.1.radical_le_iff.mpr bot_le)⟩⟩
    obtain ⟨p, hp, _, rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f (I := ⊥) I this
    exact ⟨⟨p, hp⟩, rfl⟩
  · intro H p
    obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
    exact ((le_iff_specializes ⟨q, hq.1.1⟩ p).mp hq').mem_closed isClosed_closure
      (subset_closure (H q hq))

中文:
引理 denseRange_comap_iff_minimalPrimes
  证明: by
  constructor
  · intro H I hI
    have : I in (RingHom.ker f).minimalPrimes := by
      rw [denseRange_comap_iff_ker_le_nilRadical] at H
      simp only [Set.mem_ofPred, Ideal.IsMinimalPrime] at hI ⊢
      convert! hI using 2 with p
      exact ⟨fun h => ⟨h.1, bot_le⟩, fun h => ⟨h.1, H.trans (h.1.radical_le_iff.mpr bot_le)⟩⟩
    obtain ⟨p, hp, _, rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f (I := ⊥) I this
    exact ⟨⟨p, hp⟩, rfl⟩
  · intro H p
    obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
    exact ((le_iff_specializes ⟨q, hq.1.1⟩ p).mp hq').mem_closed isClosed_closure
      (subset_closure (H q hq))

Depends on / 依赖: H.trans, Ideal.IsMinimalPrime, Ideal.exists_comap_eq_of_mem_minimalPrimes, Ideal.exists_minimalPrimes_le, IsMinimalPrime, RingHom, RingHom.ker, Set.mem_ofPred, asIdeal, bot_le, convert, denseRange_comap_iff_ker_le_nilRadical, exists_comap_eq_of_mem_minimalPrimes, exists_minimalPrimes_le, mem_ofPred, minimalPrimes, p.asIdeal, radical_le_iff, radical_le_iff.mpr
-/
lemma denseRange_comap_iff_minimalPrimes :
    DenseRange (comap f) ↔ forall I (h : I in minimalPrimes R), ⟨I, h.1.1⟩ in Set.range (comap f) := by
  constructor
  · intro H I hI
    have : I in (RingHom.ker f).minimalPrimes := by
      rw [denseRange_comap_iff_ker_le_nilRadical] at H
      simp only [Set.mem_ofPred, Ideal.IsMinimalPrime] at hI ⊢
      convert! hI using 2 with p
      exact ⟨fun h => ⟨h.1, bot_le⟩, fun h => ⟨h.1, H.trans (h.1.radical_le_iff.mpr bot_le)⟩⟩
    obtain ⟨p, hp, _, rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f (I := ⊥) I this
    exact ⟨⟨p, hp⟩, rfl⟩
  · intro H p
    obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
    exact ((le_iff_specializes ⟨q, hq.1.1⟩ p).mp hq').mem_closed isClosed_closure
      (subset_closure (H q hq))

end denseRange

variable (R) in
/--
Definition of `pointsEquivIrreducibleCloseds` / `pointsEquivIrreducibleCloseds` 的定义

English:
definition pointsEquivIrreducibleCloseds
  signature: :
  body: irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} :=
    (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans (le_iff_specializes p q).symm

中文:
定义 pointsEquivIrreducibleCloseds
  签名: :
  定义体: irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} :=
    (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans (le_iff_specializes p q).symm
-/
protected def pointsEquivIrreducibleCloseds :
    PrimeSpectrum R ≃o (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ where
  __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} :=
    (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans (le_iff_specializes p q).symm

/--
Definition of `zeroLocusEquivIrreducibleCloseds` / `zeroLocusEquivIrreducibleCloseds` 的定义

English:
definition zeroLocusEquivIrreducibleCloseds
  signature: (I : Set R)
  body: irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} := (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
    ((subtype_specializes_iff p q).trans (le_iff_specializes p.1 q.1).symm)

中文:
定义 zeroLocusEquivIrreducibleCloseds
  签名: (I : 集合 R)
  定义体: irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} := (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
    ((subtype_specializes_iff p q).trans (le_iff_specializes p.1 q.1).symm)
-/
protected def zeroLocusEquivIrreducibleCloseds (I : Set R) :
    zeroLocus I ≃o (TopologicalSpace.IrreducibleCloseds (zeroLocus I))ᵒᵈ where
  __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} := (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
    ((subtype_specializes_iff p q).trans (le_iff_specializes p.1 q.1).symm)

/--
lemma `stableUnderSpecialization_singleton` / 引理 `stableUnderSpecialization_singleton`

English:
lemma stableUnderSpecialization_singleton
  given: {x : PrimeSpectrum R}
  proof: by
  simp_rw [← isMax_iff, StableUnderSpecialization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h => (H a h).le, fun H a h => le_antisymm (H h) h⟩

中文:
引理 stableUnderSpecialization_singleton
  条件: {x : 素谱 R}
  证明: by
  simp_rw [← isMax_iff, StableUnderSpecialization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h => (H a h).le, fun H a h => le_antisymm (H h) h⟩

Depends on / 依赖: Set.mem_singleton_iff, StableUnderSpecialization, forall_comm, forall_eq, isMax_iff, le_antisymm, le_iff_specializes, mem_singleton_iff, simp_rw
-/
lemma stableUnderSpecialization_singleton {x : PrimeSpectrum R} :
    StableUnderSpecialization {x} ↔ x.asIdeal.IsMaximal := by
  simp_rw [← isMax_iff, StableUnderSpecialization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h => (H a h).le, fun H a h => le_antisymm (H h) h⟩

/--
lemma `stableUnderGeneralization_singleton` / 引理 `stableUnderGeneralization_singleton`

English:
lemma stableUnderGeneralization_singleton
  given: {x : PrimeSpectrum R}
  proof: by
  simp_rw [← isMin_iff, StableUnderGeneralization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h => (H a h).ge, fun H a h => le_antisymm h (H h)⟩

中文:
引理 stableUnderGeneralization_singleton
  条件: {x : 素谱 R}
  证明: by
  simp_rw [← isMin_iff, StableUnderGeneralization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h => (H a h).ge, fun H a h => le_antisymm h (H h)⟩

Depends on / 依赖: Set.mem_singleton_iff, StableUnderGeneralization, forall_comm, forall_eq, isMin_iff, le_antisymm, le_iff_specializes, mem_singleton_iff, simp_rw
-/
lemma stableUnderGeneralization_singleton {x : PrimeSpectrum R} :
    StableUnderGeneralization {x} ↔ x.asIdeal in minimalPrimes R := by
  simp_rw [← isMin_iff, StableUnderGeneralization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h => (H a h).ge, fun H a h => le_antisymm h (H h)⟩

/--
lemma `isCompact_isOpen_iff` / 引理 `isCompact_isOpen_iff`

English:
lemma isCompact_isOpen_iff
  given: {s : Set (PrimeSpectrum R)}
  proof: by
  rw [isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _
    isTopologicalBasis_basic_opens isCompact_basicOpen]
  simp only [basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂, ← zeroLocus_iUnion₂,
    Set.biUnion_of_singleton]
  exact ⟨fun ⟨s, hs, e⟩ => ⟨hs.toFinset, by simpa using e.symm⟩,
    fun ⟨s, e⟩ => ⟨s, s.finite_toSet, by simpa using e.symm⟩⟩

中文:
引理 isCompact_isOpen_iff
  条件: {s : 集合 (素谱 R)}
  证明: by
  rw [isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _
    isTopologicalBasis_basic_opens isCompact_basicOpen]
  simp only [basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂, ← zeroLocus_iUnion₂,
    Set.biUnion_of_singleton]
  exact ⟨fun ⟨s, hs, e⟩ => ⟨hs.toFinset, by simpa using e.symm⟩,
    fun ⟨s, e⟩ => ⟨s, s.finite_toSet, by simpa using e.symm⟩⟩

Depends on / 依赖: Set.biUnion_of_singleton, Set.compl_iInter, basicOpen_eq_zeroLocus_compl, biUnion_of_singleton, e.symm, finite_toSet, hs.toFinset, isCompact_basicOpen, isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis, isTopologicalBasis_basic_opens, s.finite_toSet, toFinset
-/
lemma isCompact_isOpen_iff {s : Set (PrimeSpectrum R)} :
    IsCompact s ∧ IsOpen s ↔ exists t : Finset R, (zeroLocus t)ᶜ = s := by
  rw [isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _
    isTopologicalBasis_basic_opens isCompact_basicOpen]
  simp only [basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂, ← zeroLocus_iUnion₂,
    Set.biUnion_of_singleton]
  exact ⟨fun ⟨s, hs, e⟩ => ⟨hs.toFinset, by simpa using e.symm⟩,
    fun ⟨s, e⟩ => ⟨s, s.finite_toSet, by simpa using e.symm⟩⟩

/--
lemma `isCompact_isOpen_iff_ideal` / 引理 `isCompact_isOpen_iff_ideal`

English:
lemma isCompact_isOpen_iff_ideal
  given: {s : Set (PrimeSpectrum R)}
  proof: by
  rw [isCompact_isOpen_iff]
  exact ⟨fun ⟨s, e⟩ => ⟨.span s, ⟨s, rfl⟩, by simpa using e⟩,
    fun ⟨I, ⟨s, hs⟩, e⟩ => ⟨s, by simpa [hs.symm] using e⟩⟩

中文:
引理 isCompact_isOpen_iff_ideal
  条件: {s : 集合 (素谱 R)}
  证明: by
  rw [isCompact_isOpen_iff]
  exact ⟨fun ⟨s, e⟩ => ⟨.span s, ⟨s, rfl⟩, by simpa using e⟩,
    fun ⟨I, ⟨s, hs⟩, e⟩ => ⟨s, by simpa [hs.symm] using e⟩⟩

Depends on / 依赖: hs.symm, isCompact_isOpen_iff
-/
lemma isCompact_isOpen_iff_ideal {s : Set (PrimeSpectrum R)} :
    IsCompact s ∧ IsOpen s ↔ exists I : Ideal R, I.FG ∧ (zeroLocus I)ᶜ = s := by
  rw [isCompact_isOpen_iff]
  exact ⟨fun ⟨s, e⟩ => ⟨.span s, ⟨s, rfl⟩, by simpa using e⟩,
    fun ⟨I, ⟨s, hs⟩, e⟩ => ⟨s, by simpa [hs.symm] using e⟩⟩

/--
lemma `basicOpen_eq_zeroLocus_of_mul_add` / 引理 `basicOpen_eq_zeroLocus_of_mul_add`

English:
lemma basicOpen_eq_zeroLocus_of_mul_add
  given: (e f : R) (mul : e * f = 0) (add : e + f = 1)
  proof: by
  ext p
  suffices e ∉ p.asIdeal ↔ f in p.asIdeal by simpa
  refine ⟨(p.2.mem_or_mem_of_mul_eq_zero mul).resolve_left, fun h₁ h₂ => p.2.1 ?_⟩
  rw [Ideal.eq_top_iff_one]; rw [← add]
  exact add_mem h₂ h₁

中文:
引理 basicOpen_eq_zeroLocus_of_mul_add
  条件: (e f : R) (mul : e * f = 0) (add : e + f = 1)
  证明: by
  ext p
  suffices e ∉ p.asIdeal ↔ f in p.asIdeal by simpa
  refine ⟨(p.2.mem_or_mem_of_mul_eq_zero mul).resolve_left, fun h₁ h₂ => p.2.1 ?_⟩
  rw [Ideal.eq_top_iff_one]; rw [← add]
  exact add_mem h₂ h₁

Depends on / 依赖: Ideal.eq_top_iff_one, add_mem, asIdeal, eq_top_iff_one, mem_or_mem_of_mul_eq_zero, p.asIdeal, resolve_left
-/
lemma basicOpen_eq_zeroLocus_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) :
    basicOpen e = zeroLocus {f} := by
  ext p
  suffices e ∉ p.asIdeal ↔ f in p.asIdeal by simpa
  refine ⟨(p.2.mem_or_mem_of_mul_eq_zero mul).resolve_left, fun h₁ h₂ => p.2.1 ?_⟩
  rw [Ideal.eq_top_iff_one]; rw [← add]
  exact add_mem h₂ h₁

/--
lemma `zeroLocus_eq_basicOpen_of_mul_add` / 引理 `zeroLocus_eq_basicOpen_of_mul_add`

English:
lemma zeroLocus_eq_basicOpen_of_mul_add
  given: (e f : R) (mul : e * f = 0) (add : e + f = 1)
  proof: by
  rw [basicOpen_eq_zeroLocus_of_mul_add f e] <;> simp only [mul, add, mul_comm, add_comm]

中文:
引理 zeroLocus_eq_basicOpen_of_mul_add
  条件: (e f : R) (mul : e * f = 0) (add : e + f = 1)
  证明: by
  rw [basicOpen_eq_zeroLocus_of_mul_add f e] <;> simp only [mul, add, mul_comm, add_comm]

Depends on / 依赖: add_comm, basicOpen_eq_zeroLocus_of_mul_add, mul_comm
-/
lemma zeroLocus_eq_basicOpen_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) :
    zeroLocus {e} = basicOpen f := by
  rw [basicOpen_eq_zeroLocus_of_mul_add f e] <;> simp only [mul, add, mul_comm, add_comm]

/--
lemma `isClopen_basicOpen_of_mul_add` / 引理 `isClopen_basicOpen_of_mul_add`

English:
lemma isClopen_basicOpen_of_mul_add
  given: (e f : R) (mul : e * f = 0) (add : e + f = 1)
  proof: ⟨basicOpen_eq_zeroLocus_of_mul_add e f mul add ▸ isClosed_zeroLocus _, (basicOpen e).2⟩

中文:
引理 isClopen_basicOpen_of_mul_add
  条件: (e f : R) (mul : e * f = 0) (add : e + f = 1)
  证明: ⟨basicOpen_eq_zeroLocus_of_mul_add e f mul add ▸ isClosed_zeroLocus _, (basicOpen e).2⟩

Depends on / 依赖: basicOpen, basicOpen_eq_zeroLocus_of_mul_add, isClosed_zeroLocus
-/
lemma isClopen_basicOpen_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) :
    IsClopen (basicOpen e : Set (PrimeSpectrum R)) :=
  ⟨basicOpen_eq_zeroLocus_of_mul_add e f mul add ▸ isClosed_zeroLocus _, (basicOpen e).2⟩

/--
lemma `basicOpen_injOn_isIdempotentElem` / 引理 `basicOpen_injOn_isIdempotentElem`

English:
lemma basicOpen_injOn_isIdempotentElem
  proof: fun x hx y hy eq => by
  by_contra! ne
  wlog ne' : x * y != x generalizing x y
  · apply this y hy x hx eq.symm ne.symm
    rwa [mul_comm, of_not_not ne']
have : x ∉ Ideal.span {y} := fun mem => ne' by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp mem
    rw [mul_assoc]; rw [hy]
  have ⟨p, prime, le, notMem⟩ := Ideal.exists_le_prime_notMem_of_isIdempotentElem _ x hx this
  exact ne_of_mem_of_not_mem' (a := ⟨p, prime⟩) notMem
    (not_not.mpr <| p.span_singleton_le_iff_mem.mp le) eq

中文:
引理 basicOpen_injOn_isIdempotentElem
  证明: fun x hx y hy eq => by
  by_contra! ne
  wlog ne' : x * y != x generalizing x y
  · apply this y hy x hx eq.symm ne.symm
    rwa [mul_comm, of_not_not ne']
have : x ∉ Ideal.span {y} := fun mem => ne' by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp mem
    rw [mul_assoc]; rw [hy]
  have ⟨p, prime, le, notMem⟩ := Ideal.exists_le_prime_notMem_of_isIdempotentElem _ x hx this
  exact ne_of_mem_of_not_mem' (a := ⟨p, prime⟩) notMem
    (not_not.mpr <| p.span_singleton_le_iff_mem.mp le) eq

Depends on / 依赖: Ideal.exists_le_prime_notMem_of_isIdempotentElem, Ideal.mem_span_singleton, Ideal.span, eq.symm, exists_le_prime_notMem_of_isIdempotentElem, generalizing, mem_span_singleton, mul_assoc, mul_comm, ne.symm, ne_of_mem_of_not_mem, notMem, not_not, not_not.mpr, of_not_not, p.span_singleton_le_iff_mem.mp, span_singleton_le_iff_mem
-/
lemma basicOpen_injOn_isIdempotentElem :
    {e : R | IsIdempotentElem e}.InjOn basicOpen := fun x hx y hy eq => by
  by_contra! ne
  wlog ne' : x * y != x generalizing x y
  · apply this y hy x hx eq.symm ne.symm
    rwa [mul_comm, of_not_not ne']
have : x ∉ Ideal.span {y} := fun mem => ne' by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp mem
    rw [mul_assoc]; rw [hy]
  have ⟨p, prime, le, notMem⟩ := Ideal.exists_le_prime_notMem_of_isIdempotentElem _ x hx this
  exact ne_of_mem_of_not_mem' (a := ⟨p, prime⟩) notMem
    (not_not.mpr <| p.span_singleton_le_iff_mem.mp le) eq

/--
lemma `exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen` / 引理 `exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen`

English:
lemma exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen
  statement: {s : Set (PrimeSpectrum R)}
  proof: by
  cases subsingleton_or_nontrivial R
  · refine ⟨0, 0, ?_, ?_, ?_, ?_⟩ <;> apply Subsingleton.elim
  obtain ⟨I, hI, hI'⟩ := isCompact_isOpen_iff_ideal.mp ⟨hs.1.isCompact, hs.2⟩
  obtain ⟨J, hJ, hJ'⟩ := isCompact_isOpen_iff_ideal.mp
    ⟨hs.2.isClosed_compl.isCompact, hs.1.isOpen_compl⟩
  simp only [compl_eq_iff_isCompl, ← eq_compl_iff_isCompl, compl_compl] at hI' hJ'
  have : I * J <= nilradical R := by
    refine Ideal.radical_le_radical_iff.mp (le_of_eq ?_)
    rw [← zeroLocus_eq_iff]; rw [Ideal.zero_eq_bot]; rw [zeroLocus_bot]; rw [zeroLocus_mul]; rw [hI']; rw [hJ']; rw [Set.compl_union_self]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg this (Submodule.FG.mul hI hJ)
  have hnz : n != 0 := by rintro rfl; simp at hn
  rw [mul_pow]; rw [Ideal.zero_eq_bot] at hn
  have : I ^ n ⊔ J ^ n = ⊤ := by
    rw [eq_top_iff]; rw [← Ideal.span_pow_eq_top (I union J : Set R) _ n]; rw [Ideal.span_le]; rw [Set.image_union]; rw [Set.union_subset_iff]
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_left (Ideal.pow_mem_pow hx n)
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_right (Ideal.pow_mem_pow hx n)
    · rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq, ← zeroLocus_empty_iff_eq_top,
        zeroLocus_sup, hI', hJ', Set.compl_inter_self]
  rw [Ideal.eq_top_iff_one]; rw [Submodule.mem_sup] at this
  obtain ⟨x, hx, y, hy, add⟩ := this
  have mul : x * y = 0 := hn (Ideal.mul_mem_mul hx hy)
  have : s = basicOpen x := by
    refine subset_antisymm ?_ ?_
    · rw [← hJ', basicOpen_eq_zeroLocus_of_mul_add _ _ mul add]
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hy)
    · rw [basicOpen_eq_zeroLocus_compl, Set.compl_subset_comm, ← hI']
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hx)
  refine ⟨x, y, mul, add, this, ?_⟩
  rw [this]; rw [basicOpen_eq_zeroLocus_of_mul_add _ _ mul add]; rw [basicOpen_eq_zeroLocus_compl]

中文:
引理 存在_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen
  结论: {s : 集合 (素谱 R)}
  证明: by
  cases subsingleton_or_nontrivial R
  · refine ⟨0, 0, ?_, ?_, ?_, ?_⟩ <;> apply Subsingleton.elim
  obtain ⟨I, hI, hI'⟩ := isCompact_isOpen_iff_ideal.mp ⟨hs.1.isCompact, hs.2⟩
  obtain ⟨J, hJ, hJ'⟩ := isCompact_isOpen_iff_ideal.mp
    ⟨hs.2.isClosed_compl.isCompact, hs.1.isOpen_compl⟩
  simp only [compl_eq_iff_isCompl, ← eq_compl_iff_isCompl, compl_compl] at hI' hJ'
  have : I * J <= nilradical R := by
    refine Ideal.radical_le_radical_iff.mp (le_of_eq ?_)
    rw [← zeroLocus_eq_iff]; rw [Ideal.zero_eq_bot]; rw [zeroLocus_bot]; rw [zeroLocus_mul]; rw [hI']; rw [hJ']; rw [Set.compl_union_self]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg this (Submodule.FG.mul hI hJ)
  have hnz : n != 0 := by rintro rfl; simp at hn
  rw [mul_pow]; rw [Ideal.zero_eq_bot] at hn
  have : I ^ n ⊔ J ^ n = ⊤ := by
    rw [eq_top_iff]; rw [← Ideal.span_pow_eq_top (I union J : Set R) _ n]; rw [Ideal.span_le]; rw [Set.image_union]; rw [Set.union_subset_iff]
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_left (Ideal.pow_mem_pow hx n)
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_right (Ideal.pow_mem_pow hx n)
    · rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq, ← zeroLocus_empty_iff_eq_top,
        zeroLocus_sup, hI', hJ', Set.compl_inter_self]
  rw [Ideal.eq_top_iff_one]; rw [Submodule.mem_sup] at this
  obtain ⟨x, hx, y, hy, add⟩ := this
  have mul : x * y = 0 := hn (Ideal.mul_mem_mul hx hy)
  have : s = basicOpen x := by
    refine subset_antisymm ?_ ?_
    · rw [← hJ', basicOpen_eq_zeroLocus_of_mul_add _ _ mul add]
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hy)
    · rw [basicOpen_eq_zeroLocus_compl, Set.compl_subset_comm, ← hI']
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hx)
  refine ⟨x, y, mul, add, this, ?_⟩
  rw [this]; rw [basicOpen_eq_zeroLocus_of_mul_add _ _ mul add]; rw [basicOpen_eq_zeroLocus_compl]

Depends on / 依赖: Ideal.radical_le_radical_iff.mp, Ideal.zero_eq_bot, Subsingleton, Subsingleton.elim, compl_compl, compl_eq_iff_isCompl, eq_compl_iff_isCompl, isClosed_compl, isClosed_compl.isCompact, isCompact, isCompact_isOpen_iff_ideal, isCompact_isOpen_iff_ideal.mp, isOpen_compl, le_of_eq, nilradical, radical_le_radical_iff, subsingleton_or_nontrivial, zeroLocus_eq_iff, zero_eq_bot
-/
lemma exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
    (hs : IsClopen s) : exists e f : R, e * f = 0 ∧ e + f = 1 ∧ s = basicOpen e ∧ sᶜ = basicOpen f := by
  cases subsingleton_or_nontrivial R
  · refine ⟨0, 0, ?_, ?_, ?_, ?_⟩ <;> apply Subsingleton.elim
  obtain ⟨I, hI, hI'⟩ := isCompact_isOpen_iff_ideal.mp ⟨hs.1.isCompact, hs.2⟩
  obtain ⟨J, hJ, hJ'⟩ := isCompact_isOpen_iff_ideal.mp
    ⟨hs.2.isClosed_compl.isCompact, hs.1.isOpen_compl⟩
  simp only [compl_eq_iff_isCompl, ← eq_compl_iff_isCompl, compl_compl] at hI' hJ'
  have : I * J <= nilradical R := by
    refine Ideal.radical_le_radical_iff.mp (le_of_eq ?_)
    rw [← zeroLocus_eq_iff]; rw [Ideal.zero_eq_bot]; rw [zeroLocus_bot]; rw [zeroLocus_mul]; rw [hI']; rw [hJ']; rw [Set.compl_union_self]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg this (Submodule.FG.mul hI hJ)
  have hnz : n != 0 := by rintro rfl; simp at hn
  rw [mul_pow]; rw [Ideal.zero_eq_bot] at hn
  have : I ^ n ⊔ J ^ n = ⊤ := by
    rw [eq_top_iff]; rw [← Ideal.span_pow_eq_top (I union J : Set R) _ n]; rw [Ideal.span_le]; rw [Set.image_union]; rw [Set.union_subset_iff]
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_left (Ideal.pow_mem_pow hx n)
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_right (Ideal.pow_mem_pow hx n)
    · rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq, ← zeroLocus_empty_iff_eq_top,
        zeroLocus_sup, hI', hJ', Set.compl_inter_self]
  rw [Ideal.eq_top_iff_one]; rw [Submodule.mem_sup] at this
  obtain ⟨x, hx, y, hy, add⟩ := this
  have mul : x * y = 0 := hn (Ideal.mul_mem_mul hx hy)
  have : s = basicOpen x := by
    refine subset_antisymm ?_ ?_
    · rw [← hJ', basicOpen_eq_zeroLocus_of_mul_add _ _ mul add]
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hy)
    · rw [basicOpen_eq_zeroLocus_compl, Set.compl_subset_comm, ← hI']
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hx)
  refine ⟨x, y, mul, add, this, ?_⟩
  rw [this]; rw [basicOpen_eq_zeroLocus_of_mul_add _ _ mul add]; rw [basicOpen_eq_zeroLocus_compl]

/--
lemma `exists_idempotent_basicOpen_eq_of_isClopen` / 引理 `exists_idempotent_basicOpen_eq_of_isClopen`

English:
lemma exists_idempotent_basicOpen_eq_of_isClopen
  statement: {s : Set (PrimeSpectrum R)}
  proof: have ⟨e, _, mul, add, eq, _⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen hs
  ⟨e, (IsIdempotentElem.of_mul_add mul add).1, eq⟩

@[stacks 00EE]

中文:
引理 存在_idempotent_basicOpen_eq_of_isClopen
  结论: {s : 集合 (素谱 R)}
  证明: have ⟨e, _, mul, add, eq, _⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen hs
  ⟨e, (IsIdempotentElem.of_mul_add mul add).1, eq⟩

@[stacks 00EE]

Depends on / 依赖: IsIdempotentElem, IsIdempotentElem.of_mul_add, exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen, of_mul_add
-/
lemma exists_idempotent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
    (hs : IsClopen s) : exists e : R, IsIdempotentElem e ∧ s = basicOpen e :=
  have ⟨e, _, mul, add, eq, _⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen hs
  ⟨e, (IsIdempotentElem.of_mul_add mul add).1, eq⟩

@[stacks 00EE]
/--
lemma `existsUnique_idempotent_basicOpen_eq_of_isClopen` / 引理 `existsUnique_idempotent_basicOpen_eq_of_isClopen`

English:
lemma existsUnique_idempotent_basicOpen_eq_of_isClopen
  statement: {s : Set (PrimeSpectrum R)}
  proof: by
  refine existsUnique_of_exists_of_unique (exists_idempotent_basicOpen_eq_of_isClopen hs) ?_
  rintro x y ⟨hx, rfl⟩ ⟨hy, eq⟩
  exact basicOpen_injOn_isIdempotentElem hx hy (SetLike.ext' eq)

中文:
引理 存在Unique_idempotent_basicOpen_eq_of_isClopen
  结论: {s : 集合 (素谱 R)}
  证明: by
  refine existsUnique_of_exists_of_unique (exists_idempotent_basicOpen_eq_of_isClopen hs) ?_
  rintro x y ⟨hx, rfl⟩ ⟨hy, eq⟩
  exact basicOpen_injOn_isIdempotentElem hx hy (SetLike.ext' eq)

Depends on / 依赖: SetLike, SetLike.ext, basicOpen_injOn_isIdempotentElem, existsUnique_of_exists_of_unique, exists_idempotent_basicOpen_eq_of_isClopen
-/
lemma existsUnique_idempotent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
    (hs : IsClopen s) : exists! e : R, IsIdempotentElem e ∧ s = basicOpen e := by
  refine existsUnique_of_exists_of_unique (exists_idempotent_basicOpen_eq_of_isClopen hs) ?_
  rintro x y ⟨hx, rfl⟩ ⟨hy, eq⟩
  exact basicOpen_injOn_isIdempotentElem hx hy (SetLike.ext' eq)

open TopologicalSpace.Opens in
/--
lemma `isClopen_iff_mul_add` / 引理 `isClopen_iff_mul_add`

English:
lemma isClopen_iff_mul_add
  given: {s : Set (PrimeSpectrum R)}
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · have ⟨e, f, h⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen h
    exact ⟨e, f, by simp only [h, and_self]⟩
  rintro ⟨e, f, mul, add, rfl⟩
  exact isClopen_basicOpen_of_mul_add e f mul add

中文:
引理 isClopen_iff_mul_add
  条件: {s : 集合 (素谱 R)}
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · have ⟨e, f, h⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen h
    exact ⟨e, f, by simp only [h, and_self]⟩
  rintro ⟨e, f, mul, add, rfl⟩
  exact isClopen_basicOpen_of_mul_add e f mul add

Depends on / 依赖: and_self, exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen, isClopen_basicOpen_of_mul_add
-/
lemma isClopen_iff_mul_add {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ exists e f : R, e * f = 0 ∧ e + f = 1 ∧ s = basicOpen e := by
  refine ⟨fun h => ?_, ?_⟩
  · have ⟨e, f, h⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen h
    exact ⟨e, f, by simp only [h, and_self]⟩
  rintro ⟨e, f, mul, add, rfl⟩
  exact isClopen_basicOpen_of_mul_add e f mul add

/--
lemma `isClopen_iff_mul_add_zeroLocus` / 引理 `isClopen_iff_mul_add_zeroLocus`

English:
lemma isClopen_iff_mul_add_zeroLocus
  given: {s : Set (PrimeSpectrum R)}
  proof: by
  rw [isClopen_iff_mul_add]; rw [exists_comm]
  refine exists₂_congr fun e f => ?_
  rw [mul_comm]; rw [add_comm]; rw [← and_assoc]; rw [← and_assoc]; rw [and_congr_right]
  intro ⟨mul, add⟩
  rw [zeroLocus_eq_basicOpen_of_mul_add e f mul add]

中文:
引理 isClopen_iff_mul_add_zeroLocus
  条件: {s : 集合 (素谱 R)}
  证明: by
  rw [isClopen_iff_mul_add]; rw [exists_comm]
  refine exists₂_congr fun e f => ?_
  rw [mul_comm]; rw [add_comm]; rw [← and_assoc]; rw [← and_assoc]; rw [and_congr_right]
  intro ⟨mul, add⟩
  rw [zeroLocus_eq_basicOpen_of_mul_add e f mul add]

Depends on / 依赖: add_comm, and_assoc, and_congr_right, exists_comm, isClopen_iff_mul_add, mul_comm, zeroLocus_eq_basicOpen_of_mul_add
-/
lemma isClopen_iff_mul_add_zeroLocus {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ exists e f : R, e * f = 0 ∧ e + f = 1 ∧ s = zeroLocus {e} := by
  rw [isClopen_iff_mul_add]; rw [exists_comm]
  refine exists₂_congr fun e f => ?_
  rw [mul_comm]; rw [add_comm]; rw [← and_assoc]; rw [← and_assoc]; rw [and_congr_right]
  intro ⟨mul, add⟩
  rw [zeroLocus_eq_basicOpen_of_mul_add e f mul add]

open TopologicalSpace (Clopens)

/--
Definition of `mulZeroAddOneEquivClopens` / `mulZeroAddOneEquivClopens` 的定义

English:
definition mulZeroAddOneEquivClopens
  signature: :
  body: .ofBijective
(fun e => ⟨basicOpen e.1.1, isClopen_iff_mul_add.mpr ⟨_, _, e.2.1, e.2.2, rfl⟩⟩) by
      refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ eq => mul_eq_zero_add_eq_one_ext_left ?_, fun s => ?_⟩
      · exact basicOpen_injOn_isIdempotentElem (IsIdempotentElem.of_mul_add hx.1 hx.2).1
(IsIdempotentElem.of_mul_add hy.1 hy.2).1 SetLike.ext' (congr_arg (·.1) eq)
      · have ⟨e, f, mul, add, eq⟩ := isClopen_iff_mul_add.mp s.2
        exact ⟨⟨(e, f), mul, add⟩, SetLike.ext' eq.symm⟩
  map_rel_iff' {a b} := show basicOpen _ <= basicOpen _ ↔ _ by
    rw [← inf_eq_left]; rw [← basicOpen_mul]
    refine ⟨fun h => ?_, (by rw [·])⟩
    rw [← inf_eq_left]
    have := (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1
    exact mul_eq_zero_add_eq_one_ext_left (basicOpen_injOn_isIdempotentElem
      (this.mul (IsIdempotentElem.of_mul_add b.2.1 b.2.2).1) this h)

中文:
定义 mulZeroAddOneEquivClopens
  签名: :
  定义体: .ofBijective
(fun e => ⟨basicOpen e.1.1, isClopen_iff_mul_add.mpr ⟨_, _, e.2.1, e.2.2, rfl⟩⟩) by
      refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ eq => mul_eq_zero_add_eq_one_ext_left ?_, fun s => ?_⟩
      · exact basicOpen_injOn_isIdempotentElem (IsIdempotentElem.of_mul_add hx.1 hx.2).1
(IsIdempotentElem.of_mul_add hy.1 hy.2).1 SetLike.ext' (congr_arg (·.1) eq)
      · have ⟨e, f, mul, add, eq⟩ := isClopen_iff_mul_add.mp s.2
        exact ⟨⟨(e, f), mul, add⟩, SetLike.ext' eq.symm⟩
  map_rel_iff' {a b} := show basicOpen _ <= basicOpen _ ↔ _ by
    rw [← inf_eq_left]; rw [← basicOpen_mul]
    refine ⟨fun h => ?_, (by rw [·])⟩
    rw [← inf_eq_left]
    have := (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1
    exact mul_eq_zero_add_eq_one_ext_left (basicOpen_injOn_isIdempotentElem
      (this.mul (IsIdempotentElem.of_mul_add b.2.1 b.2.2).1) this h)

Depends on / 依赖: ofBijective
-/
def mulZeroAddOneEquivClopens :
    {e : R × R // e.1 * e.2 = 0 ∧ e.1 + e.2 = 1} ≃o Clopens (PrimeSpectrum R) where
  toEquiv := .ofBijective
(fun e => ⟨basicOpen e.1.1, isClopen_iff_mul_add.mpr ⟨_, _, e.2.1, e.2.2, rfl⟩⟩) by
      refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ eq => mul_eq_zero_add_eq_one_ext_left ?_, fun s => ?_⟩
      · exact basicOpen_injOn_isIdempotentElem (IsIdempotentElem.of_mul_add hx.1 hx.2).1
(IsIdempotentElem.of_mul_add hy.1 hy.2).1 SetLike.ext' (congr_arg (·.1) eq)
      · have ⟨e, f, mul, add, eq⟩ := isClopen_iff_mul_add.mp s.2
        exact ⟨⟨(e, f), mul, add⟩, SetLike.ext' eq.symm⟩
  map_rel_iff' {a b} := show basicOpen _ <= basicOpen _ ↔ _ by
    rw [← inf_eq_left]; rw [← basicOpen_mul]
    refine ⟨fun h => ?_, (by rw [·])⟩
    rw [← inf_eq_left]
    have := (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1
    exact mul_eq_zero_add_eq_one_ext_left (basicOpen_injOn_isIdempotentElem
      (this.mul (IsIdempotentElem.of_mul_add b.2.1 b.2.2).1) this h)

/--
lemma `isRetrocompact_zeroLocus_compl` / 引理 `isRetrocompact_zeroLocus_compl`

English:
lemma isRetrocompact_zeroLocus_compl
  given: {s : Set R} (hs : s.Finite)
  proof: (QuasiSeparatedSpace.isRetrocompact_iff_isCompact (isClosed_zeroLocus _).isOpen_compl).mpr
    (isCompact_isOpen_iff.mpr ⟨hs.toFinset, by simp⟩).1

中文:
引理 isRetrocompact_zeroLocus_compl
  条件: {s : 集合 R} (hs : s.有限)
  证明: (QuasiSeparatedSpace.isRetrocompact_iff_isCompact (isClosed_zeroLocus _).isOpen_compl).mpr
    (isCompact_isOpen_iff.mpr ⟨hs.toFinset, by simp⟩).1

Depends on / 依赖: QuasiSeparatedSpace, QuasiSeparatedSpace.isRetrocompact_iff_isCompact, hs.toFinset, isClosed_zeroLocus, isCompact_isOpen_iff, isCompact_isOpen_iff.mpr, isOpen_compl, isRetrocompact_iff_isCompact, toFinset
-/
lemma isRetrocompact_zeroLocus_compl {s : Set R} (hs : s.Finite) :
    IsRetrocompact (zeroLocus s)ᶜ :=
  (QuasiSeparatedSpace.isRetrocompact_iff_isCompact (isClosed_zeroLocus _).isOpen_compl).mpr
    (isCompact_isOpen_iff.mpr ⟨hs.toFinset, by simp⟩).1

/--
lemma `isRetrocompact_zeroLocus_compl_of_fg` / 引理 `isRetrocompact_zeroLocus_compl_of_fg`

English:
lemma isRetrocompact_zeroLocus_compl_of_fg
  given: {I : Ideal R} (hI : I.FG)
  proof: by
  obtain ⟨s, rfl⟩ := hI
  rw [zeroLocus_span]
  exact isRetrocompact_zeroLocus_compl s.finite_toSet

中文:
引理 isRetrocompact_zeroLocus_compl_of_fg
  条件: {I : 理想 R} (hI : I.FG)
  证明: by
  obtain ⟨s, rfl⟩ := hI
  rw [zeroLocus_span]
  exact isRetrocompact_zeroLocus_compl s.finite_toSet

Depends on / 依赖: finite_toSet, isRetrocompact_zeroLocus_compl, s.finite_toSet, zeroLocus_span
-/
lemma isRetrocompact_zeroLocus_compl_of_fg {I : Ideal R} (hI : I.FG) :
    IsRetrocompact (zeroLocus (I : Set R))ᶜ := by
  obtain ⟨s, rfl⟩ := hI
  rw [zeroLocus_span]
  exact isRetrocompact_zeroLocus_compl s.finite_toSet

/--
lemma `isRetrocompact_basicOpen` / 引理 `isRetrocompact_basicOpen`

English:
lemma isRetrocompact_basicOpen
  given: {f : R}
  proof: by
  simpa using isRetrocompact_zeroLocus_compl (Set.finite_singleton f)

中文:
引理 isRetrocompact_basicOpen
  条件: {f : R}
  证明: by
  simpa using isRetrocompact_zeroLocus_compl (Set.finite_singleton f)

Depends on / 依赖: Set.finite_singleton, finite_singleton, isRetrocompact_zeroLocus_compl
-/
lemma isRetrocompact_basicOpen {f : R} :
    IsRetrocompact (basicOpen f : Set (PrimeSpectrum R)) := by
  simpa using isRetrocompact_zeroLocus_compl (Set.finite_singleton f)

/--
lemma `isConstructible_basicOpen` / 引理 `isConstructible_basicOpen`

English:
lemma isConstructible_basicOpen
  given: {f : R}
  proof: isRetrocompact_basicOpen.isConstructible (basicOpen f).2

中文:
引理 isConstructible_basicOpen
  条件: {f : R}
  证明: isRetrocompact_basicOpen.isConstructible (basicOpen f).2

Depends on / 依赖: basicOpen, isConstructible, isRetrocompact_basicOpen, isRetrocompact_basicOpen.isConstructible
-/
lemma isConstructible_basicOpen {f : R} :
    IsConstructible (basicOpen f : Set (PrimeSpectrum R)) :=
  isRetrocompact_basicOpen.isConstructible (basicOpen f).2

section IsIntegral

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)

/--
theorem `isClosedMap_comap_of_isIntegral` / 定理 `isClosedMap_comap_of_isIntegral`

English:
theorem isClosedMap_comap_of_isIntegral
  given: (hf : f.IsIntegral)
  proof: by
  refine fun s hs => isClosed_image_of_stableUnderSpecialization _ _ hs ?_
  rintro _ y e ⟨x, hx, rfl⟩
  algebraize [f]
  obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_ideal_over_prime_of_isIntegral y.asIdeal x.asIdeal
    ((le_iff_specializes _ _).mpr e)
  refine ⟨⟨q, hq₂⟩, ((le_iff_specializes _ ⟨q, hq₂⟩).mp hq₁).mem_closed hs hx,
    PrimeSpectrum.ext hq₃⟩

中文:
定理 isClosedMap_comap_of_is整数egral
  条件: (hf : f.是整)
  证明: by
  refine fun s hs => isClosed_image_of_stableUnderSpecialization _ _ hs ?_
  rintro _ y e ⟨x, hx, rfl⟩
  algebraize [f]
  obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_ideal_over_prime_of_isIntegral y.asIdeal x.asIdeal
    ((le_iff_specializes _ _).mpr e)
  refine ⟨⟨q, hq₂⟩, ((le_iff_specializes _ ⟨q, hq₂⟩).mp hq₁).mem_closed hs hx,
    PrimeSpectrum.ext hq₃⟩

Depends on / 依赖: Ideal.exists_ideal_over_prime_of_isIntegral, PrimeSpectrum, PrimeSpectrum.ext, algebraize, asIdeal, exists_ideal_over_prime_of_isIntegral, isClosed_image_of_stableUnderSpecialization, le_iff_specializes, mem_closed, x.asIdeal, y.asIdeal
-/
theorem isClosedMap_comap_of_isIntegral (hf : f.IsIntegral) :
    IsClosedMap (comap f) := by
  refine fun s hs => isClosed_image_of_stableUnderSpecialization _ _ hs ?_
  rintro _ y e ⟨x, hx, rfl⟩
  algebraize [f]
  obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_ideal_over_prime_of_isIntegral y.asIdeal x.asIdeal
    ((le_iff_specializes _ _).mpr e)
  refine ⟨⟨q, hq₂⟩, ((le_iff_specializes _ ⟨q, hq₂⟩).mp hq₁).mem_closed hs hx,
    PrimeSpectrum.ext hq₃⟩

/--
theorem `isClosed_comap_singleton_of_isIntegral` / 定理 `isClosed_comap_singleton_of_isIntegral`

English:
theorem isClosed_comap_singleton_of_isIntegral
  statement: (hf : f.IsIntegral)
  proof: by
  simpa using isClosedMap_comap_of_isIntegral f hf _ hx

中文:
定理 isClosed_comap_singleton_of_is整数egral
  结论: (hf : f.是整)
  证明: by
  simpa using isClosedMap_comap_of_isIntegral f hf _ hx

Depends on / 依赖: isClosedMap_comap_of_isIntegral
-/
theorem isClosed_comap_singleton_of_isIntegral (hf : f.IsIntegral)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) := by
  simpa using isClosedMap_comap_of_isIntegral f hf _ hx

/--
lemma `closure_image_comap_zeroLocus` / 引理 `closure_image_comap_zeroLocus`

English:
lemma closure_image_comap_zeroLocus
  given: (I : Ideal S)
  proof: by
  apply subset_antisymm
  · rw [(isClosed_zeroLocus _).closure_subset_iff, Set.image_subset_iff, preimage_comap_zeroLocus]
    exact zeroLocus_anti_mono (Set.image_preimage_subset _ _)
  · rintro x (hx : I.comap f <= x.asIdeal)
    obtain ⟨q, hq₁, hq₂⟩ := Ideal.exists_minimalPrimes_le hx
    obtain ⟨p', hp', hp'', rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f _ hq₁
    let p'' : PrimeSpectrum S := ⟨p', hp'⟩
    apply isClosed_closure.stableUnderSpecialization ((le_iff_specializes
      (comap f ⟨p', hp'⟩) x).mp hq₂) (subset_closure (by exact ⟨_, hp'', rfl⟩))

中文:
引理 closure_image_comap_zeroLocus
  条件: (I : 理想 S)
  证明: by
  apply subset_antisymm
  · rw [(isClosed_zeroLocus _).closure_subset_iff, Set.image_subset_iff, preimage_comap_zeroLocus]
    exact zeroLocus_anti_mono (Set.image_preimage_subset _ _)
  · rintro x (hx : I.comap f <= x.asIdeal)
    obtain ⟨q, hq₁, hq₂⟩ := Ideal.exists_minimalPrimes_le hx
    obtain ⟨p', hp', hp'', rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f _ hq₁
    let p'' : PrimeSpectrum S := ⟨p', hp'⟩
    apply isClosed_closure.stableUnderSpecialization ((le_iff_specializes
      (comap f ⟨p', hp'⟩) x).mp hq₂) (subset_closure (by exact ⟨_, hp'', rfl⟩))

Depends on / 依赖: I.comap, Ideal.exists_comap_eq_of_mem_minimalPrimes, Ideal.exists_minimalPrimes_le, PrimeSpectrum, Set.image_preimage_subset, Set.image_subset_iff, asIdeal, closure_subset_iff, exists_comap_eq_of_mem_minimalPrimes, exists_minimalPrimes_le, image_preimage_subset, image_subset_iff, isClosed_closure, isClosed_closure.stableUnderSpecialization, isClosed_zeroLocus, le_iff_specializes, preimage_comap_zeroLocus, stableUnderSpecialization, subset_antisymm, x.asIdeal
-/
lemma closure_image_comap_zeroLocus (I : Ideal S) :
    closure (comap f '' zeroLocus I) = zeroLocus (I.comap f) := by
  apply subset_antisymm
  · rw [(isClosed_zeroLocus _).closure_subset_iff, Set.image_subset_iff, preimage_comap_zeroLocus]
    exact zeroLocus_anti_mono (Set.image_preimage_subset _ _)
  · rintro x (hx : I.comap f <= x.asIdeal)
    obtain ⟨q, hq₁, hq₂⟩ := Ideal.exists_minimalPrimes_le hx
    obtain ⟨p', hp', hp'', rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f _ hq₁
    let p'' : PrimeSpectrum S := ⟨p', hp'⟩
    apply isClosed_closure.stableUnderSpecialization ((le_iff_specializes
      (comap f ⟨p', hp'⟩) x).mp hq₂) (subset_closure (by exact ⟨_, hp'', rfl⟩))

/--
lemma `isIntegral_of_isClosedMap_comap_mapRingHom` / 引理 `isIntegral_of_isClosedMap_comap_mapRingHom`

English:
lemma isIntegral_of_isClosedMap_comap_mapRingHom
  given: (h : IsClosedMap (comap (mapRingHom f)))
  proof: by
  algebraize [f]
  suffices Algebra.IsIntegral R S by rwa [Algebra.isIntegral_def] at this
  nontriviality R
  nontriviality S
  constructor
  intro r
  let p : S[X] := C r * X - 1
  have : (1 : R[X]) in Ideal.span {X} ⊔ (Ideal.span {p}).comap (mapRingHom f) := by
    have H := h _ (isClosed_zeroLocus {p})
    rw [← zeroLocus_span]; rw [← closure_eq_iff_isClosed]; rw [closure_image_comap_zeroLocus] at H
    rw [← Ideal.eq_top_iff_one]; rw [sup_comm]; rw [← zeroLocus_empty_iff_eq_top]; rw [zeroLocus_sup]; rw [H]
    suffices forall (a : PrimeSpectrum S[X]), p in a.asIdeal -> X ∉ a.asIdeal by
      simpa [Set.eq_empty_iff_forall_notMem]
    intro q hpq hXq
    have : 1 in q.asIdeal := by simpa [p] using! (sub_mem (q.asIdeal.mul_mem_left (C r) hXq) hpq)
    exact q.2.ne_top (q.asIdeal.eq_top_iff_one.mpr this)
  obtain ⟨a, b, hb, e⟩ := Ideal.mem_span_singleton_sup.mp this
  obtain ⟨c, hc : b.map (algebraMap R S) = _⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨b.reverse * X ^ (1 + c.natDegree), ?_, ?_⟩
  · refine Monic.mul ?_ (by simp)
    have h : b.coeff 0 = 1 := by simpa using! congr(($e).coeff 0)
    have : b.natTrailingDegree = 0 := by simp [h]
    rw [Monic.def]; rw [reverse_leadingCoeff]; rw [trailingCoeff]; rw [this]; rw [h]
  · have : p.natDegree <= 1 := by simpa using! natDegree_linear_le (a := r) (b := -1)
    rw [eval₂_eq_eval_map]; rw [reverse]; rw [Polynomial.map_mul]; rw [← reflect_map]; rw [Polynomial.map_pow]; rw [map_X]; rw [← revAt_zero (1 + _)]; rw [← reflect_monomial]; rw [← reflect_mul _ _ natDegree_map_le (by simp)]; rw [pow_zero]; rw [mul_one]; rw [hc]; rw [← add_assoc]; rw [reflect_mul _ _ (this.trans (by simp)) le_rfl]; rw [eval_mul]; rw [reflect_sub]; rw [reflect_mul _ _ (by simp) (by simp)]
    simp [← pow_succ']

中文:
引理 is整数egral_of_isClosedMap_comap_mapRingHom
  条件: (h : 是闭映射 (comap (mapRingHom f)))
  证明: by
  algebraize [f]
  suffices Algebra.IsIntegral R S by rwa [Algebra.isIntegral_def] at this
  nontriviality R
  nontriviality S
  constructor
  intro r
  let p : S[X] := C r * X - 1
  have : (1 : R[X]) in Ideal.span {X} ⊔ (Ideal.span {p}).comap (mapRingHom f) := by
    have H := h _ (isClosed_zeroLocus {p})
    rw [← zeroLocus_span]; rw [← closure_eq_iff_isClosed]; rw [closure_image_comap_zeroLocus] at H
    rw [← Ideal.eq_top_iff_one]; rw [sup_comm]; rw [← zeroLocus_empty_iff_eq_top]; rw [zeroLocus_sup]; rw [H]
    suffices forall (a : PrimeSpectrum S[X]), p in a.asIdeal -> X ∉ a.asIdeal by
      simpa [Set.eq_empty_iff_forall_notMem]
    intro q hpq hXq
    have : 1 in q.asIdeal := by simpa [p] using! (sub_mem (q.asIdeal.mul_mem_left (C r) hXq) hpq)
    exact q.2.ne_top (q.asIdeal.eq_top_iff_one.mpr this)
  obtain ⟨a, b, hb, e⟩ := Ideal.mem_span_singleton_sup.mp this
  obtain ⟨c, hc : b.map (algebraMap R S) = _⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨b.reverse * X ^ (1 + c.natDegree), ?_, ?_⟩
  · refine Monic.mul ?_ (by simp)
    have h : b.coeff 0 = 1 := by simpa using! congr(($e).coeff 0)
    have : b.natTrailingDegree = 0 := by simp [h]
    rw [Monic.def]; rw [reverse_leadingCoeff]; rw [trailingCoeff]; rw [this]; rw [h]
  · have : p.natDegree <= 1 := by simpa using! natDegree_linear_le (a := r) (b := -1)
    rw [eval₂_eq_eval_map]; rw [reverse]; rw [Polynomial.map_mul]; rw [← reflect_map]; rw [Polynomial.map_pow]; rw [map_X]; rw [← revAt_zero (1 + _)]; rw [← reflect_monomial]; rw [← reflect_mul _ _ natDegree_map_le (by simp)]; rw [pow_zero]; rw [mul_one]; rw [hc]; rw [← add_assoc]; rw [reflect_mul _ _ (this.trans (by simp)) le_rfl]; rw [eval_mul]; rw [reflect_sub]; rw [reflect_mul _ _ (by simp) (by simp)]
    simp [← pow_succ']

Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.isIntegral_def, Ideal.eq_top_iff_one, Ideal.span, IsIntegral, algebraize, closure_eq_iff_isClosed, closure_image_comap_zeroLocus, eq_top_iff_one, isClosed_zeroLocus, isIntegral_def, mapRingHom, nontriviality, sup_comm, zeroLocus_empty_iff_eq_top, zeroLocus_span, zeroLocus_sup
-/
lemma isIntegral_of_isClosedMap_comap_mapRingHom (h : IsClosedMap (comap (mapRingHom f))) :
    f.IsIntegral := by
  algebraize [f]
  suffices Algebra.IsIntegral R S by rwa [Algebra.isIntegral_def] at this
  nontriviality R
  nontriviality S
  constructor
  intro r
  let p : S[X] := C r * X - 1
  have : (1 : R[X]) in Ideal.span {X} ⊔ (Ideal.span {p}).comap (mapRingHom f) := by
    have H := h _ (isClosed_zeroLocus {p})
    rw [← zeroLocus_span]; rw [← closure_eq_iff_isClosed]; rw [closure_image_comap_zeroLocus] at H
    rw [← Ideal.eq_top_iff_one]; rw [sup_comm]; rw [← zeroLocus_empty_iff_eq_top]; rw [zeroLocus_sup]; rw [H]
    suffices forall (a : PrimeSpectrum S[X]), p in a.asIdeal -> X ∉ a.asIdeal by
      simpa [Set.eq_empty_iff_forall_notMem]
    intro q hpq hXq
    have : 1 in q.asIdeal := by simpa [p] using! (sub_mem (q.asIdeal.mul_mem_left (C r) hXq) hpq)
    exact q.2.ne_top (q.asIdeal.eq_top_iff_one.mpr this)
  obtain ⟨a, b, hb, e⟩ := Ideal.mem_span_singleton_sup.mp this
  obtain ⟨c, hc : b.map (algebraMap R S) = _⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨b.reverse * X ^ (1 + c.natDegree), ?_, ?_⟩
  · refine Monic.mul ?_ (by simp)
    have h : b.coeff 0 = 1 := by simpa using! congr(($e).coeff 0)
    have : b.natTrailingDegree = 0 := by simp [h]
    rw [Monic.def]; rw [reverse_leadingCoeff]; rw [trailingCoeff]; rw [this]; rw [h]
  · have : p.natDegree <= 1 := by simpa using! natDegree_linear_le (a := r) (b := -1)
    rw [eval₂_eq_eval_map]; rw [reverse]; rw [Polynomial.map_mul]; rw [← reflect_map]; rw [Polynomial.map_pow]; rw [map_X]; rw [← revAt_zero (1 + _)]; rw [← reflect_monomial]; rw [← reflect_mul _ _ natDegree_map_le (by simp)]; rw [pow_zero]; rw [mul_one]; rw [hc]; rw [← add_assoc]; rw [reflect_mul _ _ (this.trans (by simp)) le_rfl]; rw [eval_mul]; rw [reflect_sub]; rw [reflect_mul _ _ (by simp) (by simp)]
    simp [← pow_succ']

variable (R S) in
/--
lemma `_root_.Algebra.IsIntegral.comap_surjective` / 引理 `_root_.Algebra.IsIntegral.comap_surjective`

English:
lemma _root_.Algebra.IsIntegral.comap_surjective
  statement: [Algebra R S] [Algebra.IsIntegral R S]
  proof: by
  intro ⟨p, hp⟩
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, _, hQ, rfl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
    (by simp [Ideal.comap_bot_of_injective (algebraMap R S) hinj])
  exact ⟨⟨Q, hQ⟩, rfl⟩

中文:
引理 _root_.代数.是整.comap_surjective
  结论: [代数 R S] [代数.是整 R S]
  证明: by
  intro ⟨p, hp⟩
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, _, hQ, rfl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
    (by simp [Ideal.comap_bot_of_injective (algebraMap R S) hinj])
  exact ⟨⟨Q, hQ⟩, rfl⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Function, Function.Injective, Ideal.comap_bot_of_injective, Ideal.exists_ideal_over_prime_of_isIntegral, Injective, algebraMap, algebraMap_injective, comap_bot_of_injective, exists_ideal_over_prime_of_isIntegral
-/
lemma _root_.Algebra.IsIntegral.comap_surjective [Algebra R S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] :
    Function.Surjective (comap (algebraMap R S)) := by
  intro ⟨p, hp⟩
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, _, hQ, rfl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
    (by simp [Ideal.comap_bot_of_injective (algebraMap R S) hinj])
  exact ⟨⟨Q, hQ⟩, rfl⟩

/--
lemma `_root_.RingHom.IsIntegral.comap_surjective` / 引理 `_root_.RingHom.IsIntegral.comap_surjective`

English:
lemma _root_.RingHom.IsIntegral.comap_surjective
  statement: {f : R ->+* S} (hf : f.IsIntegral)
  proof: by
  algebraize [f]
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  exact Algebra.IsIntegral.comap_surjective _ _

中文:
引理 _root_.环态射.是整.comap_surjective
  结论: {f : R ->+* S} (hf : f.是整)
  证明: by
  algebraize [f]
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  exact Algebra.IsIntegral.comap_surjective _ _

Depends on / 依赖: Algebra, Algebra.IsIntegral.comap_surjective, FaithfulSMul, IsIntegral, algebraize, comap_surjective, faithfulSMul_iff_algebraMap_injective
-/
lemma _root_.RingHom.IsIntegral.comap_surjective {f : R ->+* S} (hf : f.IsIntegral)
    (hinj : Function.Injective f) : Function.Surjective (comap f) := by
  algebraize [f]
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  exact Algebra.IsIntegral.comap_surjective _ _

end IsIntegral

/-- Zero loci of minimal prime ideals over `I` are irreducible components in `zeroLocus I` and any
irreducible component is a zero locus of some minimal prime ideal. -/
@[stacks 00ES]
/--
Definition of `_root_.Ideal.minimalPrimes.equivIrreducibleComponents` / `_root_.Ideal.minimalPrimes.equivIrreducibleComponents` 的定义

English:
definition _root_.Ideal.minimalPrimes.equivIrreducibleComponents
  signature: (I : Ideal R)
  body: by
  let e : {p : Ideal R | p.IsPrime ∧ I <= p} ≃o zeroLocus (I : Set R) :=
    ⟨⟨fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun x => ⟨x.1.1, x.1.2, x.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩
  rw [irreducibleComponents_eq_maximals_closed]
  exact OrderIso.setOfPredMinimalIsoSetOfPredMaximal
    (e.trans ((PrimeSpectrum.zeroLocusEquivIrreducibleCloseds (I : Set R)).trans
    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (zeroLocus (I : Set R))).dual))

中文:
定义 _root_.理想.minimalPrimes.equivIrreducibleComponents
  签名: (I : 理想 R)
  定义体: by
  let e : {p : Ideal R | p.IsPrime ∧ I <= p} ≃o zeroLocus (I : Set R) :=
    ⟨⟨fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun x => ⟨x.1.1, x.1.2, x.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩
  rw [irreducibleComponents_eq_maximals_closed]
  exact OrderIso.setOfPredMinimalIsoSetOfPredMaximal
    (e.trans ((PrimeSpectrum.zeroLocusEquivIrreducibleCloseds (I : Set R)).trans
    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (zeroLocus (I : Set R))).dual))
-/
protected def _root_.Ideal.minimalPrimes.equivIrreducibleComponents (I : Ideal R) :
    I.minimalPrimes ≃o (irreducibleComponents <| (zeroLocus (I : Set R)))ᵒᵈ := by
  let e : {p : Ideal R | p.IsPrime ∧ I <= p} ≃o zeroLocus (I : Set R) :=
    ⟨⟨fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun x => ⟨x.1.1, x.1.2, x.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩
  rw [irreducibleComponents_eq_maximals_closed]
  exact OrderIso.setOfPredMinimalIsoSetOfPredMaximal
    (e.trans ((PrimeSpectrum.zeroLocusEquivIrreducibleCloseds (I : Set R)).trans
    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (zeroLocus (I : Set R))).dual))

variable (R)

/-- Zero loci of minimal prime ideals of `R` are irreducible components in `Spec R` and any
irreducible component is a zero locus of some minimal prime ideal. -/
@[stacks 00ES]
/--
Definition of `_root_.minimalPrimes.equivIrreducibleComponents` / `_root_.minimalPrimes.equivIrreducibleComponents` 的定义

English:
definition _root_.minimalPrimes.equivIrreducibleComponents
  signature: :
  body: by
  let e : {p : Ideal R | p.IsPrime ∧ ⊥ <= p} ≃o PrimeSpectrum R :=
    ⟨⟨fun x => ⟨x.1, x.2.1⟩, fun x => ⟨x.1, x.2, bot_le⟩, fun _ => rfl, fun _ => rfl⟩, Iff.rfl⟩
  rw [irreducibleComponents_eq_maximals_closed]
  exact OrderIso.setOfPredMinimalIsoSetOfPredMaximal
    (e.trans ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).trans
    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (PrimeSpectrum R)).dual))

中文:
定义 _root_.minimalPrimes.equivIrreducibleComponents
  签名: :
  定义体: by
  let e : {p : Ideal R | p.IsPrime ∧ ⊥ <= p} ≃o PrimeSpectrum R :=
    ⟨⟨fun x => ⟨x.1, x.2.1⟩, fun x => ⟨x.1, x.2, bot_le⟩, fun _ => rfl, fun _ => rfl⟩, Iff.rfl⟩
  rw [irreducibleComponents_eq_maximals_closed]
  exact OrderIso.setOfPredMinimalIsoSetOfPredMaximal
    (e.trans ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).trans
    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (PrimeSpectrum R)).dual))
-/
protected def _root_.minimalPrimes.equivIrreducibleComponents :
    minimalPrimes R ≃o (irreducibleComponents <| PrimeSpectrum R)ᵒᵈ := by
  let e : {p : Ideal R | p.IsPrime ∧ ⊥ <= p} ≃o PrimeSpectrum R :=
    ⟨⟨fun x => ⟨x.1, x.2.1⟩, fun x => ⟨x.1, x.2, bot_le⟩, fun _ => rfl, fun _ => rfl⟩, Iff.rfl⟩
  rw [irreducibleComponents_eq_maximals_closed]
  exact OrderIso.setOfPredMinimalIsoSetOfPredMaximal
    (e.trans ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).trans
    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (PrimeSpectrum R)).dual))

/--
lemma `vanishingIdeal_irreducibleComponents` / 引理 `vanishingIdeal_irreducibleComponents`

English:
lemma vanishingIdeal_irreducibleComponents
  proof: by
  rw [irreducibleComponents_eq_maximals_closed]; rw [minimalPrimes_eq_minimals]; rw [image_antitone_setOfPred_maximal (fun s t hs _ => (vanishingIdeal_anti_mono_iff hs.1).symm)]; rw [← funext (@Set.mem_ofPred_eq _ · Ideal.IsPrime)]; rw [← vanishingIdeal_isClosed_isIrreducible]
  rfl

中文:
引理 vanishingIdeal_irreducibleComponents
  证明: by
  rw [irreducibleComponents_eq_maximals_closed]; rw [minimalPrimes_eq_minimals]; rw [image_antitone_setOfPred_maximal (fun s t hs _ => (vanishingIdeal_anti_mono_iff hs.1).symm)]; rw [← funext (@Set.mem_ofPred_eq _ · Ideal.IsPrime)]; rw [← vanishingIdeal_isClosed_isIrreducible]
  rfl

Depends on / 依赖: Ideal.IsPrime, IsPrime, Set.mem_ofPred_eq, image_antitone_setOfPred_maximal, irreducibleComponents_eq_maximals_closed, mem_ofPred_eq, minimalPrimes_eq_minimals, vanishingIdeal_anti_mono_iff, vanishingIdeal_isClosed_isIrreducible
-/
lemma vanishingIdeal_irreducibleComponents :
    vanishingIdeal '' (irreducibleComponents <| PrimeSpectrum R) = minimalPrimes R := by
  rw [irreducibleComponents_eq_maximals_closed]; rw [minimalPrimes_eq_minimals]; rw [image_antitone_setOfPred_maximal (fun s t hs _ => (vanishingIdeal_anti_mono_iff hs.1).symm)]; rw [← funext (@Set.mem_ofPred_eq _ · Ideal.IsPrime)]; rw [← vanishingIdeal_isClosed_isIrreducible]
  rfl

/--
lemma `zeroLocus_minimalPrimes` / 引理 `zeroLocus_minimalPrimes`

English:
lemma zeroLocus_minimalPrimes
  proof: by
  rw [← vanishingIdeal_irreducibleComponents]; rw [← Set.image_comp]; rw [Set.EqOn.image_eq_self]
  intro s hs
  simpa [zeroLocus_vanishingIdeal_eq_closure, closure_eq_iff_isClosed]
    using isClosed_of_mem_irreducibleComponents s hs

中文:
引理 zeroLocus_minimalPrimes
  证明: by
  rw [← vanishingIdeal_irreducibleComponents]; rw [← Set.image_comp]; rw [Set.EqOn.image_eq_self]
  intro s hs
  simpa [zeroLocus_vanishingIdeal_eq_closure, closure_eq_iff_isClosed]
    using isClosed_of_mem_irreducibleComponents s hs

Depends on / 依赖: Set.EqOn.image_eq_self, Set.image_comp, closure_eq_iff_isClosed, image_comp, image_eq_self, isClosed_of_mem_irreducibleComponents, vanishingIdeal_irreducibleComponents, zeroLocus_vanishingIdeal_eq_closure
-/
lemma zeroLocus_minimalPrimes :
    zeroLocus ∘ (↑) '' minimalPrimes R = irreducibleComponents (PrimeSpectrum R) := by
  rw [← vanishingIdeal_irreducibleComponents]; rw [← Set.image_comp]; rw [Set.EqOn.image_eq_self]
  intro s hs
  simpa [zeroLocus_vanishingIdeal_eq_closure, closure_eq_iff_isClosed]
    using isClosed_of_mem_irreducibleComponents s hs

variable {R}

/--
lemma `vanishingIdeal_mem_minimalPrimes` / 引理 `vanishingIdeal_mem_minimalPrimes`

English:
lemma vanishingIdeal_mem_minimalPrimes
  given: {s : Set (PrimeSpectrum R)}
  proof: by
  constructor
  · rw [← zeroLocus_minimalPrimes, ← zeroLocus_vanishingIdeal_eq_closure]
    exact Set.mem_image_of_mem _
  · rw [← vanishingIdeal_irreducibleComponents, ← vanishingIdeal_closure]
    exact Set.mem_image_of_mem _

中文:
引理 vanishingIdeal_mem_minimalPrimes
  条件: {s : 集合 (素谱 R)}
  证明: by
  constructor
  · rw [← zeroLocus_minimalPrimes, ← zeroLocus_vanishingIdeal_eq_closure]
    exact Set.mem_image_of_mem _
  · rw [← vanishingIdeal_irreducibleComponents, ← vanishingIdeal_closure]
    exact Set.mem_image_of_mem _

Depends on / 依赖: Set.mem_image_of_mem, mem_image_of_mem, vanishingIdeal_closure, vanishingIdeal_irreducibleComponents, zeroLocus_minimalPrimes, zeroLocus_vanishingIdeal_eq_closure
-/
lemma vanishingIdeal_mem_minimalPrimes {s : Set (PrimeSpectrum R)} :
    vanishingIdeal s in minimalPrimes R ↔ closure s in irreducibleComponents (PrimeSpectrum R) := by
  constructor
  · rw [← zeroLocus_minimalPrimes, ← zeroLocus_vanishingIdeal_eq_closure]
    exact Set.mem_image_of_mem _
  · rw [← vanishingIdeal_irreducibleComponents, ← vanishingIdeal_closure]
    exact Set.mem_image_of_mem _

/--
lemma `zeroLocus_ideal_mem_irreducibleComponents` / 引理 `zeroLocus_ideal_mem_irreducibleComponents`

English:
lemma zeroLocus_ideal_mem_irreducibleComponents
  given: {I : Ideal R}
  proof: by
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  conv_lhs => rw [← (isClosed_zeroLocus _).closure_eq]
  exact vanishingIdeal_mem_minimalPrimes.symm

中文:
引理 zeroLocus_ideal_mem_irreducibleComponents
  条件: {I : 理想 R}
  证明: by
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  conv_lhs => rw [← (isClosed_zeroLocus _).closure_eq]
  exact vanishingIdeal_mem_minimalPrimes.symm

Depends on / 依赖: closure_eq, conv_lhs, isClosed_zeroLocus, vanishingIdeal_mem_minimalPrimes, vanishingIdeal_mem_minimalPrimes.symm, vanishingIdeal_zeroLocus_eq_radical
-/
lemma zeroLocus_ideal_mem_irreducibleComponents {I : Ideal R} :
    zeroLocus I in irreducibleComponents (PrimeSpectrum R) ↔ I.radical in minimalPrimes R := by
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  conv_lhs => rw [← (isClosed_zeroLocus _).closure_eq]
  exact vanishingIdeal_mem_minimalPrimes.symm

end CommSemiring

end PrimeSpectrum

namespace IsLocalRing

variable [CommSemiring R] [IsLocalRing R]

/--
Definition of `closedPoint` / `closedPoint` 的定义

English:
definition closedPoint
  signature: : PrimeSpectrum R
  body: ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩

中文:
定义 closedPoint
  签名: : 素谱 R
  定义体: ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩

Depends on / 依赖: isMaximal, isPrime, maximalIdeal, maximalIdeal.isMaximal
-/
def closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (PrimeSpectrum R)
  body: closedPoint R
  le_top := fun _ => le_maximalIdeal Ideal.IsPrime.ne_top'

中文:
实例 :
  签名: 有顶序 (素谱 R)
  定义体: closedPoint R
  le_top := fun _ => le_maximalIdeal Ideal.IsPrime.ne_top'

Depends on / 依赖: closedPoint
-/
instance : OrderTop (PrimeSpectrum R) where
  top := closedPoint R
  le_top := fun _ => le_maximalIdeal Ideal.IsPrime.ne_top'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] : BoundedOrder (PrimeSpectrum R) where

中文:
实例 [是整环
  签名: R] : 有界序 (素谱 R) where
-/
instance [IsDomain R] : BoundedOrder (PrimeSpectrum R) where

@[simp]
/--
theorem `PrimeSpectrum.asIdeal_top` / 定理 `PrimeSpectrum.asIdeal_top`

English:
theorem PrimeSpectrum.asIdeal_top
  statement: (⊤ : PrimeSpectrum R).asIdeal = IsLocalRing.maximalIdeal R
  proof: rfl

中文:
定理 素谱.asIdeal_top
  结论: (⊤ : 素谱 R).asIdeal = 是局部环.maximalIdeal R
  证明: rfl
-/
theorem PrimeSpectrum.asIdeal_top : (⊤ : PrimeSpectrum R).asIdeal = IsLocalRing.maximalIdeal R :=
  rfl

variable {R}

/--
theorem `isLocalHom_iff_comap_closedPoint` / 定理 `isLocalHom_iff_comap_closedPoint`

English:
theorem isLocalHom_iff_comap_closedPoint
  statement: {S : Type v} [CommSemiring S] [IsLocalRing S]
  proof: by
  -- Porting note: inline `this` does **not** work
  have := (local_hom_TFAE f).out 0 4
  rw [this]; rw [PrimeSpectrum.ext_iff]
  rfl

@[simp]

中文:
定理 isLocalHom_iff_comap_closedPoint
  结论: {S : 类型v} [交换半环 S] [是局部环 S]
  证明: by
  -- Porting note: inline `this` does **not** work
  have := (local_hom_TFAE f).out 0 4
  rw [this]; rw [PrimeSpectrum.ext_iff]
  rfl

@[simp]
-/
theorem isLocalHom_iff_comap_closedPoint {S : Type v} [CommSemiring S] [IsLocalRing S]
    (f : R ->+* S) : IsLocalHom f ↔ PrimeSpectrum.comap f (closedPoint S) = closedPoint R := by
  -- Porting note: inline `this` does **not** work
  have := (local_hom_TFAE f).out 0 4
  rw [this]; rw [PrimeSpectrum.ext_iff]
  rfl

@[simp]
/--
theorem `comap_closedPoint` / 定理 `comap_closedPoint`

English:
theorem comap_closedPoint
  statement: {S : Type v} [CommSemiring S] [IsLocalRing S] (f : R ->+* S)
  proof: (isLocalHom_iff_comap_closedPoint f).mp inferInstance

中文:
定理 comap_closedPoint
  结论: {S : 类型v} [交换半环 S] [是局部环 S] (f : R ->+* S)
  证明: (isLocalHom_iff_comap_closedPoint f).mp inferInstance

Depends on / 依赖: isLocalHom_iff_comap_closedPoint
-/
theorem comap_closedPoint {S : Type v} [CommSemiring S] [IsLocalRing S] (f : R ->+* S)
    [IsLocalHom f] : PrimeSpectrum.comap f (closedPoint S) = closedPoint R :=
  (isLocalHom_iff_comap_closedPoint f).mp inferInstance

/--
theorem `specializes_closedPoint` / 定理 `specializes_closedPoint`

English:
theorem specializes_closedPoint
  given: (x : PrimeSpectrum R)
  statement: x ⤳ closedPoint R
  proof: (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.2.1)

中文:
定理 specializes_closedPoint
  条件: (x : 素谱 R)
  结论: x ⤳ closedPoint R
  证明: (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.2.1)

Depends on / 依赖: IsLocalRing, IsLocalRing.le_maximalIdeal, PrimeSpectrum, PrimeSpectrum.le_iff_specializes, le_iff_specializes, le_maximalIdeal
-/
theorem specializes_closedPoint (x : PrimeSpectrum R) : x ⤳ closedPoint R :=
  (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.2.1)

/--
theorem `closedPoint_mem_iff` / 定理 `closedPoint_mem_iff`

English:
theorem closedPoint_mem_iff
  given: (U : TopologicalSpace.Opens <| PrimeSpectrum R)
  proof: by
  constructor
  · rw [eq_top_iff]
    exact fun h x _ => (specializes_closedPoint x).mem_open U.2 h
  · rintro rfl
    exact TopologicalSpace.Opens.mem_top _

中文:
定理 closedPoint_mem_iff
  条件: (U : 拓扑空间.Opens <| 素谱 R)
  证明: by
  constructor
  · rw [eq_top_iff]
    exact fun h x _ => (specializes_closedPoint x).mem_open U.2 h
  · rintro rfl
    exact TopologicalSpace.Opens.mem_top _

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.mem_top, eq_top_iff, mem_open, mem_top, specializes_closedPoint
-/
theorem closedPoint_mem_iff (U : TopologicalSpace.Opens <| PrimeSpectrum R) :
    closedPoint R in U ↔ U = ⊤ := by
  constructor
  · rw [eq_top_iff]
    exact fun h x _ => (specializes_closedPoint x).mem_open U.2 h
  · rintro rfl
    exact TopologicalSpace.Opens.mem_top _

/--
lemma `closed_point_mem_iff` / 引理 `closed_point_mem_iff`

English:
lemma closed_point_mem_iff
  given: {U : TopologicalSpace.Opens (PrimeSpectrum R)}
  proof: ⟨(eq_top_iff.mpr fun x _ => (specializes_closedPoint x).mem_open U.2 ·), (· ▸ trivial)⟩

@[simp]

中文:
引理 closed_point_mem_iff
  条件: {U : 拓扑空间.Opens (素谱 R)}
  证明: ⟨(eq_top_iff.mpr fun x _ => (specializes_closedPoint x).mem_open U.2 ·), (· ▸ trivial)⟩

@[simp]

Depends on / 依赖: eq_top_iff, eq_top_iff.mpr, mem_open, specializes_closedPoint
-/
lemma closed_point_mem_iff {U : TopologicalSpace.Opens (PrimeSpectrum R)} :
    closedPoint R in U ↔ U = ⊤ :=
  ⟨(eq_top_iff.mpr fun x _ => (specializes_closedPoint x).mem_open U.2 ·), (· ▸ trivial)⟩

@[simp]
/--
theorem `PrimeSpectrum.comap_residue` / 定理 `PrimeSpectrum.comap_residue`

English:
theorem PrimeSpectrum.comap_residue
  statement: (T : Type u) [CommRing T] [IsLocalRing T]
  proof: by
  rw [Subsingleton.elim x ⊥]
  ext1
  exact Ideal.mk_ker

中文:
定理 素谱.comap_residue
  结论: (T : 类型u) [交换环 T] [是局部环 T]
  证明: by
  rw [Subsingleton.elim x ⊥]
  ext1
  exact Ideal.mk_ker

Depends on / 依赖: Ideal.mk_ker, Subsingleton, Subsingleton.elim, mk_ker
-/
theorem PrimeSpectrum.comap_residue (T : Type u) [CommRing T] [IsLocalRing T]
    (x : PrimeSpectrum (ResidueField T)) : PrimeSpectrum.comap (residue T) x = closedPoint T := by
  rw [Subsingleton.elim x ⊥]
  ext1
  exact Ideal.mk_ker

variable (R) in
/--
lemma `isClosed_singleton_closedPoint` / 引理 `isClosed_singleton_closedPoint`

English:
lemma isClosed_singleton_closedPoint
  statement: IsClosed {closedPoint R}
  proof: by
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]; rw [closedPoint]
  infer_instance

中文:
引理 isClosed_singleton_closedPoint
  结论: 是闭集 {closedPoint R}
  证明: by
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]; rw [closedPoint]
  infer_instance

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.isClosed_singleton_iff_isMaximal, closedPoint, infer_instance, isClosed_singleton_iff_isMaximal
-/
lemma isClosed_singleton_closedPoint : IsClosed {closedPoint R} := by
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]; rw [closedPoint]
  infer_instance

/--
theorem `Ring.KrullDimLE.eq_bot_or_eq_top` / 定理 `Ring.KrullDimLE.eq_bot_or_eq_top`

English:
theorem Ring.KrullDimLE.eq_bot_or_eq_top
  statement: [IsDomain R] [Ring.KrullDimLE 1 R]
  proof: Order.krullDim_le_one_iff_of_boundedOrder.mp Order.KrullDimLE.krullDim_le _

中文:
定理 环.Krull维数不超过.eq_bot_or_eq_top
  结论: [是整环 R] [环.Krull维数不超过 1 R]
  证明: Order.krullDim_le_one_iff_of_boundedOrder.mp Order.KrullDimLE.krullDim_le _

Depends on / 依赖: KrullDimLE, Order.KrullDimLE.krullDim_le, Order.krullDim_le_one_iff_of_boundedOrder.mp, krullDim_le, krullDim_le_one_iff_of_boundedOrder
-/
theorem Ring.KrullDimLE.eq_bot_or_eq_top [IsDomain R] [Ring.KrullDimLE 1 R]
    (x : PrimeSpectrum R) : x = ⊥ ∨ x = ⊤ :=
  Order.krullDim_le_one_iff_of_boundedOrder.mp Order.KrullDimLE.krullDim_le _

end IsLocalRing

section KrullDimension

/--
theorem `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` / 定理 `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`

English:
theorem PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
  given: [CommSemiring R]
  proof: Order.krullDim_orderDual.symm.trans Order.krullDim_eq_of_orderIso
  (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm

中文:
定理 素谱.topologicalKrullDim_eq_ringKrullDim
  条件: [交换半环 R]
  证明: Order.krullDim_orderDual.symm.trans Order.krullDim_eq_of_orderIso
  (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm

Depends on / 依赖: Order.krullDim_eq_of_orderIso, Order.krullDim_orderDual.symm.trans, PrimeSpectrum, PrimeSpectrum.pointsEquivIrreducibleCloseds, krullDim_eq_of_orderIso, krullDim_orderDual, pointsEquivIrreducibleCloseds
-/
theorem PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim [CommSemiring R] :
    topologicalKrullDim (PrimeSpectrum R) = ringKrullDim R :=
Order.krullDim_orderDual.symm.trans Order.krullDim_eq_of_orderIso
  (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm

end KrullDimension

section Idempotent

variable {R} [CommRing R]

namespace PrimeSpectrum

@[stacks 00EC]
/--
lemma `basicOpen_eq_zeroLocus_of_isIdempotentElem` / 引理 `basicOpen_eq_zeroLocus_of_isIdempotentElem`

English:
lemma basicOpen_eq_zeroLocus_of_isIdempotentElem
  proof: basicOpen_eq_zeroLocus_of_mul_add _ _ (by simp [mul_sub, he.eq]) (by simp)

@[stacks 00EC]

中文:
引理 basicOpen_eq_zeroLocus_of_isIdempotentElem
  证明: basicOpen_eq_zeroLocus_of_mul_add _ _ (by simp [mul_sub, he.eq]) (by simp)

@[stacks 00EC]

Depends on / 依赖: basicOpen_eq_zeroLocus_of_mul_add, he.eq, mul_sub
-/
lemma basicOpen_eq_zeroLocus_of_isIdempotentElem
    (e : R) (he : IsIdempotentElem e) :
    basicOpen e = zeroLocus {1 - e} :=
  basicOpen_eq_zeroLocus_of_mul_add _ _ (by simp [mul_sub, he.eq]) (by simp)

@[stacks 00EC]
/--
lemma `zeroLocus_eq_basicOpen_of_isIdempotentElem` / 引理 `zeroLocus_eq_basicOpen_of_isIdempotentElem`

English:
lemma zeroLocus_eq_basicOpen_of_isIdempotentElem
  proof: by
  rw [basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub]; rw [sub_sub_cancel]

中文:
引理 zeroLocus_eq_basicOpen_of_isIdempotentElem
  证明: by
  rw [basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub]; rw [sub_sub_cancel]

Depends on / 依赖: basicOpen_eq_zeroLocus_of_isIdempotentElem, he.one_sub, one_sub, sub_sub_cancel
-/
lemma zeroLocus_eq_basicOpen_of_isIdempotentElem
    (e : R) (he : IsIdempotentElem e) :
    zeroLocus {e} = basicOpen (1 - e) := by
  rw [basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub]; rw [sub_sub_cancel]

/--
lemma `isClopen_iff` / 引理 `isClopen_iff`

English:
lemma isClopen_iff
  given: {s : Set (PrimeSpectrum R)}
  proof: by
  refine ⟨exists_idempotent_basicOpen_eq_of_isClopen, ?_⟩
  rintro ⟨e, he, rfl⟩
  refine ⟨?_, (basicOpen e).2⟩
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact isClosed_zeroLocus _

中文:
引理 isClopen_iff
  条件: {s : 集合 (素谱 R)}
  证明: by
  refine ⟨exists_idempotent_basicOpen_eq_of_isClopen, ?_⟩
  rintro ⟨e, he, rfl⟩
  refine ⟨?_, (basicOpen e).2⟩
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact isClosed_zeroLocus _

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem, basicOpen, basicOpen_eq_zeroLocus_of_isIdempotentElem, exists_idempotent_basicOpen_eq_of_isClopen, isClosed_zeroLocus
-/
lemma isClopen_iff {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ exists e : R, IsIdempotentElem e ∧ s = basicOpen e := by
  refine ⟨exists_idempotent_basicOpen_eq_of_isClopen, ?_⟩
  rintro ⟨e, he, rfl⟩
  refine ⟨?_, (basicOpen e).2⟩
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact isClosed_zeroLocus _

/--
lemma `isClopen_iff_zeroLocus` / 引理 `isClopen_iff_zeroLocus`

English:
lemma isClopen_iff_zeroLocus
  given: {s : Set (PrimeSpectrum R)}
  proof: isClopen_iff.trans ⟨fun ⟨e, he, h⟩ => ⟨1 - e, he.one_sub,
    h.trans (basicOpen_eq_zeroLocus_of_isIdempotentElem e he)⟩,
    fun ⟨e, he, h⟩ => ⟨1 - e, he.one_sub, h.trans (zeroLocus_eq_basicOpen_of_isIdempotentElem e he)⟩⟩

中文:
引理 isClopen_iff_zeroLocus
  条件: {s : 集合 (素谱 R)}
  证明: isClopen_iff.trans ⟨fun ⟨e, he, h⟩ => ⟨1 - e, he.one_sub,
    h.trans (basicOpen_eq_zeroLocus_of_isIdempotentElem e he)⟩,
    fun ⟨e, he, h⟩ => ⟨1 - e, he.one_sub, h.trans (zeroLocus_eq_basicOpen_of_isIdempotentElem e he)⟩⟩

Depends on / 依赖: basicOpen_eq_zeroLocus_of_isIdempotentElem, h.trans, he.one_sub, isClopen_iff, isClopen_iff.trans, one_sub, zeroLocus_eq_basicOpen_of_isIdempotentElem
-/
lemma isClopen_iff_zeroLocus {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ exists e : R, IsIdempotentElem e ∧ s = zeroLocus {e} :=
isClopen_iff.trans ⟨fun ⟨e, he, h⟩ => ⟨1 - e, he.one_sub,
    h.trans (basicOpen_eq_zeroLocus_of_isIdempotentElem e he)⟩,
    fun ⟨e, he, h⟩ => ⟨1 - e, he.one_sub, h.trans (zeroLocus_eq_basicOpen_of_isIdempotentElem e he)⟩⟩

open TopologicalSpace (Clopens Opens)

/-- Clopen subsets in the prime spectrum of a commutative ring are in 1-1 correspondence
with idempotent elements in the ring. -/
@[stacks 00EE]
/--
Definition of `isIdempotentElemEquivClopens` / `isIdempotentElemEquivClopens` 的定义

English:
definition isIdempotentElemEquivClopens
  signature: :
  body: .trans .isIdempotentElemMulZeroAddOne mulZeroAddOneEquivClopens

中文:
定义 isIdempotentElemEquivClopens
  签名: :
  定义体: .trans .isIdempotentElemMulZeroAddOne mulZeroAddOneEquivClopens

Depends on / 依赖: isIdempotentElemMulZeroAddOne, mulZeroAddOneEquivClopens
-/
def isIdempotentElemEquivClopens :
    {e : R // IsIdempotentElem e} ≃o Clopens (PrimeSpectrum R) :=
  .trans .isIdempotentElemMulZeroAddOne mulZeroAddOneEquivClopens

/--
lemma `basicOpen_isIdempotentElemEquivClopens_symm` / 引理 `basicOpen_isIdempotentElemEquivClopens_symm`

English:
lemma basicOpen_isIdempotentElemEquivClopens_symm
  given: (s)
  proof: Opens.ext congr_arg (·.1) (isIdempotentElemEquivClopens.apply_symm_apply s)

中文:
引理 basicOpen_isIdempotentElemEquivClopens_symm
  条件: (s)
  证明: Opens.ext congr_arg (·.1) (isIdempotentElemEquivClopens.apply_symm_apply s)

Depends on / 依赖: s.toOpens, toOpens
-/
lemma basicOpen_isIdempotentElemEquivClopens_symm (s) :
    basicOpen (isIdempotentElemEquivClopens (R := R).symm s).1 = s.toOpens :=
Opens.ext congr_arg (·.1) (isIdempotentElemEquivClopens.apply_symm_apply s)

/--
lemma `coe_isIdempotentElemEquivClopens_apply` / 引理 `coe_isIdempotentElemEquivClopens_apply`

English:
lemma coe_isIdempotentElemEquivClopens_apply
  given: (e)
  proof: rfl

中文:
引理 coe_isIdempotentElemEquivClopens_apply
  条件: (e)
  证明: rfl
-/
lemma coe_isIdempotentElemEquivClopens_apply (e) :
    (isIdempotentElemEquivClopens e : Set (PrimeSpectrum R)) = basicOpen (e.1 : R) := rfl

/--
lemma `isIdempotentElemEquivClopens_apply_toOpens` / 引理 `isIdempotentElemEquivClopens_apply_toOpens`

English:
lemma isIdempotentElemEquivClopens_apply_toOpens
  given: (e)
  proof: rfl

中文:
引理 isIdempotentElemEquivClopens_apply_toOpens
  条件: (e)
  证明: rfl
-/
lemma isIdempotentElemEquivClopens_apply_toOpens (e) :
    (isIdempotentElemEquivClopens e).toOpens = basicOpen (e.1 : R) := rfl

/--
lemma `isIdempotentElemEquivClopens_mul` / 引理 `isIdempotentElemEquivClopens_mul`

English:
lemma isIdempotentElemEquivClopens_mul
  given: (e₁ e₂ : {e : R | IsIdempotentElem e})
  proof: map_inf ..

中文:
引理 isIdempotentElemEquivClopens_mul
  条件: (e₁ e₂ : {e : R | IsIdempotentElem e})
  证明: map_inf ..

Depends on / 依赖: map_inf
-/
lemma isIdempotentElemEquivClopens_mul (e₁ e₂ : {e : R | IsIdempotentElem e}) :
    isIdempotentElemEquivClopens ⟨_, e₁.2.mul e₂.2⟩ =
      isIdempotentElemEquivClopens e₁ ⊓ isIdempotentElemEquivClopens e₂ :=
  map_inf ..

/--
lemma `isIdempotentElemEquivClopens_one_sub` / 引理 `isIdempotentElemEquivClopens_one_sub`

English:
lemma isIdempotentElemEquivClopens_one_sub
  given: (e : {e : R | IsIdempotentElem e})
  proof: map_compl ..

中文:
引理 isIdempotentElemEquivClopens_one_sub
  条件: (e : {e : R | IsIdempotentElem e})
  证明: map_compl ..

Depends on / 依赖: map_compl
-/
lemma isIdempotentElemEquivClopens_one_sub (e : {e : R | IsIdempotentElem e}) :
    isIdempotentElemEquivClopens ⟨_, e.2.one_sub⟩ = (isIdempotentElemEquivClopens e)ᶜ :=
  map_compl ..

/--
lemma `isIdempotentElemEquivClopens_symm_inf` / 引理 `isIdempotentElemEquivClopens_symm_inf`

English:
lemma isIdempotentElemEquivClopens_symm_inf
  given: (s₁ s₂)
  proof: isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊓ s₂) = ⟨_, (e s₁).2.mul (e s₂).2⟩ :=
  map_inf ..

中文:
引理 isIdempotentElemEquivClopens_symm_inf
  条件: (s₁ s₂)
  证明: isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊓ s₂) = ⟨_, (e s₁).2.mul (e s₂).2⟩ :=
  map_inf ..

Depends on / 依赖: isIdempotentElemEquivClopens
-/
lemma isIdempotentElemEquivClopens_symm_inf (s₁ s₂) :
    letI e := isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊓ s₂) = ⟨_, (e s₁).2.mul (e s₂).2⟩ :=
  map_inf ..

/--
lemma `isIdempotentElemEquivClopens_symm_compl` / 引理 `isIdempotentElemEquivClopens_symm_compl`

English:
lemma isIdempotentElemEquivClopens_symm_compl
  given: (s : Clopens (PrimeSpectrum R))
  proof: map_compl ..

中文:
引理 isIdempotentElemEquivClopens_symm_compl
  条件: (s : Clopens (素谱 R))
  证明: map_compl ..

Depends on / 依赖: map_compl
-/
lemma isIdempotentElemEquivClopens_symm_compl (s : Clopens (PrimeSpectrum R)) :
    isIdempotentElemEquivClopens.symm sᶜ = ⟨_, (isIdempotentElemEquivClopens.symm s).2.one_sub⟩ :=
  map_compl ..

/--
lemma `isIdempotentElemEquivClopens_symm_top` / 引理 `isIdempotentElemEquivClopens_symm_top`

English:
lemma isIdempotentElemEquivClopens_symm_top
  proof: map_top _

中文:
引理 isIdempotentElemEquivClopens_symm_top
  证明: map_top _

Depends on / 依赖: map_top
-/
lemma isIdempotentElemEquivClopens_symm_top :
    isIdempotentElemEquivClopens.symm ⊤ = ⟨(1 : R), .one⟩ :=
  map_top _

/--
lemma `isIdempotentElemEquivClopens_symm_bot` / 引理 `isIdempotentElemEquivClopens_symm_bot`

English:
lemma isIdempotentElemEquivClopens_symm_bot
  proof: map_bot _

中文:
引理 isIdempotentElemEquivClopens_symm_bot
  证明: map_bot _

Depends on / 依赖: map_bot
-/
lemma isIdempotentElemEquivClopens_symm_bot :
    isIdempotentElemEquivClopens.symm ⊥ = ⟨(0 : R), .zero⟩ :=
  map_bot _

/--
lemma `isIdempotentElemEquivClopens_symm_sup` / 引理 `isIdempotentElemEquivClopens_symm_sup`

English:
lemma isIdempotentElemEquivClopens_symm_sup
  given: (s₁ s₂ : Clopens (PrimeSpectrum R))
  proof: isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊔ s₂) = ⟨_, (e s₁).2.add_sub_mul (e s₂).2⟩ :=
  map_sup ..

中文:
引理 isIdempotentElemEquivClopens_symm_sup
  条件: (s₁ s₂ : Clopens (素谱 R))
  证明: isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊔ s₂) = ⟨_, (e s₁).2.add_sub_mul (e s₂).2⟩ :=
  map_sup ..

Depends on / 依赖: isIdempotentElemEquivClopens
-/
lemma isIdempotentElemEquivClopens_symm_sup (s₁ s₂ : Clopens (PrimeSpectrum R)) :
    letI e := isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊔ s₂) = ⟨_, (e s₁).2.add_sub_mul (e s₂).2⟩ :=
  map_sup ..

end PrimeSpectrum

end Idempotent
