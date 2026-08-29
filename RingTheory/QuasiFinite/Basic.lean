/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Quasi-finite algebras

In this file, we define the notion of quasi-finite algebras and prove basic properties about them

## Main definition and results
- `Algebra.QuasiFinite`: The class of quasi-finite algebras.
  We say that an `R`-algebra `S` is quasi-finite
  if `κ(p) ⊗[R] S` is finite-dimensional over `κ(p)` for all primes `p` of `R`.
- `Algebra.QuasiFinite.finite_comap_preimage_singleton`:
  Quasi-finite algebras have finite fibers.
- `Algebra.QuasiFinite.iff_of_isArtinianRing`:
  Over an artinian ring, an algebra is quasi-finite iff it is module-finite.
- `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton`: For a finite-type `R`-algebra `S`,
  `S` is quasi-finite if and only if `Spec S → Spec R` has finite fibers.
- `Algebra.QuasiFiniteAt`: If `S` is an `R`-algebra and `p` a prime of `S`,
  we say that `S` is `R`-quasi-finite at `p` if `Sₚ` is `R`-quasi-finite.

-/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

-- See `Mathlib/RingTheory/QuasiFinite/Polynomial.lean`
assert_not_exists RatFunc

open TensorProduct

-- for performance reasons
attribute [-instance] Module.Free.instFaithfulSMulOfNontrivial Algebra.IsIntegral.isLocalHom

namespace Algebra

variable (R S) in
/--
We say that an `R`-algebra `S` is quasi-finite
if `κ(p) ⊗[R] S` is finite-dimensional over `κ(p)` for all primes `p` of `R`.

This is slightly different from the
[stacks projects definition](https://stacks.math.columbia.edu/tag/00PL),
which requires `S` to be of finite type over `R`.

Also see `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` that
this is equivalent to having finite fibers for finite-type algebras.
-/
@[mk_iff, stacks 00PL]
/--
Definition of `QuasiFinite` / `QuasiFinite` 的定义

English:
class QuasiFinite
  parameters: : Prop where
  axioms and operations (1):
    - finite_fiber((P : Ideal R) [P.IsPrime]) : Module.Finite P.ResidueField (P.Fiber S)  [default: by infer_instance]

中文:
类 拟有限
  参数: : 命题 where
  公理与运算 (1 个):
    - finite_fiber((P : 理想 R) [P.是素]) : 模.有限 P.ResidueField (P.Fiber S)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class QuasiFinite : Prop where
  finite_fiber (P : Ideal R) [P.IsPrime] :
    Module.Finite P.ResidueField (P.Fiber S) := by infer_instance

attribute [stacks 00PM] quasiFinite_iff

namespace QuasiFinite

attribute [instance] finite_fiber

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiFinite
  signature: R S] (P
  body: .of_finite P.ResidueField _

中文:
实例 [拟有限
  签名: R S] (P
  定义体: .of_finite P.ResidueField _

Depends on / 依赖: P.ResidueField, ResidueField, of_finite
-/
instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] : IsArtinianRing (P.Fiber S) :=
  .of_finite P.ResidueField _

/--
lemma `finite_comap_preimage_singleton` / 引理 `finite_comap_preimage_singleton`

English:
lemma finite_comap_preimage_singleton
  given: [QuasiFinite R S] (P : PrimeSpectrum R)
  proof: (PrimeSpectrum.preimageEquivFiber R S P).finite_iff.mpr finite_of_compact_of_discrete

中文:
引理 finite_comap_preimage_singleton
  条件: [拟有限 R S] (P : 素谱 R)
  证明: (PrimeSpectrum.preimageEquivFiber R S P).finite_iff.mpr finite_of_compact_of_discrete

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.preimageEquivFiber, finite_iff, finite_iff.mpr, finite_of_compact_of_discrete, preimageEquivFiber
-/
lemma finite_comap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) :
    (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}).Finite :=
  (PrimeSpectrum.preimageEquivFiber R S P).finite_iff.mpr finite_of_compact_of_discrete

/--
lemma `finite_primesOver` / 引理 `finite_primesOver`

English:
lemma finite_primesOver
  given: [QuasiFinite R S] (I : Ideal R)
  statement: (I.primesOver S).Finite
  proof: by
  by_cases h : I.IsPrime
  · refine ((finite_comap_preimage_singleton ⟨I, h⟩).image PrimeSpectrum.asIdeal).subset ?_
    exact fun J hJ => ⟨⟨_, hJ.1⟩, PrimeSpectrum.ext hJ.2.1.symm, rfl⟩
  · convert! Set.finite_empty
    by_contra!
    obtain ⟨J, h₁, ⟨rfl⟩⟩ := this
    exact h inferInstance

中文:
引理 finite_primesOver
  条件: [拟有限 R S] (I : 理想 R)
  结论: (I.primesOver S).有限
  证明: by
  by_cases h : I.IsPrime
  · refine ((finite_comap_preimage_singleton ⟨I, h⟩).image PrimeSpectrum.asIdeal).subset ?_
    exact fun J hJ => ⟨⟨_, hJ.1⟩, PrimeSpectrum.ext hJ.2.1.symm, rfl⟩
  · convert! Set.finite_empty
    by_contra!
    obtain ⟨J, h₁, ⟨rfl⟩⟩ := this
    exact h inferInstance

Depends on / 依赖: I.IsPrime, IsPrime, PrimeSpectrum, PrimeSpectrum.asIdeal, PrimeSpectrum.ext, Set.finite_empty, asIdeal, convert, finite_comap_preimage_singleton, finite_empty, subset
-/
lemma finite_primesOver [QuasiFinite R S] (I : Ideal R) : (I.primesOver S).Finite := by
  by_cases h : I.IsPrime
  · refine ((finite_comap_preimage_singleton ⟨I, h⟩).image PrimeSpectrum.asIdeal).subset ?_
    exact fun J hJ => ⟨⟨_, hJ.1⟩, PrimeSpectrum.ext hJ.2.1.symm, rfl⟩
  · convert! Set.finite_empty
    by_contra!
    obtain ⟨J, h₁, ⟨rfl⟩⟩ := this
    exact h inferInstance

/--
lemma `finite_comap_preimage` / 引理 `finite_comap_preimage`

English:
lemma finite_comap_preimage
  given: [QuasiFinite R S] {s : Set (PrimeSpectrum R)} (hs : s.Finite)
  proof: hs.preimage' fun _ _ => finite_comap_preimage_singleton _

中文:
引理 finite_comap_preimage
  条件: [拟有限 R S] {s : 集合 (素谱 R)} (hs : s.有限)
  证明: hs.preimage' fun _ _ => finite_comap_preimage_singleton _

Depends on / 依赖: finite_comap_preimage_singleton, hs.preimage, preimage
-/
lemma finite_comap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)} (hs : s.Finite) :
    (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s).Finite :=
  hs.preimage' fun _ _ => finite_comap_preimage_singleton _

/--
lemma `isDiscrete_comap_preimage_singleton` / 引理 `isDiscrete_comap_preimage_singleton`

English:
lemma isDiscrete_comap_preimage_singleton
  given: [QuasiFinite R S] (P : PrimeSpectrum R)
  proof: ⟨(PrimeSpectrum.preimageHomeomorphFiber R S P).symm.discreteTopology⟩

中文:
引理 isDiscrete_comap_preimage_singleton
  条件: [拟有限 R S] (P : 素谱 R)
  证明: ⟨(PrimeSpectrum.preimageHomeomorphFiber R S P).symm.discreteTopology⟩

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.preimageHomeomorphFiber, discreteTopology, preimageHomeomorphFiber, symm.discreteTopology
-/
lemma isDiscrete_comap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) :
    IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}) :=
  ⟨(PrimeSpectrum.preimageHomeomorphFiber R S P).symm.discreteTopology⟩

/--
lemma `isDiscrete_comap_preimage` / 引理 `isDiscrete_comap_preimage`

English:
lemma isDiscrete_comap_preimage
  statement: [QuasiFinite R S] {s : Set (PrimeSpectrum R)}
  proof: hs.preimage' (PrimeSpectrum.continuous_comap _).continuousOn
    fun _ => isDiscrete_comap_preimage_singleton _

中文:
引理 isDiscrete_comap_preimage
  结论: [拟有限 R S] {s : 集合 (素谱 R)}
  证明: hs.preimage' (PrimeSpectrum.continuous_comap _).continuousOn
    fun _ => isDiscrete_comap_preimage_singleton _

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.continuous_comap, continuousOn, continuous_comap, hs.preimage, isDiscrete_comap_preimage_singleton, preimage
-/
lemma isDiscrete_comap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)}
    (hs : IsDiscrete s) :
    IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s) :=
  hs.preimage' (PrimeSpectrum.continuous_comap _).continuousOn
    fun _ => isDiscrete_comap_preimage_singleton _

instance (priority := low) [Module.Finite R S] : QuasiFinite R S where

@[stacks 00PP "(3)"]
/--
Instance `baseChange` / 实例 `baseChange`

English:
instance baseChange
  signature: [QuasiFinite R S] {A : Type*} [CommRing A] [Algebra R A]
  body: by
  refine ⟨fun P hP => ?_⟩
  let p := P.under R
  let := Localization.AtPrime.algebraOfLiesOver p P
  let e : P.Fiber (A otimes[R] S) ≃ₐ[P.ResidueField] P.ResidueField otimes[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

中文:
实例 baseChange
  签名: [拟有限 R S] {A : 类型} [交换环 A] [代数 R A]
  定义体: by
  refine ⟨fun P hP => ?_⟩
  let p := P.under R
  let := Localization.AtPrime.algebraOfLiesOver p P
  let e : P.Fiber (A otimes[R] S) ≃ₐ[P.ResidueField] P.ResidueField otimes[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

Depends on / 依赖: Algebra, Algebra.TensorProduct.cancelBaseChange, AtPrime, Localization, Localization.AtPrime.algebraOfLiesOver, P.Fiber, P.ResidueField, P.under, ResidueField, TensorProduct, algebraOfLiesOver, cancelBaseChange, e.symm.surjective, e.symm.toLinearMap, of_surjective, otimes, p.Fiber, p.ResidueField, surjective, toLinearMap
-/
instance baseChange [QuasiFinite R S] {A : Type*} [CommRing A] [Algebra R A] :
    QuasiFinite A (A otimes[R] S) := by
  refine ⟨fun P hP => ?_⟩
  let p := P.under R
  let := Localization.AtPrime.algebraOfLiesOver p P
  let e : P.Fiber (A otimes[R] S) ≃ₐ[P.ResidueField] P.ResidueField otimes[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

open IsLocalRing in
-- See `Module.Finite.of_quasiFinite` instead
/--
lemma `finite_of_isArtinianRing_of_isLocalRing` / 引理 `finite_of_isArtinianRing_of_isLocalRing`

English:
lemma finite_of_isArtinianRing_of_isLocalRing
  proof: by
  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars _)
  have : Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    have : Module.Finite R ((maximalIdeal R).Fiber S) :=
      .trans (maximalIdeal R).ResidueField _
    .of_surjective e.toLinearMap e.surjective
  refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.mkₐ R
    ((maximalIdeal R).map (algebraMap R S))) Ideal.Quotient.mk_surjective ?_ ?_
  · refine Ideal.mk_ker.trans_le ?_
    rw [Ideal.map_le_iff_le_comap]; rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    exact fun x hx => IsNilpotent.map hx _
  · rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
    exact Ideal.FG.map (IsNoetherian.noetherian _) _

中文:
引理 finite_of_isArtinianRing_of_isLocalRing
  证明: by
  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars _)
  have : Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    have : Module.Finite R ((maximalIdeal R).Fiber S) :=
      .trans (maximalIdeal R).ResidueField _
    .of_surjective e.toLinearMap e.surjective
  refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.mkₐ R
    ((maximalIdeal R).map (algebraMap R S))) Ideal.Quotient.mk_surjective ?_ ?_
  · refine Ideal.mk_ker.trans_le ?_
    rw [Ideal.map_le_iff_le_comap]; rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    exact fun x hx => IsNilpotent.map hx _
  · rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
    exact Ideal.FG.map (IsNoetherian.noetherian _) _
-/
private lemma finite_of_isArtinianRing_of_isLocalRing
    [QuasiFinite R S] [IsArtinianRing R] [IsLocalRing R] : Module.Finite R S := by
  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars _)
  have : Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    have : Module.Finite R ((maximalIdeal R).Fiber S) :=
      .trans (maximalIdeal R).ResidueField _
    .of_surjective e.toLinearMap e.surjective
  refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.mkₐ R
    ((maximalIdeal R).map (algebraMap R S))) Ideal.Quotient.mk_surjective ?_ ?_
  · refine Ideal.mk_ker.trans_le ?_
    rw [Ideal.map_le_iff_le_comap]; rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    exact fun x hx => IsNilpotent.map hx _
  · rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
    exact Ideal.FG.map (IsNoetherian.noetherian _) _

/--
lemma `_root_.Module.Finite.of_quasiFinite` / 引理 `_root_.Module.Finite.of_quasiFinite`

English:
lemma _root_.Module.Finite.of_quasiFinite
  given: [IsArtinianRing R] [QuasiFinite R S]
  proof: by
  classical
  let e : R ≃ₐ[R] PrimeSpectrum.PiLocalization R :=
    .ofBijective (IsScalarTower.toAlgHom _ _ _)
      (PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp inferInstance)
  have : Fintype (PrimeSpectrum R) := .ofFinite _
  let e' : S ≃ₐ[R] Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl otimes[R] S :=
(Algebra.TensorProduct.rid R R S).symm.trans (Algebra.TensorProduct.congr .refl e).trans
(Algebra.TensorProduct.piRight _ _ _ _).trans AlgEquiv.piCongrRight
      fun _ => Algebra.TensorProduct.comm _ _ _
  have (p : PrimeSpectrum R) : Module.Finite R (Localization p.asIdeal.primeCompl otimes[R] S) :=
    have : Module.Finite R (Localization.AtPrime p.asIdeal) :=
      .of_surjective (Algebra.linearMap _ _)
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
    have : Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal otimes[R] S) := finite_of_isArtinianRing_of_isLocalRing
    .trans (Localization.AtPrime p.asIdeal) _
  exact .of_surjective e'.symm.toLinearMap e'.symm.surjective

中文:
引理 _root_.模.有限.of_quasiFinite
  条件: [是Artin环 R] [拟有限 R S]
  证明: by
  classical
  let e : R ≃ₐ[R] PrimeSpectrum.PiLocalization R :=
    .ofBijective (IsScalarTower.toAlgHom _ _ _)
      (PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp inferInstance)
  have : Fintype (PrimeSpectrum R) := .ofFinite _
  let e' : S ≃ₐ[R] Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl otimes[R] S :=
(Algebra.TensorProduct.rid R R S).symm.trans (Algebra.TensorProduct.congr .refl e).trans
(Algebra.TensorProduct.piRight _ _ _ _).trans AlgEquiv.piCongrRight
      fun _ => Algebra.TensorProduct.comm _ _ _
  have (p : PrimeSpectrum R) : Module.Finite R (Localization p.asIdeal.primeCompl otimes[R] S) :=
    have : Module.Finite R (Localization.AtPrime p.asIdeal) :=
      .of_surjective (Algebra.linearMap _ _)
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
    have : Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal otimes[R] S) := finite_of_isArtinianRing_of_isLocalRing
    .trans (Localization.AtPrime p.asIdeal) _
  exact .of_surjective e'.symm.toLinearMap e'.symm.surjective

Depends on / 依赖: AlgEquiv, AlgEquiv.piCongrRight, Algebra, Algebra.T, Algebra.TensorProduct.congr, Algebra.TensorProduct.piRight, Algebra.TensorProduct.rid, Fintype, IsScalarTower, IsScalarTower.toAlgHom, Localization, PiLocalization, PrimeSpectrum, PrimeSpectrum.PiLocalization, PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp, TensorProduct, asIdeal, classical, discreteTopology_iff_toPiLocalization_bijective, ofBijective
-/
lemma _root_.Module.Finite.of_quasiFinite [IsArtinianRing R] [QuasiFinite R S] :
    Module.Finite R S := by
  classical
  let e : R ≃ₐ[R] PrimeSpectrum.PiLocalization R :=
    .ofBijective (IsScalarTower.toAlgHom _ _ _)
      (PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp inferInstance)
  have : Fintype (PrimeSpectrum R) := .ofFinite _
  let e' : S ≃ₐ[R] Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl otimes[R] S :=
(Algebra.TensorProduct.rid R R S).symm.trans (Algebra.TensorProduct.congr .refl e).trans
(Algebra.TensorProduct.piRight _ _ _ _).trans AlgEquiv.piCongrRight
      fun _ => Algebra.TensorProduct.comm _ _ _
  have (p : PrimeSpectrum R) : Module.Finite R (Localization p.asIdeal.primeCompl otimes[R] S) :=
    have : Module.Finite R (Localization.AtPrime p.asIdeal) :=
      .of_surjective (Algebra.linearMap _ _)
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
    have : Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal otimes[R] S) := finite_of_isArtinianRing_of_isLocalRing
    .trans (Localization.AtPrime p.asIdeal) _
  exact .of_surjective e'.symm.toLinearMap e'.symm.surjective

/--
lemma `iff_of_isArtinianRing` / 引理 `iff_of_isArtinianRing`

English:
lemma iff_of_isArtinianRing
  given: [IsArtinianRing R]
  proof: ⟨fun _ => .of_quasiFinite, fun _ => inferInstance⟩

中文:
引理 iff_of_isArtinianRing
  条件: [是Artin环 R]
  证明: ⟨fun _ => .of_quasiFinite, fun _ => inferInstance⟩

Depends on / 依赖: of_quasiFinite
-/
lemma iff_of_isArtinianRing [IsArtinianRing R] :
    QuasiFinite R S ↔ Module.Finite R S :=
  ⟨fun _ => .of_quasiFinite, fun _ => inferInstance⟩

attribute [local instance] TensorProduct.rightAlgebra in
variable (R S T) in
@[stacks 00PO]
/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: [QuasiFinite R S] [QuasiFinite S T]
  statement: QuasiFinite R T
  proof: by
  refine ⟨fun P hP => ?_⟩
  have : Module.Finite (P.Fiber S) ((P.Fiber S) otimes[S] T) :=
    iff_of_isArtinianRing.mp inferInstance
  have : Module.Finite P.ResidueField ((P.Fiber S) otimes[S] T) :=
    .trans (P.Fiber S) _
  let e : P.Fiber S ≃ₐ[S] S otimes[R] P.ResidueField :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e' : (P.Fiber S) otimes[S] T ≃ₐ[R] P.Fiber T :=
((Algebra.TensorProduct.congr e .refl).restrictScalars R).trans
((Algebra.TensorProduct.comm _ _ _).restrictScalars R).trans
    ((Algebra.TensorProduct.cancelBaseChange _ _ T _ _).restrictScalars R).trans
    (Algebra.TensorProduct.comm _ _ _)
  let e'' : (P.Fiber S) otimes[S] T ≃ₐ[P.ResidueField] P.Fiber T :=
    { __ := e', commutes' _ := by simp [e', e] }
  exact .of_surjective e''.toLinearMap e''.surjective

omit [Algebra S T] in

中文:
引理 trans
  条件: [拟有限 R S] [拟有限 S T]
  结论: 拟有限 R T
  证明: by
  refine ⟨fun P hP => ?_⟩
  have : Module.Finite (P.Fiber S) ((P.Fiber S) otimes[S] T) :=
    iff_of_isArtinianRing.mp inferInstance
  have : Module.Finite P.ResidueField ((P.Fiber S) otimes[S] T) :=
    .trans (P.Fiber S) _
  let e : P.Fiber S ≃ₐ[S] S otimes[R] P.ResidueField :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e' : (P.Fiber S) otimes[S] T ≃ₐ[R] P.Fiber T :=
((Algebra.TensorProduct.congr e .refl).restrictScalars R).trans
((Algebra.TensorProduct.comm _ _ _).restrictScalars R).trans
    ((Algebra.TensorProduct.cancelBaseChange _ _ T _ _).restrictScalars R).trans
    (Algebra.TensorProduct.comm _ _ _)
  let e'' : (P.Fiber S) otimes[S] T ≃ₐ[P.ResidueField] P.Fiber T :=
    { __ := e', commutes' _ := by simp [e', e] }
  exact .of_surjective e''.toLinearMap e''.surjective

omit [Algebra S T] in

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, Algebra.TensorProduct.congr, Finite, Module, Module.Finite, P.Fiber, P.ResidueField, ResidueField, TensorProduct, commutes, iff_of_isArtinianRing, iff_of_isArtinianRing.mp, otimes, restrictScalars
-/
lemma trans [QuasiFinite R S] [QuasiFinite S T] : QuasiFinite R T := by
  refine ⟨fun P hP => ?_⟩
  have : Module.Finite (P.Fiber S) ((P.Fiber S) otimes[S] T) :=
    iff_of_isArtinianRing.mp inferInstance
  have : Module.Finite P.ResidueField ((P.Fiber S) otimes[S] T) :=
    .trans (P.Fiber S) _
  let e : P.Fiber S ≃ₐ[S] S otimes[R] P.ResidueField :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e' : (P.Fiber S) otimes[S] T ≃ₐ[R] P.Fiber T :=
((Algebra.TensorProduct.congr e .refl).restrictScalars R).trans
((Algebra.TensorProduct.comm _ _ _).restrictScalars R).trans
    ((Algebra.TensorProduct.cancelBaseChange _ _ T _ _).restrictScalars R).trans
    (Algebra.TensorProduct.comm _ _ _)
  let e'' : (P.Fiber S) otimes[S] T ≃ₐ[P.ResidueField] P.Fiber T :=
    { __ := e', commutes' _ := by simp [e', e] }
  exact .of_surjective e''.toLinearMap e''.surjective

omit [Algebra S T] in
/--
lemma `of_surjective_algHom` / 引理 `of_surjective_algHom`

English:
lemma of_surjective_algHom
  given: [QuasiFinite R S] (f : S ->ₐ[R] T) (hf : Function.Surjective f)
  proof: let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap _ _) hf
  trans R S T

中文:
引理 of_surjective_algHom
  条件: [拟有限 R S] (f : S ->ₐ[R] T) (hf : 函数.满射 f)
  证明: let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap _ _) hf
  trans R S T

Depends on / 依赖: Algebra, Algebra.linearMap, Finite, IsScalarTower, IsScalarTower.of_algebraMap_eq, Module, Module.Finite, comp_algebraMap, f.comp_algebraMap.symm, f.toRingHom.toAlgebra, linearMap, of_algebraMap_eq, of_surjective, toAlgebra, toRingHom
-/
lemma of_surjective_algHom [QuasiFinite R S] (f : S ->ₐ[R] T) (hf : Function.Surjective f) :
    QuasiFinite R T :=
  let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap _ _) hf
  trans R S T

instance (I : Ideal S) [QuasiFinite R S] : QuasiFinite R (S ⧸ I) :=
  of_surjective_algHom (Ideal.Quotient.mkₐ _ _) Ideal.Quotient.mk_surjective

omit [Algebra S T] in
/--
lemma `iff_of_algEquiv` / 引理 `iff_of_algEquiv`

English:
lemma iff_of_algEquiv
  given: (e : S ≃ₐ[R] T)
  proof: ⟨fun _ => .of_surjective_algHom e.toAlgHom e.surjective,
    fun _ => .of_surjective_algHom e.symm.toAlgHom e.symm.surjective⟩

中文:
引理 iff_of_algEquiv
  条件: (e : S ≃ₐ[R] T)
  证明: ⟨fun _ => .of_surjective_algHom e.toAlgHom e.surjective,
    fun _ => .of_surjective_algHom e.symm.toAlgHom e.symm.surjective⟩

Depends on / 依赖: e.surjective, e.symm.surjective, e.symm.toAlgHom, e.toAlgHom, of_surjective_algHom, surjective, toAlgHom
-/
lemma iff_of_algEquiv (e : S ≃ₐ[R] T) :
    Algebra.QuasiFinite R S ↔ Algebra.QuasiFinite R T :=
  ⟨fun _ => .of_surjective_algHom e.toAlgHom e.surjective,
    fun _ => .of_surjective_algHom e.symm.toAlgHom e.symm.surjective⟩

/--
lemma `of_isLocalization` / 引理 `of_isLocalization`

English:
lemma of_isLocalization
  given: (M : Submonoid S) [IsLocalization M T] [QuasiFinite R S]
  proof: letI : QuasiFinite S T := by
    refine ⟨fun P hP => .of_surjective (Algebra.linearMap P.ResidueField (P.Fiber T)) ?_⟩
    rw [← LinearMap.coe_restrictScalars (R := S)]; rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← TensorProduct.span_tmul_eq_top]; rw [Submodule.span_le]
    rintro _ ⟨p, s, rfl⟩
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
    use s • p / algebraMap _ _ t.1
    apply ((IsLocalization.map_units T t).map
      Algebra.TensorProduct.includeRight).mul_left_injective
    by_cases ht : algebraMap _ P.ResidueField t.1 = 0
    · simp [ht]
    trans (s • p) otimesₜ[S] 1
    · simp [div_mul_cancel₀ _ ht]
    · dsimp; simp [Algebra.algebraMap_eq_smul_one, smul_tmul]
  trans R S T

中文:
引理 of_isLocalization
  条件: (M : 子幺半群 S) [是Localization M T] [拟有限 R S]
  证明: letI : QuasiFinite S T := by
    refine ⟨fun P hP => .of_surjective (Algebra.linearMap P.ResidueField (P.Fiber T)) ?_⟩
    rw [← LinearMap.coe_restrictScalars (R := S)]; rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← TensorProduct.span_tmul_eq_top]; rw [Submodule.span_le]
    rintro _ ⟨p, s, rfl⟩
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
    use s • p / algebraMap _ _ t.1
    apply ((IsLocalization.map_units T t).map
      Algebra.TensorProduct.includeRight).mul_left_injective
    by_cases ht : algebraMap _ P.ResidueField t.1 = 0
    · simp [ht]
    trans (s • p) otimesₜ[S] 1
    · simp [div_mul_cancel₀ _ ht]
    · dsimp; simp [Algebra.algebraMap_eq_smul_one, smul_tmul]
  trans R S T

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight, Algebra.linearMap, IsLocalization, IsLocalization.exists_mk, IsLocalization.map_units, LinearMap, LinearMap.coe_restrictScalars, LinearMap.range_eq_top, P.Fiber, P.ResidueField, QuasiFinite, ResidueField, Submodule, Submodule.span_le, TensorProduct, TensorProduct.span_tmul_eq_top, algebraM, algebraMap, coe_restrictScalars
-/
lemma of_isLocalization (M : Submonoid S) [IsLocalization M T] [QuasiFinite R S] :
    QuasiFinite R T :=
  letI : QuasiFinite S T := by
    refine ⟨fun P hP => .of_surjective (Algebra.linearMap P.ResidueField (P.Fiber T)) ?_⟩
    rw [← LinearMap.coe_restrictScalars (R := S)]; rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← TensorProduct.span_tmul_eq_top]; rw [Submodule.span_le]
    rintro _ ⟨p, s, rfl⟩
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
    use s • p / algebraMap _ _ t.1
    apply ((IsLocalization.map_units T t).map
      Algebra.TensorProduct.includeRight).mul_left_injective
    by_cases ht : algebraMap _ P.ResidueField t.1 = 0
    · simp [ht]
    trans (s • p) otimesₜ[S] 1
    · simp [div_mul_cancel₀ _ ht]
    · dsimp; simp [Algebra.algebraMap_eq_smul_one, smul_tmul]
  trans R S T

instance (M : Submonoid S) [QuasiFinite R S] : QuasiFinite R (Localization M) := of_isLocalization M

instance (priority := low) [IsFractionRing R S] : QuasiFinite R S :=
  of_isLocalization (nonZeroDivisors R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiFinite
  signature: R S] (p
  body: .of_quasiFinite

中文:
实例 [拟有限
  签名: R S] (p
  定义体: .of_quasiFinite

Depends on / 依赖: of_quasiFinite
-/
instance [QuasiFinite R S] (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime] :
    Module.Finite p.ResidueField (Localization.AtPrime q) :=
  .of_quasiFinite

instance (P : Ideal S) [P.IsPrime] [QuasiFinite R S] : QuasiFinite R P.ResidueField :=
  .trans _ (S ⧸ P) _

variable (R S T) in
/--
lemma `of_restrictScalars` / 引理 `of_restrictScalars`

English:
lemma of_restrictScalars
  given: [QuasiFinite R T]
  statement: QuasiFinite S T
  proof: by
  refine ⟨fun P hP => ?_⟩
  let f : P.ResidueField otimes[R] T ->ₐ[P.ResidueField] P.Fiber T :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (Algebra.TensorProduct.includeRight.restrictScalars R) fun _ _ => .all _ _
  have hf : Function.Surjective f := by
    rw [← AlgHom.coe_restrictScalars' (R := S)]; rw [← AlgHom.coe_toLinearMap]; rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← TensorProduct.span_tmul_eq_top]; rw [Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a otimesₜ b, by simp [f]⟩
  have : Module.Finite P.ResidueField (P.ResidueField otimes[R] T) := .of_quasiFinite
  exact .of_surjective f.toLinearMap hf

中文:
引理 of_restrictScalars
  条件: [拟有限 R T]
  结论: 拟有限 S T
  证明: by
  refine ⟨fun P hP => ?_⟩
  let f : P.ResidueField otimes[R] T ->ₐ[P.ResidueField] P.Fiber T :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (Algebra.TensorProduct.includeRight.restrictScalars R) fun _ _ => .all _ _
  have hf : Function.Surjective f := by
    rw [← AlgHom.coe_restrictScalars' (R := S)]; rw [← AlgHom.coe_toLinearMap]; rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← TensorProduct.span_tmul_eq_top]; rw [Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a otimesₜ b, by simp [f]⟩
  have : Module.Finite P.ResidueField (P.ResidueField otimes[R] T) := .of_quasiFinite
  exact .of_surjective f.toLinearMap hf

Depends on / 依赖: AlgHom, AlgHom.coe_restrictScalars, AlgHom.coe_toLinearMap, Algebra, Algebra.TensorProduct.includeRight.restrictScalars, Algebra.TensorProduct.lift, Algebra.ofId, Function, Function.Surjective, LinearMap, LinearMap.range_eq_top, P.Fiber, P.ResidueField, ResidueField, Submodule, Submodule.span_le, Surjective, TensorProduct, TensorProduct.span_tmul_eq_top, coe_restrictScalars
-/
lemma of_restrictScalars [QuasiFinite R T] : QuasiFinite S T := by
  refine ⟨fun P hP => ?_⟩
  let f : P.ResidueField otimes[R] T ->ₐ[P.ResidueField] P.Fiber T :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (Algebra.TensorProduct.includeRight.restrictScalars R) fun _ _ => .all _ _
  have hf : Function.Surjective f := by
    rw [← AlgHom.coe_restrictScalars' (R := S)]; rw [← AlgHom.coe_toLinearMap]; rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← TensorProduct.span_tmul_eq_top]; rw [Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a otimesₜ b, by simp [f]⟩
  have : Module.Finite P.ResidueField (P.ResidueField otimes[R] T) := .of_quasiFinite
  exact .of_surjective f.toLinearMap hf

variable (R S) in
/--
lemma `discreteTopology_primeSpectrum` / 引理 `discreteTopology_primeSpectrum`

English:
lemma discreteTopology_primeSpectrum
  given: [DiscreteTopology (PrimeSpectrum R)] [QuasiFinite R S]
  proof: isDiscrete_univ_iff.mp
    (isDiscrete_comap_preimage (R := R) (S := S) (isDiscrete_univ_iff.mpr ‹_›))

中文:
引理 discreteTopology_primeSpectrum
  条件: [离散拓扑 (素谱 R)] [拟有限 R S]
  证明: isDiscrete_univ_iff.mp
    (isDiscrete_comap_preimage (R := R) (S := S) (isDiscrete_univ_iff.mpr ‹_›))

Depends on / 依赖: isDiscrete_comap_preimage, isDiscrete_univ_iff, isDiscrete_univ_iff.mp, isDiscrete_univ_iff.mpr
-/
lemma discreteTopology_primeSpectrum [DiscreteTopology (PrimeSpectrum R)] [QuasiFinite R S] :
    DiscreteTopology (PrimeSpectrum S) :=
  isDiscrete_univ_iff.mp
    (isDiscrete_comap_preimage (R := R) (S := S) (isDiscrete_univ_iff.mpr ‹_›))

variable (R S) in
/--
lemma `finite_primeSpectrum` / 引理 `finite_primeSpectrum`

English:
lemma finite_primeSpectrum
  given: [Finite (PrimeSpectrum R)] [QuasiFinite R S]
  proof: Set.finite_univ_iff.mp
    (finite_comap_preimage (Set.finite_univ (α := PrimeSpectrum R)))

omit [Algebra S T] in

中文:
引理 finite_primeSpectrum
  条件: [有限 (素谱 R)] [拟有限 R S]
  证明: Set.finite_univ_iff.mp
    (finite_comap_preimage (Set.finite_univ (α := PrimeSpectrum R)))

omit [Algebra S T] in

Depends on / 依赖: PrimeSpectrum, Set.finite_univ, Set.finite_univ_iff.mp, finite_comap_preimage, finite_univ, finite_univ_iff
-/
lemma finite_primeSpectrum [Finite (PrimeSpectrum R)] [QuasiFinite R S] :
    Finite (PrimeSpectrum S) :=
  Set.finite_univ_iff.mp
    (finite_comap_preimage (Set.finite_univ (α := PrimeSpectrum R)))

omit [Algebra S T] in
/--
lemma `of_forall_exists_mul_mem_range` / 引理 `of_forall_exists_mul_mem_range`

English:
lemma of_forall_exists_mul_mem_range
  statement: [QuasiFinite R S] (f : S ->ₐ[R] T)
  proof: by
  let φ : Localization ((IsUnit.submonoid T).comap f) ->ₐ[R] T :=
    IsLocalization.liftAlgHom (M := (IsUnit.submonoid T).comap f) (f := f)
      (by simp [IsUnit.mem_submonoid_iff])
  suffices Function.Surjective φ from .of_surjective_algHom φ this
  intro x
  obtain ⟨s, hs, t, ht⟩ := H x
  refine ⟨IsLocalization.mk' (M := (IsUnit.submonoid T).comap f) _ t ⟨s, hs⟩, ?_⟩
  simpa [φ, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]

omit [Algebra S T] in

中文:
引理 of_对任意_存在_mul_mem_range
  结论: [拟有限 R S] (f : S ->ₐ[R] T)
  证明: by
  let φ : Localization ((IsUnit.submonoid T).comap f) ->ₐ[R] T :=
    IsLocalization.liftAlgHom (M := (IsUnit.submonoid T).comap f) (f := f)
      (by simp [IsUnit.mem_submonoid_iff])
  suffices Function.Surjective φ from .of_surjective_algHom φ this
  intro x
  obtain ⟨s, hs, t, ht⟩ := H x
  refine ⟨IsLocalization.mk' (M := (IsUnit.submonoid T).comap f) _ t ⟨s, hs⟩, ?_⟩
  simpa [φ, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]

omit [Algebra S T] in

Depends on / 依赖: Function, Function.Surjective, IsLocalization, IsLocalization.liftAlgHom, IsLocalization.lift_mk, IsLocalization.mk, IsUnit, IsUnit.coe_liftRight, IsUnit.mem_submonoid_iff, IsUnit.submonoid, Localization, Surjective, Units.mul_inv_eq_iff_eq_mul, coe_liftRight, liftAlgHom, lift_mk, mem_submonoid_iff, mul_inv_eq_iff_eq_mul, of_surjective_algHom, submonoid
-/
lemma of_forall_exists_mul_mem_range [QuasiFinite R S] (f : S ->ₐ[R] T)
    (H : forall x : T, exists s : S, IsUnit (f s) ∧ x * f s in f.range) :
    QuasiFinite R T := by
  let φ : Localization ((IsUnit.submonoid T).comap f) ->ₐ[R] T :=
    IsLocalization.liftAlgHom (M := (IsUnit.submonoid T).comap f) (f := f)
      (by simp [IsUnit.mem_submonoid_iff])
  suffices Function.Surjective φ from .of_surjective_algHom φ this
  intro x
  obtain ⟨s, hs, t, ht⟩ := H x
  refine ⟨IsLocalization.mk' (M := (IsUnit.submonoid T).comap f) _ t ⟨s, hs⟩, ?_⟩
  simpa [φ, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]

omit [Algebra S T] in
/--
lemma `eq_of_le_of_under_eq` / 引理 `eq_of_le_of_under_eq`

English:
lemma eq_of_le_of_under_eq
  statement: [QuasiFinite R S] (P Q : Ideal S) [P.IsPrime] [Q.IsPrime]
  proof: congr($((isDiscrete_comap_preimage_singleton ⟨_, inferInstance⟩).eq_of_specializes
    (a := ⟨P, ‹_›⟩) (b := ⟨Q, ‹_›⟩) (by simpa [← PrimeSpectrum.le_iff_specializes]) rfl
    (PrimeSpectrum.ext h₂.symm)).1)

中文:
引理 eq_of_le_of_under_eq
  结论: [拟有限 R S] (P Q : 理想 S) [P.是素] [Q.是素]
  证明: congr($((isDiscrete_comap_preimage_singleton ⟨_, inferInstance⟩).eq_of_specializes
    (a := ⟨P, ‹_›⟩) (b := ⟨Q, ‹_›⟩) (by simpa [← PrimeSpectrum.le_iff_specializes]) rfl
    (PrimeSpectrum.ext h₂.symm)).1)

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.ext, PrimeSpectrum.le_iff_specializes, eq_of_specializes, isDiscrete_comap_preimage_singleton, le_iff_specializes
-/
lemma eq_of_le_of_under_eq [QuasiFinite R S] (P Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (h₁ : P <= Q) (h₂ : P.under R = Q.under R) : P = Q :=
  congr($((isDiscrete_comap_preimage_singleton ⟨_, inferInstance⟩).eq_of_specializes
    (a := ⟨P, ‹_›⟩) (b := ⟨Q, ‹_›⟩) (by simpa [← PrimeSpectrum.le_iff_specializes]) rfl
    (PrimeSpectrum.ext h₂.symm)).1)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiFinite
  signature: R S] (P
  body: have : QuasiFinite P.ResidueField Q.ResidueField := .of_restrictScalars R _ _
  .of_quasiFinite

中文:
实例 [拟有限
  签名: R S] (P
  定义体: have : QuasiFinite P.ResidueField Q.ResidueField := .of_restrictScalars R _ _
  .of_quasiFinite

Depends on / 依赖: P.ResidueField, Q.ResidueField, QuasiFinite, ResidueField, of_quasiFinite, of_restrictScalars
-/
instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P]
    [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)]
    [Localization.AtPrime.IsLiesOverAlgebra P Q] :
    Module.Finite P.ResidueField Q.ResidueField :=
  have : QuasiFinite P.ResidueField Q.ResidueField := .of_restrictScalars R _ _
  .of_quasiFinite

section Finite

/--
lemma `iff_finite_comap_preimage_singleton` / 引理 `iff_finite_comap_preimage_singleton`

English:
lemma iff_finite_comap_preimage_singleton
  given: [FiniteType R S]
  proof: by
  refine ⟨fun H _ => finite_comap_preimage_singleton _, fun H => ⟨fun P _ => ?_⟩⟩
  rw [Module.finite_iff_isArtinianRing]; rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  have : IsJacobsonRing (P.Fiber S) := isJacobsonRing_of_finiteType (A := P.ResidueField)
  have : Finite (PrimeSpectrum (P.Fiber S)) :=
    (PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩).finite_iff.mp (H ⟨P, ‹_›⟩)
  exact ⟨Algebra.FiniteType.isNoetherianRing P.ResidueField _,
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right⟩

中文:
引理 iff_finite_comap_preimage_singleton
  条件: [有限型 R S]
  证明: by
  refine ⟨fun H _ => finite_comap_preimage_singleton _, fun H => ⟨fun P _ => ?_⟩⟩
  rw [Module.finite_iff_isArtinianRing]; rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  have : IsJacobsonRing (P.Fiber S) := isJacobsonRing_of_finiteType (A := P.ResidueField)
  have : Finite (PrimeSpectrum (P.Fiber S)) :=
    (PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩).finite_iff.mp (H ⟨P, ‹_›⟩)
  exact ⟨Algebra.FiniteType.isNoetherianRing P.ResidueField _,
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right⟩

Depends on / 依赖: Algebra, Algebra.FiniteType.isNoetherianRing, Finite, FiniteType, IsJacobsonRing, Module, Module.finite_iff_isArtinianRing, P.Fiber, P.ResidueField, PrimeSpectrum, PrimeSpectrum.discreteTopology_iff_finite_and_krull, PrimeSpectrum.preimageEquivFiber, ResidueField, discreteTopology_iff_finite_and_krull, finite_comap_preimage_singleton, finite_iff, finite_iff.mp, finite_iff_isArtinianRing, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero, isJacobsonRing_of_finiteType
-/
lemma iff_finite_comap_preimage_singleton [FiniteType R S] :
    QuasiFinite R S ↔ forall x, (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}).Finite := by
  refine ⟨fun H _ => finite_comap_preimage_singleton _, fun H => ⟨fun P _ => ?_⟩⟩
  rw [Module.finite_iff_isArtinianRing]; rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  have : IsJacobsonRing (P.Fiber S) := isJacobsonRing_of_finiteType (A := P.ResidueField)
  have : Finite (PrimeSpectrum (P.Fiber S)) :=
    (PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩).finite_iff.mp (H ⟨P, ‹_›⟩)
  exact ⟨Algebra.FiniteType.isNoetherianRing P.ResidueField _,
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `iff_finite_primesOver` / 引理 `iff_finite_primesOver`

English:
lemma iff_finite_primesOver
  given: [FiniteType R S]
  proof: by
  rw [iff_finite_comap_preimage_singleton]; rw [(PrimeSpectrum.equivSubtype R).forall_congr_left]; rw [Subtype.forall]
  refine forall₂_congr fun I hI => ?_
  rw [← Set.finite_image_iff (Function.Injective.injOn fun _ _ => PrimeSpectrum.ext)]
  congr!
  ext J
  simp [(PrimeSpectrum.equivSubtype S).exists_congr_left, PrimeSpectrum.ext_iff, eq_comm,
    PrimeSpectrum.equivSubtype, Ideal.primesOver, and_comm, Ideal.liesOver_iff, Ideal.under]

中文:
引理 iff_finite_primesOver
  条件: [有限型 R S]
  证明: by
  rw [iff_finite_comap_preimage_singleton]; rw [(PrimeSpectrum.equivSubtype R).forall_congr_left]; rw [Subtype.forall]
  refine forall₂_congr fun I hI => ?_
  rw [← Set.finite_image_iff (Function.Injective.injOn fun _ _ => PrimeSpectrum.ext)]
  congr!
  ext J
  simp [(PrimeSpectrum.equivSubtype S).exists_congr_left, PrimeSpectrum.ext_iff, eq_comm,
    PrimeSpectrum.equivSubtype, Ideal.primesOver, and_comm, Ideal.liesOver_iff, Ideal.under]

Depends on / 依赖: Function, Function.Injective.injOn, Ideal.liesOver_iff, Ideal.primesOver, Ideal.under, Injective, PrimeSpectrum, PrimeSpectrum.equivSubtype, PrimeSpectrum.ext, PrimeSpectrum.ext_iff, Set.finite_image_iff, Subtype, Subtype.forall, and_comm, eq_comm, equivSubtype, exists_congr_left, ext_iff, finite_image_iff, forall_congr_left
-/
lemma iff_finite_primesOver [FiniteType R S] :
    QuasiFinite R S ↔ forall I : Ideal R, I.IsPrime -> (I.primesOver S).Finite := by
  rw [iff_finite_comap_preimage_singleton]; rw [(PrimeSpectrum.equivSubtype R).forall_congr_left]; rw [Subtype.forall]
  refine forall₂_congr fun I hI => ?_
  rw [← Set.finite_image_iff (Function.Injective.injOn fun _ _ => PrimeSpectrum.ext)]
  congr!
  ext J
  simp [(PrimeSpectrum.equivSubtype S).exists_congr_left, PrimeSpectrum.ext_iff, eq_comm,
    PrimeSpectrum.equivSubtype, Ideal.primesOver, and_comm, Ideal.liesOver_iff, Ideal.under]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `of_isIntegral_of_finiteType` / 引理 `of_isIntegral_of_finiteType`

English:
lemma of_isIntegral_of_finiteType
  statement: [Algebra.IsIntegral R S] [Algebra.FiniteType R T]
  proof: by
  let A := Algebra.adjoin R {s}
  let sA : A := ⟨s, Algebra.subset_adjoin (by simp)⟩
  let f : Localization.Away sA ->+* T := IsLocalization.Away.lift sA (g := algebraMap _ _)
    (IsLocalization.Away.algebraMap_isUnit s)
  let := f.toAlgebra
  let : Algebra A (Localization.Away sA) := OreLocalization.instAlgebra
  let : SMul A (Localization.Away sA) := Algebra.toSMul
  let : MulAction A (Localization.Away sA) := Algebra.toModule.toDistribMulAction.toMulAction
  have : IsScalarTower R A (Localization.Away sA) := OreLocalization.instIsScalarTower
  have : IsScalarTower A (Localization.Away sA) T :=
    .of_algebraMap_eq (by simp [f, RingHom.algebraMap_toAlgebra, A])
  have : IsScalarTower R (Localization.Away sA) T := .to₁₃₄ R A (Localization.Away sA) T
  have : Algebra.IsIntegral (Localization.Away sA) T := by
    refine ⟨fun x => ?_⟩
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    have : _root_.IsIntegral (Localization.Away sA) (algebraMap S T x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).algebraMap.tower_top
    convert! this.smul (Localization.Away.invSelf sA ^ n)
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    simp only [map_pow, Algebra.smul_mul_assoc]
    trans (sA • Localization.Away.invSelf sA) ^ n • (algebraMap S T x)
    · simp [Algebra.smul_def, -map_pow, Localization.Away.invSelf, Localization.mk_eq_mk']
    · simp only [Algebra.smul_def, map_pow, map_mul, mul_pow,
        ← IsScalarTower.algebraMap_apply, Subalgebra.algebraMap_def, sA]
      ring
  have : Module.Finite (Localization.Away sA) T :=
    have : Algebra.FiniteType (Localization.Away sA) T := .of_restrictScalars_finiteType R _ _
    Algebra.IsIntegral.finite
  have : Module.Finite R A :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral _)
  have : Algebra.QuasiFinite R (Localization.Away sA) := .of_isLocalization (.powers sA)
  exact .trans _ (Localization.Away sA) _

中文:
引理 of_is整数egral_of_finiteType
  结论: [代数.是整 R S] [代数.有限型 R T]
  证明: by
  let A := Algebra.adjoin R {s}
  let sA : A := ⟨s, Algebra.subset_adjoin (by simp)⟩
  let f : Localization.Away sA ->+* T := IsLocalization.Away.lift sA (g := algebraMap _ _)
    (IsLocalization.Away.algebraMap_isUnit s)
  let := f.toAlgebra
  let : Algebra A (Localization.Away sA) := OreLocalization.instAlgebra
  let : SMul A (Localization.Away sA) := Algebra.toSMul
  let : MulAction A (Localization.Away sA) := Algebra.toModule.toDistribMulAction.toMulAction
  have : IsScalarTower R A (Localization.Away sA) := OreLocalization.instIsScalarTower
  have : IsScalarTower A (Localization.Away sA) T :=
    .of_algebraMap_eq (by simp [f, RingHom.algebraMap_toAlgebra, A])
  have : IsScalarTower R (Localization.Away sA) T := .to₁₃₄ R A (Localization.Away sA) T
  have : Algebra.IsIntegral (Localization.Away sA) T := by
    refine ⟨fun x => ?_⟩
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    have : _root_.IsIntegral (Localization.Away sA) (algebraMap S T x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).algebraMap.tower_top
    convert! this.smul (Localization.Away.invSelf sA ^ n)
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    simp only [map_pow, Algebra.smul_mul_assoc]
    trans (sA • Localization.Away.invSelf sA) ^ n • (algebraMap S T x)
    · simp [Algebra.smul_def, -map_pow, Localization.Away.invSelf, Localization.mk_eq_mk']
    · simp only [Algebra.smul_def, map_pow, map_mul, mul_pow,
        ← IsScalarTower.algebraMap_apply, Subalgebra.algebraMap_def, sA]
      ring
  have : Module.Finite (Localization.Away sA) T :=
    have : Algebra.FiniteType (Localization.Away sA) T := .of_restrictScalars_finiteType R _ _
    Algebra.IsIntegral.finite
  have : Module.Finite R A :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral _)
  have : Algebra.QuasiFinite R (Localization.Away sA) := .of_isLocalization (.powers sA)
  exact .trans _ (Localization.Away sA) _

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, Algebra.toModule.toDistribMulAction.toMulAction, Algebra.toSMul, IsLocalization, IsLocalization.Away.algebraMap_isUnit, IsLocalization.Away.lift, IsScalarTower, Localization, Localization.Away, MulAction, OreLocalization, OreLocalization.instAlgebra, adjoin, algebraMap, algebraMap_isUnit, f.toAlgebra, instAlgebra, subset_adjoin
-/
lemma of_isIntegral_of_finiteType [Algebra.IsIntegral R S] [Algebra.FiniteType R T]
    (s : S) [IsLocalization.Away s T] : Algebra.QuasiFinite R T := by
  let A := Algebra.adjoin R {s}
  let sA : A := ⟨s, Algebra.subset_adjoin (by simp)⟩
  let f : Localization.Away sA ->+* T := IsLocalization.Away.lift sA (g := algebraMap _ _)
    (IsLocalization.Away.algebraMap_isUnit s)
  let := f.toAlgebra
  let : Algebra A (Localization.Away sA) := OreLocalization.instAlgebra
  let : SMul A (Localization.Away sA) := Algebra.toSMul
  let : MulAction A (Localization.Away sA) := Algebra.toModule.toDistribMulAction.toMulAction
  have : IsScalarTower R A (Localization.Away sA) := OreLocalization.instIsScalarTower
  have : IsScalarTower A (Localization.Away sA) T :=
    .of_algebraMap_eq (by simp [f, RingHom.algebraMap_toAlgebra, A])
  have : IsScalarTower R (Localization.Away sA) T := .to₁₃₄ R A (Localization.Away sA) T
  have : Algebra.IsIntegral (Localization.Away sA) T := by
    refine ⟨fun x => ?_⟩
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    have : _root_.IsIntegral (Localization.Away sA) (algebraMap S T x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).algebraMap.tower_top
    convert! this.smul (Localization.Away.invSelf sA ^ n)
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    simp only [map_pow, Algebra.smul_mul_assoc]
    trans (sA • Localization.Away.invSelf sA) ^ n • (algebraMap S T x)
    · simp [Algebra.smul_def, -map_pow, Localization.Away.invSelf, Localization.mk_eq_mk']
    · simp only [Algebra.smul_def, map_pow, map_mul, mul_pow,
        ← IsScalarTower.algebraMap_apply, Subalgebra.algebraMap_def, sA]
      ring
  have : Module.Finite (Localization.Away sA) T :=
    have : Algebra.FiniteType (Localization.Away sA) T := .of_restrictScalars_finiteType R _ _
    Algebra.IsIntegral.finite
  have : Module.Finite R A :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral _)
  have : Algebra.QuasiFinite R (Localization.Away sA) := .of_isLocalization (.powers sA)
  exact .trans _ (Localization.Away sA) _

end Finite

end QuasiFinite

section QuasiFiniteAt

variable (R) in
/--
Definition of `QuasiFiniteAt` / `QuasiFiniteAt` 的定义

English:
abbreviation QuasiFiniteAt
  signature: (p : Ideal S) [p.IsPrime]
  body: QuasiFinite R (Localization.AtPrime p)

中文:
缩写 QuasiFiniteAt
  签名: (p : 理想 S) [p.是素]
  定义体: QuasiFinite R (Localization.AtPrime p)

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, QuasiFinite
-/
abbrev QuasiFiniteAt (p : Ideal S) [p.IsPrime] : Prop :=
  QuasiFinite R (Localization.AtPrime p)

/--
lemma `QuasiFiniteAt.baseChange` / 引理 `QuasiFiniteAt.baseChange`

English:
lemma QuasiFiniteAt.baseChange
  statement: (p : Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
  proof: by
  let f : A otimes[R] Localization.AtPrime p ->ₐ[A] Localization.AtPrime q :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨Localization.localRingHom _ _ _ hq, by
      simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime p),
        IsScalarTower.algebraMap_apply R (A otimes[R] S) (Localization.AtPrime q)]⟩ fun _ _ => .all _ _
  let g : A otimes[R] S ->ₐ[A] A otimes[R] Localization.AtPrime p :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  have : f.comp g = IsScalarTower.toAlgHom _ _ _ := by ext; simp [f, g]
  replace this (x : _) : f (g x) = algebraMap _ _ x := DFunLike.congr_fun this x
  refine .of_forall_exists_mul_mem_range f fun x => ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  refine ⟨g s, this s ▸ IsLocalization.map_units _ ⟨s, hs⟩, ?_⟩
  rw [this]; rw [IsLocalization.mk'_spec_mk]
  exact ⟨g x, this x⟩

中文:
引理 QuasiFiniteAt.baseChange
  结论: (p : 理想 S) [p.是素] [QuasiFiniteAt R p]
  证明: by
  let f : A otimes[R] Localization.AtPrime p ->ₐ[A] Localization.AtPrime q :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨Localization.localRingHom _ _ _ hq, by
      simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime p),
        IsScalarTower.algebraMap_apply R (A otimes[R] S) (Localization.AtPrime q)]⟩ fun _ _ => .all _ _
  let g : A otimes[R] S ->ₐ[A] A otimes[R] Localization.AtPrime p :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  have : f.comp g = IsScalarTower.toAlgHom _ _ _ := by ext; simp [f, g]
  replace this (x : _) : f (g x) = algebraMap _ _ x := DFunLike.congr_fun this x
  refine .of_forall_exists_mul_mem_range f fun x => ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  refine ⟨g s, this s ▸ IsLocalization.map_units _ ⟨s, hs⟩, ?_⟩
  rw [this]; rw [IsLocalization.mk'_spec_mk]
  exact ⟨g x, this x⟩

Depends on / 依赖: Algebra, Algebra.TensorProduct.lift, Algebra.TensorProduct.map, Algebra.ofId, AtPrime, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.toAlgH, IsScalarTower.toAlgHom, Localization, Localization.AtPrime, Localization.localRingHom, TensorProduct, algebraMap_apply, f.comp, localRingHom, otimes, toAlgH, toAlgHom
-/
lemma QuasiFiniteAt.baseChange (p : Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
    {A : Type*} [CommRing A] [Algebra R A] (q : Ideal (A otimes[R] S)) [q.IsPrime]
    (hq : p = q.comap Algebra.TensorProduct.includeRight.toRingHom) :
    QuasiFiniteAt A q := by
  let f : A otimes[R] Localization.AtPrime p ->ₐ[A] Localization.AtPrime q :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨Localization.localRingHom _ _ _ hq, by
      simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime p),
        IsScalarTower.algebraMap_apply R (A otimes[R] S) (Localization.AtPrime q)]⟩ fun _ _ => .all _ _
  let g : A otimes[R] S ->ₐ[A] A otimes[R] Localization.AtPrime p :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  have : f.comp g = IsScalarTower.toAlgHom _ _ _ := by ext; simp [f, g]
  replace this (x : _) : f (g x) = algebraMap _ _ x := DFunLike.congr_fun this x
  refine .of_forall_exists_mul_mem_range f fun x => ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  refine ⟨g s, this s ▸ IsLocalization.map_units _ ⟨s, hs⟩, ?_⟩
  rw [this]; rw [IsLocalization.mk'_spec_mk]
  exact ⟨g x, this x⟩

set_option backward.isDefEq.respectTransparency false in
omit [Algebra S T] in
/--
lemma `QuasiFiniteAt.of_surjectiveOnStalks` / 引理 `QuasiFiniteAt.of_surjectiveOnStalks`

English:
lemma QuasiFiniteAt.of_surjectiveOnStalks
  statement: (p : Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
  proof: by
  subst hq
  refine .of_surjective_algHom ⟨Localization.localRingHom _ q f.toRingHom rfl, ?_⟩ (hf q ‹_›)
  simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime (q.comap _)),
    IsScalarTower.algebraMap_apply R T (Localization.AtPrime _)]

中文:
引理 QuasiFiniteAt.of_surjectiveOnStalks
  结论: (p : 理想 S) [p.是素] [QuasiFiniteAt R p]
  证明: by
  subst hq
  refine .of_surjective_algHom ⟨Localization.localRingHom _ q f.toRingHom rfl, ?_⟩ (hf q ‹_›)
  simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime (q.comap _)),
    IsScalarTower.algebraMap_apply R T (Localization.AtPrime _)]

Depends on / 依赖: AtPrime, IsScalarTower, IsScalarTower.algebraMap_apply, Localization, Localization.AtPrime, Localization.localRingHom, algebraMap_apply, f.toRingHom, localRingHom, of_surjective_algHom, q.comap, toRingHom
-/
lemma QuasiFiniteAt.of_surjectiveOnStalks (p : Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
    (f : S ->ₐ[R] T) (hf : f.SurjectiveOnStalks) (q : Ideal T) [q.IsPrime]
    (hq : p = q.comap f.toRingHom) :
    QuasiFiniteAt R q := by
  subst hq
  refine .of_surjective_algHom ⟨Localization.localRingHom _ q f.toRingHom rfl, ?_⟩ (hf q ‹_›)
  simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime (q.comap _)),
    IsScalarTower.algebraMap_apply R T (Localization.AtPrime _)]

/--
lemma `QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver` / 引理 `QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver`

English:
lemma QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver
  statement: (p : Ideal S) [p.IsPrime]
  proof: .of_surjectiveOnStalks p (IsScalarTower.toAlgHom R S T) hf _ (q.over_def p)

中文:
引理 QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver
  结论: (p : 理想 S) [p.是素]
  证明: .of_surjectiveOnStalks p (IsScalarTower.toAlgHom R S T) hf _ (q.over_def p)

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, of_surjectiveOnStalks, over_def, q.over_def, toAlgHom
-/
lemma QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver (p : Ideal S) [p.IsPrime]
    [QuasiFiniteAt R p] (hf : (algebraMap S T).SurjectiveOnStalks) (q : Ideal T) [q.IsPrime]
    [q.LiesOver p] : QuasiFiniteAt R q :=
  .of_surjectiveOnStalks p (IsScalarTower.toAlgHom R S T) hf _ (q.over_def p)

/--
Instance `QuasiFiniteAt.comap_algEquiv` / 实例 `QuasiFiniteAt.comap_algEquiv`

English:
instance QuasiFiniteAt.comap_algEquiv
  signature: (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
  body: .of_surjectiveOnStalks p f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) _ (by ext; simp)

omit [Algebra S T] in

中文:
实例 QuasiFiniteAt.comap_algEquiv
  签名: (p : 理想 S) [p.是素] [代数.QuasiFiniteAt R p]
  定义体: .of_surjectiveOnStalks p f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) _ (by ext; simp)

omit [Algebra S T] in

Depends on / 依赖: RingHom, RingHom.surjectiveOnStalks_of_surjective, f.symm.surjective, f.symm.toAlgHom, of_surjectiveOnStalks, surjective, surjectiveOnStalks_of_surjective, toAlgHom
-/
instance QuasiFiniteAt.comap_algEquiv (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
    (f : T ≃ₐ[R] S) : QuasiFiniteAt R (p.comap f.toRingHom) :=
  .of_surjectiveOnStalks p f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) _ (by ext; simp)

omit [Algebra S T] in
/--
lemma `QuasiFiniteAt.of_le` / 引理 `QuasiFiniteAt.of_le`

English:
lemma QuasiFiniteAt.of_le
  statement: {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
  proof: by
  let f : Localization.AtPrime Q ->ₐ[R] Localization.AtPrime P :=
IsLocalization.liftAlgHom (M := Q.primeCompl) (f := IsScalarTower.toAlgHom _ _ _) by
      simp only [IsScalarTower.coe_toAlgHom', Subtype.forall, Ideal.mem_primeCompl_iff]
      exact fun a ha => IsLocalization.map_units (M := P.primeCompl) _ ⟨a, fun h => ha (h₁ h)⟩
  refine .of_forall_exists_mul_mem_range f fun x => ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa [f] using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp [f]⟩

omit [Algebra S T] in

中文:
引理 QuasiFiniteAt.of_le
  结论: {P Q : 理想 S} [P.是素] [Q.是素]
  证明: by
  let f : Localization.AtPrime Q ->ₐ[R] Localization.AtPrime P :=
IsLocalization.liftAlgHom (M := Q.primeCompl) (f := IsScalarTower.toAlgHom _ _ _) by
      simp only [IsScalarTower.coe_toAlgHom', Subtype.forall, Ideal.mem_primeCompl_iff]
      exact fun a ha => IsLocalization.map_units (M := P.primeCompl) _ ⟨a, fun h => ha (h₁ h)⟩
  refine .of_forall_exists_mul_mem_range f fun x => ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa [f] using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp [f]⟩

omit [Algebra S T] in

Depends on / 依赖: AtPrime, Ideal.mem_primeCompl_iff, IsLocali, IsLocalization, IsLocalization.exists_mk, IsLocalization.liftAlgHom, IsLocalization.map_units, IsScalarTower, IsScalarTower.coe_toAlgHom, IsScalarTower.toAlgHom, Localization, Localization.AtPrime, P.primeCompl, Q.primeCompl, Subtype, Subtype.forall, algebraMap, coe_toAlgHom, exists_mk, liftAlgHom
-/
lemma QuasiFiniteAt.of_le {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
    (h₁ : P <= Q) [QuasiFiniteAt R Q] :
    QuasiFiniteAt R P := by
  let f : Localization.AtPrime Q ->ₐ[R] Localization.AtPrime P :=
IsLocalization.liftAlgHom (M := Q.primeCompl) (f := IsScalarTower.toAlgHom _ _ _) by
      simp only [IsScalarTower.coe_toAlgHom', Subtype.forall, Ideal.mem_primeCompl_iff]
      exact fun a ha => IsLocalization.map_units (M := P.primeCompl) _ ⟨a, fun h => ha (h₁ h)⟩
  refine .of_forall_exists_mul_mem_range f fun x => ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa [f] using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp [f]⟩

omit [Algebra S T] in
/--
lemma `QuasiFiniteAt.eq_of_le_of_under_eq` / 引理 `QuasiFiniteAt.eq_of_le_of_under_eq`

English:
lemma QuasiFiniteAt.eq_of_le_of_under_eq
  statement: {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
  proof: by
  have := Q.isPrime_map_of_isLocalizationAtPrime h₁ (S := Localization.AtPrime Q)
  have H := QuasiFinite.eq_of_le_of_under_eq (R := R)
    (Ideal.map (algebraMap S (Localization.AtPrime Q)) P) _
    (IsLocalRing.le_maximalIdeal_of_isPrime _) (by
      convert! h₂ <;> rw [← Ideal.under_under (B := S)]
      · rw [Q.under_map_of_isLocalizationAtPrime h₁]
      · rw [Localization.AtPrime.under_maximalIdeal])
  rw [← Localization.AtPrime.under_maximalIdeal (I := Q)]; rw [← H]; rw [Q.under_map_of_isLocalizationAtPrime h₁]

中文:
引理 QuasiFiniteAt.eq_of_le_of_under_eq
  结论: {P Q : 理想 S} [P.是素] [Q.是素]
  证明: by
  have := Q.isPrime_map_of_isLocalizationAtPrime h₁ (S := Localization.AtPrime Q)
  have H := QuasiFinite.eq_of_le_of_under_eq (R := R)
    (Ideal.map (algebraMap S (Localization.AtPrime Q)) P) _
    (IsLocalRing.le_maximalIdeal_of_isPrime _) (by
      convert! h₂ <;> rw [← Ideal.under_under (B := S)]
      · rw [Q.under_map_of_isLocalizationAtPrime h₁]
      · rw [Localization.AtPrime.under_maximalIdeal])
  rw [← Localization.AtPrime.under_maximalIdeal (I := Q)]; rw [← H]; rw [Q.under_map_of_isLocalizationAtPrime h₁]

Depends on / 依赖: AtPrime, Ideal.map, Ideal.under_under, IsLocalRing, IsLocalRing.le_maximalIdeal_of_isPrime, Localization, Localization.AtPrime, Localization.AtPrime.under_maximalIdeal, Q.isPrime_map_of_isLocalizationAtPrime, Q.under_map_of_isLocalizationAtPrime, QuasiFinite, QuasiFinite.eq_of_le_of_under_eq, algebraMap, convert, eq_of_le_of_under_eq, isPrime_map_of_isLocalizationAtPrime, le_maximalIdeal_of_isPrime, under_map_of_isLocalizationAtPrime, under_maximalIdeal, under_under
-/
lemma QuasiFiniteAt.eq_of_le_of_under_eq {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
    (h₁ : P <= Q) (h₂ : P.under R = Q.under R) [QuasiFiniteAt R Q] :
    P = Q := by
  have := Q.isPrime_map_of_isLocalizationAtPrime h₁ (S := Localization.AtPrime Q)
  have H := QuasiFinite.eq_of_le_of_under_eq (R := R)
    (Ideal.map (algebraMap S (Localization.AtPrime Q)) P) _
    (IsLocalRing.le_maximalIdeal_of_isPrime _) (by
      convert! h₂ <;> rw [← Ideal.under_under (B := S)]
      · rw [Q.under_map_of_isLocalizationAtPrime h₁]
      · rw [Localization.AtPrime.under_maximalIdeal])
  rw [← Localization.AtPrime.under_maximalIdeal (I := Q)]; rw [← H]; rw [Q.under_map_of_isLocalizationAtPrime h₁]

instance (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] [QuasiFiniteAt R P]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra p P] :
    Module.Finite p.ResidueField P.ResidueField := by
  let m := IsLocalRing.maximalIdeal (Localization.AtPrime P)
  let : m.LiesOver p := .trans _ P _
  let := Localization.AtPrime.algebraOfLiesOver p m
  let := Localization.AtPrime.algebraOfLiesOver P m
  let e := AlgEquiv.ofBijective (IsScalarTower.toAlgHom p.ResidueField P.ResidueField
    m.ResidueField) ((RingHom.surjectiveOnStalks_of_isLocalization
        P.primeCompl _).residueFieldMap_bijective P m (m.over_def P))
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

set_option backward.defeqAttrib.useBackward true in
/--
lemma `QuasiFiniteAt.exists_basicOpen_eq_singleton` / 引理 `QuasiFiniteAt.exists_basicOpen_eq_singleton`

English:
lemma QuasiFiniteAt.exists_basicOpen_eq_singleton
  proof: by
  have : IsLocalizedModule p.primeCompl (.id (R := S) (M := Localization.AtPrime p)) :=
    ⟨IsLocalizedModule.map_units (Algebra.linearMap S (Localization.AtPrime p)),
      fun y => ⟨⟨y, 1⟩, by simp⟩, by simpa using ⟨1, p.primeCompl.one_mem⟩⟩
  have : Module.Finite R (Localization.AtPrime p) := .of_quasiFinite
  have : Module.Finite S (Localization.AtPrime p) := .of_restrictScalars_finite R _ _
  have : IsArtinianRing (Localization.AtPrime p) := .of_finite R _
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Module.FinitePresentation S (Localization.AtPrime p) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨r, hrp, H⟩ := IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation
    p.primeCompl (Algebra.linearMap S (Localization.AtPrime p))
  have : IsLocalization (.powers r) (Localization.AtPrime p) :=
    (isLocalizedModule_iff_isLocalization' _ _).mp H
  let φ : Localization.Away r ≃ₐ[S] Localization.AtPrime p :=
    IsLocalization.algEquiv (.powers r) _ _
  refine ⟨r, hrp, subset_antisymm (fun q hrq => ?_) (Set.singleton_subset_iff.mpr hrp)⟩
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).ge hrq
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.comapEquiv φ.toRingEquiv).symm.surjective q
  -- As Sₚ is an artinian local ring, its prime spectrum is a singleton.
  obtain rfl : q = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
  ext1
  dsimp [-RingEquiv.symm_mk]
  rw [Ideal.comap_comap]; rw [← AlgEquiv.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]
  exact IsLocalization.AtPrime.under_maximalIdeal _ _

中文:
引理 QuasiFiniteAt.存在_basicOpen_eq_singleton
  证明: by
  have : IsLocalizedModule p.primeCompl (.id (R := S) (M := Localization.AtPrime p)) :=
    ⟨IsLocalizedModule.map_units (Algebra.linearMap S (Localization.AtPrime p)),
      fun y => ⟨⟨y, 1⟩, by simp⟩, by simpa using ⟨1, p.primeCompl.one_mem⟩⟩
  have : Module.Finite R (Localization.AtPrime p) := .of_quasiFinite
  have : Module.Finite S (Localization.AtPrime p) := .of_restrictScalars_finite R _ _
  have : IsArtinianRing (Localization.AtPrime p) := .of_finite R _
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Module.FinitePresentation S (Localization.AtPrime p) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨r, hrp, H⟩ := IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation
    p.primeCompl (Algebra.linearMap S (Localization.AtPrime p))
  have : IsLocalization (.powers r) (Localization.AtPrime p) :=
    (isLocalizedModule_iff_isLocalization' _ _).mp H
  let φ : Localization.Away r ≃ₐ[S] Localization.AtPrime p :=
    IsLocalization.algEquiv (.powers r) _ _
  refine ⟨r, hrp, subset_antisymm (fun q hrq => ?_) (Set.singleton_subset_iff.mpr hrp)⟩
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).ge hrq
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.comapEquiv φ.toRingEquiv).symm.surjective q
  -- As Sₚ is an artinian local ring, its prime spectrum is a singleton.
  obtain rfl : q = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
  ext1
  dsimp [-RingEquiv.symm_mk]
  rw [Ideal.comap_comap]; rw [← AlgEquiv.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]
  exact IsLocalization.AtPrime.under_maximalIdeal _ _

Depends on / 依赖: Algebra, Algebra.EssFiniteTy, Algebra.linearMap, AtPrime, EssFiniteTy, Finite, IsArtinianRing, IsLocalizedModule, IsLocalizedModule.map_units, IsNoetherianRing, Localization, Localization.AtPrime, Module, Module.Finite, linearMap, map_units, of_finite, of_quasiFinite, of_restrictScalars_finite, one_mem
-/
lemma QuasiFiniteAt.exists_basicOpen_eq_singleton
    (p : Ideal S) [p.IsPrime] [IsArtinianRing R] [Algebra.EssFiniteType R S]
    [Algebra.QuasiFiniteAt R p] :
    exists f ∉ p, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) = {⟨p, ‹_›⟩} := by
  have : IsLocalizedModule p.primeCompl (.id (R := S) (M := Localization.AtPrime p)) :=
    ⟨IsLocalizedModule.map_units (Algebra.linearMap S (Localization.AtPrime p)),
      fun y => ⟨⟨y, 1⟩, by simp⟩, by simpa using ⟨1, p.primeCompl.one_mem⟩⟩
  have : Module.Finite R (Localization.AtPrime p) := .of_quasiFinite
  have : Module.Finite S (Localization.AtPrime p) := .of_restrictScalars_finite R _ _
  have : IsArtinianRing (Localization.AtPrime p) := .of_finite R _
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Module.FinitePresentation S (Localization.AtPrime p) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨r, hrp, H⟩ := IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation
    p.primeCompl (Algebra.linearMap S (Localization.AtPrime p))
  have : IsLocalization (.powers r) (Localization.AtPrime p) :=
    (isLocalizedModule_iff_isLocalization' _ _).mp H
  let φ : Localization.Away r ≃ₐ[S] Localization.AtPrime p :=
    IsLocalization.algEquiv (.powers r) _ _
  refine ⟨r, hrp, subset_antisymm (fun q hrq => ?_) (Set.singleton_subset_iff.mpr hrp)⟩
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).ge hrq
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.comapEquiv φ.toRingEquiv).symm.surjective q
  -- As Sₚ is an artinian local ring, its prime spectrum is a singleton.
  obtain rfl : q = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
  ext1
  dsimp [-RingEquiv.symm_mk]
  rw [Ideal.comap_comap]; rw [← AlgEquiv.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]
  exact IsLocalization.AtPrime.under_maximalIdeal _ _

/--
lemma `QuasiFiniteAt.isClopen_singleton` / 引理 `QuasiFiniteAt.isClopen_singleton`

English:
lemma QuasiFiniteAt.isClopen_singleton
  proof: by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out 0 1).mp ?_
  obtain ⟨f, hf, e⟩ := exists_basicOpen_eq_singleton (R := R) p.asIdeal
  exact e ▸ (PrimeSpectrum.basicOpen f).isOpen

中文:
引理 QuasiFiniteAt.isClopen_singleton
  证明: by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out 0 1).mp ?_
  obtain ⟨f, hf, e⟩ := exists_basicOpen_eq_singleton (R := R) p.asIdeal
  exact e ▸ (PrimeSpectrum.basicOpen f).isOpen

Depends on / 依赖: Algebra, Algebra.FiniteType.isNoetherianRing, FiniteType, IsJacobsonRing, IsNoetherianRing, PrimeSpectrum, PrimeSpectrum.basicOpen, PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing, asIdeal, basicOpen, exists_basicOpen_eq_singleton, isJacobsonRing_of_finiteType, isNoetherianRing, isOpen, isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing, p.asIdeal
-/
lemma QuasiFiniteAt.isClopen_singleton
    (p : PrimeSpectrum S) [IsArtinianRing R] [Algebra.FiniteType R S]
    [Algebra.QuasiFiniteAt R p.asIdeal] : IsClopen {p} := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out 0 1).mp ?_
  obtain ⟨f, hf, e⟩ := exists_basicOpen_eq_singleton (R := R) p.asIdeal
  exact e ▸ (PrimeSpectrum.basicOpen f).isOpen

/--
lemma `QuasiFiniteAt.of_isOpen_singleton` / 引理 `QuasiFiniteAt.of_isOpen_singleton`

English:
lemma QuasiFiniteAt.of_isOpen_singleton
  proof: by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  rw [(PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out
    0 1 rfl rfl] at H
  obtain ⟨e, he, H⟩ := PrimeSpectrum.isClopen_iff.mp H
  have hep : e ∉ p.asIdeal := H.le rfl
  let f : Localization.Away e ->ₐ[S] Localization.AtPrime p.asIdeal :=
    IsLocalization.Away.liftAlgHom e (f := Algebra.ofId _ _)
      (IsLocalization.map_units (M := p.asIdeal.primeCompl) _ ⟨e, hep⟩)
  have h₁ := (PrimeSpectrum.localization_away_comap_range (Localization.Away e) e).trans H.symm
  have : Subsingleton (PrimeSpectrum (Localization.Away e)) :=
    Function.Injective.subsingleton
    (f := Set.codRestrict (PrimeSpectrum.comap (algebraMap S (Localization.Away e))) {p} fun x =>
      h₁.le ⟨x, rfl⟩)
    ((Set.injective_codRestrict ..).mpr (PrimeSpectrum.localization_comap_injective _ (.powers e)))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl x
    suffices IsUnit (algebraMap _ (Localization.Away e) s.1) by
      refine ⟨algebraMap _ _ x * this.unit⁻¹, (this.map f).mul_right_cancel ?_⟩
      simp only [← map_mul, mul_assoc, IsUnit.val_inv_mul]
      simp
    by_contra H
    obtain ⟨M, hM, H⟩ :=
      Ideal.exists_le_maximal (.span {algebraMap _ (Localization.Away e) s.1}) (by simpa)
    have := Subsingleton.elim ((IsLocalRing.closedPoint _).comap f.toRingHom) ⟨M, inferInstance⟩
    have := congr(($this).1).ge (H (Ideal.mem_span_singleton_self _))
    simp [IsLocalRing.closedPoint, IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal] at this
  have : Algebra.FiniteType R (Localization.AtPrime p.asIdeal) :=
    .of_surjective (f.restrictScalars R) hf
  have := (PrimeSpectrum.comap_injective_of_surjective f.toRingHom hf).subsingleton
  exact QuasiFinite.iff_finite_comap_preimage_singleton.mpr fun _ =>
    Set.subsingleton_of_subsingleton.finite

中文:
引理 QuasiFiniteAt.of_isOpen_singleton
  证明: by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  rw [(PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out
    0 1 rfl rfl] at H
  obtain ⟨e, he, H⟩ := PrimeSpectrum.isClopen_iff.mp H
  have hep : e ∉ p.asIdeal := H.le rfl
  let f : Localization.Away e ->ₐ[S] Localization.AtPrime p.asIdeal :=
    IsLocalization.Away.liftAlgHom e (f := Algebra.ofId _ _)
      (IsLocalization.map_units (M := p.asIdeal.primeCompl) _ ⟨e, hep⟩)
  have h₁ := (PrimeSpectrum.localization_away_comap_range (Localization.Away e) e).trans H.symm
  have : Subsingleton (PrimeSpectrum (Localization.Away e)) :=
    Function.Injective.subsingleton
    (f := Set.codRestrict (PrimeSpectrum.comap (algebraMap S (Localization.Away e))) {p} fun x =>
      h₁.le ⟨x, rfl⟩)
    ((Set.injective_codRestrict ..).mpr (PrimeSpectrum.localization_comap_injective _ (.powers e)))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl x
    suffices IsUnit (algebraMap _ (Localization.Away e) s.1) by
      refine ⟨algebraMap _ _ x * this.unit⁻¹, (this.map f).mul_right_cancel ?_⟩
      simp only [← map_mul, mul_assoc, IsUnit.val_inv_mul]
      simp
    by_contra H
    obtain ⟨M, hM, H⟩ :=
      Ideal.exists_le_maximal (.span {algebraMap _ (Localization.Away e) s.1}) (by simpa)
    have := Subsingleton.elim ((IsLocalRing.closedPoint _).comap f.toRingHom) ⟨M, inferInstance⟩
    have := congr(($this).1).ge (H (Ideal.mem_span_singleton_self _))
    simp [IsLocalRing.closedPoint, IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal] at this
  have : Algebra.FiniteType R (Localization.AtPrime p.asIdeal) :=
    .of_surjective (f.restrictScalars R) hf
  have := (PrimeSpectrum.comap_injective_of_surjective f.toRingHom hf).subsingleton
  exact QuasiFinite.iff_finite_comap_preimage_singleton.mpr fun _ =>
    Set.subsingleton_of_subsingleton.finite

Depends on / 依赖: Algebra, Algebra.FiniteType.isNoetherianRing, Algebra.ofId, AtPrime, FiniteType, H.le, IsJacobsonRing, IsLocalization, IsLocalization.Away.liftAlgHom, IsLocalization.map_units, IsNoetherianRing, Localization, Localization.AtPrime, Localization.Away, PrimeSpectrum, PrimeSpectrum.isClopen_iff.mp, PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing, asIdeal, isClopen_iff, isJacobsonRing_of_finiteType
-/
lemma QuasiFiniteAt.of_isOpen_singleton
    [IsArtinianRing R] (p : PrimeSpectrum S) [Algebra.FiniteType R S]
    (H : IsOpen {p}) : Algebra.QuasiFiniteAt R p.asIdeal := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  rw [(PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out
    0 1 rfl rfl] at H
  obtain ⟨e, he, H⟩ := PrimeSpectrum.isClopen_iff.mp H
  have hep : e ∉ p.asIdeal := H.le rfl
  let f : Localization.Away e ->ₐ[S] Localization.AtPrime p.asIdeal :=
    IsLocalization.Away.liftAlgHom e (f := Algebra.ofId _ _)
      (IsLocalization.map_units (M := p.asIdeal.primeCompl) _ ⟨e, hep⟩)
  have h₁ := (PrimeSpectrum.localization_away_comap_range (Localization.Away e) e).trans H.symm
  have : Subsingleton (PrimeSpectrum (Localization.Away e)) :=
    Function.Injective.subsingleton
    (f := Set.codRestrict (PrimeSpectrum.comap (algebraMap S (Localization.Away e))) {p} fun x =>
      h₁.le ⟨x, rfl⟩)
    ((Set.injective_codRestrict ..).mpr (PrimeSpectrum.localization_comap_injective _ (.powers e)))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl x
    suffices IsUnit (algebraMap _ (Localization.Away e) s.1) by
      refine ⟨algebraMap _ _ x * this.unit⁻¹, (this.map f).mul_right_cancel ?_⟩
      simp only [← map_mul, mul_assoc, IsUnit.val_inv_mul]
      simp
    by_contra H
    obtain ⟨M, hM, H⟩ :=
      Ideal.exists_le_maximal (.span {algebraMap _ (Localization.Away e) s.1}) (by simpa)
    have := Subsingleton.elim ((IsLocalRing.closedPoint _).comap f.toRingHom) ⟨M, inferInstance⟩
    have := congr(($this).1).ge (H (Ideal.mem_span_singleton_self _))
    simp [IsLocalRing.closedPoint, IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal] at this
  have : Algebra.FiniteType R (Localization.AtPrime p.asIdeal) :=
    .of_surjective (f.restrictScalars R) hf
  have := (PrimeSpectrum.comap_injective_of_surjective f.toRingHom hf).subsingleton
  exact QuasiFinite.iff_finite_comap_preimage_singleton.mpr fun _ =>
    Set.subsingleton_of_subsingleton.finite

attribute [local instance] RingHom.ker_isPrime in
/--
lemma `_root_.Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver` / 引理 `_root_.Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver`

English:
lemma _root_.Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver
  proof: by
  let e := PrimeSpectrum.preimageHomeomorphFiber _ S ⟨p, inferInstance⟩
  let qF : PrimeSpectrum (p.Fiber S) := e ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩
  have : Algebra.QuasiFiniteAt p.ResidueField qF.asIdeal := .baseChange q _
    congr($(e.symm_apply_apply ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩).1.1).symm
  obtain ⟨r, hr, hrq⟩ := Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton
    (R := p.ResidueField) qF.asIdeal
  obtain ⟨s, hs, x, hsx⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ r
  have : x ∉ q := by
    have : r ∉ _ := hrq.ge rfl
    simp only [PrimeSpectrum.preimageHomeomorphFiber, PrimeSpectrum.preimageOrderIsoFiber,
      Homeomorph.homeomorph_mk_coe, qF, e] at this
    rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]; rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s)]; rw [← Algebra.smul_def]; rw [hsx] at this
    · simpa using this
    · simpa [IsScalarTower.algebraMap_apply R S q.ResidueField, q.over_def p] using hs
  refine ⟨x, this, fun q' _ hq' _ => not_not.mp fun hxq' => hq' ?_⟩
  refine congr($(e.injective (a₁ := ⟨⟨q', ‹_›⟩, PrimeSpectrum.ext (q'.over_def p).symm⟩)
    (a₂ := ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩) (hrq.le ?_)).1.1)
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, PrimeSpectrum.preimageHomeomorphFiber,
    PrimeSpectrum.preimageOrderIsoFiber, Homeomorph.homeomorph_mk_coe, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, e]
  rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]; rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s)]; rw [← Algebra.smul_def]; rw [hsx]
  · simpa
  · simpa [IsScalarTower.algebraMap_apply R S q'.ResidueField, ← Ideal.mem_comap, ← q'.over_def p]

中文:
引理 _root_.理想.存在_not_mem_对任意_mem_of_ne_of_liesOver
  证明: by
  let e := PrimeSpectrum.preimageHomeomorphFiber _ S ⟨p, inferInstance⟩
  let qF : PrimeSpectrum (p.Fiber S) := e ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩
  have : Algebra.QuasiFiniteAt p.ResidueField qF.asIdeal := .baseChange q _
    congr($(e.symm_apply_apply ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩).1.1).symm
  obtain ⟨r, hr, hrq⟩ := Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton
    (R := p.ResidueField) qF.asIdeal
  obtain ⟨s, hs, x, hsx⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ r
  have : x ∉ q := by
    have : r ∉ _ := hrq.ge rfl
    simp only [PrimeSpectrum.preimageHomeomorphFiber, PrimeSpectrum.preimageOrderIsoFiber,
      Homeomorph.homeomorph_mk_coe, qF, e] at this
    rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]; rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s)]; rw [← Algebra.smul_def]; rw [hsx] at this
    · simpa using this
    · simpa [IsScalarTower.algebraMap_apply R S q.ResidueField, q.over_def p] using hs
  refine ⟨x, this, fun q' _ hq' _ => not_not.mp fun hxq' => hq' ?_⟩
  refine congr($(e.injective (a₁ := ⟨⟨q', ‹_›⟩, PrimeSpectrum.ext (q'.over_def p).symm⟩)
    (a₂ := ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩) (hrq.le ?_)).1.1)
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, PrimeSpectrum.preimageHomeomorphFiber,
    PrimeSpectrum.preimageOrderIsoFiber, Homeomorph.homeomorph_mk_coe, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, e]
  rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]; rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s)]; rw [← Algebra.smul_def]; rw [hsx]
  · simpa
  · simpa [IsScalarTower.algebraMap_apply R S q'.ResidueField, ← Ideal.mem_comap, ← q'.over_def p]

Depends on / 依赖: Algebra, Algebra.QuasiFiniteAt, Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton, Ideal.Fiber.exists_smul_eq_one_tmul, PrimeSpectrum, PrimeSpectrum.ext, PrimeSpectrum.preimageHomeomorphFiber, QuasiFiniteAt, ResidueField, asIdeal, baseChange, e.symm_apply_apply, exists_basicOpen_eq_singleton, exists_smul_eq_one_tmul, over_def, p.Fiber, p.ResidueField, preimageHomeomorphFiber, q.over_def, qF.asIdeal
-/
lemma _root_.Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFiniteAt R q] :
    exists s ∉ q, forall q' : Ideal S, q'.IsPrime -> q' != q -> q'.LiesOver p -> s in q' := by
  let e := PrimeSpectrum.preimageHomeomorphFiber _ S ⟨p, inferInstance⟩
  let qF : PrimeSpectrum (p.Fiber S) := e ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩
  have : Algebra.QuasiFiniteAt p.ResidueField qF.asIdeal := .baseChange q _
    congr($(e.symm_apply_apply ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩).1.1).symm
  obtain ⟨r, hr, hrq⟩ := Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton
    (R := p.ResidueField) qF.asIdeal
  obtain ⟨s, hs, x, hsx⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ r
  have : x ∉ q := by
    have : r ∉ _ := hrq.ge rfl
    simp only [PrimeSpectrum.preimageHomeomorphFiber, PrimeSpectrum.preimageOrderIsoFiber,
      Homeomorph.homeomorph_mk_coe, qF, e] at this
    rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]; rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s)]; rw [← Algebra.smul_def]; rw [hsx] at this
    · simpa using this
    · simpa [IsScalarTower.algebraMap_apply R S q.ResidueField, q.over_def p] using hs
  refine ⟨x, this, fun q' _ hq' _ => not_not.mp fun hxq' => hq' ?_⟩
  refine congr($(e.injective (a₁ := ⟨⟨q', ‹_›⟩, PrimeSpectrum.ext (q'.over_def p).symm⟩)
    (a₂ := ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩) (hrq.le ?_)).1.1)
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, PrimeSpectrum.preimageHomeomorphFiber,
    PrimeSpectrum.preimageOrderIsoFiber, Homeomorph.homeomorph_mk_coe, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, e]
  rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]; rw [← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s)]; rw [← Algebra.smul_def]; rw [hsx]
  · simpa
  · simpa [IsScalarTower.algebraMap_apply R S q'.ResidueField, ← Ideal.mem_comap, ← q'.over_def p]

/--
lemma `_root_.Ideal.Fiber.lift_residueField_surjective` / 引理 `_root_.Ideal.Fiber.lift_residueField_surjective`

English:
lemma _root_.Ideal.Fiber.lift_residueField_surjective
  statement: [Algebra.FiniteType R S]
  proof: by
  let q' : Ideal (p.Fiber S) := (PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q, ‹_›, ‹_›⟩).asIdeal
  have hq' : q = q'.comap Algebra.TensorProduct.includeRight.toRingHom :=
    congr($((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply ⟨q, ‹_›, ‹_›⟩).1).symm
  have : Algebra.QuasiFiniteAt p.ResidueField q' := .baseChange q _ hq'
  have : q'.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
    (QuasiFiniteAt.isClopen_singleton (R := p.ResidueField) _).isClosed
  refine .of_comp_left ?_
    (p.surjectiveOnStalks_residueField.baseChange'.residueFieldMap_bijective q q' hq').1
  rw [← AlgHom.coe_toRingHom]; rw [← RingHom.coe_comp]
  convert! q'.algebraMap_residueField_surjective
  ext <;> simp [IsScalarTower.algebraMap_apply R S q.ResidueField]

中文:
引理 _root_.理想.Fiber.lift_residueField_surjective
  结论: [代数.有限型 R S]
  证明: by
  let q' : Ideal (p.Fiber S) := (PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q, ‹_›, ‹_›⟩).asIdeal
  have hq' : q = q'.comap Algebra.TensorProduct.includeRight.toRingHom :=
    congr($((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply ⟨q, ‹_›, ‹_›⟩).1).symm
  have : Algebra.QuasiFiniteAt p.ResidueField q' := .baseChange q _ hq'
  have : q'.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
    (QuasiFiniteAt.isClopen_singleton (R := p.ResidueField) _).isClosed
  refine .of_comp_left ?_
    (p.surjectiveOnStalks_residueField.baseChange'.residueFieldMap_bijective q q' hq').1
  rw [← AlgHom.coe_toRingHom]; rw [← RingHom.coe_comp]
  convert! q'.algebraMap_residueField_surjective
  ext <;> simp [IsScalarTower.algebraMap_apply R S q.ResidueField]

Depends on / 依赖: Algebra, Algebra.QuasiFiniteAt, Algebra.TensorProduct.includeRight.toRingHom, IsMaximal, PrimeSpectrum, PrimeSpectrum.isClosed_singleton_iff_isMaximal, PrimeSpectrum.primesOverOrderIsoFiber, QuasiFiniteAt, QuasiFiniteAt.isClopen_singleton, ResidueField, TensorProduct, asIdeal, baseChange, includeRight, isClopen_singleton, isClosed, isClosed_singleton_iff_isMaximal, of_comp_le, p.Fiber, p.ResidueField
-/
lemma _root_.Ideal.Fiber.lift_residueField_surjective [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Function.Surjective (Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (IsScalarTower.toAlgHom _ _ _) fun _ _ => .all _ _ :
      p.Fiber S ->ₐ[p.ResidueField] q.ResidueField) := by
  let q' : Ideal (p.Fiber S) := (PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q, ‹_›, ‹_›⟩).asIdeal
  have hq' : q = q'.comap Algebra.TensorProduct.includeRight.toRingHom :=
    congr($((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply ⟨q, ‹_›, ‹_›⟩).1).symm
  have : Algebra.QuasiFiniteAt p.ResidueField q' := .baseChange q _ hq'
  have : q'.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
    (QuasiFiniteAt.isClopen_singleton (R := p.ResidueField) _).isClosed
  refine .of_comp_left ?_
    (p.surjectiveOnStalks_residueField.baseChange'.residueFieldMap_bijective q q' hq').1
  rw [← AlgHom.coe_toRingHom]; rw [← RingHom.coe_comp]
  convert! q'.algebraMap_residueField_surjective
  ext <;> simp [IsScalarTower.algebraMap_apply R S q.ResidueField]

end QuasiFiniteAt

end Algebra
