/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Smooth algebras are flat

Let `A` be a smooth `R`-algebra. In this file we show that then `A` is `R`-flat.
The proof proceeds in two steps:

1. If `R` is Noetherian, let `R[X₁, ..., Xₙ] →ₐ[R] A` be surjective with kernel `I`. By
  formal smoothness we construct a section `A →ₐ[R] AdicCompletion I R[X₁, ..., Xₙ]`
  of the canonical map `AdicCompletion I R[X₁, ..., Xₙ] →ₐ[R] R[X₁, ..., Xₙ] ⧸ I ≃ₐ[R] A`.
  Since `R` is Noetherian, `AdicCompletion I R` is `R`-flat so `A` is a retract
  of a flat `R`-module and hence flat.
2. In the general case, we choose a model of `A` over a finitely generated
  `ℤ`-subalgebra of `R` and apply 1.


## References

- [Conde-Lago, A short proof of smooth implies flat][condelago2016shortproofsmoothimplies]
-/

public section

namespace Algebra

variable {R A S : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]

/--
lemma `FormallySmooth.flat_of_algHom_of_isNoetherianRing` / 引理 `FormallySmooth.flat_of_algHom_of_isNoetherianRing`

English:
lemma FormallySmooth.flat_of_algHom_of_isNoetherianRing
  statement: (f : S ->ₐ[R] A) (hf : Function.Surjective f)
  proof: by
  have : Module.Flat R (AdicCompletion (RingHom.ker f) S) := .trans _ S _
  obtain ⟨g, hg⟩ := exists_kerProj_comp_eq_id f hf
  exact .of_retract g.toLinearMap
    (AdicCompletion.kerProj hf).toLinearMap (LinearMap.ext fun x => congr($hg x))

中文:
引理 FormallySmooth.flat_of_algHom_of_isNoetherianRing
  结论: (f : S ->ₐ[R] A) (hf : Function.Surjective f)
  证明: by
  have : Module.Flat R (AdicCompletion (RingHom.ker f) S) := .trans _ S _
  obtain ⟨g, hg⟩ := exists_kerProj_comp_eq_id f hf
  exact .of_retract g.toLinearMap
    (AdicCompletion.kerProj hf).toLinearMap (LinearMap.ext fun x => congr($hg x))

Depends on / 依赖: AdicCompletion, AdicCompletion.kerProj, LinearMap, LinearMap.ext, Module, Module.Flat, RingHom, RingHom.ker, WeaklyLocallyCompactSpace, exists_kerProj_comp_eq_id, g.toLinearMap, kerProj, of_retract, paracompact_of_locallyCompact_sigmaCompact, toLinearMap
-/
lemma FormallySmooth.flat_of_algHom_of_isNoetherianRing (f : S ->ₐ[R] A) (hf : Function.Surjective f)
    [Module.Flat R S] [IsNoetherianRing S] [FormallySmooth R A] :
    Module.Flat R A := by
  have : Module.Flat R (AdicCompletion (RingHom.ker f) S) := .trans _ S _
  obtain ⟨g, hg⟩ := exists_kerProj_comp_eq_id f hf
  exact .of_retract g.toLinearMap
    (AdicCompletion.kerProj hf).toLinearMap (LinearMap.ext fun x => congr($hg x))

variable (R A)

/--
theorem `Smooth.flat_of_isNoetherianRing` / 定理 `Smooth.flat_of_isNoetherianRing`

English:
theorem Smooth.flat_of_isNoetherianRing
  given: [IsNoetherianRing R] [Smooth R A]
  proof: by
  obtain ⟨k, f, hf⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact FormallySmooth.flat_of_algHom_of_isNoetherianRing f hf

中文:
定理 Smooth.flat_of_isNoetherianRing
  条件: [IsNoetherianRing R] [Smooth R A]
  证明: by
  obtain ⟨k, f, hf⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact FormallySmooth.flat_of_algHom_of_isNoetherianRing f hf

Depends on / 依赖: FiniteType, FiniteType.iff_quotient_mvPolynomial, FormallySmooth, FormallySmooth.flat_of_algHom_of_isNoetherianRing, NormalSpace, NormalSpace.of_paracompactSpace_r1Space, flat_of_algHom_of_isNoetherianRing, iff_quotient_mvPolynomial, of_paracompactSpace_r1Space
-/
theorem Smooth.flat_of_isNoetherianRing [IsNoetherianRing R] [Smooth R A] :
    Module.Flat R A := by
  obtain ⟨k, f, hf⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact FormallySmooth.flat_of_algHom_of_isNoetherianRing f hf

/--
Instance `Smooth.flat` / 实例 `Smooth.flat`

English:
instance Smooth.flat
  signature: [Smooth R A]
  body: by
  obtain ⟨A₀, B₀, _, _, _, _, _, _, _, _, ⟨e⟩⟩ := exists_finiteType Int R A
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing Int _
  have : Module.Flat A₀ B₀ := Smooth.flat_of_isNoetherianRing _ _
  exact .of_linearEquiv e.toLinearEquiv

中文:
实例 Smooth.flat
  签名: [Smooth R A]
  定义体: by
  obtain ⟨A₀, B₀, _, _, _, _, _, _, _, _, ⟨e⟩⟩ := exists_finiteType Int R A
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing Int _
  have : Module.Flat A₀ B₀ := Smooth.flat_of_isNoetherianRing _ _
  exact .of_linearEquiv e.toLinearEquiv

Depends on / 依赖: Algebra, Algebra.FiniteType.isNoetherianRing, FiniteType, IsNoetherianRing, Module, Module.Flat, Smooth, Smooth.flat_of_isNoetherianRing, e.toLinearEquiv, exists_finiteType, flat_of_isNoetherianRing, isNoetherianRing, of_linearEquiv, toLinearEquiv
-/
instance Smooth.flat [Smooth R A] : Module.Flat R A := by
  obtain ⟨A₀, B₀, _, _, _, _, _, _, _, _, ⟨e⟩⟩ := exists_finiteType Int R A
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing Int _
  have : Module.Flat A₀ B₀ := Smooth.flat_of_isNoetherianRing _ _
  exact .of_linearEquiv e.toLinearEquiv

end Algebra

/--
lemma `RingHom.Smooth.flat` / 引理 `RingHom.Smooth.flat`

English:
lemma RingHom.Smooth.flat
  given: {R S : Type*} [CommRing R] [CommRing S] {f : R ->+* S} (hf : f.Smooth)
  proof: by
  algebraize [f]
  exact Algebra.Smooth.flat R S

中文:
引理 RingHom.Smooth.flat
  条件: {R S : 类型} [CommRing R] [CommRing S] {f : R ->+* S} (hf : f.Smooth)
  证明: by
  algebraize [f]
  exact Algebra.Smooth.flat R S

Depends on / 依赖: Algebra, Algebra.Smooth.flat, Smooth, algebraize
-/
lemma RingHom.Smooth.flat {R S : Type*} [CommRing R] [CommRing S] {f : R ->+* S} (hf : f.Smooth) :
    f.Flat := by
  algebraize [f]
  exact Algebra.Smooth.flat R S
