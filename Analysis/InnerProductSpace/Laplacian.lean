/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.DerivNotation
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-!
# The Laplacian

This file defines the Laplacian for functions `f : E → F` on real, finite-dimensional, inner product
spaces `E`. In essence, we define the Laplacian of `f` as the second derivative, applied to the
canonical covariant tensor of `E`, as defined and discussed in
`Mathlib.Analysis.InnerProductSpace.CanonicalTensor`.

We show that the Laplacian is `ℝ`-linear on continuously differentiable functions, and establish the
standard formula for computing the Laplacian in terms of orthonormal bases of `E`.
-/

@[expose] public section

open Filter TensorProduct Topology

section secondDerivativeAPI

/-!
## Supporting API

The definition of the Laplacian of a function `f : E → F` involves the notion of the second
derivative, which can be seen as a continuous multilinear map `ContinuousMultilinearMap 𝕜 (fun (i :
Fin 2) ↦ E) F`, a bilinear map `E →ₗ[𝕜] E →ₗ[𝕜] F`, or a linear map on tensors `E ⊗[𝕜] E →ₗ[𝕜]
F`. This section provides convenience API to convert between these notions.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜) in
/--
Definition of `bilinearIteratedFDerivWithinTwo` / `bilinearIteratedFDerivWithinTwo` 的定义

English:
definition bilinearIteratedFDerivWithinTwo
  signature: (f : E -> F) (s : Set E)
  body: fun x => (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x).toLinearMap₁₂

中文:
定义 bilinearIteratedFDerivWithinTwo
  签名: (f : E -> F) (s : 集合 E)
  定义体: fun x => (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x).toLinearMap₁₂

Depends on / 依赖: fderivWithin
-/
noncomputable def bilinearIteratedFDerivWithinTwo (f : E -> F) (s : Set E) : E -> E ->ₗ[𝕜] E ->ₗ[𝕜] F :=
  fun x => (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x).toLinearMap₁₂

variable (𝕜) in
/--
Definition of `bilinearIteratedFDerivTwo` / `bilinearIteratedFDerivTwo` 的定义

English:
definition bilinearIteratedFDerivTwo
  signature: (f : E -> F)
  body: fun x => (fderiv 𝕜 (fderiv 𝕜 f) x).toLinearMap₁₂

中文:
定义 bilinearIteratedFDerivTwo
  签名: (f : E -> F)
  定义体: fun x => (fderiv 𝕜 (fderiv 𝕜 f) x).toLinearMap₁₂

Depends on / 依赖: fderiv
-/
noncomputable def bilinearIteratedFDerivTwo (f : E -> F) : E -> E ->ₗ[𝕜] E ->ₗ[𝕜] F :=
  fun x => (fderiv 𝕜 (fderiv 𝕜 f) x).toLinearMap₁₂

/--
lemma `bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv` / 引理 `bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv`

English:
lemma bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv
  statement: {e : E} {s : Set E} (f : E -> F)
  proof: by
  simp [iteratedFDerivWithin_two_apply f hs he ![e₁, e₂], bilinearIteratedFDerivWithinTwo]

中文:
引理 bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv
  结论: {e : E} {s : 集合 E} (f : E -> F)
  证明: by
  simp [iteratedFDerivWithin_two_apply f hs he ![e₁, e₂], bilinearIteratedFDerivWithinTwo]

Depends on / 依赖: bilinearIteratedFDerivWithinTwo, iteratedFDerivWithin_two_apply
-/
lemma bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv {e : E} {s : Set E} (f : E -> F)
    (hs : UniqueDiffOn 𝕜 s) (he : e in s) (e₁ e₂ : E) :
    bilinearIteratedFDerivWithinTwo 𝕜 f s e e₁ e₂ = iteratedFDerivWithin 𝕜 2 f s e ![e₁, e₂] := by
  simp [iteratedFDerivWithin_two_apply f hs he ![e₁, e₂], bilinearIteratedFDerivWithinTwo]

/--
lemma `bilinearIteratedFDerivTwo_eq_iteratedFDeriv` / 引理 `bilinearIteratedFDerivTwo_eq_iteratedFDeriv`

English:
lemma bilinearIteratedFDerivTwo_eq_iteratedFDeriv
  given: (f : E -> F) (e e₁ e₂ : E)
  proof: by
  simp [iteratedFDeriv_two_apply f e ![e₁, e₂], bilinearIteratedFDerivTwo]

中文:
引理 bilinearIteratedFDerivTwo_eq_iteratedFDeriv
  条件: (f : E -> F) (e e₁ e₂ : E)
  证明: by
  simp [iteratedFDeriv_two_apply f e ![e₁, e₂], bilinearIteratedFDerivTwo]

Depends on / 依赖: bilinearIteratedFDerivTwo, iteratedFDeriv_two_apply
-/
lemma bilinearIteratedFDerivTwo_eq_iteratedFDeriv (f : E -> F) (e e₁ e₂ : E) :
    bilinearIteratedFDerivTwo 𝕜 f e e₁ e₂ = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  simp [iteratedFDeriv_two_apply f e ![e₁, e₂], bilinearIteratedFDerivTwo]

variable (𝕜) in
/--
Definition of `tensorIteratedFDerivWithinTwo` / `tensorIteratedFDerivWithinTwo` 的定义

English:
definition tensorIteratedFDerivWithinTwo
  signature: (f : E -> F) (s : Set E)
  body: fun e => lift (bilinearIteratedFDerivWithinTwo 𝕜 f s e)

中文:
定义 tensorIteratedFDerivWithinTwo
  签名: (f : E -> F) (s : 集合 E)
  定义体: fun e => lift (bilinearIteratedFDerivWithinTwo 𝕜 f s e)

Depends on / 依赖: bilinearIteratedFDerivWithinTwo
-/
noncomputable def tensorIteratedFDerivWithinTwo (f : E -> F) (s : Set E) : E -> E otimes[𝕜] E ->ₗ[𝕜] F :=
  fun e => lift (bilinearIteratedFDerivWithinTwo 𝕜 f s e)

variable (𝕜) in
/--
Definition of `tensorIteratedFDerivTwo` / `tensorIteratedFDerivTwo` 的定义

English:
definition tensorIteratedFDerivTwo
  signature: (f : E -> F)
  body: fun e => lift (bilinearIteratedFDerivTwo 𝕜 f e)

中文:
定义 tensorIteratedFDerivTwo
  签名: (f : E -> F)
  定义体: fun e => lift (bilinearIteratedFDerivTwo 𝕜 f e)

Depends on / 依赖: bilinearIteratedFDerivTwo
-/
noncomputable def tensorIteratedFDerivTwo (f : E -> F) : E -> E otimes[𝕜] E ->ₗ[𝕜] F :=
  fun e => lift (bilinearIteratedFDerivTwo 𝕜 f e)

/--
lemma `tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin` / 引理 `tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin`

English:
lemma tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin
  statement: {e : E} {s : Set E} (f : E -> F)
  proof: by
  rw [← bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv f hs he]; rw [tensorIteratedFDerivWithinTwo]; rw [lift.tmul]

中文:
引理 tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin
  结论: {e : E} {s : 集合 E} (f : E -> F)
  证明: by
  rw [← bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv f hs he]; rw [tensorIteratedFDerivWithinTwo]; rw [lift.tmul]

Depends on / 依赖: bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv, lift.tmul, tensorIteratedFDerivWithinTwo
-/
lemma tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin {e : E} {s : Set E} (f : E -> F)
    (hs : UniqueDiffOn 𝕜 s) (he : e in s) (e₁ e₂ : E) :
    tensorIteratedFDerivWithinTwo 𝕜 f s e (e₁ otimesₜ[𝕜] e₂) =
      iteratedFDerivWithin 𝕜 2 f s e ![e₁, e₂] := by
  rw [← bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv f hs he]; rw [tensorIteratedFDerivWithinTwo]; rw [lift.tmul]

/--
lemma `tensorIteratedFDerivTwo_eq_iteratedFDeriv` / 引理 `tensorIteratedFDerivTwo_eq_iteratedFDeriv`

English:
lemma tensorIteratedFDerivTwo_eq_iteratedFDeriv
  given: (f : E -> F) (e e₁ e₂ : E)
  proof: by
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]; rw [tensorIteratedFDerivTwo]; rw [lift.tmul]

中文:
引理 tensorIteratedFDerivTwo_eq_iteratedFDeriv
  条件: (f : E -> F) (e e₁ e₂ : E)
  证明: by
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]; rw [tensorIteratedFDerivTwo]; rw [lift.tmul]

Depends on / 依赖: bilinearIteratedFDerivTwo_eq_iteratedFDeriv, lift.tmul, tensorIteratedFDerivTwo
-/
lemma tensorIteratedFDerivTwo_eq_iteratedFDeriv (f : E -> F) (e e₁ e₂ : E) :
    tensorIteratedFDerivTwo 𝕜 f e (e₁ otimesₜ[𝕜] e₂) = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]; rw [tensorIteratedFDerivTwo]; rw [lift.tmul]

end secondDerivativeAPI

/-!
## Definition of the Laplacian
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra Real 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [NormedSpace 𝕜 F] [IsScalarTower Real 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]
  {f f₁ f₂ : E -> F} {x : E} {s : Set E}

namespace InnerProductSpace

variable (f s) in
/--
Laplacian for functions on real inner product spaces, with respect to a set `s`. Use `open
InnerProductSpace` to access the notation `Δ[s]` for `InnerProductSpace.LaplacianWithin`.
-/
@[wikidata Q203484]
/--
Definition of `laplacianWithin` / `laplacianWithin` 的定义

English:
definition laplacianWithin
  signature: : E -> F
  body: fun x => tensorIteratedFDerivWithinTwo Real f s x (InnerProductSpace.canonicalCovariantTensor E)

@[inherit_doc]
scoped[InnerProductSpace] notation "Δ[" s "] " f:60 => laplacianWithin f s

noncomputable

中文:
定义 laplacianWithin
  签名: : E -> F
  定义体: fun x => tensorIteratedFDerivWithinTwo Real f s x (InnerProductSpace.canonicalCovariantTensor E)

@[inherit_doc]
scoped[InnerProductSpace] notation "Δ[" s "] " f:60 => laplacianWithin f s

noncomputable

Depends on / 依赖: InnerProductSpace, InnerProductSpace.canonicalCovariantTensor, canonicalCovariantTensor, tensorIteratedFDerivWithinTwo
-/
noncomputable def laplacianWithin : E -> F :=
  fun x => tensorIteratedFDerivWithinTwo Real f s x (InnerProductSpace.canonicalCovariantTensor E)

@[inherit_doc]
scoped[InnerProductSpace] notation "Δ[" s "] " f:60 => laplacianWithin f s

noncomputable
/--
Instance `instLaplacian` / 实例 `instLaplacian`

English:
instance instLaplacian
  signature: : Laplacian (E -> F) (E -> F) where
  body: tensorIteratedFDerivTwo Real f x (InnerProductSpace.canonicalCovariantTensor E)

中文:
实例 instLaplacian
  签名: : Laplace算子 (E -> F) (E -> F) where
  定义体: tensorIteratedFDerivTwo Real f x (InnerProductSpace.canonicalCovariantTensor E)

Depends on / 依赖: InnerProductSpace, InnerProductSpace.canonicalCovariantTensor, canonicalCovariantTensor, tensorIteratedFDerivTwo
-/
instance instLaplacian : Laplacian (E -> F) (E -> F) where
  laplacian f x := tensorIteratedFDerivTwo Real f x (InnerProductSpace.canonicalCovariantTensor E)

open Laplacian

/--
The Laplacian equals the Laplacian with respect to `Set.univ`.
-/
@[simp]
/--
theorem `laplacianWithin_univ` / 定理 `laplacianWithin_univ`

English:
theorem laplacianWithin_univ
  proof: by
  ext x
  simp [laplacian, tensorIteratedFDerivTwo, bilinearIteratedFDerivTwo,
    laplacianWithin, tensorIteratedFDerivWithinTwo, bilinearIteratedFDerivWithinTwo]

中文:
定理 laplacianWithin_univ
  证明: by
  ext x
  simp [laplacian, tensorIteratedFDerivTwo, bilinearIteratedFDerivTwo,
    laplacianWithin, tensorIteratedFDerivWithinTwo, bilinearIteratedFDerivWithinTwo]

Depends on / 依赖: bilinearIteratedFDerivTwo, bilinearIteratedFDerivWithinTwo, laplacian, laplacianWithin, tensorIteratedFDerivTwo, tensorIteratedFDerivWithinTwo
-/
theorem laplacianWithin_univ :
    Δ[(Set.univ : Set E)] f = Δ f := by
  ext x
  simp [laplacian, tensorIteratedFDerivTwo, bilinearIteratedFDerivTwo,
    laplacianWithin, tensorIteratedFDerivWithinTwo, bilinearIteratedFDerivWithinTwo]

/-!
## Computation of Δ in Terms of Orthonormal Bases
-/

variable (f) in
/--
theorem `laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis` / 定理 `laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis`

English:
theorem laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis
  statement: {ι : Type*} [Fintype ι] {e : E}
  proof: by
  simp [InnerProductSpace.laplacianWithin, canonicalCovariantTensor_eq_sum E v,
    tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin f hs he]

中文:
定理 laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis
  结论: {ι : 类型} [有限类型 ι] {e : E}
  证明: by
  simp [InnerProductSpace.laplacianWithin, canonicalCovariantTensor_eq_sum E v,
    tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin f hs he]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.laplacianWithin, canonicalCovariantTensor_eq_sum, laplacianWithin, tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin
-/
theorem laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis {ι : Type*} [Fintype ι] {e : E}
    (hs : UniqueDiffOn Real s) (he : e in s) (v : OrthonormalBasis ι Real E) :
    (Δ[s] f) e = ∑ i, iteratedFDerivWithin Real 2 f s e ![v i, v i] := by
  simp [InnerProductSpace.laplacianWithin, canonicalCovariantTensor_eq_sum E v,
    tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin f hs he]

variable (f) in
/--
theorem `laplacian_eq_iteratedFDeriv_orthonormalBasis` / 定理 `laplacian_eq_iteratedFDeriv_orthonormalBasis`

English:
theorem laplacian_eq_iteratedFDeriv_orthonormalBasis
  statement: {ι : Type*} [Fintype ι]
  proof: by
  ext x
  simp [laplacian, canonicalCovariantTensor_eq_sum E v, tensorIteratedFDerivTwo_eq_iteratedFDeriv]

中文:
定理 laplacian_eq_iteratedFDeriv_orthonormalBasis
  结论: {ι : 类型} [有限类型 ι]
  证明: by
  ext x
  simp [laplacian, canonicalCovariantTensor_eq_sum E v, tensorIteratedFDerivTwo_eq_iteratedFDeriv]

Depends on / 依赖: canonicalCovariantTensor_eq_sum, laplacian, tensorIteratedFDerivTwo_eq_iteratedFDeriv
-/
theorem laplacian_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι Real E) :
    Δ f = fun x => ∑ i, iteratedFDeriv Real 2 f x ![v i, v i] := by
  ext x
  simp [laplacian, canonicalCovariantTensor_eq_sum E v, tensorIteratedFDerivTwo_eq_iteratedFDeriv]

variable (f) in
/--
theorem `laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis` / 定理 `laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis`

English:
theorem laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis
  statement: {e : E} (hs : UniqueDiffOn Real s)
  proof: by
  apply laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he (stdOrthonormalBasis Real E)

中文:
定理 laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis
  结论: {e : E} (hs : UniqueDiffOn 实数 s)
  证明: by
  apply laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he (stdOrthonormalBasis Real E)

Depends on / 依赖: laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis, stdOrthonormalBasis
-/
theorem laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis {e : E} (hs : UniqueDiffOn Real s)
    (he : e in s) :
    (Δ[s] f) e = ∑ i, iteratedFDerivWithin Real 2 f s e
      ![(stdOrthonormalBasis Real E) i, (stdOrthonormalBasis Real E) i] := by
  apply laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he (stdOrthonormalBasis Real E)

variable (f) in
/--
theorem `laplacian_eq_iteratedFDeriv_stdOrthonormalBasis` / 定理 `laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`

English:
theorem laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
  proof: laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis Real E)

中文:
定理 laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
  证明: laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis Real E)

Depends on / 依赖: laplacian_eq_iteratedFDeriv_orthonormalBasis, stdOrthonormalBasis
-/
theorem laplacian_eq_iteratedFDeriv_stdOrthonormalBasis :
    Δ f = fun x =>
      ∑ i, iteratedFDeriv Real 2 f x ![(stdOrthonormalBasis Real E) i, (stdOrthonormalBasis Real E) i] :=
  laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis Real E)

/--
theorem `laplacianWithin_eq_iteratedDerivWithin_real` / 定理 `laplacianWithin_eq_iteratedDerivWithin_real`

English:
theorem laplacianWithin_eq_iteratedDerivWithin_real
  statement: {e : Real} {s : Set Real} (f : Real -> F)
  proof: by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
        (OrthonormalBasis.singleton (Fin 1) Real),
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, OrthonormalBasis.singleton_apply,
    Finset.sum_const, Finset.card_singleton, one_smul, iteratedDerivWithin_e

中文:
定理 laplacianWithin_eq_iteratedDerivWithin_real
  结论: {e : 实数} {s : 集合 实数} (f : 实数 -> F)
  证明: by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
        (OrthonormalBasis.singleton (Fin 1) Real),
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, OrthonormalBasis.singleton_apply,
    Finset.sum_const, Finset.card_singleton, one_smul, iteratedDerivWithin_e

Depends on / 依赖: Fin.default_eq_zero, Fin.isValue, Finset, Finset.card_singleton, Finset.sum_const, Finset.univ_unique, OrthonormalBasis, OrthonormalBasis.singleton, OrthonormalBasis.singleton_apply, card_singleton, default_eq_zero, fin_cases, isValue, iteratedDerivWithin_eq_iteratedFDerivWithin, laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis, one_smul, singleton, singleton_apply, sum_const, univ_unique
-/
theorem laplacianWithin_eq_iteratedDerivWithin_real {e : Real} {s : Set Real} (f : Real -> F)
    (hs : UniqueDiffOn Real s) (he : e in s) :
    (Δ[s] f) e = iteratedDerivWithin 2 f s e := by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
        (OrthonormalBasis.singleton (Fin 1) Real),
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, OrthonormalBasis.singleton_apply,
    Finset.sum_const, Finset.card_singleton, one_smul, iteratedDerivWithin_eq_iteratedFDerivWithin]
  congr with i
  fin_cases i <;> simp

/-- For a function on `ℝ`, the Laplacian is the second derivative. -/
@[simp]
/--
theorem `laplacian_eq_iteratedDeriv_real` / 定理 `laplacian_eq_iteratedDeriv_real`

English:
theorem laplacian_eq_iteratedDeriv_real
  given: {e : Real} (f : Real -> F)
  proof: by
  rw [← laplacianWithin_univ]; rw [← iteratedDerivWithin_univ]; rw [laplacianWithin_eq_iteratedDerivWithin_real _ (by simp) (by simp)]

中文:
定理 laplacian_eq_iteratedDeriv_real
  条件: {e : 实数} (f : 实数 -> F)
  证明: by
  rw [← laplacianWithin_univ]; rw [← iteratedDerivWithin_univ]; rw [laplacianWithin_eq_iteratedDerivWithin_real _ (by simp) (by simp)]

Depends on / 依赖: iteratedDerivWithin_univ, laplacianWithin_eq_iteratedDerivWithin_real, laplacianWithin_univ
-/
theorem laplacian_eq_iteratedDeriv_real {e : Real} (f : Real -> F) :
    Δ f e = iteratedDeriv 2 f e := by
  rw [← laplacianWithin_univ]; rw [← iteratedDerivWithin_univ]; rw [laplacianWithin_eq_iteratedDerivWithin_real _ (by simp) (by simp)]

/--
theorem `laplacianWithin_eq_iteratedFDerivWithin_complexPlane` / 定理 `laplacianWithin_eq_iteratedFDerivWithin_complexPlane`

English:
theorem laplacianWithin_eq_iteratedFDerivWithin_complexPlane
  statement: {e : Complex} {s : Set Complex} (f : Complex -> F)
  proof: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
    Complex.orthonormalBasisOneI]

中文:
定理 laplacianWithin_eq_iteratedFDerivWithin_complexPlane
  结论: {e : 复形} {s : 集合 复形} (f : 复形 -> F)
  证明: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
    Complex.orthonormalBasisOneI]

Depends on / 依赖: Complex.orthonormalBasisOneI, laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis, orthonormalBasisOneI
-/
theorem laplacianWithin_eq_iteratedFDerivWithin_complexPlane {e : Complex} {s : Set Complex} (f : Complex -> F)
    (hs : UniqueDiffOn Real s) (he : e in s) :
    (Δ[s] f) e = iteratedFDerivWithin Real 2 f s e ![1, 1]
      + iteratedFDerivWithin Real 2 f s e ![Complex.I, Complex.I] := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
    Complex.orthonormalBasisOneI]

/--
theorem `laplacian_eq_iteratedFDeriv_complexPlane` / 定理 `laplacian_eq_iteratedFDeriv_complexPlane`

English:
theorem laplacian_eq_iteratedFDeriv_complexPlane
  given: (f : Complex -> F)
  proof: by
  simp [laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]

中文:
定理 laplacian_eq_iteratedFDeriv_complexPlane
  条件: (f : 复形 -> F)
  证明: by
  simp [laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]

Depends on / 依赖: Complex.orthonormalBasisOneI, laplacian_eq_iteratedFDeriv_orthonormalBasis, orthonormalBasisOneI
-/
theorem laplacian_eq_iteratedFDeriv_complexPlane (f : Complex -> F) :
    Δ f = fun x =>
      iteratedFDeriv Real 2 f x ![1, 1] + iteratedFDeriv Real 2 f x ![Complex.I, Complex.I] := by
  simp [laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]

/--
theorem `laplacian_const` / 定理 `laplacian_const`

English:
theorem laplacian_const
  given: {c : F}
  proof: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_of_ne two_ne_zero,
    Pi.zero_def]

中文:
定理 laplacian_const
  条件: {c : F}
  证明: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_of_ne two_ne_zero,
    Pi.zero_def]
-/
@[simp] theorem laplacian_const {c : F} :
    Laplacian.laplacian (fun (_ : E) => c) = 0 := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_of_ne two_ne_zero,
    Pi.zero_def]

/-!
## Congruence Lemmata for Δ
-/

/--
theorem `laplacianWithin_congr_nhdsWithin` / 定理 `laplacianWithin_congr_nhdsWithin`

English:
theorem laplacianWithin_congr_nhdsWithin
  given: (h : f₁ =ᶠ[𝓝[s] x] f₂) (hs : UniqueDiffOn Real s)
  proof: by
  filter_upwards [EventuallyEq.iteratedFDerivWithin (𝕜 := Real) h 2,
    eventually_mem_nhdsWithin] with x h₁x h₂x
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs h₂x, h₁x]

中文:
定理 laplacianWithin_congr_nhdsWithin
  条件: (h : f₁ =ᶠ[𝓝[s] x] f₂) (hs : UniqueDiffOn 实数 s)
  证明: by
  filter_upwards [EventuallyEq.iteratedFDerivWithin (𝕜 := Real) h 2,
    eventually_mem_nhdsWithin] with x h₁x h₂x
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs h₂x, h₁x]

Depends on / 依赖: EventuallyEq, EventuallyEq.iteratedFDerivWithin, eventually_mem_nhdsWithin, filter_upwards, iteratedFDerivWithin, laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis
-/
theorem laplacianWithin_congr_nhdsWithin (h : f₁ =ᶠ[𝓝[s] x] f₂) (hs : UniqueDiffOn Real s) :
    Δ[s] f₁ =ᶠ[𝓝[s] x] Δ[s] f₂ := by
  filter_upwards [EventuallyEq.iteratedFDerivWithin (𝕜 := Real) h 2,
    eventually_mem_nhdsWithin] with x h₁x h₂x
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs h₂x, h₁x]

/--
theorem `laplacian_congr_nhds` / 定理 `laplacian_congr_nhds`

English:
theorem laplacian_congr_nhds
  given: (h : f₁ =ᶠ[𝓝 x] f₂)
  proof: by
  filter_upwards [EventuallyEq.iteratedFDeriv Real h 2] with x hx
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hx]

中文:
定理 laplacian_congr_nhds
  条件: (h : f₁ =ᶠ[𝓝 x] f₂)
  证明: by
  filter_upwards [EventuallyEq.iteratedFDeriv Real h 2] with x hx
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hx]

Depends on / 依赖: EventuallyEq, EventuallyEq.iteratedFDeriv, filter_upwards, iteratedFDeriv, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
-/
theorem laplacian_congr_nhds (h : f₁ =ᶠ[𝓝 x] f₂) :
    Δ f₁ =ᶠ[𝓝 x] Δ f₂ := by
  filter_upwards [EventuallyEq.iteratedFDeriv Real h 2] with x hx
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hx]

/-!
## 𝕜-Linearity of Δ on Continuously Differentiable Functions
-/

/--
theorem `_root_.ContDiffWithinAt.laplacianWithin_add` / 定理 `_root_.ContDiffWithinAt.laplacianWithin_add`

English:
theorem _root_.ContDiffWithinAt.laplacianWithin_add
  statement: (h₁ : ContDiffWithinAt Real 2 f₁ s x)
  proof: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_add_distrib, iteratedFDerivWithin_add_apply h₁ h₂ hs hx]

中文:
定理 _root_.ContDiffWithinAt.laplacianWithin_add
  结论: (h₁ : ContDiffWithinAt 实数 2 f₁ s x)
  证明: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_add_distrib, iteratedFDerivWithin_add_apply h₁ h₂ hs hx]

Depends on / 依赖: Finset, Finset.sum_add_distrib, iteratedFDerivWithin_add_apply, laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis, sum_add_distrib
-/
theorem _root_.ContDiffWithinAt.laplacianWithin_add (h₁ : ContDiffWithinAt Real 2 f₁ s x)
    (h₂ : ContDiffWithinAt Real 2 f₂ s x) (hs : UniqueDiffOn Real s) (hx : x in s) :
    (Δ[s] (f₁ + f₂)) x = (Δ[s] f₁) x + (Δ[s] f₂) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_add_distrib, iteratedFDerivWithin_add_apply h₁ h₂ hs hx]

/--
theorem `_root_.ContDiffAt.laplacian_add` / 定理 `_root_.ContDiffAt.laplacian_add`

English:
theorem _root_.ContDiffAt.laplacian_add
  given: (h₁ : ContDiffAt Real 2 f₁ x) (h₂ : ContDiffAt Real 2 f₂ x)
  proof: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_add_distrib, iteratedFDeriv_add_apply h₁ h₂]

中文:
定理 _root_.ContDiffAt.laplacian_add
  条件: (h₁ : ContDiffAt 实数 2 f₁ x) (h₂ : ContDiffAt 实数 2 f₂ x)
  证明: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_add_distrib, iteratedFDeriv_add_apply h₁ h₂]

Depends on / 依赖: Finset, Finset.sum_add_distrib, iteratedFDeriv_add_apply, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, sum_add_distrib
-/
theorem _root_.ContDiffAt.laplacian_add (h₁ : ContDiffAt Real 2 f₁ x) (h₂ : ContDiffAt Real 2 f₂ x) :
    Δ (f₁ + f₂) x = Δ f₁ x + Δ f₂ x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_add_distrib, iteratedFDeriv_add_apply h₁ h₂]

/--
theorem `_root_.ContDiffAt.laplacianWithin_add_nhdsWithin` / 定理 `_root_.ContDiffAt.laplacianWithin_add_nhdsWithin`

English:
theorem _root_.ContDiffAt.laplacianWithin_add_nhdsWithin
  statement: (h₁ : ContDiffWithinAt Real 2 f₁ s x)
  proof: by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_add h₂y hs h₃y]

中文:
定理 _root_.ContDiffAt.laplacianWithin_add_nhdsWithin
  结论: (h₁ : ContDiffWithinAt 实数 2 f₁ s x)
  证明: by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_add h₂y hs h₃y]

Depends on / 依赖: eventually, eventually_mem_nhdsWithin, filter_upwards, insert_eq_of_mem, laplacianWithin_add, nth_rw, s.insert_eq_of_mem, y.laplacianWithin_add
-/
theorem _root_.ContDiffAt.laplacianWithin_add_nhdsWithin (h₁ : ContDiffWithinAt Real 2 f₁ s x)
    (h₂ : ContDiffWithinAt Real 2 f₂ s x) (hs : UniqueDiffOn Real s) (hx : x in s) :
    Δ[s] (f₁ + f₂) =ᶠ[𝓝[s] x] (Δ[s] f₁) + Δ[s] f₂ := by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_add h₂y hs h₃y]

/--
theorem `_root_.ContDiffAt.laplacian_add_nhds` / 定理 `_root_.ContDiffAt.laplacian_add_nhds`

English:
theorem _root_.ContDiffAt.laplacian_add_nhds
  given: (h₁ : ContDiffAt Real 2 f₁ x) (h₂ : ContDiffAt Real 2 f₂ x)
  proof: by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_add h₂x

中文:
定理 _root_.ContDiffAt.laplacian_add_nhds
  条件: (h₁ : ContDiffAt 实数 2 f₁ x) (h₂ : ContDiffAt 实数 2 f₂ x)
  证明: by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_add h₂x

Depends on / 依赖: eventually, filter_upwards, laplacian_add, x.laplacian_add
-/
theorem _root_.ContDiffAt.laplacian_add_nhds (h₁ : ContDiffAt Real 2 f₁ x) (h₂ : ContDiffAt Real 2 f₂ x) :
    Δ (f₁ + f₂) =ᶠ[𝓝 x] (Δ f₁) + (Δ f₂) := by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_add h₂x

/--
theorem `laplacianWithin_neg` / 定理 `laplacianWithin_neg`

English:
theorem laplacianWithin_neg
  given: (hs : UniqueDiffOn Real s) (hx : x in s)
  proof: by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx]
  rw [iteratedFDerivWithin_neg_apply hs hx]
  aesop

中文:
定理 laplacianWithin_neg
  条件: (hs : UniqueDiffOn 实数 s) (hx : x in s)
  证明: by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx]
  rw [iteratedFDerivWithin_neg_apply hs hx]
  aesop

Depends on / 依赖: iteratedFDerivWithin_neg_apply, laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis
-/
theorem laplacianWithin_neg (hs : UniqueDiffOn Real s) (hx : x in s) :
    (Δ[s] (-f)) x = -(Δ[s] f) x := by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx]
  rw [iteratedFDerivWithin_neg_apply hs hx]
  aesop

/--
theorem `laplacian_neg` / 定理 `laplacian_neg`

English:
theorem laplacian_neg
  proof: by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_neg]
  aesop

中文:
定理 laplacian_neg
  证明: by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_neg]
  aesop

Depends on / 依赖: iteratedFDeriv_neg, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
-/
theorem laplacian_neg :
    Δ (-f) = -(Δ f) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_neg]
  aesop

/--
theorem `_root_.ContDiffWithinAt.laplacianWithin_sub` / 定理 `_root_.ContDiffWithinAt.laplacianWithin_sub`

English:
theorem _root_.ContDiffWithinAt.laplacianWithin_sub
  statement: (h₁ : ContDiffWithinAt Real 2 f₁ s x)
  proof: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_sub_distrib, iteratedFDerivWithin_sub_apply h₁ h₂ hs hx]

中文:
定理 _root_.ContDiffWithinAt.laplacianWithin_sub
  结论: (h₁ : ContDiffWithinAt 实数 2 f₁ s x)
  证明: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_sub_distrib, iteratedFDerivWithin_sub_apply h₁ h₂ hs hx]

Depends on / 依赖: Finset, Finset.sum_sub_distrib, iteratedFDerivWithin_sub_apply, laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis, sum_sub_distrib
-/
theorem _root_.ContDiffWithinAt.laplacianWithin_sub (h₁ : ContDiffWithinAt Real 2 f₁ s x)
    (h₂ : ContDiffWithinAt Real 2 f₂ s x) (hs : UniqueDiffOn Real s) (hx : x in s) :
    (Δ[s] (f₁ - f₂)) x = (Δ[s] f₁) x - (Δ[s] f₂) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_sub_distrib, iteratedFDerivWithin_sub_apply h₁ h₂ hs hx]

/--
theorem `_root_.ContDiffAt.laplacian_sub` / 定理 `_root_.ContDiffAt.laplacian_sub`

English:
theorem _root_.ContDiffAt.laplacian_sub
  given: (h₁ : ContDiffAt Real 2 f₁ x) (h₂ : ContDiffAt Real 2 f₂ x)
  proof: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_sub_distrib, iteratedFDeriv_sub_apply h₁ h₂]

中文:
定理 _root_.ContDiffAt.laplacian_sub
  条件: (h₁ : ContDiffAt 实数 2 f₁ x) (h₂ : ContDiffAt 实数 2 f₂ x)
  证明: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_sub_distrib, iteratedFDeriv_sub_apply h₁ h₂]

Depends on / 依赖: Finset, Finset.sum_sub_distrib, iteratedFDeriv_sub_apply, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, sum_sub_distrib
-/
theorem _root_.ContDiffAt.laplacian_sub (h₁ : ContDiffAt Real 2 f₁ x) (h₂ : ContDiffAt Real 2 f₂ x) :
    Δ (f₁ - f₂) x = Δ f₁ x - Δ f₂ x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_sub_distrib, iteratedFDeriv_sub_apply h₁ h₂]

/--
theorem `_root_.ContDiffAt.laplacianWithin_sub_nhdsWithin` / 定理 `_root_.ContDiffAt.laplacianWithin_sub_nhdsWithin`

English:
theorem _root_.ContDiffAt.laplacianWithin_sub_nhdsWithin
  statement: (h₁ : ContDiffWithinAt Real 2 f₁ s x)
  proof: by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_sub h₂y hs h₃y]

中文:
定理 _root_.ContDiffAt.laplacianWithin_sub_nhdsWithin
  结论: (h₁ : ContDiffWithinAt 实数 2 f₁ s x)
  证明: by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_sub h₂y hs h₃y]

Depends on / 依赖: eventually, eventually_mem_nhdsWithin, filter_upwards, insert_eq_of_mem, laplacianWithin_sub, nth_rw, s.insert_eq_of_mem, y.laplacianWithin_sub
-/
theorem _root_.ContDiffAt.laplacianWithin_sub_nhdsWithin (h₁ : ContDiffWithinAt Real 2 f₁ s x)
    (h₂ : ContDiffWithinAt Real 2 f₂ s x) (hs : UniqueDiffOn Real s) (hx : x in s) :
    Δ[s] (f₁ - f₂) =ᶠ[𝓝[s] x] (Δ[s] f₁) - Δ[s] f₂ := by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_sub h₂y hs h₃y]

/--
theorem `_root_.ContDiffAt.laplacian_sub_nhds` / 定理 `_root_.ContDiffAt.laplacian_sub_nhds`

English:
theorem _root_.ContDiffAt.laplacian_sub_nhds
  given: (h₁ : ContDiffAt Real 2 f₁ x) (h₂ : ContDiffAt Real 2 f₂ x)
  proof: by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_sub h₂x

中文:
定理 _root_.ContDiffAt.laplacian_sub_nhds
  条件: (h₁ : ContDiffAt 实数 2 f₁ x) (h₂ : ContDiffAt 实数 2 f₂ x)
  证明: by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_sub h₂x

Depends on / 依赖: eventually, filter_upwards, laplacian_sub, x.laplacian_sub
-/
theorem _root_.ContDiffAt.laplacian_sub_nhds (h₁ : ContDiffAt Real 2 f₁ x) (h₂ : ContDiffAt Real 2 f₂ x) :
    Δ (f₁ - f₂) =ᶠ[𝓝 x] (Δ f₁) - (Δ f₂) := by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_sub h₂x

/--
theorem `laplacianWithin_smul` / 定理 `laplacianWithin_smul`

English:
theorem laplacianWithin_smul
  statement: (v : 𝕜) (hf : ContDiffWithinAt Real 2 f s x) (hs : UniqueDiffOn Real s)
  proof: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    iteratedFDerivWithin_const_smul_apply hf hs hx,
    Finset.smul_sum]

中文:
定理 laplacianWithin_smul
  结论: (v : 𝕜) (hf : ContDiffWithinAt 实数 2 f s x) (hs : UniqueDiffOn 实数 s)
  证明: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    iteratedFDerivWithin_const_smul_apply hf hs hx,
    Finset.smul_sum]

Depends on / 依赖: Finset, Finset.smul_sum, iteratedFDerivWithin_const_smul_apply, laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis, smul_sum
-/
theorem laplacianWithin_smul (v : 𝕜) (hf : ContDiffWithinAt Real 2 f s x) (hs : UniqueDiffOn Real s)
    (hx : x in s) :
    (Δ[s] (v • f)) x = v • (Δ[s] f) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    iteratedFDerivWithin_const_smul_apply hf hs hx,
    Finset.smul_sum]

/--
theorem `laplacian_smul` / 定理 `laplacian_smul`

English:
theorem laplacian_smul
  given: (v : 𝕜) (hf : ContDiffAt Real 2 f x)
  statement: Δ (v • f) x = v • (Δ f) x
  proof: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_smul_apply hf,
    Finset.smul_sum]

中文:
定理 laplacian_smul
  条件: (v : 𝕜) (hf : ContDiffAt 实数 2 f x)
  结论: Δ (v • f) x = v • (Δ f) x
  证明: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_smul_apply hf,
    Finset.smul_sum]

Depends on / 依赖: Finset, Finset.smul_sum, iteratedFDeriv_const_smul_apply, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, smul_sum
-/
theorem laplacian_smul (v : 𝕜) (hf : ContDiffAt Real 2 f x) : Δ (v • f) x = v • (Δ f) x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_smul_apply hf,
    Finset.smul_sum]

/--
theorem `laplacianWithin_smul_nhds` / 定理 `laplacianWithin_smul_nhds`

English:
theorem laplacianWithin_smul_nhds
  proof: by
  filter_upwards [(hf.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using laplacianWithin_smul v h₁a hs

中文:
定理 laplacianWithin_smul_nhds
  证明: by
  filter_upwards [(hf.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using laplacianWithin_smul v h₁a hs

Depends on / 依赖: Set.subset_insert, eventually, eventually_mem_nhdsWithin, filter_mono, filter_upwards, hf.eventually, laplacianWithin_smul, nhdsWithin_mono, subset_insert
-/
theorem laplacianWithin_smul_nhds
    (v : 𝕜) (hf : ContDiffWithinAt Real 2 f s x) (hs : UniqueDiffOn Real s) :
    Δ[s] (v • f) =ᶠ[𝓝[s] x] v • (Δ[s] f) := by
  filter_upwards [(hf.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using laplacianWithin_smul v h₁a hs

/--
theorem `laplacian_smul_nhds` / 定理 `laplacian_smul_nhds`

English:
theorem laplacian_smul_nhds
  given: (v : 𝕜) (h : ContDiffAt Real 2 f x)
  proof: by
  filter_upwards [h.eventually (by simp)] with a ha
  simp [laplacian_smul v ha]

中文:
定理 laplacian_smul_nhds
  条件: (v : 𝕜) (h : ContDiffAt 实数 2 f x)
  证明: by
  filter_upwards [h.eventually (by simp)] with a ha
  simp [laplacian_smul v ha]

Depends on / 依赖: eventually, filter_upwards, h.eventually, laplacian_smul
-/
theorem laplacian_smul_nhds (v : 𝕜) (h : ContDiffAt Real 2 f x) :
    Δ (v • f) =ᶠ[𝓝 x] v • (Δ f) := by
  filter_upwards [h.eventually (by simp)] with a ha
  simp [laplacian_smul v ha]

/-!
## Commutativity of Δ with Linear Operators

This section establishes commutativity with linear operators, showing in particular that `Δ`
commutes with taking real and imaginary parts of complex-valued functions.
-/

/--
theorem `_root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left` / 定理 `_root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left`

English:
theorem _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left
  statement: {l : F ->L[Real] G}
  proof: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left h hs hx]

中文:
定理 _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left
  结论: {l : F ->L[实数] G}
  证明: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left h hs hx]

Depends on / 依赖: iteratedFDerivWithin_comp_left, l.iteratedFDerivWithin_comp_left, laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis
-/
theorem _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left {l : F ->L[Real] G}
    (h : ContDiffWithinAt Real 2 f s x) (hs : UniqueDiffOn Real s) (hx : x in s) :
    (Δ[s] (l ∘ f)) x = (l ∘ (Δ[s] f)) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left h hs hx]

/--
theorem `_root_.ContDiffAt.laplacian_CLM_comp_left` / 定理 `_root_.ContDiffAt.laplacian_CLM_comp_left`

English:
theorem _root_.ContDiffAt.laplacian_CLM_comp_left
  given: {l : F ->L[Real] G} (h : ContDiffAt Real 2 f x)
  proof: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left h]

中文:
定理 _root_.ContDiffAt.laplacian_CLM_comp_left
  条件: {l : F ->L[实数] G} (h : ContDiffAt 实数 2 f x)
  证明: by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left h]

Depends on / 依赖: iteratedFDeriv_comp_left, l.iteratedFDeriv_comp_left, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
-/
theorem _root_.ContDiffAt.laplacian_CLM_comp_left {l : F ->L[Real] G} (h : ContDiffAt Real 2 f x) :
    Δ (l ∘ f) x = (l ∘ (Δ f)) x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left h]

/--
theorem `_root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left_nhds` / 定理 `_root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left_nhds`

English:
theorem _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left_nhds
  statement: {l : F ->L[Real] G}
  proof: by
  filter_upwards [(h.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using h₁a.laplacianWithin_CLM_comp_left hs

中文:
定理 _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left_nhds
  结论: {l : F ->L[实数] G}
  证明: by
  filter_upwards [(h.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using h₁a.laplacianWithin_CLM_comp_left hs

Depends on / 依赖: Set.subset_insert, a.laplacianWithin_CLM_comp_left, eventually, eventually_mem_nhdsWithin, filter_mono, filter_upwards, h.eventually, laplacianWithin_CLM_comp_left, nhdsWithin_mono, subset_insert
-/
theorem _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left_nhds {l : F ->L[Real] G}
    (h : ContDiffWithinAt Real 2 f s x) (hs : UniqueDiffOn Real s) :
    Δ[s] (l ∘ f) =ᶠ[𝓝[s] x] l ∘ Δ[s] f := by
  filter_upwards [(h.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using h₁a.laplacianWithin_CLM_comp_left hs

/--
theorem `_root_.ContDiffAt.laplacian_CLM_comp_left_nhds` / 定理 `_root_.ContDiffAt.laplacian_CLM_comp_left_nhds`

English:
theorem _root_.ContDiffAt.laplacian_CLM_comp_left_nhds
  given: {l : F ->L[Real] G} (h : ContDiffAt Real 2 f x)
  proof: by
  filter_upwards [h.eventually (by simp)] with a ha
  rw [ha.laplacian_CLM_comp_left]

中文:
定理 _root_.ContDiffAt.laplacian_CLM_comp_left_nhds
  条件: {l : F ->L[实数] G} (h : ContDiffAt 实数 2 f x)
  证明: by
  filter_upwards [h.eventually (by simp)] with a ha
  rw [ha.laplacian_CLM_comp_left]

Depends on / 依赖: eventually, filter_upwards, h.eventually, ha.laplacian_CLM_comp_left, laplacian_CLM_comp_left
-/
theorem _root_.ContDiffAt.laplacian_CLM_comp_left_nhds {l : F ->L[Real] G} (h : ContDiffAt Real 2 f x) :
    Δ (l ∘ f) =ᶠ[𝓝 x] l ∘ (Δ f) := by
  filter_upwards [h.eventually (by simp)] with a ha
  rw [ha.laplacian_CLM_comp_left]

/--
theorem `laplacianWithin_CLE_comp_left` / 定理 `laplacianWithin_CLE_comp_left`

English:
theorem laplacianWithin_CLE_comp_left
  given: {l : F ≃L[Real] G} (hs : UniqueDiffOn Real s) (hx : x in s)
  proof: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left _ hs hx]

中文:
定理 laplacianWithin_CLE_comp_left
  条件: {l : F ≃L[实数] G} (hs : UniqueDiffOn 实数 s) (hx : x in s)
  证明: by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left _ hs hx]

Depends on / 依赖: iteratedFDerivWithin_comp_left, l.iteratedFDerivWithin_comp_left, laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis
-/
theorem laplacianWithin_CLE_comp_left {l : F ≃L[Real] G} (hs : UniqueDiffOn Real s) (hx : x in s) :
    (Δ[s] (l ∘ f)) x = (l ∘ (Δ[s] f)) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left _ hs hx]

/--
theorem `laplacian_CLE_comp_left` / 定理 `laplacian_CLE_comp_left`

English:
theorem laplacian_CLE_comp_left
  given: {l : F ≃L[Real] G}
  proof: by
  ext x
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left]

中文:
定理 laplacian_CLE_comp_left
  条件: {l : F ≃L[实数] G}
  证明: by
  ext x
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left]

Depends on / 依赖: iteratedFDeriv_comp_left, l.iteratedFDeriv_comp_left, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
-/
theorem laplacian_CLE_comp_left {l : F ≃L[Real] G} :
    Δ (l ∘ f) = l ∘ (Δ f) := by
  ext x
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left]

end InnerProductSpace
