/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Topology.ContinuousMap.Units

/-!
# Continuous Functional Calculus for Hermitian Matrices

This file defines an instance of the continuous functional calculus for Hermitian matrices over an
`RCLike` field `𝕜`.

## Main Results

- `Matrix.IsHermitian.cfc` : Realization of the functional calculus for a Hermitian matrix
  as the triple product `U * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) * star U` with
  `U = eigenvectorUnitary hA`.

- `cfc_eq` : Proof that the above agrees with the continuous functional calculus.

- `Matrix.IsHermitian.instContinuousFunctionalCalculus` : Instance of the continuous functional
  calculus for a Hermitian matrix `A` over `𝕜`.

## Tags

spectral theorem, diagonalization theorem, continuous functional calculus
-/

@[expose] public section

open Topology Unitary

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

namespace IsHermitian

variable (hA : IsHermitian A)

/-- The star algebra homomorphism underlying the instance of the continuous functional
calculus of a Hermitian matrix. This is an auxiliary definition and is not intended
for use outside of this file. -/
@[simps]
/--
Definition of `cfcAux` / `cfcAux` 的定义

English:
definition cfcAux
  signature: : C(spectrum Real A, Real) ->⋆ₐ[Real] (Matrix n n 𝕜) where
  body: conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
    diagonal (RCLike.ofReal ∘ g ∘ fun i => ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩)
  map_zero' := by simp [Pi.zero_def, Function.comp_def]
  map_one' := by simp [Pi.one_def, Function.comp_def]
  map_mul' f g := by
    simp only [ContinuousMap.

中文:
定义 cfcAux
  签名: : C(spectrum 实数 A, 实数) ->⋆ₐ[实数] (矩阵 n n 𝕜) where
  定义体: conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
    diagonal (RCLike.ofReal ∘ g ∘ fun i => ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩)
  map_zero' := by simp [Pi.zero_def, Function.comp_def]
  map_one' := by simp [Pi.one_def, Function.comp_def]
  map_mul' f g := by
    simp only [ContinuousMap.

Depends on / 依赖: conjStarAlgAut, eigenvectorUnitary, hA.eigenvectorUnitary
-/
noncomputable def cfcAux : C(spectrum Real A, Real) ->⋆ₐ[Real] (Matrix n n 𝕜) where
toFun g := conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
    diagonal (RCLike.ofReal ∘ g ∘ fun i => ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩)
  map_zero' := by simp [Pi.zero_def, Function.comp_def]
  map_one' := by simp [Pi.one_def, Function.comp_def]
  map_mul' f g := by
    simp only [ContinuousMap.coe_mul, ← map_mul, diagonal_mul_diagonal, Function.comp_apply]
    rfl
  map_add' f g := by
    simp only [ContinuousMap.coe_add, ← map_add, diagonal_add, Function.comp_apply]
    rfl
  commutes' r := by
    simp only [Function.comp_def, algebraMap_apply, smul_eq_mul, mul_one]
    rw [← mul_one (algebraMap _ _ _)]; rw [← coe_mul_star_self hA.eigenvectorUnitary]; rw [← Algebra.left_comm]; rw [coe_star]; rw [← mul_assoc]; rw [conjStarAlgAut_apply]
    rfl
  map_star' f := by
    simp only [star_trivial, ← map_star, star_eq_conjTranspose, diagonal_conjTranspose, Pi.star_def,
      Function.comp_apply, RCLike.star_def, RCLike.conj_ofReal]
    rfl

/--
lemma `isClosedEmbedding_cfcAux` / 引理 `isClosedEmbedding_cfcAux`

English:
lemma isClosedEmbedding_cfcAux
  statement: IsClosedEmbedding hA.cfcAux
  proof: by
  have h0 : FiniteDimensional Real C(spectrum Real A, Real) :=
    FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap Real (M := Real)) DFunLike.coe_injective
  refine LinearMap.isClosedEmbedding_of_injective (𝕜 := Real) (E := C(spectrum Real A, Real))
(F := Matrix n n 𝕜) (f := hA.cfcAu

中文:
引理 isClosedEmbedding_cfcAux
  结论: 是闭嵌入 hA.cfcAux
  证明: by
  have h0 : FiniteDimensional Real C(spectrum Real A, Real) :=
    FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap Real (M := Real)) DFunLike.coe_injective
  refine LinearMap.isClosedEmbedding_of_injective (𝕜 := Real) (E := C(spectrum Real A, Real))
(F := Matrix n n 𝕜) (f := hA.cfcAu

Depends on / 依赖: ContinuousMap, ContinuousMap.coeFnLinearMap, DFunLike, DFunLike.coe_injective, FiniteDimensional, FiniteDimensional.of_injective, LinearMap, LinearMap.coe_coe, LinearMap.isClosedEmbedding_of_injective, LinearMap.ker_eq_bot, Matrix, RCLike, RCLike.ofReal, cfcAux, coeFnLinearMap, coe_coe, coe_injective, diagonal, eigenvalues, eigenvalues_mem_spectrum_real
-/
lemma isClosedEmbedding_cfcAux : IsClosedEmbedding hA.cfcAux := by
  have h0 : FiniteDimensional Real C(spectrum Real A, Real) :=
    FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap Real (M := Real)) DFunLike.coe_injective
  refine LinearMap.isClosedEmbedding_of_injective (𝕜 := Real) (E := C(spectrum Real A, Real))
(F := Matrix n n 𝕜) (f := hA.cfcAux) LinearMap.ker_eq_bot'.mpr fun f hf => ?_
  have h2 :
      diagonal (RCLike.ofReal ∘ f ∘ fun i => ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩)
        = (0 : Matrix n n 𝕜) := by
    simp only [LinearMap.coe_coe, cfcAux_apply, conjStarAlgAut_apply] at hf
    replace hf := congr($hf * (hA.eigenvectorUnitary : Matrix n n 𝕜))
    simp only [mul_assoc, SetLike.coe_mem, Unitary.star_mul_self_of_mem, mul_one, zero_mul] at hf
    simpa [← mul_assoc] using congr((star hA.eigenvectorUnitary : Matrix n n 𝕜) * $hf)
  ext x
  simp only [ContinuousMap.zero_apply]
  obtain ⟨x, hx⟩ := x
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  rw [← diagonal_zero] at h2
  have := diagonal_eq_diagonal_iff.mp h2
  exact RCLike.ofReal_eq_zero.mp (this i)

/--
lemma `cfcAux_id` / 引理 `cfcAux_id`

English:
lemma cfcAux_id
  statement: hA.cfcAux (.restrict (spectrum Real A) (.id Real)) = A
  proof: by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

中文:
引理 cfcAux_id
  结论: hA.cfcAux (.restrict (spectrum 实数 A) (.id 实数)) = A
  证明: by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

Depends on / 依赖: conv_rhs, hA.spectral_theorem, spectral_theorem
-/
lemma cfcAux_id : hA.cfcAux (.restrict (spectrum Real A) (.id Real)) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

/--
Instance `instContinuousFunctionalCalculus` / 实例 `instContinuousFunctionalCalculus`

English:
instance instContinuousFunctionalCalculus
  signature: :
  body: by
    replace ha : IsHermitian a := ha
    refine ⟨ha.cfcAux, ha.isClosedEmbedding_cfcAux.continuous,
      ha.isClosedEmbedding_cfcAux.injective, ha.cfcAux_id, fun f => ?map_spec,
      fun f => ?hermitian⟩
    case map_spec =>
      apply Set.eq_of_subset_of_subset
      · rw [← ContinuousMap.spe

中文:
实例 instContinuousFunctionalCalculus
  签名: :
  定义体: by
    replace ha : IsHermitian a := ha
    refine ⟨ha.cfcAux, ha.isClosedEmbedding_cfcAux.continuous,
      ha.isClosedEmbedding_cfcAux.injective, ha.cfcAux_id, fun f => ?map_spec,
      fun f => ?hermitian⟩
    case map_spec =>
      apply Set.eq_of_subset_of_subset
      · rw [← ContinuousMap.spe

Depends on / 依赖: AlgHom, AlgHom.spectrum_apply_subset, ContinuousMap, ContinuousMap.spectrum_eq_range, Function, Function.comp_apply, IsHermitian, Set.eq_of_subset_of_subset, Set.mem_range, Unitary, Unitary.spectrum_star_right_conjugate, cfcAux, cfcAux_apply, cfcAux_id, comp_apply, conjStarAlgAut_apply, continuous, eq_of_subset_of_subset, ha.cfcAux, ha.cfcAux_id
-/
instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus Real (Matrix n n 𝕜) IsSelfAdjoint where
  exists_cfc_of_predicate a ha := by
    replace ha : IsHermitian a := ha
    refine ⟨ha.cfcAux, ha.isClosedEmbedding_cfcAux.continuous,
      ha.isClosedEmbedding_cfcAux.injective, ha.cfcAux_id, fun f => ?map_spec,
      fun f => ?hermitian⟩
    case map_spec =>
      apply Set.eq_of_subset_of_subset
      · rw [← ContinuousMap.spectrum_eq_range f]
        apply AlgHom.spectrum_apply_subset
      · rw [cfcAux_apply, conjStarAlgAut_apply, Unitary.spectrum_star_right_conjugate]
        rintro - ⟨x, rfl⟩
        apply spectrum.of_algebraMap_mem 𝕜
        simp only [Function.comp_apply, Set.mem_range, spectrum_diagonal]
        obtain ⟨x, hx⟩ := x
        obtain ⟨i, rfl⟩ := ha.spectrum_real_eq_range_eigenvalues ▸ hx
        exact ⟨i, rfl⟩
    case hermitian =>
      simp only [isSelfAdjoint_iff, cfcAux_apply, ← map_star]
      rw [star_eq_conjTranspose]; rw [diagonal_conjTranspose]
      congr!
      simp [Pi.star_def, Function.comp_def]
  spectrum_nonempty a ha := by
    obtain (h | h) := isEmpty_or_nonempty n
    · obtain ⟨x, y, hxy⟩ := exists_pair_ne (Matrix n n 𝕜)
exact False.elim Matrix.of.symm.injective.ne hxy Subsingleton.elim _ _
    · exact spectrum_real_eq_range_eigenvalues ha ▸ Set.range_nonempty _
  predicate_zero := .zero _

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def cfc (f : Real -> Real)
  body: conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues))

中文:
定义 noncomputable
  签名: def cfc (f : 实数 -> 实数)
  定义体: conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues))
-/
protected noncomputable def cfc (f : Real -> Real) : Matrix n n 𝕜 :=
  conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues))

/--
lemma `cfcHom_eq_cfcAux` / 引理 `cfcHom_eq_cfcAux`

English:
lemma cfcHom_eq_cfcAux
  statement: cfcHom hA.isSelfAdjoint = hA.cfcAux
  proof: cfcHom_eq_of_continuous_of_map_id hA hA.cfcAux
    hA.isClosedEmbedding_cfcAux.continuous hA.cfcAux_id

中文:
引理 cfcHom_eq_cfcAux
  结论: cfcHom hA.isSelfAdjoint = hA.cfcAux
  证明: cfcHom_eq_of_continuous_of_map_id hA hA.cfcAux
    hA.isClosedEmbedding_cfcAux.continuous hA.cfcAux_id

Depends on / 依赖: cfcAux, cfcAux_id, cfcHom_eq_of_continuous_of_map_id, continuous, hA.cfcAux, hA.cfcAux_id, hA.isClosedEmbedding_cfcAux.continuous, isClosedEmbedding_cfcAux
-/
lemma cfcHom_eq_cfcAux : cfcHom hA.isSelfAdjoint = hA.cfcAux :=
  cfcHom_eq_of_continuous_of_map_id hA hA.cfcAux
    hA.isClosedEmbedding_cfcAux.continuous hA.cfcAux_id

/--
Instance `instContinuousFunctionalCalculusIsClosedEmbedding` / 实例 `instContinuousFunctionalCalculusIsClosedEmbedding`

English:
instance instContinuousFunctionalCalculusIsClosedEmbedding
  signature: :
  body: cfcHom_eq_cfcAux hA ▸ hA.isHermitian.isClosedEmbedding_cfcAux

中文:
实例 instContinuousFunctionalCalculusIsClosedEmbedding
  签名: :
  定义体: cfcHom_eq_cfcAux hA ▸ hA.isHermitian.isClosedEmbedding_cfcAux

Depends on / 依赖: cfcHom_eq_cfcAux, hA.isHermitian.isClosedEmbedding_cfcAux, isClosedEmbedding_cfcAux, isHermitian
-/
instance instContinuousFunctionalCalculusIsClosedEmbedding :
    ClosedEmbeddingContinuousFunctionalCalculus Real (Matrix n n 𝕜) IsSelfAdjoint where
  isClosedEmbedding _ hA := cfcHom_eq_cfcAux hA ▸ hA.isHermitian.isClosedEmbedding_cfcAux

/--
lemma `cfc_eq` / 引理 `cfc_eq`

English:
lemma cfc_eq
  given: (f : Real -> Real)
  statement: cfc f A = hA.cfc f
  proof: by
  have hA' : IsSelfAdjoint A := hA
  have := cfcHom_eq_of_continuous_of_map_id hA' hA.cfcAux hA.isClosedEmbedding_cfcAux.continuous
    hA.cfcAux_id
  rw [cfc_apply f A hA' (by rw [continuousOn_iff_continuous_domRestrict]; fun_prop), this]
  simp only [cfcAux_apply, ContinuousMap.coe_mk, Function

中文:
引理 cfc_eq
  条件: (f : 实数 -> 实数)
  结论: cfc f A = hA.cfc f
  证明: by
  have hA' : IsSelfAdjoint A := hA
  have := cfcHom_eq_of_continuous_of_map_id hA' hA.cfcAux hA.isClosedEmbedding_cfcAux.continuous
    hA.cfcAux_id
  rw [cfc_apply f A hA' (by rw [continuousOn_iff_continuous_domRestrict]; fun_prop), this]
  simp only [cfcAux_apply, ContinuousMap.coe_mk, Function

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, Function, Function.comp_def, IsHermitian, IsHermitian.cfc, IsSelfAdjoint, Set.domRestrict_apply, cfcAux, cfcAux_apply, cfcAux_id, cfcHom_eq_of_continuous_of_map_id, cfc_apply, coe_mk, comp_def, continuous, continuousOn_iff_continuous_domRestrict, domRestrict_apply, fun_prop, hA.cfcAux
-/
lemma cfc_eq (f : Real -> Real) : cfc f A = hA.cfc f := by
  have hA' : IsSelfAdjoint A := hA
  have := cfcHom_eq_of_continuous_of_map_id hA' hA.cfcAux hA.isClosedEmbedding_cfcAux.continuous
    hA.cfcAux_id
  rw [cfc_apply f A hA' (by rw [continuousOn_iff_continuous_domRestrict]; fun_prop), this]
  simp only [cfcAux_apply, ContinuousMap.coe_mk, Function.comp_def, Set.domRestrict_apply,
    IsHermitian.cfc]

open Polynomial in
/--
lemma `charpoly_cfc_eq` / 引理 `charpoly_cfc_eq`

English:
lemma charpoly_cfc_eq
  given: (f : Real -> Real)
  proof: by
  rw [cfc_eq hA f]; rw [IsHermitian.cfc]; rw [conjStarAlgAut_apply]; rw [charpoly_mul_comm]; rw [← mul_assoc]
  simp [charpoly_diagonal]

中文:
引理 charpoly_cfc_eq
  条件: (f : 实数 -> 实数)
  证明: by
  rw [cfc_eq hA f]; rw [IsHermitian.cfc]; rw [conjStarAlgAut_apply]; rw [charpoly_mul_comm]; rw [← mul_assoc]
  simp [charpoly_diagonal]

Depends on / 依赖: IsHermitian, IsHermitian.cfc, cfc_eq, charpoly_diagonal, charpoly_mul_comm, conjStarAlgAut_apply, mul_assoc
-/
lemma charpoly_cfc_eq (f : Real -> Real) :
    (cfc f A).charpoly = ∏ i, (X - C (f (hA.eigenvalues i) : 𝕜)) := by
  rw [cfc_eq hA f]; rw [IsHermitian.cfc]; rw [conjStarAlgAut_apply]; rw [charpoly_mul_comm]; rw [← mul_assoc]
  simp [charpoly_diagonal]

end IsHermitian
end Matrix
