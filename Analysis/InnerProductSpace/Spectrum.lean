/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Data.Fin.Tuple.Sort

/-! # Spectral theory of self-adjoint operators

This file covers the spectral theory of self-adjoint operators on an inner product space.

The first part of the file covers general properties, true without any condition on boundedness or
compactness of the operator or finite-dimensionality of the underlying space, notably:
* `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`: the eigenvalues are real
* `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`: the eigenspaces are orthogonal
* `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces`: the restriction of the operator to
  the mutual orthogonal complement of the eigenspaces has, itself, no eigenvectors

The second part of the file covers properties of self-adjoint operators in finite dimension.
Letting `T` be a self-adjoint operator on a finite-dimensional inner product space `T`,
* The definition `LinearMap.IsSymmetric.diagonalization` provides a linear isometry equivalence `E`
  to the direct sum of the eigenspaces of `T`. The theorem
  `LinearMap.IsSymmetric.diagonalization_apply_self_apply` states that, when `T` is transferred via
  this equivalence to an operator on the direct sum, it acts diagonally.
* The definition `LinearMap.IsSymmetric.eigenvectorBasis` provides an orthonormal basis for `E`
  consisting of eigenvectors of `T`, with `LinearMap.IsSymmetric.eigenvalues` giving the
  corresponding list of eigenvalues, as real numbers. The definition
  `LinearMap.IsSymmetric.eigenvectorBasis` gives the associated linear isometry equivalence
  from `E` to Euclidean space, and the theorem
  `LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply` states that, when `T` is
  transferred via this equivalence to an operator on Euclidean space, it acts diagonally.
* `LinearMap.IsSymmetric.eigenvalues` gives the eigenvalues in decreasing order. This is
  done for several reasons: (i) This agrees with the standard convention of listing singular
  values in decreasing order, with the operator norm as the first singular value
  (ii) For positive compact operators on an infinite-dimensional space, one can list the nonzero
  eigenvalues in decreasing (but not increasing) order since they converge to zero. (iii) This
  simplifies several theorem statements. For example the Schur-Horn theorem states that the diagonal
  of the matrix representation of a selfadjoint linear map is majorized by the eigenvalue sequence
  listed in decreasing order.

These are forms of the *diagonalization theorem* for self-adjoint operators on finite-dimensional
inner product spaces.

The third part of the file covers properties of compact self-adjoint operators:
* `orthogonalComplement_iSup_eigenspaces_eq_bot`: the eigenspaces of a compact self-adjoint operator
  have trivial orthogonal complement.
* `finite_dimensional_eigenspace`: the eigenspaces of a compact self-adjoint operator are
  finite-dimensional.

## TODO

Spectral theory for bounded self-adjoint operators.

## Tags

self-adjoint operator, spectral theorem, diagonalization theorem

-/

@[expose] public section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped ComplexConjugate

open Module End WithLp

namespace LinearMap

namespace IsSymmetric

variable {T : E ->ₗ[𝕜] E}

/--
theorem `invariant_orthogonalComplement_eigenspace` / 定理 `invariant_orthogonalComplement_eigenspace`

English:
theorem invariant_orthogonalComplement_eigenspace
  statement: (hT : T.IsSymmetric) (μ : 𝕜)
  proof: by
  intro w hw
  have : T w = (μ : 𝕜) • w := by rwa [mem_eigenspace_iff] at hw
  simp [← hT w, this, inner_smul_left, hv w hw]

中文:
定理 invariant_orthogonalComplement_eigenspace
  结论: (hT : T.IsSymmetric) (μ : 𝕜)
  证明: by
  intro w hw
  have : T w = (μ : 𝕜) • w := by rwa [mem_eigenspace_iff] at hw
  simp [← hT w, this, inner_smul_left, hv w hw]

Depends on / 依赖: inner_smul_left, mem_eigenspace_iff
-/
theorem invariant_orthogonalComplement_eigenspace (hT : T.IsSymmetric) (μ : 𝕜)
    (v : E) (hv : v in (eigenspace T μ)ᗮ) : T v in (eigenspace T μ)ᗮ := by
  intro w hw
  have : T w = (μ : 𝕜) • w := by rwa [mem_eigenspace_iff] at hw
  simp [← hT w, this, inner_smul_left, hv w hw]

/--
theorem `conj_eigenvalue_eq_self` / 定理 `conj_eigenvalue_eq_self`

English:
theorem conj_eigenvalue_eq_self
  given: (hT : T.IsSymmetric) {μ : 𝕜} (hμ : HasEigenvalue T μ)
  proof: by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  rw [mem_eigenspace_iff] at hv₁
  simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v

中文:
定理 conj_eigenvalue_eq_self
  条件: (hT : T.IsSymmetric) {μ : 𝕜} (hμ : HasEigenvalue T μ)
  证明: by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  rw [mem_eigenspace_iff] at hv₁
  simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v

Depends on / 依赖: exists_hasEigenvector, inner_smul_left, inner_smul_right, mem_eigenspace_iff
-/
theorem conj_eigenvalue_eq_self (hT : T.IsSymmetric) {μ : 𝕜} (hμ : HasEigenvalue T μ) :
    conj μ = μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  rw [mem_eigenspace_iff] at hv₁
  simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v

/--
theorem `orthogonalFamily_eigenspaces` / 定理 `orthogonalFamily_eigenspaces`

English:
theorem orthogonalFamily_eigenspaces
  given: (hT : T.IsSymmetric)
  proof: by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  by_cases hv' : v = 0
  · simp [hv']
  have H := hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hv, hv'⟩)
  rw [mem_eigenspace_iff] at hv hw
  refine Or.resolve_left ?_ hμν.symm
  simpa [inner_smul_left, inner_smul_right, hv, hw, H] using (hT v w).s

中文:
定理 orthogonalFamily_eigenspaces
  条件: (hT : T.IsSymmetric)
  证明: by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  by_cases hv' : v = 0
  · simp [hv']
  have H := hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hv, hv'⟩)
  rw [mem_eigenspace_iff] at hv hw
  refine Or.resolve_left ?_ hμν.symm
  simpa [inner_smul_left, inner_smul_right, hv, hw, H] using (hT v w).s

Depends on / 依赖: Or.resolve_left, conj_eigenvalue_eq_self, hT.conj_eigenvalue_eq_self, hasEigenvalue_of_hasEigenvector, inner_smul_left, inner_smul_right, mem_eigenspace_iff, resolve_left
-/
theorem orthogonalFamily_eigenspaces (hT : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ => eigenspace T μ) fun μ => (eigenspace T μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  by_cases hv' : v = 0
  · simp [hv']
  have H := hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hv, hv'⟩)
  rw [mem_eigenspace_iff] at hv hw
  refine Or.resolve_left ?_ hμν.symm
  simpa [inner_smul_left, inner_smul_right, hv, hw, H] using (hT v w).symm

/--
theorem `orthogonalFamily_eigenspaces'` / 定理 `orthogonalFamily_eigenspaces'`

English:
theorem orthogonalFamily_eigenspaces'
  given: (hT : T.IsSymmetric)
  proof: hT.orthogonalFamily_eigenspaces.comp Subtype.coe_injective

中文:
定理 orthogonalFamily_eigenspaces'
  条件: (hT : T.IsSymmetric)
  证明: hT.orthogonalFamily_eigenspaces.comp Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, hT.orthogonalFamily_eigenspaces.comp, orthogonalFamily_eigenspaces
-/
theorem orthogonalFamily_eigenspaces' (hT : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ : Eigenvalues T => eigenspace T μ) fun μ =>
      (eigenspace T μ).subtypeₗᵢ :=
  hT.orthogonalFamily_eigenspaces.comp Subtype.coe_injective

/--
theorem `orthogonalComplement_iSup_eigenspaces_invariant` / 定理 `orthogonalComplement_iSup_eigenspaces_invariant`

English:
theorem orthogonalComplement_iSup_eigenspaces_invariant
  statement: (hT : T.IsSymmetric)
  proof: by
  rw [← Submodule.iInf_orthogonal] at hv ⊢
  exact T.iInf_invariant hT.invariant_orthogonalComplement_eigenspace v hv

中文:
定理 orthogonalComplement_iSup_eigenspaces_invariant
  结论: (hT : T.IsSymmetric)
  证明: by
  rw [← Submodule.iInf_orthogonal] at hv ⊢
  exact T.iInf_invariant hT.invariant_orthogonalComplement_eigenspace v hv

Depends on / 依赖: Submodule, Submodule.iInf_orthogonal, T.iInf_invariant, hT.invariant_orthogonalComplement_eigenspace, iInf_invariant, iInf_orthogonal, invariant_orthogonalComplement_eigenspace
-/
theorem orthogonalComplement_iSup_eigenspaces_invariant (hT : T.IsSymmetric)
    ⦃v : E⦄ (hv : v in (⨆ μ, eigenspace T μ)ᗮ) : T v in (⨆ μ, eigenspace T μ)ᗮ := by
  rw [← Submodule.iInf_orthogonal] at hv ⊢
  exact T.iInf_invariant hT.invariant_orthogonalComplement_eigenspace v hv

/--
theorem `orthogonalComplement_iSup_eigenspaces` / 定理 `orthogonalComplement_iSup_eigenspaces`

English:
theorem orthogonalComplement_iSup_eigenspaces
  given: (hT : T.IsSymmetric) (μ : 𝕜)
  proof: by
  set p : Submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ
  refine eigenspace_restrict_eq_bot hT.orthogonalComplement_iSup_eigenspaces_invariant ?_
  have H₂ : eigenspace T μ ⟂ p := (Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ _)
  exact H₂.disjoint

中文:
定理 orthogonalComplement_iSup_eigenspaces
  条件: (hT : T.IsSymmetric) (μ : 𝕜)
  证明: by
  set p : Submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ
  refine eigenspace_restrict_eq_bot hT.orthogonalComplement_iSup_eigenspaces_invariant ?_
  have H₂ : eigenspace T μ ⟂ p := (Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ _)
  exact H₂.disjoint

Depends on / 依赖: Submodule, Submodule.isOrtho_orthogonal_right, disjoint, eigenspace, eigenspace_restrict_eq_bot, hT.orthogonalComplement_iSup_eigenspaces_invariant, isOrtho_orthogonal_right, le_iSup, mono_left, orthogonalComplement_iSup_eigenspaces_invariant
-/
theorem orthogonalComplement_iSup_eigenspaces (hT : T.IsSymmetric) (μ : 𝕜) :
    eigenspace (T.restrict hT.orthogonalComplement_iSup_eigenspaces_invariant) μ = ⊥ := by
  set p : Submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ
  refine eigenspace_restrict_eq_bot hT.orthogonalComplement_iSup_eigenspaces_invariant ?_
  have H₂ : eigenspace T μ ⟂ p := (Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ _)
  exact H₂.disjoint

/-! ### Finite-dimensional theory -/

variable [FiniteDimensional 𝕜 E]

/--
theorem `orthogonalComplement_iSup_eigenspaces_eq_bot` / 定理 `orthogonalComplement_iSup_eigenspaces_eq_bot`

English:
theorem orthogonalComplement_iSup_eigenspaces_eq_bot
  given: (hT : T.IsSymmetric)
  proof: by
  have hT' : IsSymmetric _ :=
    hT.restrict_invariant hT.orthogonalComplement_iSup_eigenspaces_invariant
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  have :=
    hT'.subsingleton_of_no_eigenvalue_finiteDimensional hT.orthogonalComplement_iSup_eigenspaces


中文:
定理 orthogonalComplement_iSup_eigenspaces_eq_bot
  条件: (hT : T.IsSymmetric)
  证明: by
  have hT' : IsSymmetric _ :=
    hT.restrict_invariant hT.orthogonalComplement_iSup_eigenspaces_invariant
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  have :=
    hT'.subsingleton_of_no_eigenvalue_finiteDimensional hT.orthogonalComplement_iSup_eigenspaces


Depends on / 依赖: IsSymmetric, hT.orthogonalComplement_iSup_eigenspaces_invariant, hT.restrict_invariant, orthogonalComplement_iSup_eigenspaces_invariant, restrict_invariant
-/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot (hT : T.IsSymmetric) :
    (⨆ μ, eigenspace T μ)ᗮ = ⊥ := by
  have hT' : IsSymmetric _ :=
    hT.restrict_invariant hT.orthogonalComplement_iSup_eigenspaces_invariant
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  have :=
    hT'.subsingleton_of_no_eigenvalue_finiteDimensional hT.orthogonalComplement_iSup_eigenspaces
  exact Submodule.eq_bot_of_subsingleton

/--
theorem `orthogonalComplement_iSup_eigenspaces_eq_bot'` / 定理 `orthogonalComplement_iSup_eigenspaces_eq_bot'`

English:
theorem orthogonalComplement_iSup_eigenspaces_eq_bot'
  given: (hT : T.IsSymmetric)
  proof: show (⨆ μ : { μ // eigenspace T μ != ⊥ }, eigenspace T μ)ᗮ = ⊥ by
    rw [iSup_ne_bot_subtype]; rw [hT.orthogonalComplement_iSup_eigenspaces_eq_bot]

中文:
定理 orthogonalComplement_iSup_eigenspaces_eq_bot'
  条件: (hT : T.IsSymmetric)
  证明: show (⨆ μ : { μ // eigenspace T μ != ⊥ }, eigenspace T μ)ᗮ = ⊥ by
    rw [iSup_ne_bot_subtype]; rw [hT.orthogonalComplement_iSup_eigenspaces_eq_bot]

Depends on / 依赖: eigenspace, hT.orthogonalComplement_iSup_eigenspaces_eq_bot, iSup_ne_bot_subtype, orthogonalComplement_iSup_eigenspaces_eq_bot
-/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot' (hT : T.IsSymmetric) :
    (⨆ μ : Eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
  show (⨆ μ : { μ // eigenspace T μ != ⊥ }, eigenspace T μ)ᗮ = ⊥ by
    rw [iSup_ne_bot_subtype]; rw [hT.orthogonalComplement_iSup_eigenspaces_eq_bot]

/--
Instance `directSumDecomposition` / 实例 `directSumDecomposition`

English:
instance directSumDecomposition
  signature: [hT : Fact T.IsSymmetric]
  body: haveI h : forall μ : Eigenvalues T, CompleteSpace (eigenspace T μ) := fun μ => by infer_instance
  hT.out.orthogonalFamily_eigenspaces'.decomposition
    (Submodule.orthogonal_eq_bot_iff.mp hT.out.orthogonalComplement_iSup_eigenspaces_eq_bot')

中文:
实例 directSumDecomposition
  签名: [hT : Fact T.IsSymmetric]
  定义体: haveI h : forall μ : Eigenvalues T, CompleteSpace (eigenspace T μ) := fun μ => by infer_instance
  hT.out.orthogonalFamily_eigenspaces'.decomposition
    (Submodule.orthogonal_eq_bot_iff.mp hT.out.orthogonalComplement_iSup_eigenspaces_eq_bot')

Depends on / 依赖: CompleteSpace, Eigenvalues, Submodule, Submodule.orthogonal_eq_bot_iff.mp, decomposition, eigenspace, hT.out.orthogonalComplement_iSup_eigenspaces_eq_bot, hT.out.orthogonalFamily_eigenspaces, infer_instance, orthogonalComplement_iSup_eigenspaces_eq_bot, orthogonalFamily_eigenspaces, orthogonal_eq_bot_iff
-/
noncomputable instance directSumDecomposition [hT : Fact T.IsSymmetric] :
    DirectSum.Decomposition fun μ : Eigenvalues T => eigenspace T μ :=
  haveI h : forall μ : Eigenvalues T, CompleteSpace (eigenspace T μ) := fun μ => by infer_instance
  hT.out.orthogonalFamily_eigenspaces'.decomposition
    (Submodule.orthogonal_eq_bot_iff.mp hT.out.orthogonalComplement_iSup_eigenspaces_eq_bot')

/--
theorem `directSum_decompose_apply` / 定理 `directSum_decompose_apply`

English:
theorem directSum_decompose_apply
  given: [_hT : Fact T.IsSymmetric] (x : E) (μ : Eigenvalues T)
  proof: rfl

中文:
定理 directSum_decompose_apply
  条件: [_hT : Fact T.IsSymmetric] (x : E) (μ : Eigenvalues T)
  证明: rfl
-/
theorem directSum_decompose_apply [_hT : Fact T.IsSymmetric] (x : E) (μ : Eigenvalues T) :
    DirectSum.decompose (fun μ : Eigenvalues T => eigenspace T μ) x μ =
      (eigenspace T μ).orthogonalProjectionOnto x :=
  rfl

/--
theorem `direct_sum_isInternal` / 定理 `direct_sum_isInternal`

English:
theorem direct_sum_isInternal
  given: (hT : T.IsSymmetric)
  proof: hT.orthogonalFamily_eigenspaces'.isInternal_iff.mpr
    hT.orthogonalComplement_iSup_eigenspaces_eq_bot'

中文:
定理 direct_sum_is整数ernal
  条件: (hT : T.IsSymmetric)
  证明: hT.orthogonalFamily_eigenspaces'.isInternal_iff.mpr
    hT.orthogonalComplement_iSup_eigenspaces_eq_bot'

Depends on / 依赖: hT.orthogonalComplement_iSup_eigenspaces_eq_bot, hT.orthogonalFamily_eigenspaces, isInternal_iff, isInternal_iff.mpr, orthogonalComplement_iSup_eigenspaces_eq_bot, orthogonalFamily_eigenspaces
-/
theorem direct_sum_isInternal (hT : T.IsSymmetric) :
    DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ :=
  hT.orthogonalFamily_eigenspaces'.isInternal_iff.mpr
    hT.orthogonalComplement_iSup_eigenspaces_eq_bot'

section Version1

/--
Definition of `diagonalization` / `diagonalization` 的定义

English:
definition diagonalization
  signature: (hT : T.IsSymmetric)
  body: hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily hT.orthogonalFamily_eigenspaces'

@[simp]

中文:
定义 diagonalization
  签名: (hT : T.IsSymmetric)
  定义体: hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily hT.orthogonalFamily_eigenspaces'

@[simp]

Depends on / 依赖: direct_sum_isInternal, hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily, hT.orthogonalFamily_eigenspaces, isometryL2OfOrthogonalFamily, orthogonalFamily_eigenspaces
-/
noncomputable def diagonalization (hT : T.IsSymmetric) : E ≃ₗᵢ[𝕜] PiLp 2 fun μ :
    Eigenvalues T => eigenspace T μ :=
  hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily hT.orthogonalFamily_eigenspaces'

@[simp]
/--
theorem `diagonalization_symm_apply` / 定理 `diagonalization_symm_apply`

English:
theorem diagonalization_symm_apply
  statement: (hT : T.IsSymmetric)
  proof: hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily_symm_apply
    hT.orthogonalFamily_eigenspaces' w

中文:
定理 diagonalization_symm_apply
  结论: (hT : T.IsSymmetric)
  证明: hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily_symm_apply
    hT.orthogonalFamily_eigenspaces' w

Depends on / 依赖: direct_sum_isInternal, hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily_symm_apply, hT.orthogonalFamily_eigenspaces, isometryL2OfOrthogonalFamily_symm_apply, orthogonalFamily_eigenspaces
-/
theorem diagonalization_symm_apply (hT : T.IsSymmetric)
    (w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ) :
    hT.diagonalization.symm w = ∑ μ, w μ :=
  hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily_symm_apply
    hT.orthogonalFamily_eigenspaces' w

/--
theorem `diagonalization_apply_self_apply` / 定理 `diagonalization_apply_self_apply`

English:
theorem diagonalization_apply_self_apply
  given: (hT : T.IsSymmetric) (v : E) (μ : Eigenvalues T)
  proof: by
  suffices
    forall w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ,
      T (hT.diagonalization.symm w) = hT.diagonalization.symm (toLp 2 fun μ => (μ : 𝕜) • w μ) by
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using
      congr_arg (fun w => hT

中文:
定理 diagonalization_apply_self_apply
  条件: (hT : T.IsSymmetric) (v : E) (μ : Eigenvalues T)
  证明: by
  suffices
    forall w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ,
      T (hT.diagonalization.symm w) = hT.diagonalization.symm (toLp 2 fun μ => (μ : 𝕜) • w μ) by
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using
      congr_arg (fun w => hT

Depends on / 依赖: Eigenvalues, LinearIsometryEquiv, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply, SetLike, SetLike.val_smul, apply_symm_apply, congr_arg, diagonalization, diagonalization_symm_apply, eigenspace, hT.diagonalization, hT.diagonalization.symm, map_sum, mem_eigenspace_iff, symm_apply_apply, val_smul
-/
theorem diagonalization_apply_self_apply (hT : T.IsSymmetric) (v : E) (μ : Eigenvalues T) :
    hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ := by
  suffices
    forall w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ,
      T (hT.diagonalization.symm w) = hT.diagonalization.symm (toLp 2 fun μ => (μ : 𝕜) • w μ) by
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using
      congr_arg (fun w => hT.diagonalization w μ) (this (hT.diagonalization v))
  intro w
  have hwT : forall μ, T (w μ) = (μ : 𝕜) • w μ := fun μ => mem_eigenspace_iff.1 (w μ).2
  simp only [diagonalization_symm_apply, map_sum, hwT, SetLike.val_smul]

end Version1

section Version2

variable {n : Nat}

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  body: @RCLike.re 𝕜 _ (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces').val

中文:
定义 noncomputable
  签名: def unsortedEigenvalues (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  定义体: @RCLike.re 𝕜 _ (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces').val
-/
private noncomputable def unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : Real :=
@RCLike.re 𝕜 _ (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces').val

/--
theorem `hasEigenvalue_unsortedEigenvalues` / 定理 `hasEigenvalue_unsortedEigenvalues`

English:
theorem hasEigenvalue_unsortedEigenvalues
  statement: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: by
  unfold unsortedEigenvalues
  let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces'
  rwa [Eigenvalues.val_mk, RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hx)]

中文:
定理 hasEigenvalue_unsortedEigenvalues
  结论: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: by
  unfold unsortedEigenvalues
  let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces'
  rwa [Eigenvalues.val_mk, RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hx)]
-/
private theorem hasEigenvalue_unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : HasEigenvalue T (hT.unsortedEigenvalues hn i) := by
  unfold unsortedEigenvalues
  let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces'
  rwa [Eigenvalues.val_mk, RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hx)]

/--
theorem `exists_unsortedEigenvalues_eq` / 定理 `exists_unsortedEigenvalues_eq`

English:
theorem exists_unsortedEigenvalues_eq
  statement: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: by
  let (eq := hx) x : Eigenvalues T := ⟨μ, hμ⟩
  obtain ⟨i, hi⟩ := hT.direct_sum_isInternal.exists_subordinateOrthonormalBasisIndex_eq hn
    hT.orthogonalFamily_eigenspaces' (hasEigenvalue_iff.mp x.prop)
  use i
  rw [unsortedEigenvalues]; rw [hi]; rw [hx]; rw [Eigenvalues.val_mk]; rw [← RCLike.c

中文:
定理 存在_unsortedEigenvalues_eq
  结论: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: by
  let (eq := hx) x : Eigenvalues T := ⟨μ, hμ⟩
  obtain ⟨i, hi⟩ := hT.direct_sum_isInternal.exists_subordinateOrthonormalBasisIndex_eq hn
    hT.orthogonalFamily_eigenspaces' (hasEigenvalue_iff.mp x.prop)
  use i
  rw [unsortedEigenvalues]; rw [hi]; rw [hx]; rw [Eigenvalues.val_mk]; rw [← RCLike.c
-/
private theorem exists_unsortedEigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {μ : 𝕜} (hμ : HasEigenvalue T μ) : exists i : Fin n, hT.unsortedEigenvalues hn i = μ := by
  let (eq := hx) x : Eigenvalues T := ⟨μ, hμ⟩
  obtain ⟨i, hi⟩ := hT.direct_sum_isInternal.exists_subordinateOrthonormalBasisIndex_eq hn
    hT.orthogonalFamily_eigenspaces' (hasEigenvalue_iff.mp x.prop)
  use i
  rw [unsortedEigenvalues]; rw [hi]; rw [hx]; rw [Eigenvalues.val_mk]; rw [← RCLike.conj_eq_iff_re]; rw [hT.conj_eigenvalue_eq_self hμ]

/--
theorem `card_filter_unsortedEigenvalues_eq` / 定理 `card_filter_unsortedEigenvalues_eq`

English:
theorem card_filter_unsortedEigenvalues_eq
  statement: (hT : T.IsSymmetric)
  proof: by
  by_cases hμ : HasEigenvalue T μ
  · convert!
      hT.direct_sum_isInternal.card_filter_subordinateOrthonormalBasisIndex_eq hn
        hT.orthogonalFamily_eigenspaces' ⟨μ, hμ⟩ with i
    unfold unsortedEigenvalues
    let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i

中文:
定理 card_filter_unsortedEigenvalues_eq
  结论: (hT : T.IsSymmetric)
  证明: by
  by_cases hμ : HasEigenvalue T μ
  · convert!
      hT.direct_sum_isInternal.card_filter_subordinateOrthonormalBasisIndex_eq hn
        hT.orthogonalFamily_eigenspaces' ⟨μ, hμ⟩ with i
    unfold unsortedEigenvalues
    let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
-/
private theorem card_filter_unsortedEigenvalues_eq (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (μ : 𝕜) :
    Finset.card {i | hT.unsortedEigenvalues hn i = μ} = Module.finrank 𝕜 (eigenspace T μ) := by
  by_cases hμ : HasEigenvalue T μ
  · convert!
      hT.direct_sum_isInternal.card_filter_subordinateOrthonormalBasisIndex_eq hn
        hT.orthogonalFamily_eigenspaces' ⟨μ, hμ⟩ with i
    unfold unsortedEigenvalues
    let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
      hT.orthogonalFamily_eigenspaces'
    rw [Eigenvalues.val_mk]; rw [RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hx)]
    exact Subtype.mk_eq_mk.symm
  · rw [Module.End.hasEigenvalue_iff.not_left.mp hμ, finrank_bot, Finset.card_filter_eq_zero_iff]
    intro i _ rfl
    exact hμ (hT.hasEigenvalue_unsortedEigenvalues hn i)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def unsortedEigenvectorBasis (hT : T.IsSymmetric)
  body: hT.direct_sum_isInternal.subordinateOrthonormalBasis hn hT.orthogonalFamily_eigenspaces'

中文:
定义 noncomputable
  签名: def unsortedEigenvectorBasis (hT : T.IsSymmetric)
  定义体: hT.direct_sum_isInternal.subordinateOrthonormalBasis hn hT.orthogonalFamily_eigenspaces'
-/
private noncomputable def unsortedEigenvectorBasis (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) : OrthonormalBasis (Fin n) 𝕜 E :=
  hT.direct_sum_isInternal.subordinateOrthonormalBasis hn hT.orthogonalFamily_eigenspaces'

/--
theorem `hasEigenvector_eigenvectorBasis_helper` / 定理 `hasEigenvector_eigenvectorBasis_helper`

English:
theorem hasEigenvector_eigenvectorBasis_helper
  statement: (hT : T.IsSymmetric)
  proof: by
  let v : E := hT.unsortedEigenvectorBasis hn i
  let μ : 𝕜 :=
    (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
      hT.orthogonalFamily_eigenspaces').val
  simp_rw [unsortedEigenvalues]
  change HasEigenvector T (RCLike.re μ) v
  have key : HasEigenvector T μ v := by
    have

中文:
定理 hasEigenvector_eigenvectorBasis_helper
  结论: (hT : T.IsSymmetric)
  证明: by
  let v : E := hT.unsortedEigenvectorBasis hn i
  let μ : 𝕜 :=
    (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
      hT.orthogonalFamily_eigenspaces').val
  simp_rw [unsortedEigenvalues]
  change HasEigenvector T (RCLike.re μ) v
  have key : HasEigenvector T μ v := by
    have
-/
private theorem hasEigenvector_eigenvectorBasis_helper (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    HasEigenvector T (hT.unsortedEigenvalues hn i) (hT.unsortedEigenvectorBasis hn i) := by
  let v : E := hT.unsortedEigenvectorBasis hn i
  let μ : 𝕜 :=
    (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
      hT.orthogonalFamily_eigenspaces').val
  simp_rw [unsortedEigenvalues]
  change HasEigenvector T (RCLike.re μ) v
  have key : HasEigenvector T μ v := by
    have H₁ : v in eigenspace T μ := by
      simp_rw [v, unsortedEigenvectorBasis]
      exact
        hT.direct_sum_isInternal.subordinateOrthonormalBasis_subordinate hn i
          hT.orthogonalFamily_eigenspaces'
    have H₂ : v != 0 := by simpa using (hT.unsortedEigenvectorBasis hn).toBasis.ne_zero i
    exact ⟨H₁, H₂⟩
  have re_μ : ↑(RCLike.re μ) = μ := by
    rw [← RCLike.conj_eq_iff_re]
    exact hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector key)
  simpa [re_μ] using key

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The eigenvalues for a self-adjoint operator `T` on a
finite-dimensional inner product space `E`, sorted in decreasing order -/
noncomputable irreducible_def eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    Fin n -> Real :=
  (hT.unsortedEigenvalues hn) ∘ Tuple.sort (hT.unsortedEigenvalues hn) ∘ @Fin.revPerm n

/--
theorem `exists_eigenvalues_eq` / 定理 `exists_eigenvalues_eq`

English:
theorem exists_eigenvalues_eq
  statement: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {μ : 𝕜}
  proof: by
  obtain ⟨i, hi⟩ := hT.exists_unsortedEigenvalues_eq hn hμ
  use ((Tuple.sort (hT.unsortedEigenvalues hn)).symm i).revPerm
  simp [eigenvalues_def, hi]

中文:
定理 存在_eigenvalues_eq
  结论: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n) {μ : 𝕜}
  证明: by
  obtain ⟨i, hi⟩ := hT.exists_unsortedEigenvalues_eq hn hμ
  use ((Tuple.sort (hT.unsortedEigenvalues hn)).symm i).revPerm
  simp [eigenvalues_def, hi]

Depends on / 依赖: Tuple.sort, eigenvalues_def, exists_unsortedEigenvalues_eq, hT.exists_unsortedEigenvalues_eq, hT.unsortedEigenvalues, revPerm, unsortedEigenvalues
-/
theorem exists_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {μ : 𝕜}
    (hμ : HasEigenvalue T μ) : exists i : Fin n, hT.eigenvalues hn i = μ := by
  obtain ⟨i, hi⟩ := hT.exists_unsortedEigenvalues_eq hn hμ
  use ((Tuple.sort (hT.unsortedEigenvalues hn)).symm i).revPerm
  simp [eigenvalues_def, hi]

/--
theorem `card_filter_eigenvalues_eq` / 定理 `card_filter_eigenvalues_eq`

English:
theorem card_filter_eigenvalues_eq
  given: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (μ : 𝕜)
  proof: by
  rw [← hT.card_filter_unsortedEigenvalues_eq hn]; rw [eigenvalues_def]
  apply Finset.card_equiv (Fin.revPerm.trans (Tuple.sort (hT.unsortedEigenvalues hn)))
  simp

中文:
定理 card_filter_eigenvalues_eq
  条件: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n) (μ : 𝕜)
  证明: by
  rw [← hT.card_filter_unsortedEigenvalues_eq hn]; rw [eigenvalues_def]
  apply Finset.card_equiv (Fin.revPerm.trans (Tuple.sort (hT.unsortedEigenvalues hn)))
  simp

Depends on / 依赖: Fin.revPerm.trans, Finset, Finset.card_equiv, Tuple.sort, card_equiv, card_filter_unsortedEigenvalues_eq, eigenvalues_def, hT.card_filter_unsortedEigenvalues_eq, hT.unsortedEigenvalues, revPerm, unsortedEigenvalues
-/
theorem card_filter_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (μ : 𝕜) :
    Finset.card {i | hT.eigenvalues hn i = μ} = Module.finrank 𝕜 (eigenspace T μ) := by
  rw [← hT.card_filter_unsortedEigenvalues_eq hn]; rw [eigenvalues_def]
  apply Finset.card_equiv (Fin.revPerm.trans (Tuple.sort (hT.unsortedEigenvalues hn)))
  simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`. Eigenvectors are sorted in decreasing
order of their eigenvalues. -/
noncomputable irreducible_def eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  (hT.direct_sum_isInternal.subordinateOrthonormalBasis
    hn hT.orthogonalFamily_eigenspaces').reindex
      (Tuple.sort (hT.unsortedEigenvalues hn) * @Fin.revPerm n).symm

/--
theorem `hasEigenvector_eigenvectorBasis` / 定理 `hasEigenvector_eigenvectorBasis`

English:
theorem hasEigenvector_eigenvectorBasis
  statement: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: by
  rw [eigenvalues_def]; rw [eigenvectorBasis_def]; rw [OrthonormalBasis.reindex_apply]
  apply hasEigenvector_eigenvectorBasis_helper

中文:
定理 hasEigenvector_eigenvectorBasis
  结论: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: by
  rw [eigenvalues_def]; rw [eigenvectorBasis_def]; rw [OrthonormalBasis.reindex_apply]
  apply hasEigenvector_eigenvectorBasis_helper

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.reindex_apply, eigenvalues_def, eigenvectorBasis_def, hasEigenvector_eigenvectorBasis_helper, reindex_apply
-/
theorem hasEigenvector_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : HasEigenvector T (hT.eigenvalues hn i) (hT.eigenvectorBasis hn i) := by
  rw [eigenvalues_def]; rw [eigenvectorBasis_def]; rw [OrthonormalBasis.reindex_apply]
  apply hasEigenvector_eigenvectorBasis_helper

/--
theorem `eigenvalues_antitone` / 定理 `eigenvalues_antitone`

English:
theorem eigenvalues_antitone
  given: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: by
  rw [eigenvalues_def]; rw [← Function.comp_assoc]
  refine Monotone.comp_antitone ?_ ?_
  · apply Tuple.monotone_sort
  intro _ _ h
  exact Fin.rev_le_rev.mpr h

中文:
定理 eigenvalues_antitone
  条件: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: by
  rw [eigenvalues_def]; rw [← Function.comp_assoc]
  refine Monotone.comp_antitone ?_ ?_
  · apply Tuple.monotone_sort
  intro _ _ h
  exact Fin.rev_le_rev.mpr h

Depends on / 依赖: Fin.rev_le_rev.mpr, Function, Function.comp_assoc, Monotone, Monotone.comp_antitone, Tuple.monotone_sort, comp_antitone, comp_assoc, eigenvalues_def, monotone_sort, rev_le_rev
-/
theorem eigenvalues_antitone (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    Antitone (hT.eigenvalues hn) := by
  rw [eigenvalues_def]; rw [← Function.comp_assoc]
  refine Monotone.comp_antitone ?_ ?_
  · apply Tuple.monotone_sort
  intro _ _ h
  exact Fin.rev_le_rev.mpr h

/--
theorem `hasEigenvalue_eigenvalues` / 定理 `hasEigenvalue_eigenvalues`

English:
theorem hasEigenvalue_eigenvalues
  given: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  proof: Module.End.hasEigenvalue_of_hasEigenvector (hT.hasEigenvector_eigenvectorBasis hn i)

@[simp]

中文:
定理 hasEigenvalue_eigenvalues
  条件: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n) (i : 有限集 n)
  证明: Module.End.hasEigenvalue_of_hasEigenvector (hT.hasEigenvector_eigenvectorBasis hn i)

@[simp]

Depends on / 依赖: Module, Module.End.hasEigenvalue_of_hasEigenvector, hT.hasEigenvector_eigenvectorBasis, hasEigenvalue_of_hasEigenvector, hasEigenvector_eigenvectorBasis
-/
theorem hasEigenvalue_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    HasEigenvalue T (hT.eigenvalues hn i) :=
  Module.End.hasEigenvalue_of_hasEigenvector (hT.hasEigenvector_eigenvectorBasis hn i)

@[simp]
/--
theorem `apply_eigenvectorBasis` / 定理 `apply_eigenvectorBasis`

English:
theorem apply_eigenvectorBasis
  given: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  proof: mem_eigenspace_iff.mp (hT.hasEigenvector_eigenvectorBasis hn i).1

中文:
定理 apply_eigenvectorBasis
  条件: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n) (i : 有限集 n)
  证明: mem_eigenspace_iff.mp (hT.hasEigenvector_eigenvectorBasis hn i).1

Depends on / 依赖: hT.hasEigenvector_eigenvectorBasis, hasEigenvector_eigenvectorBasis, mem_eigenspace_iff, mem_eigenspace_iff.mp
-/
theorem apply_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    T (hT.eigenvectorBasis hn i) = (hT.eigenvalues hn i : 𝕜) • hT.eigenvectorBasis hn i :=
  mem_eigenspace_iff.mp (hT.hasEigenvector_eigenvectorBasis hn i).1

/--
theorem `eigenvectorBasis_apply_self_apply` / 定理 `eigenvectorBasis_apply_self_apply`

English:
theorem eigenvectorBasis_apply_self_apply
  statement: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: by
  suffices
    forall w : EuclideanSpace 𝕜 (Fin n),
      T ((hT.eigenvectorBasis hn).repr.symm w) =
        (hT.eigenvectorBasis hn).repr.symm (toLp 2 fun i => hT.eigenvalues hn i * w i) by
    simpa [OrthonormalBasis.sum_repr_symm] using
      congr_arg (fun v => (hT.eigenvectorBasis hn).repr v

中文:
定理 eigenvectorBasis_apply_self_apply
  结论: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: by
  suffices
    forall w : EuclideanSpace 𝕜 (Fin n),
      T ((hT.eigenvectorBasis hn).repr.symm w) =
        (hT.eigenvectorBasis hn).repr.symm (toLp 2 fun i => hT.eigenvalues hn i * w i) by
    simpa [OrthonormalBasis.sum_repr_symm] using
      congr_arg (fun v => (hT.eigenvectorBasis hn).repr v

Depends on / 依赖: EuclideanSpace, Fintype, Fintype.sum_congr, OrthonormalBasis, OrthonormalBasis.sum_repr_symm, apply_eigenvectorBasis, congr_arg, eigenvalues, eigenvectorBasis, hT.eigenvalues, hT.eigenvectorBasis, map_smul, map_sum, mul_comm, ofLp_toLp, repr.symm, simp_rw, smul_smul, sum_congr, sum_repr_symm
-/
theorem eigenvectorBasis_apply_self_apply (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (v : E) (i : Fin n) :
    (hT.eigenvectorBasis hn).repr (T v) i =
      hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr v i := by
  suffices
    forall w : EuclideanSpace 𝕜 (Fin n),
      T ((hT.eigenvectorBasis hn).repr.symm w) =
        (hT.eigenvectorBasis hn).repr.symm (toLp 2 fun i => hT.eigenvalues hn i * w i) by
    simpa [OrthonormalBasis.sum_repr_symm] using
      congr_arg (fun v => (hT.eigenvectorBasis hn).repr v i)
        (this ((hT.eigenvectorBasis hn).repr v))
  intro w
  simp_rw [← OrthonormalBasis.sum_repr_symm, map_sum, map_smul, apply_eigenvectorBasis]
  apply Fintype.sum_congr
  intro a
  rw [smul_smul]; rw [mul_comm]; rw [ofLp_toLp]

/--
theorem `toMatrix_eigenvectorBasis` / 定理 `toMatrix_eigenvectorBasis`

English:
theorem toMatrix_eigenvectorBasis
  given: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: (hT.eigenvectorBasis hn).toBasis
    T.toMatrix b b = Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hn) := by
  ext i j
  simp [toMatrix_apply, Matrix.diagonal_apply, RCLike.real_smul_eq_coe_mul]
  grind

中文:
定理 toMatrix_eigenvectorBasis
  条件: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: (hT.eigenvectorBasis hn).toBasis
    T.toMatrix b b = Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hn) := by
  ext i j
  simp [toMatrix_apply, Matrix.diagonal_apply, RCLike.real_smul_eq_coe_mul]
  grind

Depends on / 依赖: eigenvectorBasis, hT.eigenvectorBasis, toBasis
-/
theorem toMatrix_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    letI b := (hT.eigenvectorBasis hn).toBasis
    T.toMatrix b b = Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hn) := by
  ext i j
  simp [toMatrix_apply, Matrix.diagonal_apply, RCLike.real_smul_eq_coe_mul]
  grind

open Polynomial in
/--
theorem `charpoly_eq` / 定理 `charpoly_eq`

English:
theorem charpoly_eq
  given: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: by
  simp [← T.charpoly_toMatrix (hT.eigenvectorBasis hn).toBasis, toMatrix_eigenvectorBasis,
    Matrix.charpoly_diagonal]

中文:
定理 charpoly_eq
  条件: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: by
  simp [← T.charpoly_toMatrix (hT.eigenvectorBasis hn).toBasis, toMatrix_eigenvectorBasis,
    Matrix.charpoly_diagonal]

Depends on / 依赖: Matrix, Matrix.charpoly_diagonal, T.charpoly_toMatrix, charpoly_diagonal, charpoly_toMatrix, eigenvectorBasis, hT.eigenvectorBasis, toBasis, toMatrix_eigenvectorBasis
-/
theorem charpoly_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.charpoly = ∏ i, (X - C (hT.eigenvalues hn i : 𝕜)) := by
  simp [← T.charpoly_toMatrix (hT.eigenvectorBasis hn).toBasis, toMatrix_eigenvectorBasis,
    Matrix.charpoly_diagonal]

/--
theorem `roots_charpoly_eq_eigenvalues` / 定理 `roots_charpoly_eq_eigenvalues`

English:
theorem roots_charpoly_eq_eigenvalues
  given: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: by
  rw [← charpoly_toMatrix _ (hT.eigenvectorBasis hn).toBasis]; rw [toMatrix_eigenvectorBasis]; rw [Matrix.charpoly_diagonal]; rw [Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff]; rw [Polynomial.X_sub_C_ne_zero])]
  simp

中文:
定理 roots_charpoly_eq_eigenvalues
  条件: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: by
  rw [← charpoly_toMatrix _ (hT.eigenvectorBasis hn).toBasis]; rw [toMatrix_eigenvectorBasis]; rw [Matrix.charpoly_diagonal]; rw [Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff]; rw [Polynomial.X_sub_C_ne_zero])]
  simp

Depends on / 依赖: Finset, Finset.prod_ne_zero_iff, Matrix, Matrix.charpoly_diagonal, Polynomial, Polynomial.X_sub_C_ne_zero, Polynomial.roots_prod, X_sub_C_ne_zero, charpoly_diagonal, charpoly_toMatrix, eigenvectorBasis, hT.eigenvectorBasis, prod_ne_zero_iff, roots_prod, toBasis, toMatrix_eigenvectorBasis
-/
theorem roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hT.eigenvalues hn) Finset.univ.val := by
  rw [← charpoly_toMatrix _ (hT.eigenvectorBasis hn).toBasis]; rw [toMatrix_eigenvectorBasis]; rw [Matrix.charpoly_diagonal]; rw [Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff]; rw [Polynomial.X_sub_C_ne_zero])]
  simp

/--
theorem `sort_roots_charpoly_eq_eigenvalues` / 定理 `sort_roots_charpoly_eq_eigenvalues`

English:
theorem sort_roots_charpoly_eq_eigenvalues
  given: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: by
  simp_rw [hT.roots_charpoly_eq_eigenvalues, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  have := hn.symm
  convert! List.mergeSort_of_pairwise ?_
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  convert! (hT.eigenva

中文:
定理 sort_roots_charpoly_eq_eigenvalues
  条件: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: by
  simp_rw [hT.roots_charpoly_eq_eigenvalues, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  have := hn.symm
  convert! List.mergeSort_of_pairwise ?_
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  convert! (hT.eigenva

Depends on / 依赖: Fin.univ_val_map, Function, Function.comp_def, List.map_ofFn, List.mergeSort_of_pairwise, List.sortedGE_iff_pairwise, Multiset, Multiset.coe_sort, Multiset.map_coe, RCLike, RCLike.ofReal_re, coe_sort, comp_def, convert, decide_eq_true_eq, eigenvalues_antitone, hT.eigenvalues_antitone, hT.roots_charpoly_eq_eigenvalues, hn.symm, map_coe
-/
theorem sort_roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    (T.charpoly.roots.map RCLike.re).sort (· >= ·) = List.ofFn (hT.eigenvalues hn) := by
  simp_rw [hT.roots_charpoly_eq_eigenvalues, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  have := hn.symm
  convert! List.mergeSort_of_pairwise ?_
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  convert! (hT.eigenvalues_antitone hn).sortedGE_ofFn

/--
theorem `eigenvalues_eq_eigenvalues_iff` / 定理 `eigenvalues_eq_eigenvalues_iff`

English:
theorem eigenvalues_eq_eigenvalues_iff
  statement: {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  proof: by rw [hT.charpoly_eq hn, hT'.charpoly_eq hn', h]
  mpr h := by
    rw [← List.ofFn_inj]; rw [← sort_roots_charpoly_eq_eigenvalues]; rw [← sort_roots_charpoly_eq_eigenvalues]; rw [h]

中文:
定理 eigenvalues_eq_eigenvalues_iff
  结论: {E' : 类型} [赋范交换加群 E'] [内积空间 𝕜 E']
  证明: by rw [hT.charpoly_eq hn, hT'.charpoly_eq hn', h]
  mpr h := by
    rw [← List.ofFn_inj]; rw [← sort_roots_charpoly_eq_eigenvalues]; rw [← sort_roots_charpoly_eq_eigenvalues]; rw [h]

Depends on / 依赖: List.ofFn_inj, charpoly_eq, hT.charpoly_eq, ofFn_inj, sort_roots_charpoly_eq_eigenvalues
-/
theorem eigenvalues_eq_eigenvalues_iff {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    [FiniteDimensional 𝕜 E'] {T' : E' ->ₗ[𝕜] E'} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (hT' : T'.IsSymmetric) (hn' : Module.finrank 𝕜 E' = n) :
    hT.eigenvalues hn = hT'.eigenvalues hn' ↔ T.charpoly = T'.charpoly where
  mp h := by rw [hT.charpoly_eq hn, hT'.charpoly_eq hn', h]
  mpr h := by
    rw [← List.ofFn_inj]; rw [← sort_roots_charpoly_eq_eigenvalues]; rw [← sort_roots_charpoly_eq_eigenvalues]; rw [h]

/--
theorem `splits_charpoly` / 定理 `splits_charpoly`

English:
theorem splits_charpoly
  given: (hT : T.IsSymmetric)
  statement: T.charpoly.Splits
  proof: by
  refine Polynomial.splits_iff_card_roots.mpr ?_
  simp [hT.roots_charpoly_eq_eigenvalues rfl, LinearMap.charpoly_natDegree]

中文:
定理 splits_charpoly
  条件: (hT : T.IsSymmetric)
  结论: T.charpoly.Splits
  证明: by
  refine Polynomial.splits_iff_card_roots.mpr ?_
  simp [hT.roots_charpoly_eq_eigenvalues rfl, LinearMap.charpoly_natDegree]

Depends on / 依赖: LinearMap, LinearMap.charpoly_natDegree, Polynomial, Polynomial.splits_iff_card_roots.mpr, charpoly_natDegree, hT.roots_charpoly_eq_eigenvalues, roots_charpoly_eq_eigenvalues, splits_iff_card_roots
-/
theorem splits_charpoly (hT : T.IsSymmetric) : T.charpoly.Splits := by
  refine Polynomial.splits_iff_card_roots.mpr ?_
  simp [hT.roots_charpoly_eq_eigenvalues rfl, LinearMap.charpoly_natDegree]

/--
theorem `det_eq_prod_eigenvalues` / 定理 `det_eq_prod_eigenvalues`

English:
theorem det_eq_prod_eigenvalues
  given: (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  proof: by
  simp [det_eq_prod_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.prod_ofFn]

中文:
定理 det_eq_prod_eigenvalues
  条件: (hT : T.IsSymmetric) (hn : 模.finrank 𝕜 E = n)
  证明: by
  simp [det_eq_prod_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.prod_ofFn]

Depends on / 依赖: List.prod_ofFn, det_eq_prod_roots_charpoly_of_splits, hT.roots_charpoly_eq_eigenvalues, hT.splits_charpoly, prod_ofFn, roots_charpoly_eq_eigenvalues, splits_charpoly
-/
theorem det_eq_prod_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.det = ∏ i, (hT.eigenvalues hn i : 𝕜) := by
  simp [det_eq_prod_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.prod_ofFn]

end Version2

end IsSymmetric

end LinearMap

section Nonneg

-- Cannot be @[simp] because the LHS is not in simp normal form
/--
theorem `inner_product_apply_eigenvector` / 定理 `inner_product_apply_eigenvector`

English:
theorem inner_product_apply_eigenvector
  statement: {μ : 𝕜} {v : E} {T : E ->ₗ[𝕜] E}
  proof: by
  simp only [h, inner_smul_right, inner_self_eq_norm_sq_to_K]

中文:
定理 inner_product_apply_eigenvector
  结论: {μ : 𝕜} {v : E} {T : E ->ₗ[𝕜] E}
  证明: by
  simp only [h, inner_smul_right, inner_self_eq_norm_sq_to_K]

Depends on / 依赖: inner_self_eq_norm_sq_to_K, inner_smul_right
-/
theorem inner_product_apply_eigenvector {μ : 𝕜} {v : E} {T : E ->ₗ[𝕜] E}
    (h : T v = μ • v) : ⟪v, T v⟫ = μ * (‖v‖ : 𝕜) ^ 2 := by
  simp only [h, inner_smul_right, inner_self_eq_norm_sq_to_K]

/--
theorem `eigenvalue_nonneg_of_nonneg` / 定理 `eigenvalue_nonneg_of_nonneg`

English:
theorem eigenvalue_nonneg_of_nonneg
  statement: {μ : Real} {T : E ->ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
  proof: by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : Real) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector

中文:
定理 eigenvalue_nonneg_of_nonneg
  结论: {μ : 实数} {T : E ->ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
  证明: by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : Real) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector

Depends on / 依赖: RCLike, RCLike.re, congr_arg, exists_hasEigenvector, inner_product_apply_eigenvector, mem_genEigenspace_one, mod_cast, mul_nonneg_iff_of_pos_right, norm_ne_zero_iff, sq_pos_iff
-/
theorem eigenvalue_nonneg_of_nonneg {μ : Real} {T : E ->ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : forall x : E, 0 <= RCLike.re ⟪x, T x⟫) : 0 <= μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : Real) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector hv₁)
  exact (mul_nonneg_iff_of_pos_right hpos).mp (this ▸ hnn v)

/--
theorem `eigenvalue_pos_of_pos` / 定理 `eigenvalue_pos_of_pos`

English:
theorem eigenvalue_pos_of_pos
  statement: {μ : Real} {T : E ->ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
  proof: by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : Real) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector

中文:
定理 eigenvalue_pos_of_pos
  结论: {μ : 实数} {T : E ->ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
  证明: by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : Real) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector

Depends on / 依赖: RCLike, RCLike.re, congr_arg, exists_hasEigenvector, inner_product_apply_eigenvector, mem_genEigenspace_one, mod_cast, mul_pos_iff_of_pos_right, norm_ne_zero_iff, sq_pos_iff
-/
theorem eigenvalue_pos_of_pos {μ : Real} {T : E ->ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : forall x : E, 0 < RCLike.re ⟪x, T x⟫) : 0 < μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : Real) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector hv₁)
  exact (mul_pos_iff_of_pos_right hpos).mp (this ▸ hnn v)

end Nonneg

namespace ContinuousLinearMap

variable [CompleteSpace E] {T : E ->L[𝕜] E}

/--
theorem `eq_zero_of_forall_hasEigenvalue_eq_zero` / 定理 `eq_zero_of_forall_hasEigenvalue_eq_zero`

English:
theorem eq_zero_of_forall_hasEigenvalue_eq_zero
  given: (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
  proof: by
  rw [← nnnorm_eq_zero]; rw [← ENNReal.coe_eq_zero]; rw [← T.spectralRadius_eq_nnnorm hT'.isSelfAdjoint]; rw [spectralRadius]; rw [← not_iff_not]; rw [ENNReal.iSup_eq_zero]
  push Not
  apply exists_congr
  simp +contextual [hT.hasEigenvalue_iff_mem_spectrum]

中文:
定理 eq_zero_of_对任意_hasEigenvalue_eq_zero
  条件: (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
  证明: by
  rw [← nnnorm_eq_zero]; rw [← ENNReal.coe_eq_zero]; rw [← T.spectralRadius_eq_nnnorm hT'.isSelfAdjoint]; rw [spectralRadius]; rw [← not_iff_not]; rw [ENNReal.iSup_eq_zero]
  push Not
  apply exists_congr
  simp +contextual [hT.hasEigenvalue_iff_mem_spectrum]

Depends on / 依赖: ENNReal, ENNReal.coe_eq_zero, ENNReal.iSup_eq_zero, T.spectralRadius_eq_nnnorm, coe_eq_zero, contextual, exists_congr, hT.hasEigenvalue_iff_mem_spectrum, hasEigenvalue_iff_mem_spectrum, iSup_eq_zero, isSelfAdjoint, nnnorm_eq_zero, not_iff_not, spectralRadius, spectralRadius_eq_nnnorm
-/
theorem eq_zero_of_forall_hasEigenvalue_eq_zero (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (forall μ, HasEigenvalue (T : End 𝕜 E) μ -> μ = 0) ↔ T = 0 := by
  rw [← nnnorm_eq_zero]; rw [← ENNReal.coe_eq_zero]; rw [← T.spectralRadius_eq_nnnorm hT'.isSelfAdjoint]; rw [spectralRadius]; rw [← not_iff_not]; rw [ENNReal.iSup_eq_zero]
  push Not
  apply exists_congr
  simp +contextual [hT.hasEigenvalue_iff_mem_spectrum]

/--
theorem `orthogonalComplement_iSup_eigenspaces_eq_bot` / 定理 `orthogonalComplement_iSup_eigenspaces_eq_bot`

English:
theorem orthogonalComplement_iSup_eigenspaces_eq_bot
  proof: by
  let S : (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ ->L[𝕜] (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ :=
    T.restrict hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_compact : IsCompactOperator S :=
    hT.restrict' hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_symm : S.I

中文:
定理 orthogonalComplement_iSup_eigenspaces_eq_bot
  证明: by
  let S : (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ ->L[𝕜] (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ :=
    T.restrict hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_compact : IsCompactOperator S :=
    hT.restrict' hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_symm : S.I

Depends on / 依赖: IsCompactOperator, IsSymmetric, Module, Module.End, S.IsSymmetric, Submodule, T.restrict, eigenspace, hS_compact, hS_symm, hT.restrict, orthogonalComplement_iSup_eig, orthogonalComplement_iSup_eigenspaces_invariant, restrict, restrict_invariant
-/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot
    (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ := by
  let S : (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ ->L[𝕜] (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ :=
    T.restrict hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_compact : IsCompactOperator S :=
    hT.restrict' hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_symm : S.IsSymmetric :=
    hT'.restrict_invariant (hT'.orthogonalComplement_iSup_eigenspaces_invariant)
  have hS μ : eigenspace (S : Module.End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ) μ = ⊥ :=
    hT'.orthogonalComplement_iSup_eigenspaces _
  have h μ : HasEigenvalue (S : End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ) μ -> μ = 0 := by
    simp_all [hasEigenvalue_iff]
  rw [eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact hS_symm] at h
  rw [← Submodule.subsingleton_iff_eq_bot]
  by_contra! hV
  simpa [h] using hS 0

/--
theorem `finite_dimensional_eigenspace` / 定理 `finite_dimensional_eigenspace`

English:
theorem finite_dimensional_eigenspace
  given: (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ != 0)
  proof: by
  replace hT := hT.restrict'
    ((mem_invtSubmodule_iff_forall_mem_of_mem _).mp (eigenspace_mem_invtSubmodule T.toLinearMap μ))
  rw [restrict_eigenspace]; rw [LinearMap.coe_smul]; rw [IsCompactOperator.smul_iff₀ hμ] at hT
  rwa [← isCompactOperator_id_iff_finiteDimensional]

中文:
定理 finite_dimensional_eigenspace
  条件: (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ != 0)
  证明: by
  replace hT := hT.restrict'
    ((mem_invtSubmodule_iff_forall_mem_of_mem _).mp (eigenspace_mem_invtSubmodule T.toLinearMap μ))
  rw [restrict_eigenspace]; rw [LinearMap.coe_smul]; rw [IsCompactOperator.smul_iff₀ hμ] at hT
  rwa [← isCompactOperator_id_iff_finiteDimensional]

Depends on / 依赖: IsCompactOperator, IsCompactOperator.smul_iff, LinearMap, LinearMap.coe_smul, T.toLinearMap, coe_smul, eigenspace_mem_invtSubmodule, hT.restrict, isCompactOperator_id_iff_finiteDimensional, mem_invtSubmodule_iff_forall_mem_of_mem, replace, restrict, restrict_eigenspace, toLinearMap
-/
theorem finite_dimensional_eigenspace (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ != 0) :
    FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ) := by
  replace hT := hT.restrict'
    ((mem_invtSubmodule_iff_forall_mem_of_mem _).mp (eigenspace_mem_invtSubmodule T.toLinearMap μ))
  rw [restrict_eigenspace]; rw [LinearMap.coe_smul]; rw [IsCompactOperator.smul_iff₀ hμ] at hT
  rwa [← isCompactOperator_id_iff_finiteDimensional]

end ContinuousLinearMap
