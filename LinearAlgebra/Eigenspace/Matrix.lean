/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!

# Eigenvalues, Eigenvectors and Spectrum for Matrices

This file collects results about eigenvectors, eigenvalues and spectrum specific to matrices
over a nontrivial commutative ring, nontrivial commutative ring without zero divisors, or field.

## Tags
eigenspace, eigenvector, eigenvalue, spectrum, matrix

-/

public section

open Matrix Module End

variable {R n M : Type*} [DecidableEq n] [Fintype n]

section SpectrumDiagonal

section NontrivialCommRing

variable [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]

/--
lemma `hasEigenvector_toLin_diagonal` / 引理 `hasEigenvector_toLin_diagonal`

English:
lemma hasEigenvector_toLin_diagonal
  given: (d : n -> R) (i : n) (b : Basis n R M)
  proof: ⟨mem_eigenspace_iff.mpr by simp [diagonal], Basis.ne_zero b i⟩

中文:
引理 hasEigenvector_toLin_diagonal
  条件: (d : n -> R) (i : n) (b : 基 n R M)
  证明: ⟨mem_eigenspace_iff.mpr by simp [diagonal], Basis.ne_zero b i⟩

Depends on / 依赖: Basis.ne_zero, diagonal, mem_eigenspace_iff, mem_eigenspace_iff.mpr, ne_zero
-/
lemma hasEigenvector_toLin_diagonal (d : n -> R) (i : n) (b : Basis n R M) :
    HasEigenvector (toLin b b (diagonal d)) (d i) (b i) :=
⟨mem_eigenspace_iff.mpr by simp [diagonal], Basis.ne_zero b i⟩

/--
lemma `hasEigenvector_toLin'_diagonal` / 引理 `hasEigenvector_toLin'_diagonal`

English:
lemma hasEigenvector_toLin'_diagonal
  given: (d : n -> R) (i : n)
  proof: hasEigenvector_toLin_diagonal _ _ (Pi.basisFun R n)

中文:
引理 hasEigenvector_toLin'_diagonal
  条件: (d : n -> R) (i : n)
  证明: hasEigenvector_toLin_diagonal _ _ (Pi.basisFun R n)

Depends on / 依赖: Pi.basisFun, basisFun, hasEigenvector_toLin_diagonal
-/
lemma hasEigenvector_toLin'_diagonal (d : n -> R) (i : n) :
    HasEigenvector (toLin' (diagonal d)) (d i) (Pi.basisFun R n i) :=
  hasEigenvector_toLin_diagonal _ _ (Pi.basisFun R n)

set_option linter.overlappingInstances false

/--
lemma `hasEigenvalue_toLin_diagonal_iff` / 引理 `hasEigenvalue_toLin_diagonal_iff`

English:
lemma hasEigenvalue_toLin_diagonal_iff
  statement: (d : n -> R) {μ : R} [IsDomain R] [IsTorsionFree R M]
  proof: by
  have (i : n) : HasEigenvalue (toLin b b (diagonal d)) (d i) :=
hasEigenvalue_of_hasEigenvector hasEigenvector_toLin_diagonal d i b
  constructor
  · contrapose!
    intro hμ h_eig
    have h_iSup : ⨆ μ in Set.range d, eigenspace (toLin b b (diagonal d)) μ = ⊤ := by
      rw [eq_top_iff]; rw [← b.span_eq]; rw [Submodule.span_le]
      rintro - ⟨i, rfl⟩
      simp only [SetLike.mem_coe]
      apply Submodule.mem_iSup_of_mem (d i)
      apply Submodule.mem_iSup_of_mem ⟨i, rfl⟩
      rw [mem_eigenspace_iff]
      exact (hasEigenvector_toLin_diagonal d i b).apply_eq_smul
    have hμ_notMem : μ ∉ Set.range d := by simpa using fun i => (hμ i)
.disjoint_biSup hμ_notMem have := eigenspaces_iSupIndep (toLin b b (diagonal d))
    rw [h_iSup]; rw [disjoint_top] at this
    exact h_eig this
  · rintro ⟨i, rfl⟩
    exact this i

中文:
引理 hasEigenvalue_toLin_diagonal_iff
  结论: (d : n -> R) {μ : R} [是整环 R] [是无挠 R M]
  证明: by
  have (i : n) : HasEigenvalue (toLin b b (diagonal d)) (d i) :=
hasEigenvalue_of_hasEigenvector hasEigenvector_toLin_diagonal d i b
  constructor
  · contrapose!
    intro hμ h_eig
    have h_iSup : ⨆ μ in Set.range d, eigenspace (toLin b b (diagonal d)) μ = ⊤ := by
      rw [eq_top_iff]; rw [← b.span_eq]; rw [Submodule.span_le]
      rintro - ⟨i, rfl⟩
      simp only [SetLike.mem_coe]
      apply Submodule.mem_iSup_of_mem (d i)
      apply Submodule.mem_iSup_of_mem ⟨i, rfl⟩
      rw [mem_eigenspace_iff]
      exact (hasEigenvector_toLin_diagonal d i b).apply_eq_smul
    have hμ_notMem : μ ∉ Set.range d := by simpa using fun i => (hμ i)
.disjoint_biSup hμ_notMem have := eigenspaces_iSupIndep (toLin b b (diagonal d))
    rw [h_iSup]; rw [disjoint_top] at this
    exact h_eig this
  · rintro ⟨i, rfl⟩
    exact this i

Depends on / 依赖: HasEigenvalue, Set.range, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_iSup_of_mem, Submodule.span_le, b.span_eq, contrapose, diagonal, eigenspace, eq_top_iff, h_eig, h_iSup, hasEigenvalue_of_hasEigenvector, hasEigenvector_toLin_diagonal, mem_coe, mem_eigenspace_iff, mem_iSup_of_mem, span_eq
-/
lemma hasEigenvalue_toLin_diagonal_iff (d : n -> R) {μ : R} [IsDomain R] [IsTorsionFree R M]
    (b : Basis n R M) : HasEigenvalue (toLin b b (diagonal d)) μ ↔ exists i, d i = μ := by
  have (i : n) : HasEigenvalue (toLin b b (diagonal d)) (d i) :=
hasEigenvalue_of_hasEigenvector hasEigenvector_toLin_diagonal d i b
  constructor
  · contrapose!
    intro hμ h_eig
    have h_iSup : ⨆ μ in Set.range d, eigenspace (toLin b b (diagonal d)) μ = ⊤ := by
      rw [eq_top_iff]; rw [← b.span_eq]; rw [Submodule.span_le]
      rintro - ⟨i, rfl⟩
      simp only [SetLike.mem_coe]
      apply Submodule.mem_iSup_of_mem (d i)
      apply Submodule.mem_iSup_of_mem ⟨i, rfl⟩
      rw [mem_eigenspace_iff]
      exact (hasEigenvector_toLin_diagonal d i b).apply_eq_smul
    have hμ_notMem : μ ∉ Set.range d := by simpa using fun i => (hμ i)
.disjoint_biSup hμ_notMem have := eigenspaces_iSupIndep (toLin b b (diagonal d))
    rw [h_iSup]; rw [disjoint_top] at this
    exact h_eig this
  · rintro ⟨i, rfl⟩
    exact this i

/--
lemma `hasEigenvalue_toLin'_diagonal_iff` / 引理 `hasEigenvalue_toLin'_diagonal_iff`

English:
lemma hasEigenvalue_toLin'_diagonal_iff
  given: [IsDomain R] (d : n -> R) {μ : R}
  proof: hasEigenvalue_toLin_diagonal_iff _ Pi.basisFun R n

中文:
引理 hasEigenvalue_toLin'_diagonal_iff
  条件: [是整环 R] (d : n -> R) {μ : R}
  证明: hasEigenvalue_toLin_diagonal_iff _ Pi.basisFun R n

Depends on / 依赖: Pi.basisFun, basisFun, hasEigenvalue_toLin_diagonal_iff
-/
lemma hasEigenvalue_toLin'_diagonal_iff [IsDomain R] (d : n -> R) {μ : R} :
    HasEigenvalue (toLin' (diagonal d)) μ ↔ (exists i, d i = μ) :=
hasEigenvalue_toLin_diagonal_iff _ Pi.basisFun R n

end NontrivialCommRing

namespace Matrix

variable [CommRing R] [AddCommGroup M] [Module R M] (d : n -> R) {μ : R} (b : Basis n R M)

/--
lemma `_root_.Module.End.HasEigenvalue.nonempty` / 引理 `_root_.Module.End.HasEigenvalue.nonempty`

English:
lemma _root_.Module.End.HasEigenvalue.nonempty
  proof: by
  rw [hasEigenvalue_iff] at hμ
  contrapose! hμ
  exact Submodule.eq_bot_of_subsingleton

@[simp]

中文:
引理 _root_.模.End.HasEigenvalue.nonempty
  证明: by
  rw [hasEigenvalue_iff] at hμ
  contrapose! hμ
  exact Submodule.eq_bot_of_subsingleton

@[simp]

Depends on / 依赖: Submodule, Submodule.eq_bot_of_subsingleton, contrapose, eq_bot_of_subsingleton, hasEigenvalue_iff
-/
lemma _root_.Module.End.HasEigenvalue.nonempty
    {A : Matrix n n R} {μ : R} (hμ : HasEigenvalue A.toLin' μ) :
    Nonempty n := by
  rw [hasEigenvalue_iff] at hμ
  contrapose! hμ
  exact Submodule.eq_bot_of_subsingleton

@[simp]
/--
lemma `iSup_eigenspace_toLin_diagonal_eq_top` / 引理 `iSup_eigenspace_toLin_diagonal_eq_top`

English:
lemma iSup_eigenspace_toLin_diagonal_eq_top
  proof: by
  refine (Submodule.eq_top_iff_forall_basis_mem b).mpr fun j => ?_
exact Submodule.mem_iSup_of_mem (d j) by simp [diagonal_apply]

@[simp]

中文:
引理 iSup_eigenspace_toLin_diagonal_eq_top
  证明: by
  refine (Submodule.eq_top_iff_forall_basis_mem b).mpr fun j => ?_
exact Submodule.mem_iSup_of_mem (d j) by simp [diagonal_apply]

@[simp]

Depends on / 依赖: Submodule, Submodule.eq_top_iff_forall_basis_mem, Submodule.mem_iSup_of_mem, diagonal_apply, eq_top_iff_forall_basis_mem, mem_iSup_of_mem
-/
lemma iSup_eigenspace_toLin_diagonal_eq_top :
    ⨆ μ, eigenspace ((diagonal d).toLin b b) μ = ⊤ := by
  refine (Submodule.eq_top_iff_forall_basis_mem b).mpr fun j => ?_
exact Submodule.mem_iSup_of_mem (d j) by simp [diagonal_apply]

@[simp]
/--
lemma `iSup_eigenspace_toLin'_diagonal_eq_top` / 引理 `iSup_eigenspace_toLin'_diagonal_eq_top`

English:
lemma iSup_eigenspace_toLin'_diagonal_eq_top
  proof: iSup_eigenspace_toLin_diagonal_eq_top d Pi.basisFun R n

中文:
引理 iSup_eigenspace_toLin'_diagonal_eq_top
  证明: iSup_eigenspace_toLin_diagonal_eq_top d Pi.basisFun R n

Depends on / 依赖: Pi.basisFun, basisFun, iSup_eigenspace_toLin_diagonal_eq_top
-/
lemma iSup_eigenspace_toLin'_diagonal_eq_top :
    ⨆ μ, eigenspace (diagonal d).toLin' μ = ⊤ :=
iSup_eigenspace_toLin_diagonal_eq_top d Pi.basisFun R n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `maxGenEigenspace_toLin_diagonal_eq_eigenspace` / 引理 `maxGenEigenspace_toLin_diagonal_eq_eigenspace`

English:
lemma maxGenEigenspace_toLin_diagonal_eq_eigenspace
  given: [IsDomain R]
  proof: by
  refine le_antisymm (fun x hx => ?_) eigenspace_le_maxGenEigenspace
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace _ _ _).mp hx
  replace hk (j : n) : b.repr x j = 0 ∨ d j = μ ∧ k != 0 := by
    have aux : (diagonal d).toLin b b - μ • 1 = (diagonal (d - μ • 1)).toLin b b := by
      rw [Pi.sub_def]; rw [← diagonal_sub]; simp [one_eq_id]
    rw [aux]; rw [← toLin_pow]; rw [diagonal_pow]; rw [toLin_apply_eq_zero_iff] at hk
    simpa [mulVec_eq_sum, diagonal_apply, sub_eq_zero] using hk j
  have aux (j : n) : (b.repr x j * d j) • b j = μ • (b.repr x j • b j) := by
    rcases hk j with hj | hj
    · simp [hj]
    · rw [← hj.1, mul_comm, mul_smul]
  simp [toLin_apply, mulVec_eq_sum, diagonal_apply, aux, ← Finset.smul_sum]

@[simp]

中文:
引理 maxGenEigenspace_toLin_diagonal_eq_eigenspace
  条件: [是整环 R]
  证明: by
  refine le_antisymm (fun x hx => ?_) eigenspace_le_maxGenEigenspace
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace _ _ _).mp hx
  replace hk (j : n) : b.repr x j = 0 ∨ d j = μ ∧ k != 0 := by
    have aux : (diagonal d).toLin b b - μ • 1 = (diagonal (d - μ • 1)).toLin b b := by
      rw [Pi.sub_def]; rw [← diagonal_sub]; simp [one_eq_id]
    rw [aux]; rw [← toLin_pow]; rw [diagonal_pow]; rw [toLin_apply_eq_zero_iff] at hk
    simpa [mulVec_eq_sum, diagonal_apply, sub_eq_zero] using hk j
  have aux (j : n) : (b.repr x j * d j) • b j = μ • (b.repr x j • b j) := by
    rcases hk j with hj | hj
    · simp [hj]
    · rw [← hj.1, mul_comm, mul_smul]
  simp [toLin_apply, mulVec_eq_sum, diagonal_apply, aux, ← Finset.smul_sum]

@[simp]

Depends on / 依赖: Pi.sub_def, b.repr, diagonal, diagonal_apply, diagonal_pow, diagonal_sub, eigenspace_le_maxGenEigenspace, le_antisymm, mem_maxGenEigenspace, mulVec_eq_sum, one_eq_id, replace, sub_def, sub_eq_zero, toLin_apply_eq_zero_iff, toLin_pow
-/
lemma maxGenEigenspace_toLin_diagonal_eq_eigenspace [IsDomain R] :
    maxGenEigenspace ((diagonal d).toLin b b) μ = eigenspace ((diagonal d).toLin b b) μ := by
  refine le_antisymm (fun x hx => ?_) eigenspace_le_maxGenEigenspace
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace _ _ _).mp hx
  replace hk (j : n) : b.repr x j = 0 ∨ d j = μ ∧ k != 0 := by
    have aux : (diagonal d).toLin b b - μ • 1 = (diagonal (d - μ • 1)).toLin b b := by
      rw [Pi.sub_def]; rw [← diagonal_sub]; simp [one_eq_id]
    rw [aux]; rw [← toLin_pow]; rw [diagonal_pow]; rw [toLin_apply_eq_zero_iff] at hk
    simpa [mulVec_eq_sum, diagonal_apply, sub_eq_zero] using hk j
  have aux (j : n) : (b.repr x j * d j) • b j = μ • (b.repr x j • b j) := by
    rcases hk j with hj | hj
    · simp [hj]
    · rw [← hj.1, mul_comm, mul_smul]
  simp [toLin_apply, mulVec_eq_sum, diagonal_apply, aux, ← Finset.smul_sum]

@[simp]
/--
lemma `maxGenEigenspace_toLin'_diagonal_eq_eigenspace` / 引理 `maxGenEigenspace_toLin'_diagonal_eq_eigenspace`

English:
lemma maxGenEigenspace_toLin'_diagonal_eq_eigenspace
  given: [IsDomain R]
  proof: maxGenEigenspace_toLin_diagonal_eq_eigenspace d Pi.basisFun R n

@[simp]

中文:
引理 maxGenEigenspace_toLin'_diagonal_eq_eigenspace
  条件: [是整环 R]
  证明: maxGenEigenspace_toLin_diagonal_eq_eigenspace d Pi.basisFun R n

@[simp]

Depends on / 依赖: Pi.basisFun, basisFun, maxGenEigenspace_toLin_diagonal_eq_eigenspace
-/
lemma maxGenEigenspace_toLin'_diagonal_eq_eigenspace [IsDomain R] :
    maxGenEigenspace (diagonal d).toLin' μ = eigenspace (diagonal d).toLin' μ :=
maxGenEigenspace_toLin_diagonal_eq_eigenspace d Pi.basisFun R n

@[simp]
/--
theorem `_root_.LinearMap.spectrum_toMatrix` / 定理 `_root_.LinearMap.spectrum_toMatrix`

English:
theorem _root_.LinearMap.spectrum_toMatrix
  given: (f : M ->ₗ[R] M) (b : Basis n R M)
  proof: AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv b) f

@[simp]

中文:
定理 _root_.线性映射.spectrum_toMatrix
  条件: (f : M ->ₗ[R] M) (b : 基 n R M)
  证明: AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv b) f

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.spectrum_eq, LinearMap, LinearMap.toMatrixAlgEquiv, spectrum_eq, toMatrixAlgEquiv
-/
theorem _root_.LinearMap.spectrum_toMatrix (f : M ->ₗ[R] M) (b : Basis n R M) :
    spectrum R (f.toMatrix b b) = spectrum R f :=
  AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv b) f

@[simp]
/--
theorem `_root_.LinearMap.spectrum_toMatrix'` / 定理 `_root_.LinearMap.spectrum_toMatrix'`

English:
theorem _root_.LinearMap.spectrum_toMatrix'
  given: (f : (n -> R) ->ₗ[R] (n -> R))
  proof: AlgEquiv.spectrum_eq LinearMap.toMatrixAlgEquiv' f

@[simp]

中文:
定理 _root_.线性映射.spectrum_toMatrix'
  条件: (f : (n -> R) ->ₗ[R] (n -> R))
  证明: AlgEquiv.spectrum_eq LinearMap.toMatrixAlgEquiv' f

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.spectrum_eq, LinearMap, LinearMap.toMatrixAlgEquiv, spectrum_eq, toMatrixAlgEquiv
-/
theorem _root_.LinearMap.spectrum_toMatrix' (f : (n -> R) ->ₗ[R] (n -> R)) :
    spectrum R f.toMatrix' = spectrum R f :=
  AlgEquiv.spectrum_eq LinearMap.toMatrixAlgEquiv' f

@[simp]
/--
theorem `spectrum_toLin` / 定理 `spectrum_toLin`

English:
theorem spectrum_toLin
  given: (A : Matrix n n R) (b : Basis n R M)
  proof: AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv b) A

@[simp]

中文:
定理 spectrum_toLin
  条件: (A : 矩阵 n n R) (b : 基 n R M)
  证明: AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv b) A

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.spectrum_eq, Matrix, Matrix.toLinAlgEquiv, spectrum_eq, toLinAlgEquiv
-/
theorem spectrum_toLin (A : Matrix n n R) (b : Basis n R M) :
    spectrum R (A.toLin b b) = spectrum R A :=
  AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv b) A

@[simp]
/--
theorem `spectrum_toLin'` / 定理 `spectrum_toLin'`

English:
theorem spectrum_toLin'
  given: (A : Matrix n n R)
  statement: spectrum R A.toLin' = spectrum R A
  proof: AlgEquiv.spectrum_eq Matrix.toLinAlgEquiv' A

中文:
定理 spectrum_toLin'
  条件: (A : 矩阵 n n R)
  结论: spectrum R A.toLin' = spectrum R A
  证明: AlgEquiv.spectrum_eq Matrix.toLinAlgEquiv' A

Depends on / 依赖: AlgEquiv, AlgEquiv.spectrum_eq, Matrix, Matrix.toLinAlgEquiv, spectrum_eq, toLinAlgEquiv
-/
theorem spectrum_toLin' (A : Matrix n n R) : spectrum R A.toLin' = spectrum R A :=
  AlgEquiv.spectrum_eq Matrix.toLinAlgEquiv' A

end Matrix

/--
lemma `spectrum_diagonal` / 引理 `spectrum_diagonal`

English:
lemma spectrum_diagonal
  given: [Field R] (d : n -> R)
  proof: by
  ext μ
  rw [← AlgEquiv.spectrum_eq (toLinAlgEquiv <| Pi.basisFun R n)]; rw [← hasEigenvalue_iff_mem_spectrum]
  exact hasEigenvalue_toLin'_diagonal_iff d

中文:
引理 spectrum_diagonal
  条件: [域 R] (d : n -> R)
  证明: by
  ext μ
  rw [← AlgEquiv.spectrum_eq (toLinAlgEquiv <| Pi.basisFun R n)]; rw [← hasEigenvalue_iff_mem_spectrum]
  exact hasEigenvalue_toLin'_diagonal_iff d
-/
@[simp] lemma spectrum_diagonal [Field R] (d : n -> R) :
    spectrum R (diagonal d) = Set.range d := by
  ext μ
  rw [← AlgEquiv.spectrum_eq (toLinAlgEquiv <| Pi.basisFun R n)]; rw [← hasEigenvalue_iff_mem_spectrum]
  exact hasEigenvalue_toLin'_diagonal_iff d

end SpectrumDiagonal
