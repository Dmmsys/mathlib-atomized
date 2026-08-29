/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The partial order on matrices

This file constructs the partial order and star ordered instances on matrices on `𝕜`.
This allows us to use more general results from C⋆-algebras, like `CFC.sqrt`.

## Main results

* `Matrix.instPartialOrder`: the partial order on matrices given by `x ≤ y := (y - x).PosSemidef`.
* `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`: for a positive semi-definite matrix `A`,
  we have `x⋆ A x = 0` iff `A x = 0`.
* `Matrix.toMatrixInnerProductSpace`: the inner product on matrices induced by a
  positive semi-definite matrix `M`: `⟪x, y⟫ = (y * M * xᴴ).trace`.

## Implementation notes

Note that the partial order instance is scoped to `MatrixOrder`.
Please `open scoped MatrixOrder` to use this.
-/

@[expose] public section

variable {𝕜 n : Type*} [RCLike 𝕜]

open scoped ComplexOrder
open Matrix

namespace Matrix

section PartialOrder

/--
Definition of `instPreOrder` / `instPreOrder` 的定义

English:
abbreviation instPreOrder
  signature: : Preorder (Matrix n n 𝕜) where
  body: (B - A).PosSemidef
  le_refl A := sub_self A ▸ PosSemidef.zero
  le_trans A B C h₁ h₂ := sub_add_sub_cancel C B A ▸ h₂.add h₁

scoped[MatrixOrder] attribute [instance] Matrix.instPreOrder

中文:
缩写 instPreOrder
  签名: : 预序 (矩阵 n n 𝕜) where
  定义体: (B - A).PosSemidef
  le_refl A := sub_self A ▸ PosSemidef.zero
  le_trans A B C h₁ h₂ := sub_add_sub_cancel C B A ▸ h₂.add h₁

scoped[MatrixOrder] attribute [instance] Matrix.instPreOrder

Depends on / 依赖: PosSemidef
-/
abbrev instPreOrder : Preorder (Matrix n n 𝕜) where
  le A B := (B - A).PosSemidef
  le_refl A := sub_self A ▸ PosSemidef.zero
  le_trans A B C h₁ h₂ := sub_add_sub_cancel C B A ▸ h₂.add h₁

scoped[MatrixOrder] attribute [instance] Matrix.instPreOrder

open MatrixOrder

/--
lemma `le_iff` / 引理 `le_iff`

English:
lemma le_iff
  given: {A B : Matrix n n 𝕜}
  statement: A <= B ↔ (B - A).PosSemidef
  proof: Iff.rfl

中文:
引理 le_iff
  条件: {A B : 矩阵 n n 𝕜}
  结论: A <= B ↔ (B - A).PosSemidef
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_iff {A B : Matrix n n 𝕜} : A <= B ↔ (B - A).PosSemidef := Iff.rfl

/--
lemma `nonneg_iff_posSemidef` / 引理 `nonneg_iff_posSemidef`

English:
lemma nonneg_iff_posSemidef
  given: {A : Matrix n n 𝕜}
  statement: 0 <= A ↔ A.PosSemidef
  proof: by rw [le_iff, sub_zero]

protected alias ⟨LE.le.posSemidef, PosSemidef.nonneg⟩ := nonneg_iff_posSemidef

中文:
引理 nonneg_iff_posSemidef
  条件: {A : 矩阵 n n 𝕜}
  结论: 0 <= A ↔ A.PosSemidef
  证明: by rw [le_iff, sub_zero]

protected alias ⟨LE.le.posSemidef, PosSemidef.nonneg⟩ := nonneg_iff_posSemidef

Depends on / 依赖: le_iff, sub_zero
-/
lemma nonneg_iff_posSemidef {A : Matrix n n 𝕜} : 0 <= A ↔ A.PosSemidef := by rw [le_iff, sub_zero]

protected alias ⟨LE.le.posSemidef, PosSemidef.nonneg⟩ := nonneg_iff_posSemidef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosSemidef.nonneg

/--
lemma `le_antisymm_aux` / 引理 `le_antisymm_aux`

English:
lemma le_antisymm_aux
  given: {A : Matrix n n 𝕜} (h₁ : A.PosSemidef) (h₂ : (-A).PosSemidef)
  proof: by
  classical
  ext i j
  have hdiag i : A i i = 0 :=
    le_antisymm (by simpa using h₂.diag_nonneg) (by simpa using h₁.diag_nonneg)
  have h1 := h₁.2 (.single i 1 + .single j (A j i))
  have h2 := h₂.2 (.single i 1 + .single j (A j i))
  simp [Finsupp.sum_add_index, mul_add, add_mul,
      -neg_a

中文:
引理 le_antisymm_aux
  条件: {A : 矩阵 n n 𝕜} (h₁ : A.PosSemidef) (h₂ : (-A).PosSemidef)
  证明: by
  classical
  ext i j
  have hdiag i : A i i = 0 :=
    le_antisymm (by simpa using h₂.diag_nonneg) (by simpa using h₁.diag_nonneg)
  have h1 := h₁.2 (.single i 1 + .single j (A j i))
  have h2 := h₂.2 (.single i 1 + .single j (A j i))
  simp [Finsupp.sum_add_index, mul_add, add_mul,
      -neg_a
-/
private lemma le_antisymm_aux {A : Matrix n n 𝕜} (h₁ : A.PosSemidef) (h₂ : (-A).PosSemidef) :
    A = 0 := by
  classical
  ext i j
  have hdiag i : A i i = 0 :=
    le_antisymm (by simpa using h₂.diag_nonneg) (by simpa using h₁.diag_nonneg)
  have h1 := h₁.2 (.single i 1 + .single j (A j i))
  have h2 := h₂.2 (.single i 1 + .single j (A j i))
  simp [Finsupp.sum_add_index, mul_add, add_mul,
      -neg_add_rev, hdiag, ← h₁.1.apply j i, -RCLike.star_def] at *
  simpa using le_antisymm h2 h1

/--
Definition of `instPartialOrder` / `instPartialOrder` 的定义

English:
abbreviation instPartialOrder
  signature: : PartialOrder (Matrix n n 𝕜) where
  body: by
    simpa [sub_eq_zero, eq_comm] using le_antisymm_aux h₁
     (by simpa only [← neg_sub B, le_iff] using h₂)

scoped[MatrixOrder] attribute [instance] Matrix.instPartialOrder

中文:
缩写 instPartialOrder
  签名: : 偏序 (矩阵 n n 𝕜) where
  定义体: by
    simpa [sub_eq_zero, eq_comm] using le_antisymm_aux h₁
     (by simpa only [← neg_sub B, le_iff] using h₂)

scoped[MatrixOrder] attribute [instance] Matrix.instPartialOrder

Depends on / 依赖: eq_comm, le_antisymm_aux, le_iff, neg_sub, sub_eq_zero
-/
abbrev instPartialOrder : PartialOrder (Matrix n n 𝕜) where
  le_antisymm A B h₁ h₂ := by
    simpa [sub_eq_zero, eq_comm] using le_antisymm_aux h₁
     (by simpa only [← neg_sub B, le_iff] using h₂)

scoped[MatrixOrder] attribute [instance] Matrix.instPartialOrder

/--
lemma `instIsOrderedAddMonoid` / 引理 `instIsOrderedAddMonoid`

English:
lemma instIsOrderedAddMonoid
  statement: IsOrderedAddMonoid (Matrix n n 𝕜) where
  proof: by rwa [le_iff, add_sub_add_right_eq_sub]

scoped[MatrixOrder] attribute [instance] Matrix.instIsOrderedAddMonoid

中文:
引理 instIsOrderedAddMonoid
  结论: 是OrderedAdd幺半群 (矩阵 n n 𝕜) where
  证明: by rwa [le_iff, add_sub_add_right_eq_sub]

scoped[MatrixOrder] attribute [instance] Matrix.instIsOrderedAddMonoid

Depends on / 依赖: add_sub_add_right_eq_sub, le_iff
-/
lemma instIsOrderedAddMonoid : IsOrderedAddMonoid (Matrix n n 𝕜) where
  add_le_add_left _ _ _ _ := by rwa [le_iff, add_sub_add_right_eq_sub]

scoped[MatrixOrder] attribute [instance] Matrix.instIsOrderedAddMonoid

variable [Fintype n]

/--
lemma `instNonnegSpectrumClass` / 引理 `instNonnegSpectrumClass`

English:
lemma instNonnegSpectrumClass
  statement: NonnegSpectrumClass Real (Matrix n n 𝕜) where
  proof: by
    classical
    simp only [quasispectrum_eq_spectrum_union_zero Real A, Set.union_singleton, Set.mem_insert_iff,
      forall_eq_or_imp, le_refl, true_and]
    intro x hx
    obtain ⟨i, rfl⟩ := Set.ext_iff.mp
.mp hx hA.posSemidef.1.spectrum_real_eq_range_eigenvalues x
    exact hA.posSemidef.ei

中文:
引理 instNonnegSpectrumClass
  结论: NonnegSpectrum类 实数 (矩阵 n n 𝕜) where
  证明: by
    classical
    simp only [quasispectrum_eq_spectrum_union_zero Real A, Set.union_singleton, Set.mem_insert_iff,
      forall_eq_or_imp, le_refl, true_and]
    intro x hx
    obtain ⟨i, rfl⟩ := Set.ext_iff.mp
.mp hx hA.posSemidef.1.spectrum_real_eq_range_eigenvalues x
    exact hA.posSemidef.ei

Depends on / 依赖: Set.ext_iff.mp, Set.mem_insert_iff, Set.union_singleton, classical, eigenvalues_nonneg, ext_iff, forall_eq_or_imp, hA.posSemidef, hA.posSemidef.eigenvalues_nonneg, le_refl, mem_insert_iff, posSemidef, quasispectrum_eq_spectrum_union_zero, spectrum_real_eq_range_eigenvalues, true_and, union_singleton
-/
lemma instNonnegSpectrumClass : NonnegSpectrumClass Real (Matrix n n 𝕜) where
  quasispectrum_nonneg_of_nonneg A hA := by
    classical
    simp only [quasispectrum_eq_spectrum_union_zero Real A, Set.union_singleton, Set.mem_insert_iff,
      forall_eq_or_imp, le_refl, true_and]
    intro x hx
    obtain ⟨i, rfl⟩ := Set.ext_iff.mp
.mp hx hA.posSemidef.1.spectrum_real_eq_range_eigenvalues x
    exact hA.posSemidef.eigenvalues_nonneg _

scoped[MatrixOrder] attribute [instance] instNonnegSpectrumClass

/--
lemma `instStarOrderedRing` / 引理 `instStarOrderedRing`

English:
lemma instStarOrderedRing
  statement: StarOrderedRing (Matrix n n 𝕜)
  proof: .of_nonneg_iff' add_le_add_right fun A =>
    ⟨fun hA => by
      classical
      obtain ⟨X, hX, -, rfl⟩ :=
        sub_zero A ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian
          (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
      exact ⟨X, hX.star_eq.symm ▸ r

中文:
引理 instStarOrderedRing
  结论: StarOrdered环 (矩阵 n n 𝕜)
  证明: .of_nonneg_iff' add_le_add_right fun A =>
    ⟨fun hA => by
      classical
      obtain ⟨X, hX, -, rfl⟩ :=
        sub_zero A ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian
          (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
      exact ⟨X, hX.star_eq.symm ▸ r

Depends on / 依赖: CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, QuasispectrumRestricts, QuasispectrumRestricts.nnreal_of_nonneg, add_le_add_right, classical, exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, hA.isHermitian, hA.nonneg, hX.star_eq.symm, isHermitian, nnreal_of_nonneg, nonneg, of_nonneg_iff, posSemidef_conjTranspose_mul_self, star_eq, sub_zero
-/
lemma instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
  .of_nonneg_iff' add_le_add_right fun A =>
    ⟨fun hA => by
      classical
      obtain ⟨X, hX, -, rfl⟩ :=
        sub_zero A ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian
          (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
      exact ⟨X, hX.star_eq.symm ▸ rfl⟩,
    fun ⟨A, hA⟩ => hA ▸ (posSemidef_conjTranspose_mul_self A).nonneg⟩

scoped[MatrixOrder] attribute [instance] instStarOrderedRing

end PartialOrder

open scoped MatrixOrder

variable [Fintype n]

namespace PosSemidef

section sqrtDeprecated

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

include hA

/--
lemma `inv_sqrt` / 引理 `inv_sqrt`

English:
lemma inv_sqrt
  statement: (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹
  proof: by
  rw [eq_comm]; rw [CFC.sqrt_eq_iff _ _ hA.inv.nonneg (CFC.sqrt_nonneg A).posSemidef.inv.nonneg]; rw [← sq]; rw [inv_pow']; rw [CFC.sq_sqrt A]

中文:
引理 inv_sqrt
  结论: (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹
  证明: by
  rw [eq_comm]; rw [CFC.sqrt_eq_iff _ _ hA.inv.nonneg (CFC.sqrt_nonneg A).posSemidef.inv.nonneg]; rw [← sq]; rw [inv_pow']; rw [CFC.sq_sqrt A]

Depends on / 依赖: CFC.sq_sqrt, CFC.sqrt_eq_iff, CFC.sqrt_nonneg, eq_comm, hA.inv.nonneg, inv_pow, nonneg, posSemidef, posSemidef.inv.nonneg, sq_sqrt, sqrt_eq_iff, sqrt_nonneg
-/
lemma inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ := by
  rw [eq_comm]; rw [CFC.sqrt_eq_iff _ _ hA.inv.nonneg (CFC.sqrt_nonneg A).posSemidef.inv.nonneg]; rw [← sq]; rw [inv_pow']; rw [CFC.sq_sqrt A]

end sqrtDeprecated

/--
theorem `dotProduct_mulVec_zero_iff` / 定理 `dotProduct_mulVec_zero_iff`

English:
theorem dotProduct_mulVec_zero_iff
  given: {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n -> 𝕜)
  proof: by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ dotProduct_zero _⟩
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp_rw [← Matrix.mulVec_mulVec, dotProduct_mulVec _ _ (B *ᵥ x), star_eq_conjTranspose,
    vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero

中文:
定理 dotProduct_mulVec_zero_iff
  条件: {A : 矩阵 n n 𝕜} (hA : PosSemidef A) (x : n -> 𝕜)
  证明: by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ dotProduct_zero _⟩
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp_rw [← Matrix.mulVec_mulVec, dotProduct_mulVec _ _ (B *ᵥ x), star_eq_conjTranspose,
    vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero

Depends on / 依赖: CStarAlgebra, CStarAlgebra.nonneg_iff_eq_star_mul_self.mp, Matrix, Matrix.mulVec_mulVec, classical, dotProduct_mulVec, dotProduct_star_self_eq_zero, dotProduct_zero, hA.nonneg, mulVec_mulVec, mulVec_zero, nonneg, nonneg_iff_eq_star_mul_self, simp_rw, star_eq_conjTranspose, star_star, vecMul_conjTranspose
-/
theorem dotProduct_mulVec_zero_iff {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n -> 𝕜) :
    star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ dotProduct_zero _⟩
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp_rw [← Matrix.mulVec_mulVec, dotProduct_mulVec _ _ (B *ᵥ x), star_eq_conjTranspose,
    vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero] at h ⊢
  rw [h]; rw [mulVec_zero]

/--
theorem `toLinearMap₂'_zero_iff` / 定理 `toLinearMap₂'_zero_iff`

English:
theorem toLinearMap₂'_zero_iff
  statement: [DecidableEq n]
  proof: by
  simpa only [toLinearMap₂'_apply'] using hA.dotProduct_mulVec_zero_iff x

中文:
定理 toLinearMap₂'_zero_iff
  结论: [DecidableEq n]
  证明: by
  simpa only [toLinearMap₂'_apply'] using hA.dotProduct_mulVec_zero_iff x

Depends on / 依赖: _apply, dotProduct_mulVec_zero_iff, hA.dotProduct_mulVec_zero_iff
-/
theorem toLinearMap₂'_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n -> 𝕜) :
    Matrix.toLinearMap₂' 𝕜 A (star x) x = 0 ↔ A *ᵥ x = 0 := by
  simpa only [toLinearMap₂'_apply'] using hA.dotProduct_mulVec_zero_iff x

/--
theorem `det_sqrt` / 定理 `det_sqrt`

English:
theorem det_sqrt
  given: [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef)
  proof: by
  rw [CFC.sqrt_eq_cfc]; rw [cfc_nnreal_eq_real _ A]; rw [hA.1.cfc_eq]; rw [RCLike.sqrt_of_nonneg hA.det_nonneg]
  simp only [IsHermitian.cfc, Real.coe_sqrt, Real.coe_toNNReal', det_map, det_diagonal,
    Function.comp_apply, hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod,
    RCLike

中文:
定理 det_sqrt
  条件: [DecidableEq n] {A : 矩阵 n n 𝕜} (hA : A.PosSemidef)
  证明: by
  rw [CFC.sqrt_eq_cfc]; rw [cfc_nnreal_eq_real _ A]; rw [hA.1.cfc_eq]; rw [RCLike.sqrt_of_nonneg hA.det_nonneg]
  simp only [IsHermitian.cfc, Real.coe_sqrt, Real.coe_toNNReal', det_map, det_diagonal,
    Function.comp_apply, hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod,
    RCLike

Depends on / 依赖: CFC.sqrt_eq_cfc, Function, Function.comp_apply, IsHermitian, IsHermitian.cfc, RCLike, RCLike.ofReal_prod, RCLike.ofReal_re, RCLike.sqrt_of_nonneg, Real.coe_sqrt, Real.coe_toNNReal, Real.sqrt_prod, cfc_eq, cfc_nnreal_eq_real, coe_sqrt, coe_toNNReal, comp_apply, det_diagonal, det_eq_prod_eigenvalues, det_map
-/
theorem det_sqrt [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (CFC.sqrt A).det = RCLike.sqrt A.det := by
  rw [CFC.sqrt_eq_cfc]; rw [cfc_nnreal_eq_real _ A]; rw [hA.1.cfc_eq]; rw [RCLike.sqrt_of_nonneg hA.det_nonneg]
  simp only [IsHermitian.cfc, Real.coe_sqrt, Real.coe_toNNReal', det_map, det_diagonal,
    Function.comp_apply, hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod,
    RCLike.ofReal_re, Real.sqrt_prod _ fun _ _ => hA.eigenvalues_nonneg _]
  grind

end PosSemidef

/--
theorem `IsHermitian.det_abs` / 定理 `IsHermitian.det_abs`

English:
theorem IsHermitian.det_abs
  given: [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
  proof: by
  rw [CFC.abs_eq_cfc_norm A]; rw [hA.cfc_eq]
  simp [IsHermitian.cfc, -Unitary.conjStarAlgAut_apply, hA.det_eq_prod_eigenvalues]

中文:
定理 IsHermitian.det_abs
  条件: [DecidableEq n] {A : 矩阵 n n 𝕜} (hA : A.IsHermitian)
  证明: by
  rw [CFC.abs_eq_cfc_norm A]; rw [hA.cfc_eq]
  simp [IsHermitian.cfc, -Unitary.conjStarAlgAut_apply, hA.det_eq_prod_eigenvalues]

Depends on / 依赖: CFC.abs_eq_cfc_norm, IsHermitian, IsHermitian.cfc, Unitary, Unitary.conjStarAlgAut_apply, abs_eq_cfc_norm, cfc_eq, conjStarAlgAut_apply, det_eq_prod_eigenvalues, hA.cfc_eq, hA.det_eq_prod_eigenvalues
-/
theorem IsHermitian.det_abs [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    det (CFC.abs A) = ‖det A‖ := by
  rw [CFC.abs_eq_cfc_norm A]; rw [hA.cfc_eq]
  simp [IsHermitian.cfc, -Unitary.conjStarAlgAut_apply, hA.det_eq_prod_eigenvalues]

/--
theorem `posSemidef_iff_isHermitian_and_spectrum_nonneg` / 定理 `posSemidef_iff_isHermitian_and_spectrum_nonneg`

English:
theorem posSemidef_iff_isHermitian_and_spectrum_nonneg
  given: [DecidableEq n] {A : Matrix n n 𝕜}
  proof: by
  refine ⟨fun h => ⟨h.isHermitian, fun a => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · simp only [h.isHermitian.spectrum_eq_image_range, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, Set.mem_ofPred_eq, forall_exists_index]
    rintro i rfl
    exact_mod_cast h.eigenvalues_nonneg _
  · rw [h1.posSem

中文:
定理 posSemidef_iff_isHermitian_and_spectrum_nonneg
  条件: [DecidableEq n] {A : 矩阵 n n 𝕜}
  证明: by
  refine ⟨fun h => ⟨h.isHermitian, fun a => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · simp only [h.isHermitian.spectrum_eq_image_range, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, Set.mem_ofPred_eq, forall_exists_index]
    rintro i rfl
    exact_mod_cast h.eigenvalues_nonneg _
  · rw [h1.posSem

Depends on / 依赖: Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, eigenvalues, eigenvalues_nonneg, exists_exists_eq_and, forall_exists_index, h.eigenvalues_nonneg, h.isHermitian, h.isHermitian.spectrum_eq_image_range, h1.eigenvalues, h1.posSemidef_iff_eigenvalues_nonneg, h1.spectrum_eq_image_range, isHermitian, mem_image, mem_ofPred_eq, mem_range, posSemidef_iff_eigenvalues_nonneg, spectrum_eq_image_range
-/
theorem posSemidef_iff_isHermitian_and_spectrum_nonneg [DecidableEq n] {A : Matrix n n 𝕜} :
    A.PosSemidef ↔ A.IsHermitian ∧ spectrum 𝕜 A subseteq {a : 𝕜 | 0 <= a} := by
  refine ⟨fun h => ⟨h.isHermitian, fun a => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · simp only [h.isHermitian.spectrum_eq_image_range, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, Set.mem_ofPred_eq, forall_exists_index]
    rintro i rfl
    exact_mod_cast h.eigenvalues_nonneg _
  · rw [h1.posSemidef_iff_eigenvalues_nonneg]
    intro i
    simpa [h1.spectrum_eq_image_range] using @h2 (h1.eigenvalues i)

/-- A positive semi-definite matrix is positive definite if and only if it is invertible. -/
@[grind =]
/--
theorem `PosSemidef.posDef_iff_isUnit` / 定理 `PosSemidef.posDef_iff_isUnit`

English:
theorem PosSemidef.posDef_iff_isUnit
  statement: [DecidableEq n] {x : Matrix n n 𝕜}
  proof: by
  refine ⟨fun h => h.isUnit, fun h => .of_dotProduct_mulVec_pos hx.1 fun v hv => ?_⟩
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  simp_rw [dotProduct_mulVec, ← vecMul_vecMul, star_eq_conjTranspose, ← star_mulVec,
    ← dotProduct_mulVec, dotProduct_star_self_pos_if

中文:
定理 PosSemidef.posDef_iff_isUnit
  结论: [DecidableEq n] {x : 矩阵 n n 𝕜}
  证明: by
  refine ⟨fun h => h.isUnit, fun h => .of_dotProduct_mulVec_pos hx.1 fun v hv => ?_⟩
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  simp_rw [dotProduct_mulVec, ← vecMul_vecMul, star_eq_conjTranspose, ← star_mulVec,
    ← dotProduct_mulVec, dotProduct_star_self_pos_if

Depends on / 依赖: CStarAlgebra, CStarAlgebra.nonneg_iff_eq_star_mul_self.mp, contrapose, dotProduct_mulVec, dotProduct_star_self_pos_iff, h.isUnit, hx.nonneg, isUnit, map_eq_zero_iff, mulVecLin, mulVecLin_apply, mulVec_injective_iff_isUnit, mulVec_injective_iff_isUnit.mpr, mulVec_mulVec, mulVec_zero, nonneg, nonneg_iff_eq_star_mul_self, of_dotProduct_mulVec_pos, simp_rw, star_eq_conjTranspose
-/
theorem PosSemidef.posDef_iff_isUnit [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.PosSemidef) : x.PosDef ↔ IsUnit x := by
  refine ⟨fun h => h.isUnit, fun h => .of_dotProduct_mulVec_pos hx.1 fun v hv => ?_⟩
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  simp_rw [dotProduct_mulVec, ← vecMul_vecMul, star_eq_conjTranspose, ← star_mulVec,
    ← dotProduct_mulVec, dotProduct_star_self_pos_iff]
  contrapose hv
  rw [← map_eq_zero_iff (f := (yᴴ * y).mulVecLin) (mulVec_injective_iff_isUnit.mpr h)]; rw [mulVecLin_apply]; rw [← mulVec_mulVec]; rw [hv]; rw [mulVec_zero]

/--
theorem `isStrictlyPositive_iff_posDef` / 定理 `isStrictlyPositive_iff_posDef`

English:
theorem isStrictlyPositive_iff_posDef
  given: [DecidableEq n] {x : Matrix n n 𝕜}
  proof: ⟨fun h => h.nonneg.posSemidef.posDef_iff_isUnit.mpr h.isUnit,
  fun h => h.isUnit.isStrictlyPositive h.posSemidef.nonneg⟩

alias ⟨IsStrictlyPositive.posDef, PosDef.isStrictlyPositive⟩ := isStrictlyPositive_iff_posDef

中文:
定理 isStrictlyPositive_iff_posDef
  条件: [DecidableEq n] {x : 矩阵 n n 𝕜}
  证明: ⟨fun h => h.nonneg.posSemidef.posDef_iff_isUnit.mpr h.isUnit,
  fun h => h.isUnit.isStrictlyPositive h.posSemidef.nonneg⟩

alias ⟨IsStrictlyPositive.posDef, PosDef.isStrictlyPositive⟩ := isStrictlyPositive_iff_posDef

Depends on / 依赖: h.isUnit, h.isUnit.isStrictlyPositive, h.nonneg.posSemidef.posDef_iff_isUnit.mpr, h.posSemidef.nonneg, isStrictlyPositive, isUnit, nonneg, posDef_iff_isUnit, posSemidef
-/
theorem isStrictlyPositive_iff_posDef [DecidableEq n] {x : Matrix n n 𝕜} :
    IsStrictlyPositive x ↔ x.PosDef :=
  ⟨fun h => h.nonneg.posSemidef.posDef_iff_isUnit.mpr h.isUnit,
  fun h => h.isUnit.isStrictlyPositive h.posSemidef.nonneg⟩

alias ⟨IsStrictlyPositive.posDef, PosDef.isStrictlyPositive⟩ := isStrictlyPositive_iff_posDef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosDef.isStrictlyPositive

/--
lemma `PosSemidef.posDef_iff_det_ne_zero` / 引理 `PosSemidef.posDef_iff_det_ne_zero`

English:
lemma PosSemidef.posDef_iff_det_ne_zero
  given: [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef)
  proof: by
  simp [hA.posDef_iff_isUnit, isUnit_iff_isUnit_det]

中文:
引理 PosSemidef.posDef_iff_det_ne_zero
  条件: [DecidableEq n] {A : 矩阵 n n 𝕜} (hA : A.PosSemidef)
  证明: by
  simp [hA.posDef_iff_isUnit, isUnit_iff_isUnit_det]

Depends on / 依赖: hA.posDef_iff_isUnit, isUnit_iff_isUnit_det, posDef_iff_isUnit
-/
lemma PosSemidef.posDef_iff_det_ne_zero [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.PosDef ↔ A.det != 0 := by
  simp [hA.posDef_iff_isUnit, isUnit_iff_isUnit_det]

section kronecker

omit [Fintype n]

variable [Finite n] {m : Type*} [Finite m]

open scoped Kronecker

/--
theorem `PosSemidef.kronecker` / 定理 `PosSemidef.kronecker`

English:
theorem PosSemidef.kronecker
  statement: {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
  proof: by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy.nonneg
  simpa [mul_kronecker_mul, ← conjTranspose_kronecker, star_eq_conjTranspose] 

中文:
定理 PosSemidef.kronecker
  结论: {x : 矩阵 n n 𝕜} {y : 矩阵 m m 𝕜}
  证明: by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy.nonneg
  simpa [mul_kronecker_mul, ← conjTranspose_kronecker, star_eq_conjTranspose] 

Depends on / 依赖: CStarAlgebra, CStarAlgebra.nonneg_iff_eq_star_mul_self.mp, Fintype, Fintype.ofFinite, classical, conjTranspose_kronecker, hx.nonneg, hy.nonneg, mul_kronecker_mul, nonneg, nonneg_iff_eq_star_mul_self, ofFinite, posSemidef_conjTranspose_mul_self, star_eq_conjTranspose
-/
theorem PosSemidef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (x otimesₖ y).PosSemidef := by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy.nonneg
  simpa [mul_kronecker_mul, ← conjTranspose_kronecker, star_eq_conjTranspose] using
    posSemidef_conjTranspose_mul_self _

open Matrix in
/--
theorem `PosDef.kronecker` / 定理 `PosDef.kronecker`

English:
theorem PosDef.kronecker
  statement: {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
  proof: by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
.posDef_iff_isUnit.mpr exact hx.posSemidef.kronecker hy.posSemidef
    hx.isUnit.kronecker hy.isUnit

中文:
定理 PosDef.kronecker
  结论: {x : 矩阵 n n 𝕜} {y : 矩阵 m m 𝕜}
  证明: by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
.posDef_iff_isUnit.mpr exact hx.posSemidef.kronecker hy.posSemidef
    hx.isUnit.kronecker hy.isUnit

Depends on / 依赖: Fintype, Fintype.ofFinite, classical, hx.isUnit.kronecker, hx.posSemidef.kronecker, hy.isUnit, hy.posSemidef, isUnit, kronecker, ofFinite, posDef_iff_isUnit, posDef_iff_isUnit.mpr, posSemidef
-/
theorem PosDef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosDef) (hy : y.PosDef) : (x otimesₖ y).PosDef := by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
.posDef_iff_isUnit.mpr exact hx.posSemidef.kronecker hy.posSemidef
    hx.isUnit.kronecker hy.isUnit

end kronecker

section hadamard

variable {ι : Type*}

/--
theorem `PosSemidef.hadamard` / 定理 `PosSemidef.hadamard`

English:
theorem PosSemidef.hadamard
  statement: {A B : Matrix ι ι 𝕜}
  proof: by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x => ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosSemidef := by
    have hAs := hA.submatrix ((↑) : x.support -> ι)
    have hBs := hB.submatrix ((↑) : x.support -> ι)
    rw [submatrix_hadamard]; rw [posS

中文:
定理 PosSemidef.hadamard
  结论: {A B : 矩阵 ι ι 𝕜}
  证明: by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x => ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosSemidef := by
    have hAs := hA.submatrix ((↑) : x.support -> ι)
    have hBs := hB.submatrix ((↑) : x.support -> ι)
    rw [submatrix_hadamard]; rw [posS

Depends on / 依赖: Finsupp, Finsupp.sum, Matrix, PosSemidef, classical, dotProduct_mulVec_nonneg, hA.isHermitian.hadamard, hA.submatrix, hAs.isHermitian.hadamard, hAs.kronecker, hB.isHermitian, hB.submatrix, hBs.isHermitian, hadamard, isHermitian, kronecker, posSemidef_iff_dotProduct_mulVec, star_dotProduct_hadamard_mulVec_eq_kronecker, submatrix, submatrix_hadamard
-/
theorem PosSemidef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊙ B).PosSemidef := by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x => ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosSemidef := by
    have hAs := hA.submatrix ((↑) : x.support -> ι)
    have hBs := hB.submatrix ((↑) : x.support -> ι)
    rw [submatrix_hadamard]; rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨hAs.isHermitian.hadamard hBs.isHermitian, fun y => ?_⟩
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
    exact (hAs.kronecker hBs).dotProduct_mulVec_nonneg _
  simpa [Finsupp.sum, ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain] using hAB.2 _

/--
theorem `PosDef.hadamard` / 定理 `PosDef.hadamard`

English:
theorem PosDef.hadamard
  statement: {A B : Matrix ι ι 𝕜}
  proof: by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x hx => ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosDef := by
    have hAs : (A.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hA.submatrix Subtype.coe_injective
    have hBs : (B.submatrix (↑)

中文:
定理 PosDef.hadamard
  结论: {A B : 矩阵 ι ι 𝕜}
  证明: by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x hx => ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosDef := by
    have hAs : (A.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hA.submatrix Subtype.coe_injective
    have hBs : (B.submatrix (↑)

Depends on / 依赖: A.submatrix, B.submatrix, Matrix, PosDef, Subtype, Subtype.coe_injective, classical, coe_injective, hA.isHermitian.hadamard, hA.submatrix, hAs.isHermitian.hadamard, hB.isHermitian, hB.submatrix, hBs.isHermitian, hadamard, isHermitian, posDef_iff_dotProduct_mulVec, star_dotProduct_h, submatrix, submatrix_hadamard
-/
theorem PosDef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) : (A ⊙ B).PosDef := by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x hx => ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosDef := by
    have hAs : (A.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hA.submatrix Subtype.coe_injective
    have hBs : (B.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hB.submatrix Subtype.coe_injective
    rw [submatrix_hadamard]; rw [posDef_iff_dotProduct_mulVec]
    refine ⟨hAs.isHermitian.hadamard hBs.isHermitian, fun y hy => ?_⟩
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
exact (hAs.kronecker hBs).dotProduct_mulVec_pos by simpa
  simp_rw [RCLike.star_def, hadamard_apply, Finsupp.sum,
    ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain]
  refine hAB.2 ?_
  simpa [← Finsupp.support_nonempty_iff] using Finsupp.support_nonempty_iff.mpr hx

end hadamard

section tracePositiveLinearMap
variable (n α 𝕜 : Type*) [Fintype n] [Semiring α] [RCLike 𝕜] [Module α 𝕜]

/--
Definition of `tracePositiveLinearMap` / `tracePositiveLinearMap` 的定义

English:
definition tracePositiveLinearMap
  signature: : Matrix n n 𝕜 ->ₚ[α] 𝕜
  body: .mk₀ (traceLinearMap n α 𝕜) fun _ h => h.posSemidef.trace_nonneg

中文:
定义 tracePositiveLinearMap
  签名: : 矩阵 n n 𝕜 ->ₚ[α] 𝕜
  定义体: .mk₀ (traceLinearMap n α 𝕜) fun _ h => h.posSemidef.trace_nonneg

Depends on / 依赖: h.posSemidef.trace_nonneg, posSemidef, traceLinearMap, trace_nonneg
-/
def tracePositiveLinearMap : Matrix n n 𝕜 ->ₚ[α] 𝕜 :=
  .mk₀ (traceLinearMap n α 𝕜) fun _ h => h.posSemidef.trace_nonneg

/--
lemma `toLinearMap_tracePositiveLinearMap` / 引理 `toLinearMap_tracePositiveLinearMap`

English:
lemma toLinearMap_tracePositiveLinearMap
  proof: rfl

中文:
引理 toLinearMap_tracePositiveLinearMap
  证明: rfl
-/
@[simp] lemma toLinearMap_tracePositiveLinearMap :
    (tracePositiveLinearMap n α 𝕜).toLinearMap = traceLinearMap n α 𝕜 := rfl

/--
lemma `tracePositiveLinearMap_apply` / 引理 `tracePositiveLinearMap_apply`

English:
lemma tracePositiveLinearMap_apply
  given: (x)
  statement: tracePositiveLinearMap n α 𝕜 x = trace x
  proof: rfl

中文:
引理 tracePositiveLinearMap_apply
  条件: (x)
  结论: tracePositiveLinearMap n α 𝕜 x = trace x
  证明: rfl
-/
@[simp] lemma tracePositiveLinearMap_apply (x) : tracePositiveLinearMap n α 𝕜 x = trace x := rfl

end tracePositiveLinearMap

set_option backward.privateInPublic true in
/--
Definition of `PosSemidef.matrixPreInnerProductSpace` / `PosSemidef.matrixPreInnerProductSpace` 的定义

English:
abbreviation PosSemidef.matrixPreInnerProductSpace
  signature: {M : Matrix n n 𝕜} (hM : M.PosSemidef)
  body: (y * M * xᴴ).trace
  conj_inner_symm _ _ := by
    simp only [mul_assoc, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose, hM.isHermitian.eq]
.1 re_inner_nonneg x := RCLike.nonneg_iff.mp (hM.mul_mul_conjTranspose_same x).trace_nonneg
  add_left := by sim

中文:
缩写 PosSemidef.matrixPreInnerProductSpace
  签名: {M : 矩阵 n n 𝕜} (hM : M.PosSemidef)
  定义体: (y * M * xᴴ).trace
  conj_inner_symm _ _ := by
    simp only [mul_assoc, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose, hM.isHermitian.eq]
.1 re_inner_nonneg x := RCLike.nonneg_iff.mp (hM.mul_mul_conjTranspose_same x).trace_nonneg
  add_left := by sim
-/
private abbrev PosSemidef.matrixPreInnerProductSpace {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    PreInnerProductSpace.Core 𝕜 (Matrix n n 𝕜) where
  inner x y := (y * M * xᴴ).trace
  conj_inner_symm _ _ := by
    simp only [mul_assoc, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose, hM.isHermitian.eq]
.1 re_inner_nonneg x := RCLike.nonneg_iff.mp (hM.mul_mul_conjTranspose_same x).trace_nonneg
  add_left := by simp [mul_add]
  smul_left := by simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
@[instance_reducible]
/--
Definition of `toMatrixSeminormedAddCommGroup` / `toMatrixSeminormedAddCommGroup` 的定义

English:
definition toMatrixSeminormedAddCommGroup
  signature: (M : Matrix n n 𝕜) (hM : M.PosSemidef)
  body: @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.matrixPreInnerProductSpace

中文:
定义 toMatrixSeminormedAddCommGroup
  签名: (M : 矩阵 n n 𝕜) (hM : M.PosSemidef)
  定义体: @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.matrixPreInnerProductSpace

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.toSeminormedAddCommGroup, hM.matrixPreInnerProductSpace, matrixPreInnerProductSpace, toSeminormedAddCommGroup
-/
noncomputable def toMatrixSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    SeminormedAddCommGroup (Matrix n n 𝕜) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.matrixPreInnerProductSpace

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`:
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
@[instance_reducible]
/--
Definition of `toMatrixNormedAddCommGroup` / `toMatrixNormedAddCommGroup` 的定义

English:
definition toMatrixNormedAddCommGroup
  signature: (M : Matrix n n 𝕜) (hM : M.PosDef)
  body: letI : InnerProductSpace.Core 𝕜 (Matrix n n 𝕜) :=
  { __ := hM.posSemidef.matrixPreInnerProductSpace
    definite x hx := by
      classical
      obtain ⟨y, hy, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
        hM.isStrictlyPositive
      simp +instances only at hx
      rw [←

中文:
定义 toMatrixNormedAddCommGroup
  签名: (M : 矩阵 n n 𝕜) (hM : M.PosDef)
  定义体: letI : InnerProductSpace.Core 𝕜 (Matrix n n 𝕜) :=
  { __ := hM.posSemidef.matrixPreInnerProductSpace
    definite x hx := by
      classical
      obtain ⟨y, hy, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
        hM.isStrictlyPositive
      simp +instances only at hx
      rw [←

Depends on / 依赖: CStarAlgebra, CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp, InnerProductSpace, InnerProductSpace.Core, Matrix, classical, conjTranspose_conjTranspose, conjTranspose_mul, definite, hM.isStrictlyPositive, hM.posSemidef.matrixPreInnerProductSpace, instances, isStrictlyPositive, isStrictlyPositive_iff_eq_star_mul_self, matrixPreInnerProductSpace, mul_assoc, posSemidef, star_eq_conjTranspose, trace_conjTranspose_mul_self_eq_zero_iff
-/
noncomputable def toMatrixNormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (Matrix n n 𝕜) :=
  letI : InnerProductSpace.Core 𝕜 (Matrix n n 𝕜) :=
  { __ := hM.posSemidef.matrixPreInnerProductSpace
    definite x hx := by
      classical
      obtain ⟨y, hy, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
        hM.isStrictlyPositive
      simp +instances only at hx
      rw [← mul_assoc]; rw [← conjTranspose_conjTranspose x]; rw [star_eq_conjTranspose]; rw [← conjTranspose_mul]; rw [conjTranspose_conjTranspose]; rw [mul_assoc]; rw [trace_conjTranspose_mul_self_eq_zero_iff] at hx
      lift y to (Matrix n n 𝕜)ˣ using hy
      simpa [← mul_assoc] using congr(y⁻¹ * $hx) }
  this.toNormedAddCommGroup

/-- A positive semi-definite matrix `M` induces an inner product on `Matrix n n 𝕜`:
`⟪x, y⟫ = (y * M * xᴴ).trace`. -/
@[instance_reducible]
/--
Definition of `toMatrixInnerProductSpace` / `toMatrixInnerProductSpace` 的定义

English:
definition toMatrixInnerProductSpace
  signature: (M : Matrix n n 𝕜) (hM : M.PosSemidef)
  body: M.toMatrixSeminormedAddCommGroup hM
    InnerProductSpace 𝕜 (Matrix n n 𝕜) :=
  InnerProductSpace.ofCore _

中文:
定义 toMatrixInnerProductSpace
  签名: (M : 矩阵 n n 𝕜) (hM : M.PosSemidef)
  定义体: M.toMatrixSeminormedAddCommGroup hM
    InnerProductSpace 𝕜 (Matrix n n 𝕜) :=
  InnerProductSpace.ofCore _

Depends on / 依赖: M.toMatrixSeminormedAddCommGroup, toMatrixSeminormedAddCommGroup
-/
def toMatrixInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    letI : SeminormedAddCommGroup (Matrix n n 𝕜) := M.toMatrixSeminormedAddCommGroup hM
    InnerProductSpace 𝕜 (Matrix n n 𝕜) :=
  InnerProductSpace.ofCore _

open scoped Norms.L2Operator in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `instIsometricContinuousFunctionalCalculus` / 实例 `instIsometricContinuousFunctionalCalculus`

English:
instance instIsometricContinuousFunctionalCalculus
  signature: [DecidableEq n]
  body: by
    rw [← isHermitian_iff_isSelfAdjoint] at hA
    rw [IsHermitian.cfcHom_eq_cfcAux hA]; rw [AddMonoidHomClass.isometry_iff_norm]
    intro f
    simp only [IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary

中文:
实例 instIsometricContinuousFunctionalCalculus
  签名: [DecidableEq n]
  定义体: by
    rw [← isHermitian_iff_isSelfAdjoint] at hA
    rw [IsHermitian.cfcHom_eq_cfcAux hA]; rw [AddMonoidHomClass.isometry_iff_norm]
    intro f
    simp only [IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_iff_norm, CStarRing, CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary, ContinuousMap, ContinuousMap.norm_eq_norm_coeFn, Fintype, Function, Function.Surjective, IsHermitian, IsHermitian.cfcAux_apply, IsHermitian.cfcHom_eq_cfcAux, Surjective, Unitary, Unitary.coe_star, Unitary.conjStarAlgAut_apply, algebraMap_isometry, cfcAux_apply, cfcHom_eq_cfcAux
-/
instance instIsometricContinuousFunctionalCalculus [DecidableEq n] :
    IsometricContinuousFunctionalCalculus Real (Matrix n n 𝕜) IsSelfAdjoint where
  isometric A hA := by
    rw [← isHermitian_iff_isSelfAdjoint] at hA
    rw [IsHermitian.cfcHom_eq_cfcAux hA]; rw [AddMonoidHomClass.isometry_iff_norm]
    intro f
    simp only [IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
    rw [((algebraMap_isometry Real 𝕜).postcomp_pi).norm_map_of_map_zero (by ext; simp)]
    let : Fintype (spectrum Real A) := .ofFinite _
    rw [ContinuousMap.norm_eq_norm_coeFn]
    refine Function.Surjective.pi_norm_comp ?_ _
    rw [← Function.Surjective.of_comp_iff'
      (Equiv.setCongr hA.spectrum_real_eq_range_eigenvalues).bijective]
    exact Set.codRestrict_range_surjective hA.eigenvalues

scoped[Matrix.Norms.L2Operator] attribute [instance]
  Matrix.instIsometricContinuousFunctionalCalculus

end Matrix
