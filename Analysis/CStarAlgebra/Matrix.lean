/-
Copyright (c) 2022 Hans Parshall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hans Parshall
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.UniformSpace.Matrix

/-!
# Analytic properties of the `star` operation on matrices

This transports the operator norm on `EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m` to
`Matrix m n 𝕜`. See the file `Mathlib/Analysis/Matrix.lean` for many other matrix norms.

## Main definitions

* `Matrix.instNormedRingL2Op`: the (necessarily unique) normed ring structure on `Matrix n n 𝕜`
  which ensure it is a `CStarRing` in `Matrix.instCStarRing`. This is a scoped instance in the
  namespace `Matrix.Norms.L2Operator` in order to avoid choosing a global norm for `Matrix`.

## Main statements

* `entry_norm_bound_of_unitary`: the entries of a unitary matrix are uniformly bound by `1`.

## Implementation details

We take care to ensure the topology and uniformity induced by `Matrix.instMetricSpaceL2Op`
coincide with the existing topology and uniformity on matrices.

-/

@[expose] public section

open WithLp
open scoped Matrix

variable {𝕜 m n l E : Type*}

section EntrywiseSupNorm

variable [RCLike 𝕜] [Fintype n] [DecidableEq n]

/--
theorem `entry_norm_bound_of_unitary` / 定理 `entry_norm_bound_of_unitary`

English:
theorem entry_norm_bound_of_unitary
  statement: {U : Matrix n n 𝕜} (hU : U in Matrix.unitaryGroup n 𝕜)
  proof: by
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : ‖U i j‖ ^ 2 <= ∑ x, ‖U i x‖ ^ 2 := by
    apply Multiset.single_le_sum
    · intro x h_x
      rw [Multiset.mem_map] at h_x
      obtain ⟨a, h_a⟩ := h_x
      rw [← h_a.2]
      apply sq_nonneg
    · rw [Multis

中文:
定理 entry_norm_bound_of_unitary
  结论: {U : Matrix n n 𝕜} (hU : U in Matrix.unitaryGroup n 𝕜)
  证明: by
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : ‖U i j‖ ^ 2 <= ∑ x, ‖U i x‖ ^ 2 := by
    apply Multiset.single_le_sum
    · intro x h_x
      rw [Multiset.mem_map] at h_x
      obtain ⟨a, h_a⟩ := h_x
      rw [← h_a.2]
      apply sq_nonneg
    · rw [Multis
-/
theorem entry_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U in Matrix.unitaryGroup n 𝕜)
    (i j : n) : ‖U i j‖ <= 1 := by
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : ‖U i j‖ ^ 2 <= ∑ x, ‖U i x‖ ^ 2 := by
    apply Multiset.single_le_sum
    · intro x h_x
      rw [Multiset.mem_map] at h_x
      obtain ⟨a, h_a⟩ := h_x
      rw [← h_a.2]
      apply sq_nonneg
    · rw [Multiset.mem_map]
      use j
      simp only [Finset.mem_univ_val, and_self_iff]
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ
  have diag_eq_norm_sum : (U * Uᴴ) i i = (∑ x : n, ‖U i x‖ ^ 2 : Real) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply, RCLike.mul_conj]
    norm_cast
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ, real part
  have re_diag_eq_norm_sum : RCLike.re ((U * Uᴴ) i i) = ∑ x : n, ‖U i x‖ ^ 2 := by
    rw [RCLike.ext_iff] at diag_eq_norm_sum
    rw [diag_eq_norm_sum.1]
    norm_cast
  -- Since U is unitary, the diagonal entries of U * Uᴴ are all 1
  have mul_eq_one : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  have diag_eq_one : RCLike.re ((U * Uᴴ) i i) = 1 := by
    simp only [mul_eq_one, Matrix.one_apply_eq, RCLike.one_re]
  -- Putting it all together
  rw [← sq_le_one_iff₀ (norm_nonneg (U i j))]; rw [← diag_eq_one]; rw [re_diag_eq_norm_sum]
  exact norm_sum

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Elementwise in
/--
theorem `entrywise_sup_norm_bound_of_unitary` / 定理 `entrywise_sup_norm_bound_of_unitary`

English:
theorem entrywise_sup_norm_bound_of_unitary
  given: {U : Matrix n n 𝕜} (hU : U in Matrix.unitaryGroup n 𝕜)
  proof: by
  simp_rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intros
  exact entry_norm_bound_of_unitary hU _ _

中文:
定理 entrywise_sup_norm_bound_of_unitary
  条件: {U : Matrix n n 𝕜} (hU : U in Matrix.unitaryGroup n 𝕜)
  证明: by
  simp_rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intros
  exact entry_norm_bound_of_unitary hU _ _

Depends on / 依赖: entry_norm_bound_of_unitary, intros, pi_norm_le_iff_of_nonneg, simp_rw, zero_le_one
-/
theorem entrywise_sup_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U in Matrix.unitaryGroup n 𝕜) :
    ‖U‖ <= 1 := by
  simp_rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intros
  exact entry_norm_bound_of_unitary hU _ _

end EntrywiseSupNorm

noncomputable section L2OpNorm

namespace Matrix
open LinearMap

variable [RCLike 𝕜]
variable [Fintype m] [Fintype n] [DecidableEq n] [Fintype l] [DecidableEq l]

/--
Definition of `toEuclideanCLM` / `toEuclideanCLM` 的定义

English:
definition toEuclideanCLM
  signature: :
  body: .symm.trans toMatrixOrthonormal (EuclideanSpace.basisFun n 𝕜)
    { toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := adjoint_toContinuousLinearMap }

中文:
定义 toEuclideanCLM
  签名: :
  定义体: .symm.trans toMatrixOrthonormal (EuclideanSpace.basisFun n 𝕜)
    { toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := adjoint_toContinuousLinearMap }

Depends on / 依赖: EuclideanSpace, EuclideanSpace.basisFun, adjoint_toContinuousLinearMap, basisFun, map_mul, map_star, symm.trans, toContinuousLinearMap, toMatrixOrthonormal
-/
def toEuclideanCLM :
    Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n ->L[𝕜] EuclideanSpace 𝕜 n) :=
.symm.trans toMatrixOrthonormal (EuclideanSpace.basisFun n 𝕜)
    { toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := adjoint_toContinuousLinearMap }

/--
lemma `coe_toEuclideanCLM_eq_toEuclideanLin` / 引理 `coe_toEuclideanCLM_eq_toEuclideanLin`

English:
lemma coe_toEuclideanCLM_eq_toEuclideanLin
  given: (A : Matrix n n 𝕜)
  proof: rfl

@[simp]

中文:
引理 coe_toEuclideanCLM_eq_toEuclideanLin
  条件: (A : Matrix n n 𝕜)
  证明: rfl

@[simp]

Depends on / 依赖: toEuclideanLin
-/
lemma coe_toEuclideanCLM_eq_toEuclideanLin (A : Matrix n n 𝕜) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) A : _ ->ₗ[𝕜] _) = toEuclideanLin A :=
  rfl

@[simp]
/--
lemma `toEuclideanCLM_toLp` / 引理 `toEuclideanCLM_toLp`

English:
lemma toEuclideanCLM_toLp
  given: (A : Matrix n n 𝕜) (x : n -> 𝕜)
  proof: rfl

@[simp]

中文:
引理 toEuclideanCLM_toLp
  条件: (A : Matrix n n 𝕜) (x : n -> 𝕜)
  证明: rfl

@[simp]
-/
lemma toEuclideanCLM_toLp (A : Matrix n n 𝕜) (x : n -> 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) A (toLp _ x) = toLp _ (A *ᵥ x) := rfl

@[simp]
/--
lemma `ofLp_toEuclideanCLM` / 引理 `ofLp_toEuclideanCLM`

English:
lemma ofLp_toEuclideanCLM
  given: (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n)
  proof: rfl

中文:
引理 ofLp_toEuclideanCLM
  条件: (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n)
  证明: rfl
-/
lemma ofLp_toEuclideanCLM (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ofLp (toEuclideanCLM (n := n) (𝕜 := 𝕜) A x) = A *ᵥ ofLp x := rfl

open scoped RealInnerProductSpace in
/--
lemma `inner_toEuclideanCLM` / 引理 `inner_toEuclideanCLM`

English:
lemma inner_toEuclideanCLM
  given: (A : Matrix n n Real) (x y : EuclideanSpace Real n)
  proof: by
  simp only [toEuclideanCLM, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearMap.coe_toContinuousLinearMap_symm, StarAlgEquiv.trans_apply,
    LinearMap.toMatrixOrthonormal_symm_apply, LinearMap.toMatrix_symm, StarAlgEquiv.coe_mk,
    StarRi

中文:
引理 inner_toEuclideanCLM
  条件: (A : Matrix n n 实数) (x y : EuclideanSpace 实数 n)
  证明: by
  simp only [toEuclideanCLM, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearMap.coe_toContinuousLinearMap_symm, StarAlgEquiv.trans_apply,
    LinearMap.toMatrixOrthonormal_symm_apply, LinearMap.toMatrix_symm, StarAlgEquiv.coe_mk,
    StarRi

Depends on / 依赖: AddHom, AddHom.toFun_eq_coe, Equiv.coe_fn_mk, EuclideanSpace, EuclideanSpace.basisFun_repr, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm, LinearMap, LinearMap.coe_toAddHom, LinearMap.coe_toContinuousLinearMap, LinearMap.coe_toContinuousLinearMap_symm, LinearMap.toMatrixOrthonormal_symm_apply, LinearMap.toMatrix_symm, OrthonormalBasis, OrthonormalBasis.coe_toBasis_repr_apply, RingEquiv, RingEquiv.coe_mk, StarAlgEquiv, StarAlgEquiv.coe_mk
-/
lemma inner_toEuclideanCLM (A : Matrix n n Real) (x y : EuclideanSpace Real n) :
    ⟪x, toEuclideanCLM (𝕜 := Real) A y⟫ = x ⬝ᵥ A *ᵥ y := by
  simp only [toEuclideanCLM, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearMap.coe_toContinuousLinearMap_symm, StarAlgEquiv.trans_apply,
    LinearMap.toMatrixOrthonormal_symm_apply, LinearMap.toMatrix_symm, StarAlgEquiv.coe_mk,
    StarRingEquiv.coe_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, LinearMap.coe_toContinuousLinearMap',
    toLin_apply, mulVec_eq_sum, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply,
    smul_eq_mul, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    ofLp_sum, ofLp_smul, PiLp.ofLp_single, RCLike.inner_apply, conj_trivial, dotProduct]
  congr with i
  rw [mul_comm (x.ofLp i)]
  simp [Pi.single_apply]

/-- An auxiliary definition used only to construct the true `NormedAddCommGroup` (and `Metric`)
structure provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedAddCommGroupL2Op`. -/
@[instance_reducible]
/--
Definition of `l2OpNormedAddCommGroupAux` / `l2OpNormedAddCommGroupAux` 的定义

English:
definition l2OpNormedAddCommGroupAux
  signature: : NormedAddCommGroup (Matrix m n 𝕜)
  body: @NormedAddCommGroup.induced ((Matrix m n 𝕜) ≃ₗ[𝕜] (EuclideanSpace 𝕜 n ->L[𝕜] EuclideanSpace 𝕜 m)) _
_ _ _ ContinuousLinearMap.toNormedAddCommGroup.toNormedAddGroup _ _
    (toEuclideanLin.trans toContinuousLinearMap).injective

中文:
定义 l2OpNormedAddCommGroupAux
  签名: : NormedAddCommGroup (Matrix m n 𝕜)
  定义体: @NormedAddCommGroup.induced ((Matrix m n 𝕜) ≃ₗ[𝕜] (EuclideanSpace 𝕜 n ->L[𝕜] EuclideanSpace 𝕜 m)) _
_ _ _ ContinuousLinearMap.toNormedAddCommGroup.toNormedAddGroup _ _
    (toEuclideanLin.trans toContinuousLinearMap).injective

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.toNormedAddCommGroup.toNormedAddGroup, EuclideanSpace, Matrix, NormedAddCommGroup, NormedAddCommGroup.induced, induced, injective, toContinuousLinearMap, toEuclideanLin, toEuclideanLin.trans, toNormedAddCommGroup, toNormedAddGroup
-/
def l2OpNormedAddCommGroupAux : NormedAddCommGroup (Matrix m n 𝕜) :=
  @NormedAddCommGroup.induced ((Matrix m n 𝕜) ≃ₗ[𝕜] (EuclideanSpace 𝕜 n ->L[𝕜] EuclideanSpace 𝕜 m)) _
_ _ _ ContinuousLinearMap.toNormedAddCommGroup.toNormedAddGroup _ _
    (toEuclideanLin.trans toContinuousLinearMap).injective

/-- An auxiliary definition used only to construct the true `NormedRing` (and `Metric`) structure
provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedRingL2Op`. -/
@[instance_reducible]
/--
Definition of `l2OpNormedRingAux` / `l2OpNormedRingAux` 的定义

English:
definition l2OpNormedRingAux
  signature: : NormedRing (Matrix n n 𝕜)
  body: @NormedRing.induced ((Matrix n n 𝕜) ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n ->L[𝕜] EuclideanSpace 𝕜 n)) _
    _ _ _ ContinuousLinearMap.toNormedRing _ _ toEuclideanCLM.injective

中文:
定义 l2OpNormedRingAux
  签名: : NormedRing (Matrix n n 𝕜)
  定义体: @NormedRing.induced ((Matrix n n 𝕜) ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n ->L[𝕜] EuclideanSpace 𝕜 n)) _
    _ _ _ ContinuousLinearMap.toNormedRing _ _ toEuclideanCLM.injective

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.toNormedRing, EuclideanSpace, Matrix, NormedRing, NormedRing.induced, induced, injective, toEuclideanCLM, toEuclideanCLM.injective, toNormedRing
-/
def l2OpNormedRingAux : NormedRing (Matrix n n 𝕜) :=
  @NormedRing.induced ((Matrix n n 𝕜) ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n ->L[𝕜] EuclideanSpace 𝕜 n)) _
    _ _ _ ContinuousLinearMap.toNormedRing _ _ toEuclideanCLM.injective

open Bornology Filter
open scoped Topology Uniformity

/-- The metric on `Matrix m n 𝕜` arising from the operator norm given by the identification with
(continuous) linear maps of `EuclideanSpace`. -/
@[instance_reducible]
/--
Definition of `instL2OpMetricSpace` / `instL2OpMetricSpace` 的定义

English:
definition instL2OpMetricSpace
  signature: : MetricSpace (Matrix m n 𝕜)
  body: by
  /- We first replace the topology so that we can automatically replace the uniformity using
  `IsUniformAddGroup.toUniformSpace_eq`. -/
  letI normed_add_comm_group : NormedAddCommGroup (Matrix m n 𝕜) :=
    { l2OpNormedAddCommGroupAux.replaceTopology <|
        (toEuclideanLin (𝕜 := 𝕜) (m := m)

中文:
定义 instL2OpMetricSpace
  签名: : MetricSpace (Matrix m n 𝕜)
  定义体: by
  /- We first replace the topology so that we can automatically replace the uniformity using
  `IsUniformAddGroup.toUniformSpace_eq`. -/
  letI normed_add_comm_group : NormedAddCommGroup (Matrix m n 𝕜) :=
    { l2OpNormedAddCommGroupAux.replaceTopology <|
        (toEuclideanLin (𝕜 := 𝕜) (m := m)
-/
def instL2OpMetricSpace : MetricSpace (Matrix m n 𝕜) := by
  /- We first replace the topology so that we can automatically replace the uniformity using
  `IsUniformAddGroup.toUniformSpace_eq`. -/
  letI normed_add_comm_group : NormedAddCommGroup (Matrix m n 𝕜) :=
    { l2OpNormedAddCommGroupAux.replaceTopology <|
        (toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap
.toContinuousLinearEquiv.toHomeomorph.isInducing.eq_induced with
      norm := l2OpNormedAddCommGroupAux.norm
      dist_eq := l2OpNormedAddCommGroupAux.dist_eq }
exact normed_add_comm_group.replaceUniformity by
    congr
    rw [← @IsUniformAddGroup.rightUniformSpace_eq _ (Matrix.instUniformSpace m n 𝕜) _ _]
    rw [@IsUniformAddGroup.rightUniformSpace_eq _ PseudoEMetricSpace.toUniformSpace _ _]

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpMetricSpace

open scoped Matrix.Norms.L2Operator

/-- The norm structure on `Matrix m n 𝕜` arising from the operator norm given by the identification
with (continuous) linear maps of `EuclideanSpace`. -/
@[instance_reducible]
/--
Definition of `instL2OpNormedAddCommGroup` / `instL2OpNormedAddCommGroup` 的定义

English:
definition instL2OpNormedAddCommGroup
  signature: : NormedAddCommGroup (Matrix m n 𝕜) where
  body: l2OpNormedAddCommGroupAux.norm
  dist_eq := l2OpNormedAddCommGroupAux.dist_eq

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedAddCommGroup

中文:
定义 instL2OpNormedAddCommGroup
  签名: : NormedAddCommGroup (Matrix m n 𝕜) where
  定义体: l2OpNormedAddCommGroupAux.norm
  dist_eq := l2OpNormedAddCommGroupAux.dist_eq

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedAddCommGroup

Depends on / 依赖: l2OpNormedAddCommGroupAux, l2OpNormedAddCommGroupAux.norm
-/
def instL2OpNormedAddCommGroup : NormedAddCommGroup (Matrix m n 𝕜) where
  norm := l2OpNormedAddCommGroupAux.norm
  dist_eq := l2OpNormedAddCommGroupAux.dist_eq

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedAddCommGroup

/--
lemma `l2_opNorm_def` / 引理 `l2_opNorm_def`

English:
lemma l2_opNorm_def
  given: (A : Matrix m n 𝕜)
  proof: rfl

中文:
引理 l2_opNorm_def
  条件: (A : Matrix m n 𝕜)
  证明: rfl

Depends on / 依赖: toContinuousLinearMap
-/
lemma l2_opNorm_def (A : Matrix m n 𝕜) :
    ‖A‖ = ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A‖ := rfl

/--
lemma `l2_opNNNorm_def` / 引理 `l2_opNNNorm_def`

English:
lemma l2_opNNNorm_def
  given: (A : Matrix m n 𝕜)
  proof: rfl

中文:
引理 l2_opNNNorm_def
  条件: (A : Matrix m n 𝕜)
  证明: rfl

Depends on / 依赖: toContinuousLinearMap
-/
lemma l2_opNNNorm_def (A : Matrix m n 𝕜) :
    ‖A‖₊ = ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A‖₊ := rfl

/--
lemma `l2_opNorm_conjTranspose` / 引理 `l2_opNorm_conjTranspose`

English:
lemma l2_opNorm_conjTranspose
  given: [DecidableEq m] (A : Matrix m n 𝕜)
  statement: ‖Aᴴ‖ = ‖A‖
  proof: by
  rw [l2_opNorm_def]; rw [toEuclideanLin_eq_toLin_orthonormal]; rw [LinearEquiv.trans_apply]; rw [toLin_conjTranspose]; rw [adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

中文:
引理 l2_opNorm_conjTranspose
  条件: [DecidableEq m] (A : Matrix m n 𝕜)
  结论: ‖Aᴴ‖ = ‖A‖
  证明: by
  rw [l2_opNorm_def]; rw [toEuclideanLin_eq_toLin_orthonormal]; rw [LinearEquiv.trans_apply]; rw [toLin_conjTranspose]; rw [adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.adjoint.norm_map, LinearEquiv, LinearEquiv.trans_apply, adjoint, adjoint_toContinuousLinearMap, l2_opNorm_def, norm_map, toEuclideanLin_eq_toLin_orthonormal, toLin_conjTranspose, trans_apply
-/
lemma l2_opNorm_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) : ‖Aᴴ‖ = ‖A‖ := by
  rw [l2_opNorm_def]; rw [toEuclideanLin_eq_toLin_orthonormal]; rw [LinearEquiv.trans_apply]; rw [toLin_conjTranspose]; rw [adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

/--
lemma `l2_opNNNorm_conjTranspose` / 引理 `l2_opNNNorm_conjTranspose`

English:
lemma l2_opNNNorm_conjTranspose
  given: [DecidableEq m] (A : Matrix m n 𝕜)
  statement: ‖Aᴴ‖₊ = ‖A‖₊
  proof: Subtype.ext l2_opNorm_conjTranspose _

中文:
引理 l2_opNNNorm_conjTranspose
  条件: [DecidableEq m] (A : Matrix m n 𝕜)
  结论: ‖Aᴴ‖₊ = ‖A‖₊
  证明: Subtype.ext l2_opNorm_conjTranspose _

Depends on / 依赖: DenselyNormedField, DenselyNormedField.toNontriviallyNormedField, Subtype, Subtype.ext, l2_opNorm_conjTranspose, toNontriviallyNormedField
-/
lemma l2_opNNNorm_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) : ‖Aᴴ‖₊ = ‖A‖₊ :=
Subtype.ext l2_opNorm_conjTranspose _

/--
lemma `l2_opNorm_conjTranspose_mul_self` / 引理 `l2_opNorm_conjTranspose_mul_self`

English:
lemma l2_opNorm_conjTranspose_mul_self
  given: (A : Matrix m n 𝕜)
  statement: ‖Aᴴ * A‖ = ‖A‖ * ‖A‖
  proof: by
  classical
  rw [l2_opNorm_def]; rw [toEuclideanLin_eq_toLin_orthonormal]; rw [LinearEquiv.trans_apply]; rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun m 𝕜).toBasis)]; rw [toLin_conjTranspose]
  exact ContinuousLinearMap.norm_adjoint_comp_self _

中文:
引理 l2_opNorm_conjTranspose_mul_self
  条件: (A : Matrix m n 𝕜)
  结论: ‖Aᴴ * A‖ = ‖A‖ * ‖A‖
  证明: by
  classical
  rw [l2_opNorm_def]; rw [toEuclideanLin_eq_toLin_orthonormal]; rw [LinearEquiv.trans_apply]; rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun m 𝕜).toBasis)]; rw [toLin_conjTranspose]
  exact ContinuousLinearMap.norm_adjoint_comp_self _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_adjoint_comp_self, EuclideanSpace, EuclideanSpace.basisFun, LinearEquiv, LinearEquiv.trans_apply, Matrix, Matrix.toLin_mul, NormedDivisionRing, NormedField, NormedField.toNormedDivisionRing, basisFun, classical, l2_opNorm_def, norm_adjoint_comp_self, toBasis, toEuclideanLin_eq_toLin_orthonormal, toLin_conjTranspose, toLin_mul, toNormedDivisionRing
-/
lemma l2_opNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) : ‖Aᴴ * A‖ = ‖A‖ * ‖A‖ := by
  classical
  rw [l2_opNorm_def]; rw [toEuclideanLin_eq_toLin_orthonormal]; rw [LinearEquiv.trans_apply]; rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun m 𝕜).toBasis)]; rw [toLin_conjTranspose]
  exact ContinuousLinearMap.norm_adjoint_comp_self _

/--
lemma `l2_opNNNorm_conjTranspose_mul_self` / 引理 `l2_opNNNorm_conjTranspose_mul_self`

English:
lemma l2_opNNNorm_conjTranspose_mul_self
  given: (A : Matrix m n 𝕜)
  statement: ‖Aᴴ * A‖₊ = ‖A‖₊ * ‖A‖₊
  proof: Subtype.ext l2_opNorm_conjTranspose_mul_self _

中文:
引理 l2_opNNNorm_conjTranspose_mul_self
  条件: (A : Matrix m n 𝕜)
  结论: ‖Aᴴ * A‖₊ = ‖A‖₊ * ‖A‖₊
  证明: Subtype.ext l2_opNorm_conjTranspose_mul_self _

Depends on / 依赖: NormedCommRing, NormedField, NormedField.toNormedCommRing, Subtype, Subtype.ext, l2_opNorm_conjTranspose_mul_self, toNormedCommRing
-/
lemma l2_opNNNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) : ‖Aᴴ * A‖₊ = ‖A‖₊ * ‖A‖₊ :=
Subtype.ext l2_opNorm_conjTranspose_mul_self _

-- note: with only a type ascription in the left-hand side, Lean picks the wrong norm.
/--
lemma `l2_opNorm_mulVec` / 引理 `l2_opNorm_mulVec`

English:
lemma l2_opNorm_mulVec
  given: (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n)
  proof: .le_opNorm x .trans toContinuousLinearMap A toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜)

中文:
引理 l2_opNorm_mulVec
  条件: (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n)
  证明: .le_opNorm x .trans toContinuousLinearMap A toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜)

Depends on / 依赖: le_opNorm, toContinuousLinearMap, toEuclideanLin
-/
lemma l2_opNorm_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
‖(EuclideanSpace.equiv m 𝕜).symm A *ᵥ x‖ <= ‖A‖ * ‖x‖ :=
.le_opNorm x .trans toContinuousLinearMap A toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜)

/--
lemma `l2_opNNNorm_mulVec` / 引理 `l2_opNNNorm_mulVec`

English:
lemma l2_opNNNorm_mulVec
  given: (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n)
  proof: A.l2_opNorm_mulVec x

中文:
引理 l2_opNNNorm_mulVec
  条件: (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n)
  证明: A.l2_opNorm_mulVec x

Depends on / 依赖: A.l2_opNorm_mulVec, l2_opNorm_mulVec
-/
lemma l2_opNNNorm_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
‖(EuclideanSpace.equiv m 𝕜).symm A *ᵥ x‖₊ <= ‖A‖₊ * ‖x‖₊ :=
  A.l2_opNorm_mulVec x

/--
lemma `l2_opNorm_mul` / 引理 `l2_opNorm_mul`

English:
lemma l2_opNorm_mul
  given: (A : Matrix m n 𝕜) (B : Matrix n l 𝕜)
  proof: by
  simp only [l2_opNorm_def]
  have := (toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) A
.opNorm_comp_le (toEuclideanLin (n := l) (m := n) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) B
  convert! this
  ext1 x
  exact congr(toLp 2 ($(Matrix.toLin'_mul A B) x))

中文:
引理 l2_opNorm_mul
  条件: (A : Matrix m n 𝕜) (B : Matrix n l 𝕜)
  证明: by
  simp only [l2_opNorm_def]
  have := (toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) A
.opNorm_comp_le (toEuclideanLin (n := l) (m := n) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) B
  convert! this
  ext1 x
  exact congr(toLp 2 ($(Matrix.toLin'_mul A B) x))

Depends on / 依赖: Matrix, Matrix.toLin, _mul, convert, l2_opNorm_def, opNorm_comp_le, toContinuousLinearMap, toEuclideanLin
-/
lemma l2_opNorm_mul (A : Matrix m n 𝕜) (B : Matrix n l 𝕜) :
    ‖A * B‖ <= ‖A‖ * ‖B‖ := by
  simp only [l2_opNorm_def]
  have := (toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) A
.opNorm_comp_le (toEuclideanLin (n := l) (m := n) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) B
  convert! this
  ext1 x
  exact congr(toLp 2 ($(Matrix.toLin'_mul A B) x))

/--
lemma `l2_opNNNorm_mul` / 引理 `l2_opNNNorm_mul`

English:
lemma l2_opNNNorm_mul
  given: (A : Matrix m n 𝕜) (B : Matrix n l 𝕜)
  statement: ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊
  proof: l2_opNorm_mul A B

中文:
引理 l2_opNNNorm_mul
  条件: (A : Matrix m n 𝕜) (B : Matrix n l 𝕜)
  结论: ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊
  证明: l2_opNorm_mul A B

Depends on / 依赖: l2_opNorm_mul
-/
lemma l2_opNNNorm_mul (A : Matrix m n 𝕜) (B : Matrix n l 𝕜) : ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊ :=
  l2_opNorm_mul A B

/--
lemma `l2_opNorm_toEuclideanCLM` / 引理 `l2_opNorm_toEuclideanCLM`

English:
lemma l2_opNorm_toEuclideanCLM
  given: (A : Matrix n n 𝕜)
  proof: rfl

@[simp]

中文:
引理 l2_opNorm_toEuclideanCLM
  条件: (A : Matrix n n 𝕜)
  证明: rfl

@[simp]
-/
lemma l2_opNorm_toEuclideanCLM (A : Matrix n n 𝕜) :
    ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖ = ‖A‖ := rfl

@[simp]
/--
lemma `l2_opNorm_diagonal` / 引理 `l2_opNorm_diagonal`

English:
lemma l2_opNorm_diagonal
  given: (v : n -> 𝕜)
  statement: ‖(diagonal v : Matrix n n 𝕜)‖ = ‖v‖
  proof: by
  set T := toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal v)
  rw [← l2_opNorm_toEuclideanCLM]
  refine le_antisymm ?_ ?_
  · refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    simp only [(T x).norm_sq_eq, ofLp_toEuclideanCLM, mulVec_

中文:
引理 l2_opNorm_diagonal
  条件: (v : n -> 𝕜)
  结论: ‖(diagonal v : Matrix n n 𝕜)‖ = ‖v‖
  证明: by
  set T := toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal v)
  rw [← l2_opNorm_toEuclideanCLM]
  refine le_antisymm ?_ ?_
  · refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    simp only [(T x).norm_sq_eq, ofLp_toEuclideanCLM, mulVec_

Depends on / 依赖: EuclideanSpace, EuclideanSpace.norm_sq_eq, Finset, Finset.mul_sum, Finset.sum_le_sum, T.opNorm_le_bound, diagonal, l2_opNorm_toEuclideanCLM, le_antisymm, mulVec_diagonal, mul_pow, mul_sum, norm_le_pi_norm, norm_mul, norm_nonneg, norm_sq_eq, ofLp_toEuclideanCLM, opNorm_le_bound, pi_norm_le_iff_of_nonneg, sum_le_sum
-/
lemma l2_opNorm_diagonal (v : n -> 𝕜) : ‖(diagonal v : Matrix n n 𝕜)‖ = ‖v‖ := by
  set T := toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal v)
  rw [← l2_opNorm_toEuclideanCLM]
  refine le_antisymm ?_ ?_
  · refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    simp only [(T x).norm_sq_eq, ofLp_toEuclideanCLM, mulVec_diagonal, norm_mul, T]
    calc _ <= _ := Finset.sum_le_sum fun i _ => by grw [mul_pow, norm_le_pi_norm v i]
      _ = _ := by simp [mul_pow, EuclideanSpace.norm_sq_eq x, Finset.mul_sum]
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg T)).mpr fun i => ?_
    calc _ = ‖T (toLp 2 (Pi.single i (1 : 𝕜)))‖ := by
          rw [toEuclideanCLM_toLp (diagonal v) (Pi.single i (1 : 𝕜))]
          simp
      _ <= _ := by grw [T.le_opNorm]; simp

@[simp]
/--
lemma `l2_opNNNorm_diagonal` / 引理 `l2_opNNNorm_diagonal`

English:
lemma l2_opNNNorm_diagonal
  given: (v : n -> 𝕜)
  statement: ‖(diagonal v : Matrix n n 𝕜)‖₊ = ‖v‖₊
  proof: Subtype.ext l2_opNorm_diagonal (n := n) (𝕜 := 𝕜) v

中文:
引理 l2_opNNNorm_diagonal
  条件: (v : n -> 𝕜)
  结论: ‖(diagonal v : Matrix n n 𝕜)‖₊ = ‖v‖₊
  证明: Subtype.ext l2_opNorm_diagonal (n := n) (𝕜 := 𝕜) v

Depends on / 依赖: Subtype, Subtype.ext, l2_opNorm_diagonal
-/
lemma l2_opNNNorm_diagonal (v : n -> 𝕜) : ‖(diagonal v : Matrix n n 𝕜)‖₊ = ‖v‖₊ :=
Subtype.ext l2_opNorm_diagonal (n := n) (𝕜 := 𝕜) v

/-- The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`. -/
@[instance_reducible]
/--
Definition of `instL2OpNormedSpace` / `instL2OpNormedSpace` 的定义

English:
definition instL2OpNormedSpace
  signature: : NormedSpace 𝕜 (Matrix m n 𝕜) where
  body: by
    rw [l2_opNorm_def]; rw [map_smul]
    exact norm_smul_le r ((toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap x)

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedSpace

中文:
定义 instL2OpNormedSpace
  签名: : NormedSpace 𝕜 (Matrix m n 𝕜) where
  定义体: by
    rw [l2_opNorm_def]; rw [map_smul]
    exact norm_smul_le r ((toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap x)

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedSpace

Depends on / 依赖: l2_opNorm_def, map_smul, norm_smul_le, toContinuousLinearMap, toEuclideanLin
-/
def instL2OpNormedSpace : NormedSpace 𝕜 (Matrix m n 𝕜) where
  norm_smul_le r x := by
    rw [l2_opNorm_def]; rw [map_smul]
    exact norm_smul_le r ((toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap x)

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedSpace

/-- The normed ring structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`. -/
@[instance_reducible]
/--
Definition of `instL2OpNormedRing` / `instL2OpNormedRing` 的定义

English:
definition instL2OpNormedRing
  signature: : NormedRing (Matrix n n 𝕜) where
  body: l2OpNormedRingAux.dist_eq
  norm_mul_le := l2OpNormedRingAux.norm_mul_le

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedRing

中文:
定义 instL2OpNormedRing
  签名: : NormedRing (Matrix n n 𝕜) where
  定义体: l2OpNormedRingAux.dist_eq
  norm_mul_le := l2OpNormedRingAux.norm_mul_le

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedRing

Depends on / 依赖: dist_eq, l2OpNormedRingAux, l2OpNormedRingAux.dist_eq
-/
def instL2OpNormedRing : NormedRing (Matrix n n 𝕜) where
  dist_eq := l2OpNormedRingAux.dist_eq
  norm_mul_le := l2OpNormedRingAux.norm_mul_le

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedRing

/--
lemma `cstar_norm_def` / 引理 `cstar_norm_def`

English:
lemma cstar_norm_def
  given: (A : Matrix n n 𝕜)
  statement: ‖A‖ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖
  proof: rfl

中文:
引理 cstar_norm_def
  条件: (A : Matrix n n 𝕜)
  结论: ‖A‖ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖
  证明: rfl
-/
lemma cstar_norm_def (A : Matrix n n 𝕜) : ‖A‖ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖ := rfl

/--
lemma `cstar_nnnorm_def` / 引理 `cstar_nnnorm_def`

English:
lemma cstar_nnnorm_def
  given: (A : Matrix n n 𝕜)
  statement: ‖A‖₊ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖₊
  proof: rfl

中文:
引理 cstar_nnnorm_def
  条件: (A : Matrix n n 𝕜)
  结论: ‖A‖₊ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖₊
  证明: rfl
-/
lemma cstar_nnnorm_def (A : Matrix n n 𝕜) : ‖A‖₊ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖₊ := rfl

/-- The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`. -/
@[instance_reducible]
/--
Definition of `instL2OpNormedAlgebra` / `instL2OpNormedAlgebra` 的定义

English:
definition instL2OpNormedAlgebra
  signature: : NormedAlgebra 𝕜 (Matrix n n 𝕜) where
  body: norm_smul_le

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedAlgebra

中文:
定义 instL2OpNormedAlgebra
  签名: : NormedAlgebra 𝕜 (Matrix n n 𝕜) where
  定义体: norm_smul_le

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedAlgebra

Depends on / 依赖: norm_smul_le
-/
def instL2OpNormedAlgebra : NormedAlgebra 𝕜 (Matrix n n 𝕜) where
  norm_smul_le := norm_smul_le

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedAlgebra

/--
lemma `instCStarRing` / 引理 `instCStarRing`

English:
lemma instCStarRing
  statement: CStarRing (Matrix n n 𝕜) where
  proof: le_of_eq Eq.symm l2_opNorm_conjTranspose_mul_self M

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instCStarRing

中文:
引理 instCStarRing
  结论: CStarRing (Matrix n n 𝕜) where
  证明: le_of_eq Eq.symm l2_opNorm_conjTranspose_mul_self M

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instCStarRing

Depends on / 依赖: Eq.symm, l2_opNorm_conjTranspose_mul_self, le_of_eq
-/
lemma instCStarRing : CStarRing (Matrix n n 𝕜) where
norm_mul_self_le M := le_of_eq Eq.symm l2_opNorm_conjTranspose_mul_self M

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instCStarRing

/--
Definition of `instCStarAlgebra` / `instCStarAlgebra` 的定义

English:
definition instCStarAlgebra
  signature: {n : Type*} [Fintype n] [DecidableEq n]

中文:
定义 instCStarAlgebra
  签名: {n : 类型} [Fintype n] [DecidableEq n]
-/
@[instance_reducible] noncomputable def instCStarAlgebra {n : Type*} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n Complex) where

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instCStarAlgebra

end Matrix

end L2OpNorm
