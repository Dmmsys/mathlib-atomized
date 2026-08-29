/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# `L²` inner product space structure on products of inner product spaces

The `L²` norm on product of two inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \langle x_1, y_1 \rangle + \langle x_2, y_2 \rangle.
$$
This is recorded in this file as an inner product space instance on `WithLp 2 (E × F)`.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

variable {𝕜 ι₁ ι₂ E F : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F]

namespace WithLp

/--
Instance `instProdInnerProductSpace` / 实例 `instProdInnerProductSpace`

English:
instance instProdInnerProductSpace
  signature: :
  body: ⟪x.fst, y.fst⟫_𝕜 + ⟪x.snd, y.snd⟫_𝕜
  norm_sq_eq_re_inner x := by
    simp [prod_norm_sq_eq_of_L2]
  conj_inner_symm x y := by
    simp
  add_left x y z := by
    simp only [add_fst, add_snd, inner_add_left]
    ring
  smul_left x y r := by
    simp only [smul_fst, inner_smul_left, smul_snd]
    ring

@[simp]

中文:
实例 instProdInnerProductSpace
  签名: :
  定义体: ⟪x.fst, y.fst⟫_𝕜 + ⟪x.snd, y.snd⟫_𝕜
  norm_sq_eq_re_inner x := by
    simp [prod_norm_sq_eq_of_L2]
  conj_inner_symm x y := by
    simp
  add_left x y z := by
    simp only [add_fst, add_snd, inner_add_left]
    ring
  smul_left x y r := by
    simp only [smul_fst, inner_smul_left, smul_snd]
    ring

@[simp]

Depends on / 依赖: x.fst, x.snd, y.fst, y.snd
-/
noncomputable instance instProdInnerProductSpace :
    InnerProductSpace 𝕜 (WithLp 2 (E × F)) where
  inner x y := ⟪x.fst, y.fst⟫_𝕜 + ⟪x.snd, y.snd⟫_𝕜
  norm_sq_eq_re_inner x := by
    simp [prod_norm_sq_eq_of_L2]
  conj_inner_symm x y := by
    simp
  add_left x y z := by
    simp only [add_fst, add_snd, inner_add_left]
    ring
  smul_left x y r := by
    simp only [smul_fst, inner_smul_left, smul_snd]
    ring

@[simp]
/--
theorem `prod_inner_apply` / 定理 `prod_inner_apply`

English:
theorem prod_inner_apply
  given: (x y : WithLp 2 (E × F))
  proof: rfl

中文:
定理 prod_inner_apply
  条件: (x y : WithLp 2 (E × F))
  证明: rfl
-/
theorem prod_inner_apply (x y : WithLp 2 (E × F)) :
    ⟪x, y⟫_𝕜 = ⟪(ofLp x).fst, (ofLp y).fst⟫_𝕜 + ⟪(ofLp x).snd, (ofLp y).snd⟫_𝕜 := rfl

end WithLp

noncomputable section
namespace OrthonormalBasis

variable [Fintype ι₁] [Fintype ι₂]

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F)
  body: ((v.toBasis.prod w.toBasis).map (WithLp.linearEquiv 2 𝕜 (E × F)).symm).toOrthonormalBasis
  (by
    constructor
    · simp
    · unfold Pairwise
      simp only [ne_eq, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl,
        OrthonormalBasis.coe_toBasis, LinearMap.coe_inr, WithLp.coe_symm_linearEquiv,
        WithLp.prod_inner_apply, Sum.forall, Sum.elim_inl, Function.comp_apply, inner_zero_right,
        add_zero, Sum.elim_inr, zero_add, Sum.inl.injEq, reduceCtorEq, not_false_eq_true,
        inner_zero_left, imp_self, implies_true, and_true, Sum.inr.injEq, true_and]
      exact ⟨v.orthonormal.2, w.orthonormal.2⟩)

中文:
定义 乘积
  签名: (v : 正交标准基 ι₁ 𝕜 E) (w : 正交标准基 ι₂ 𝕜 F)
  定义体: ((v.toBasis.prod w.toBasis).map (WithLp.linearEquiv 2 𝕜 (E × F)).symm).toOrthonormalBasis
  (by
    constructor
    · simp
    · unfold Pairwise
      simp only [ne_eq, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl,
        OrthonormalBasis.coe_toBasis, LinearMap.coe_inr, WithLp.coe_symm_linearEquiv,
        WithLp.prod_inner_apply, Sum.forall, Sum.elim_inl, Function.comp_apply, inner_zero_right,
        add_zero, Sum.elim_inr, zero_add, Sum.inl.injEq, reduceCtorEq, not_false_eq_true,
        inner_zero_left, imp_self, implies_true, and_true, Sum.inr.injEq, true_and]
      exact ⟨v.orthonormal.2, w.orthonormal.2⟩)

Depends on / 依赖: Basis.map_apply, Basis.prod_apply, Function, Function.comp_apply, LinearMap, LinearMap.coe_inl, LinearMap.coe_inr, OrthonormalBasis, OrthonormalBasis.coe_toBasis, Pairwise, Sum.elim_inl, Sum.elim_inr, Sum.forall, Sum.inl.injEq, WithLp, WithLp.coe_symm_linearEquiv, WithLp.linearEquiv, WithLp.prod_inner_apply, add_zero, and_tr
-/
def prod (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ oplus ι₂) 𝕜 (WithLp 2 (E × F)) :=
  ((v.toBasis.prod w.toBasis).map (WithLp.linearEquiv 2 𝕜 (E × F)).symm).toOrthonormalBasis
  (by
    constructor
    · simp
    · unfold Pairwise
      simp only [ne_eq, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl,
        OrthonormalBasis.coe_toBasis, LinearMap.coe_inr, WithLp.coe_symm_linearEquiv,
        WithLp.prod_inner_apply, Sum.forall, Sum.elim_inl, Function.comp_apply, inner_zero_right,
        add_zero, Sum.elim_inr, zero_add, Sum.inl.injEq, reduceCtorEq, not_false_eq_true,
        inner_zero_left, imp_self, implies_true, and_true, Sum.inr.injEq, true_and]
      exact ⟨v.orthonormal.2, w.orthonormal.2⟩)

/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F)
  proof: by
  rw [Sum.forall]
  unfold OrthonormalBasis.prod
  aesop

中文:
定理 prod_apply
  条件: (v : 正交标准基 ι₁ 𝕜 E) (w : 正交标准基 ι₂ 𝕜 F)
  证明: by
  rw [Sum.forall]
  unfold OrthonormalBasis.prod
  aesop
-/
@[simp] theorem prod_apply (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F) :
    forall i : ι₁ oplus ι₂, v.prod w i =
      Sum.elim ((WithLp.toLp 2) ∘ (LinearMap.inl 𝕜 E F) ∘ v)
        ((WithLp.toLp 2) ∘ (LinearMap.inr 𝕜 E F) ∘ w) i := by
  rw [Sum.forall]
  unfold OrthonormalBasis.prod
  aesop

end OrthonormalBasis

namespace Submodule

variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E)

/-- If a subspace `K` of an inner product space `E` admits an orthogonal projection, then `E` is
isometrically isomorphic to the `L²` product of `K` and `Kᗮ`. -/
@[simps! symm_apply]
/--
Definition of `orthogonalDecomposition` / `orthogonalDecomposition` 的定义

English:
definition orthogonalDecomposition
  signature: : E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ) where
  body: (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm
    ≪≫ₗ (WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).symm
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]; rw [WithLp.prod_norm_sq_eq_of_L2]; rw [K.norm_sq_eq_add_norm_sq_projection]
    simp [starProjection_apply_eq_isComplProjection]

@[simp]

中文:
定义 orthogonalDecomposition
  签名: : E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ) where
  定义体: (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm
    ≪≫ₗ (WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).symm
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]; rw [WithLp.prod_norm_sq_eq_of_L2]; rw [K.norm_sq_eq_add_norm_sq_projection]
    simp [starProjection_apply_eq_isComplProjection]

@[simp]

Depends on / 依赖: K.isCompl_orthogonal, K.prodEquivOfIsCompl, isCompl_orthogonal, prodEquivOfIsCompl
-/
def orthogonalDecomposition : E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ) where
  __ := (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm
    ≪≫ₗ (WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).symm
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]; rw [WithLp.prod_norm_sq_eq_of_L2]; rw [K.norm_sq_eq_add_norm_sq_projection]
    simp [starProjection_apply_eq_isComplProjection]

@[simp]
/--
theorem `orthogonalDecomposition_apply` / 定理 `orthogonalDecomposition_apply`

English:
theorem orthogonalDecomposition_apply
  proof: by
  simp [orthogonalDecomposition, orthogonalProjectionOnto_apply_eq_projectionOnto]

中文:
定理 orthogonalDecomposition_apply
  证明: by
  simp [orthogonalDecomposition, orthogonalProjectionOnto_apply_eq_projectionOnto]

Depends on / 依赖: orthogonalDecomposition, orthogonalProjectionOnto_apply_eq_projectionOnto
-/
theorem orthogonalDecomposition_apply :
    K.orthogonalDecomposition x =
      .toLp 2 (K.orthogonalProjectionOnto x, Kᗮ.orthogonalProjectionOnto x) := by
  simp [orthogonalDecomposition, orthogonalProjectionOnto_apply_eq_projectionOnto]

/--
theorem `toLinearEquiv_orthogonalDecomposition` / 定理 `toLinearEquiv_orthogonalDecomposition`

English:
theorem toLinearEquiv_orthogonalDecomposition
  proof: rfl

中文:
定理 toLinearEquiv_orthogonalDecomposition
  证明: rfl
-/
theorem toLinearEquiv_orthogonalDecomposition :
    K.orthogonalDecomposition.toLinearEquiv =
      (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm ≪≫ₗ
        (WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).symm :=
  rfl

/--
theorem `toLinearEquiv_orthogonalDecomposition_symm` / 定理 `toLinearEquiv_orthogonalDecomposition_symm`

English:
theorem toLinearEquiv_orthogonalDecomposition_symm
  proof: rfl

中文:
定理 toLinearEquiv_orthogonalDecomposition_symm
  证明: rfl
-/
theorem toLinearEquiv_orthogonalDecomposition_symm :
    K.orthogonalDecomposition.symm.toLinearEquiv =
      WithLp.linearEquiv 2 𝕜 (K × Kᗮ) ≪≫ₗ
        K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal :=
  rfl

/--
theorem `coe_orthogonalDecomposition` / 定理 `coe_orthogonalDecomposition`

English:
theorem coe_orthogonalDecomposition
  proof: by
  ext; simp

中文:
定理 coe_orthogonalDecomposition
  证明: by
  ext; simp
-/
theorem coe_orthogonalDecomposition :
    (K.orthogonalDecomposition : E ->L[𝕜] WithLp 2 (K × Kᗮ)) =
      (WithLp.prodContinuousLinearEquiv 2 𝕜 K Kᗮ).symm ∘L
        K.orthogonalProjectionOnto.prod Kᗮ.orthogonalProjectionOnto := by
  ext; simp

/--
theorem `coe_orthogonalDecomposition_symm` / 定理 `coe_orthogonalDecomposition_symm`

English:
theorem coe_orthogonalDecomposition_symm
  proof: rfl

中文:
定理 coe_orthogonalDecomposition_symm
  证明: rfl
-/
theorem coe_orthogonalDecomposition_symm :
    (K.orthogonalDecomposition.symm : WithLp 2 (K × Kᗮ) ->L[𝕜] E) =
      K.subtypeL.coprod Kᗮ.subtypeL ∘L WithLp.prodContinuousLinearEquiv 2 𝕜 K Kᗮ :=
  rfl

/--
theorem `fst_orthogonalDecomposition_apply` / 定理 `fst_orthogonalDecomposition_apply`

English:
theorem fst_orthogonalDecomposition_apply
  proof: by
  simp

中文:
定理 fst_orthogonalDecomposition_apply
  证明: by
  simp
-/
theorem fst_orthogonalDecomposition_apply :
    (K.orthogonalDecomposition x).fst = K.orthogonalProjectionOnto x := by
  simp

/--
theorem `snd_orthogonalDecomposition_apply` / 定理 `snd_orthogonalDecomposition_apply`

English:
theorem snd_orthogonalDecomposition_apply
  proof: by
  simp

中文:
定理 snd_orthogonalDecomposition_apply
  证明: by
  simp
-/
theorem snd_orthogonalDecomposition_apply :
    (K.orthogonalDecomposition x).snd = Kᗮ.orthogonalProjectionOnto x := by
  simp

/--
theorem `fstL_comp_coe_orthogonalDecomposition` / 定理 `fstL_comp_coe_orthogonalDecomposition`

English:
theorem fstL_comp_coe_orthogonalDecomposition
  proof: by
  ext; simp

中文:
定理 fstL_comp_coe_orthogonalDecomposition
  证明: by
  ext; simp
-/
theorem fstL_comp_coe_orthogonalDecomposition :
    WithLp.fstL 2 𝕜 K Kᗮ ∘L K.orthogonalDecomposition = K.orthogonalProjectionOnto := by
  ext; simp

/--
theorem `sndL_comp_coe_orthogonalDecomposition` / 定理 `sndL_comp_coe_orthogonalDecomposition`

English:
theorem sndL_comp_coe_orthogonalDecomposition
  proof: by
  ext; simp

中文:
定理 sndL_comp_coe_orthogonalDecomposition
  证明: by
  ext; simp
-/
theorem sndL_comp_coe_orthogonalDecomposition :
    WithLp.sndL 2 𝕜 K Kᗮ ∘L K.orthogonalDecomposition = Kᗮ.orthogonalProjectionOnto := by
  ext; simp

/--
Definition of `quotientEquivOrthogonal` / `quotientEquivOrthogonal` 的定义

English:
definition quotientEquivOrthogonal
  signature: : (E ⧸ K) ≃ₗᵢ[𝕜] ↥Kᗮ where
  body: K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  norm_map' y := by
    set f := K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal
    rw [coe_norm]; rw [← norm_orthogonalProjectionOnto_apply Kᗮ (f y).2]; rw [orthogonalProjectionOnto_orthogonal]; rw [coe_norm]; rw [starProjection_minimal]; rw [eq_comm]
    have h : ‖Quotient.mk (f y).val‖ = sInf ((fun (x : E) => ‖(f y).val + x‖) '' K.toAddSubgroup) :=
      quotient_norm_mk_eq K.toAddSubgroup (f y).1
    convert! h using 2
    · simp [f]
    · rw [sInf_image', ← Equiv.iInf_comp (Equiv.neg K)]
      simp

@[simp]

中文:
定义 quotientEquivOrthogonal
  签名: : (E ⧸ K) ≃ₗᵢ[𝕜] ↥Kᗮ where
  定义体: K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  norm_map' y := by
    set f := K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal
    rw [coe_norm]; rw [← norm_orthogonalProjectionOnto_apply Kᗮ (f y).2]; rw [orthogonalProjectionOnto_orthogonal]; rw [coe_norm]; rw [starProjection_minimal]; rw [eq_comm]
    have h : ‖Quotient.mk (f y).val‖ = sInf ((fun (x : E) => ‖(f y).val + x‖) '' K.toAddSubgroup) :=
      quotient_norm_mk_eq K.toAddSubgroup (f y).1
    convert! h using 2
    · simp [f]
    · rw [sInf_image', ← Equiv.iInf_comp (Equiv.neg K)]
      simp

@[simp]

Depends on / 依赖: K.isCompl_orthogonal, K.quotientEquivOfIsCompl, isCompl_orthogonal, quotientEquivOfIsCompl
-/
def quotientEquivOrthogonal : (E ⧸ K) ≃ₗᵢ[𝕜] ↥Kᗮ where
  __ := K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  norm_map' y := by
    set f := K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal
    rw [coe_norm]; rw [← norm_orthogonalProjectionOnto_apply Kᗮ (f y).2]; rw [orthogonalProjectionOnto_orthogonal]; rw [coe_norm]; rw [starProjection_minimal]; rw [eq_comm]
    have h : ‖Quotient.mk (f y).val‖ = sInf ((fun (x : E) => ‖(f y).val + x‖) '' K.toAddSubgroup) :=
      quotient_norm_mk_eq K.toAddSubgroup (f y).1
    convert! h using 2
    · simp [f]
    · rw [sInf_image', ← Equiv.iInf_comp (Equiv.neg K)]
      simp

@[simp]
/--
theorem `coe_quotientEquivOrthogonal` / 定理 `coe_quotientEquivOrthogonal`

English:
theorem coe_quotientEquivOrthogonal
  proof: rfl

@[simp]

中文:
定理 coe_quotientEquivOrthogonal
  证明: rfl

@[simp]
-/
theorem coe_quotientEquivOrthogonal :
    ⇑K.quotientEquivOrthogonal = K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal :=
  rfl

@[simp]
/--
theorem `coe_quotientEquivOrthogonal_symm` / 定理 `coe_quotientEquivOrthogonal_symm`

English:
theorem coe_quotientEquivOrthogonal_symm
  proof: rfl

@[simp]

中文:
定理 coe_quotientEquivOrthogonal_symm
  证明: rfl

@[simp]
-/
theorem coe_quotientEquivOrthogonal_symm :
    ⇑K.quotientEquivOrthogonal.symm = (K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm :=
  rfl

@[simp]
/--
lemma `toLinearEquiv_quotientEquivOrthogonal` / 引理 `toLinearEquiv_quotientEquivOrthogonal`

English:
lemma toLinearEquiv_quotientEquivOrthogonal
  proof: rfl

中文:
引理 toLinearEquiv_quotientEquivOrthogonal
  证明: rfl
-/
lemma toLinearEquiv_quotientEquivOrthogonal :
    (quotientEquivOrthogonal K).toLinearEquiv = K.quotientEquivOfIsCompl _ K.isCompl_orthogonal :=
  rfl

/--
theorem `quotientEquivOrthogonal_mk` / 定理 `quotientEquivOrthogonal_mk`

English:
theorem quotientEquivOrthogonal_mk
  given: (x : E) (hx : x in Kᗮ)
  proof: by
  simp [← K.quotientEquivOfIsCompl_apply_mk_right K.isCompl_orthogonal ⟨x, hx⟩]

中文:
定理 quotientEquivOrthogonal_mk
  条件: (x : E) (hx : x in Kᗮ)
  证明: by
  simp [← K.quotientEquivOfIsCompl_apply_mk_right K.isCompl_orthogonal ⟨x, hx⟩]

Depends on / 依赖: K.isCompl_orthogonal, K.quotientEquivOfIsCompl_apply_mk_right, isCompl_orthogonal, quotientEquivOfIsCompl_apply_mk_right
-/
theorem quotientEquivOrthogonal_mk (x : E) (hx : x in Kᗮ) :
    K.quotientEquivOrthogonal (Quotient.mk x) = ⟨x, hx⟩ := by
  simp [← K.quotientEquivOfIsCompl_apply_mk_right K.isCompl_orthogonal ⟨x, hx⟩]

/--
theorem `quotientEquivOrthogonal_symm_eq_mk` / 定理 `quotientEquivOrthogonal_symm_eq_mk`

English:
theorem quotientEquivOrthogonal_symm_eq_mk
  given: (x : E) (hx : x in Kᗮ)
  proof: by
  simp

中文:
定理 quotientEquivOrthogonal_symm_eq_mk
  条件: (x : E) (hx : x in Kᗮ)
  证明: by
  simp
-/
theorem quotientEquivOrthogonal_symm_eq_mk (x : E) (hx : x in Kᗮ) :
    K.quotientEquivOrthogonal.symm ⟨x, hx⟩ = Quotient.mk x := by
  simp

/--
Instance `instQuotientInnerProductSpace` / 实例 `instQuotientInnerProductSpace`

English:
instance instQuotientInnerProductSpace
  signature: :
  body: ⟪K.quotientEquivOrthogonal x, K.quotientEquivOrthogonal y⟫_𝕜
  add_left x y z := by rw [map_add, inner_add_left]
  smul_left x y r := by rw [map_smul, inner_smul_left]
  conj_inner_symm x y := inner_conj_symm _ _
  norm_sq_eq_re_inner y := by rw [inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]

@[simp]

中文:
实例 instQuotientInnerProductSpace
  签名: :
  定义体: ⟪K.quotientEquivOrthogonal x, K.quotientEquivOrthogonal y⟫_𝕜
  add_left x y z := by rw [map_add, inner_add_left]
  smul_left x y r := by rw [map_smul, inner_smul_left]
  conj_inner_symm x y := inner_conj_symm _ _
  norm_sq_eq_re_inner y := by rw [inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]

@[simp]

Depends on / 依赖: K.quotientEquivOrthogonal, quotientEquivOrthogonal
-/
noncomputable instance instQuotientInnerProductSpace :
    InnerProductSpace 𝕜 (E ⧸ K) where
  inner x y := ⟪K.quotientEquivOrthogonal x, K.quotientEquivOrthogonal y⟫_𝕜
  add_left x y z := by rw [map_add, inner_add_left]
  smul_left x y r := by rw [map_smul, inner_smul_left]
  conj_inner_symm x y := inner_conj_symm _ _
  norm_sq_eq_re_inner y := by rw [inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]

@[simp]
/--
theorem `inner_quotient_eq` / 定理 `inner_quotient_eq`

English:
theorem inner_quotient_eq
  given: (x y : E ⧸ K)
  proof: rfl

中文:
定理 inner_quotient_eq
  条件: (x y : E ⧸ K)
  证明: rfl
-/
theorem inner_quotient_eq (x y : E ⧸ K) :
    ⟪x, y⟫_𝕜 = ⟪K.quotientEquivOrthogonal x, K.quotientEquivOrthogonal y⟫_𝕜 :=
  rfl

/--
theorem `Quotient.inner_mk_mk` / 定理 `Quotient.inner_mk_mk`

English:
theorem Quotient.inner_mk_mk
  given: (x y : E) (hx : x in Kᗮ) (hy : y in Kᗮ)
  proof: by
  simp [K.quotientEquivOrthogonal_mk x hx, K.quotientEquivOrthogonal_mk y hy]

中文:
定理 商.inner_mk_mk
  条件: (x y : E) (hx : x in Kᗮ) (hy : y in Kᗮ)
  证明: by
  simp [K.quotientEquivOrthogonal_mk x hx, K.quotientEquivOrthogonal_mk y hy]

Depends on / 依赖: K.quotientEquivOrthogonal_mk, Quotient, Quotient.mk, quotientEquivOrthogonal_mk
-/
theorem Quotient.inner_mk_mk (x y : E) (hx : x in Kᗮ) (hy : y in Kᗮ) :
    ⟪Quotient.mk (p := K) x, Quotient.mk y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  simp [K.quotientEquivOrthogonal_mk x hx, K.quotientEquivOrthogonal_mk y hy]

end Submodule

end
