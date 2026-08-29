/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# The orthogonal projection

Given a nonempty subspace `K` of an inner product space `E` such that `K`
admits an orthogonal projection, this file constructs
`K.orthogonalProjectionOnto : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`. This map
satisfies: for any point `u` in `E`, the point `v = K.orthogonalProjectionOnto u` in `K`
minimizes the distance `‖u - v‖` to `u`.

This file also defines `K.starProjection : E →L[𝕜] E` which is the
orthogonal projection of `E` onto `K` but as a map from `E` to `E` instead of `E` to `K`.

Basic API for `orthogonalProjectionOnto` and `starProjection` is developed.

## References

The orthogonal projection construction is adapted from
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

@[expose] public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
local notation "absR" => @abs Real _ _

namespace Submodule

/--
Definition of `HasOrthogonalProjection` / `HasOrthogonalProjection` 的定义

English:
class HasOrthogonalProjection
  parameters: (K : Submodule 𝕜 E)
  axioms and operations (1):
    - exists_orthogonal((v : E)) : exists w in K, v - w in Kᗮ

中文:
类 有OrthogonalProjection
  参数: (K : 子模 𝕜 E)
  公理与运算 (1 个):
    - exists_orthogonal((v : E)) : 存在 w in K, v - w in Kᗮ
-/
class HasOrthogonalProjection (K : Submodule 𝕜 E) : Prop where
  exists_orthogonal (v : E) : exists w in K, v - w in Kᗮ

variable (K : Submodule 𝕜 E)

instance (priority := 100) HasOrthogonalProjection.ofCompleteSpace [CompleteSpace K] :
    K.HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases K.exists_norm_eq_iInf_of_complete_subspace (completeSpace_coe_iff_isComplete.mp ‹_›) v
      with ⟨w, hwK, hw⟩
    refine ⟨w, hwK, (K.mem_orthogonal' _).2 ?_⟩
    rwa [← K.norm_eq_iInf_iff_inner_eq_zero hwK]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.HasOrthogonalProjection]
  signature: : Kᗮ.HasOrthogonalProjection where
  body: by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) v with ⟨w, hwK, hw⟩
    refine ⟨_, hw, ?_⟩
    rw [sub_sub_cancel]
    exact K.le_orthogonal_orthogonal hwK

中文:
实例 [K.有OrthogonalProjection]
  签名: : Kᗮ.有OrthogonalProjection where
  定义体: by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) v with ⟨w, hwK, hw⟩
    refine ⟨_, hw, ?_⟩
    rw [sub_sub_cancel]
    exact K.le_orthogonal_orthogonal hwK

Depends on / 依赖: HasOrthogonalProjection, HasOrthogonalProjection.exists_orthogonal, K.le_orthogonal_orthogonal, exists_orthogonal, le_orthogonal_orthogonal, sub_sub_cancel
-/
instance [K.HasOrthogonalProjection] : Kᗮ.HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) v with ⟨w, hwK, hw⟩
    refine ⟨_, hw, ?_⟩
    rw [sub_sub_cancel]
    exact K.le_orthogonal_orthogonal hwK

/--
Instance `HasOrthogonalProjection.map_linearIsometryEquiv` / 实例 `HasOrthogonalProjection.map_linearIsometryEquiv`

English:
instance HasOrthogonalProjection.map_linearIsometryEquiv
  signature: [K.HasOrthogonalProjection]
  body: by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) (f.symm v) with ⟨w, hwK, hw⟩
    refine ⟨f w, Submodule.mem_map_of_mem hwK, Set.forall_mem_image.2 fun u hu => ?_⟩
    simp [← f.symm.inner_map_map, hw u hu]

中文:
实例 有OrthogonalProjection.map_linearIsometryEquiv
  签名: [K.有OrthogonalProjection]
  定义体: by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) (f.symm v) with ⟨w, hwK, hw⟩
    refine ⟨f w, Submodule.mem_map_of_mem hwK, Set.forall_mem_image.2 fun u hu => ?_⟩
    simp [← f.symm.inner_map_map, hw u hu]

Depends on / 依赖: HasOrthogonalProjection, HasOrthogonalProjection.exists_orthogonal, Set.forall_mem_image, Submodule, Submodule.mem_map_of_mem, exists_orthogonal, f.symm, f.symm.inner_map_map, forall_mem_image, inner_map_map, mem_map_of_mem
-/
instance HasOrthogonalProjection.map_linearIsometryEquiv [K.HasOrthogonalProjection]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    (K.map (f.toLinearEquiv : E ->ₗ[𝕜] E')).HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) (f.symm v) with ⟨w, hwK, hw⟩
    refine ⟨f w, Submodule.mem_map_of_mem hwK, Set.forall_mem_image.2 fun u hu => ?_⟩
    simp [← f.symm.inner_map_map, hw u hu]

/--
Instance `HasOrthogonalProjection.map_linearIsometryEquiv'` / 实例 `HasOrthogonalProjection.map_linearIsometryEquiv'`

English:
instance HasOrthogonalProjection.map_linearIsometryEquiv'
  signature: [K.HasOrthogonalProjection]
  body: HasOrthogonalProjection.map_linearIsometryEquiv K f

中文:
实例 有OrthogonalProjection.map_linearIsometryEquiv'
  签名: [K.有OrthogonalProjection]
  定义体: HasOrthogonalProjection.map_linearIsometryEquiv K f

Depends on / 依赖: HasOrthogonalProjection, HasOrthogonalProjection.map_linearIsometryEquiv, map_linearIsometryEquiv
-/
instance HasOrthogonalProjection.map_linearIsometryEquiv' [K.HasOrthogonalProjection]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    (K.map (f.toLinearIsometry : E ->ₗ[𝕜] E')).HasOrthogonalProjection :=
  HasOrthogonalProjection.map_linearIsometryEquiv K f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : Submodule 𝕜 E).HasOrthogonalProjection
  body: ⟨fun v => ⟨v, trivial, by simp⟩⟩

中文:
实例 :
  签名: (⊤ : 子模 𝕜 E).有OrthogonalProjection
  定义体: ⟨fun v => ⟨v, trivial, by simp⟩⟩
-/
instance : (⊤ : Submodule 𝕜 E).HasOrthogonalProjection := ⟨fun v => ⟨v, trivial, by simp⟩⟩

instance (K : ClosedSubmodule 𝕜 E) [CompleteSpace E] : K.HasOrthogonalProjection := by
  let := K.isClosed'
  infer_instance

/--
theorem `isCompl_orthogonal` / 定理 `isCompl_orthogonal`

English:
theorem isCompl_orthogonal
  given: [K.HasOrthogonalProjection]
  statement: IsCompl K Kᗮ where
  proof: K.orthogonal_disjoint
  codisjoint := K.codisjoint_iff_exists_add_eq.mpr fun z =>
    have ⟨w, hw, hzw⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := K) z
    ⟨w, z - w, hw, hzw, add_sub_cancel w z⟩

中文:
定理 isCompl_orthogonal
  条件: [K.有OrthogonalProjection]
  结论: 是补集 K Kᗮ where
  证明: K.orthogonal_disjoint
  codisjoint := K.codisjoint_iff_exists_add_eq.mpr fun z =>
    have ⟨w, hw, hzw⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := K) z
    ⟨w, z - w, hw, hzw, add_sub_cancel w z⟩

Depends on / 依赖: K.orthogonal_disjoint, orthogonal_disjoint
-/
theorem isCompl_orthogonal [K.HasOrthogonalProjection] : IsCompl K Kᗮ where
  disjoint := K.orthogonal_disjoint
  codisjoint := K.codisjoint_iff_exists_add_eq.mpr fun z =>
    have ⟨w, hw, hzw⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := K) z
    ⟨w, z - w, hw, hzw, add_sub_cancel w z⟩

/--
theorem `norm_projection_orthogonal_le` / 定理 `norm_projection_orthogonal_le`

English:
theorem norm_projection_orthogonal_le
  given: [K.HasOrthogonalProjection] (x : E)
  proof: by
  conv_rhs => rw [← projection_add_projection_eq_self K.isCompl_orthogonal x]
  simp [← sq_le_sq₀ (norm_nonneg _), sq, mul_nonneg,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (K.mem_orthogonal _ |>.mp _ _ _)]

中文:
定理 norm_projection_orthogonal_le
  条件: [K.有OrthogonalProjection] (x : E)
  证明: by
  conv_rhs => rw [← projection_add_projection_eq_self K.isCompl_orthogonal x]
  simp [← sq_le_sq₀ (norm_nonneg _), sq, mul_nonneg,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (K.mem_orthogonal _ |>.mp _ _ _)]

Depends on / 依赖: K.isCompl_orthogonal, K.mem_orthogonal, conv_rhs, isCompl_orthogonal, mem_orthogonal, mul_nonneg, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, norm_nonneg, projection_add_projection_eq_self
-/
theorem norm_projection_orthogonal_le [K.HasOrthogonalProjection] (x : E) :
    ‖K.projection Kᗮ K.isCompl_orthogonal x‖ <= ‖x‖ := by
  conv_rhs => rw [← projection_add_projection_eq_self K.isCompl_orthogonal x]
  simp [← sq_le_sq₀ (norm_nonneg _), sq, mul_nonneg,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (K.mem_orthogonal _ |>.mp _ _ _)]

/--
theorem `isTopCompl_orthogonal` / 定理 `isTopCompl_orthogonal`

English:
theorem isTopCompl_orthogonal
  given: [K.HasOrthogonalProjection]
  statement: IsTopCompl K Kᗮ where
  proof: K.isCompl_orthogonal
  continuous_projection := AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
    grw [norm_projection_orthogonal_le, one_mul]

noncomputable section

中文:
定理 isTopCompl_orthogonal
  条件: [K.有OrthogonalProjection]
  结论: 是TopCompl K Kᗮ where
  证明: K.isCompl_orthogonal
  continuous_projection := AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
    grw [norm_projection_orthogonal_le, one_mul]

noncomputable section

Depends on / 依赖: K.isCompl_orthogonal, isCompl_orthogonal
-/
theorem isTopCompl_orthogonal [K.HasOrthogonalProjection] : IsTopCompl K Kᗮ where
  isCompl := K.isCompl_orthogonal
  continuous_projection := AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
    grw [norm_projection_orthogonal_le, one_mul]

noncomputable section

section orthogonalProjection

variable [K.HasOrthogonalProjection]

/--
Definition of `orthogonalProjectionOnto` / `orthogonalProjectionOnto` 的定义

English:
definition orthogonalProjectionOnto
  signature: : E ->L[𝕜] K
  body: K.projectionOntoL Kᗮ K.isTopCompl_orthogonal

中文:
定义 orthogonalProjectionOnto
  签名: : E ->L[𝕜] K
  定义体: K.projectionOntoL Kᗮ K.isTopCompl_orthogonal

Depends on / 依赖: K.isTopCompl_orthogonal, K.projectionOntoL, isTopCompl_orthogonal, projectionOntoL
-/
def orthogonalProjectionOnto : E ->L[𝕜] K := K.projectionOntoL Kᗮ K.isTopCompl_orthogonal

/--
Definition of `orthogonalProjection` / `orthogonalProjection` 的定义

English:
abbreviation orthogonalProjection
  signature: :
  body: K.orthogonalProjectionOnto

中文:
缩写 orthogonalProjection
  签名: :
  定义体: K.orthogonalProjectionOnto
-/
@[deprecated orthogonalProjectionOnto (since := "2026-05-05")] abbrev orthogonalProjection :
    E ->L[𝕜] K := K.orthogonalProjectionOnto

variable {K}

/--
Definition of `starProjection` / `starProjection` 的定义

English:
definition starProjection
  signature: (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
  body: U.subtypeL ∘L U.orthogonalProjectionOnto

中文:
定义 starProjection
  签名: (U : 子模 𝕜 E) [U.有OrthogonalProjection]
  定义体: U.subtypeL ∘L U.orthogonalProjectionOnto

Depends on / 依赖: U.orthogonalProjectionOnto, U.subtypeL, orthogonalProjectionOnto, subtypeL
-/
def starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    E ->L[𝕜] E := U.subtypeL ∘L U.orthogonalProjectionOnto

/-- The orthogonal projection onto a complete subspace, as an
unbundled function. This definition is only intended for use in
setting up the bundled version `orthogonalProjection` and should not
be used once that is defined. -/
@[deprecated "Please use `orthogonalProjectionOnto` or `starProjection`." (since := "2026-06-10")]
/--
Definition of `orthogonalProjectionFn` / `orthogonalProjectionFn` 的定义

English:
abbreviation orthogonalProjectionFn
  signature: (x : E)
  body: K.starProjection x

@[deprecated "Please use `orthogonalProjectionOnto` or `starProjection`." (since := "2026-06-10")]

中文:
缩写 orthogonalProjectionFn
  签名: (x : E)
  定义体: K.starProjection x

@[deprecated "Please use `orthogonalProjectionOnto` or `starProjection`." (since := "2026-06-10")]

Depends on / 依赖: K.starProjection, starProjection
-/
abbrev orthogonalProjectionFn (x : E) : E := K.starProjection x

@[deprecated "Please use `orthogonalProjectionOnto` or `starProjection`." (since := "2026-06-10")]
/--
theorem `orthogonalProjectionFn_eq` / 定理 `orthogonalProjectionFn_eq`

English:
theorem orthogonalProjectionFn_eq
  given: (v : E)
  proof: rfl

中文:
定理 orthogonalProjectionFn_eq
  条件: (v : E)
  证明: rfl
-/
theorem orthogonalProjectionFn_eq (v : E) :
    K.orthogonalProjectionFn v = (K.orthogonalProjectionOnto v : E) := rfl

/--
lemma `starProjection_apply` / 引理 `starProjection_apply`

English:
lemma starProjection_apply
  given: (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E)
  proof: rfl

@[simp]

中文:
引理 starProjection_apply
  条件: (U : 子模 𝕜 E) [U.有OrthogonalProjection] (v : E)
  证明: rfl

@[simp]
-/
lemma starProjection_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E) :
    U.starProjection v = U.orthogonalProjectionOnto v := rfl

@[simp]
/--
lemma `coe_orthogonalProjectionOnto_apply` / 引理 `coe_orthogonalProjectionOnto_apply`

English:
lemma coe_orthogonalProjectionOnto_apply
  given: (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E)
  proof: rfl

@[deprecated (since := "2026-05-05")]
alias coe_orthogonalProjection_apply := coe_orthogonalProjectionOnto_apply

@[simp]

中文:
引理 coe_orthogonalProjectionOnto_apply
  条件: (U : 子模 𝕜 E) [U.有OrthogonalProjection] (v : E)
  证明: rfl

@[deprecated (since := "2026-05-05")]
alias coe_orthogonalProjection_apply := coe_orthogonalProjectionOnto_apply

@[simp]
-/
lemma coe_orthogonalProjectionOnto_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E) :
     U.orthogonalProjectionOnto v = U.starProjection v := rfl

@[deprecated (since := "2026-05-05")]
alias coe_orthogonalProjection_apply := coe_orthogonalProjectionOnto_apply

@[simp]
/--
lemma `starProjection_apply_mem` / 引理 `starProjection_apply_mem`

English:
lemma starProjection_apply_mem
  given: (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E)
  proof: by
  simp only [starProjection_apply, SetLike.coe_mem]

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_mem := starProjection_apply_mem

中文:
引理 starProjection_apply_mem
  条件: (U : 子模 𝕜 E) [U.有OrthogonalProjection] (x : E)
  证明: by
  simp only [starProjection_apply, SetLike.coe_mem]

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_mem := starProjection_apply_mem

Depends on / 依赖: SetLike, SetLike.coe_mem, coe_mem, starProjection_apply
-/
lemma starProjection_apply_mem (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    U.starProjection x in U := by
  simp only [starProjection_apply, SetLike.coe_mem]

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_mem := starProjection_apply_mem

/-- The characterization of the orthogonal projection. -/
@[simp]
/--
theorem `starProjection_inner_eq_zero` / 定理 `starProjection_inner_eq_zero`

English:
theorem starProjection_inner_eq_zero
  given: (v w : E) (hw : w in K)
  statement: ⟪v - K.starProjection v, w⟫ = 0
  proof: by
suffices v - K.projection Kᗮ K.isCompl_orthogonal v in Kᗮ from inner_eq_zero_symm.mp this w hw
  simp [← projection_eq_self_sub_projection]

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_inner_eq_zero :=
  starProjection_inner_eq_zero

中文:
定理 starProjection_inner_eq_zero
  条件: (v w : E) (hw : w in K)
  结论: ⟪v - K.starProjection v, w⟫ = 0
  证明: by
suffices v - K.projection Kᗮ K.isCompl_orthogonal v in Kᗮ from inner_eq_zero_symm.mp this w hw
  simp [← projection_eq_self_sub_projection]

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_inner_eq_zero :=
  starProjection_inner_eq_zero

Depends on / 依赖: K.isCompl_orthogonal, K.projection, inner_eq_zero_symm, inner_eq_zero_symm.mp, isCompl_orthogonal, projection, projection_eq_self_sub_projection
-/
theorem starProjection_inner_eq_zero (v w : E) (hw : w in K) : ⟪v - K.starProjection v, w⟫ = 0 := by
suffices v - K.projection Kᗮ K.isCompl_orthogonal v in Kᗮ from inner_eq_zero_symm.mp this w hw
  simp [← projection_eq_self_sub_projection]

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_inner_eq_zero :=
  starProjection_inner_eq_zero

/-- The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`. -/
@[simp]
/--
theorem `sub_starProjection_mem_orthogonal` / 定理 `sub_starProjection_mem_orthogonal`

English:
theorem sub_starProjection_mem_orthogonal
  given: (v : E)
  statement: v - K.starProjection v in Kᗮ
  proof: by
  intro w hw
  rw [inner_eq_zero_symm]
  exact starProjection_inner_eq_zero _ _ hw

中文:
定理 sub_starProjection_mem_orthogonal
  条件: (v : E)
  结论: v - K.starProjection v in Kᗮ
  证明: by
  intro w hw
  rw [inner_eq_zero_symm]
  exact starProjection_inner_eq_zero _ _ hw

Depends on / 依赖: inner_eq_zero_symm, starProjection_inner_eq_zero
-/
theorem sub_starProjection_mem_orthogonal (v : E) : v - K.starProjection v in Kᗮ := by
  intro w hw
  rw [inner_eq_zero_symm]
  exact starProjection_inner_eq_zero _ _ hw

/--
theorem `eq_starProjection_of_mem_of_inner_eq_zero` / 定理 `eq_starProjection_of_mem_of_inner_eq_zero`

English:
theorem eq_starProjection_of_mem_of_inner_eq_zero
  statement: {u v : E} (hvm : v in K)
  proof: by
  have hvs : K.starProjection u - v in K := K.sub_mem (coe_mem _) hvm
  have houv : ⟪u - v - (u - K.starProjection u), K.starProjection u - v⟫ = 0 := by
    rw [inner_sub_left]; rw [starProjection_inner_eq_zero u _ hvs]; rw [hvo _ hvs]; rw [sub_zero]
  rwa [sub_sub_sub_cancel_left, inner_self_eq_

中文:
定理 eq_starProjection_of_mem_of_inner_eq_zero
  结论: {u v : E} (hvm : v in K)
  证明: by
  have hvs : K.starProjection u - v in K := K.sub_mem (coe_mem _) hvm
  have houv : ⟪u - v - (u - K.starProjection u), K.starProjection u - v⟫ = 0 := by
    rw [inner_sub_left]; rw [starProjection_inner_eq_zero u _ hvs]; rw [hvo _ hvs]; rw [sub_zero]
  rwa [sub_sub_sub_cancel_left, inner_self_eq_

Depends on / 依赖: K.starProjection, K.sub_mem, coe_mem, inner_self_eq_zero, inner_sub_left, starProjection, starProjection_inner_eq_zero, sub_eq_zero, sub_mem, sub_sub_sub_cancel_left, sub_zero
-/
theorem eq_starProjection_of_mem_of_inner_eq_zero {u v : E} (hvm : v in K)
    (hvo : forall w in K, ⟪u - v, w⟫ = 0) : K.starProjection u = v := by
  have hvs : K.starProjection u - v in K := K.sub_mem (coe_mem _) hvm
  have houv : ⟪u - v - (u - K.starProjection u), K.starProjection u - v⟫ = 0 := by
    rw [inner_sub_left]; rw [starProjection_inner_eq_zero u _ hvs]; rw [hvo _ hvs]; rw [sub_zero]
  rwa [sub_sub_sub_cancel_left, inner_self_eq_zero, sub_eq_zero] at houv

@[deprecated (since := "2026-06-10")] alias eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero :=
  eq_starProjection_of_mem_of_inner_eq_zero

/--
theorem `eq_starProjection_of_mem_orthogonal` / 定理 `eq_starProjection_of_mem_orthogonal`

English:
theorem eq_starProjection_of_mem_orthogonal
  statement: {u v : E} (hv : v in K)
  proof: eq_starProjection_of_mem_of_inner_eq_zero hv (Submodule.mem_orthogonal' _ _).1 hvo

中文:
定理 eq_starProjection_of_mem_orthogonal
  结论: {u v : E} (hv : v in K)
  证明: eq_starProjection_of_mem_of_inner_eq_zero hv (Submodule.mem_orthogonal' _ _).1 hvo

Depends on / 依赖: Submodule, Submodule.mem_orthogonal, eq_starProjection_of_mem_of_inner_eq_zero, mem_orthogonal
-/
theorem eq_starProjection_of_mem_orthogonal {u v : E} (hv : v in K)
    (hvo : u - v in Kᗮ) : K.starProjection u = v :=
eq_starProjection_of_mem_of_inner_eq_zero hv (Submodule.mem_orthogonal' _ _).1 hvo

/--
theorem `eq_starProjection_of_mem_orthogonal'` / 定理 `eq_starProjection_of_mem_orthogonal'`

English:
theorem eq_starProjection_of_mem_orthogonal'
  statement: {u v z : E}
  proof: eq_starProjection_of_mem_orthogonal hv (by simpa [hu])

@[simp]

中文:
定理 eq_starProjection_of_mem_orthogonal'
  结论: {u v z : E}
  证明: eq_starProjection_of_mem_orthogonal hv (by simpa [hu])

@[simp]

Depends on / 依赖: eq_starProjection_of_mem_orthogonal
-/
theorem eq_starProjection_of_mem_orthogonal' {u v z : E}
    (hv : v in K) (hz : z in Kᗮ) (hu : u = v + z) : K.starProjection u = v :=
  eq_starProjection_of_mem_orthogonal hv (by simpa [hu])

@[simp]
/--
theorem `starProjection_orthogonal_val` / 定理 `starProjection_orthogonal_val`

English:
theorem starProjection_orthogonal_val
  given: (u : E)
  proof: eq_starProjection_of_mem_orthogonal' (sub_starProjection_mem_orthogonal _)
(K.le_orthogonal_orthogonal (K.orthogonalProjectionOnto u).2) (sub_add_cancel _ _).symm

中文:
定理 starProjection_orthogonal_val
  条件: (u : E)
  证明: eq_starProjection_of_mem_orthogonal' (sub_starProjection_mem_orthogonal _)
(K.le_orthogonal_orthogonal (K.orthogonalProjectionOnto u).2) (sub_add_cancel _ _).symm

Depends on / 依赖: K.le_orthogonal_orthogonal, K.orthogonalProjectionOnto, eq_starProjection_of_mem_orthogonal, le_orthogonal_orthogonal, orthogonalProjectionOnto, sub_add_cancel, sub_starProjection_mem_orthogonal
-/
theorem starProjection_orthogonal_val (u : E) :
    Kᗮ.starProjection u = u - K.starProjection u :=
  eq_starProjection_of_mem_orthogonal' (sub_starProjection_mem_orthogonal _)
(K.le_orthogonal_orthogonal (K.orthogonalProjectionOnto u).2) (sub_add_cancel _ _).symm

/--
theorem `orthogonalProjectionOnto_orthogonal` / 定理 `orthogonalProjectionOnto_orthogonal`

English:
theorem orthogonalProjectionOnto_orthogonal
  given: (u : E)
  proof: Subtype.ext starProjection_orthogonal_val _

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_orthogonal := orthogonalProjectionOnto_orthogonal

中文:
定理 orthogonalProjectionOnto_orthogonal
  条件: (u : E)
  证明: Subtype.ext starProjection_orthogonal_val _

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_orthogonal := orthogonalProjectionOnto_orthogonal

Depends on / 依赖: Subtype, Subtype.ext, starProjection_orthogonal_val
-/
theorem orthogonalProjectionOnto_orthogonal (u : E) :
    Kᗮ.orthogonalProjectionOnto u =
      ⟨u - K.starProjection u, sub_starProjection_mem_orthogonal _⟩ :=
Subtype.ext starProjection_orthogonal_val _

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_orthogonal := orthogonalProjectionOnto_orthogonal

/--
lemma `starProjection_orthogonal` / 引理 `starProjection_orthogonal`

English:
lemma starProjection_orthogonal
  given: (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
  proof: by
  ext
  simp only [starProjection, ContinuousLinearMap.comp_apply,
    orthogonalProjectionOnto_orthogonal]
  simp

中文:
引理 starProjection_orthogonal
  条件: (U : 子模 𝕜 E) [U.有OrthogonalProjection]
  证明: by
  ext
  simp only [starProjection, ContinuousLinearMap.comp_apply,
    orthogonalProjectionOnto_orthogonal]
  simp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, comp_apply, orthogonalProjectionOnto_orthogonal, starProjection
-/
lemma starProjection_orthogonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Uᗮ.starProjection = ContinuousLinearMap.id 𝕜 E - U.starProjection := by
  ext
  simp only [starProjection, ContinuousLinearMap.comp_apply,
    orthogonalProjectionOnto_orthogonal]
  simp

/--
lemma `starProjection_orthogonal'` / 引理 `starProjection_orthogonal'`

English:
lemma starProjection_orthogonal'
  given: (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
  proof: starProjection_orthogonal U

中文:
引理 starProjection_orthogonal'
  条件: (U : 子模 𝕜 E) [U.有OrthogonalProjection]
  证明: starProjection_orthogonal U

Depends on / 依赖: starProjection_orthogonal
-/
lemma starProjection_orthogonal' (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Uᗮ.starProjection = 1 - U.starProjection := starProjection_orthogonal U

/--
theorem `starProjection_minimal` / 定理 `starProjection_minimal`

English:
theorem starProjection_minimal
  given: {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (y : E)
  proof: by
  rw [starProjection_apply]; rw [U.norm_eq_iInf_iff_inner_eq_zero (Submodule.coe_mem _)]
  exact starProjection_inner_eq_zero _

中文:
定理 starProjection_minimal
  条件: {U : 子模 𝕜 E} [U.有OrthogonalProjection] (y : E)
  证明: by
  rw [starProjection_apply]; rw [U.norm_eq_iInf_iff_inner_eq_zero (Submodule.coe_mem _)]
  exact starProjection_inner_eq_zero _

Depends on / 依赖: Submodule, Submodule.coe_mem, U.norm_eq_iInf_iff_inner_eq_zero, coe_mem, norm_eq_iInf_iff_inner_eq_zero, starProjection_apply, starProjection_inner_eq_zero
-/
theorem starProjection_minimal {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (y : E) :
    ‖y - U.starProjection y‖ = ⨅ x : U, ‖y - x‖ := by
  rw [starProjection_apply]; rw [U.norm_eq_iInf_iff_inner_eq_zero (Submodule.coe_mem _)]
  exact starProjection_inner_eq_zero _

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp]
/--
theorem `orthogonalProjectionOnto_mem_subspace_eq_self` / 定理 `orthogonalProjectionOnto_mem_subspace_eq_self`

English:
theorem orthogonalProjectionOnto_mem_subspace_eq_self
  given: (v : K)
  proof: by
  ext
  apply eq_starProjection_of_mem_of_inner_eq_zero <;> simp

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_mem_subspace_eq_self := orthogonalProjectionOnto_mem_subspace_eq_self

@[simp]

中文:
定理 orthogonalProjectionOnto_mem_subspace_eq_self
  条件: (v : K)
  证明: by
  ext
  apply eq_starProjection_of_mem_of_inner_eq_zero <;> simp

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_mem_subspace_eq_self := orthogonalProjectionOnto_mem_subspace_eq_self

@[simp]

Depends on / 依赖: eq_starProjection_of_mem_of_inner_eq_zero
-/
theorem orthogonalProjectionOnto_mem_subspace_eq_self (v : K) :
    K.orthogonalProjectionOnto v = v := by
  ext
  apply eq_starProjection_of_mem_of_inner_eq_zero <;> simp

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_mem_subspace_eq_self := orthogonalProjectionOnto_mem_subspace_eq_self

@[simp]
/--
theorem `starProjection_mem_subspace_eq_self` / 定理 `starProjection_mem_subspace_eq_self`

English:
theorem starProjection_mem_subspace_eq_self
  given: (v : K)
  proof: by simp [starProjection_apply]

中文:
定理 starProjection_mem_subspace_eq_self
  条件: (v : K)
  证明: by simp [starProjection_apply]

Depends on / 依赖: starProjection_apply
-/
theorem starProjection_mem_subspace_eq_self (v : K) :
    K.starProjection v = v := by simp [starProjection_apply]

/--
theorem `starProjection_eq_self_iff` / 定理 `starProjection_eq_self_iff`

English:
theorem starProjection_eq_self_iff
  given: {v : E}
  statement: K.starProjection v = v ↔ v in K
  proof: by
  refine ⟨fun h => ?_, fun h => eq_starProjection_of_mem_of_inner_eq_zero h ?_⟩
  · rw [← h]
    simp
  · simp

中文:
定理 starProjection_eq_self_iff
  条件: {v : E}
  结论: K.starProjection v = v ↔ v in K
  证明: by
  refine ⟨fun h => ?_, fun h => eq_starProjection_of_mem_of_inner_eq_zero h ?_⟩
  · rw [← h]
    simp
  · simp

Depends on / 依赖: eq_starProjection_of_mem_of_inner_eq_zero
-/
theorem starProjection_eq_self_iff {v : E} : K.starProjection v = v ↔ v in K := by
  refine ⟨fun h => ?_, fun h => eq_starProjection_of_mem_of_inner_eq_zero h ?_⟩
  · rw [← h]
    simp
  · simp

variable (K) in
@[simp]
/--
lemma `isIdempotentElem_starProjection` / 引理 `isIdempotentElem_starProjection`

English:
lemma isIdempotentElem_starProjection
  statement: IsIdempotentElem K.starProjection
  proof: ContinuousLinearMap.ext fun x => starProjection_eq_self_iff.mpr by simp

@[simp]

中文:
引理 isIdempotentElem_starProjection
  结论: IsIdempotentElem K.starProjection
  证明: ContinuousLinearMap.ext fun x => starProjection_eq_self_iff.mpr by simp

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, starProjection_eq_self_iff, starProjection_eq_self_iff.mpr
-/
lemma isIdempotentElem_starProjection : IsIdempotentElem K.starProjection :=
ContinuousLinearMap.ext fun x => starProjection_eq_self_iff.mpr by simp

@[simp]
/--
lemma `range_starProjection` / 引理 `range_starProjection`

English:
lemma range_starProjection
  given: (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
  proof: by
  ext x
  exact ⟨fun ⟨y, hy⟩ => hy ▸ coe_mem (U.orthogonalProjectionOnto y),
    fun h => ⟨x, starProjection_eq_self_iff.mpr h⟩⟩

中文:
引理 range_starProjection
  条件: (U : 子模 𝕜 E) [U.有OrthogonalProjection]
  证明: by
  ext x
  exact ⟨fun ⟨y, hy⟩ => hy ▸ coe_mem (U.orthogonalProjectionOnto y),
    fun h => ⟨x, starProjection_eq_self_iff.mpr h⟩⟩

Depends on / 依赖: U.orthogonalProjectionOnto, coe_mem, orthogonalProjectionOnto, starProjection_eq_self_iff, starProjection_eq_self_iff.mpr
-/
lemma range_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.starProjection.range = U := by
  ext x
  exact ⟨fun ⟨y, hy⟩ => hy ▸ coe_mem (U.orthogonalProjectionOnto y),
    fun h => ⟨x, starProjection_eq_self_iff.mpr h⟩⟩

/--
lemma `starProjection_top` / 引理 `starProjection_top`

English:
lemma starProjection_top
  statement: (⊤ : Submodule 𝕜 E).starProjection = ContinuousLinearMap.id 𝕜 E
  proof: by
  ext
  exact starProjection_eq_self_iff.mpr trivial

中文:
引理 starProjection_top
  结论: (⊤ : 子模 𝕜 E).starProjection = 连续线性映射.id 𝕜 E
  证明: by
  ext
  exact starProjection_eq_self_iff.mpr trivial

Depends on / 依赖: starProjection_eq_self_iff, starProjection_eq_self_iff.mpr
-/
lemma starProjection_top : (⊤ : Submodule 𝕜 E).starProjection = ContinuousLinearMap.id 𝕜 E := by
  ext
  exact starProjection_eq_self_iff.mpr trivial

/--
lemma `starProjection_top'` / 引理 `starProjection_top'`

English:
lemma starProjection_top'
  statement: (⊤ : Submodule 𝕜 E).starProjection = 1
  proof: starProjection_top

@[simp]

中文:
引理 starProjection_top'
  结论: (⊤ : 子模 𝕜 E).starProjection = 1
  证明: starProjection_top

@[simp]

Depends on / 依赖: starProjection_top
-/
lemma starProjection_top' : (⊤ : Submodule 𝕜 E).starProjection = 1 :=
  starProjection_top

@[simp]
/--
theorem `orthogonalProjectionOnto_eq_zero_iff` / 定理 `orthogonalProjectionOnto_eq_zero_iff`

English:
theorem orthogonalProjectionOnto_eq_zero_iff
  given: {v : E}
  proof: by
refine ⟨fun h => ?_, fun h => Subtype.ext eq_starProjection_of_mem_orthogonal
    (zero_mem _) ?_⟩
  · rw [← sub_zero v, ← coe_zero (p := K), ← h]
    exact sub_starProjection_mem_orthogonal (K := K) v
  · simpa

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_eq_zero_iff := orth

中文:
定理 orthogonalProjectionOnto_eq_zero_iff
  条件: {v : E}
  证明: by
refine ⟨fun h => ?_, fun h => Subtype.ext eq_starProjection_of_mem_orthogonal
    (zero_mem _) ?_⟩
  · rw [← sub_zero v, ← coe_zero (p := K), ← h]
    exact sub_starProjection_mem_orthogonal (K := K) v
  · simpa

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_eq_zero_iff := orth

Depends on / 依赖: Subtype, Subtype.ext, coe_zero, eq_starProjection_of_mem_orthogonal, sub_starProjection_mem_orthogonal, sub_zero, zero_mem
-/
theorem orthogonalProjectionOnto_eq_zero_iff {v : E} :
    K.orthogonalProjectionOnto v = 0 ↔ v in Kᗮ := by
refine ⟨fun h => ?_, fun h => Subtype.ext eq_starProjection_of_mem_orthogonal
    (zero_mem _) ?_⟩
  · rw [← sub_zero v, ← coe_zero (p := K), ← h]
    exact sub_starProjection_mem_orthogonal (K := K) v
  · simpa

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_eq_zero_iff := orthogonalProjectionOnto_eq_zero_iff

@[simp]
/--
theorem `ker_orthogonalProjectionOnto` / 定理 `ker_orthogonalProjectionOnto`

English:
theorem ker_orthogonalProjectionOnto
  statement: K.orthogonalProjectionOnto.ker = Kᗮ
  proof: by
  ext; exact orthogonalProjectionOnto_eq_zero_iff

@[deprecated (since := "2026-05-05")] alias ker_orthogonalProjection := ker_orthogonalProjectionOnto

中文:
定理 ker_orthogonalProjectionOnto
  结论: K.orthogonalProjectionOnto.ker = Kᗮ
  证明: by
  ext; exact orthogonalProjectionOnto_eq_zero_iff

@[deprecated (since := "2026-05-05")] alias ker_orthogonalProjection := ker_orthogonalProjectionOnto

Depends on / 依赖: orthogonalProjectionOnto_eq_zero_iff
-/
theorem ker_orthogonalProjectionOnto : K.orthogonalProjectionOnto.ker = Kᗮ := by
  ext; exact orthogonalProjectionOnto_eq_zero_iff

@[deprecated (since := "2026-05-05")] alias ker_orthogonalProjection := ker_orthogonalProjectionOnto

open ContinuousLinearMap in
@[simp]
/--
lemma `ker_starProjection` / 引理 `ker_starProjection`

English:
lemma ker_starProjection
  given: (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
  proof: by
  rw [LinearMap.IsIdempotentElem.ker_eq_range U.isIdempotentElem_starProjection.toLinearMap]; rw [← range_starProjection Uᗮ]; rw [starProjection_orthogonal]; rw [toLinearMap_sub]; rw [coe_id]

中文:
引理 ker_starProjection
  条件: (U : 子模 𝕜 E) [U.有OrthogonalProjection]
  证明: by
  rw [LinearMap.IsIdempotentElem.ker_eq_range U.isIdempotentElem_starProjection.toLinearMap]; rw [← range_starProjection Uᗮ]; rw [starProjection_orthogonal]; rw [toLinearMap_sub]; rw [coe_id]

Depends on / 依赖: IsIdempotentElem, LinearMap, LinearMap.IsIdempotentElem.ker_eq_range, U.isIdempotentElem_starProjection.toLinearMap, coe_id, isIdempotentElem_starProjection, ker_eq_range, range_starProjection, starProjection_orthogonal, toLinearMap, toLinearMap_sub
-/
lemma ker_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.starProjection.ker = Uᗮ := by
  rw [LinearMap.IsIdempotentElem.ker_eq_range U.isIdempotentElem_starProjection.toLinearMap]; rw [← range_starProjection Uᗮ]; rw [starProjection_orthogonal]; rw [toLinearMap_sub]; rw [coe_id]

/--
theorem `_root_.LinearIsometry.map_starProjection` / 定理 `_root_.LinearIsometry.map_starProjection`

English:
theorem _root_.LinearIsometry.map_starProjection
  statement: {E E' : Type*} [NormedAddCommGroup E]
  proof: by
  refine (eq_starProjection_of_mem_of_inner_eq_zero ?_ fun y hy => ?_).symm
  · refine Submodule.apply_coe_mem_map _ _
  rcases hy with ⟨x', hx', rfl : f x' = y⟩
  rw [← f.map_sub]; rw [f.inner_map_map]; rw [starProjection_inner_eq_zero x x' hx']

中文:
定理 _root_.线性等距.map_starProjection
  结论: {E E' : 类型} [赋范交换加群 E]
  证明: by
  refine (eq_starProjection_of_mem_of_inner_eq_zero ?_ fun y hy => ?_).symm
  · refine Submodule.apply_coe_mem_map _ _
  rcases hy with ⟨x', hx', rfl : f x' = y⟩
  rw [← f.map_sub]; rw [f.inner_map_map]; rw [starProjection_inner_eq_zero x x' hx']

Depends on / 依赖: Submodule, Submodule.apply_coe_mem_map, apply_coe_mem_map, eq_starProjection_of_mem_of_inner_eq_zero, f.inner_map_map, f.map_sub, inner_map_map, map_sub, starProjection_inner_eq_zero
-/
theorem _root_.LinearIsometry.map_starProjection {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ->ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection] [(p.map f.toLinearMap).HasOrthogonalProjection]
    (x : E) : f (p.starProjection x) = (p.map f.toLinearMap).starProjection (f x) := by
  refine (eq_starProjection_of_mem_of_inner_eq_zero ?_ fun y hy => ?_).symm
  · refine Submodule.apply_coe_mem_map _ _
  rcases hy with ⟨x', hx', rfl : f x' = y⟩
  rw [← f.map_sub]; rw [f.inner_map_map]; rw [starProjection_inner_eq_zero x x' hx']

/--
theorem `_root_.LinearIsometry.map_starProjection'` / 定理 `_root_.LinearIsometry.map_starProjection'`

English:
theorem _root_.LinearIsometry.map_starProjection'
  statement: {E E' : Type*} [NormedAddCommGroup E]
  proof: have : (p.map f.toLinearMap).HasOrthogonalProjection := ‹_›
  f.map_starProjection p x

中文:
定理 _root_.线性等距.map_starProjection'
  结论: {E E' : 类型} [赋范交换加群 E]
  证明: have : (p.map f.toLinearMap).HasOrthogonalProjection := ‹_›
  f.map_starProjection p x

Depends on / 依赖: HasOrthogonalProjection, f.map_starProjection, f.toLinearMap, map_starProjection, p.map, toLinearMap
-/
theorem _root_.LinearIsometry.map_starProjection' {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ->ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection]
    [(p.map (f : E ->ₗ[𝕜] E')).HasOrthogonalProjection] (x : E) :
    f (p.starProjection x) = (p.map (f : E ->ₗ[𝕜] E')).starProjection (f x) :=
  have : (p.map f.toLinearMap).HasOrthogonalProjection := ‹_›
  f.map_starProjection p x

/--
theorem `starProjection_map_apply` / 定理 `starProjection_map_apply`

English:
theorem starProjection_map_apply
  statement: {E E' : Type*} [NormedAddCommGroup E]
  proof: by
  simpa only [f.coe_toLinearIsometry, f.apply_symm_apply] using!
    (f.toLinearIsometry.map_starProjection' p (f.symm x)).symm

中文:
定理 starProjection_map_apply
  结论: {E E' : 类型} [赋范交换加群 E]
  证明: by
  simpa only [f.coe_toLinearIsometry, f.apply_symm_apply] using!
    (f.toLinearIsometry.map_starProjection' p (f.symm x)).symm

Depends on / 依赖: apply_symm_apply, coe_toLinearIsometry, f.apply_symm_apply, f.coe_toLinearIsometry, f.symm, f.toLinearIsometry.map_starProjection, map_starProjection, toLinearIsometry
-/
theorem starProjection_map_apply {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection] (x : E') :
    (p.map (f.toLinearEquiv : E ->ₗ[𝕜] E')).starProjection x =
      f (p.starProjection (f.symm x)) := by
  simpa only [f.coe_toLinearIsometry, f.apply_symm_apply] using!
    (f.toLinearIsometry.map_starProjection' p (f.symm x)).symm

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp]
/--
theorem `orthogonalProjectionOnto_bot` / 定理 `orthogonalProjectionOnto_bot`

English:
theorem orthogonalProjectionOnto_bot
  statement: (⊥ : Submodule 𝕜 E).orthogonalProjectionOnto = 0
  proof: by ext

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_bot := orthogonalProjectionOnto_bot

@[simp]

中文:
定理 orthogonalProjectionOnto_bot
  结论: (⊥ : 子模 𝕜 E).orthogonalProjectionOnto = 0
  证明: by ext

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_bot := orthogonalProjectionOnto_bot

@[simp]
-/
theorem orthogonalProjectionOnto_bot : (⊥ : Submodule 𝕜 E).orthogonalProjectionOnto = 0 := by ext

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_bot := orthogonalProjectionOnto_bot

@[simp]
/--
lemma `starProjection_bot` / 引理 `starProjection_bot`

English:
lemma starProjection_bot
  statement: (⊥ : Submodule 𝕜 E).starProjection = 0
  proof: by
  rw [starProjection]; rw [orthogonalProjectionOnto_bot]; rw [ContinuousLinearMap.comp_zero]

中文:
引理 starProjection_bot
  结论: (⊥ : 子模 𝕜 E).starProjection = 0
  证明: by
  rw [starProjection]; rw [orthogonalProjectionOnto_bot]; rw [ContinuousLinearMap.comp_zero]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_zero, comp_zero, orthogonalProjectionOnto_bot, starProjection
-/
lemma starProjection_bot : (⊥ : Submodule 𝕜 E).starProjection = 0 := by
  rw [starProjection]; rw [orthogonalProjectionOnto_bot]; rw [ContinuousLinearMap.comp_zero]

variable (K)

/--
theorem `orthogonalProjectionOnto_norm_le` / 定理 `orthogonalProjectionOnto_norm_le`

English:
theorem orthogonalProjectionOnto_norm_le
  statement: ‖K.orthogonalProjectionOnto‖ <= 1
  proof: by
  refine K.orthogonalProjectionOnto.opNorm_le_bound zero_le_one ?_
  simp [orthogonalProjectionOnto, projectionOntoL, norm_projection_orthogonal_le]

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_norm_le := orthogonalProjectionOnto_norm_le

中文:
定理 orthogonalProjectionOnto_norm_le
  结论: ‖K.orthogonalProjectionOnto‖ <= 1
  证明: by
  refine K.orthogonalProjectionOnto.opNorm_le_bound zero_le_one ?_
  simp [orthogonalProjectionOnto, projectionOntoL, norm_projection_orthogonal_le]

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_norm_le := orthogonalProjectionOnto_norm_le

Depends on / 依赖: K.orthogonalProjectionOnto.opNorm_le_bound, norm_projection_orthogonal_le, opNorm_le_bound, orthogonalProjectionOnto, projectionOntoL, zero_le_one
-/
theorem orthogonalProjectionOnto_norm_le : ‖K.orthogonalProjectionOnto‖ <= 1 := by
  refine K.orthogonalProjectionOnto.opNorm_le_bound zero_le_one ?_
  simp [orthogonalProjectionOnto, projectionOntoL, norm_projection_orthogonal_le]

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_norm_le := orthogonalProjectionOnto_norm_le

/--
theorem `starProjection_norm_le` / 定理 `starProjection_norm_le`

English:
theorem starProjection_norm_le
  statement: ‖K.starProjection‖ <= 1
  proof: K.orthogonalProjectionOnto_norm_le

中文:
定理 starProjection_norm_le
  结论: ‖K.starProjection‖ <= 1
  证明: K.orthogonalProjectionOnto_norm_le

Depends on / 依赖: K.orthogonalProjectionOnto_norm_le, orthogonalProjectionOnto_norm_le
-/
theorem starProjection_norm_le : ‖K.starProjection‖ <= 1 :=
  K.orthogonalProjectionOnto_norm_le

/--
theorem `norm_orthogonalProjectionOnto_apply` / 定理 `norm_orthogonalProjectionOnto_apply`

English:
theorem norm_orthogonalProjectionOnto_apply
  given: {v : E} (hv : v in K)
  proof: congr(‖$(K.starProjection_eq_self_iff.mpr hv)‖)

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection_apply := norm_orthogonalProjectionOnto_apply

中文:
定理 norm_orthogonalProjectionOnto_apply
  条件: {v : E} (hv : v in K)
  证明: congr(‖$(K.starProjection_eq_self_iff.mpr hv)‖)

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection_apply := norm_orthogonalProjectionOnto_apply

Depends on / 依赖: K.starProjection_eq_self_iff.mpr, starProjection_eq_self_iff
-/
theorem norm_orthogonalProjectionOnto_apply {v : E} (hv : v in K) :
    ‖orthogonalProjectionOnto K v‖ = ‖v‖ :=
  congr(‖$(K.starProjection_eq_self_iff.mpr hv)‖)

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection_apply := norm_orthogonalProjectionOnto_apply

/--
theorem `norm_starProjection_apply` / 定理 `norm_starProjection_apply`

English:
theorem norm_starProjection_apply
  given: {v : E} (hv : v in K)
  proof: norm_orthogonalProjectionOnto_apply _ hv

中文:
定理 norm_starProjection_apply
  条件: {v : E} (hv : v in K)
  证明: norm_orthogonalProjectionOnto_apply _ hv

Depends on / 依赖: norm_orthogonalProjectionOnto_apply
-/
theorem norm_starProjection_apply {v : E} (hv : v in K) :
    ‖K.starProjection v‖ = ‖v‖ :=
  norm_orthogonalProjectionOnto_apply _ hv

/--
theorem `norm_orthogonalProjectionOnto_apply_le` / 定理 `norm_orthogonalProjectionOnto_apply_le`

English:
theorem norm_orthogonalProjectionOnto_apply_le
  given: (v : E)
  proof: by calc
  ‖orthogonalProjectionOnto K v‖ <= ‖orthogonalProjectionOnto K‖ * ‖v‖ :=
    K.orthogonalProjectionOnto.le_opNorm _
  _ <= 1 * ‖v‖ := by gcongr; exact orthogonalProjectionOnto_norm_le K
  _ = _ := by simp

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection_apply_le := nor

中文:
定理 norm_orthogonalProjectionOnto_apply_le
  条件: (v : E)
  证明: by calc
  ‖orthogonalProjectionOnto K v‖ <= ‖orthogonalProjectionOnto K‖ * ‖v‖ :=
    K.orthogonalProjectionOnto.le_opNorm _
  _ <= 1 * ‖v‖ := by gcongr; exact orthogonalProjectionOnto_norm_le K
  _ = _ := by simp

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection_apply_le := nor

Depends on / 依赖: K.orthogonalProjectionOnto.le_opNorm, le_opNorm, orthogonalProjectionOnto, orthogonalProjectionOnto_norm_le
-/
theorem norm_orthogonalProjectionOnto_apply_le (v : E) :
    ‖orthogonalProjectionOnto K v‖ <= ‖v‖ := by calc
  ‖orthogonalProjectionOnto K v‖ <= ‖orthogonalProjectionOnto K‖ * ‖v‖ :=
    K.orthogonalProjectionOnto.le_opNorm _
  _ <= 1 * ‖v‖ := by gcongr; exact orthogonalProjectionOnto_norm_le K
  _ = _ := by simp

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection_apply_le := norm_orthogonalProjectionOnto_apply_le

/--
theorem `norm_starProjection_apply_le` / 定理 `norm_starProjection_apply_le`

English:
theorem norm_starProjection_apply_le
  given: (v : E)
  proof: K.norm_orthogonalProjectionOnto_apply_le v

中文:
定理 norm_starProjection_apply_le
  条件: (v : E)
  证明: K.norm_orthogonalProjectionOnto_apply_le v

Depends on / 依赖: K.norm_orthogonalProjectionOnto_apply_le, norm_orthogonalProjectionOnto_apply_le
-/
theorem norm_starProjection_apply_le (v : E) :
    ‖K.starProjection v‖ <= ‖v‖ := K.norm_orthogonalProjectionOnto_apply_le v

/--
theorem `lipschitzWith_orthogonalProjectionOnto` / 定理 `lipschitzWith_orthogonalProjectionOnto`

English:
theorem lipschitzWith_orthogonalProjectionOnto
  proof: ContinuousLinearMap.lipschitzWith_of_opNorm_le K.orthogonalProjectionOnto_norm_le

@[deprecated (since := "2026-05-05")]
alias lipschitzWith_orthogonalProjection := lipschitzWith_orthogonalProjectionOnto

中文:
定理 lipschitzWith_orthogonalProjectionOnto
  证明: ContinuousLinearMap.lipschitzWith_of_opNorm_le K.orthogonalProjectionOnto_norm_le

@[deprecated (since := "2026-05-05")]
alias lipschitzWith_orthogonalProjection := lipschitzWith_orthogonalProjectionOnto

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lipschitzWith_of_opNorm_le, K.orthogonalProjectionOnto_norm_le, lipschitzWith_of_opNorm_le, orthogonalProjectionOnto_norm_le
-/
theorem lipschitzWith_orthogonalProjectionOnto :
    LipschitzWith 1 (orthogonalProjectionOnto K) :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le K.orthogonalProjectionOnto_norm_le

@[deprecated (since := "2026-05-05")]
alias lipschitzWith_orthogonalProjection := lipschitzWith_orthogonalProjectionOnto

/--
theorem `lipschitzWith_starProjection` / 定理 `lipschitzWith_starProjection`

English:
theorem lipschitzWith_starProjection
  proof: ContinuousLinearMap.lipschitzWith_of_opNorm_le K.starProjection_norm_le

中文:
定理 lipschitzWith_starProjection
  证明: ContinuousLinearMap.lipschitzWith_of_opNorm_le K.starProjection_norm_le

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lipschitzWith_of_opNorm_le, K.starProjection_norm_le, lipschitzWith_of_opNorm_le, starProjection_norm_le
-/
theorem lipschitzWith_starProjection :
    LipschitzWith 1 K.starProjection :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le K.starProjection_norm_le

/--
theorem `norm_orthogonalProjectionOnto` / 定理 `norm_orthogonalProjectionOnto`

English:
theorem norm_orthogonalProjectionOnto
  given: (hK : K != ⊥)
  proof: by
  refine le_antisymm K.orthogonalProjectionOnto_norm_le ?_
  obtain ⟨x, hxK, hx_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  simpa [K.norm_orthogonalProjectionOnto_apply hxK, norm_eq_zero, hx_ne_zero]
    using K.orthogonalProjectionOnto.ratio_le_opNorm x

@[deprecated (since := "2026-

中文:
定理 norm_orthogonalProjectionOnto
  条件: (hK : K != ⊥)
  证明: by
  refine le_antisymm K.orthogonalProjectionOnto_norm_le ?_
  obtain ⟨x, hxK, hx_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  simpa [K.norm_orthogonalProjectionOnto_apply hxK, norm_eq_zero, hx_ne_zero]
    using K.orthogonalProjectionOnto.ratio_le_opNorm x

@[deprecated (since := "2026-

Depends on / 依赖: K.norm_orthogonalProjectionOnto_apply, K.orthogonalProjectionOnto.ratio_le_opNorm, K.orthogonalProjectionOnto_norm_le, Submodule, Submodule.exists_mem_ne_zero_of_ne_bot, exists_mem_ne_zero_of_ne_bot, hx_ne_zero, le_antisymm, norm_eq_zero, norm_orthogonalProjectionOnto_apply, orthogonalProjectionOnto, orthogonalProjectionOnto_norm_le, ratio_le_opNorm
-/
theorem norm_orthogonalProjectionOnto (hK : K != ⊥) :
    ‖K.orthogonalProjectionOnto‖ = 1 := by
  refine le_antisymm K.orthogonalProjectionOnto_norm_le ?_
  obtain ⟨x, hxK, hx_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  simpa [K.norm_orthogonalProjectionOnto_apply hxK, norm_eq_zero, hx_ne_zero]
    using K.orthogonalProjectionOnto.ratio_le_opNorm x

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection := norm_orthogonalProjectionOnto

/--
theorem `norm_starProjection` / 定理 `norm_starProjection`

English:
theorem norm_starProjection
  given: (hK : K != ⊥)
  proof: K.norm_orthogonalProjectionOnto hK

中文:
定理 norm_starProjection
  条件: (hK : K != ⊥)
  证明: K.norm_orthogonalProjectionOnto hK

Depends on / 依赖: K.norm_orthogonalProjectionOnto, norm_orthogonalProjectionOnto
-/
theorem norm_starProjection (hK : K != ⊥) :
    ‖K.starProjection‖ = 1 :=
  K.norm_orthogonalProjectionOnto hK

variable (𝕜)

/--
theorem `smul_starProjection_singleton` / 定理 `smul_starProjection_singleton`

English:
theorem smul_starProjection_singleton
  given: {v : E} (w : E)
  proof: by
  suffices ((𝕜 ∙ v).starProjection (((‖v‖ : 𝕜) ^ 2) • w)) = ⟪v, w⟫ • v by
    simpa using this
  apply eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Submodule.mem_span_singleton]
    use ⟪v, w⟫
  · rw [← Submodule.mem_orthogonal', Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [i

中文:
定理 smul_starProjection_singleton
  条件: {v : E} (w : E)
  证明: by
  suffices ((𝕜 ∙ v).starProjection (((‖v‖ : 𝕜) ^ 2) • w)) = ⟪v, w⟫ • v by
    simpa using this
  apply eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Submodule.mem_span_singleton]
    use ⟪v, w⟫
  · rw [← Submodule.mem_orthogonal', Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [i

Depends on / 依赖: Submodule, Submodule.mem_orthogonal, Submodule.mem_orthogonal_singleton_iff_inner_left, Submodule.mem_span_singleton, eq_starProjection_of_mem_of_inner_eq_zero, inner_self_eq_norm_sq_to_K, inner_smul_left, inner_sub_left, mem_orthogonal, mem_orthogonal_singleton_iff_inner_left, mem_span_singleton, mul_comm, starProjection
-/
theorem smul_starProjection_singleton {v : E} (w : E) :
    ((‖v‖ ^ 2 : Real) : 𝕜) • (𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v := by
  suffices ((𝕜 ∙ v).starProjection (((‖v‖ : 𝕜) ^ 2) • w)) = ⟪v, w⟫ • v by
    simpa using this
  apply eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Submodule.mem_span_singleton]
    use ⟪v, w⟫
  · rw [← Submodule.mem_orthogonal', Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_comm]

/--
theorem `starProjection_singleton` / 定理 `starProjection_singleton`

English:
theorem starProjection_singleton
  given: {v : E} (w : E)
  proof: by
  by_cases hv : v = 0
  · rw [hv]
    simp [Submodule.span_zero_singleton 𝕜]
  have hv' : ‖v‖ != 0 := ne_of_gt (norm_pos_iff.mpr hv)
  have key :
    (((‖v‖ ^ 2 : Real) : 𝕜)⁻¹ * ((‖v‖ ^ 2 : Real) : 𝕜)) • (𝕜 ∙ v).starProjection w =
      (((‖v‖ ^ 2 : Real) : 𝕜)⁻¹ * ⟪v, w⟫) • v := by
    simp [mul_

中文:
定理 starProjection_singleton
  条件: {v : E} (w : E)
  证明: by
  by_cases hv : v = 0
  · rw [hv]
    simp [Submodule.span_zero_singleton 𝕜]
  have hv' : ‖v‖ != 0 := ne_of_gt (norm_pos_iff.mpr hv)
  have key :
    (((‖v‖ ^ 2 : Real) : 𝕜)⁻¹ * ((‖v‖ ^ 2 : Real) : 𝕜)) • (𝕜 ∙ v).starProjection w =
      (((‖v‖ ^ 2 : Real) : 𝕜)⁻¹ * ⟪v, w⟫) • v := by
    simp [mul_

Depends on / 依赖: Submodule, Submodule.span_zero_singleton, convert, map_pow, match_scalars, mul_smul, ne_of_gt, norm_pos_iff, norm_pos_iff.mpr, smul_starProjection_singleton, span_zero_singleton, starProjection
-/
theorem starProjection_singleton {v : E} (w : E) :
    (𝕜 ∙ v).starProjection w = (⟪v, w⟫ / ((‖v‖ ^ 2 : Real) : 𝕜)) • v := by
  by_cases hv : v = 0
  · rw [hv]
    simp [Submodule.span_zero_singleton 𝕜]
  have hv' : ‖v‖ != 0 := ne_of_gt (norm_pos_iff.mpr hv)
  have key :
    (((‖v‖ ^ 2 : Real) : 𝕜)⁻¹ * ((‖v‖ ^ 2 : Real) : 𝕜)) • (𝕜 ∙ v).starProjection w =
      (((‖v‖ ^ 2 : Real) : 𝕜)⁻¹ * ⟪v, w⟫) • v := by
    simp [mul_smul, smul_starProjection_singleton 𝕜 w, -map_pow]
  convert! key using 1 <;> match_scalars <;> field_simp [hv']

/--
theorem `starProjection_unit_singleton` / 定理 `starProjection_unit_singleton`

English:
theorem starProjection_unit_singleton
  given: {v : E} (hv : ‖v‖ = 1) (w : E)
  proof: by
  rw [← smul_starProjection_singleton 𝕜 w]
  simp [hv]

中文:
定理 starProjection_unit_singleton
  条件: {v : E} (hv : ‖v‖ = 1) (w : E)
  证明: by
  rw [← smul_starProjection_singleton 𝕜 w]
  simp [hv]

Depends on / 依赖: smul_starProjection_singleton
-/
theorem starProjection_unit_singleton {v : E} (hv : ‖v‖ = 1) (w : E) :
    (𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v := by
  rw [← smul_starProjection_singleton 𝕜 w]
  simp [hv]

end orthogonalProjection

variable {K}

/--
theorem `exists_add_mem_mem_orthogonal` / 定理 `exists_add_mem_mem_orthogonal`

English:
theorem exists_add_mem_mem_orthogonal
  given: [K.HasOrthogonalProjection] (v : E)
  proof: ⟨K.orthogonalProjectionOnto v, Subtype.coe_prop _, v - K.orthogonalProjectionOnto v,
    sub_starProjection_mem_orthogonal _, by simp⟩

中文:
定理 存在_add_mem_mem_orthogonal
  条件: [K.有OrthogonalProjection] (v : E)
  证明: ⟨K.orthogonalProjectionOnto v, Subtype.coe_prop _, v - K.orthogonalProjectionOnto v,
    sub_starProjection_mem_orthogonal _, by simp⟩

Depends on / 依赖: K.orthogonalProjectionOnto, Subtype, Subtype.coe_prop, coe_prop, orthogonalProjectionOnto, sub_starProjection_mem_orthogonal
-/
theorem exists_add_mem_mem_orthogonal [K.HasOrthogonalProjection] (v : E) :
    exists y in K, exists z in Kᗮ, v = y + z :=
  ⟨K.orthogonalProjectionOnto v, Subtype.coe_prop _, v - K.orthogonalProjectionOnto v,
    sub_starProjection_mem_orthogonal _, by simp⟩

/--
theorem `orthogonalProjectionOnto_apply_of_mem_orthogonal` / 定理 `orthogonalProjectionOnto_apply_of_mem_orthogonal`

English:
theorem orthogonalProjectionOnto_apply_of_mem_orthogonal
  proof: orthogonalProjectionOnto_eq_zero_iff.mpr hv

@[deprecated (since := "2026-05-06")] alias
orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero :=
  orthogonalProjectionOnto_apply_of_mem_orthogonal

中文:
定理 orthogonalProjectionOnto_apply_of_mem_orthogonal
  证明: orthogonalProjectionOnto_eq_zero_iff.mpr hv

@[deprecated (since := "2026-05-06")] alias
orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero :=
  orthogonalProjectionOnto_apply_of_mem_orthogonal

Depends on / 依赖: orthogonalProjectionOnto_eq_zero_iff, orthogonalProjectionOnto_eq_zero_iff.mpr
-/
theorem orthogonalProjectionOnto_apply_of_mem_orthogonal
    [K.HasOrthogonalProjection] {v : E} (hv : v in Kᗮ) : K.orthogonalProjectionOnto v = 0 :=
  orthogonalProjectionOnto_eq_zero_iff.mpr hv

@[deprecated (since := "2026-05-06")] alias
orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero :=
  orthogonalProjectionOnto_apply_of_mem_orthogonal

/--
theorem `IsOrtho.orthogonalProjectionOnto_comp_subtypeL` / 定理 `IsOrtho.orthogonalProjectionOnto_comp_subtypeL`

English:
theorem IsOrtho.orthogonalProjectionOnto_comp_subtypeL
  statement: {U V : Submodule 𝕜 E}
  proof: by
  ext v; simp [orthogonalProjectionOnto_apply_of_mem_orthogonal <| h.symm v.prop]

@[deprecated (since := "2026-05-05")]
alias IsOrtho.orthogonalProjection_comp_subtypeL := IsOrtho.orthogonalProjectionOnto_comp_subtypeL

中文:
定理 IsOrtho.orthogonalProjectionOnto_comp_subtypeL
  结论: {U V : 子模 𝕜 E}
  证明: by
  ext v; simp [orthogonalProjectionOnto_apply_of_mem_orthogonal <| h.symm v.prop]

@[deprecated (since := "2026-05-05")]
alias IsOrtho.orthogonalProjection_comp_subtypeL := IsOrtho.orthogonalProjectionOnto_comp_subtypeL

Depends on / 依赖: h.symm, orthogonalProjectionOnto_apply_of_mem_orthogonal, v.prop
-/
theorem IsOrtho.orthogonalProjectionOnto_comp_subtypeL {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (h : U ⟂ V) : U.orthogonalProjectionOnto ∘L V.subtypeL = 0 := by
  ext v; simp [orthogonalProjectionOnto_apply_of_mem_orthogonal <| h.symm v.prop]

@[deprecated (since := "2026-05-05")]
alias IsOrtho.orthogonalProjection_comp_subtypeL := IsOrtho.orthogonalProjectionOnto_comp_subtypeL

/--
theorem `IsOrtho.starProjection_comp_starProjection` / 定理 `IsOrtho.starProjection_comp_starProjection`

English:
theorem IsOrtho.starProjection_comp_starProjection
  statement: {U V : Submodule 𝕜 E}
  proof: calc
  _ = U.subtypeL ∘L (U.orthogonalProjectionOnto ∘L V.subtypeL) ∘L V.orthogonalProjectionOnto := by
      simp only [starProjection, ContinuousLinearMap.comp_assoc]
    _ = 0 := by simp [h.orthogonalProjectionOnto_comp_subtypeL]

中文:
定理 IsOrtho.starProjection_comp_starProjection
  结论: {U V : 子模 𝕜 E}
  证明: calc
  _ = U.subtypeL ∘L (U.orthogonalProjectionOnto ∘L V.subtypeL) ∘L V.orthogonalProjectionOnto := by
      simp only [starProjection, ContinuousLinearMap.comp_assoc]
    _ = 0 := by simp [h.orthogonalProjectionOnto_comp_subtypeL]
-/
theorem IsOrtho.starProjection_comp_starProjection {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) :
    U.starProjection ∘L V.starProjection = 0 := calc
  _ = U.subtypeL ∘L (U.orthogonalProjectionOnto ∘L V.subtypeL) ∘L V.orthogonalProjectionOnto := by
      simp only [starProjection, ContinuousLinearMap.comp_assoc]
    _ = 0 := by simp [h.orthogonalProjectionOnto_comp_subtypeL]

/--
theorem `orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff` / 定理 `orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff`

English:
theorem orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff
  statement: {U V : Submodule 𝕜 E}
  proof: by
  refine ⟨fun h u hu v hv => ?_, Submodule.IsOrtho.orthogonalProjectionOnto_comp_subtypeL⟩
  convert starProjection_inner_eq_zero v u hu
  have : U.orthogonalProjectionOnto v = 0 := DFunLike.congr_fun h (⟨_, hv⟩ : V)
  rw [starProjection_apply]; rw [this]; rw [Submodule.coe_zero]; rw [sub_zero]



中文:
定理 orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff
  结论: {U V : 子模 𝕜 E}
  证明: by
  refine ⟨fun h u hu v hv => ?_, Submodule.IsOrtho.orthogonalProjectionOnto_comp_subtypeL⟩
  convert starProjection_inner_eq_zero v u hu
  have : U.orthogonalProjectionOnto v = 0 := DFunLike.congr_fun h (⟨_, hv⟩ : V)
  rw [starProjection_apply]; rw [this]; rw [Submodule.coe_zero]; rw [sub_zero]



Depends on / 依赖: DFunLike, DFunLike.congr_fun, IsOrtho, Submodule, Submodule.IsOrtho.orthogonalProjectionOnto_comp_subtypeL, Submodule.coe_zero, U.orthogonalProjectionOnto, coe_zero, congr_fun, convert, orthogonalProjectionOnto, orthogonalProjectionOnto_comp_subtypeL, starProjection_apply, starProjection_inner_eq_zero, sub_zero
-/
theorem orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] : U.orthogonalProjectionOnto ∘L V.subtypeL = 0 ↔ U ⟂ V := by
  refine ⟨fun h u hu v hv => ?_, Submodule.IsOrtho.orthogonalProjectionOnto_comp_subtypeL⟩
  convert starProjection_inner_eq_zero v u hu
  have : U.orthogonalProjectionOnto v = 0 := DFunLike.congr_fun h (⟨_, hv⟩ : V)
  rw [starProjection_apply]; rw [this]; rw [Submodule.coe_zero]; rw [sub_zero]

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_comp_subtypeL_eq_zero_iff :=
  orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff

/--
theorem `starProjection_comp_starProjection_eq_zero_iff` / 定理 `starProjection_comp_starProjection_eq_zero_iff`

English:
theorem starProjection_comp_starProjection_eq_zero_iff
  statement: {U V : Submodule 𝕜 E}
  proof: by
  refine ⟨fun h => ?_, fun h => h.starProjection_comp_starProjection⟩
  rw [← orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff]
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply, subtypeL_apply,
    starProjection_apply, zero_apply, coe_eq_zero] at h ⊢
  intro x
  simpa u

中文:
定理 starProjection_comp_starProjection_eq_zero_iff
  结论: {U V : 子模 𝕜 E}
  证明: by
  refine ⟨fun h => ?_, fun h => h.starProjection_comp_starProjection⟩
  rw [← orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff]
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply, subtypeL_apply,
    starProjection_apply, zero_apply, coe_eq_zero] at h ⊢
  intro x
  simpa u

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.ext_iff, coe_eq_zero, comp_apply, ext_iff, h.starProjection_comp_starProjection, orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff, starProjection_apply, starProjection_comp_starProjection, subtypeL_apply, zero_apply
-/
theorem starProjection_comp_starProjection_eq_zero_iff {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection ∘L V.starProjection = 0 ↔ U ⟂ V := by
  refine ⟨fun h => ?_, fun h => h.starProjection_comp_starProjection⟩
  rw [← orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff]
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply, subtypeL_apply,
    starProjection_apply, zero_apply, coe_eq_zero] at h ⊢
  intro x
  simpa using h (x : E)

/--
theorem `orthogonalProjectionOnto_orthogonal_apply_eq_zero` / 定理 `orthogonalProjectionOnto_orthogonal_apply_eq_zero`

English:
theorem orthogonalProjectionOnto_orthogonal_apply_eq_zero
  proof: orthogonalProjectionOnto_apply_of_mem_orthogonal (K.le_orthogonal_orthogonal hv)

@[deprecated (since := "2026-05-06")] alias orthogonalProjection_orthogonal_apply_eq_zero :=
  orthogonalProjectionOnto_orthogonal_apply_eq_zero

中文:
定理 orthogonalProjectionOnto_orthogonal_apply_eq_zero
  证明: orthogonalProjectionOnto_apply_of_mem_orthogonal (K.le_orthogonal_orthogonal hv)

@[deprecated (since := "2026-05-06")] alias orthogonalProjection_orthogonal_apply_eq_zero :=
  orthogonalProjectionOnto_orthogonal_apply_eq_zero

Depends on / 依赖: K.le_orthogonal_orthogonal, le_orthogonal_orthogonal, orthogonalProjectionOnto_apply_of_mem_orthogonal
-/
theorem orthogonalProjectionOnto_orthogonal_apply_eq_zero
    [Kᗮ.HasOrthogonalProjection] {v : E} (hv : v in K) : Kᗮ.orthogonalProjectionOnto v = 0 :=
  orthogonalProjectionOnto_apply_of_mem_orthogonal (K.le_orthogonal_orthogonal hv)

@[deprecated (since := "2026-05-06")] alias orthogonalProjection_orthogonal_apply_eq_zero :=
  orthogonalProjectionOnto_orthogonal_apply_eq_zero

/--
theorem `starProjection_orthogonal_apply_eq_zero` / 定理 `starProjection_orthogonal_apply_eq_zero`

English:
theorem starProjection_orthogonal_apply_eq_zero
  proof: by
  rw [starProjection_apply]; rw [coe_eq_zero]
  exact orthogonalProjectionOnto_orthogonal_apply_eq_zero hv

中文:
定理 starProjection_orthogonal_apply_eq_zero
  证明: by
  rw [starProjection_apply]; rw [coe_eq_zero]
  exact orthogonalProjectionOnto_orthogonal_apply_eq_zero hv

Depends on / 依赖: coe_eq_zero, orthogonalProjectionOnto_orthogonal_apply_eq_zero, starProjection_apply
-/
theorem starProjection_orthogonal_apply_eq_zero
    [Kᗮ.HasOrthogonalProjection] {v : E} (hv : v in K) :
    Kᗮ.starProjection v = 0 := by
  rw [starProjection_apply]; rw [coe_eq_zero]
  exact orthogonalProjectionOnto_orthogonal_apply_eq_zero hv

/--
theorem `orthogonalProjectionOnto_starProjection_of_le` / 定理 `orthogonalProjectionOnto_starProjection_of_le`

English:
theorem orthogonalProjectionOnto_starProjection_of_le
  statement: {U V : Submodule 𝕜 E}
  proof: Eq.symm by
    simpa only [sub_eq_zero, map_sub] using
      orthogonalProjectionOnto_apply_of_mem_orthogonal
        (Submodule.orthogonal_le h (sub_starProjection_mem_orthogonal x))

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_starProjection_of_le := orthogonalProjectionOnto_s

中文:
定理 orthogonalProjectionOnto_starProjection_of_le
  结论: {U V : 子模 𝕜 E}
  证明: Eq.symm by
    simpa only [sub_eq_zero, map_sub] using
      orthogonalProjectionOnto_apply_of_mem_orthogonal
        (Submodule.orthogonal_le h (sub_starProjection_mem_orthogonal x))

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_starProjection_of_le := orthogonalProjectionOnto_s

Depends on / 依赖: Eq.symm, Submodule, Submodule.orthogonal_le, map_sub, orthogonalProjectionOnto_apply_of_mem_orthogonal, orthogonal_le, sub_eq_zero, sub_starProjection_mem_orthogonal
-/
theorem orthogonalProjectionOnto_starProjection_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U <= V) (x : E) :
    U.orthogonalProjectionOnto (V.starProjection x) = U.orthogonalProjectionOnto x :=
Eq.symm by
    simpa only [sub_eq_zero, map_sub] using
      orthogonalProjectionOnto_apply_of_mem_orthogonal
        (Submodule.orthogonal_le h (sub_starProjection_mem_orthogonal x))

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_starProjection_of_le := orthogonalProjectionOnto_starProjection_of_le

/--
theorem `starProjection_comp_starProjection_of_le` / 定理 `starProjection_comp_starProjection_of_le`

English:
theorem starProjection_comp_starProjection_of_le
  statement: {U V : Submodule 𝕜 E}
  proof: ContinuousLinearMap.ext fun _ => by
  nth_rw 1 [starProjection]
  simp [orthogonalProjectionOnto_starProjection_of_le h]

中文:
定理 starProjection_comp_starProjection_of_le
  结论: {U V : 子模 𝕜 E}
  证明: ContinuousLinearMap.ext fun _ => by
  nth_rw 1 [starProjection]
  simp [orthogonalProjectionOnto_starProjection_of_le h]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, nth_rw, orthogonalProjectionOnto_starProjection_of_le, starProjection
-/
theorem starProjection_comp_starProjection_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U <= V) :
    U.starProjection ∘L V.starProjection = U.starProjection := ContinuousLinearMap.ext fun _ => by
  nth_rw 1 [starProjection]
  simp [orthogonalProjectionOnto_starProjection_of_le h]

open ContinuousLinearMap in
/--
theorem `_root_.ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range` / 定理 `_root_.ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range`

English:
theorem _root_.ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
  statement: [CompleteSpace E]
  proof: have := hp.isClosed_range.completeSpace_coe
  .ofCompleteSpace _

中文:
定理 _root_.连续线性映射.IsIdempotentElem.hasOrthogonalProjection_range
  结论: [完备空间 E]
  证明: have := hp.isClosed_range.completeSpace_coe
  .ofCompleteSpace _

Depends on / 依赖: completeSpace_coe, hp.isClosed_range.completeSpace_coe, isClosed_range, ofCompleteSpace
-/
theorem _root_.ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range [CompleteSpace E]
    {p : E ->L[𝕜] E} (hp : IsIdempotentElem p) : p.range.HasOrthogonalProjection :=
  have := hp.isClosed_range.completeSpace_coe
  .ofCompleteSpace _

open LinearMap in
/--
theorem `_root_.LinearMap.IsSymmetricProjection.hasOrthogonalProjection_range` / 定理 `_root_.LinearMap.IsSymmetricProjection.hasOrthogonalProjection_range`

English:
theorem _root_.LinearMap.IsSymmetricProjection.hasOrthogonalProjection_range
  proof: ⟨fun v => ⟨p v, by
    simp [hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hp.isSymmetric,
      ← Module.End.mul_apply, hp.isIdempotentElem.eq]⟩⟩

中文:
定理 _root_.线性映射.是SymmetricProjection.hasOrthogonalProjection_range
  证明: ⟨fun v => ⟨p v, by
    simp [hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hp.isSymmetric,
      ← Module.End.mul_apply, hp.isIdempotentElem.eq]⟩⟩

Depends on / 依赖: Module, Module.End.mul_apply, hp.isIdempotentElem.eq, hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp, hp.isSymmetric, isIdempotentElem, isSymmetric, isSymmetric_iff_orthogonal_range, mul_apply
-/
theorem _root_.LinearMap.IsSymmetricProjection.hasOrthogonalProjection_range
    {p : E ->ₗ[𝕜] E} (hp : p.IsSymmetricProjection) :
    (range p).HasOrthogonalProjection :=
  ⟨fun v => ⟨p v, by
    simp [hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hp.isSymmetric,
      ← Module.End.mul_apply, hp.isIdempotentElem.eq]⟩⟩

/--
theorem `orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero` / 定理 `orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero`

English:
theorem orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero
  given: (v : E)
  proof: orthogonalProjectionOnto_orthogonal_apply_eq_zero
    (Submodule.mem_span_singleton_self v)

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_orthogonalComplement_singleton_eq_zero :=
  orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero

中文:
定理 orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero
  条件: (v : E)
  证明: orthogonalProjectionOnto_orthogonal_apply_eq_zero
    (Submodule.mem_span_singleton_self v)

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_orthogonalComplement_singleton_eq_zero :=
  orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero

Depends on / 依赖: Submodule, Submodule.mem_span_singleton_self, mem_span_singleton_self, orthogonalProjectionOnto_orthogonal_apply_eq_zero
-/
theorem orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero (v : E) :
    (𝕜 ∙ v)ᗮ.orthogonalProjectionOnto v = 0 :=
  orthogonalProjectionOnto_orthogonal_apply_eq_zero
    (Submodule.mem_span_singleton_self v)

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_orthogonalComplement_singleton_eq_zero :=
  orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero

/--
theorem `starProjection_orthogonalComplement_singleton_eq_zero` / 定理 `starProjection_orthogonalComplement_singleton_eq_zero`

English:
theorem starProjection_orthogonalComplement_singleton_eq_zero
  given: (v : E)
  proof: by
  rw [starProjection_apply]; rw [coe_eq_zero]
  exact orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero v

中文:
定理 starProjection_orthogonalComplement_singleton_eq_zero
  条件: (v : E)
  证明: by
  rw [starProjection_apply]; rw [coe_eq_zero]
  exact orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero v

Depends on / 依赖: coe_eq_zero, orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, starProjection_apply
-/
theorem starProjection_orthogonalComplement_singleton_eq_zero (v : E) :
    (𝕜 ∙ v)ᗮ.starProjection v = 0 := by
  rw [starProjection_apply]; rw [coe_eq_zero]
  exact orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero v

/--
theorem `starProjection_add_starProjection_orthogonal` / 定理 `starProjection_add_starProjection_orthogonal`

English:
theorem starProjection_add_starProjection_orthogonal
  statement: [K.HasOrthogonalProjection]
  proof: by
  simp

中文:
定理 starProjection_add_starProjection_orthogonal
  结论: [K.有OrthogonalProjection]
  证明: by
  simp
-/
theorem starProjection_add_starProjection_orthogonal [K.HasOrthogonalProjection]
    (w : E) : K.starProjection w + Kᗮ.starProjection w = w := by
  simp

/--
theorem `norm_sq_eq_add_norm_sq_projection` / 定理 `norm_sq_eq_add_norm_sq_projection`

English:
theorem norm_sq_eq_add_norm_sq_projection
  given: (x : E) (S : Submodule 𝕜 E) [S.HasOrthogonalProjection]
  proof: calc
    ‖x‖ ^ 2 = ‖S.starProjection x + Sᗮ.starProjection x‖ ^ 2 := by
      rw [starProjection_add_starProjection_orthogonal]
    _ = ‖S.orthogonalProjectionOnto x‖ ^ 2 + ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2 := by
      simp only [sq]
exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
  

中文:
定理 norm_sq_eq_add_norm_sq_projection
  条件: (x : E) (S : 子模 𝕜 E) [S.有OrthogonalProjection]
  证明: calc
    ‖x‖ ^ 2 = ‖S.starProjection x + Sᗮ.starProjection x‖ ^ 2 := by
      rw [starProjection_add_starProjection_orthogonal]
    _ = ‖S.orthogonalProjectionOnto x‖ ^ 2 + ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2 := by
      simp only [sq]
exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
  

Depends on / 依赖: S.mem_orthogonal, S.orthogonalProjectionOnto, S.starProjection, mem_orthogonal, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, orthogonalProjectionOnto, starProjection, starProjection_add_starProjection_orthogonal
-/
theorem norm_sq_eq_add_norm_sq_projection (x : E) (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    ‖x‖ ^ 2 = ‖S.orthogonalProjectionOnto x‖ ^ 2 + ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2 :=
  calc
    ‖x‖ ^ 2 = ‖S.starProjection x + Sᗮ.starProjection x‖ ^ 2 := by
      rw [starProjection_add_starProjection_orthogonal]
    _ = ‖S.orthogonalProjectionOnto x‖ ^ 2 + ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2 := by
      simp only [sq]
exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
        (S.mem_orthogonal _).1 (Sᗮ.orthogonalProjectionOnto x).2 _ (S.orthogonalProjectionOnto x).2

/--
theorem `norm_sq_eq_add_norm_sq_starProjection` / 定理 `norm_sq_eq_add_norm_sq_starProjection`

English:
theorem norm_sq_eq_add_norm_sq_starProjection
  statement: (x : E) (S : Submodule 𝕜 E)
  proof: norm_sq_eq_add_norm_sq_projection x S

中文:
定理 norm_sq_eq_add_norm_sq_starProjection
  结论: (x : E) (S : 子模 𝕜 E)
  证明: norm_sq_eq_add_norm_sq_projection x S

Depends on / 依赖: norm_sq_eq_add_norm_sq_projection
-/
theorem norm_sq_eq_add_norm_sq_starProjection (x : E) (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] :
    ‖x‖ ^ 2 = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.starProjection x‖ ^ 2 :=
  norm_sq_eq_add_norm_sq_projection x S

/--
theorem `mem_iff_norm_starProjection` / 定理 `mem_iff_norm_starProjection`

English:
theorem mem_iff_norm_starProjection
  statement: (U : Submodule 𝕜 E)
  proof: by
  refine ⟨fun h => norm_starProjection_apply _ h, fun h => ?_⟩
  simpa [h, sub_eq_zero, eq_comm (a := v), starProjection_eq_self_iff] using
    U.norm_sq_eq_add_norm_sq_starProjection v

中文:
定理 mem_iff_norm_starProjection
  结论: (U : 子模 𝕜 E)
  证明: by
  refine ⟨fun h => norm_starProjection_apply _ h, fun h => ?_⟩
  simpa [h, sub_eq_zero, eq_comm (a := v), starProjection_eq_self_iff] using
    U.norm_sq_eq_add_norm_sq_starProjection v

Depends on / 依赖: U.norm_sq_eq_add_norm_sq_starProjection, eq_comm, norm_sq_eq_add_norm_sq_starProjection, norm_starProjection_apply, starProjection_eq_self_iff, sub_eq_zero
-/
theorem mem_iff_norm_starProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (v : E) :
    v in U ↔ ‖U.starProjection v‖ = ‖v‖ := by
  refine ⟨fun h => norm_starProjection_apply _ h, fun h => ?_⟩
  simpa [h, sub_eq_zero, eq_comm (a := v), starProjection_eq_self_iff] using
    U.norm_sq_eq_add_norm_sq_starProjection v

/--
theorem `id_eq_sum_starProjection_self_orthogonalComplement` / 定理 `id_eq_sum_starProjection_self_orthogonalComplement`

English:
theorem id_eq_sum_starProjection_self_orthogonalComplement
  given: [K.HasOrthogonalProjection]
  proof: by
  ext w
  exact (K.starProjection_add_starProjection_orthogonal w).symm

中文:
定理 id_eq_sum_starProjection_self_orthogonalComplement
  条件: [K.有OrthogonalProjection]
  证明: by
  ext w
  exact (K.starProjection_add_starProjection_orthogonal w).symm

Depends on / 依赖: K.starProjection_add_starProjection_orthogonal, starProjection_add_starProjection_orthogonal
-/
theorem id_eq_sum_starProjection_self_orthogonalComplement [K.HasOrthogonalProjection] :
    ContinuousLinearMap.id 𝕜 E =
      K.starProjection + Kᗮ.starProjection := by
  ext w
  exact (K.starProjection_add_starProjection_orthogonal w).symm

-- The priority should be higher than `Submodule.coe_inner`.
@[simp high]
/--
theorem `inner_orthogonalProjectionOnto_eq_of_mem_right` / 定理 `inner_orthogonalProjectionOnto_eq_of_mem_right`

English:
theorem inner_orthogonalProjectionOnto_eq_of_mem_right
  given: [K.HasOrthogonalProjection] (u : K) (v : E)
  proof: calc
    ⟪K.orthogonalProjectionOnto v, u⟫ = ⟪K.starProjection v, u⟫ := K.coe_inner _ _
    _ = ⟪K.starProjection v, u⟫ + ⟪v - K.starProjection v, u⟫ := by
      rw [starProjection_inner_eq_zero _ _ (Submodule.coe_mem _)]; rw [add_zero]
    _ = ⟪v, u⟫ := by rw [← inner_add_left, add_sub_cancel]

@[d

中文:
定理 inner_orthogonalProjectionOnto_eq_of_mem_right
  条件: [K.有OrthogonalProjection] (u : K) (v : E)
  证明: calc
    ⟪K.orthogonalProjectionOnto v, u⟫ = ⟪K.starProjection v, u⟫ := K.coe_inner _ _
    _ = ⟪K.starProjection v, u⟫ + ⟪v - K.starProjection v, u⟫ := by
      rw [starProjection_inner_eq_zero _ _ (Submodule.coe_mem _)]; rw [add_zero]
    _ = ⟪v, u⟫ := by rw [← inner_add_left, add_sub_cancel]

@[d

Depends on / 依赖: K.coe_inner, K.orthogonalProjectionOnto, K.starProjection, Submodule, Submodule.coe_mem, add_sub_cancel, add_zero, coe_inner, coe_mem, inner_add_left, orthogonalProjectionOnto, starProjection, starProjection_inner_eq_zero
-/
theorem inner_orthogonalProjectionOnto_eq_of_mem_right [K.HasOrthogonalProjection] (u : K) (v : E) :
    ⟪K.orthogonalProjectionOnto v, u⟫ = ⟪v, u⟫ :=
  calc
    ⟪K.orthogonalProjectionOnto v, u⟫ = ⟪K.starProjection v, u⟫ := K.coe_inner _ _
    _ = ⟪K.starProjection v, u⟫ + ⟪v - K.starProjection v, u⟫ := by
      rw [starProjection_inner_eq_zero _ _ (Submodule.coe_mem _)]; rw [add_zero]
    _ = ⟪v, u⟫ := by rw [← inner_add_left, add_sub_cancel]

@[deprecated (since := "2026-05-05")]
alias inner_orthogonalProjection_eq_of_mem_right := inner_orthogonalProjectionOnto_eq_of_mem_right

-- The priority should be higher than `Submodule.coe_inner`.
@[simp high]
/--
theorem `inner_orthogonalProjectionOnto_eq_of_mem_left` / 定理 `inner_orthogonalProjectionOnto_eq_of_mem_left`

English:
theorem inner_orthogonalProjectionOnto_eq_of_mem_left
  given: [K.HasOrthogonalProjection] (u : K) (v : E)
  proof: by
  rw [← inner_conj_symm]; rw [← inner_conj_symm (u : E)]; rw [inner_orthogonalProjectionOnto_eq_of_mem_right]

@[deprecated (since := "2026-05-05")]
alias inner_orthogonalProjection_eq_of_mem_left := inner_orthogonalProjectionOnto_eq_of_mem_left

中文:
定理 inner_orthogonalProjectionOnto_eq_of_mem_left
  条件: [K.有OrthogonalProjection] (u : K) (v : E)
  证明: by
  rw [← inner_conj_symm]; rw [← inner_conj_symm (u : E)]; rw [inner_orthogonalProjectionOnto_eq_of_mem_right]

@[deprecated (since := "2026-05-05")]
alias inner_orthogonalProjection_eq_of_mem_left := inner_orthogonalProjectionOnto_eq_of_mem_left

Depends on / 依赖: inner_conj_symm, inner_orthogonalProjectionOnto_eq_of_mem_right
-/
theorem inner_orthogonalProjectionOnto_eq_of_mem_left [K.HasOrthogonalProjection] (u : K) (v : E) :
    ⟪u, K.orthogonalProjectionOnto v⟫ = ⟪(u : E), v⟫ := by
  rw [← inner_conj_symm]; rw [← inner_conj_symm (u : E)]; rw [inner_orthogonalProjectionOnto_eq_of_mem_right]

@[deprecated (since := "2026-05-05")]
alias inner_orthogonalProjection_eq_of_mem_left := inner_orthogonalProjectionOnto_eq_of_mem_left

variable (K)

/--
theorem `inner_starProjection_left_eq_right` / 定理 `inner_starProjection_left_eq_right`

English:
theorem inner_starProjection_left_eq_right
  given: [K.HasOrthogonalProjection] (u v : E)
  proof: by
  simp_rw [starProjection_apply, ← inner_orthogonalProjectionOnto_eq_of_mem_left,
    inner_orthogonalProjectionOnto_eq_of_mem_right]

中文:
定理 inner_starProjection_left_eq_right
  条件: [K.有OrthogonalProjection] (u v : E)
  证明: by
  simp_rw [starProjection_apply, ← inner_orthogonalProjectionOnto_eq_of_mem_left,
    inner_orthogonalProjectionOnto_eq_of_mem_right]

Depends on / 依赖: inner_orthogonalProjectionOnto_eq_of_mem_left, inner_orthogonalProjectionOnto_eq_of_mem_right, simp_rw, starProjection_apply
-/
theorem inner_starProjection_left_eq_right [K.HasOrthogonalProjection] (u v : E) :
    ⟪K.starProjection u, v⟫ = ⟪u, K.starProjection v⟫ := by
  simp_rw [starProjection_apply, ← inner_orthogonalProjectionOnto_eq_of_mem_left,
    inner_orthogonalProjectionOnto_eq_of_mem_right]

/--
theorem `starProjection_isSymmetric` / 定理 `starProjection_isSymmetric`

English:
theorem starProjection_isSymmetric
  given: [K.HasOrthogonalProjection]
  proof: inner_starProjection_left_eq_right K

中文:
定理 starProjection_isSymmetric
  条件: [K.有OrthogonalProjection]
  证明: inner_starProjection_left_eq_right K

Depends on / 依赖: inner_starProjection_left_eq_right
-/
theorem starProjection_isSymmetric [K.HasOrthogonalProjection] :
    (K.starProjection : E ->ₗ[𝕜] E).IsSymmetric :=
  inner_starProjection_left_eq_right K

open ContinuousLinearMap in
/-- `U.starProjection` is a symmetric projection. -/
@[simp]
/--
theorem `isSymmetricProjection_starProjection` / 定理 `isSymmetricProjection_starProjection`

English:
theorem isSymmetricProjection_starProjection
  proof: ⟨U.isIdempotentElem_starProjection.toLinearMap, U.starProjection_isSymmetric⟩

中文:
定理 isSymmetricProjection_starProjection
  证明: ⟨U.isIdempotentElem_starProjection.toLinearMap, U.starProjection_isSymmetric⟩

Depends on / 依赖: U.isIdempotentElem_starProjection.toLinearMap, U.starProjection_isSymmetric, isIdempotentElem_starProjection, starProjection_isSymmetric, toLinearMap
-/
theorem isSymmetricProjection_starProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.starProjection.IsSymmetricProjection :=
  ⟨U.isIdempotentElem_starProjection.toLinearMap, U.starProjection_isSymmetric⟩

open LinearMap in
/--
theorem `_root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range` / 定理 `_root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range`

English:
theorem _root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range
  given: {p : E ->ₗ[𝕜] E}
  proof: by
  refine ⟨fun hp => ?_, fun ⟨h, hp⟩ => hp ▸ isSymmetricProjection_starProjection _⟩
  have : (LinearMap.range p).HasOrthogonalProjection := hp.hasOrthogonalProjection_range
  refine ⟨this, Eq.symm ?_⟩
  ext x
  refine Submodule.eq_starProjection_of_mem_orthogonal (by simp) ?_
  rw [hp.isIdempoten

中文:
定理 _root_.线性映射.isSymmetricProjection_iff_eq_coe_starProjection_range
  条件: {p : E ->ₗ[𝕜] E}
  证明: by
  refine ⟨fun hp => ?_, fun ⟨h, hp⟩ => hp ▸ isSymmetricProjection_starProjection _⟩
  have : (LinearMap.range p).HasOrthogonalProjection := hp.hasOrthogonalProjection_range
  refine ⟨this, Eq.symm ?_⟩
  ext x
  refine Submodule.eq_starProjection_of_mem_orthogonal (by simp) ?_
  rw [hp.isIdempoten

Depends on / 依赖: Eq.symm, HasOrthogonalProjection, LinearMap, LinearMap.range, Submodule, Submodule.eq_starProjection_of_mem_orthogonal, eq_starProjection_of_mem_orthogonal, hasOrthogonalProjection_range, hp.hasOrthogonalProjection_range, hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp, hp.isIdempotentElem.mul_one_sub_self, hp.isSymmetric, isIdempotentElem, isSymmetric, isSymmetricProjection_starProjection, isSymmetric_iff_orthogonal_range, mul_one_sub_self
-/
theorem _root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range {p : E ->ₗ[𝕜] E} :
    p.IsSymmetricProjection ↔ exists (_ : (LinearMap.range p).HasOrthogonalProjection),
    p = (LinearMap.range p).starProjection := by
  refine ⟨fun hp => ?_, fun ⟨h, hp⟩ => hp ▸ isSymmetricProjection_starProjection _⟩
  have : (LinearMap.range p).HasOrthogonalProjection := hp.hasOrthogonalProjection_range
  refine ⟨this, Eq.symm ?_⟩
  ext x
  refine Submodule.eq_starProjection_of_mem_orthogonal (by simp) ?_
  rw [hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hp.isSymmetric]
  simpa using congr($hp.isIdempotentElem.mul_one_sub_self x)

/--
lemma `_root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection` / 引理 `_root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection`

English:
lemma _root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection
  given: {p : E ->ₗ[𝕜] E}
  proof: ⟨fun h => ⟨LinearMap.range p, p.isSymmetricProjection_iff_eq_coe_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; exact isSymmetricProjection_starProjection _⟩

中文:
引理 _root_.线性映射.isSymmetricProjection_iff_eq_coe_starProjection
  条件: {p : E ->ₗ[𝕜] E}
  证明: ⟨fun h => ⟨LinearMap.range p, p.isSymmetricProjection_iff_eq_coe_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; exact isSymmetricProjection_starProjection _⟩

Depends on / 依赖: LinearMap, LinearMap.range, isSymmetricProjection_iff_eq_coe_starProjection_range, isSymmetricProjection_starProjection, p.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
-/
lemma _root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection {p : E ->ₗ[𝕜] E} :
    p.IsSymmetricProjection
      ↔ exists (K : Submodule 𝕜 E) (_ : K.HasOrthogonalProjection), p = K.starProjection :=
  ⟨fun h => ⟨LinearMap.range p, p.isSymmetricProjection_iff_eq_coe_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; exact isSymmetricProjection_starProjection _⟩

/--
theorem `starProjection_apply_eq_zero_iff` / 定理 `starProjection_apply_eq_zero_iff`

English:
theorem starProjection_apply_eq_zero_iff
  given: [K.HasOrthogonalProjection] {v : E}
  proof: by
  refine ⟨fun h w hw => ?_, fun hv => ?_⟩
  · rw [← starProjection_eq_self_iff.mpr hw, inner_starProjection_left_eq_right, h,
      inner_zero_right]
  · simp [starProjection_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hv]

中文:
定理 starProjection_apply_eq_zero_iff
  条件: [K.有OrthogonalProjection] {v : E}
  证明: by
  refine ⟨fun h w hw => ?_, fun hv => ?_⟩
  · rw [← starProjection_eq_self_iff.mpr hw, inner_starProjection_left_eq_right, h,
      inner_zero_right]
  · simp [starProjection_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hv]

Depends on / 依赖: inner_starProjection_left_eq_right, inner_zero_right, orthogonalProjectionOnto_apply_of_mem_orthogonal, starProjection_apply, starProjection_eq_self_iff, starProjection_eq_self_iff.mpr
-/
theorem starProjection_apply_eq_zero_iff [K.HasOrthogonalProjection] {v : E} :
    K.starProjection v = 0 ↔ v in Kᗮ := by
  refine ⟨fun h w hw => ?_, fun hv => ?_⟩
  · rw [← starProjection_eq_self_iff.mpr hw, inner_starProjection_left_eq_right, h,
      inner_zero_right]
  · simp [starProjection_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hv]

open RCLike

/--
lemma `re_inner_starProjection_eq_normSq` / 引理 `re_inner_starProjection_eq_normSq`

English:
lemma re_inner_starProjection_eq_normSq
  given: [K.HasOrthogonalProjection] (v : E)
  proof: by
  rw [starProjection_apply]; rw [re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]; rw [div_eq_iff (NeZero.ne' 2).symm]; rw [pow_two]; rw [add_sub_assoc]; rw [← eq_sub_iff_add_eq']; rw [coe_norm]; rw [← mul_sub_one]; rw [show (2 : Real) - 1 = 1 by norm_num]; rw [mul_one];

中文:
引理 re_inner_starProjection_eq_normSq
  条件: [K.有OrthogonalProjection] (v : E)
  证明: by
  rw [starProjection_apply]; rw [re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]; rw [div_eq_iff (NeZero.ne' 2).symm]; rw [pow_two]; rw [add_sub_assoc]; rw [← eq_sub_iff_add_eq']; rw [coe_norm]; rw [← mul_sub_one]; rw [show (2 : Real) - 1 = 1 by norm_num]; rw [mul_one];

Depends on / 依赖: K.norm_sq_eq_add_norm_sq_starProjection, NeZero, NeZero.ne, add_comm, add_sub_assoc, coe_norm, div_eq_iff, eq_sub_iff_add_eq, mul_one, mul_sub_one, norm_sq_eq_add_norm_sq_starProjection, norm_sub_rev, pow_two, re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, starProjection_apply, sub_eq_iff_eq_add
-/
lemma re_inner_starProjection_eq_normSq [K.HasOrthogonalProjection] (v : E) :
    re ⟪K.starProjection v, v⟫ = ‖K.orthogonalProjectionOnto v‖ ^ 2 := by
  rw [starProjection_apply]; rw [re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]; rw [div_eq_iff (NeZero.ne' 2).symm]; rw [pow_two]; rw [add_sub_assoc]; rw [← eq_sub_iff_add_eq']; rw [coe_norm]; rw [← mul_sub_one]; rw [show (2 : Real) - 1 = 1 by norm_num]; rw [mul_one]; rw [sub_eq_iff_eq_add']; rw [norm_sub_rev]
  simpa [sq, add_comm] using K.norm_sq_eq_add_norm_sq_starProjection v

@[deprecated norm_sq_eq_add_norm_sq_starProjection (since := "2026-06-10")]
/--
theorem `orthogonalProjectionFn_norm_sq` / 定理 `orthogonalProjectionFn_norm_sq`

English:
theorem orthogonalProjectionFn_norm_sq
  given: [K.HasOrthogonalProjection] (v : E)
  proof: by
  simpa [sq, add_comm] using K.norm_sq_eq_add_norm_sq_starProjection v

中文:
定理 orthogonalProjectionFn_norm_sq
  条件: [K.有OrthogonalProjection] (v : E)
  证明: by
  simpa [sq, add_comm] using K.norm_sq_eq_add_norm_sq_starProjection v

Depends on / 依赖: K.norm_sq_eq_add_norm_sq_starProjection, add_comm, norm_sq_eq_add_norm_sq_starProjection
-/
theorem orthogonalProjectionFn_norm_sq [K.HasOrthogonalProjection] (v : E) :
    ‖v‖ * ‖v‖ = ‖v - K.orthogonalProjectionFn v‖ * ‖v - K.orthogonalProjectionFn v‖ +
      ‖K.orthogonalProjectionFn v‖ * ‖K.orthogonalProjectionFn v‖ := by
  simpa [sq, add_comm] using K.norm_sq_eq_add_norm_sq_starProjection v

/--
lemma `re_inner_starProjection_nonneg` / 引理 `re_inner_starProjection_nonneg`

English:
lemma re_inner_starProjection_nonneg
  given: [K.HasOrthogonalProjection] (v : E)
  proof: by
  rw [re_inner_starProjection_eq_normSq K v]
  exact sq_nonneg ‖K.orthogonalProjectionOnto v‖

中文:
引理 re_inner_starProjection_nonneg
  条件: [K.有OrthogonalProjection] (v : E)
  证明: by
  rw [re_inner_starProjection_eq_normSq K v]
  exact sq_nonneg ‖K.orthogonalProjectionOnto v‖

Depends on / 依赖: K.orthogonalProjectionOnto, orthogonalProjectionOnto, re_inner_starProjection_eq_normSq, sq_nonneg
-/
lemma re_inner_starProjection_nonneg [K.HasOrthogonalProjection] (v : E) :
    0 <= re ⟪K.starProjection v, v⟫ := by
  rw [re_inner_starProjection_eq_normSq K v]
  exact sq_nonneg ‖K.orthogonalProjectionOnto v‖

end

end Submodule
