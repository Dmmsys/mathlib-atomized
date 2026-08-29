/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Reflection

A linear isometry equivalence `K.reflection : E ≃ₗᵢ[𝕜] E` in constructed, by choosing
for each `u : E`, `K.reflection u = 2 • K.starProjection u - u`.
-/

@[expose] public section

noncomputable section

namespace Submodule

section reflection

open Submodule RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : Submodule 𝕜 E)
variable [K.HasOrthogonalProjection]

/--
Definition of `reflectionLinearEquiv` / `reflectionLinearEquiv` 的定义

English:
definition reflectionLinearEquiv
  signature: : E ≃ₗ[𝕜] E
  body: LinearEquiv.ofInvolutive
    (2 • (K.starProjection.toLinearMap) - LinearMap.id) fun x => by
    simp [two_smul, starProjection_eq_self_iff.mpr]

中文:
定义 reflectionLinearEquiv
  签名: : E ≃ₗ[𝕜] E
  定义体: LinearEquiv.ofInvolutive
    (2 • (K.starProjection.toLinearMap) - LinearMap.id) fun x => by
    simp [two_smul, starProjection_eq_self_iff.mpr]

Depends on / 依赖: K.starProjection.toLinearMap, LinearEquiv, LinearEquiv.ofInvolutive, LinearMap, LinearMap.id, ofInvolutive, starProjection, starProjection_eq_self_iff, starProjection_eq_self_iff.mpr, toLinearMap, two_smul
-/
def reflectionLinearEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInvolutive
    (2 • (K.starProjection.toLinearMap) - LinearMap.id) fun x => by
    simp [two_smul, starProjection_eq_self_iff.mpr]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `reflection` / `reflection` 的定义

English:
definition reflection
  signature: : E ≃ₗᵢ[𝕜] E
  body: { K.reflectionLinearEquiv with
    norm_map' := by
      intro x
      let w : K := K.orthogonalProjectionOnto x
      let v := x - w
      have : ⟪v, w⟫ = 0 := starProjection_inner_eq_zero x w w.2
      convert norm_sub_eq_norm_add this
      · dsimp [reflectionLinearEquiv, v, w]
        abel
     

中文:
定义 reflection
  签名: : E ≃ₗᵢ[𝕜] E
  定义体: { K.reflectionLinearEquiv with
    norm_map' := by
      intro x
      let w : K := K.orthogonalProjectionOnto x
      let v := x - w
      have : ⟪v, w⟫ = 0 := starProjection_inner_eq_zero x w w.2
      convert norm_sub_eq_norm_add this
      · dsimp [reflectionLinearEquiv, v, w]
        abel
     

Depends on / 依赖: K.orthogonalProjectionOnto, K.reflectionLinearEquiv, add_sub_cancel, convert, norm_map, norm_sub_eq_norm_add, orthogonalProjectionOnto, reflectionLinearEquiv, starProjection_inner_eq_zero
-/
def reflection : E ≃ₗᵢ[𝕜] E :=
  { K.reflectionLinearEquiv with
    norm_map' := by
      intro x
      let w : K := K.orthogonalProjectionOnto x
      let v := x - w
      have : ⟪v, w⟫ = 0 := starProjection_inner_eq_zero x w w.2
      convert norm_sub_eq_norm_add this
      · dsimp [reflectionLinearEquiv, v, w]
        abel
      · simp only [v, add_sub_cancel] }

variable {K}

/--
theorem `reflection_apply` / 定理 `reflection_apply`

English:
theorem reflection_apply
  given: (p : E)
  statement: K.reflection p = 2 • K.starProjection p - p
  proof: rfl

中文:
定理 reflection_apply
  条件: (p : E)
  结论: K.reflection p = 2 • K.starProjection p - p
  证明: rfl
-/
theorem reflection_apply (p : E) : K.reflection p = 2 • K.starProjection p - p :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
/--
theorem `reflection_symm` / 定理 `reflection_symm`

English:
theorem reflection_symm
  statement: K.reflection.symm = K.reflection
  proof: rfl

中文:
定理 reflection_symm
  结论: K.reflection.symm = K.reflection
  证明: rfl
-/
theorem reflection_symm : K.reflection.symm = K.reflection :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
/--
theorem `reflection_inv` / 定理 `reflection_inv`

English:
theorem reflection_inv
  statement: K.reflection⁻¹ = K.reflection
  proof: rfl

中文:
定理 reflection_inv
  结论: K.reflection⁻¹ = K.reflection
  证明: rfl
-/
theorem reflection_inv : K.reflection⁻¹ = K.reflection :=
  rfl

variable (K)

/-- Reflecting twice in the same subspace. -/
@[simp]
/--
theorem `reflection_reflection` / 定理 `reflection_reflection`

English:
theorem reflection_reflection
  given: (p : E)
  statement: K.reflection (K.reflection p) = p
  proof: K.reflection.left_inv p

中文:
定理 reflection_reflection
  条件: (p : E)
  结论: K.reflection (K.reflection p) = p
  证明: K.reflection.left_inv p

Depends on / 依赖: K.reflection.left_inv, left_inv, reflection
-/
theorem reflection_reflection (p : E) : K.reflection (K.reflection p) = p :=
  K.reflection.left_inv p

/--
theorem `reflection_involutive` / 定理 `reflection_involutive`

English:
theorem reflection_involutive
  statement: Function.Involutive K.reflection
  proof: K.reflection_reflection

中文:
定理 reflection_involutive
  结论: Function.Involutive K.reflection
  证明: K.reflection_reflection

Depends on / 依赖: K.reflection_reflection, reflection_reflection
-/
theorem reflection_involutive : Function.Involutive K.reflection :=
  K.reflection_reflection

/-- Reflection is involutive. -/
@[simp]
/--
theorem `reflection_trans_reflection` / 定理 `reflection_trans_reflection`

English:
theorem reflection_trans_reflection
  proof: LinearIsometryEquiv.ext reflection_involutive K

中文:
定理 reflection_trans_reflection
  证明: LinearIsometryEquiv.ext reflection_involutive K

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ext, reflection_involutive
-/
theorem reflection_trans_reflection :
    K.reflection.trans K.reflection = LinearIsometryEquiv.refl 𝕜 E :=
LinearIsometryEquiv.ext reflection_involutive K

/-- Reflection is involutive. -/
@[simp]
/--
theorem `reflection_mul_reflection` / 定理 `reflection_mul_reflection`

English:
theorem reflection_mul_reflection
  statement: K.reflection * K.reflection = 1
  proof: reflection_trans_reflection _

中文:
定理 reflection_mul_reflection
  结论: K.reflection * K.reflection = 1
  证明: reflection_trans_reflection _

Depends on / 依赖: reflection_trans_reflection
-/
theorem reflection_mul_reflection : K.reflection * K.reflection = 1 :=
  reflection_trans_reflection _
/--
theorem `reflection_orthogonal_apply` / 定理 `reflection_orthogonal_apply`

English:
theorem reflection_orthogonal_apply
  given: (v : E)
  statement: Kᗮ.reflection v = -K.reflection v
  proof: by
  simp [reflection_apply]; abel

中文:
定理 reflection_orthogonal_apply
  条件: (v : E)
  结论: Kᗮ.reflection v = -K.reflection v
  证明: by
  simp [reflection_apply]; abel

Depends on / 依赖: reflection_apply
-/
theorem reflection_orthogonal_apply (v : E) : Kᗮ.reflection v = -K.reflection v := by
  simp [reflection_apply]; abel

/--
theorem `reflection_orthogonal` / 定理 `reflection_orthogonal`

English:
theorem reflection_orthogonal
  statement: Kᗮ.reflection = .trans K.reflection (.neg _)
  proof: by
  ext; apply reflection_orthogonal_apply

中文:
定理 reflection_orthogonal
  结论: Kᗮ.reflection = .trans K.reflection (.neg _)
  证明: by
  ext; apply reflection_orthogonal_apply

Depends on / 依赖: reflection_orthogonal_apply
-/
theorem reflection_orthogonal : Kᗮ.reflection = .trans K.reflection (.neg _) := by
  ext; apply reflection_orthogonal_apply

variable {K}

/--
theorem `reflection_singleton_apply` / 定理 `reflection_singleton_apply`

English:
theorem reflection_singleton_apply
  given: (u v : E)
  proof: by
  rw [reflection_apply]; rw [starProjection_singleton]; rw [ofReal_pow]

中文:
定理 reflection_singleton_apply
  条件: (u v : E)
  证明: by
  rw [reflection_apply]; rw [starProjection_singleton]; rw [ofReal_pow]

Depends on / 依赖: ofReal_pow, reflection_apply, starProjection_singleton
-/
theorem reflection_singleton_apply (u v : E) :
    reflection (𝕜 ∙ u) v = 2 • (⟪u, v⟫ / ((‖u‖ : 𝕜) ^ 2)) • u - v := by
  rw [reflection_apply]; rw [starProjection_singleton]; rw [ofReal_pow]

/--
theorem `reflection_eq_self_iff` / 定理 `reflection_eq_self_iff`

English:
theorem reflection_eq_self_iff
  given: (x : E)
  statement: K.reflection x = x ↔ x in K
  proof: by
  rw [← starProjection_eq_self_iff]; rw [reflection_apply]; rw [sub_eq_iff_eq_add']; rw [← two_smul 𝕜]; rw [two_smul Nat]; rw [← two_smul 𝕜]
  refine (smul_right_injective E ?_).eq_iff
  exact two_ne_zero

中文:
定理 reflection_eq_self_iff
  条件: (x : E)
  结论: K.reflection x = x ↔ x in K
  证明: by
  rw [← starProjection_eq_self_iff]; rw [reflection_apply]; rw [sub_eq_iff_eq_add']; rw [← two_smul 𝕜]; rw [two_smul Nat]; rw [← two_smul 𝕜]
  refine (smul_right_injective E ?_).eq_iff
  exact two_ne_zero

Depends on / 依赖: eq_iff, reflection_apply, smul_right_injective, starProjection_eq_self_iff, sub_eq_iff_eq_add, two_ne_zero, two_smul
-/
theorem reflection_eq_self_iff (x : E) : K.reflection x = x ↔ x in K := by
  rw [← starProjection_eq_self_iff]; rw [reflection_apply]; rw [sub_eq_iff_eq_add']; rw [← two_smul 𝕜]; rw [two_smul Nat]; rw [← two_smul 𝕜]
  refine (smul_right_injective E ?_).eq_iff
  exact two_ne_zero

/--
theorem `reflection_mem_subspace_eq_self` / 定理 `reflection_mem_subspace_eq_self`

English:
theorem reflection_mem_subspace_eq_self
  given: {x : E} (hx : x in K)
  statement: K.reflection x = x
  proof: (reflection_eq_self_iff x).mpr hx

中文:
定理 reflection_mem_subspace_eq_self
  条件: {x : E} (hx : x in K)
  结论: K.reflection x = x
  证明: (reflection_eq_self_iff x).mpr hx

Depends on / 依赖: reflection_eq_self_iff
-/
theorem reflection_mem_subspace_eq_self {x : E} (hx : x in K) : K.reflection x = x :=
  (reflection_eq_self_iff x).mpr hx

/--
theorem `reflection_map_apply` / 定理 `reflection_map_apply`

English:
theorem reflection_map_apply
  statement: {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
  proof: by
  simp [reflection_apply, starProjection_map_apply f K x]

中文:
定理 reflection_map_apply
  结论: {E E' : 类型} [NormedAddCommGroup E] [NormedAddCommGroup E']
  证明: by
  simp [reflection_apply, starProjection_map_apply f K x]

Depends on / 依赖: reflection_apply, starProjection_map_apply
-/
theorem reflection_map_apply {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (x : E') :
    reflection (K.map (f.toLinearEquiv : E ->ₗ[𝕜] E')) x = f (K.reflection (f.symm x)) := by
  simp [reflection_apply, starProjection_map_apply f K x]

/--
theorem `reflection_map` / 定理 `reflection_map`

English:
theorem reflection_map
  statement: {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
  proof: LinearIsometryEquiv.ext reflection_map_apply f K

中文:
定理 reflection_map
  结论: {E E' : 类型} [NormedAddCommGroup E] [NormedAddCommGroup E']
  证明: LinearIsometryEquiv.ext reflection_map_apply f K

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ext, reflection_map_apply
-/
theorem reflection_map {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] :
    reflection (K.map (f.toLinearEquiv : E ->ₗ[𝕜] E')) = f.symm.trans (K.reflection.trans f) :=
LinearIsometryEquiv.ext reflection_map_apply f K

/-- Reflection through the trivial subspace `{0}` is just negation. -/
@[simp]
/--
theorem `reflection_bot` / 定理 `reflection_bot`

English:
theorem reflection_bot
  statement: reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 𝕜
  proof: by
  ext; simp [reflection_apply]

中文:
定理 reflection_bot
  结论: reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 𝕜
  证明: by
  ext; simp [reflection_apply]

Depends on / 依赖: reflection_apply
-/
theorem reflection_bot : reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 𝕜 := by
  ext; simp [reflection_apply]

/--
theorem `reflection_mem_subspace_orthogonalComplement_eq_neg` / 定理 `reflection_mem_subspace_orthogonalComplement_eq_neg`

English:
theorem reflection_mem_subspace_orthogonalComplement_eq_neg
  statement: {v : E}
  proof: by
  simp [starProjection_apply, reflection_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hv]

中文:
定理 reflection_mem_subspace_orthogonalComplement_eq_neg
  结论: {v : E}
  证明: by
  simp [starProjection_apply, reflection_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hv]

Depends on / 依赖: orthogonalProjectionOnto_apply_of_mem_orthogonal, reflection_apply, starProjection_apply
-/
theorem reflection_mem_subspace_orthogonalComplement_eq_neg {v : E}
    (hv : v in Kᗮ) : K.reflection v = -v := by
  simp [starProjection_apply, reflection_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hv]

/--
theorem `reflection_mem_subspace_orthogonal_precomplement_eq_neg` / 定理 `reflection_mem_subspace_orthogonal_precomplement_eq_neg`

English:
theorem reflection_mem_subspace_orthogonal_precomplement_eq_neg
  statement: {v : E}
  proof: reflection_mem_subspace_orthogonalComplement_eq_neg (K.le_orthogonal_orthogonal hv)

中文:
定理 reflection_mem_subspace_orthogonal_precomplement_eq_neg
  结论: {v : E}
  证明: reflection_mem_subspace_orthogonalComplement_eq_neg (K.le_orthogonal_orthogonal hv)

Depends on / 依赖: K.le_orthogonal_orthogonal, le_orthogonal_orthogonal, reflection_mem_subspace_orthogonalComplement_eq_neg
-/
theorem reflection_mem_subspace_orthogonal_precomplement_eq_neg {v : E}
    (hv : v in K) : Kᗮ.reflection v = -v :=
  reflection_mem_subspace_orthogonalComplement_eq_neg (K.le_orthogonal_orthogonal hv)

/--
theorem `reflection_orthogonalComplement_singleton_eq_neg` / 定理 `reflection_orthogonalComplement_singleton_eq_neg`

English:
theorem reflection_orthogonalComplement_singleton_eq_neg
  given: (v : E)
  statement: reflection (𝕜 ∙ v)ᗮ v = -v
  proof: reflection_mem_subspace_orthogonal_precomplement_eq_neg (Submodule.mem_span_singleton_self v)

中文:
定理 reflection_orthogonalComplement_singleton_eq_neg
  条件: (v : E)
  结论: reflection (𝕜 ∙ v)ᗮ v = -v
  证明: reflection_mem_subspace_orthogonal_precomplement_eq_neg (Submodule.mem_span_singleton_self v)

Depends on / 依赖: Submodule, Submodule.mem_span_singleton_self, mem_span_singleton_self, reflection_mem_subspace_orthogonal_precomplement_eq_neg
-/
theorem reflection_orthogonalComplement_singleton_eq_neg (v : E) : reflection (𝕜 ∙ v)ᗮ v = -v :=
  reflection_mem_subspace_orthogonal_precomplement_eq_neg (Submodule.mem_span_singleton_self v)

/--
theorem `reflection_sub` / 定理 `reflection_sub`

English:
theorem reflection_sub
  given: {v w : F} (h : ‖v‖ = ‖w‖)
  statement: reflection (Real ∙ (v - w))ᗮ v = w
  proof: by
  set R : F ≃ₗᵢ[Real] F := reflection (Real ∙ (v - w))ᗮ
  suffices R v + R v = w + w by
    apply smul_right_injective F (by simp : (2 : Real) != 0)
    simpa [two_smul] using this
  have h₁ : R (v - w) = -(v - w) := reflection_orthogonalComplement_singleton_eq_neg (v - w)
  have h₂ : R (v + w) =

中文:
定理 reflection_sub
  条件: {v w : F} (h : ‖v‖ = ‖w‖)
  结论: reflection (实数 ∙ (v - w))ᗮ v = w
  证明: by
  set R : F ≃ₗᵢ[Real] F := reflection (Real ∙ (v - w))ᗮ
  suffices R v + R v = w + w by
    apply smul_right_injective F (by simp : (2 : Real) != 0)
    simpa [two_smul] using this
  have h₁ : R (v - w) = -(v - w) := reflection_orthogonalComplement_singleton_eq_neg (v - w)
  have h₂ : R (v + w) =

Depends on / 依赖: Submodule, Submodule.mem_orthogonal_singleton_iff_inner_left, convert, mem_orthogonal_singleton_iff_inner_left, real_inner_add_sub_eq_zero_iff, reflection, reflection_mem_subspace_eq_self, reflection_orthogonalComplement_singleton_eq_neg, smul_right_injective, two_smul
-/
theorem reflection_sub {v w : F} (h : ‖v‖ = ‖w‖) : reflection (Real ∙ (v - w))ᗮ v = w := by
  set R : F ≃ₗᵢ[Real] F := reflection (Real ∙ (v - w))ᗮ
  suffices R v + R v = w + w by
    apply smul_right_injective F (by simp : (2 : Real) != 0)
    simpa [two_smul] using this
  have h₁ : R (v - w) = -(v - w) := reflection_orthogonalComplement_singleton_eq_neg (v - w)
  have h₂ : R (v + w) = v + w := by
    apply reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_add_sub_eq_zero_iff]
    exact h
  convert! congr_arg₂ (· + ·) h₂ h₁ using 1
  · simp
  · abel

end reflection

end Submodule

end
