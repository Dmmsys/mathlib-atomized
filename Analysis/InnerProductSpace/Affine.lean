/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
/-!
# Normed affine spaces over an inner product space
-/

public section

variable {𝕜 V P : Type*}

section RCLike
variable [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped InnerProductSpace

/--
theorem `inner_vsub_left_eq_zero_symm` / 定理 `inner_vsub_left_eq_zero_symm`

English:
theorem inner_vsub_left_eq_zero_symm
  given: {a b : P} {v : V}
  proof: by
  rw [← neg_vsub_eq_vsub_rev]; rw [inner_neg_left]; rw [neg_eq_zero]

中文:
定理 inner_vsub_left_eq_zero_symm
  条件: {a b : P} {v : V}
  证明: by
  rw [← neg_vsub_eq_vsub_rev]; rw [inner_neg_left]; rw [neg_eq_zero]

Depends on / 依赖: inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev
-/
theorem inner_vsub_left_eq_zero_symm {a b : P} {v : V} :
    ⟪a -ᵥ b, v⟫_𝕜 = 0 ↔ ⟪b -ᵥ a, v⟫_𝕜 = 0 := by
  rw [← neg_vsub_eq_vsub_rev]; rw [inner_neg_left]; rw [neg_eq_zero]

/--
theorem `inner_vsub_right_eq_zero_symm` / 定理 `inner_vsub_right_eq_zero_symm`

English:
theorem inner_vsub_right_eq_zero_symm
  given: {v : V} {a b : P}
  proof: by
  rw [← neg_vsub_eq_vsub_rev]; rw [inner_neg_right]; rw [neg_eq_zero]

中文:
定理 inner_vsub_right_eq_zero_symm
  条件: {v : V} {a b : P}
  证明: by
  rw [← neg_vsub_eq_vsub_rev]; rw [inner_neg_right]; rw [neg_eq_zero]

Depends on / 依赖: inner_neg_right, neg_eq_zero, neg_vsub_eq_vsub_rev
-/
theorem inner_vsub_right_eq_zero_symm {v : V} {a b : P} :
    ⟪v, a -ᵥ b⟫_𝕜 = 0 ↔ ⟪v, b -ᵥ a⟫_𝕜 = 0 := by
  rw [← neg_vsub_eq_vsub_rev]; rw [inner_neg_right]; rw [neg_eq_zero]

end RCLike

section Real
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped RealInnerProductSpace


/--
theorem `inner_vsub_vsub_left_eq_dist_sq_left_iff` / 定理 `inner_vsub_vsub_left_eq_dist_sq_left_iff`

English:
theorem inner_vsub_vsub_left_eq_dist_sq_left_iff
  given: {a b c : P}
  proof: by
  rw [dist_eq_norm_vsub V]; rw [inner_eq_norm_sq_left_iff]; rw [vsub_sub_vsub_cancel_left]; rw [inner_vsub_right_eq_zero_symm]

中文:
定理 inner_vsub_vsub_left_eq_dist_sq_left_iff
  条件: {a b c : P}
  证明: by
  rw [dist_eq_norm_vsub V]; rw [inner_eq_norm_sq_left_iff]; rw [vsub_sub_vsub_cancel_left]; rw [inner_vsub_right_eq_zero_symm]

Depends on / 依赖: dist_eq_norm_vsub, inner_eq_norm_sq_left_iff, inner_vsub_right_eq_zero_symm, vsub_sub_vsub_cancel_left
-/
theorem inner_vsub_vsub_left_eq_dist_sq_left_iff {a b c : P} :
    ⟪a -ᵥ b, a -ᵥ c⟫ = dist a b ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0 := by
  rw [dist_eq_norm_vsub V]; rw [inner_eq_norm_sq_left_iff]; rw [vsub_sub_vsub_cancel_left]; rw [inner_vsub_right_eq_zero_symm]

/--
theorem `inner_vsub_vsub_left_eq_dist_sq_right_iff` / 定理 `inner_vsub_vsub_left_eq_dist_sq_right_iff`

English:
theorem inner_vsub_vsub_left_eq_dist_sq_right_iff
  given: {a b c : P}
  proof: by
  rw [real_inner_comm]; rw [inner_vsub_vsub_left_eq_dist_sq_left_iff]; rw [real_inner_comm]

中文:
定理 inner_vsub_vsub_left_eq_dist_sq_right_iff
  条件: {a b c : P}
  证明: by
  rw [real_inner_comm]; rw [inner_vsub_vsub_left_eq_dist_sq_left_iff]; rw [real_inner_comm]

Depends on / 依赖: inner_vsub_vsub_left_eq_dist_sq_left_iff, real_inner_comm
-/
theorem inner_vsub_vsub_left_eq_dist_sq_right_iff {a b c : P} :
    ⟪a -ᵥ b, a -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪c -ᵥ b, a -ᵥ c⟫ = 0 := by
  rw [real_inner_comm]; rw [inner_vsub_vsub_left_eq_dist_sq_left_iff]; rw [real_inner_comm]

/--
theorem `inner_vsub_vsub_right_eq_dist_sq_left_iff` / 定理 `inner_vsub_vsub_right_eq_dist_sq_left_iff`

English:
theorem inner_vsub_vsub_right_eq_dist_sq_left_iff
  given: {a b c : P}
  proof: by
  rw [dist_eq_norm_vsub V]; rw [inner_eq_norm_sq_left_iff]; rw [vsub_sub_vsub_cancel_right]; rw [inner_vsub_right_eq_zero_symm]

中文:
定理 inner_vsub_vsub_right_eq_dist_sq_left_iff
  条件: {a b c : P}
  证明: by
  rw [dist_eq_norm_vsub V]; rw [inner_eq_norm_sq_left_iff]; rw [vsub_sub_vsub_cancel_right]; rw [inner_vsub_right_eq_zero_symm]

Depends on / 依赖: dist_eq_norm_vsub, inner_eq_norm_sq_left_iff, inner_vsub_right_eq_zero_symm, vsub_sub_vsub_cancel_right
-/
theorem inner_vsub_vsub_right_eq_dist_sq_left_iff {a b c : P} :
    ⟪a -ᵥ c, b -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪a -ᵥ c, b -ᵥ a⟫ = 0 := by
  rw [dist_eq_norm_vsub V]; rw [inner_eq_norm_sq_left_iff]; rw [vsub_sub_vsub_cancel_right]; rw [inner_vsub_right_eq_zero_symm]

/--
theorem `inner_vsub_vsub_right_eq_dist_sq_right_iff` / 定理 `inner_vsub_vsub_right_eq_dist_sq_right_iff`

English:
theorem inner_vsub_vsub_right_eq_dist_sq_right_iff
  given: {a b c : P}
  proof: by
  rw [real_inner_comm]; rw [inner_vsub_vsub_right_eq_dist_sq_left_iff]; rw [real_inner_comm]

中文:
定理 inner_vsub_vsub_right_eq_dist_sq_right_iff
  条件: {a b c : P}
  证明: by
  rw [real_inner_comm]; rw [inner_vsub_vsub_right_eq_dist_sq_left_iff]; rw [real_inner_comm]

Depends on / 依赖: inner_vsub_vsub_right_eq_dist_sq_left_iff, real_inner_comm
-/
theorem inner_vsub_vsub_right_eq_dist_sq_right_iff {a b c : P} :
    ⟪a -ᵥ c, b -ᵥ c⟫ = dist b c ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0 := by
  rw [real_inner_comm]; rw [inner_vsub_vsub_right_eq_dist_sq_left_iff]; rw [real_inner_comm]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dist_sq_lineMap_lineMap_of_inner_eq_zero` / 定理 `dist_sq_lineMap_lineMap_of_inner_eq_zero`

English:
theorem dist_sq_lineMap_lineMap_of_inner_eq_zero
  statement: {a b c : P} (t₁ t₂ : Real)
  proof: by
  have hvec : AffineMap.lineMap a b t₁ -ᵥ AffineMap.lineMap a c t₂ =
              t₁ • (b -ᵥ a) - t₂ • (c -ᵥ a) := by
    rw [AffineMap.lineMap_apply]; rw [AffineMap.lineMap_apply]; rw [vadd_vsub_vadd_cancel_right]
  rw [dist_eq_norm_vsub V]; rw [hvec]; rw [norm_sub_sq_real]; rw [norm_smul]; rw 

中文:
定理 dist_sq_lineMap_lineMap_of_inner_eq_zero
  结论: {a b c : P} (t₁ t₂ : 实数)
  证明: by
  have hvec : AffineMap.lineMap a b t₁ -ᵥ AffineMap.lineMap a c t₂ =
              t₁ • (b -ᵥ a) - t₂ • (c -ᵥ a) := by
    rw [AffineMap.lineMap_apply]; rw [AffineMap.lineMap_apply]; rw [vadd_vsub_vadd_cancel_right]
  rw [dist_eq_norm_vsub V]; rw [hvec]; rw [norm_sub_sq_real]; rw [norm_smul]; rw 

Depends on / 依赖: AffineMap, AffineMap.lineMap, AffineMap.lineMap_apply, Real.norm_eq_abs, dist_eq_norm_vsub, h_inner, inner_smul_left, inner_smul_right, lineMap, lineMap_apply, mul_pow, mul_zero, norm_eq_abs, norm_smul, norm_sub_sq_real, sq_abs, sub_zero, vadd_vsub_vadd_cancel_right
-/
theorem dist_sq_lineMap_lineMap_of_inner_eq_zero {a b c : P} (t₁ t₂ : Real)
    (h_inner : ⟪b -ᵥ a, c -ᵥ a⟫ = 0) :
    dist (AffineMap.lineMap a b t₁) (AffineMap.lineMap a c t₂) ^ 2 =
      t₁ ^ 2 * dist a b ^ 2 + t₂ ^ 2 * dist a c ^ 2 := by
  have hvec : AffineMap.lineMap a b t₁ -ᵥ AffineMap.lineMap a c t₂ =
              t₁ • (b -ᵥ a) - t₂ • (c -ᵥ a) := by
    rw [AffineMap.lineMap_apply]; rw [AffineMap.lineMap_apply]; rw [vadd_vsub_vadd_cancel_right]
  rw [dist_eq_norm_vsub V]; rw [hvec]; rw [norm_sub_sq_real]; rw [norm_smul]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [Real.norm_eq_abs]; rw [inner_smul_left]; rw [inner_smul_right]; rw [h_inner]
  simp only [mul_zero, sub_zero, mul_pow, sq_abs, ← dist_eq_norm_vsub' V]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dist_sq_lineMap_of_inner_eq_zero` / 定理 `dist_sq_lineMap_of_inner_eq_zero`

English:
theorem dist_sq_lineMap_of_inner_eq_zero
  statement: {a b p : P} (t : Real)
  proof: by
  have h := dist_sq_lineMap_lineMap_of_inner_eq_zero (t₁ := 1) (t₂ := t) h_inner
  simp only [AffineMap.lineMap_apply_one, one_pow, one_mul] at h
  rwa [dist_comm a p] at h

中文:
定理 dist_sq_lineMap_of_inner_eq_zero
  结论: {a b p : P} (t : 实数)
  证明: by
  have h := dist_sq_lineMap_lineMap_of_inner_eq_zero (t₁ := 1) (t₂ := t) h_inner
  simp only [AffineMap.lineMap_apply_one, one_pow, one_mul] at h
  rwa [dist_comm a p] at h

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_one, dist_comm, dist_sq_lineMap_lineMap_of_inner_eq_zero, h_inner, lineMap_apply_one, one_mul, one_pow
-/
theorem dist_sq_lineMap_of_inner_eq_zero {a b p : P} (t : Real)
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p (AffineMap.lineMap a b t) ^ 2 = dist p a ^ 2 + t ^ 2 * dist a b ^ 2 := by
  have h := dist_sq_lineMap_lineMap_of_inner_eq_zero (t₁ := 1) (t₂ := t) h_inner
  simp only [AffineMap.lineMap_apply_one, one_pow, one_mul] at h
  rwa [dist_comm a p] at h

/--
theorem `dist_sq_of_inner_eq_zero` / 定理 `dist_sq_of_inner_eq_zero`

English:
theorem dist_sq_of_inner_eq_zero
  statement: {a b p : P}
  proof: by
  simpa using dist_sq_lineMap_of_inner_eq_zero 1 h_inner

中文:
定理 dist_sq_of_inner_eq_zero
  结论: {a b p : P}
  证明: by
  simpa using dist_sq_lineMap_of_inner_eq_zero 1 h_inner

Depends on / 依赖: dist_sq_lineMap_of_inner_eq_zero, h_inner
-/
theorem dist_sq_of_inner_eq_zero {a b p : P}
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2 := by
  simpa using dist_sq_lineMap_of_inner_eq_zero 1 h_inner

end Real
