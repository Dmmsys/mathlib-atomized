/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Joseph Myers
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.InnerProductSpace.Affine

/-!
# Perpendicular bisector of a segment

We define `AffineSubspace.perpBisector p₁ p₂` to be the perpendicular bisector of the segment
`[p₁, p₂]`, as a bundled affine subspace. We also prove that a point belongs to the perpendicular
bisector if and only if it is equidistant from `p₁` and `p₂`, as well as a few linear equations that
define this subspace.

## Keywords

euclidean geometry, perpendicular, perpendicular bisector, line segment bisector, equidistant
-/

@[expose] public section

open Set
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P]

noncomputable section

namespace AffineSubspace

variable {c p₁ p₂ : P}

/--
Definition of `perpBisector` / `perpBisector` 的定义

English:
definition perpBisector
  signature: (p₁ p₂ : P)
  body: mk' (midpoint Real p₁ p₂) (LinearMap.ker (innerₛₗ Real (p₂ -ᵥ p₁)))

中文:
定义 perpBisector
  签名: (p₁ p₂ : P)
  定义体: mk' (midpoint Real p₁ p₂) (LinearMap.ker (innerₛₗ Real (p₂ -ᵥ p₁)))

Depends on / 依赖: LinearMap, LinearMap.ker, midpoint
-/
def perpBisector (p₁ p₂ : P) : AffineSubspace Real P :=
  mk' (midpoint Real p₁ p₂) (LinearMap.ker (innerₛₗ Real (p₂ -ᵥ p₁)))

/--
theorem `mem_perpBisector_iff_inner_eq_zero'` / 定理 `mem_perpBisector_iff_inner_eq_zero'`

English:
theorem mem_perpBisector_iff_inner_eq_zero'
  proof: Iff.rfl

中文:
定理 mem_perpBisector_iff_inner_eq_zero'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_perpBisector_iff_inner_eq_zero' :
    c in perpBisector p₁ p₂ ↔ ⟪p₂ -ᵥ p₁, c -ᵥ midpoint Real p₁ p₂⟫ = 0 :=
  Iff.rfl

/--
theorem `mem_perpBisector_iff_inner_eq_zero` / 定理 `mem_perpBisector_iff_inner_eq_zero`

English:
theorem mem_perpBisector_iff_inner_eq_zero
  proof: inner_eq_zero_symm

中文:
定理 mem_perpBisector_iff_inner_eq_zero
  证明: inner_eq_zero_symm

Depends on / 依赖: inner_eq_zero_symm
-/
theorem mem_perpBisector_iff_inner_eq_zero :
    c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint Real p₁ p₂, p₂ -ᵥ p₁⟫ = 0 :=
  inner_eq_zero_symm

/--
theorem `mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero` / 定理 `mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero`

English:
theorem mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero
  proof: by
  rw [mem_perpBisector_iff_inner_eq_zero]; rw [Equiv.pointReflection_apply]; rw [vsub_midpoint]; rw [invOf_eq_inv]; rw [← smul_add]; rw [real_inner_smul_left]; rw [vadd_vsub_assoc]
  simp

中文:
定理 mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero
  证明: by
  rw [mem_perpBisector_iff_inner_eq_zero]; rw [Equiv.pointReflection_apply]; rw [vsub_midpoint]; rw [invOf_eq_inv]; rw [← smul_add]; rw [real_inner_smul_left]; rw [vadd_vsub_assoc]
  simp

Depends on / 依赖: Equiv.pointReflection_apply, invOf_eq_inv, mem_perpBisector_iff_inner_eq_zero, pointReflection_apply, real_inner_smul_left, smul_add, vadd_vsub_assoc, vsub_midpoint
-/
theorem mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero :
    c in perpBisector p₁ p₂ ↔ ⟪Equiv.pointReflection c p₁ -ᵥ p₂, p₂ -ᵥ p₁⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero]; rw [Equiv.pointReflection_apply]; rw [vsub_midpoint]; rw [invOf_eq_inv]; rw [← smul_add]; rw [real_inner_smul_left]; rw [vadd_vsub_assoc]
  simp

/--
theorem `mem_perpBisector_pointReflection_iff_inner_eq_zero` / 定理 `mem_perpBisector_pointReflection_iff_inner_eq_zero`

English:
theorem mem_perpBisector_pointReflection_iff_inner_eq_zero
  proof: by
  rw [mem_perpBisector_iff_inner_eq_zero]; rw [midpoint_pointReflection_right]; rw [Equiv.pointReflection_apply]; rw [vadd_vsub_assoc]; rw [inner_add_right]; rw [add_self_eq_zero]; rw [← neg_eq_zero]; rw [← inner_neg_right]; rw [neg_vsub_eq_vsub_rev]

中文:
定理 mem_perpBisector_pointReflection_iff_inner_eq_zero
  证明: by
  rw [mem_perpBisector_iff_inner_eq_zero]; rw [midpoint_pointReflection_right]; rw [Equiv.pointReflection_apply]; rw [vadd_vsub_assoc]; rw [inner_add_right]; rw [add_self_eq_zero]; rw [← neg_eq_zero]; rw [← inner_neg_right]; rw [neg_vsub_eq_vsub_rev]

Depends on / 依赖: Equiv.pointReflection_apply, add_self_eq_zero, inner_add_right, inner_neg_right, mem_perpBisector_iff_inner_eq_zero, midpoint_pointReflection_right, neg_eq_zero, neg_vsub_eq_vsub_rev, pointReflection_apply, vadd_vsub_assoc
-/
theorem mem_perpBisector_pointReflection_iff_inner_eq_zero :
    c in perpBisector p₁ (Equiv.pointReflection p₂ p₁) ↔ ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero]; rw [midpoint_pointReflection_right]; rw [Equiv.pointReflection_apply]; rw [vadd_vsub_assoc]; rw [inner_add_right]; rw [add_self_eq_zero]; rw [← neg_eq_zero]; rw [← inner_neg_right]; rw [neg_vsub_eq_vsub_rev]

/--
theorem `midpoint_mem_perpBisector` / 定理 `midpoint_mem_perpBisector`

English:
theorem midpoint_mem_perpBisector
  given: (p₁ p₂ : P)
  proof: by
  simp [mem_perpBisector_iff_inner_eq_zero]

中文:
定理 midpoint_mem_perpBisector
  条件: (p₁ p₂ : P)
  证明: by
  simp [mem_perpBisector_iff_inner_eq_zero]

Depends on / 依赖: mem_perpBisector_iff_inner_eq_zero
-/
theorem midpoint_mem_perpBisector (p₁ p₂ : P) :
    midpoint Real p₁ p₂ in perpBisector p₁ p₂ := by
  simp [mem_perpBisector_iff_inner_eq_zero]

/--
theorem `perpBisector_nonempty` / 定理 `perpBisector_nonempty`

English:
theorem perpBisector_nonempty
  statement: (perpBisector p₁ p₂ : Set P).Nonempty
  proof: ⟨_, midpoint_mem_perpBisector _ _⟩

@[simp]

中文:
定理 perpBisector_nonempty
  结论: (perpBisector p₁ p₂ : 集合 P).非空
  证明: ⟨_, midpoint_mem_perpBisector _ _⟩

@[simp]

Depends on / 依赖: midpoint_mem_perpBisector
-/
theorem perpBisector_nonempty : (perpBisector p₁ p₂ : Set P).Nonempty :=
  ⟨_, midpoint_mem_perpBisector _ _⟩

@[simp]
/--
theorem `direction_perpBisector` / 定理 `direction_perpBisector`

English:
theorem direction_perpBisector
  given: (p₁ p₂ : P)
  proof: by
  rw [perpBisector]; rw [direction_mk']
  ext x
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm

中文:
定理 direction_perpBisector
  条件: (p₁ p₂ : P)
  证明: by
  rw [perpBisector]; rw [direction_mk']
  ext x
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm

Depends on / 依赖: Submodule, Submodule.mem_orthogonal_singleton_iff_inner_right.symm, direction_mk, mem_orthogonal_singleton_iff_inner_right, perpBisector
-/
theorem direction_perpBisector (p₁ p₂ : P) :
    (perpBisector p₁ p₂).direction = (Real ∙ (p₂ -ᵥ p₁))ᗮ := by
  rw [perpBisector]; rw [direction_mk']
  ext x
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm

/--
theorem `mem_perpBisector_iff_inner_eq_inner` / 定理 `mem_perpBisector_iff_inner_eq_inner`

English:
theorem mem_perpBisector_iff_inner_eq_inner
  proof: by
  rw [Iff.comm]; rw [mem_perpBisector_iff_inner_eq_zero]; rw [← add_neg_eq_zero]; rw [← inner_neg_right]; rw [neg_vsub_eq_vsub_rev]; rw [← inner_add_left]; rw [vsub_midpoint]; rw [invOf_eq_inv]; rw [← smul_add]; rw [real_inner_smul_left]; simp

中文:
定理 mem_perpBisector_iff_inner_eq_inner
  证明: by
  rw [Iff.comm]; rw [mem_perpBisector_iff_inner_eq_zero]; rw [← add_neg_eq_zero]; rw [← inner_neg_right]; rw [neg_vsub_eq_vsub_rev]; rw [← inner_add_left]; rw [vsub_midpoint]; rw [invOf_eq_inv]; rw [← smul_add]; rw [real_inner_smul_left]; simp

Depends on / 依赖: Iff.comm, add_neg_eq_zero, inner_add_left, inner_neg_right, invOf_eq_inv, mem_perpBisector_iff_inner_eq_zero, neg_vsub_eq_vsub_rev, real_inner_smul_left, smul_add, vsub_midpoint
-/
theorem mem_perpBisector_iff_inner_eq_inner :
    c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ := by
  rw [Iff.comm]; rw [mem_perpBisector_iff_inner_eq_zero]; rw [← add_neg_eq_zero]; rw [← inner_neg_right]; rw [neg_vsub_eq_vsub_rev]; rw [← inner_add_left]; rw [vsub_midpoint]; rw [invOf_eq_inv]; rw [← smul_add]; rw [real_inner_smul_left]; simp

/--
theorem `mem_perpBisector_iff_inner_eq` / 定理 `mem_perpBisector_iff_inner_eq`

English:
theorem mem_perpBisector_iff_inner_eq
  proof: by
  rw [mem_perpBisector_iff_inner_eq_zero]; rw [← vsub_sub_vsub_cancel_right _ _ p₁]; rw [inner_sub_left]; rw [sub_eq_zero]; rw [midpoint_vsub_left]; rw [invOf_eq_inv]; rw [real_inner_smul_left]; rw [real_inner_self_eq_norm_sq]; rw [dist_eq_norm_vsub' V]; rw [div_eq_inv_mul]

中文:
定理 mem_perpBisector_iff_inner_eq
  证明: by
  rw [mem_perpBisector_iff_inner_eq_zero]; rw [← vsub_sub_vsub_cancel_right _ _ p₁]; rw [inner_sub_left]; rw [sub_eq_zero]; rw [midpoint_vsub_left]; rw [invOf_eq_inv]; rw [real_inner_smul_left]; rw [real_inner_self_eq_norm_sq]; rw [dist_eq_norm_vsub' V]; rw [div_eq_inv_mul]

Depends on / 依赖: dist_eq_norm_vsub, div_eq_inv_mul, inner_sub_left, invOf_eq_inv, mem_perpBisector_iff_inner_eq_zero, midpoint_vsub_left, real_inner_self_eq_norm_sq, real_inner_smul_left, sub_eq_zero, vsub_sub_vsub_cancel_right
-/
theorem mem_perpBisector_iff_inner_eq :
    c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = (dist p₁ p₂) ^ 2 / 2 := by
  rw [mem_perpBisector_iff_inner_eq_zero]; rw [← vsub_sub_vsub_cancel_right _ _ p₁]; rw [inner_sub_left]; rw [sub_eq_zero]; rw [midpoint_vsub_left]; rw [invOf_eq_inv]; rw [real_inner_smul_left]; rw [real_inner_self_eq_norm_sq]; rw [dist_eq_norm_vsub' V]; rw [div_eq_inv_mul]

/--
theorem `mem_perpBisector_iff_dist_eq` / 定理 `mem_perpBisector_iff_dist_eq`

English:
theorem mem_perpBisector_iff_dist_eq
  statement: c in perpBisector p₁ p₂ ↔ dist c p₁ = dist c p₂
  proof: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← real_inner_add_sub_eq_zero_iff]; rw [vsub_sub_vsub_cancel_left]; rw [inner_add_left]; rw [add_eq_zero_iff_eq_neg]; rw [← inner_neg_right]; rw [neg_vsub_eq_vsub_rev]; rw [mem_perpBisector_iff_inner_eq_inner]

中文:
定理 mem_perpBisector_iff_dist_eq
  结论: c in perpBisector p₁ p₂ ↔ dist c p₁ = dist c p₂
  证明: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← real_inner_add_sub_eq_zero_iff]; rw [vsub_sub_vsub_cancel_left]; rw [inner_add_left]; rw [add_eq_zero_iff_eq_neg]; rw [← inner_neg_right]; rw [neg_vsub_eq_vsub_rev]; rw [mem_perpBisector_iff_inner_eq_inner]

Depends on / 依赖: add_eq_zero_iff_eq_neg, dist_eq_norm_vsub, inner_add_left, inner_neg_right, mem_perpBisector_iff_inner_eq_inner, neg_vsub_eq_vsub_rev, real_inner_add_sub_eq_zero_iff, vsub_sub_vsub_cancel_left
-/
theorem mem_perpBisector_iff_dist_eq : c in perpBisector p₁ p₂ ↔ dist c p₁ = dist c p₂ := by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← real_inner_add_sub_eq_zero_iff]; rw [vsub_sub_vsub_cancel_left]; rw [inner_add_left]; rw [add_eq_zero_iff_eq_neg]; rw [← inner_neg_right]; rw [neg_vsub_eq_vsub_rev]; rw [mem_perpBisector_iff_inner_eq_inner]

/--
theorem `mem_perpBisector_iff_dist_eq'` / 定理 `mem_perpBisector_iff_dist_eq'`

English:
theorem mem_perpBisector_iff_dist_eq'
  statement: c in perpBisector p₁ p₂ ↔ dist p₁ c = dist p₂ c
  proof: by
  simp only [mem_perpBisector_iff_dist_eq, dist_comm]

中文:
定理 mem_perpBisector_iff_dist_eq'
  结论: c in perpBisector p₁ p₂ ↔ dist p₁ c = dist p₂ c
  证明: by
  simp only [mem_perpBisector_iff_dist_eq, dist_comm]

Depends on / 依赖: dist_comm, mem_perpBisector_iff_dist_eq
-/
theorem mem_perpBisector_iff_dist_eq' : c in perpBisector p₁ p₂ ↔ dist p₁ c = dist p₂ c := by
  simp only [mem_perpBisector_iff_dist_eq, dist_comm]

/--
theorem `perpBisector_comm` / 定理 `perpBisector_comm`

English:
theorem perpBisector_comm
  given: (p₁ p₂ : P)
  statement: perpBisector p₁ p₂ = perpBisector p₂ p₁
  proof: by
  ext c; simp only [mem_perpBisector_iff_dist_eq, eq_comm]

中文:
定理 perpBisector_comm
  条件: (p₁ p₂ : P)
  结论: perpBisector p₁ p₂ = perpBisector p₂ p₁
  证明: by
  ext c; simp only [mem_perpBisector_iff_dist_eq, eq_comm]

Depends on / 依赖: eq_comm, mem_perpBisector_iff_dist_eq
-/
theorem perpBisector_comm (p₁ p₂ : P) : perpBisector p₁ p₂ = perpBisector p₂ p₁ := by
  ext c; simp only [mem_perpBisector_iff_dist_eq, eq_comm]

/--
theorem `right_mem_perpBisector` / 定理 `right_mem_perpBisector`

English:
theorem right_mem_perpBisector
  statement: p₂ in perpBisector p₁ p₂ ↔ p₁ = p₂
  proof: by
  simpa [mem_perpBisector_iff_inner_eq_inner] using eq_comm

中文:
定理 right_mem_perpBisector
  结论: p₂ in perpBisector p₁ p₂ ↔ p₁ = p₂
  证明: by
  simpa [mem_perpBisector_iff_inner_eq_inner] using eq_comm
-/
@[simp] theorem right_mem_perpBisector : p₂ in perpBisector p₁ p₂ ↔ p₁ = p₂ := by
  simpa [mem_perpBisector_iff_inner_eq_inner] using eq_comm

/--
theorem `left_mem_perpBisector` / 定理 `left_mem_perpBisector`

English:
theorem left_mem_perpBisector
  statement: p₁ in perpBisector p₁ p₂ ↔ p₁ = p₂
  proof: by
  rw [perpBisector_comm]; rw [right_mem_perpBisector]; rw [eq_comm]

中文:
定理 left_mem_perpBisector
  结论: p₁ in perpBisector p₁ p₂ ↔ p₁ = p₂
  证明: by
  rw [perpBisector_comm]; rw [right_mem_perpBisector]; rw [eq_comm]
-/
@[simp] theorem left_mem_perpBisector : p₁ in perpBisector p₁ p₂ ↔ p₁ = p₂ := by
  rw [perpBisector_comm]; rw [right_mem_perpBisector]; rw [eq_comm]

/--
theorem `perpBisector_self` / 定理 `perpBisector_self`

English:
theorem perpBisector_self
  given: (p : P)
  statement: perpBisector p p = ⊤
  proof: top_unique fun _ => by simp [mem_perpBisector_iff_inner_eq_inner]

中文:
定理 perpBisector_self
  条件: (p : P)
  结论: perpBisector p p = ⊤
  证明: top_unique fun _ => by simp [mem_perpBisector_iff_inner_eq_inner]
-/
@[simp] theorem perpBisector_self (p : P) : perpBisector p p = ⊤ :=
  top_unique fun _ => by simp [mem_perpBisector_iff_inner_eq_inner]

/--
theorem `perpBisector_eq_top` / 定理 `perpBisector_eq_top`

English:
theorem perpBisector_eq_top
  statement: perpBisector p₁ p₂ = ⊤ ↔ p₁ = p₂
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ perpBisector_self _⟩
  rw [← left_mem_perpBisector]; rw [h]
  trivial

中文:
定理 perpBisector_eq_top
  结论: perpBisector p₁ p₂ = ⊤ ↔ p₁ = p₂
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ perpBisector_self _⟩
  rw [← left_mem_perpBisector]; rw [h]
  trivial
-/
@[simp] theorem perpBisector_eq_top : perpBisector p₁ p₂ = ⊤ ↔ p₁ = p₂ := by
  refine ⟨fun h => ?_, fun h => h ▸ perpBisector_self _⟩
  rw [← left_mem_perpBisector]; rw [h]
  trivial

/--
theorem `perpBisector_ne_bot` / 定理 `perpBisector_ne_bot`

English:
theorem perpBisector_ne_bot
  statement: perpBisector p₁ p₂ != ⊥
  proof: by
  rw [← nonempty_iff_ne_bot]; exact perpBisector_nonempty

中文:
定理 perpBisector_ne_bot
  结论: perpBisector p₁ p₂ != ⊥
  证明: by
  rw [← nonempty_iff_ne_bot]; exact perpBisector_nonempty
-/
@[simp] theorem perpBisector_ne_bot : perpBisector p₁ p₂ != ⊥ := by
  rw [← nonempty_iff_ne_bot]; exact perpBisector_nonempty

end AffineSubspace

open AffineSubspace

namespace EuclideanGeometry

/--
theorem `dist_lt_of_sbtw_of_inner_eq_zero` / 定理 `dist_lt_of_sbtw_of_inner_eq_zero`

English:
theorem dist_lt_of_sbtw_of_inner_eq_zero
  statement: {a b c p : P}
  proof: by
  obtain ⟨t, ⟨ht0, ht1⟩, hb_eq⟩ := h_sbtw.mem_image_Ioo
  have hb : b -ᵥ a = t • (c -ᵥ a) := by simp [← hb_eq, AffineMap.lineMap_apply]
  have hpc : ⟪p -ᵥ a, c -ᵥ a⟫ = 0 := by simpa [ht0.ne', hb, inner_smul_right] using h_inner
  have h_sq_ineq : dist p b ^ 2 < dist p c ^ 2 := by
    rw [← hb_eq]; rw [dist_sq_lineMap_of_inner_eq_zero t hpc]; rw [dist_sq_of_inner_eq_zero hpc]
    have hv_pos : 0 < dist a c ^ 2 := sq_pos_of_pos (dist_pos.mpr h_sbtw.left_ne_right)
.mpr ht1 have ht_sq_lt : t ^ 2 < 1 := sq_lt_one_iff₀ ht0.le
    nlinarith [sq_nonneg (dist p a), sq_nonneg (dist a c)]
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_ineq

中文:
定理 dist_lt_of_sbtw_of_inner_eq_zero
  结论: {a b c p : P}
  证明: by
  obtain ⟨t, ⟨ht0, ht1⟩, hb_eq⟩ := h_sbtw.mem_image_Ioo
  have hb : b -ᵥ a = t • (c -ᵥ a) := by simp [← hb_eq, AffineMap.lineMap_apply]
  have hpc : ⟪p -ᵥ a, c -ᵥ a⟫ = 0 := by simpa [ht0.ne', hb, inner_smul_right] using h_inner
  have h_sq_ineq : dist p b ^ 2 < dist p c ^ 2 := by
    rw [← hb_eq]; rw [dist_sq_lineMap_of_inner_eq_zero t hpc]; rw [dist_sq_of_inner_eq_zero hpc]
    have hv_pos : 0 < dist a c ^ 2 := sq_pos_of_pos (dist_pos.mpr h_sbtw.left_ne_right)
.mpr ht1 have ht_sq_lt : t ^ 2 < 1 := sq_lt_one_iff₀ ht0.le
    nlinarith [sq_nonneg (dist p a), sq_nonneg (dist a c)]
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_ineq

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, dist_pos, dist_pos.mpr, dist_sq_lineMap_of_inner_eq_zero, dist_sq_of_inner_eq_zero, h_inner, h_sbtw, h_sbtw.left_ne_right, h_sbtw.mem_image_Ioo, h_sq_ineq, hb_eq, ht0.ne, ht_sq_lt, hv_pos, inner_smul_right, left_ne_right, lineMap_apply, mem_image_Ioo, sq_lt_one
-/
theorem dist_lt_of_sbtw_of_inner_eq_zero {a b c p : P}
    (h_sbtw : Sbtw Real a b c)
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p b < dist p c := by
  obtain ⟨t, ⟨ht0, ht1⟩, hb_eq⟩ := h_sbtw.mem_image_Ioo
  have hb : b -ᵥ a = t • (c -ᵥ a) := by simp [← hb_eq, AffineMap.lineMap_apply]
  have hpc : ⟪p -ᵥ a, c -ᵥ a⟫ = 0 := by simpa [ht0.ne', hb, inner_smul_right] using h_inner
  have h_sq_ineq : dist p b ^ 2 < dist p c ^ 2 := by
    rw [← hb_eq]; rw [dist_sq_lineMap_of_inner_eq_zero t hpc]; rw [dist_sq_of_inner_eq_zero hpc]
    have hv_pos : 0 < dist a c ^ 2 := sq_pos_of_pos (dist_pos.mpr h_sbtw.left_ne_right)
.mpr ht1 have ht_sq_lt : t ^ 2 < 1 := sq_lt_one_iff₀ ht0.le
    nlinarith [sq_nonneg (dist p a), sq_nonneg (dist a c)]
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_ineq

/--
theorem `dist_le_of_wbtw_of_inner_eq_zero` / 定理 `dist_le_of_wbtw_of_inner_eq_zero`

English:
theorem dist_le_of_wbtw_of_inner_eq_zero
  statement: {a b c p : P}
  proof: by
  obtain ⟨t, ⟨ht0, ht1⟩, hb_eq⟩ := h_wbtw
  have h_sq_ineq : dist p b ^ 2 <= dist p c ^ 2 := by
    rw [← hb_eq]; rw [dist_sq_lineMap_of_inner_eq_zero t h_inner]; rw [dist_sq_of_inner_eq_zero h_inner]
.mpr ht1 have ht_sq_le : t ^ 2 <= 1 := sq_le_one_iff₀ ht0
    nlinarith [sq_nonneg (dist p a), sq_nonneg (dist a c)]
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_le_sqrt h_sq_ineq

中文:
定理 dist_le_of_wbtw_of_inner_eq_zero
  结论: {a b c p : P}
  证明: by
  obtain ⟨t, ⟨ht0, ht1⟩, hb_eq⟩ := h_wbtw
  have h_sq_ineq : dist p b ^ 2 <= dist p c ^ 2 := by
    rw [← hb_eq]; rw [dist_sq_lineMap_of_inner_eq_zero t h_inner]; rw [dist_sq_of_inner_eq_zero h_inner]
.mpr ht1 have ht_sq_le : t ^ 2 <= 1 := sq_le_one_iff₀ ht0
    nlinarith [sq_nonneg (dist p a), sq_nonneg (dist a c)]
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_le_sqrt h_sq_ineq

Depends on / 依赖: Real.sqrt_le_sqrt, Real.sqrt_sq, dist_nonneg, dist_sq_lineMap_of_inner_eq_zero, dist_sq_of_inner_eq_zero, h_inner, h_sq_ineq, h_wbtw, hb_eq, ht_sq_le, sq_nonneg, sqrt_le_sqrt, sqrt_sq
-/
theorem dist_le_of_wbtw_of_inner_eq_zero {a b c p : P}
    (h_wbtw : Wbtw Real a b c)
    (h_inner : ⟪p -ᵥ a, c -ᵥ a⟫ = 0) :
    dist p b <= dist p c := by
  obtain ⟨t, ⟨ht0, ht1⟩, hb_eq⟩ := h_wbtw
  have h_sq_ineq : dist p b ^ 2 <= dist p c ^ 2 := by
    rw [← hb_eq]; rw [dist_sq_lineMap_of_inner_eq_zero t h_inner]; rw [dist_sq_of_inner_eq_zero h_inner]
.mpr ht1 have ht_sq_le : t ^ 2 <= 1 := sq_le_one_iff₀ ht0
    nlinarith [sq_nonneg (dist p a), sq_nonneg (dist a c)]
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_le_sqrt h_sq_ineq

/--
theorem `dist_lt_of_sbtw_of_mem_perpBisector` / 定理 `dist_lt_of_sbtw_of_mem_perpBisector`

English:
theorem dist_lt_of_sbtw_of_mem_perpBisector
  statement: {a b c p : P}
  proof: dist_lt_of_sbtw_of_inner_eq_zero
(h_sbtw.trans_left_right (sbtw_midpoint_of_ne Real h_sbtw.left_ne)) by
    rw [right_vsub_midpoint]; rw [inner_smul_right]; rw [mem_perpBisector_iff_inner_eq_zero.mp hp]; rw [invOf_eq_inv]; rw [mul_zero]

中文:
定理 dist_lt_of_sbtw_of_mem_perpBisector
  结论: {a b c p : P}
  证明: dist_lt_of_sbtw_of_inner_eq_zero
(h_sbtw.trans_left_right (sbtw_midpoint_of_ne Real h_sbtw.left_ne)) by
    rw [right_vsub_midpoint]; rw [inner_smul_right]; rw [mem_perpBisector_iff_inner_eq_zero.mp hp]; rw [invOf_eq_inv]; rw [mul_zero]

Depends on / 依赖: dist_lt_of_sbtw_of_inner_eq_zero, h_sbtw, h_sbtw.left_ne, h_sbtw.trans_left_right, inner_smul_right, invOf_eq_inv, left_ne, mem_perpBisector_iff_inner_eq_zero, mem_perpBisector_iff_inner_eq_zero.mp, mul_zero, right_vsub_midpoint, sbtw_midpoint_of_ne, trans_left_right
-/
theorem dist_lt_of_sbtw_of_mem_perpBisector {a b c p : P}
    (h_sbtw : Sbtw Real a b c)
    (hp : p in AffineSubspace.perpBisector a b) :
    dist p b < dist p c :=
  dist_lt_of_sbtw_of_inner_eq_zero
(h_sbtw.trans_left_right (sbtw_midpoint_of_ne Real h_sbtw.left_ne)) by
    rw [right_vsub_midpoint]; rw [inner_smul_right]; rw [mem_perpBisector_iff_inner_eq_zero.mp hp]; rw [invOf_eq_inv]; rw [mul_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dist_le_of_wbtw_of_mem_perpBisector` / 定理 `dist_le_of_wbtw_of_mem_perpBisector`

English:
theorem dist_le_of_wbtw_of_mem_perpBisector
  statement: {a b c p : P}
  proof: dist_le_of_wbtw_of_inner_eq_zero
(h_wbtw.trans_left_right (wbtw_midpoint Real a b)) by
    rcases h_wbtw.right_mem_image_Ici_of_left_ne hab with ⟨s, -, rfl⟩
    rw [← vsub_add_vsub_cancel (AffineMap.lineMap a b s) a]; rw [AffineMap.lineMap_vsub_left]; rw [left_vsub_midpoint]; rw [← neg_vsub_eq_vsub_rev b a]; rw [smul_neg]; rw [← sub_eq_add_neg]; rw [inner_sub_right]; rw [inner_smul_right]; rw [inner_smul_right]; rw [mem_perpBisector_iff_inner_eq_zero.mp hp]; rw [mul_zero]; rw [mul_zero]; rw [sub_self]

中文:
定理 dist_le_of_wbtw_of_mem_perpBisector
  结论: {a b c p : P}
  证明: dist_le_of_wbtw_of_inner_eq_zero
(h_wbtw.trans_left_right (wbtw_midpoint Real a b)) by
    rcases h_wbtw.right_mem_image_Ici_of_left_ne hab with ⟨s, -, rfl⟩
    rw [← vsub_add_vsub_cancel (AffineMap.lineMap a b s) a]; rw [AffineMap.lineMap_vsub_left]; rw [left_vsub_midpoint]; rw [← neg_vsub_eq_vsub_rev b a]; rw [smul_neg]; rw [← sub_eq_add_neg]; rw [inner_sub_right]; rw [inner_smul_right]; rw [inner_smul_right]; rw [mem_perpBisector_iff_inner_eq_zero.mp hp]; rw [mul_zero]; rw [mul_zero]; rw [sub_self]

Depends on / 依赖: AffineMap, AffineMap.lineMap, AffineMap.lineMap_vsub_left, dist_le_of_wbtw_of_inner_eq_zero, h_wbtw, h_wbtw.right_mem_image_Ici_of_left_ne, h_wbtw.trans_left_right, inner_smul_right, inner_sub_right, left_vsub_midpoint, lineMap, lineMap_vsub_left, mem_perpBisector_iff_inner_eq_zero, mem_perpBisector_iff_inner_eq_zero.mp, mul_zero, neg_vsub_eq_vsub_rev, right_mem_image_Ici_of_left_ne, smul_neg, sub_eq_add_neg, sub_self
-/
theorem dist_le_of_wbtw_of_mem_perpBisector {a b c p : P}
    (h_wbtw : Wbtw Real a b c) (hab : a != b)
    (hp : p in AffineSubspace.perpBisector a b) :
    dist p b <= dist p c :=
  dist_le_of_wbtw_of_inner_eq_zero
(h_wbtw.trans_left_right (wbtw_midpoint Real a b)) by
    rcases h_wbtw.right_mem_image_Ici_of_left_ne hab with ⟨s, -, rfl⟩
    rw [← vsub_add_vsub_cancel (AffineMap.lineMap a b s) a]; rw [AffineMap.lineMap_vsub_left]; rw [left_vsub_midpoint]; rw [← neg_vsub_eq_vsub_rev b a]; rw [smul_neg]; rw [← sub_eq_add_neg]; rw [inner_sub_right]; rw [inner_smul_right]; rw [inner_smul_right]; rw [mem_perpBisector_iff_inner_eq_zero.mp hp]; rw [mul_zero]; rw [mul_zero]; rw [sub_self]

/--
theorem `inner_vsub_vsub_of_dist_eq_of_dist_eq` / 定理 `inner_vsub_vsub_of_dist_eq_of_dist_eq`

English:
theorem inner_vsub_vsub_of_dist_eq_of_dist_eq
  statement: {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
  proof: by
  rw [← Submodule.mem_orthogonal_singleton_iff_inner_left]; rw [← direction_perpBisector]
  apply vsub_mem_direction <;> rwa [mem_perpBisector_iff_dist_eq']

中文:
定理 inner_vsub_vsub_of_dist_eq_of_dist_eq
  结论: {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
  证明: by
  rw [← Submodule.mem_orthogonal_singleton_iff_inner_left]; rw [← direction_perpBisector]
  apply vsub_mem_direction <;> rwa [mem_perpBisector_iff_dist_eq']

Depends on / 依赖: Submodule, Submodule.mem_orthogonal_singleton_iff_inner_left, direction_perpBisector, mem_orthogonal_singleton_iff_inner_left, mem_perpBisector_iff_dist_eq, vsub_mem_direction
-/
theorem inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
    (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 := by
  rw [← Submodule.mem_orthogonal_singleton_iff_inner_left]; rw [← direction_perpBisector]
  apply vsub_mem_direction <;> rwa [mem_perpBisector_iff_dist_eq']

end EuclideanGeometry

variable {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace Real V'] [MetricSpace P']
variable [NormedAddTorsor V' P']

/--
theorem `Isometry.preimage_perpBisector` / 定理 `Isometry.preimage_perpBisector`

English:
theorem Isometry.preimage_perpBisector
  given: {f : P -> P'} (h : Isometry f) (p₁ p₂ : P)
  proof: by
  ext x; simp [mem_perpBisector_iff_dist_eq, h.dist_eq]

中文:
定理 等距.preimage_perpBisector
  条件: {f : P -> P'} (h : 等距 f) (p₁ p₂ : P)
  证明: by
  ext x; simp [mem_perpBisector_iff_dist_eq, h.dist_eq]

Depends on / 依赖: dist_eq, h.dist_eq, mem_perpBisector_iff_dist_eq
-/
theorem Isometry.preimage_perpBisector {f : P -> P'} (h : Isometry f) (p₁ p₂ : P) :
    f ⁻¹' (perpBisector (f p₁) (f p₂)) = perpBisector p₁ p₂ := by
  ext x; simp [mem_perpBisector_iff_dist_eq, h.dist_eq]

/--
theorem `Isometry.mapsTo_perpBisector` / 定理 `Isometry.mapsTo_perpBisector`

English:
theorem Isometry.mapsTo_perpBisector
  given: {f : P -> P'} (h : Isometry f) (p₁ p₂ : P)
  proof: (h.preimage_perpBisector p₁ p₂).ge

中文:
定理 等距.mapsTo_perpBisector
  条件: {f : P -> P'} (h : 等距 f) (p₁ p₂ : P)
  证明: (h.preimage_perpBisector p₁ p₂).ge

Depends on / 依赖: h.preimage_perpBisector, preimage_perpBisector
-/
theorem Isometry.mapsTo_perpBisector {f : P -> P'} (h : Isometry f) (p₁ p₂ : P) :
    MapsTo f (perpBisector p₁ p₂) (perpBisector (f p₁) (f p₂)) :=
  (h.preimage_perpBisector p₁ p₂).ge
