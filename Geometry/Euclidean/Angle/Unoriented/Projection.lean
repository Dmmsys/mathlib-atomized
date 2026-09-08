/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Angles and orthogonal projection.

This file proves lemmas relating to angles involving orthogonal projections.

-/

public section


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped Real

/-
**EuclideanGeometry.angle_self_orthogonalProjection** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
p : P) {p' : P} {s : AffineSubspace ℝ P}   [inst_4 : s.direction.HasOrthogonalPr
ojection] (h : p' ∈ s),   EuclideanGeometry.angle p (↑((EuclideanGeometry.orthog
onalProjection s) p)) p' = Real.pi / 2
参数：p : P；h : p' ∈ s；↑((EuclideanGeometry.orthogonalProjection s) p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `Submodule.inner_left_of_mem_orthogonal`：inner_left_of_mem_orthogonal {u 
v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪v, u⟫ = 0
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…
-/
@[simp] lemma angle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (h : p' ∈ s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p (orthogonalProjection s p) p' = π / 2 := by
  have : Nonempty s := ⟨p', h⟩
  rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact Submodule.inner_left_of_mem_orthogonal (K := s.direction)
    (AffineSubspace.vsub_mem_direction h (orthogonalProjection_mem _))
    (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
/-
**EuclideanGeometry.angle_orthogonalProjection_self** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
p : P) {p' : P} {s : AffineSubspace ℝ P}   [inst_4 : s.direction.HasOrthogonalPr
ojection] (h : p' ∈ s),   EuclideanGeometry.angle p' (↑((EuclideanGeometry.ortho
gonalProjection s) p)) p = Real.pi / 2
参数：p : P；h : p' ∈ s；↑((EuclideanGeometry.orthogonalProjection s) p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_self_orthogonalProjection`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_
2 : MetricSpace P]   [inst_3 : NormedAd…
-/
@[simp] lemma angle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (h : p' ∈ s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p' (orthogonalProjection s p) p = π / 2 := by
  rw [angle_comm, angle_self_orthogonalProjection p h]

end EuclideanGeometry

