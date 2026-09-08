/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Spaces orthogonal to the radius vector in spheres.

This file defines the affine subspace orthogonal to the radius vector at a point.

## Main definitions

* `EuclideanGeometry.Sphere.orthRadius`: the affine subspace orthogonal to the radius vector at
  a point (the tangent space, if that point lies in the sphere; more generally, the polar of the
  inversion of that point in the sphere).

-/

@[expose] public section


namespace EuclideanGeometry

namespace Sphere

open AffineSubspace Function RealInnerProductSpace
open scoped Affine

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The affine subspace orthogonal to the radius vector of the sphere `s` at the point `p` (if
`p` lies in `s`, this is the tangent space; generally, this is the polar of the inversion of `p`
in `s`). -/
/-
**EuclideanGeometry.Sphere.orthRadius** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeomet
ry.Sphere`。
形式化陈述：orthRadius (s : Sphere P) (p : P) : AffineSubspace Real P
参数：s : Sphere P；p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine subspace orthogonal to the radius vector of the sphere `s` at the poi
nt `p` (if
`p` lies in `s`, this is the tangent space; generally, this is the polar of the 
inversion of `p`
in `s`).
-/
noncomputable def orthRadius (s : Sphere P) (p : P) : AffineSubspace ℝ P :=
  .mk' p (ℝ ∙ (p -ᵥ s.center))ᗮ
/-
**EuclideanGeometry.Sphere.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanGeometry.Sphere`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : Sphere P) (p : P) : Nonempty (s.orthRadius p) := by
  rw [orthRadius]
  infer_instance
/-
**EuclideanGeometry.Sphere.self_mem_orthRadius** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p : P), p ∈ s.orthRadius p
参数：s : EuclideanGeometry.Sphere P；p : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction
-/
@[simp] lemma self_mem_orthRadius (s : Sphere P) (p : P) : p ∈ s.orthRadius p :=
  self_mem_mk' _ _
/-
**EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left** 是 Mathlib 中的一个引理，位于命名
空间 `EuclideanGeometry.Sphere`。
形式化陈述：mem_orthRadius_iff_inner_left {s : Sphere P} {p x : P} : x in s.orthRadius
 p ↔ ⟪x -ᵥ p, p -ᵥ s.center⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.orthRadius.eq_1`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `AffineSubspace.mem_mk'`：mem_mk' {p q : P} {direction : Submodule k V} : 
q in mk' p direction ↔ q -ᵥ p in direction
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_left`：mem_orthogonal_single
ton_iff_inner_left {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_orthRadius_iff_inner_left {s : Sphere P} {p x : P} :
    x ∈ s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.center⟫ = 0 := by
  rw [orthRadius, mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_left]
/-
**EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_right** 是 Mathlib 中的一个引理，位于命
名空间 `EuclideanGeometry.Sphere`。
形式化陈述：mem_orthRadius_iff_inner_right {s : Sphere P} {p x : P} : x in s.orthRadiu
s p ↔ ⟪p -ᵥ s.center, x -ᵥ p⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left`：mem_orthRadius_i
ff_inner_left {s : Sphere P} {p x : P} : x in s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.c
enter⟫ = 0
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_orthRadius_iff_inner_right {s : Sphere P} {p x : P} :
    x ∈ s.orthRadius p ↔ ⟪p -ᵥ s.center, x -ᵥ p⟫ = 0 := by
  rw [mem_orthRadius_iff_inner_left, inner_eq_zero_symm]
/-
**EuclideanGeometry.Sphere.direction_orthRadius** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p : P),   (s.orthRadius p).direction = (ℝ ∙ (p 
-ᵥ s.center))ᗮ
参数：s : EuclideanGeometry.Sphere P；p : P；s.orthRadius p；ℝ ∙ (p -ᵥ s.center)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.orthRadius.eq_1`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
-/
@[simp] lemma direction_orthRadius (s : Sphere P) (p : P) :
    (s.orthRadius p).direction = (ℝ ∙ (p -ᵥ s.center))ᗮ := by
  rw [orthRadius, direction_mk']
/-
**EuclideanGeometry.Sphere.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanGeometry.Sphere`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : Sphere P) (p : P) : (s.orthRadius p).direction.HasOrthogonalProjection := by
  rw [direction_orthRadius]
  infer_instance
/-
**EuclideanGeometry.Sphere.orthRadius_center** 是 Mathlib 中的一个定理，位于命名空间 `Euclidea
nGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P), s.orthRadius s.center = ⊤
参数：s : EuclideanGeometry.Sphere P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `Submodule.bot_orthogonal_eq_top`：bot_orthogonal_eq_top : (⊥ : Submodule 
𝕜 E)ᗮ = ⊤
· 使用定理 `AffineSubspace.mk'_top`：∀ (k : Type u_1) (V : Type u_2) {P : Type u_3} [
inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : Add
Torsor V P] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma orthRadius_center (s : Sphere P) : s.orthRadius s.center = ⊤ := by
  simp [orthRadius]
/-
**EuclideanGeometry.Sphere.center_mem_orthRadius_iff** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P}, s.center ∈ s.orthRadius p ↔ p = s.cente
r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left`：mem_orthRadius_i
ff_inner_left {s : Sphere P} {p x : P} : x in s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.c
enter⟫ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma center_mem_orthRadius_iff {s : Sphere P} {p : P} :
    s.center ∈ s.orthRadius p ↔ p = s.center := by
  rw [mem_orthRadius_iff_inner_left, ← neg_vsub_eq_vsub_rev, inner_neg_left]
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**EuclideanGeometry.Sphere.orthogonalProjection_orthRadius_center** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p : P),   ↑((EuclideanGeometry.orthogonalProjec
tion (s.orthRadius p)) s.center) = p
参数：s : EuclideanGeometry.Sphere P；p : P；(EuclideanGeometry.orthogonalProjection 
(s.orthRadius p)) s.center。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.instNonemptySubtypeMemAffineSubspaceRealOrthRad
ius`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : Inn
erProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.instHasOrthogonalProjectionRealDirectionOrthRad
ius`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : Inn
erProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma orthogonalProjection_orthRadius_center (s : Sphere P) (p : P) :
    orthogonalProjection (s.orthRadius p) s.center = p := by
  simp_rw [orthRadius, coe_orthogonalProjection_eq_iff_mem]
  rw [← Submodule.neg_mem_iff]
  simp
/-
**EuclideanGeometry.Sphere.orthRadius_le_orthRadius_iff** 是 Mathlib 中的一个引理，位于命名空
间 `EuclideanGeometry.Sphere`。
形式化陈述：orthRadius_le_orthRadius_iff {s : Sphere P} {p q : P} : s.orthRadius p <= 
s.orthRadius q ↔ p = q ∨ q = s.center
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.direction_orthRadius`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `EuclideanGeometry.Sphere.self_mem_orthRadius`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : M
etricSpace P]   [inst_3 : NormedAd…
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `real_inner_smul_right`：real_inner_smul_right (x y : F) (r : Real) : ⟪x, 
r • y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用引理 `EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left`：mem_orthRadius_i
ff_inner_left {s : Sphere P} {p x : P} : x in s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.c
enter⟫ = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `vsub_left_cancel_iff`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] {p₁ p₂ p : P}, p₁ -ᵥ p = p₂ -ᵥ p ↔ p₁ = p₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
（共 32 条，此处仅展示前 30 条）
-/
lemma orthRadius_le_orthRadius_iff {s : Sphere P} {p q : P} :
    s.orthRadius p ≤ s.orthRadius q ↔ p = q ∨ q = s.center := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := direction_le h
    simp only [direction_orthRadius] at h'
    have h'' := Submodule.orthogonal_le h'
    simp only [Submodule.orthogonal_orthogonal, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_span_singleton] at h''
    rcases h'' with ⟨r, hr⟩
    have hp : p ∈ s.orthRadius q := h (s.self_mem_orthRadius p)
    rw [mem_orthRadius_iff_inner_left, ← vsub_sub_vsub_cancel_right p q s.center, ← hr,
      inner_sub_left, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← sub_mul,
      mul_eq_zero] at hp
    rcases hp with hp | hp
    · nth_rw 1 [← one_mul r] at hp
      rw [← sub_mul, mul_eq_zero] at hp
      rcases hp with hp | rfl
      · rw [sub_eq_zero] at hp
        rw [← hp, one_smul, vsub_left_cancel_iff] at hr
        exact .inl hr
      · rw [zero_smul, eq_comm, vsub_eq_zero_iff_eq] at hr
        exact .inr hr
    · simp only [inner_self_eq_zero, vsub_eq_zero_iff_eq] at hp
      rw [hp, vsub_self, smul_zero, eq_comm, vsub_eq_zero_iff_eq] at hr
      exact .inr hr
  · rcases h with rfl | rfl <;> simp
/-
**EuclideanGeometry.Sphere.orthRadius_eq_orthRadius_iff** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p q : P}, s.orthRadius p = s.orthRadius q ↔ p =
 q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `EuclideanGeometry.Sphere.orthRadius_le_orthRadius_iff`：orthRadius_le_ort
hRadius_iff {s : Sphere P} {p q : P} : s.orthRadius p <= s.orthRadius q ↔ p = q 
∨ q = s.center
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma orthRadius_eq_orthRadius_iff {s : Sphere P} {p q : P} :
    s.orthRadius p = s.orthRadius q ↔ p = q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hpq := orthRadius_le_orthRadius_iff.1 h.le
  have hqp := orthRadius_le_orthRadius_iff.1 h.symm.le
  grind
/-
**EuclideanGeometry.Sphere.orthRadius_injective** 是 Mathlib 中的一个引理，位于命名空间 `Eucli
deanGeometry.Sphere`。
形式化陈述：orthRadius_injective (s : Sphere P) : Injective s.orthRadius
参数：s : Sphere P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.Sphere.orthRadius_eq_orthRadius_iff`：∀ {V : Type u_1} 
{P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [i
nst_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma orthRadius_injective (s : Sphere P) : Injective s.orthRadius :=
  fun _ _ ↦ orthRadius_eq_orthRadius_iff.1
/-
**EuclideanGeometry.Sphere.finrank_orthRadius** 是 Mathlib 中的一个引理，位于命名空间 `Euclide
anGeometry.Sphere`。
形式化陈述：finrank_orthRadius [FiniteDimensional Real V] {s : Sphere P} {p : P} (hp :
 p != s.center) : Module.finrank Real (s.orthRadius p).direction + 1 = Module.fi
nrank Real V
参数：hp : p != s.center。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.orthRadius.eq_1`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `Submodule.finrank_add_finrank_orthogonal`：finrank_add_finrank_orthogonal
 [FiniteDimensional 𝕜 E] (K : Submodule 𝕜 E) : finrank 𝕜 K + finrank 𝕜 Kᗮ = finr
ank 𝕜 E
-/
lemma finrank_orthRadius [FiniteDimensional ℝ V] {s : Sphere P} {p : P} (hp : p ≠ s.center) :
    Module.finrank ℝ (s.orthRadius p).direction + 1 = Module.finrank ℝ V := by
  rw [orthRadius, add_comm, direction_mk']
  convert! (ℝ ∙ (p -ᵥ s.center)).finrank_add_finrank_orthogonal
  exact (finrank_span_singleton (vsub_ne_zero.2 hp)).symm
/-
**EuclideanGeometry.Sphere.orthRadius_map** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGe
ometry.Sphere`。
形式化陈述：orthRadius_map {s : Sphere P} (p : P) {f : P ≃ᵃⁱ[Real] P} (h : f s.center 
= s.center) : (s.orthRadius p).map f.toAffineMap = s.orthRadius (f p)
参数：p : P；h : f s.center = s.center。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.orthRadius.eq_1`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用引理 `AffineSubspace.map_mk'`：map_mk' (p : P₁) (direction : Submodule k V₁) : 
(mk' p direction).map f = mk' (f p) (direction.map f.linear)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `AffineIsometryEquiv.map_vsub`：map_vsub (p1 p2 : P) : e.linearIsometryEqu
iv (p1 -ᵥ p2) = e p1 -ᵥ e p2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Submodule.map_orthogonal_equiv`：map_orthogonal_equiv (f : E ≃ₗᵢ[𝕜] F) : 
Kᗮ.map (f.toLinearEquiv : E ->ₗ[𝕜] F) = (K.map (f.toLinearEquiv : E ->ₗ[𝕜] F))ᗮ
-/
lemma orthRadius_map {s : Sphere P} (p : P) {f : P ≃ᵃⁱ[ℝ] P} (h : f s.center = s.center) :
    (s.orthRadius p).map f.toAffineMap = s.orthRadius (f p) := by
  rw [orthRadius, map_mk', orthRadius]
  convert! rfl using 2
  convert! (Submodule.map_orthogonal_equiv (ℝ ∙ (p -ᵥ s.center)) f.linearIsometryEquiv).symm
  simp [Submodule.map_span, Set.image_singleton, h]
/-
**EuclideanGeometry.Sphere.direction_orthRadius_le_iff** 是 Mathlib 中的一个引理，位于命名空间
 `EuclideanGeometry.Sphere`。
形式化陈述：direction_orthRadius_le_iff {s : Sphere P} {p q : P} : (s.orthRadius p).di
rection <= (s.orthRadius q).direction ↔ exists r : Real, q -ᵥ s.center = r • (p 
-ᵥ s.center)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.direction_orthRadius`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma direction_orthRadius_le_iff {s : Sphere P} {p q : P} :
    (s.orthRadius p).direction ≤ (s.orthRadius q).direction ↔
      ∃ r : ℝ, q -ᵥ s.center = r • (p -ᵥ s.center) := by
  simp [Submodule.orthogonal_le_orthogonal_iff, Submodule.mem_span_singleton, eq_comm]
/-
**EuclideanGeometry.Sphere.orthRadius_parallel_orthRadius_iff** 是 Mathlib 中的一个引理
，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：orthRadius_parallel_orthRadius_iff {s : Sphere P} {p q : P} : s.orthRadius
 p ∥ s.orthRadius q ↔ exists r : Real, r != 0 ∧ q -ᵥ s.center = r • (p -ᵥ s.cent
er)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma orthRadius_parallel_orthRadius_iff {s : Sphere P} {p q : P} :
    s.orthRadius p ∥ s.orthRadius q ↔ ∃ r : ℝ, r ≠ 0 ∧ q -ᵥ s.center = r • (p -ᵥ s.center) := by
  simp_rw [orthRadius, parallel_iff_direction_eq_and_eq_bot_iff_eq_bot, direction_mk',
    Submodule.orthogonalComplement_eq_orthogonalComplement,
    Submodule.span_singleton_eq_span_singleton, ← coe_eq_bot_iff,
    ← Set.not_nonempty_iff_eq_empty, mk'_nonempty, and_true, ← Units.exists_iff_ne_zero, eq_comm,
    Units.smul_def]
/-
**EuclideanGeometry.Sphere.dist_sq_eq_iff_mem_orthRadius** 是 Mathlib 中的一个引理，位于命名
空间 `EuclideanGeometry.Sphere`。
形式化陈述：dist_sq_eq_iff_mem_orthRadius {s : Sphere P} {p q : P} : (dist q s.center)
 ^ 2 = (dist p s.center) ^ 2 + (dist q p) ^ 2 ↔ q in s.orthRadius p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`：norm_add_sq_e
q_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0
· 使用引理 `EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left`：mem_orthRadius_i
ff_inner_left {s : Sphere P} {p x : P} : x in s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.c
enter⟫ = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma dist_sq_eq_iff_mem_orthRadius {s : Sphere P} {p q : P} :
    (dist q s.center) ^ 2 = (dist p s.center) ^ 2 + (dist q p) ^ 2 ↔ q ∈ s.orthRadius p := by
  simp_rw [dist_eq_norm_vsub, pow_two]
  rw [← vsub_add_vsub_cancel q p s.center]
  nth_rw 3 [add_comm]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, ← mem_orthRadius_iff_inner_left]

alias ⟨_, dist_sq_eq_of_mem_orthRadius⟩ := dist_sq_eq_iff_mem_orthRadius
/-
**EuclideanGeometry.Sphere.mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_a
nd_norm_sq** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_sq {s : Spher
e P} {p q : P} : q in (s inter s.orthRadius p : Set P) ↔ 0 <= s.radius ∧ q -ᵥ p 
in (Real ∙ (p -ᵥ s.center))ᗮ ∧ ‖q -ᵥ p‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^
 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSubspace.vsub_right_mem_direction_iff_mem`：vsub_right_mem_directio
n_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p₂ -ᵥ p in s
.direction ↔ p₂ in s
· 使用定理 `EuclideanGeometry.Sphere.self_mem_orthRadius`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : M
etricSpace P]   [inst_3 : NormedAd…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `EuclideanGeometry.Sphere.radius_nonneg_of_mem`：∀ {P : Type u_2} [inst : 
MetricSpace P] {s : EuclideanGeometry.Sphere P} {p : P}, p ∈ s → 0 ≤ s.radius
-/
lemma mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_sq {s : Sphere P} {p q : P} :
    q ∈ (s ∩ s.orthRadius p : Set P) ↔ 0 ≤ s.radius ∧
      q -ᵥ p ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ ∧ ‖q -ᵥ p‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^ 2 := by
  simp only [Set.mem_inter_iff, Metric.mem_sphere, mem_coe', SetLike.mem_coe,
    ← dist_sq_eq_iff_mem_orthRadius, ← direction_orthRadius,
    vsub_right_mem_direction_iff_mem (s.self_mem_orthRadius p), ← dist_eq_norm_vsub]
  nth_rw 3 [and_comm]
  rw [← and_assoc, and_congr_left_iff]
  intro h
  rw [← sub_eq_iff_eq_add'] at h
  rw [← h]
  rcases le_or_gt 0 s.radius with h0 | h0
  · simp [h0]
  · simp only [h0.not_ge, sub_left_inj, false_and, iff_false]
    intro hm
    exact h0.not_ge (radius_nonneg_of_mem hm)
/-
**EuclideanGeometry.Sphere.mem_inter_orthRadius_iff_vsub_mem_and_norm_sq** 是 Mat
hlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：mem_inter_orthRadius_iff_vsub_mem_and_norm_sq {s : Sphere P} {p q : P} (h 
: 0 <= s.radius) : q in (s inter s.orthRadius p : Set P) ↔ q -ᵥ p in (Real ∙ (p 
-ᵥ s.center))ᗮ ∧ ‖q -ᵥ p‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^ 2
参数：h : 0 <= s.radius。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.mem_inter_orthRadius_iff_radius_nonneg_and_vsub
_mem_and_norm_sq`：mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_s
q {s : Sphere P} {p q : P} : q in (s inter s.orthRadius p : Set P) ↔ 0 <= s.ra…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_inter_orthRadius_iff_vsub_mem_and_norm_sq {s : Sphere P} {p q : P} (h : 0 ≤ s.radius) :
    q ∈ (s ∩ s.orthRadius p : Set P) ↔
      q -ᵥ p ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ ∧ ‖q -ᵥ p‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^ 2 := by
  rw [mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_sq]
  simp [h]
/-
**EuclideanGeometry.Sphere.vadd_mem_inter_orthRadius_iff_norm_sq** 是 Mathlib 中的一
个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：vadd_mem_inter_orthRadius_iff_norm_sq {s : Sphere P} {p : P} {v : V} (h : 
0 <= s.radius) (hv : v in (Real ∙ (p -ᵥ s.center))ᗮ) : v +ᵥ p in (s inter s.orth
Radius p : Set P) ↔ ‖v‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^ 2
参数：h : 0 <= s.radius；hv : v in (Real ∙ (p -ᵥ s.center))ᗮ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.mem_inter_orthRadius_iff_vsub_mem_and_norm_sq`：
mem_inter_orthRadius_iff_vsub_mem_and_norm_sq {s : Sphere P} {p q : P} (h : 0 <=
 s.radius) : q in (s inter s.orthRadius p : Set P) ↔ q -ᵥ p …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma vadd_mem_inter_orthRadius_iff_norm_sq {s : Sphere P} {p : P} {v : V} (h : 0 ≤ s.radius)
    (hv : v ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ) :
    v +ᵥ p ∈ (s ∩ s.orthRadius p : Set P) ↔ ‖v‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^ 2 := by
  rw [mem_inter_orthRadius_iff_vsub_mem_and_norm_sq h]
  simp [hv]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two
/-
**EuclideanGeometry.Sphere.inter_orthRadius_eq_singleton_of_dist_eq_radius** 是 M
athlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：inter_orthRadius_eq_singleton_of_dist_eq_radius {s : Sphere P} {p : P} (hp
 : dist p s.center = s.radius) : (s inter s.orthRadius p : Set P) = {p}
参数：hp : dist p s.center = s.radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanGeometry.Sphere.dist_sq_eq_of_mem_orthRadius`：∀ {V : Type u_1} 
{P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [i
nst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma inter_orthRadius_eq_singleton_of_dist_eq_radius {s : Sphere P} {p : P}
    (hp : dist p s.center = s.radius) : (s ∩ s.orthRadius p : Set P) = {p} := by
  ext p'
  simp only [Set.mem_inter_iff, Metric.mem_sphere, mem_coe', SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp's, hp'i⟩
    have h' := dist_sq_eq_of_mem_orthRadius hp'i
    rw [hp's, hp] at h'
    simpa using h'
  · rintro rfl
    simpa using hp
/-
**EuclideanGeometry.Sphere.inter_orthRadius_eq_singleton_iff** 是 Mathlib 中的一个引理，
位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：inter_orthRadius_eq_singleton_iff {s : Sphere P} {p q : P} : (s inter s.or
thRadius p : Set P) = {q} ↔ q = p ∧ dist p s.center = s.radius
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `EuclideanGeometry.Sphere.radius_nonneg_of_mem`：∀ {P : Type u_2} [inst : 
MetricSpace P] {s : EuclideanGeometry.Sphere P} {p : P}, p ∈ s → 0 ≤ s.radius
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `EuclideanGeometry.Sphere.mem_inter_orthRadius_iff_vsub_mem_and_norm_sq`：
mem_inter_orthRadius_iff_vsub_mem_and_norm_sq {s : Sphere P} {p q : P} (h : 0 <=
 s.radius) : q in (s inter s.orthRadius p : Set P) ↔ q -ᵥ p …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 35 条，此处仅展示前 30 条）
-/
lemma inter_orthRadius_eq_singleton_iff {s : Sphere P} {p q : P} :
    (s ∩ s.orthRadius p : Set P) = {q} ↔ q = p ∧ dist p s.center = s.radius := by
  constructor
  · intro h
    have hq : q ∈ (s ∩ s.orthRadius p : Set P) := h ▸ Set.mem_singleton _
    have h' (q' : P) : q' ∈ (s ∩ s.orthRadius p : Set P) ↔ q' = q := by simp [h]
    have hr : 0 ≤ s.radius := radius_nonneg_of_mem hq.1
    simp_rw [mem_inter_orthRadius_iff_vsub_mem_and_norm_sq hr] at h'
    have hq' := (h' q).2 rfl
    have hq'' : (-(q -ᵥ p) +ᵥ p) -ᵥ p ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ ∧
        ‖(-(q -ᵥ p) +ᵥ p) -ᵥ p‖ ^ 2 = s.radius ^ 2 - dist p s.center ^ 2 := by
      simpa [-neg_vsub_eq_vsub_rev] using hq'
    have hqq := (h' _).1 hq''
    rw [eq_comm, eq_vadd_iff_vsub_eq, eq_neg_iff_add_eq_zero, ← two_smul ℝ,
      smul_eq_zero_iff_right (by norm_num), vsub_eq_zero_iff_eq] at hqq
    refine ⟨hqq, ?_⟩
    subst hqq
    exact hq.1
  · rintro ⟨rfl, h⟩
    exact inter_orthRadius_eq_singleton_of_dist_eq_radius h
/-
**EuclideanGeometry.Sphere.inter_orthRadius_eq_empty_of_radius_lt_dist** 是 Mathl
ib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：inter_orthRadius_eq_empty_of_radius_lt_dist {s : Sphere P} {p : P} (hp : s
.radius < dist p s.center) : (s inter s.orthRadius p : Set P) = ∅
参数：hp : s.radius < dist p s.center。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.mem_inter_orthRadius_iff_radius_nonneg_and_vsub
_mem_and_norm_sq`：mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_s
q {s : Sphere P} {p q : P} : q in (s inter s.orthRadius p : Set P) ↔ 0 <= s.ra…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 83 条，此处仅展示前 30 条）
-/
lemma inter_orthRadius_eq_empty_of_radius_lt_dist {s : Sphere P} {p : P}
    (hp : s.radius < dist p s.center) : (s ∩ s.orthRadius p : Set P) = ∅ := by
  ext p'
  rw [mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_sq]
  simp only [Set.mem_empty_iff_false, iff_false, not_and]
  rintro hle - h
  nlinarith
/-
**EuclideanGeometry.Sphere.inter_orthRadius_eq_empty_of_finrank_eq_one** 是 Mathl
ib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：inter_orthRadius_eq_empty_of_finrank_eq_one {s : Sphere P} {p : P} (hpc : 
p != s.center) (hp : dist p s.center != s.radius) (hf : Module.finrank Real V = 
1) : (s inter s.orthRadius p : Set P) = ∅
参数：hpc : p != s.center；hp : dist p s.center != s.radius；hf : Module.finrank Real
 V = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.mem_inter_orthRadius_iff_radius_nonneg_and_vsub
_mem_and_norm_sq`：mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_s
q {s : Sphere P} {p q : P} : q in (s inter s.orthRadius p : Set P) ↔ 0 <= s.ra…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Module.finite_of_finrank_eq_succ`：finite_of_finrank_eq_succ {n : Nat} (h
n : finrank R M = n.succ) : Module.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Submodule.finrank_add_finrank_orthogonal`：finrank_add_finrank_orthogonal
 [FiniteDimensional 𝕜 E] (K : Submodule 𝕜 E) : finrank 𝕜 K + finrank 𝕜 Kᗮ = finr
ank 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Submodule.top_orthogonal_eq_bot`：top_orthogonal_eq_bot : (⊤ : Submodule 
𝕜 E)ᗮ = ⊥
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
（共 35 条，此处仅展示前 30 条）
-/
lemma inter_orthRadius_eq_empty_of_finrank_eq_one {s : Sphere P} {p : P} (hpc : p ≠ s.center)
    (hp : dist p s.center ≠ s.radius) (hf : Module.finrank ℝ V = 1) :
    (s ∩ s.orthRadius p : Set P) = ∅ := by
  ext p'
  rw [mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_sq]
  simp only [Set.mem_empty_iff_false, iff_false, not_and]
  intro hr hpo
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hf
  have ha := (ℝ ∙ (p -ᵥ s.center)).finrank_add_finrank_orthogonal
  simp only [finrank_span_singleton (vsub_ne_zero.2 hpc), hf, Nat.add_eq_left,
    Submodule.finrank_eq_zero, Submodule.orthogonal_eq_bot_iff] at ha
  simp only [ha, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hpo
  simp only [hpo, vsub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [eq_comm, sub_eq_zero, eq_comm, sq_eq_sq₀ dist_nonneg hr]
  exact hp
/-
**EuclideanGeometry.Sphere.inter_orthRadius_eq_empty_iff** 是 Mathlib 中的一个引理，位于命名
空间 `EuclideanGeometry.Sphere`。
形式化陈述：inter_orthRadius_eq_empty_iff {s : Sphere P} {p : P} : (s inter s.orthRadi
us p : Set P) = ∅ ↔ s.radius < dist p s.center ∨ (Module.finrank Real V = 1 ∧ di
st p s.center < s.radius ∧ p != s.center) ∨ (Subsingleton V ∧ s.radius != 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddTorsor.subsingleton_iff`：∀ (G : Type u_1) (P : Type u_2) [inst : AddG
roup G] [AddTorsor G P], Subsingleton G ↔ Subsingleton P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Metric.sphere_eq_empty_of_subsingleton`：sphere_eq_empty_of_subsingleton 
[Subsingleton α] (hε : ε != 0) : sphere x ε = ∅
· 使用定理 `EuclideanGeometry.Sphere.orthRadius_center`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
（共 82 条，此处仅展示前 30 条）
-/
lemma inter_orthRadius_eq_empty_iff {s : Sphere P} {p : P} :
    (s ∩ s.orthRadius p : Set P) = ∅ ↔ s.radius < dist p s.center ∨
      (Module.finrank ℝ V = 1 ∧ dist p s.center < s.radius ∧ p ≠ s.center) ∨
      (Subsingleton V ∧ s.radius ≠ 0) := by
  rcases lt_trichotomy (dist p s.center) s.radius with h | h | h
  · simp only [h.not_gt, h, ne_eq, true_and, (dist_nonneg.trans_lt h).ne', not_false_eq_true,
      and_true, false_or]
    obtain rfl | hp := eq_or_ne p s.center
    · rcases subsingleton_or_nontrivial V with hs | hs
      · have hs' := (AddTorsor.subsingleton_iff V P).1 hs
        simp [hs, Metric.sphere_eq_empty_of_subsingleton (dist_nonneg.trans_lt h).ne']
      · simp only [orthRadius_center, top_coe, Set.inter_univ, not_true_eq_false, and_false,
          not_subsingleton_iff_nontrivial.2 hs, or_self, iff_false, ← Set.nonempty_iff_ne_empty]
        obtain ⟨v, hv⟩ := exists_norm_eq V (dist_nonneg.trans_lt h).le
        exact ⟨v +ᵥ s.center, by simp [hv]⟩
    · simp only [hp, not_false_eq_true, and_true]
      rcases eq_or_ne (ℝ ∙ (p -ᵥ s.center)) ⊤ with hb | hb
      · have hb' := hb
        rw [Submodule.span_singleton_eq_top_iff] at hb'
        have hf := finrank_eq_one_iff'.2 ⟨p -ᵥ s.center, vsub_ne_zero.2 hp, hb'⟩
        simpa [hf] using inter_orthRadius_eq_empty_of_finrank_eq_one hp h.ne
      · have hn : ¬Subsingleton V := by
          rw [AddTorsor.subsingleton_iff V P]
          intro hs
          simp [Subsingleton.elim p s.center] at hp
        have hnf : Module.finrank ℝ V ≠ 1 := by
          intro hf
          apply hb
          rw [Submodule.span_singleton_eq_top_iff]
          rw [finrank_eq_one_iff'] at hf
          obtain ⟨v, hv0, hv⟩ := hf
          obtain ⟨c, hc⟩ := hv (p -ᵥ s.center)
          have hc0 : c ≠ 0 := by
            rintro rfl
            rw [zero_smul, eq_comm, vsub_eq_zero_iff_eq] at hc
            simp [hc] at hp
          intro v'
          obtain ⟨c', rfl⟩ := hv v'
          refine ⟨c' / c, ?_⟩
          simp [← hc, smul_smul, hc0]
        simp only [hnf, hn, or_self, iff_false, ← Set.nonempty_iff_ne_empty]
        rw [ne_eq, ← Submodule.orthogonal_eq_bot_iff] at hb
        obtain ⟨v, hvm, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
        refine ⟨(√(s.radius ^ 2 - (dist p s.center) ^ 2) / ‖v‖) • v +ᵥ p, ?_⟩
        rw [vadd_mem_inter_orthRadius_iff_norm_sq (dist_nonneg.trans_lt h).le
          (Submodule.smul_mem _ _ hvm)]
        rw [norm_smul, norm_div, norm_norm, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv0)]
        simp only [Real.norm_eq_abs, sq_abs]
        refine Real.sq_sqrt ?_
        rw [sub_nonneg, sq_le_sq, abs_of_nonneg dist_nonneg]
        exact h.le.trans (le_abs_self _)
  · rw [inter_orthRadius_eq_singleton_of_dist_eq_radius h]
    simp only [Set.singleton_ne_empty, h, lt_self_iff_false, ne_eq, false_and, and_false, false_or,
      false_iff, not_and, not_not]
    intro hs
    rw [AddTorsor.subsingleton_iff V P] at hs
    rw [Subsingleton.elim p s.center] at h
    simpa using h.symm
  · simp [h, inter_orthRadius_eq_empty_of_radius_lt_dist]

/-- In 2D, the line defined by `s.orthRadius p` intersects `s` at at most two points so long as `p`
lies within `s` and not at its center.

This version provides expressions for those points in terms of an arbitrary vector in
`s.orthRadius p` with norm `1`. -/
/-
**EuclideanGeometry.Sphere.inter_orthRadius_eq_of_dist_le_radius_of_norm_eq_one*
* 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：inter_orthRadius_eq_of_dist_le_radius_of_norm_eq_one [hf2 : Fact (Module.f
inrank Real V = 2)] {s : Sphere P} {p : P} (hp : dist p s.center <= s.radius) (h
pc : p != s.center) {v : V} (hv : v in (Real ∙ (p -ᵥ s.center))ᗮ) (hv1 : ‖v‖ = 1
) : (s inter s.orthRadius p : Set P) = {√(s.radius ^ 2 - (dist p s.center) ^ 2) 
• v +ᵥ p, -√(s.radius ^ 2 - (dist p s.center) ^ 2) • v +ᵥ p}
参数：Module.finrank Real V = 2；hp : dist p s.center <= s.radius；hpc : p != s.cente
r；hv : v in (Real ∙ (p -ᵥ s.center))ᗮ；hv1 : ‖v‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `EuclideanGeometry.Sphere.finrank_orthRadius`：finrank_orthRadius [FiniteD
imensional Real V] {s : Sphere P} {p : P} (hp : p != s.center) : Module.finrank 
Real (s.orthRadius p).direction +…
· 使用引理 `FiniteDimensional.of_fact_finrank_eq_two`：of_fact_finrank_eq_two [Fact (
finrank K V = 2)] : FiniteDimensional K V
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `finrank_eq_one_iff_of_nonzero'`：finrank_eq_one_iff_of_nonzero' (v : V) (
nz : v != 0) : finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.Simproc.add_eq_le`：∀ (a : ℕ) {b c : ℕ}, b ≤ c → (a + b = c) = (a = c
 - b)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `EuclideanGeometry.Sphere.direction_orthRadius`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `sq_le_sq`：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] {a
 b : α}, a ≤ |b| ↔ a ≤ b ∨ a ≤ -b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
In 2D, the line defined by `s.orthRadius p` intersects `s` at at most two points
 so long as `p`
lies within `s` and not at its center.

This version provides expressions for those points in terms of an arbitrary vect
or in
`s.orthRadius p` with norm `1`.
-/
lemma inter_orthRadius_eq_of_dist_le_radius_of_norm_eq_one [hf2 : Fact (Module.finrank ℝ V = 2)]
    {s : Sphere P} {p : P} (hp : dist p s.center ≤ s.radius) (hpc : p ≠ s.center) {v : V}
    (hv : v ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ) (hv1 : ‖v‖ = 1) :
    (s ∩ s.orthRadius p : Set P) = {√(s.radius ^ 2 - (dist p s.center) ^ 2) • v +ᵥ p,
      -√(s.radius ^ 2 - (dist p s.center) ^ 2) • v +ᵥ p} := by
  have hr : 0 ≤ s.radius := dist_nonneg.trans hp
  have hv0 : v ≠ 0 := by rw [← norm_ne_zero_iff, hv1]; simp
  rw [neg_smul]
  have hf := finrank_orthRadius hpc
  rw [direction_orthRadius] at hf
  simp only [hf2.out, Nat.reduceEqDiff] at hf
  rw [finrank_eq_one_iff_of_nonzero' ⟨v, hv⟩ (by simpa using hv0)] at hf
  have hvc : ∀ w ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ, ∃ c : ℝ, c • v = w := by
    intro w hw
    simpa using hf ⟨w, hw⟩
  have hvp : 0 ≤ s.radius ^ 2 - (dist p s.center) ^ 2 := by
    rw [sub_nonneg, sq_le_sq, abs_of_nonneg dist_nonneg]
    exact le_abs.2 (.inl hp)
  ext p'
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← vsub_vadd p' p, Set.mem_insert_iff, Set.mem_singleton_iff, vadd_right_cancel_iff,
      vadd_right_cancel_iff]
    have h' : p' -ᵥ p ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ := by
      rw [← direction_orthRadius, vsub_right_mem_direction_iff_mem (s.self_mem_orthRadius p)]
      exact h.2
    rw [← vsub_vadd p' p, vadd_mem_inter_orthRadius_iff_norm_sq hr h'] at h
    obtain ⟨c, hc⟩ := hvc _ h'
    rw [← hc] at h ⊢
    rw [← neg_smul]
    simp_rw [(smul_left_injective ℝ hv0).eq_iff, ← sq_eq_sq_iff_eq_or_eq_neg, Real.sq_sqrt hvp]
    simpa [norm_smul, hv1] using h
  · rw [← neg_smul] at h
    rcases h with rfl | rfl <;>
      rw [vadd_mem_inter_orthRadius_iff_norm_sq hr (Submodule.smul_mem _ _ hv)] <;>
      simp [norm_smul, hv1, hvp]

/-- In 2D, the line defined by `s.orthRadius p` intersects `s` at at most two points so long as `p`
lies within `s` and not at its center.

This version provides expressions for those points in terms of an arbitrary vector in
`s.orthRadius p`. -/
/-
**EuclideanGeometry.Sphere.inter_orthRadius_eq_of_dist_le_radius** 是 Mathlib 中的一
个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：inter_orthRadius_eq_of_dist_le_radius [hf2 : Fact (Module.finrank Real V =
 2)] {s : Sphere P} {p : P} (hp : dist p s.center <= s.radius) (hpc : p != s.cen
ter) {v : V} (hv : v in (Real ∙ (p -ᵥ s.center))ᗮ) (hv0 : v != 0) : (s inter s.o
rthRadius p : Set P) = {(√(s.radius ^ 2 - (dist p s.center) ^ 2) / ‖v‖) • v +ᵥ p
, -(√(s.radius ^ 2 - (dist p s.center) ^ 2) / ‖v‖) • v +ᵥ p}
参数：Module.finrank Real V = 2；hp : dist p s.center <= s.radius；hpc : p != s.cente
r；hv : v in (Real ∙ (p -ᵥ s.center))ᗮ；hv0 : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `EuclideanGeometry.Sphere.inter_orthRadius_eq_of_dist_le_radius_of_norm_e
q_one`：inter_orthRadius_eq_of_dist_le_radius_of_norm_eq_one [hf2 : Fact (Module.
finrank Real V = 2)] {s : Sphere P} {p : P} (hp : dist p s.center <…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
In 2D, the line defined by `s.orthRadius p` intersects `s` at at most two points
 so long as `p`
lies within `s` and not at its center.

This version provides expressions for those points in terms of an arbitrary vect
or in
`s.orthRadius p`.
-/
lemma inter_orthRadius_eq_of_dist_le_radius [hf2 : Fact (Module.finrank ℝ V = 2)]
    {s : Sphere P} {p : P} (hp : dist p s.center ≤ s.radius) (hpc : p ≠ s.center) {v : V}
    (hv : v ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ) (hv0 : v ≠ 0) :
    (s ∩ s.orthRadius p : Set P) = {(√(s.radius ^ 2 - (dist p s.center) ^ 2) / ‖v‖) • v +ᵥ p,
      -(√(s.radius ^ 2 - (dist p s.center) ^ 2) / ‖v‖) • v +ᵥ p} := by
  convert!
    inter_orthRadius_eq_of_dist_le_radius_of_norm_eq_one hp hpc (v := ‖v‖⁻¹ • v)
      (Submodule.smul_mem _ _ hv) ?_ using 2
  · simp [div_eq_mul_inv, smul_smul]
  · simp [div_eq_mul_inv, smul_smul]
  · simp [norm_smul, norm_ne_zero_iff.2 hv0]

/-- In 2D, the line defined by `s.orthRadius p` intersects `s` at exactly two points so long as `p`
lies strictly within `s` and not at its center. -/
/-
**EuclideanGeometry.Sphere.ncard_inter_orthRadius_eq_two_of_dist_lt_radius** 是 M
athlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：ncard_inter_orthRadius_eq_two_of_dist_lt_radius [hf2 : Fact (Module.finran
k Real V = 2)] {s : Sphere P} {p : P} (hp : dist p s.center < s.radius) (hpc : p
 != s.center) : (s inter s.orthRadius p : Set P).ncard = 2
参数：Module.finrank Real V = 2；hp : dist p s.center < s.radius；hpc : p != s.center
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EuclideanGeometry.Sphere.finrank_orthRadius`：finrank_orthRadius [FiniteD
imensional Real V] {s : Sphere P} {p : P} (hp : p != s.center) : Module.finrank 
Real (s.orthRadius p).direction +…
· 使用引理 `FiniteDimensional.of_fact_finrank_eq_two`：of_fact_finrank_eq_two [Fact (
finrank K V = 2)] : FiniteDimensional K V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.Simproc.add_eq_le`：∀ (a : ℕ) {b c : ℕ}, b ≤ c → (a + b = c) = (a = c
 - b)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用引理 `EuclideanGeometry.Sphere.inter_orthRadius_eq_of_dist_le_radius`：inter_or
thRadius_eq_of_dist_le_radius [hf2 : Fact (Module.finrank Real V = 2)] {s : Sphe
re P} {p : P} (hp : dist p s.center <= s.radius) (hp…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.Sphere.direction_orthRadius`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.norm_coe`：norm_coe [Ring 𝕜] [SeminormedAddCommGroup E] [Module
 𝕜 E] {s : Submodule 𝕜 E} (x : s) : ‖(x : E)‖ = ‖x‖
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Set.ncard_pair`：ncard_pair {a b : α} (h : a != b) : ({a, b} : Set α).nca
rd = 2
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `vadd_right_cancel_iff`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] {g₁ g₂ : G} (p : P), g₁ +ᵥ p = g₂ +ᵥ p ↔ g₁ = g₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
In 2D, the line defined by `s.orthRadius p` intersects `s` at exactly two points
 so long as `p`
lies strictly within `s` and not at its center.
-/
lemma ncard_inter_orthRadius_eq_two_of_dist_lt_radius [hf2 : Fact (Module.finrank ℝ V = 2)]
    {s : Sphere P} {p : P} (hp : dist p s.center < s.radius) (hpc : p ≠ s.center) :
    (s ∩ s.orthRadius p : Set P).ncard = 2 := by
  have hf := finrank_orthRadius hpc
  simp only [hf2.out, Nat.reduceEqDiff, finrank_eq_one_iff'] at hf
  obtain ⟨v, hv0, hv⟩ := hf
  replace hv0 : (v : V) ≠ 0 := by simpa using hv0
  rw [inter_orthRadius_eq_of_dist_le_radius hp.le hpc (by simpa using v.property) hv0,
    Submodule.norm_coe, neg_smul, Set.ncard_pair]
  rw [ne_eq, vadd_right_cancel_iff, ← add_eq_zero_iff_eq_neg, ← two_smul ℝ,
    smul_eq_zero_iff_right two_ne_zero, smul_eq_zero_iff_left hv0, div_eq_iff, zero_mul]
  · have hvp : 0 < √(s.radius ^ 2 - dist p s.center ^ 2) := by
      rw [Real.sqrt_pos, sub_pos, sq_lt_sq, abs_of_nonneg dist_nonneg]
      exact lt_abs.2 (.inl hp)
    exact hvp.ne'
  · simpa using hv0
/-
**EuclideanGeometry.Sphere.ncard_inter_orthRadius_le_two** 是 Mathlib 中的一个引理，位于命名
空间 `EuclideanGeometry.Sphere`。
形式化陈述：ncard_inter_orthRadius_le_two [hf2 : Fact (Module.finrank Real V = 2)] {s 
: Sphere P} {p : P} (hpc : p != s.center) : (s inter s.orthRadius p : Set P).nca
rd <= 2
参数：Module.finrank Real V = 2；hpc : p != s.center。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `EuclideanGeometry.Sphere.ncard_inter_orthRadius_eq_two_of_dist_lt_radius
`：ncard_inter_orthRadius_eq_two_of_dist_lt_radius [hf2 : Fact (Module.finrank Re
al V = 2)] {s : Sphere P} {p : P} (hp : dist p s.center < s.ra…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.inter_orthRadius_eq_singleton_of_dist_eq_radius
`：inter_orthRadius_eq_singleton_of_dist_eq_radius {s : Sphere P} {p : P} (hp : d
ist p s.center = s.radius) : (s inter s.orthRadius p : Set P) …
· 使用定理 `Set.ncard_singleton`：∀ {α : Type u_1} (a : α), {a}.ncard = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EuclideanGeometry.Sphere.inter_orthRadius_eq_empty_of_radius_lt_dist`：in
ter_orthRadius_eq_empty_of_radius_lt_dist {s : Sphere P} {p : P} (hp : s.radius 
< dist p s.center) : (s inter s.orthRadius p : Set P) = ∅
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma ncard_inter_orthRadius_le_two [hf2 : Fact (Module.finrank ℝ V = 2)]
    {s : Sphere P} {p : P} (hpc : p ≠ s.center) : (s ∩ s.orthRadius p : Set P).ncard ≤ 2 := by
  rcases lt_trichotomy (dist p s.center) s.radius with h | h | h
  · exact (ncard_inter_orthRadius_eq_two_of_dist_lt_radius h hpc).le
  · simp [inter_orthRadius_eq_singleton_of_dist_eq_radius h]
  · simp [inter_orthRadius_eq_empty_of_radius_lt_dist h]

end Sphere

end EuclideanGeometry

