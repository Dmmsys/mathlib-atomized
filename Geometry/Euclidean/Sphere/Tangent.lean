/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Geometry.Euclidean.Sphere.OrthRadius

/-!
# Tangency for spheres.

This file defines notions of spheres being tangent to affine subspaces and other spheres.

## Main definitions

* `EuclideanGeometry.Sphere.IsTangentAt`: the property of an affine subspace being tangent to a
  sphere at a given point.

* `EuclideanGeometry.Sphere.IsTangent`: the property of an affine subspace being tangent to a
  sphere at some point.

* `EuclideanGeometry.Sphere.tangentSet`: the set of all maximal tangent spaces to a given sphere.

* `EuclideanGeometry.Sphere.tangentsFrom`: the set of all maximal tangent spaces to a given
  sphere and containing a given point.

* `EuclideanGeometry.Sphere.commonTangents`: the set of all maximal common tangent spaces to two
  given spheres.

* `EuclideanGeometry.Sphere.commonIntTangents`: the set of all maximal common internal tangent
  spaces to two given spheres.

* `EuclideanGeometry.Sphere.commonExtTangents`: the set of all maximal common external tangent
  spaces to two given spheres.

* `EuclideanGeometry.Sphere.IsExtTangentAt`: the property of two spheres being externally tangent
  at a given point.

* `EuclideanGeometry.Sphere.IsIntTangentAt`: the property of two spheres being internally tangent
  at a given point.

* `EuclideanGeometry.Sphere.IsExtTangent`: the property of two spheres being externally tangent.

* `EuclideanGeometry.Sphere.IsIntTangent`: the property of two spheres being internally tangent.

-/

@[expose] public section


namespace EuclideanGeometry

namespace Sphere

open AffineSubspace RealInnerProductSpace
open scoped Affine

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The affine subspace `as` is tangent to the sphere `s` at the point `p`. -/
/-
**EuclideanGeometry.Sphere.IsTangentAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `EuclideanGeo
metry.Sphere`。
形式化陈述：{V : Type u_1} →   {P : Type u_2} →     [inst : NormedAddCommGroup V] →   
    [inst_1 : InnerProductSpace ℝ V] →         [inst_2 : MetricSpace P] →       
    [inst_3 : NormedAddTorsor V P] → EuclideanGeometry.Sphere P → P → AffineSubs
pace ℝ P → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine subspace `as` is tangent to the sphere `s` at the point `p`.
-/
structure IsTangentAt (s : Sphere P) (p : P) (as : AffineSubspace ℝ P) : Prop where
  mem_sphere : p ∈ s
  mem_space : p ∈ as
  le_orthRadius : as ≤ s.orthRadius p
/-
**EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P}, s.IsTangentAt p (s.orthRadius p) ↔ p ∈ 
s
参数：s.orthRadius p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_sphere`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.self_mem_orthRadius`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : M
etricSpace P]   [inst_3 : NormedAd…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
@[simp] lemma isTangentAt_orthRadius_iff_mem {s : Sphere P} {p : P} :
    s.IsTangentAt p (s.orthRadius p) ↔ p ∈ s :=
  ⟨fun h ↦ h.mem_sphere, fun h ↦ ⟨h, self_mem_orthRadius _ _, le_rfl⟩⟩
/-
**EuclideanGeometry.Sphere.IsTangentAt.inner_left_eq_zero_of_mem** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P} {as : AffineSubspace ℝ P},   s.IsTangent
At p as → ∀ {x : P}, x ∈ as → inner ℝ (x -ᵥ p) (p -ᵥ s.center) = 0
参数：x -ᵥ p；p -ᵥ s.center。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left`：mem_orthRadius_i
ff_inner_left {s : Sphere P} {p x : P} : x in s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.c
enter⟫ = 0
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.le_orthRadius`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma IsTangentAt.inner_left_eq_zero_of_mem {s : Sphere P} {p : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) {x : P} (hx : x ∈ as) : ⟪x -ᵥ p, p -ᵥ s.center⟫ = 0 :=
  mem_orthRadius_iff_inner_left.1 (h.le_orthRadius hx)
/-
**EuclideanGeometry.Sphere.IsTangentAt.inner_right_eq_zero_of_mem** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P} {as : AffineSubspace ℝ P},   s.IsTangent
At p as → ∀ {x : P}, x ∈ as → inner ℝ (p -ᵥ s.center) (x -ᵥ p) = 0
参数：p -ᵥ s.center；x -ᵥ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_right`：mem_orthRadius_
iff_inner_right {s : Sphere P} {p x : P} : x in s.orthRadius p ↔ ⟪p -ᵥ s.center,
 x -ᵥ p⟫ = 0
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.le_orthRadius`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma IsTangentAt.inner_right_eq_zero_of_mem {s : Sphere P} {p : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) {x : P} (hx : x ∈ as) : ⟪p -ᵥ s.center, x -ᵥ p⟫ = 0 :=
  mem_orthRadius_iff_inner_right.1 (h.le_orthRadius hx)
/-
**EuclideanGeometry.Sphere.IsTangentAt.eq_of_isTangentAt** 是 Mathlib 中的一个定理，位于命名
空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p q : P} {as : AffineSubspace ℝ P},   s.IsTange
ntAt p as → s.IsTangentAt q as → p = q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.inner_left_eq_zero_of_mem`：∀ {V : T
ype u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpac
e ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_space`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
-/
lemma IsTangentAt.eq_of_isTangentAt {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (hp : s.IsTangentAt p as) (hq : s.IsTangentAt q as) : p = q := by
  have hqp := hp.inner_left_eq_zero_of_mem hq.mem_space
  have hpq := hq.inner_left_eq_zero_of_mem hp.mem_space
  rw [← neg_vsub_eq_vsub_rev, inner_neg_left, neg_eq_zero, ← hpq, ← sub_eq_zero,
    ← inner_sub_right, vsub_sub_vsub_cancel_right] at hqp
  simpa using hqp
/-
**EuclideanGeometry.Sphere.isTangentAt_center_iff** 是 Mathlib 中的一个引理，位于命名空间 `Euc
lideanGeometry.Sphere`。
形式化陈述：isTangentAt_center_iff {s : Sphere P} {as : AffineSubspace Real P} : s.IsT
angentAt s.center as ↔ s.radius = 0 ∧ s.center in as
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.center_mem_iff`：∀ {P : Type u_2} [inst : Metric
Space P] {s : EuclideanGeometry.Sphere P}, s.center ∈ s ↔ s.radius = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanGeometry.Sphere.orthRadius_center`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
-/
lemma isTangentAt_center_iff {s : Sphere P} {as : AffineSubspace ℝ P} :
    s.IsTangentAt s.center as ↔ s.radius = 0 ∧ s.center ∈ as := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hr, hm, -⟩
    rw [center_mem_iff] at hr
    exact ⟨hr, hm⟩
  · rintro ⟨hr, hm⟩
    refine ⟨?_, hm, ?_⟩
    · rw [center_mem_iff, hr]
    · simp
/-
**EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem** 是 Mathlib 中的一个定理，位于命名
空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p q : P} {as : AffineSubspace ℝ P},   s.IsTange
ntAt p as → q ∈ as → dist q s.center ^ 2 = s.radius ^ 2 + dist q p ^ 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_sphere`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.dist_sq_eq_of_mem_orthRadius`：∀ {V : Type u_1} 
{P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [i
nst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.le_orthRadius`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma IsTangentAt.dist_sq_eq_of_mem {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) (hq : q ∈ as) :
    (dist q s.center) ^ 2 = s.radius ^ 2 + (dist q p) ^ 2 := by
  rw [← h.mem_sphere]
  exact s.dist_sq_eq_of_mem_orthRadius (SetLike.le_def.1 h.le_orthRadius hq)
/-
**EuclideanGeometry.Sphere.IsTangentAt.mem_and_mem_iff_eq** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p q : P} {as : AffineSubspace ℝ P},   s.IsTange
ntAt p as → (q ∈ s ∧ q ∈ as ↔ q = p)
参数：q ∈ s ∧ q ∈ as ↔ q = p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_sphere`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_space`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
-/
lemma IsTangentAt.mem_and_mem_iff_eq {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) : (q ∈ s ∧ q ∈ as) ↔ q = p := by
  refine ⟨fun ⟨hs, has⟩ ↦ ?_, ?_⟩
  · have hd := h.dist_sq_eq_of_mem has
    rw [hs] at hd
    simpa using hd
  · rintro rfl
    exact ⟨h.mem_sphere, h.mem_space⟩
/-
**EuclideanGeometry.Sphere.IsTangentAt.eq_of_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p q : P} {as : AffineSubspace ℝ P},   s.IsTange
ntAt p as → q ∈ s → q ∈ as → q = p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_and_mem_iff_eq`：∀ {V : Type u_1
} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] 
[inst_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma IsTangentAt.eq_of_mem_of_mem {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) (hs : q ∈ s) (has : q ∈ as) : q = p :=
  h.mem_and_mem_iff_eq.1 ⟨hs, has⟩

/-- If two tangent lines to a sphere pass through the same point `q`,
then the distances from `q` to the tangent points are equal. -/
/-
**EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p₁ p₂ q : P} {as₁ as₂ : AffineSubspace ℝ P},   
s.IsTangentAt p₁ as₁ → s.IsTangentAt p₂ as₂ → q ∈ as₁ → q ∈ as₂ → dist q p₁ = di
st q p₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If two tangent lines to a sphere pass through the same point `q`,
then the distances from `q` to the tangent points are equal.
-/
lemma IsTangentAt.dist_eq_of_mem_of_mem {s : Sphere P} {p₁ p₂ q : P}
    {as₁ as₂ : AffineSubspace ℝ P}
    (h₁ : s.IsTangentAt p₁ as₁) (h₂ : s.IsTangentAt p₂ as₂) (hq_mem₁ : q ∈ as₁)
    (hq_mem₂ : q ∈ as₂) :
    dist q p₁ = dist q p₂ := by
  have h1 := dist_sq_eq_of_mem h₁ hq_mem₁
  have h2 := dist_sq_eq_of_mem h₂ hq_mem₂
  rwa [h1, add_left_cancel_iff, sq_eq_sq₀ dist_nonneg dist_nonneg] at h2
/-
**EuclideanGeometry.Sphere.IsTangentAt.radius_lt_dist_center** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {as : AffineSubspace ℝ P} {p q : P},   s.IsTange
ntAt p as → q ∈ as → q ≠ p → s.radius < dist q s.center
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `EuclideanGeometry.Sphere.radius_nonneg_of_mem`：∀ {P : Type u_2} [inst : 
MetricSpace P] {s : EuclideanGeometry.Sphere P} {p : P}, p ∈ s → 0 ≤ s.radius
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_sphere`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `abs_dist`：∀ {α : Type u} [inst : PseudoMetricSpace α] {a b : α}, |dist a
 b| = dist a b
-/
lemma IsTangentAt.radius_lt_dist_center {s : Sphere P} {as : AffineSubspace ℝ P} {p q : P}
    (h : s.IsTangentAt p as) (hq : q ∈ as) (hqp : q ≠ p) : s.radius < dist q s.center := by
  suffices s.radius ^ 2 < dist q s.center ^ 2 by
    simpa [sq_lt_sq, abs_of_nonneg (s.radius_nonneg_of_mem h.mem_sphere)] using this
  rw [h.dist_sq_eq_of_mem hq]
  simp [hqp]
/-
**EuclideanGeometry.Sphere.IsTangentAt.eq_orthRadius_of_finrank_add_one_eq** 是 M
athlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {as : AffineSubspace ℝ P} {p : P},   s.IsTangent
At p as → s.radius ≠ 0 → Module.finrank ℝ ↥as.direction + 1 = Module.finrank ℝ V
 → as = s.orthRadius p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_finrank_eq_succ`：finite_of_finrank_eq_succ {n : Nat} (h
n : finrank R M = n.succ) : Module.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `EuclideanGeometry.Sphere.center_mem_iff`：∀ {P : Type u_2} [inst : Metric
Space P] {s : EuclideanGeometry.Sphere P}, s.center ∈ s ↔ s.radius = 0
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_sphere`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `AffineSubspace.eq_of_direction_eq_of_nonempty_of_le`：eq_of_direction_eq_
of_nonempty_of_le {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction
) (hn : (s₁ : Set P).Nonempty) (hle : s₁ …
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.le_orthRadius`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_right_cancel_iff`：∀ {m k n : ℕ}, m + n = k + n ↔ m = k
· 使用引理 `EuclideanGeometry.Sphere.finrank_orthRadius`：finrank_orthRadius [FiniteD
imensional Real V] {s : Sphere P} {p : P} (hp : p != s.center) : Module.finrank 
Real (s.orthRadius p).direction +…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_space`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
-/
lemma IsTangentAt.eq_orthRadius_of_finrank_add_one_eq {s : Sphere P} {as : AffineSubspace ℝ P}
    {p : P} (ht : s.IsTangentAt p as) (hr : s.radius ≠ 0)
    (hfr : Module.finrank ℝ as.direction + 1 = Module.finrank ℝ V) : as = s.orthRadius p := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hfr.symm
  have hp : p ≠ s.center := fun h ↦ (h ▸ s.center_mem_iff).not.2 hr ht.mem_sphere
  rw [← finrank_orthRadius hp, Nat.add_right_cancel_iff] at hfr
  exact eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (direction_le ht.le_orthRadius) hfr) ⟨p, ht.mem_space⟩
    ht.le_orthRadius

/-- The affine subspace `as` is tangent to the sphere `s` at some point. -/
/-
**EuclideanGeometry.Sphere.IsTangent** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeometr
y.Sphere`。
形式化陈述：IsTangent (s : Sphere P) (as : AffineSubspace Real P) : Prop
参数：s : Sphere P；as : AffineSubspace Real P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine subspace `as` is tangent to the sphere `s` at some point.
-/
def IsTangent (s : Sphere P) (as : AffineSubspace ℝ P) : Prop :=
  ∃ p, s.IsTangentAt p as
/-
**EuclideanGeometry.Sphere.IsTangentAt.isTangent** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P} {as : AffineSubspace ℝ P},   s.IsTangent
At p as → s.IsTangent as
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsTangentAt.isTangent {s : Sphere P} {p : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) : s.IsTangent as :=
  ⟨p, h⟩
/-
**EuclideanGeometry.Sphere.isTangent_orthRadius_iff_mem** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P}, s.IsTangent (s.orthRadius p) ↔ p ∈ s
参数：s.orthRadius p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.orthRadius_le_orthRadius_iff`：orthRadius_le_ort
hRadius_iff {s : Sphere P} {p q : P} : s.orthRadius p <= s.orthRadius q ↔ p = q 
∨ q = s.center
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.center_mem_orthRadius_iff`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.isTangent`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem`：∀ {V : Type u_1
} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] 
[inst_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
@[simp] lemma isTangent_orthRadius_iff_mem {s : Sphere P} {p : P} :
    s.IsTangent (s.orthRadius p) ↔ p ∈ s := by
  refine ⟨?_, fun h ↦ (isTangentAt_orthRadius_iff_mem.2 h).isTangent⟩
  rintro ⟨q, hs, hsp, hle⟩
  rw [orthRadius_le_orthRadius_iff] at hle
  rcases hle with rfl | rfl
  · exact hs
  · rw [center_mem_orthRadius_iff] at hsp
    rwa [← hsp] at hs
/-
**EuclideanGeometry.Sphere.IsTangent.radius_le_dist_center** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry.Sphere.IsTangent`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {as : AffineSubspace ℝ P},   s.IsTangent as → ∀ 
{p : P}, p ∈ as → s.radius ≤ dist p s.center
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_sq_le_sq`：le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : a <=
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `le_add_iff_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_
1 : LE α] [AddLeftMono α] [AddLeftReflectLE α] (a : α) {b : α},   a ≤ a + b ↔ 0 
≤ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
lemma IsTangent.radius_le_dist_center {s : Sphere P} {as : AffineSubspace ℝ P} (h : s.IsTangent as)
    {p : P} (hp : p ∈ as) : s.radius ≤ dist p s.center := by
  obtain ⟨x, h⟩ := h
  refine le_of_sq_le_sq ?_ dist_nonneg
  rw [h.dist_sq_eq_of_mem hp, le_add_iff_nonneg_right]
  exact sq_nonneg _
/-
**EuclideanGeometry.Sphere.IsTangent.notMem_of_dist_lt** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry.Sphere.IsTangent`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {as : AffineSubspace ℝ P},   s.IsTangent as → ∀ 
{p : P}, dist p s.center < s.radius → p ∉ as
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `EuclideanGeometry.Sphere.IsTangent.radius_le_dist_center`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma IsTangent.notMem_of_dist_lt {s : Sphere P} {as : AffineSubspace ℝ P} (h : s.IsTangent as)
    {p : P} (hp : dist p s.center < s.radius) : p ∉ as := by
  contrapose! hp
  exact h.radius_le_dist_center hp
/-
**EuclideanGeometry.Sphere.IsTangent.infDist_eq_radius** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry.Sphere.IsTangent`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {as : AffineSubspace ℝ P},   s.IsTangent as → Me
tric.infDist s.center ↑as = s.radius
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_sphere`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Metric.infDist_le_dist_of_mem`：infDist_le_dist_of_mem (h : y in s) : inf
Dist x s <= dist x y
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.mem_space`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Metric.infDist_eq_iInf`：infDist_eq_iInf : infDist x s = ⨅ y : s, dist x 
y
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `EuclideanGeometry.Sphere.IsTangent.radius_le_dist_center`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.isTangent`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma IsTangent.infDist_eq_radius {s : Sphere P} {as : AffineSubspace ℝ P} (h : s.IsTangent as) :
    Metric.infDist s.center as = s.radius := by
  obtain ⟨p, h⟩ := h
  refine le_antisymm ?_ ?_
  · convert! Metric.infDist_le_dist_of_mem h.mem_space
    rw [mem_sphere'.1 h.mem_sphere]
  · rw [Metric.infDist_eq_iInf]
    have : Nonempty as := ⟨⟨p, h.mem_space⟩⟩
    refine le_ciInf fun x ↦ ?_
    rw [dist_comm]
    exact h.isTangent.radius_le_dist_center x.property
/-
**EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTangentAt**
 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：dist_orthogonalProjection_eq_radius_iff_isTangentAt {s : Sphere P} {as : A
ffineSubspace Real P} [Nonempty as] [as.direction.HasOrthogonalProjection] : dis
t s.center (orthogonalProjection as s.center) = s.radius ↔ s.IsTangentAt (orthog
onalProjection as s.center) as
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用引理 `EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left`：mem_orthRadius_i
ff_inner_left {s : Sphere P} {p x : P} : x in s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.c
enter⟫ = 0
· 使用定理 `EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal`：or
thogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : (or…
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction`：vsub_orthogon
alProjection_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.Ha
sOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ :…
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_infDist`：dist_orthogonalP
rojection_eq_infDist (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrtho
gonalProjection] (p : P) : dist p (orthogona…
· 使用定理 `EuclideanGeometry.Sphere.IsTangent.infDist_eq_radius`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.isTangent`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
-/
lemma dist_orthogonalProjection_eq_radius_iff_isTangentAt {s : Sphere P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    dist s.center (orthogonalProjection as s.center) = s.radius ↔
      s.IsTangentAt (orthogonalProjection as s.center) as := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ⟨?_, orthogonalProjection_mem _, fun p hp ↦ ?_⟩
    · rwa [mem_sphere']
    · rw [mem_orthRadius_iff_inner_left]
      exact orthogonalProjection_vsub_mem_direction_orthogonal as s.center _
        (vsub_orthogonalProjection_mem_direction s.center hp)
  · rw [dist_orthogonalProjection_eq_infDist, h.isTangent.infDist_eq_radius]
/-
**EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTangent** 是
 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：dist_orthogonalProjection_eq_radius_iff_isTangent {s : Sphere P} {as : Aff
ineSubspace Real P} [Nonempty as] [as.direction.HasOrthogonalProjection] : dist 
s.center (orthogonalProjection as s.center) = s.radius ↔ s.IsTangent as
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.isTangent`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTange
ntAt`：dist_orthogonalProjection_eq_radius_iff_isTangentAt {s : Sphere P} {as : A
ffineSubspace Real P} [Nonempty as] [as.direction.HasOrthogonalPro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_infDist`：dist_orthogonalP
rojection_eq_infDist (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrtho
gonalProjection] (p : P) : dist p (orthogona…
· 使用定理 `EuclideanGeometry.Sphere.IsTangent.infDist_eq_radius`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma dist_orthogonalProjection_eq_radius_iff_isTangent {s : Sphere P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    dist s.center (orthogonalProjection as s.center) = s.radius ↔ s.IsTangent as := by
  refine ⟨fun h ↦ (dist_orthogonalProjection_eq_radius_iff_isTangentAt.1 h).isTangent, fun h ↦ ?_⟩
  rw [dist_orthogonalProjection_eq_infDist, h.infDist_eq_radius]
/-
**EuclideanGeometry.Sphere.infDist_eq_radius_iff_isTangent** 是 Mathlib 中的一个引理，位于
命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：infDist_eq_radius_iff_isTangent {s : Sphere P} {as : AffineSubspace Real P
} [Nonempty as] [as.direction.HasOrthogonalProjection] : Metric.infDist s.center
 as = s.radius ↔ s.IsTangent as
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_infDist`：dist_orthogonalP
rojection_eq_infDist (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrtho
gonalProjection] (p : P) : dist p (orthogona…
· 使用引理 `EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTange
nt`：dist_orthogonalProjection_eq_radius_iff_isTangent {s : Sphere P} {as : Affin
eSubspace Real P} [Nonempty as] [as.direction.HasOrthogonalProje…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma infDist_eq_radius_iff_isTangent {s : Sphere P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    Metric.infDist s.center as = s.radius ↔ s.IsTangent as := by
  rw [← dist_orthogonalProjection_eq_infDist, dist_orthogonalProjection_eq_radius_iff_isTangent]
/-
**EuclideanGeometry.Sphere.isTangent_iff_isTangentAt_orthogonalProjection** 是 Ma
thlib 中的一个引理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：isTangent_iff_isTangentAt_orthogonalProjection {s : Sphere P} {as : Affine
Subspace Real P} [Nonempty as] [as.direction.HasOrthogonalProjection] : s.IsTang
ent as ↔ s.IsTangentAt (orthogonalProjection as s.center) as
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTange
nt`：dist_orthogonalProjection_eq_radius_iff_isTangent {s : Sphere P} {as : Affin
eSubspace Real P} [Nonempty as] [as.direction.HasOrthogonalProje…
· 使用引理 `EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTange
ntAt`：dist_orthogonalProjection_eq_radius_iff_isTangentAt {s : Sphere P} {as : A
ffineSubspace Real P} [Nonempty as] [as.direction.HasOrthogonalPro…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isTangent_iff_isTangentAt_orthogonalProjection {s : Sphere P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    s.IsTangent as ↔ s.IsTangentAt (orthogonalProjection as s.center) as := by
  rw [← dist_orthogonalProjection_eq_radius_iff_isTangent,
    dist_orthogonalProjection_eq_radius_iff_isTangentAt]

alias ⟨IsTangent.isTangentAt, _⟩ := isTangent_iff_isTangentAt_orthogonalProjection
/-
**EuclideanGeometry.Sphere.IsTangent.eq_orthRadius_or_eq_orthRadius_pointReflect
ion_of_parallel_orthRadius** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere.I
sTangent`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {as : AffineSubspace ℝ P} {p : P},   s.IsTangent
 as →     as.Parallel (s.orthRadius p) → p ∈ s → as = s.orthRadius p ∨ as = s.or
thRadius ((Equiv.pointReflection s.center) p)
参数：s.orthRadius p；(Equiv.pointReflection s.center) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.direction_orthRadius_le_iff`：direction_orthRadi
us_le_iff {s : Sphere P} {p q : P} : (s.orthRadius p).direction <= (s.orthRadius
 q).direction ↔ exists r : Real, q -ᵥ s.ce…
· 使用定理 `AffineSubspace.Parallel.direction_eq`：∀ {k : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k
 V]   [inst_3 : AddTorsor …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `dist_eq_zero`：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `EuclideanGeometry.Sphere.orthRadius_center`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `AffineSubspace.eq_of_direction_eq_of_nonempty_of_le`：eq_of_direction_eq_
of_nonempty_of_le {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction
) (hn : (s₁ : Set P).Nonempty) (hle : s₁ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_eq_neg_of_abs_eq`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : L
inearOrder α] {a b : α}, |a| = b → a = b ∨ a = -b
· 使用定理 `right_eq_mul₀`：right_eq_mul₀ [IsRightCancelMulZero M₀] (hb : b != 0) : b
 = a * b ↔ a = 1
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
（共 38 条，此处仅展示前 30 条）
-/
lemma IsTangent.eq_orthRadius_or_eq_orthRadius_pointReflection_of_parallel_orthRadius {s : Sphere P}
    {as : AffineSubspace ℝ P} {p : P} (h : s.IsTangent as) (hpar : as ∥ s.orthRadius p)
    (hp : p ∈ s) :
    as = s.orthRadius p ∨ as = s.orthRadius (Equiv.pointReflection s.center p) := by
  rcases h with ⟨q, hqs, hqas, hqo⟩
  have hd := direction_le hqo
  rw [hpar.direction_eq, direction_orthRadius_le_iff] at hd
  obtain ⟨r, hr⟩ := hd
  rcases eq_or_ne s.radius 0 with hrad | hrad
  · rw [mem_sphere, hrad, dist_eq_zero] at hp hqs
    rw [hp, orthRadius_center] at hpar ⊢
    rw [hqs, orthRadius_center] at hqo
    exact .inl (eq_of_direction_eq_of_nonempty_of_le hpar.direction_eq ⟨q, hqas⟩ hqo)
  obtain rfl : as = s.orthRadius q := by
    refine eq_of_direction_eq_of_nonempty_of_le ?_ ⟨q, hqas⟩ hqo
    rw [hpar.direction_eq, direction_orthRadius, direction_orthRadius]
    congr 1
    rcases eq_or_ne r 0 with rfl | hr0
    · simp_all
    · rw [hr, Submodule.span_singleton_smul_eq hr0.isUnit]
  rcases eq_or_ne r 0 with rfl | hr0
  · simp_all
  · have hr' : ‖q -ᵥ s.center‖ = ‖r • (p -ᵥ s.center)‖ := by
      rw [hr]
    simp_rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm_vsub, mem_sphere.1 hp,
      mem_sphere.1 hqs, right_eq_mul₀ hrad] at hr'
    rcases eq_or_eq_neg_of_abs_eq hr' with rfl | rfl
    · simp_all
    · right
      convert! rfl
      rw [← eq_vadd_iff_vsub_eq] at hr
      rw [hr]
      simp [Equiv.pointReflection_apply]
/-
**EuclideanGeometry.Sphere.IsTangentAt.eq_orthogonalProjection** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry.Sphere.IsTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P} {as : AffineSubspace ℝ P}   [inst_4 : No
nempty ↥as] [inst_5 : as.direction.HasOrthogonalProjection],   s.IsTangentAt p a
s → p = ↑((EuclideanGeometry.orthogonalProjection as) s.center)
参数：(EuclideanGeometry.orthogonalProjection as) s.center。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.eq_of_isTangentAt`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.isTangent`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.Sphere.isTangent_iff_isTangentAt_orthogonalProjection`
：isTangent_iff_isTangentAt_orthogonalProjection {s : Sphere P} {as : AffineSubsp
ace Real P} [Nonempty as] [as.direction.HasOrthogonalProjecti…
-/
lemma IsTangentAt.eq_orthogonalProjection {s : Sphere P} {p : P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] (h : s.IsTangentAt p as) :
    p = orthogonalProjection as s.center := by
  refine h.eq_of_isTangentAt ?_
  have h' := h.isTangent
  rwa [isTangent_iff_isTangentAt_orthogonalProjection] at h'

/-- The set of all maximal tangent spaces to the sphere `s`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**EuclideanGeometry.Sphere.tangentSet** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeomet
ry.Sphere`。
形式化陈述：tangentSet (s : Sphere P) : Set (AffineSubspace Real P)
参数：s : Sphere P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def tangentSet (s : Sphere P) : Set (AffineSubspace ℝ P) :=
  s.orthRadius '' s
/-
**EuclideanGeometry.Sphere.mem_tangentSet_iff** 是 Mathlib 中的一个引理，位于命名空间 `Euclide
anGeometry.Sphere`。
形式化陈述：mem_tangentSet_iff {as : AffineSubspace Real P} {s : Sphere P} : as in s.t
angentSet ↔ exists p, p in s ∧ s.orthRadius p = as
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_tangentSet_iff {as : AffineSubspace ℝ P} {s : Sphere P} :
    as ∈ s.tangentSet ↔ ∃ p, p ∈ s ∧ s.orthRadius p = as :=
  Iff.rfl
/-
**EuclideanGeometry.Sphere.isTangent_of_mem_tangentSet** 是 Mathlib 中的一个引理，位于命名空间
 `EuclideanGeometry.Sphere`。
形式化陈述：isTangent_of_mem_tangentSet {as : AffineSubspace Real P} {s : Sphere P} (h
 : as in s.tangentSet) : s.IsTangent as
参数：h : as in s.tangentSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.Sphere.isTangent_orthRadius_iff_mem`：∀ {V : Type u_1} 
{P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [i
nst_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma isTangent_of_mem_tangentSet {as : AffineSubspace ℝ P} {s : Sphere P}
    (h : as ∈ s.tangentSet) : s.IsTangent as := by
  rcases h with ⟨p, hps, rfl⟩
  exact isTangent_orthRadius_iff_mem.2 hps

/-- The set of all maximal tangent spaces to the sphere `s` containing the point `p`. -/
/-
**EuclideanGeometry.Sphere.tangentsFrom** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeom
etry.Sphere`。
形式化陈述：tangentsFrom (s : Sphere P) (p : P) : Set (AffineSubspace Real P)
参数：s : Sphere P；p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all maximal tangent spaces to the sphere `s` containing the point `p`
.
-/
def tangentsFrom (s : Sphere P) (p : P) : Set (AffineSubspace ℝ P) :=
  {as ∈ s.tangentSet | p ∈ as}
/-
**EuclideanGeometry.Sphere.mem_tangentsFrom_iff** 是 Mathlib 中的一个引理，位于命名空间 `Eucli
deanGeometry.Sphere`。
形式化陈述：mem_tangentsFrom_iff {as : AffineSubspace Real P} {s : Sphere P} {p : P} :
 as in s.tangentsFrom p ↔ as in s.tangentSet ∧ p in as
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_tangentsFrom_iff {as : AffineSubspace ℝ P} {s : Sphere P} {p : P} :
    as ∈ s.tangentsFrom p ↔ as ∈ s.tangentSet ∧ p ∈ as :=
  Iff.rfl
/-
**EuclideanGeometry.Sphere.mem_tangentSet_of_mem_tangentsFrom** 是 Mathlib 中的一个引理
，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：mem_tangentSet_of_mem_tangentsFrom {as : AffineSubspace Real P} {s : Spher
e P} {p : P} (h : as in s.tangentsFrom p) : as in s.tangentSet
参数：h : as in s.tangentsFrom p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma mem_tangentSet_of_mem_tangentsFrom {as : AffineSubspace ℝ P} {s : Sphere P} {p : P}
    (h : as ∈ s.tangentsFrom p) : as ∈ s.tangentSet :=
  h.1
/-
**EuclideanGeometry.Sphere.mem_of_mem_tangentsFrom** 是 Mathlib 中的一个引理，位于命名空间 `Eu
clideanGeometry.Sphere`。
形式化陈述：mem_of_mem_tangentsFrom {as : AffineSubspace Real P} {s : Sphere P} {p : P
} (h : as in s.tangentsFrom p) : p in as
参数：h : as in s.tangentsFrom p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mem_of_mem_tangentsFrom {as : AffineSubspace ℝ P} {s : Sphere P} {p : P}
    (h : as ∈ s.tangentsFrom p) : p ∈ as :=
  h.2
/-
**EuclideanGeometry.Sphere.isTangent_of_mem_tangentsFrom** 是 Mathlib 中的一个引理，位于命名
空间 `EuclideanGeometry.Sphere`。
形式化陈述：isTangent_of_mem_tangentsFrom {as : AffineSubspace Real P} {s : Sphere P} 
{p : P} (h : as in s.tangentsFrom p) : s.IsTangent as
参数：h : as in s.tangentsFrom p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EuclideanGeometry.Sphere.isTangent_of_mem_tangentSet`：isTangent_of_mem_t
angentSet {as : AffineSubspace Real P} {s : Sphere P} (h : as in s.tangentSet) :
 s.IsTangent as
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma isTangent_of_mem_tangentsFrom {as : AffineSubspace ℝ P} {s : Sphere P} {p : P}
    (h : as ∈ s.tangentsFrom p) : s.IsTangent as :=
  isTangent_of_mem_tangentSet h.1

/-- The set of all maximal common tangent spaces to the spheres `s₁` and `s₂`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**EuclideanGeometry.Sphere.commonTangents** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGe
ometry.Sphere`。
形式化陈述：commonTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace Real P)
参数：s₁ s₂ : Sphere P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def commonTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace ℝ P) :=
  s₁.tangentSet ∩ s₂.tangentSet
/-
**EuclideanGeometry.Sphere.mem_commonTangents_iff** 是 Mathlib 中的一个引理，位于命名空间 `Euc
lideanGeometry.Sphere`。
形式化陈述：mem_commonTangents_iff {as : AffineSubspace Real P} {s₁ s₂ : Sphere P} : a
s in s₁.commonTangents s₂ ↔ as in s₁.tangentSet ∧ as in s₂.tangentSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_commonTangents_iff {as : AffineSubspace ℝ P} {s₁ s₂ : Sphere P} :
    as ∈ s₁.commonTangents s₂ ↔ as ∈ s₁.tangentSet ∧ as ∈ s₂.tangentSet :=
  Iff.rfl
/-
**EuclideanGeometry.Sphere.commonTangents_comm** 是 Mathlib 中的一个引理，位于命名空间 `Euclid
eanGeometry.Sphere`。
形式化陈述：commonTangents_comm (s₁ s₂ : Sphere P) : s₁.commonTangents s₂ = s₂.commonT
angents s₁
参数：s₁ s₂ : Sphere P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
lemma commonTangents_comm (s₁ s₂ : Sphere P) : s₁.commonTangents s₂ = s₂.commonTangents s₁ :=
  Set.inter_comm _ _

/-- The set of all maximal common internal tangent spaces to the spheres `s₁` and `s₂`: tangent
spaces containing a point weakly between the centers of the spheres. -/
/-
**EuclideanGeometry.Sphere.commonIntTangents** 是 Mathlib 中的一个定义，位于命名空间 `Euclidea
nGeometry.Sphere`。
形式化陈述：commonIntTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace Real P)
参数：s₁ s₂ : Sphere P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all maximal common internal tangent spaces to the spheres `s₁` and `s
₂`: tangent
spaces containing a point weakly between the centers of the spheres.
-/
def commonIntTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace ℝ P) :=
  {as ∈ s₁.commonTangents s₂ | ∃ p ∈ as, Wbtw ℝ s₁.center p s₂.center}

/-- The set of all maximal common external tangent spaces to the spheres `s₁` and `s₂`: tangent
spaces not containing a point strictly between the centers of the spheres. (In the degenerate case
where the two spheres are the same sphere with radius 0, the space is considered both an internal
and an external common tangent.) -/
/-
**EuclideanGeometry.Sphere.commonExtTangents** 是 Mathlib 中的一个定义，位于命名空间 `Euclidea
nGeometry.Sphere`。
形式化陈述：commonExtTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace Real P)
参数：s₁ s₂ : Sphere P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all maximal common external tangent spaces to the spheres `s₁` and `s
₂`: tangent
spaces not containing a point strictly between the centers of the spheres. (In t
he degenerate case
where the two spheres are the same sphere with radius 0, the space is considered
 both an internal
and an external common tangent.)
-/
def commonExtTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace ℝ P) :=
  {as ∈ s₁.commonTangents s₂ | ∀ p ∈ as, ¬Sbtw ℝ s₁.center p s₂.center}
/-
**EuclideanGeometry.Sphere.mem_commonIntTangents_iff** 是 Mathlib 中的一个引理，位于命名空间 `
EuclideanGeometry.Sphere`。
形式化陈述：mem_commonIntTangents_iff {as : AffineSubspace Real P} {s₁ s₂ : Sphere P} 
: as in s₁.commonIntTangents s₂ ↔ as in s₁.commonTangents s₂ ∧ exists p in as, W
btw Real s₁.center p s₂.center
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_commonIntTangents_iff {as : AffineSubspace ℝ P} {s₁ s₂ : Sphere P} :
    as ∈ s₁.commonIntTangents s₂ ↔
      as ∈ s₁.commonTangents s₂ ∧ ∃ p ∈ as, Wbtw ℝ s₁.center p s₂.center :=
  Iff.rfl
/-
**EuclideanGeometry.Sphere.mem_commonExtTangents_iff** 是 Mathlib 中的一个引理，位于命名空间 `
EuclideanGeometry.Sphere`。
形式化陈述：mem_commonExtTangents_iff {as : AffineSubspace Real P} {s₁ s₂ : Sphere P} 
: as in s₁.commonExtTangents s₂ ↔ as in s₁.commonTangents s₂ ∧ forall p in as, ¬
Sbtw Real s₁.center p s₂.center
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_commonExtTangents_iff {as : AffineSubspace ℝ P} {s₁ s₂ : Sphere P} :
    as ∈ s₁.commonExtTangents s₂ ↔
      as ∈ s₁.commonTangents s₂ ∧ ∀ p ∈ as, ¬Sbtw ℝ s₁.center p s₂.center :=
  Iff.rfl
/-
**EuclideanGeometry.Sphere.commonIntTangents_union_commonExtTangents** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s₁ s₂ : EuclideanGeometry.Sphere P),   s₁.commonIntTangents s₂ ∪ s₁.commonExtTan
gents s₂ = s₁.commonTangents s₂
参数：s₁ s₂ : EuclideanGeometry.Sphere P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用引理 `EuclideanGeometry.Sphere.mem_commonIntTangents_iff`：mem_commonIntTangent
s_iff {as : AffineSubspace Real P} {s₁ s₂ : Sphere P} : as in s₁.commonIntTangen
ts s₂ ↔ as in s₁.commonTangents s₂ ∧ exi…
· 使用引理 `EuclideanGeometry.Sphere.mem_commonExtTangents_iff`：mem_commonExtTangent
s_iff {as : AffineSubspace Real P} {s₁ s₂ : Sphere P} : as in s₁.commonExtTangen
ts s₂ ↔ as in s₁.commonTangents s₂ ∧ for…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_or_left`：∀ {a b c : Prop}, a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
-/
@[simp] lemma commonIntTangents_union_commonExtTangents (s₁ s₂ : Sphere P) :
    s₁.commonIntTangents s₂ ∪ s₁.commonExtTangents s₂ = s₁.commonTangents s₂ := by
  ext as
  rw [Set.mem_union, mem_commonIntTangents_iff, mem_commonExtTangents_iff, ← and_or_left,
    and_iff_left_iff_imp]
  rintro -
  by_cases! h : ∃ p ∈ as, Wbtw ℝ s₁.center p s₂.center
  · exact .inl h
  · refine .inr ?_
    rintro p hp
    exact mt Sbtw.wbtw (h p hp)

/-- The spheres `s₁` and `s₂` are externally tangent at the point `p`. -/
/-
**EuclideanGeometry.Sphere.IsExtTangentAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `Euclidean
Geometry.Sphere`。
形式化陈述：{V : Type u_1} →   {P : Type u_2} →     [inst : NormedAddCommGroup V] →   
    [InnerProductSpace ℝ V] →         [inst_2 : MetricSpace P] →           [Norm
edAddTorsor V P] → EuclideanGeometry.Sphere P → EuclideanGeometry.Sphere P → P →
 Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spheres `s₁` and `s₂` are externally tangent at the point `p`.
-/
structure IsExtTangentAt (s₁ s₂ : Sphere P) (p : P) : Prop where
  mem_left : p ∈ s₁
  mem_right : p ∈ s₂
  wbtw : Wbtw ℝ s₁.center p s₂.center
/-
**EuclideanGeometry.Sphere.IsExtTangentAt.symm** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry.Sphere.IsExtTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s₁ s₂ : EuclideanGeometry.Sphere P} {p : P},   s₁.IsExtTangentAt s₂ p → s₂.IsExt
TangentAt s₁ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsExtTangentAt.mem_right`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_
2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsExtTangentAt.mem_left`：∀ {V : Type u_1} {P : 
Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Wbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `EuclideanGeometry.Sphere.IsExtTangentAt.wbtw`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : M
etricSpace P]   [inst_3 : NormedAd…
-/
lemma IsExtTangentAt.symm {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsExtTangentAt s₂ p) :
    s₂.IsExtTangentAt s₁ p where
  mem_left := h.mem_right
  mem_right := h.mem_left
  wbtw := h.wbtw.symm
/-
**EuclideanGeometry.Sphere.isExtTangentAt_comm** 是 Mathlib 中的一个引理，位于命名空间 `Euclid
eanGeometry.Sphere`。
形式化陈述：isExtTangentAt_comm {s₁ s₂ : Sphere P} {p : P} : s₁.IsExtTangentAt s₂ p ↔ 
s₂.IsExtTangentAt s₁ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsExtTangentAt.symm`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : M
etricSpace P]   [inst_3 : NormedAd…
-/
lemma isExtTangentAt_comm {s₁ s₂ : Sphere P} {p : P} :
    s₁.IsExtTangentAt s₂ p ↔ s₂.IsExtTangentAt s₁ p :=
  ⟨IsExtTangentAt.symm, IsExtTangentAt.symm⟩
/-
**EuclideanGeometry.Sphere.isExtTangentAt_center_iff** 是 Mathlib 中的一个引理，位于命名空间 `
EuclideanGeometry.Sphere`。
形式化陈述：isExtTangentAt_center_iff {s₁ s₂ : Sphere P} : s₁.IsExtTangentAt s₂ s₁.cen
ter ↔ s₁.radius = 0 ∧ s₁.center in s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.center_mem_iff`：∀ {P : Type u_2} [inst : Metric
Space P] {s : EuclideanGeometry.Sphere P}, s.center ∈ s ↔ s.radius = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma isExtTangentAt_center_iff {s₁ s₂ : Sphere P} :
    s₁.IsExtTangentAt s₂ s₁.center ↔ s₁.radius = 0 ∧ s₁.center ∈ s₂ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

/-- The sphere `s₁` is internally tangent to the sphere `s₂` at the point `p` (that is, `s₁` lies
inside `s₂` and is tangent to it at that point). This includes the degenerate case where the
spheres are the same. -/
/-
**EuclideanGeometry.Sphere.IsIntTangentAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `Euclidean
Geometry.Sphere`。
形式化陈述：{V : Type u_1} →   {P : Type u_2} →     [inst : NormedAddCommGroup V] →   
    [InnerProductSpace ℝ V] →         [inst_2 : MetricSpace P] →           [Norm
edAddTorsor V P] → EuclideanGeometry.Sphere P → EuclideanGeometry.Sphere P → P →
 Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sphere `s₁` is internally tangent to the sphere `s₂` at the point `p` (that 
is, `s₁` lies
inside `s₂` and is tangent to it at that point). This includes the degenerate ca
se where the
spheres are the same.
-/
structure IsIntTangentAt (s₁ s₂ : Sphere P) (p : P) : Prop where
  mem_left : p ∈ s₁
  mem_right : p ∈ s₂
  wbtw : Wbtw ℝ s₂.center s₁.center p
/-
**EuclideanGeometry.Sphere.isIntTangentAt_center_iff** 是 Mathlib 中的一个引理，位于命名空间 `
EuclideanGeometry.Sphere`。
形式化陈述：isIntTangentAt_center_iff {s₁ s₂ : Sphere P} : s₁.IsIntTangentAt s₂ s₁.cen
ter ↔ s₁.radius = 0 ∧ s₁.center in s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.center_mem_iff`：∀ {P : Type u_2} [inst : Metric
Space P] {s : EuclideanGeometry.Sphere P}, s.center ∈ s ↔ s.radius = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma isIntTangentAt_center_iff {s₁ s₂ : Sphere P} :
    s₁.IsIntTangentAt s₂ s₁.center ↔ s₁.radius = 0 ∧ s₁.center ∈ s₂ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp
/-
**EuclideanGeometry.Sphere.isIntTangentAt_self_iff_mem** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P}, s.IsIntTangentAt s p ↔ p ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma isIntTangentAt_self_iff_mem {s : Sphere P} {p : P} :
    s.IsIntTangentAt s p ↔ p ∈ s :=
  ⟨fun ⟨h, _, _⟩ ↦ h, fun h ↦ ⟨h, h, by simp⟩⟩

/-- The spheres `s₁` and `s₂` are externally tangent at some point. -/
/-
**EuclideanGeometry.Sphere.IsExtTangent** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeom
etry.Sphere`。
形式化陈述：IsExtTangent (s₁ s₂ : Sphere P) : Prop
参数：s₁ s₂ : Sphere P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spheres `s₁` and `s₂` are externally tangent at some point.
-/
def IsExtTangent (s₁ s₂ : Sphere P) : Prop :=
  ∃ p, s₁.IsExtTangentAt s₂ p
/-
**EuclideanGeometry.Sphere.IsExtTangent.symm** 是 Mathlib 中的一个定理，位于命名空间 `Euclidea
nGeometry.Sphere.IsExtTangent`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s₁ s₂ : EuclideanGeometry.Sphere P}, s₁.IsExtTangent s₂ → s₂.IsExtTangent s₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsExtTangentAt.symm`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : M
etricSpace P]   [inst_3 : NormedAd…
-/
lemma IsExtTangent.symm {s₁ s₂ : Sphere P} (h : s₁.IsExtTangent s₂) : s₂.IsExtTangent s₁ := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.symm⟩
/-
**EuclideanGeometry.Sphere.isExtTangent_comm** 是 Mathlib 中的一个引理，位于命名空间 `Euclidea
nGeometry.Sphere`。
形式化陈述：isExtTangent_comm {s₁ s₂ : Sphere P} : s₁.IsExtTangent s₂ ↔ s₂.IsExtTangen
t s₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsExtTangent.symm`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
-/
lemma isExtTangent_comm {s₁ s₂ : Sphere P} : s₁.IsExtTangent s₂ ↔ s₂.IsExtTangent s₁ :=
  ⟨IsExtTangent.symm, IsExtTangent.symm⟩

/-- The sphere `s₁` is internally tangent to the sphere `s₂` at some point. -/
/-
**EuclideanGeometry.Sphere.IsIntTangent** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeom
etry.Sphere`。
形式化陈述：IsIntTangent (s₁ s₂ : Sphere P) : Prop
参数：s₁ s₂ : Sphere P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sphere `s₁` is internally tangent to the sphere `s₂` at some point.
-/
def IsIntTangent (s₁ s₂ : Sphere P) : Prop :=
  ∃ p, s₁.IsIntTangentAt s₂ p
/-
**EuclideanGeometry.Sphere.IsExtTangentAt.isExtTangent** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry.Sphere.IsExtTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s₁ s₂ : EuclideanGeometry.Sphere P} {p : P},   s₁.IsExtTangentAt s₂ p → s₁.IsExt
Tangent s₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsExtTangentAt.isExtTangent {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsExtTangentAt s₂ p) :
    s₁.IsExtTangent s₂ :=
  ⟨p, h⟩
/-
**EuclideanGeometry.Sphere.IsIntTangentAt.isIntTangent** 是 Mathlib 中的一个定理，位于命名空间
 `EuclideanGeometry.Sphere.IsIntTangentAt`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s₁ s₂ : EuclideanGeometry.Sphere P} {p : P},   s₁.IsIntTangentAt s₂ p → s₁.IsInt
Tangent s₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsIntTangentAt.isIntTangent {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsIntTangentAt s₂ p) :
    s₁.IsIntTangent s₂ :=
  ⟨p, h⟩
/-
**EuclideanGeometry.Sphere.isIntTangent_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] [
Nontrivial V] {s : EuclideanGeometry.Sphere P}, s.IsIntTangent s ↔ 0 ≤ s.radius
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.Sphere.nonempty_iff`：∀ {V : Type u_1} {P : Type u_2} [
inst : NormedAddCommGroup V] [NormedSpace ℝ V] [inst_2 : MetricSpace P]   [Norme
dAddTorsor V P] [Nontrivial…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isIntTangent_self_iff [Nontrivial V] {s : Sphere P} :
    s.IsIntTangent s ↔ 0 ≤ s.radius := by
  simp_rw [IsIntTangent, isIntTangentAt_self_iff_mem]
  rw [← nonempty_iff]
  simp [Set.Nonempty]
/-
**EuclideanGeometry.Sphere.IsExtTangent.dist_center** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry.Sphere.IsExtTangent`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s₁ s₂ : EuclideanGeometry.Sphere P},   s₁.IsExtTangent s₂ → dist s₁.center s₂.ce
nter = s₁.radius + s₂.radius
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dist_add_dist_eq_iff`：dist_add_dist_eq_iff : dist a b + dist b c = dist 
a c ↔ Wbtw Real a b c
· 使用定理 `UniformConvexSpace.toStrictConvexSpace`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [UniformConvexSpace E], StrictConvexSp
ace ℝ E
· 使用定理 `InnerProductSpace.toUniformConvexSpace`：∀ {F : Type u_3} [inst : Seminor
medAddCommGroup F] [InnerProductSpace ℝ F], UniformConvexSpace F
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius
-/
lemma IsExtTangent.dist_center {s₁ s₂ : Sphere P} (h : s₁.IsExtTangent s₂) :
    dist s₁.center s₂.center = s₁.radius + s₂.radius := by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff] at h
  rw [← h, mem_sphere'.1 h₁, h₂]
/-
**EuclideanGeometry.Sphere.IsIntTangent.dist_center** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry.Sphere.IsIntTangent`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s₁ s₂ : EuclideanGeometry.Sphere P},   s₁.IsIntTangent s₂ → dist s₁.center s₂.ce
nter = s₂.radius - s₁.radius
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius
· 使用引理 `dist_add_dist_eq_iff`：dist_add_dist_eq_iff : dist a b + dist b c = dist 
a c ↔ Wbtw Real a b c
· 使用定理 `UniformConvexSpace.toStrictConvexSpace`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [UniformConvexSpace E], StrictConvexSp
ace ℝ E
· 使用定理 `InnerProductSpace.toUniformConvexSpace`：∀ {F : Type u_3} [inst : Seminor
medAddCommGroup F] [InnerProductSpace ℝ F], UniformConvexSpace F
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsIntTangent.dist_center {s₁ s₂ : Sphere P} (h : s₁.IsIntTangent s₂) :
    dist s₁.center s₂.center = s₂.radius - s₁.radius := by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff, mem_sphere'.1 h₁, mem_sphere'.1 h₂] at h
  simp [← h, dist_comm]

set_option backward.isDefEq.respectTransparency false in
/-
**EuclideanGeometry.Sphere.isExtTangent_iff_dist_center** 是 Mathlib 中的一个引理，位于命名空
间 `EuclideanGeometry.Sphere`。
形式化陈述：isExtTangent_iff_dist_center {s₁ s₂ : Sphere P} : s₁.IsExtTangent s₂ ↔ dis
t s₁.center s₂.center = s₁.radius + s₂.radius ∧ 0 <= s₁.radius ∧ 0 <= s₂.radius
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsExtTangent.dist_center`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_
2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.radius_nonneg_of_mem`：∀ {P : Type u_2} [inst : 
MetricSpace P] {s : EuclideanGeometry.Sphere P} {p : P}, p ∈ s → 0 ≤ s.radius
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 91 条，此处仅展示前 30 条）
-/
lemma isExtTangent_iff_dist_center {s₁ s₂ : Sphere P} : s₁.IsExtTangent s₂ ↔
    dist s₁.center s₂.center = s₁.radius + s₂.radius ∧ 0 ≤ s₁.radius ∧ 0 ≤ s₂.radius := by
  refine ⟨fun h ↦ ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    refine ⟨AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius + s₂.radius)), ?_⟩
    by_cases h0 : s₁.radius + s₂.radius = 0
    · simp only [h0, div_zero, AffineMap.lineMap_apply_zero, isExtTangentAt_center_iff, mem_sphere]
      exact ⟨by linarith, by linarith⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp only [mem_sphere, dist_lineMap_left, norm_div, Real.norm_eq_abs, h, abs_of_nonneg h₁,
          abs_of_nonneg (add_nonneg h₁ h₂)]
        field
      · simp only [mem_sphere, dist_lineMap_right, Real.norm_eq_abs, h]
        rw [one_sub_div h0, add_sub_cancel_left, abs_div, abs_of_nonneg h₂,
          abs_of_nonneg (add_nonneg h₁ h₂)]
        field
      · simp only [wbtw_lineMap_iff]
        refine .inr ⟨?_, ?_⟩
        · positivity
        · rw [div_le_one (by positivity)]
          linarith

set_option backward.isDefEq.respectTransparency false in
/-
**EuclideanGeometry.Sphere.isIntTangent_iff_dist_center** 是 Mathlib 中的一个引理，位于命名空
间 `EuclideanGeometry.Sphere`。
形式化陈述：isIntTangent_iff_dist_center [Nontrivial V] {s₁ s₂ : Sphere P} : s₁.IsIntT
angent s₂ ↔ dist s₁.center s₂.center = s₂.radius - s₁.radius ∧ 0 <= s₁.radius ∧ 
0 <= s₂.radius
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsIntTangent.dist_center`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_
2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.radius_nonneg_of_mem`：∀ {P : Type u_2} [inst : 
MetricSpace P] {s : EuclideanGeometry.Sphere P} {p : P}, p ∈ s → 0 ≤ s.radius
· 使用定理 `EuclideanGeometry.Sphere.ext`：∀ {P : Type u_2} {inst : MetricSpace P} {x
 y : EuclideanGeometry.Sphere P},   x.center = y.center → x.radius = y.radius → 
x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `dist_eq_zero`：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
· 使用定理 `dist_lineMap_right`：dist_lineMap_right (p₁ p₂ : P) (c : 𝕜) : dist (lineM
ap p₁ p₂ c) p₂ = ‖1 - c‖ * dist p₁ p₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_sub_div`：one_sub_div {a b : K} (h : b != 0) : 1 - a / b = (b - a) / 
b
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
（共 91 条，此处仅展示前 30 条）
-/
lemma isIntTangent_iff_dist_center [Nontrivial V] {s₁ s₂ : Sphere P} : s₁.IsIntTangent s₂ ↔
    dist s₁.center s₂.center = s₂.radius - s₁.radius ∧ 0 ≤ s₁.radius ∧ 0 ≤ s₂.radius := by
  refine ⟨fun h ↦ ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    by_cases h0 : s₁.center = s₂.center
    · rw [h0, dist_self, eq_comm, sub_eq_zero, eq_comm] at h
      have hs : s₁ = s₂ := by
        ext <;> assumption
      simp [hs, h₂]
    · rw [dist_comm] at h
      have ha : |s₂.radius - s₁.radius| = s₂.radius - s₁.radius := by
        refine abs_of_nonneg ?_
        rw [← h]
        exact dist_nonneg
      have hr0 : s₂.radius - s₁.radius ≠ 0 := by
        intro hr0
        rw [hr0, dist_eq_zero] at h
        exact h0 h.symm
      refine ⟨AffineMap.lineMap s₂.center s₁.center (s₂.radius / (s₂.radius - s₁.radius)),
              ?_, ?_, ?_⟩
      · simp only [mem_sphere, dist_lineMap_right, Real.norm_eq_abs, h, one_sub_div hr0, abs_div,
          sub_sub_cancel_left, abs_neg, abs_of_nonneg h₁, ha]
        field
      · simp only [mem_sphere, dist_lineMap_left, norm_div, Real.norm_eq_abs, h, ha,
          abs_of_nonneg h₂]
        field
      · rw [wbtw_iff_left_eq_or_right_mem_image_Ici]
        simp only [Ne.symm h0, Set.mem_image, Set.mem_Ici, AffineMap.lineMap_eq_lineMap_iff,
          false_or, exists_eq_right]
        rw [one_le_div]
        · linarith
        · rw [← h]
          simp [Ne.symm h0]

end Sphere

end EuclideanGeometry

