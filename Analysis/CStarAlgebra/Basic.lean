/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Real.Star
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Normed star rings and algebras

A normed star group is a normed group with a compatible `star` which is isometric.

A C⋆-ring is a normed star group that is also a ring and that verifies the stronger
condition `‖x‖^2 ≤ ‖x⋆ * x‖` for all `x` (which actually implies equality). If a C⋆-ring is also
a star algebra, then it is a C⋆-algebra.

Note that the type classes corresponding to C⋆-algebras are defined in
`Mathlib/Analysis/CStarAlgebra/Classes`.

## TODO

- Show that `‖x⋆ * x‖ = ‖x‖^2` is equivalent to `‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖`, which is used as the
  definition of C⋆-algebras in some sources (e.g. Wikipedia).

-/

@[expose] public section

assert_not_exists ContinuousLinearMap.hasOpNorm

open Topology

local postfix:max "⋆" => star

/-- A normed star group is a normed group with a compatible `star` which is isometric. -/
/-
**NormedStarGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_1) → [inst : SeminormedAddCommGroup E] → [StarAddMonoid E] → P
rop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed star group is a normed group with a compatible `star` which is isometri
c.
-/
class NormedStarGroup (E : Type*) [SeminormedAddCommGroup E] [StarAddMonoid E] : Prop where
  norm_star_le : ∀ x : E, ‖x⋆‖ ≤ ‖x‖

variable {𝕜 E α : Type*}

section NormedStarGroup

variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]

@[simp]
/-
**norm_star** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_star (x : E) : ‖x⋆‖ = ‖x‖
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NormedStarGroup.norm_star_le`：∀ {E : Type u_1} {inst : SeminormedAddComm
Group E} {inst_1 : StarAddMonoid E} [self : NormedStarGroup E] (x : E),   ‖star 
x‖ ≤ ‖x‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
lemma norm_star (x : E) : ‖x⋆‖ = ‖x‖ :=
  le_antisymm (NormedStarGroup.norm_star_le x) (by simpa using NormedStarGroup.norm_star_le x⋆)

@[simp]
/-
**nnnorm_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
-/
theorem nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊ :=
  Subtype.ext <| norm_star _

/-- The `star` map in a normed star group is a normed group homomorphism. -/
/-
**starNormedAddGroupHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starNormedAddGroupHom : NormedAddGroupHom E E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `star` map in a normed star group is a normed group homomorphism.
-/
def starNormedAddGroupHom : NormedAddGroupHom E E :=
  { starAddEquiv with bound' := ⟨1, fun _ => le_trans (norm_star _).le (one_mul _).symm.le⟩ }

/-- The `star` map in a normed star group is an isometry -/
/-
**star_isometry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_isometry : Isometry (star : E -> E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖

--- 原说明 ---
The `star` map in a normed star group is an isometry
-/
theorem star_isometry : Isometry (star : E → E) :=
  show Isometry starAddEquiv from
    AddMonoidHomClass.isometry_of_norm starAddEquiv (show ∀ x, ‖x⋆‖ = ‖x‖ from norm_star)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormedStarGroup.to_continuousStar : ContinuousStar E :=
  ⟨star_isometry.continuous⟩

noncomputable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NormedField 𝕜] [NormedSpace 𝕜 E] [Star 𝕜] [TrivialStar 𝕜] [StarModule 𝕜 E] :
    NormedSpace 𝕜 (selfAdjoint E) where
  norm_smul_le _ _ := norm_smul_le _ (_ : E)

variable (x : E) (r : ℝ)
/-
**Metric.star_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] [inst_1 : StarAddMonoid
 E] [NormedStarGroup E] (x : E) (r : ℝ),   star (Metric.ball x r) = Metric.ball 
(star x) r
参数：x : E；r : ℝ；Metric.ball x r；star x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Isometry.preimage_ball`：preimage_ball (hf : Isometry f) (x : α) (r : Rea
l) : f ⁻¹' Metric.ball (f x) r = Metric.ball x r
· 使用定理 `star_isometry`：star_isometry : Isometry (star : E -> E)
-/
@[simp] lemma Metric.star_ball : star (ball x r) = ball (star x) r := by
  simpa using star_isometry.preimage_ball (star x) r
/-
**Metric.star_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] [inst_1 : StarAddMonoid
 E] [NormedStarGroup E] (x : E) (r : ℝ),   star (Metric.closedBall x r) = Metric
.closedBall (star x) r
参数：x : E；r : ℝ；Metric.closedBall x r；star x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Isometry.preimage_closedBall`：preimage_closedBall (hf : Isometry f) (x :
 α) (r : Real) : f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r
· 使用定理 `star_isometry`：star_isometry : Isometry (star : E -> E)
-/
@[simp] lemma Metric.star_closedBall : star (closedBall x r) = closedBall (star x) r := by
  simpa using star_isometry.preimage_closedBall (star x) r
/-
**Metric.star_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] [inst_1 : StarAddMonoid
 E] [NormedStarGroup E] (x : E) (r : ℝ),   star (Metric.sphere x r) = Metric.sph
ere (star x) r
参数：x : E；r : ℝ；Metric.sphere x r；star x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Isometry.preimage_sphere`：preimage_sphere (hf : Isometry f) (x : α) (r :
 Real) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r
· 使用定理 `star_isometry`：star_isometry : Isometry (star : E -> E)
-/
@[simp] lemma Metric.star_sphere : star (sphere x r) = sphere (star x) r := by
  simpa using star_isometry.preimage_sphere (star x) r
/-
**dist_star_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] [inst_1 : StarAddMonoid
 E] [NormedStarGroup E] (x y : E),   dist (star x) (star y) = dist x y
参数：x y : E；star x；star y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `star_isometry`：star_isometry : Isometry (star : E -> E)
-/
@[simp] lemma dist_star_star (x y : E) : dist (star x) (star y) = dist x y :=
  star_isometry.dist_eq x y
/-
**edist_star_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] [inst_1 : StarAddMonoid
 E] [NormedStarGroup E] (x y : E),   edist (star x) (star y) = edist x y
参数：x y : E；star x；star y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `star_isometry`：star_isometry : Isometry (star : E -> E)
-/
@[simp] lemma edist_star_star (x y : E) : edist (star x) (star y) = edist x y :=
  star_isometry.edist_eq x y
/-
**nndist_star_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] [inst_1 : StarAddMonoid
 E] [NormedStarGroup E] (x y : E),   nndist (star x) (star y) = nndist x y
参数：x y : E；star x；star y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.nndist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpac
e α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), nnd
ist (f x…
· 使用定理 `star_isometry`：star_isometry : Isometry (star : E -> E)
-/
@[simp] lemma nndist_star_star (x y : E) : nndist (star x) (star y) = nndist x y :=
  star_isometry.nndist_eq x y

end NormedStarGroup

/-
**RingHomIsometric.starRingEnd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RingHomIsometric.starRingEnd [NormedCommRing E] [StarRing E] [NormedStarGr
oup E] : RingHomIsometric (starRingEnd E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
-/
instance RingHomIsometric.starRingEnd [NormedCommRing E] [StarRing E] [NormedStarGroup E] :
    RingHomIsometric (starRingEnd E) :=
  ⟨@norm_star _ _ _ _⟩

/-- A C⋆-ring is a normed star ring that satisfies the stronger condition `‖x‖ ^ 2 ≤ ‖x⋆ * x‖`
for every `x`. Note that this condition actually implies equality, as is shown in
`norm_star_mul_self` below. -/
/-
**CStarRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_4) → [inst : NonUnitalNormedRing E] → [StarRing E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A C⋆-ring is a normed star ring that satisfies the stronger condition `‖x‖ ^ 2 ≤
 ‖x⋆ * x‖`
for every `x`. Note that this condition actually implies equality, as is shown i
n
`norm_star_mul_self` below.
-/
class CStarRing (E : Type*) [NonUnitalNormedRing E] [StarRing E] : Prop where
  norm_mul_self_le : ∀ x : E, ‖x‖ * ‖x‖ ≤ ‖x⋆ * x‖
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CStarRing ℝ where
  norm_mul_self_le x := by simp

namespace CStarRing

section NonUnital

/-
**CStarRing.of_le_norm_mul_star_self** 是 Mathlib 中的一个引理，位于命名空间 `CStarRing`。
形式化陈述：of_le_norm_mul_star_self [NonUnitalNormedRing E] [StarRing E] (h : forall 
x : E, ‖x‖ * ‖x‖ <= ‖x * x⋆‖) : CStarRing E
参数：h : forall x : E, ‖x‖ * ‖x‖ <= ‖x * x⋆‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_norm_pos`：∀ {E : Type u_5} [inst : NormedAddGroup E] (a : E),
 a = 0 ∨ 0 < ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
-/
lemma of_le_norm_mul_star_self
    [NonUnitalNormedRing E] [StarRing E]
    (h : ∀ x : E, ‖x‖ * ‖x‖ ≤ ‖x * x⋆‖) : CStarRing E :=
  have : NormedStarGroup E :=
    { norm_star_le x := by
        obtain (hx | hx) := eq_zero_or_norm_pos x⋆
        · simp [hx]
        · refine le_of_mul_le_mul_right ?_ hx
          simpa [sq, mul_comm ‖x⋆‖] using h x⋆ |>.trans <| norm_mul_le _ _ }
  ⟨star_involutive.surjective.forall.mpr <| by simpa⟩

variable [NonUnitalNormedRing E] [StarRing E] [CStarRing E]

-- see Note [lower instance priority]
/-- In a C⋆-ring, star preserves the norm. -/
/-
**CStarRing.** 是 Mathlib 中的一个实例，位于命名空间 `CStarRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a C⋆-ring, star preserves the norm.
-/
instance (priority := 100) to_normedStarGroup : NormedStarGroup E where
  norm_star_le x := by
    obtain (hx | hx) := eq_zero_or_norm_pos x⋆
    · simp [hx]
    · refine le_of_mul_le_mul_right ?_ hx
      simpa using norm_mul_self_le (x := x⋆) |>.trans <| norm_mul_le _ _
/-
**CStarRing.norm_star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x‖ * ‖x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CStarRing.norm_mul_self_le`：∀ {E : Type u_4} {inst : NonUnitalNormedRing
 E} {inst_1 : StarRing E} [self : CStarRing E] (x : E),   ‖x‖ * ‖x‖ ≤ ‖star x * 
x‖
-/
theorem norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x‖ * ‖x‖ :=
  le_antisymm ((norm_mul_le _ _).trans (by rw [norm_star])) (CStarRing.norm_mul_self_le x)
/-
**CStarRing.norm_self_mul_star** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_self_mul_star {x : E} : ‖x * x⋆‖ = ‖x‖ * ‖x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_self_mul_star {x : E} : ‖x * x⋆‖ = ‖x‖ * ‖x‖ := by
  nth_rw 1 [← star_star x]
  simp only [norm_star_mul_self, norm_star]
/-
**CStarRing.norm_star_mul_self'** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_star_mul_self' {x : E} : ‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
-/
theorem norm_star_mul_self' {x : E} : ‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖ := by rw [norm_star_mul_self, norm_star]
/-
**CStarRing.nnnorm_self_mul_star** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：nnnorm_self_mul_star {x : E} : ‖x * x⋆‖₊ = ‖x‖₊ * ‖x‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `CStarRing.norm_self_mul_star`：norm_self_mul_star {x : E} : ‖x * x⋆‖ = ‖x
‖ * ‖x‖
-/
theorem nnnorm_self_mul_star {x : E} : ‖x * x⋆‖₊ = ‖x‖₊ * ‖x‖₊ :=
  Subtype.ext norm_self_mul_star
/-
**CStarRing.nnnorm_star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：nnnorm_star_mul_self {x : E} : ‖x⋆ * x‖₊ = ‖x‖₊ * ‖x‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
-/
theorem nnnorm_star_mul_self {x : E} : ‖x⋆ * x‖₊ = ‖x‖₊ * ‖x‖₊ :=
  Subtype.ext norm_star_mul_self
/-
**CStarRing._root_.IsSelfAdjoint.norm_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `CStarR
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsSelfAdjoint.norm_mul_self {x : E} (hx : IsSelfAdjoint x) :
    ‖x * x‖ = ‖x‖ ^ 2 := by
  simpa [sq, hx.star_eq] using CStarRing.norm_star_mul_self (x := x)
/-
**CStarRing._root_.IsSelfAdjoint.nnnorm_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `CSta
rRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsSelfAdjoint.nnnorm_mul_self {x : E} (hx : IsSelfAdjoint x) :
    ‖x * x‖₊ = ‖x‖₊ ^ 2 :=
  Subtype.ext hx.norm_mul_self

@[simp]
/-
**CStarRing.star_mul_self_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：star_mul_self_eq_zero_iff (x : E) : x⋆ * x = 0 ↔ x = 0
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mul_self_eq_zero`：mul_self_eq_zero : a * a = 0 ↔ a = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem star_mul_self_eq_zero_iff (x : E) : x⋆ * x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero, norm_star_mul_self]
  exact mul_self_eq_zero.trans norm_eq_zero
/-
**CStarRing.star_mul_self_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：star_mul_self_ne_zero_iff (x : E) : x⋆ * x != 0 ↔ x != 0
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem star_mul_self_ne_zero_iff (x : E) : x⋆ * x ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne, star_mul_self_eq_zero_iff]

@[simp]
/-
**CStarRing.mul_star_self_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：mul_star_self_eq_zero_iff (x : E) : x * x⋆ = 0 ↔ x = 0
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `CStarRing.star_mul_self_eq_zero_iff`：star_mul_self_eq_zero_iff (x : E) :
 x⋆ * x = 0 ↔ x = 0
-/
theorem mul_star_self_eq_zero_iff (x : E) : x * x⋆ = 0 ↔ x = 0 := by
  simpa only [star_eq_zero, star_star] using @star_mul_self_eq_zero_iff _ _ _ _ (star x)
/-
**CStarRing.mul_star_self_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：mul_star_self_ne_zero_iff (x : E) : x * x⋆ != 0 ↔ x != 0
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_star_self_ne_zero_iff (x : E) : x * x⋆ ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne, mul_star_self_eq_zero_iff]

end NonUnital

section ProdPi

variable {ι R₁ R₂ : Type*} {R : ι → Type*}
variable [NonUnitalNormedRing R₁] [StarRing R₁] [CStarRing R₁]
variable [NonUnitalNormedRing R₂] [StarRing R₂] [CStarRing R₂]
variable [∀ i, NonUnitalNormedRing (R i)] [∀ i, StarRing (R i)]

/-- This instance exists to short circuit type class resolution because of problems with
inference involving Π-types. -/
/-
**CStarRing._root_.Pi.starRing'** 是 Mathlib 中的一个实例，位于命名空间 `CStarRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance exists to short circuit type class resolution because of problems 
with
inference involving Π-types.
-/
instance _root_.Pi.starRing' : StarRing (∀ i, R i) :=
  inferInstance

variable [Fintype ι] [∀ i, CStarRing (R i)]
/-
**CStarRing._root_.Prod.cstarRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Prod.cstarRing : CStarRing (R₁ × R₂) where
  norm_mul_self_le x := by
    dsimp only [norm]
    simp only [Prod.fst_mul, Prod.fst_star, Prod.snd_mul, Prod.snd_star, norm_star_mul_self, ← sq]
    rw [le_sup_iff]
    rcases le_total ‖x.fst‖ ‖x.snd‖ with (h | h) <;> simp [h]
/-
**CStarRing._root_.Pi.cstarRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Pi.cstarRing : CStarRing (∀ i, R i) where
  norm_mul_self_le x := by
    refine le_of_eq (Eq.symm ?_)
    simp only [norm, Pi.mul_apply, Pi.star_apply, nnnorm_star_mul_self, ← sq]
    norm_cast
    exact
      (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : NNReal => x ^ 2)
          (fun x y h => by simpa only [sq] using mul_le_mul' h h) (by simp)).symm
/-
**CStarRing._root_.Pi.cstarRing'** 是 Mathlib 中的一个实例，位于命名空间 `CStarRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Pi.cstarRing' : CStarRing (ι → R₁) :=
  Pi.cstarRing

end ProdPi

namespace MulOpposite

/-
**CStarRing.MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `CStarRing.MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E] : CStarRing Eᵐᵒᵖ where
  norm_mul_self_le x := CStarRing.norm_self_mul_star (x := MulOpposite.unop x) |>.symm.le

end MulOpposite

section Unital


variable [NormedRing E] [StarRing E] [CStarRing E]

/-
**CStarRing.norm_one** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_one [Nontrivial E] : ‖(1 : E)‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_one [Nontrivial E] : ‖(1 : E)‖ = 1 := by
  have : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  rw [← mul_left_inj' this.ne', ← norm_star_mul_self, mul_one, star_one, one_mul]

-- see Note [lower instance priority]
/-
**CStarRing.** 是 Mathlib 中的一个实例，位于命名空间 `CStarRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Nontrivial E] : NormOneClass E :=
  ⟨norm_one⟩

@[simp]
/-
**CStarRing.norm_coe_unitary** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_coe_unitary [Nontrivial E] (U : unitary E) : ‖(U : E)‖ = 1
参数：U : unitary E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `Unitary.coe_star_mul_self`：coe_star_mul_self (U : unitary R) : (star U :
 R) * U = 1
· 使用定理 `CStarRing.norm_one`：norm_one [Nontrivial E] : ‖(1 : E)‖ = 1
-/
theorem norm_coe_unitary [Nontrivial E] (U : unitary E) : ‖(U : E)‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow 2, sq, ← CStarRing.norm_star_mul_self,
    Unitary.coe_star_mul_self, CStarRing.norm_one]
/-
**CStarRing.norm_of_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_of_mem_unitary [Nontrivial E] {U : E} (hU : U in unitary E) : ‖U‖ = 1
参数：hU : U in unitary E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarRing.norm_coe_unitary`：norm_coe_unitary [Nontrivial E] (U : unitary
 E) : ‖(U : E)‖ = 1
-/
theorem norm_of_mem_unitary [Nontrivial E] {U : E} (hU : U ∈ unitary E) : ‖U‖ = 1 :=
  norm_coe_unitary ⟨U, hU⟩

@[simp]
/-
**CStarRing.norm_coe_unitary_mul** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_coe_unitary_mul (U : unitary E) (A : E) : ‖(U : E) * A‖ = ‖A‖
参数：U : unitary E；A : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_coe_unitary_mul (U : unitary E) (A : E) : ‖(U : E) * A‖ = ‖A‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [sq, ← CStarRing.norm_star_mul_self, mul_assoc, ← mul_assoc (U : E)⋆]

@[simp]
/-
**CStarRing.norm_unitary_smul** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_unitary_smul (U : unitary E) (A : E) : ‖U • A‖ = ‖A‖
参数：U : unitary E；A : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarRing.norm_coe_unitary_mul`：norm_coe_unitary_mul (U : unitary E) (A 
: E) : ‖(U : E) * A‖ = ‖A‖
-/
theorem norm_unitary_smul (U : unitary E) (A : E) : ‖U • A‖ = ‖A‖ :=
  norm_coe_unitary_mul U A
/-
**CStarRing.norm_mem_unitary_mul** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_mem_unitary_mul {U : E} (A : E) (hU : U in unitary E) : ‖U * A‖ = ‖A‖
参数：A : E；hU : U in unitary E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarRing.norm_coe_unitary_mul`：norm_coe_unitary_mul (U : unitary E) (A 
: E) : ‖(U : E) * A‖ = ‖A‖
-/
theorem norm_mem_unitary_mul {U : E} (A : E) (hU : U ∈ unitary E) : ‖U * A‖ = ‖A‖ :=
  norm_coe_unitary_mul ⟨U, hU⟩ A

@[simp]
/-
**CStarRing.norm_mul_coe_unitary** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_mul_coe_unitary (A : E) (U : unitary E) : ‖A * U‖ = ‖A‖
参数：A : E；U : unitary E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `CStarRing.norm_coe_unitary_mul`：norm_coe_unitary_mul (U : unitary E) (A 
: E) : ‖(U : E) * A‖ = ‖A‖
-/
theorem norm_mul_coe_unitary (A : E) (U : unitary E) : ‖A * U‖ = ‖A‖ := by
  simpa [← norm_star (A * U)] using norm_coe_unitary_mul (star U) (star A)
/-
**CStarRing.norm_mul_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `CStarRing`。
形式化陈述：norm_mul_mem_unitary (A : E) {U : E} (hU : U in unitary E) : ‖A * U‖ = ‖A‖
参数：A : E；hU : U in unitary E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarRing.norm_mul_coe_unitary`：norm_mul_coe_unitary (A : E) (U : unitar
y E) : ‖A * U‖ = ‖A‖
-/
theorem norm_mul_mem_unitary (A : E) {U : E} (hU : U ∈ unitary E) : ‖A * U‖ = ‖A‖ :=
  norm_mul_coe_unitary A ⟨U, hU⟩

end Unital

end CStarRing

section SelfAdjoint

variable [NormedRing E] [StarRing E] [CStarRing E]

/-
**IsSelfAdjoint.nnnorm_pow_two_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.nnnorm_pow_two_pow {x : E} (hx : IsSelfAdjoint x) (n : Nat) 
: ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ 2 ^ n
参数：hx : IsSelfAdjoint x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `IsSelfAdjoint.nnnorm_mul_self`：∀ {E : Type u_2} [inst : NonUnitalNormedR
ing E] [inst_1 : StarRing E] [CStarRing E] {x : E},   IsSelfAdjoint x → ‖x * x‖₊
 = ‖x‖₊ ^ 2
· 使用定理 `IsSelfAdjoint.pow`：pow {x : R} (hx : IsSelfAdjoint x) (n : Nat) : IsSelf
Adjoint (x ^ n)
-/
theorem IsSelfAdjoint.nnnorm_pow_two_pow {x : E} (hx : IsSelfAdjoint x) (n : ℕ) :
    ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ 2 ^ n := by
  induction n with
  | zero => simp only [pow_zero, pow_one]
  | succ k hk =>
    rw [pow_succ', pow_mul', sq, (hx.pow (2 ^ k)).nnnorm_mul_self, hk, pow_mul']
/-
**IsSelfAdjoint.norm_pow_two_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.norm_pow_two_pow {x : E} (hx : IsSelfAdjoint x) (n : Nat) : 
‖x ^ 2 ^ n‖ = ‖x‖ ^ 2 ^ n
参数：hx : IsSelfAdjoint x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSelfAdjoint.nnnorm_pow_two_pow`：IsSelfAdjoint.nnnorm_pow_two_pow {x : 
E} (hx : IsSelfAdjoint x) (n : Nat) : ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ 2 ^ n
-/
theorem IsSelfAdjoint.norm_pow_two_pow {x : E} (hx : IsSelfAdjoint x) (n : ℕ) :
    ‖x ^ 2 ^ n‖ = ‖x‖ ^ 2 ^ n :=
  congr($(hx.nnnorm_pow_two_pow n))

end SelfAdjoint

/-
**IsStarProjection.norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStarProjection.norm_le [NonUnitalNormedRing E] [StarRing E] [CStarRing E
] (e : E) (he : IsStarProjection e) : ‖e‖ <= 1
参数：e : E；he : IsStarProjection e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsStarProjection.norm_le [NonUnitalNormedRing E] [StarRing E] [CStarRing E]
    (e : E) (he : IsStarProjection e) : ‖e‖ ≤ 1 := by
  suffices ‖e‖ * (‖e‖ - 1) = 0 by grind [sub_eq_zero]
  simp [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]

section starₗᵢ

variable [CommSemiring 𝕜] [StarRing 𝕜]
variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]
variable [Module 𝕜 E] [StarModule 𝕜 E]

variable (𝕜) in
/-- `star` bundled as a linear isometric equivalence -/
/-
**star** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`star` bundled as a linear isometric equivalence
-/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
  { starAddEquiv with
    map_smul' := star_smul
    norm_map' := norm_star }

@[simp]
/-
**coe_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_starₗᵢ : (starₗᵢ 𝕜 : E → E) = star :=
  rfl
/-
**star** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x :=
  rfl

@[simp]
/-
**symm_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_starₗᵢ : (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).symm = starₗᵢ 𝕜 :=
  rfl

@[simp]
/-
**star** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem starₗᵢ_toContinuousLinearEquiv :
    (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).toContinuousLinearEquiv = (starL 𝕜 : E ≃L⋆[𝕜] E) :=
  ContinuousLinearEquiv.ext rfl

@[simp]
/-
**toLinearEquiv_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_starₗᵢ : (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).toLinearEquiv = starLinearEquiv 𝕜 :=
  rfl

end starₗᵢ

namespace StarSubalgebra

/-
**StarSubalgebra.** 是 Mathlib 中的一个示例，位于命名空间 `StarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {𝕜 A : Type*} [NormedField 𝕜] [StarRing 𝕜] [SeminormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [StarModule 𝕜 A] (S : StarSubalgebra 𝕜 A) :
    NormedAlgebra 𝕜 S := by infer_instance
/-
**StarSubalgebra.to_cstarRing** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：to_cstarRing {R A} [CommRing R] [StarRing R] [NormedRing A] [StarRing A] [
CStarRing A] [Algebra R A] [StarModule R A] (S : StarSubalgebra R A) : CStarRing
 S where norm_mul_self_le x
参数：S : StarSubalgebra R A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarRing.norm_mul_self_le`：∀ {E : Type u_4} {inst : NonUnitalNormedRing
 E} {inst_1 : StarRing E} [self : CStarRing E] (x : E),   ‖x‖ * ‖x‖ ≤ ‖star x * 
x‖
-/
instance to_cstarRing {R A} [CommRing R] [StarRing R] [NormedRing A] [StarRing A] [CStarRing A]
    [Algebra R A] [StarModule R A] (S : StarSubalgebra R A) : CStarRing S where
  norm_mul_self_le x := @CStarRing.norm_mul_self_le A _ _ _ x

end StarSubalgebra

