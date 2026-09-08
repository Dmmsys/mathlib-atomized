/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.Star

/-!
# Star structures on bounded continuous functions

-/

@[expose] public section

noncomputable section

open Topology Bornology NNReal uniformity UniformConvergence RCLike BoundedContinuousFunction

open Set Filter Metric Function

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}

namespace BoundedContinuousFunction

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of bounded
continuous functions from `α` to `β`, by using the star operation pointwise.

If `𝕜` is normed field and a ⋆-ring over which `β` is a normed algebra and a
star module, then the space of bounded continuous functions from `α` to `β`
is a star module.

If `β` is a ⋆-ring in addition to being a normed ⋆-group, then `α →ᵇ β`
inherits a ⋆-ring structure.

In summary, if `β` is a C⋆-algebra over `𝕜`, then so is `α →ᵇ β`; note that
completeness is guaranteed when `β` is complete (see
`BoundedContinuousFunction.complete`). -/


section NormedAddCommGroup

variable {𝕜 : Type*} [NormedField 𝕜] [StarRing 𝕜] [TopologicalSpace α] [SeminormedAddCommGroup β]
  [StarAddMonoid β] [NormedStarGroup β]

variable [NormedSpace 𝕜 β] [StarModule 𝕜 β]

/-
**BoundedContinuousFunction.instStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：instStarAddMonoid : StarAddMonoid (α ->ᵇ β) where star f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarAddMonoid : StarAddMonoid (α →ᵇ β) where
  star f := f.comp star starNormedAddGroupHom.lipschitz
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

/-- The right-hand side of this equality can be parsed `star ∘ ⇑f` because of the
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance `Pi.instStarForAll`. Upon inspecting the goal, one sees `⊢ ↑(star f) = star ↑f`. -/
@[simp]
/-
**BoundedContinuousFunction.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：coe_star (f : α ->ᵇ β) : ⇑(star f) = star (⇑f)
参数：f : α ->ᵇ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
The right-hand side of this equality can be parsed `star ∘ ⇑f` because of the
instance `Pi.instStarForAll`. Upon inspecting the goal, one sees `⊢ ↑(star f) = 
star ↑f`.
-/
theorem coe_star (f : α →ᵇ β) : ⇑(star f) = star (⇑f) := rfl

@[simp]
/-
**BoundedContinuousFunction.star_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：star_apply (f : α ->ᵇ β) (x : α) : star f x = star (f x)
参数：f : α ->ᵇ β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem star_apply (f : α →ᵇ β) (x : α) : star f x = star (f x) := rfl
/-
**BoundedContinuousFunction.instNormedStarGroup** 是 Mathlib 中的一个实例，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：instNormedStarGroup : NormedStarGroup (α ->ᵇ β) where norm_star_le f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.norm_eq`：norm_eq (f : α ->ᵇ β) : ‖f‖ = sInf { 
C : Real | 0 <= C ∧ forall x : α, ‖f x‖ <= C }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instNormedStarGroup : NormedStarGroup (α →ᵇ β) where
  norm_star_le f := by simp only [norm_eq, star_apply, norm_star, le_of_eq]
/-
**BoundedContinuousFunction.instStarModule** 是 Mathlib 中的一个实例，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：instStarModule : StarModule 𝕜 (α ->ᵇ β) where star_smul k f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
-/
instance instStarModule : StarModule 𝕜 (α →ᵇ β) where
  star_smul k f := ext fun x => star_smul k (f x)

end NormedAddCommGroup

section CStarRing

variable [TopologicalSpace α]
variable [NonUnitalNormedRing β] [StarRing β]

/-
**BoundedContinuousFunction.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：instStarRing [NormedStarGroup β] : StarRing (α ->ᵇ β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarRing [NormedStarGroup β] : StarRing (α →ᵇ β) where
  __ := instStarAddMonoid
  star_mul f g := ext fun x ↦ star_mul (f x) (g x)

variable [CStarRing β]
/-
**BoundedContinuousFunction.instCStarRing** 是 Mathlib 中的一个实例，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：instCStarRing : CStarRing (α ->ᵇ β) where norm_mul_self_le f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.le_sqrt`：le_sqrt (hx : 0 <= x) (hy : 0 <= y) : x <= √y ↔ x ^ 2 <= y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
instance instCStarRing : CStarRing (α →ᵇ β) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _), norm_le (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
    exact norm_coe_le_norm (star f * f) x

end CStarRing

section NormedAlgebra

variable (𝕜 : Type*) [NormedField 𝕜] [TopologicalSpace α]
  [NormedRing β] [NormedAlgebra 𝕜 β] [StarAddMonoid β] [NormedStarGroup β]

/-- The ⋆-algebra-homomorphism forgetting that a bounded continuous function is bounded. -/
@[simps!]
/-
**BoundedContinuousFunction.toContinuousMapStar** 是 Mathlib 中的一个定义，位于命名空间 `Bound
edContinuousFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ⋆-algebra-homomorphism forgetting that a bounded continuous function is boun
ded.
-/
def toContinuousMapStarₐ : (α →ᵇ β) →⋆ₐ[𝕜] C(α, β) := { toContinuousMapₐ 𝕜 with
  map_star' _ := rfl }

@[simp]
/-
**BoundedContinuousFunction.coe_toContinuousMapStar** 是 Mathlib 中的一个定理，位于命名空间 `B
oundedContinuousFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMapStarₐ (f : α →ᵇ β) : (f.toContinuousMapStarₐ 𝕜 : α → β) = f := rfl

end NormedAlgebra

end BoundedContinuousFunction

