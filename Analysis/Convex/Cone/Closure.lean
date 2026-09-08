/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Closure of cones

We define the closures of convex and pointed cones. This construction is primarily needed for
defining maps between proper cones. The current API is basic and should be extended as necessary.

-/

@[expose] public section

namespace ConvexCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [SMul 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-- The closure of a convex cone inside a topological space as a convex cone. This
construction is mainly used for defining maps between proper cones. -/
/-
**ConvexCone.closure** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：{𝕜 : Type u_1} →   [inst : Semiring 𝕜] →     [inst_1 : PartialOrder 𝕜] →  
     {E : Type u_2} →         [inst_2 : AddCommMonoid E] →           [inst_3 : T
opologicalSpace E] →             [ContinuousAdd E] → [inst_5 : SMul 𝕜 E] → [Cont
inuousConstSMul 𝕜 E] → ConvexCone 𝕜 E → ConvexCone 𝕜 E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of a convex cone inside a topological space as a convex cone. This
construction is mainly used for defining maps between proper cones.
-/
protected def closure (K : ConvexCone 𝕜 E) : ConvexCone 𝕜 E where
  carrier := closure ↑K
  smul_mem' c hc _ h₁ := map_mem_closure (by fun_prop) h₁ fun _ h₂ ↦ K.smul_mem hc h₂
  add_mem' _ h₁ _ h₂ := map_mem_closure₂ continuous_add h₁ h₂ K.add_mem

@[simp, norm_cast]
/-
**ConvexCone.coe_closure** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：coe_closure (K : ConvexCone 𝕜 E) : (K.closure : Set E) = closure K
参数：K : ConvexCone 𝕜 E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_closure (K : ConvexCone 𝕜 E) : (K.closure : Set E) = closure K :=
  rfl

@[simp]
/-
**ConvexCone.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] {E : Type u
_2} [inst_2 : AddCommMonoid E]   [inst_3 : TopologicalSpace E] [inst_4 : Continu
ousAdd E] [inst_5 : SMul 𝕜 E] [inst_6 : ContinuousConstSMul 𝕜 E]   {K : ConvexCo
ne 𝕜 E} {a : E}, a ∈ K.closure ↔ a ∈ closure ↑K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem mem_closure {K : ConvexCone 𝕜 E} {a : E} :
    a ∈ K.closure ↔ a ∈ closure (K : Set E) :=
  Iff.rfl

@[simp]
/-
**ConvexCone.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：closure_eq {K L : ConvexCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = 
L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
-/
theorem closure_eq {K L : ConvexCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = L :=
  SetLike.ext'_iff

end ConvexCone



namespace PointedCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-
**PointedCone.toConvexCone_closure_pointed** 是 Mathlib 中的一个引理，位于命名空间 `PointedCon
e`。
形式化陈述：toConvexCone_closure_pointed (K : PointedCone 𝕜 E) : (K : ConvexCone 𝕜 E).
closure.Pointed
参数：K : PointedCone 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `PointedCone.pointed_toConvexCone`：pointed_toConvexCone (C : PointedCone 
R E) : (C : ConvexCone R E).Pointed
-/
lemma toConvexCone_closure_pointed (K : PointedCone 𝕜 E) : (K : ConvexCone 𝕜 E).closure.Pointed :=
  subset_closure <| PointedCone.pointed_toConvexCone _

/-- The closure of a pointed cone inside a topological space as a pointed cone. This
construction is mainly used for defining maps between proper cones. -/
/-
**PointedCone.closure** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：{𝕜 : Type u_1} →   [inst : Semiring 𝕜] →     [inst_1 : PartialOrder 𝕜] →  
     [inst_2 : IsOrderedRing 𝕜] →         {E : Type u_2} →           [inst_3 : A
ddCommMonoid E] →             [inst_4 : TopologicalSpace E] →               [Con
tinuousAdd E] →                 [inst_6 : _root_.Module 𝕜 E] → [ContinuousConstS
Mul 𝕜 E] → PointedCone 𝕜 E → PointedCone 𝕜 E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The closure of a pointed cone inside a topological space as a pointed cone. This
construction is mainly used for defining maps between proper cones.
-/
protected def closure (K : PointedCone 𝕜 E) : PointedCone 𝕜 E where
  carrier := closure ↑K
  zero_mem' := subset_closure (zero_mem K)
  smul_mem' c _ h₁ := map_mem_closure (continuous_const_smul c.1) h₁ fun _ h₂ ↦ K.smul_mem c.2 h₂
  add_mem' h₁ h₂ := map_mem_closure₂ continuous_add h₁ h₂ (fun _ ha _ hb ↦ K.add_mem ha hb)

@[simp, norm_cast]
/-
**PointedCone.coe_closure** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：coe_closure (K : PointedCone 𝕜 E) : (K.closure : Set E) = closure K
参数：K : PointedCone 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem coe_closure (K : PointedCone 𝕜 E) : (K.closure : Set E) = closure K :=
  rfl

@[simp]
/-
**PointedCone.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : I
sOrderedRing 𝕜] {E : Type u_2}   [inst_3 : AddCommMonoid E] [inst_4 : Topologica
lSpace E] [inst_5 : ContinuousAdd E] [inst_6 : _root_.Module 𝕜 E]   [inst_7 : Co
ntinuousConstSMul 𝕜 E] {K : PointedCone 𝕜 E} {a : E}, a ∈ K.closure ↔ a ∈ closur
e ↑K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
protected theorem mem_closure {K : PointedCone 𝕜 E} {a : E} :
    a ∈ K.closure ↔ a ∈ closure (K : Set E) :=
  Iff.rfl

@[simp]
/-
**PointedCone.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：closure_eq {K L : PointedCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) =
 L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem closure_eq {K L : PointedCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = L :=
  SetLike.ext'_iff

end PointedCone

