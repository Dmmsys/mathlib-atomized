/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.SetLike.Basic

/-! # Class of grading-preserving functions and isomorphisms

We define `GradedFunLike F 𝒜 ℬ` where `𝒜` and `ℬ` represent some sort of grading. This class
assumes `FunLike A B` where `A` and `B` are the underlying types.

We also define `GradedEquivLike E 𝒜 ℬ`, which is similar to `EquivLike`, where here `e : E` is
required to satisfy `x ∈ 𝒜 i ↔ e x ∈ ℬ i`.
-/

@[expose] public section

/-- The class `GradedFunLike F 𝒜 ℬ` expresses that terms of type `F` have an injective coercion to
grading-preserving functions from `A` to `B`, where `𝒜` is a grading on `A` and `ℬ` is a grading on
`B`. This typeclass has `[FunLike F A B]` as one of the assumptions. This typeclass is used in the
characterisation of certain types of graded homomorphisms, such as `GradedRingHom` and
`GradedAlgHom`. For example, what would be called `"GradedRingHomClass F 𝒜 ℬ`" would be expressed
as `[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]`.
-/
/-
**GradedFunLike** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   {A : outParam (Type u_2)} →     {B : outParam (Type u_3
)} →       {σ : outParam (Type u_4)} →         {τ : outParam (Type u_5)} →      
     {ι : outParam (Type u_6)} →             [SetLike σ A] → [SetLike τ B] → out
Param (ι → σ) → outParam (ι → τ) → [FunLike F A B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class `GradedFunLike F 𝒜 ℬ` expresses that terms of type `F` have an injecti
ve coercion to
grading-preserving functions from `A` to `B`, where `𝒜` is a grading on `A` and 
`ℬ` is a grading on
`B`. This typeclass has `[FunLike F A B]` as one of the assumptions. This typecl
ass is used in the
characterisation of certain types of graded homomorphisms, such as `GradedRingHo
m` and
`GradedAlgHom`. For example, what would be called `"GradedRingHomClass F 𝒜 ℬ`" w
ould be expressed
as `[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]`.
-/
class GradedFunLike (F : Type*) {A B σ τ ι : outParam Type*}
    [SetLike σ A] [SetLike τ B] (𝒜 : outParam <| ι → σ) (ℬ : outParam <| ι → τ)
    [FunLike F A B] where
  map_mem (f : F) {i x} : x ∈ 𝒜 i → f x ∈ ℬ i

section GradedFunLike

variable {F A B σ τ ι : Type*}
  [SetLike σ A] [SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]

/-
**Graded.map_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
参数：f : F；h : x in 𝒜 i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedFunLike.map_mem`：∀ {F : Type u_1} {A : outParam (Type u_2)} {B : o
utParam (Type u_3)} {σ : outParam (Type u_4)} {τ : outParam (Type u_5)}   {ι : o
utParam (Ty…
-/
lemma Graded.map_mem (f : F) {i x} (h : x ∈ 𝒜 i) : f x ∈ ℬ i :=
  GradedFunLike.map_mem f h

/-- A graded map descends to a map on each component. -/
/-
**Graded.subtypeMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Graded.subtypeMap (f : F) (i : ι) (x : 𝒜 i) : ℬ i
参数：f : F；i : ι；x : 𝒜 i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded map descends to a map on each component.
-/
def Graded.subtypeMap (f : F) (i : ι) (x : 𝒜 i) : ℬ i :=
  ⟨f x, map_mem f x.2⟩

end GradedFunLike

/-- The class `GradedEquivLike E 𝒜 ℬ` says that `E` is a type of grading-preserving isomorphisms
between `𝒜` and `ℬ`. It is the combination of `GradedFunLike E 𝒜 ℬ` and `EquivLike E A B`. -/
/-
**GradedEquivLike** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_1) →   {A : outParam (Type u_2)} →     {B : outParam (Type u_3
)} →       {σ : outParam (Type u_4)} →         {τ : outParam (Type u_5)} →      
     {ι : outParam (Type u_6)} →             [SetLike σ A] → [SetLike τ B] → out
Param (ι → σ) → outParam (ι → τ) → [EquivLike E A B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class `GradedEquivLike E 𝒜 ℬ` says that `E` is a type of grading-preserving 
isomorphisms
between `𝒜` and `ℬ`. It is the combination of `GradedFunLike E 𝒜 ℬ` and `EquivLi
ke E A B`.
-/
class GradedEquivLike (E : Type*) {A B σ τ ι : outParam Type*}
    [SetLike σ A] [SetLike τ B] (𝒜 : outParam <| ι → σ) (ℬ : outParam <| ι → τ)
    [EquivLike E A B] where
  map_mem_iff (e : E) {i x} : e x ∈ ℬ i ↔ x ∈ 𝒜 i

section GradedEquivLike

variable (E : Type*) {A B σ τ ι : Type*} [SetLike σ A] [SetLike τ B]
  (𝒜 : ι → σ) (ℬ : ι → τ) [EquivLike E A B] [GradedEquivLike E 𝒜 ℬ]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) GradedEquivLike.toGradedFunLike : GradedFunLike E 𝒜 ℬ where
  __ := (inferInstance : FunLike E A B)
  map_mem e := (map_mem_iff e).mpr

variable {E 𝒜 ℬ}
/-
**Graded.map_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Graded.map_mem_iff (e : E) {i x} : e x in ℬ i ↔ x in 𝒜 i
参数：e : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedEquivLike.map_mem_iff`：∀ {E : Type u_1} {A : outParam (Type u_2)} 
{B : outParam (Type u_3)} {σ : outParam (Type u_4)} {τ : outParam (Type u_5)}   
{ι : outParam (Ty…
-/
lemma Graded.map_mem_iff (e : E) {i x} : e x ∈ ℬ i ↔ x ∈ 𝒜 i :=
  GradedEquivLike.map_mem_iff e
alias ⟨Graded.mem_of_map_mem, Graded.map_mem_of_mem⟩ := Graded.map_mem_iff

/-- A graded isomorphism descends to an isomorphism on each component. -/
/-
**Graded.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Graded`。
形式化陈述：{E : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       {σ : Type u
_4} →         {τ : Type u_5} →           {ι : Type u_6} →             [inst : Se
tLike σ A] →               [inst_1 : SetLike τ B] →                 {𝒜 : ι → σ} 
→                   {ℬ : ι → τ} → [inst_2 : EquivLike E A B] → [GradedEquivLike 
E 𝒜 ℬ] → E → (i : ι) → ↥(𝒜 i) ≃ ↥(ℬ i)
参数：i : ι；𝒜 i；ℬ i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedEquivLike.toGradedFunLike`：∀ (E : Type u_1) {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_4} {τ : Type u_5} {ι : Type u_6} [inst : SetLike σ A]   [ins
t_1 : SetLike τ B] (𝒜…

--- 原说明 ---
A graded isomorphism descends to an isomorphism on each component.
-/
@[simps] def Graded.equiv (e : E) (i : ι) : 𝒜 i ≃ ℬ i where
  toFun := subtypeMap e i
  invFun y := ⟨EquivLike.inv e (y : B),
    mem_of_map_mem e <| by rw [EquivLike.apply_inv_apply]; exact y.2⟩
  left_inv _ := by ext; exact EquivLike.inv_apply_apply e _
  right_inv _ := by ext; exact EquivLike.apply_inv_apply e _

end GradedEquivLike

