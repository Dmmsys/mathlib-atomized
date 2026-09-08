/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Bornology

/-!
# Topology on the integers

The structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/

public section


noncomputable section

open Filter Metric Set Topology

namespace Int

/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Dist ℤ :=
  ⟨fun x y => dist (x : ℝ) y⟩
/-
**Int.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：dist_eq (x y : Int) : dist x y = |(x : Real) - y|
参数：x y : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq (x y : ℤ) : dist x y = |(x : ℝ) - y| := rfl
/-
**Int.dist_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：dist_eq' (m n : Int) : dist m n = |m - n|
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.dist_eq`：dist_eq (x y : Int) : dist x y = |(x : Real) - y|
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem dist_eq' (m n : ℤ) : dist m n = |m - n| := by rw [dist_eq]; norm_cast

@[norm_cast, simp]
/-
**Int.dist_cast_real** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：dist_cast_real (x y : Int) : dist (x : Real) y = dist x y
参数：x y : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y :=
  rfl
/-
**Int.pairwise_one_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：pairwise_one_le_dist : Pairwise fun m n : Int => 1 <= dist m n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.dist_eq`：dist_eq (x y : Int) : dist x y = |(x : Real) - y|
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Int.add_one_le_iff`：∀ {a b : ℤ}, a + 1 ≤ b ↔ a < b
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
-/
theorem pairwise_one_le_dist : Pairwise fun m n : ℤ => 1 ≤ dist m n := by
  intro m n hne
  rw [dist_eq]; norm_cast; rwa [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
/-
**Int.isUniformEmbedding_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : Int -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isUniformEmbedding_bot_of_pairwise_le_dist`：isUniformEmbedding_bo
t_of_pairwise_le_dist {β : Type*} {ε : Real} (hε : 0 < ε) {f : β -> α} (hf : Pai
rwise fun x y => ε <= dist (f x) (f y))…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.pairwise_one_le_dist`：pairwise_one_le_dist : Pairwise fun m n : Int 
=> 1 <= dist m n
-/
theorem isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : ℤ → ℝ) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
/-
**Int.isClosedEmbedding_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：isClosedEmbedding_coe_real : IsClosedEmbedding ((↑) : Int -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isClosedEmbedding_of_pairwise_le_dist`：isClosedEmbedding_of_pairw
ise_le_dist {α : Type*} [TopologicalSpace α] [DiscreteTopology α] {ε : Real} (hε
 : 0 < ε) {f : α -> γ} (hf : Pairw…
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.pairwise_one_le_dist`：pairwise_one_le_dist : Pairwise fun m n : Int 
=> 1 <= dist m n
-/
theorem isClosedEmbedding_coe_real : IsClosedEmbedding ((↑) : ℤ → ℝ) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace ℤ := Int.isUniformEmbedding_coe_real.comapMetricSpace _
/-
**Int.preimage_ball** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：preimage_ball (x : Int) (r : Real) : (↑) ⁻¹' ball (x : Real) r = ball x r
参数：x : Int；r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_ball (x : ℤ) (r : ℝ) : (↑) ⁻¹' ball (x : ℝ) r = ball x r := rfl
/-
**Int.preimage_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：preimage_closedBall (x : Int) (r : Real) : (↑) ⁻¹' closedBall (x : Real) r
 = closedBall x r
参数：x : Int；r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_closedBall (x : ℤ) (r : ℝ) : (↑) ⁻¹' closedBall (x : ℝ) r = closedBall x r := rfl
/-
**Int.ball_eq_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：ball_eq_Ioo (x : Int) (r : Real) : ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉
参数：x : Int；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.preimage_ball`：preimage_ball (x : Int) (r : Real) : (↑) ⁻¹' ball (x 
: Real) r = ball x r
· 使用定理 `Real.ball_eq_Ioo`：Real.ball_eq_Ioo (x r : Real) : ball x r = Ioo (x - r)
 (x + r)
· 使用定理 `Int.preimage_Ioo`：preimage_Ioo {a b : R} : ((↑) : Int -> R) ⁻¹' Set.Ioo 
a b = Set.Ioo ⌊a⌋ ⌈b⌉
-/
theorem ball_eq_Ioo (x : ℤ) (r : ℝ) : ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ := by
  rw [← preimage_ball, Real.ball_eq_Ioo, preimage_Ioo]
/-
**Int.closedBall_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：closedBall_eq_Icc (x : Int) (r : Real) : closedBall x r = Icc ⌈↑x - r⌉ ⌊↑x
 + r⌋
参数：x : Int；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.preimage_closedBall`：preimage_closedBall (x : Int) (r : Real) : (↑) 
⁻¹' closedBall (x : Real) r = closedBall x r
· 使用定理 `Real.closedBall_eq_Icc`：Real.closedBall_eq_Icc {x r : Real} : closedBall
 x r = Icc (x - r) (x + r)
· 使用定理 `Int.preimage_Icc`：preimage_Icc {a b : R} : ((↑) : Int -> R) ⁻¹' Set.Icc 
a b = Set.Icc ⌈a⌉ ⌊b⌋
-/
theorem closedBall_eq_Icc (x : ℤ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ := by
  rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ProperSpace ℤ :=
  ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderBornology ℤ :=
  .of_isCompactIcc 0 (by simp [Int.closedBall_eq_Icc]) (by simp [Int.closedBall_eq_Icc])

@[deprecated (since := "2026-04-07")]
alias cobounded_eq := IsOrderBornology.cobounded_eq

@[simp]
/-
**Int.cofinite_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cofinite_eq : (cofinite : Filter Int) = atBot ⊔ atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.cocompact_eq_cofinite`：cocompact_eq_cofinite (X : Type*) [Topolog
icalSpace X] [DiscreteTopology X] : cocompact X = cofinite
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
· 使用定理 `cocompact_eq_atBot_atTop`：cocompact_eq_atBot_atTop [NoMaxOrder α] [NoMin
Order α] [OrderClosedTopology α] [CompactIccSpace α] : cocompact α = atBot ⊔ atT
op
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
-/
theorem cofinite_eq : (cofinite : Filter ℤ) = atBot ⊔ atTop := by
  rw [← cocompact_eq_cofinite, cocompact_eq_atBot_atTop]

end Int

