/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Nat

/-!
# Topology on the rational numbers

The structure of a metric space on `ℚ` is introduced in this file, induced from `ℝ`.
-/

public section

open Filter Metric Set Topology

namespace Rat

/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace ℚ :=
  fast_instance% MetricSpace.induced (↑) Rat.cast_injective Real.metricSpace
/-
**Rat.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：dist_eq (x y : Rat) : dist x y = |(x : Real) - y|
参数：x y : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq (x y : ℚ) : dist x y = |(x : ℝ) - y| := rfl

@[norm_cast, simp]
/-
**Rat.dist_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：dist_cast (x y : Rat) : dist (x : Real) y = dist x y
参数：x y : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y :=
  rfl
/-
**Rat.uniformContinuous_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：uniformContinuous_coe_real : UniformContinuous ((↑) : Rat -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap`：uniformContinuous_comap {f : α -> β} [u : Unifo
rmSpace β] : @UniformContinuous α β (UniformSpace.comap f u) u f
-/
theorem uniformContinuous_coe_real : UniformContinuous ((↑) : ℚ → ℝ) :=
  uniformContinuous_comap
/-
**Rat.isUniformEmbedding_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : Rat -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformEmbedding_comap`：isUniformEmbedding_comap {α : Type*} {β : Type
*} {f : α -> β} [u : UniformSpace β] (hf : Function.Injective f) : @IsUniformEmb
edding α β (Un…
· 使用引理 `Rat.cast_injective`：cast_injective : Injective ((↑) : Rat -> α) | ⟨n₁, d
₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩, h => by have d₁a : (d₁ : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : ℚ → ℝ) :=
  isUniformEmbedding_comap Rat.cast_injective
/-
**Rat.isDenseEmbedding_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isDenseEmbedding_coe_real : IsDenseEmbedding ((↑) : Rat -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isDenseEmbedding`：IsUniformEmbedding.isDenseEmbedding
 {f : α -> β} (h : IsUniformEmbedding f) (hd : DenseRange f) : IsDenseEmbedding 
f
· 使用定理 `Rat.isUniformEmbedding_coe_real`：isUniformEmbedding_coe_real : IsUniform
Embedding ((↑) : Rat -> Real)
· 使用定理 `Rat.denseRange_cast`：Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [
IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜] : 
DenseRang…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem isDenseEmbedding_coe_real : IsDenseEmbedding ((↑) : ℚ → ℝ) :=
  isUniformEmbedding_coe_real.isDenseEmbedding Rat.denseRange_cast
/-
**Rat.isEmbedding_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isEmbedding_coe_real : IsEmbedding ((↑) : Rat -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseEmbedding.isEmbedding`：isEmbedding (de : IsDenseEmbedding e) : Is
Embedding e where __
· 使用定理 `Rat.isDenseEmbedding_coe_real`：isDenseEmbedding_coe_real : IsDenseEmbedd
ing ((↑) : Rat -> Real)
-/
theorem isEmbedding_coe_real : IsEmbedding ((↑) : ℚ → ℝ) :=
  isDenseEmbedding_coe_real.isEmbedding
/-
**Rat.continuous_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：continuous_coe_real : Continuous ((↑) : Rat -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `Rat.uniformContinuous_coe_real`：uniformContinuous_coe_real : UniformCont
inuous ((↑) : Rat -> Real)
-/
theorem continuous_coe_real : Continuous ((↑) : ℚ → ℝ) :=
  uniformContinuous_coe_real.continuous

end Rat

@[norm_cast, simp]
/-
**Nat.dist_cast_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.dist_cast_rat (x y : Nat) : dist (x : Rat) y = dist x y
参数：x y : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dist_cast_real`：dist_cast_real (x y : Nat) : dist (x : Real) y = dis
t x y
· 使用定理 `Rat.dist_cast`：dist_cast (x y : Rat) : dist (x : Real) y = dist x y
-/
theorem Nat.dist_cast_rat (x y : ℕ) : dist (x : ℚ) y = dist x y := by
  rw [← Nat.dist_cast_real, ← Rat.dist_cast]; congr
/-
**Nat.isUniformEmbedding_coe_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.isUniformEmbedding_coe_rat : IsUniformEmbedding ((↑) : Nat -> Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isUniformEmbedding_bot_of_pairwise_le_dist`：isUniformEmbedding_bo
t_of_pairwise_le_dist {β : Type*} {ε : Real} (hε : 0 < ε) {f : β -> α} (hf : Pai
rwise fun x y => ε <= dist (f x) (f y))…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.dist_cast_rat`：Nat.dist_cast_rat (x y : Nat) : dist (x : Rat) y = di
st x y
· 使用定理 `Nat.pairwise_one_le_dist`：pairwise_one_le_dist : Pairwise fun m n : Nat 
=> 1 <= dist m n
-/
theorem Nat.isUniformEmbedding_coe_rat : IsUniformEmbedding ((↑) : ℕ → ℚ) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one <| by simpa using Nat.pairwise_one_le_dist
/-
**Nat.isClosedEmbedding_coe_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.isClosedEmbedding_coe_rat : IsClosedEmbedding ((↑) : Nat -> Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isClosedEmbedding_of_pairwise_le_dist`：isClosedEmbedding_of_pairw
ise_le_dist {α : Type*} [TopologicalSpace α] [DiscreteTopology α] {ε : Real} (hε
 : 0 < ε) {f : α -> γ} (hf : Pairw…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.dist_cast_rat`：Nat.dist_cast_rat (x y : Nat) : dist (x : Rat) y = di
st x y
· 使用定理 `Nat.pairwise_one_le_dist`：pairwise_one_le_dist : Pairwise fun m n : Nat 
=> 1 <= dist m n
-/
theorem Nat.isClosedEmbedding_coe_rat : IsClosedEmbedding ((↑) : ℕ → ℚ) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one <| by simpa using Nat.pairwise_one_le_dist

@[norm_cast, simp]
/-
**Int.dist_cast_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.dist_cast_rat (x y : Int) : dist (x : Rat) y = dist x y
参数：x y : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.dist_cast_real`：dist_cast_real (x y : Int) : dist (x : Real) y = dis
t x y
· 使用定理 `Rat.dist_cast`：dist_cast (x y : Rat) : dist (x : Real) y = dist x y
-/
theorem Int.dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y := by
  rw [← Int.dist_cast_real, ← Rat.dist_cast]; congr
/-
**Int.isUniformEmbedding_coe_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.isUniformEmbedding_coe_rat : IsUniformEmbedding ((↑) : Int -> Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isUniformEmbedding_bot_of_pairwise_le_dist`：isUniformEmbedding_bo
t_of_pairwise_le_dist {β : Type*} {ε : Real} (hε : 0 < ε) {f : β -> α} (hf : Pai
rwise fun x y => ε <= dist (f x) (f y))…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Int.dist_cast_rat`：Int.dist_cast_rat (x y : Int) : dist (x : Rat) y = di
st x y
· 使用定理 `Int.pairwise_one_le_dist`：pairwise_one_le_dist : Pairwise fun m n : Int 
=> 1 <= dist m n
-/
theorem Int.isUniformEmbedding_coe_rat : IsUniformEmbedding ((↑) : ℤ → ℚ) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one <| by simpa using Int.pairwise_one_le_dist
/-
**Int.isClosedEmbedding_coe_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.isClosedEmbedding_coe_rat : IsClosedEmbedding ((↑) : Int -> Rat)
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Int.dist_cast_rat`：Int.dist_cast_rat (x y : Int) : dist (x : Rat) y = di
st x y
· 使用定理 `Int.pairwise_one_le_dist`：pairwise_one_le_dist : Pairwise fun m n : Int 
=> 1 <= dist m n
-/
theorem Int.isClosedEmbedding_coe_rat : IsClosedEmbedding ((↑) : ℤ → ℚ) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one <| by simpa using Int.pairwise_one_le_dist

namespace Rat

/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoncompactSpace ℚ := Int.isClosedEmbedding_coe_rat.noncompactSpace
/-
**Rat.uniformContinuous_add** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：uniformContinuous_add : UniformContinuous fun p : Rat × Rat => p.1 + p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `Rat.isUniformEmbedding_coe_real`：isUniformEmbedding_coe_real : IsUniform
Embedding ((↑) : Rat -> Real)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `Real.uniformContinuous_add`：Real.uniformContinuous_add : UniformContinuo
us fun p : Real × Real => p.1 + p.2
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `Rat.uniformContinuous_coe_real`：uniformContinuous_coe_real : UniformCont
inuous ((↑) : Rat -> Real)
-/
theorem uniformContinuous_add : UniformContinuous fun p : ℚ × ℚ => p.1 + p.2 :=
  Rat.isUniformEmbedding_coe_real.isUniformInducing.uniformContinuous_iff.2 <| by
    simp only [Function.comp_def, Rat.cast_add]
    exact Real.uniformContinuous_add.comp
      (Rat.uniformContinuous_coe_real.prodMap Rat.uniformContinuous_coe_real)
/-
**Rat.uniformContinuous_neg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：uniformContinuous_neg : UniformContinuous (@Neg.neg Rat _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
-/
theorem uniformContinuous_neg : UniformContinuous (@Neg.neg ℚ _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by
      simpa only [abs_sub_comm, dist_eq, cast_neg, neg_sub_neg] using h⟩
/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUniformAddGroup ℚ :=
  IsUniformAddGroup.mk' Rat.uniformContinuous_add Rat.uniformContinuous_neg
/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalAddGroup ℚ := inferInstance
/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology ℚ := induced_orderTopology _ Rat.cast_lt exists_rat_btwn
/-
**Rat.uniformContinuous_abs** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：uniformContinuous_abs : UniformContinuous (abs : Rat -> Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_abs`：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K]
 [IsStrictOrderedRing K] (q : ℚ), ↑|q| = |↑q|
· 使用定理 `abs_abs_sub_abs_le_abs_sub`：∀ {G : Type u_1} [inst : AddCommGroup G] [in
st_1 : LinearOrder G] [IsOrderedAddMonoid G] (a b : G),   ||a| - |b|| ≤ |a - b|
-/
theorem uniformContinuous_abs : UniformContinuous (abs : ℚ → ℚ) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ h =>
      lt_of_le_of_lt (by simpa [Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩
/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalRing ℚ := inferInstance

nonrec theorem totallyBounded_Icc (a b : ℚ) : TotallyBounded (Icc a b) := by
  simpa only [preimage_cast_Icc]
    using totallyBounded_preimage Rat.isUniformEmbedding_coe_real.isUniformInducing
      (totallyBounded_Icc (a : ℝ) b)

end Rat

namespace NNRat

/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace ℚ≥0 :=
  inferInstanceAs <| MetricSpace (Subtype _)

set_option linter.style.whitespace false in -- linter false positive
@[simp ←, push_cast]
/-
**NNRat.dist_eq** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：dist_eq (p q : Rat>=0) : dist p q = dist (p : Rat) (q : Rat)
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_eq (p q : ℚ≥0) : dist p q = dist (p : ℚ) (q : ℚ) := rfl

set_option linter.style.whitespace false in -- linter false positive
@[simp ←, push_cast]
/-
**NNRat.nndist_eq** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：nndist_eq (p q : Rat>=0) : nndist p q = nndist (p : Rat) (q : Rat)
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nndist_eq (p q : ℚ≥0) : nndist p q = nndist (p : ℚ) (q : ℚ) := rfl
/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalSemiring ℚ≥0 where
  toContinuousAdd := continuousAdd_induced Nonneg.coeRingHom
  toContinuousMul := continuousMul_induced Nonneg.coeRingHom
/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousSub ℚ≥0 := ⟨Continuous.subtype_mk (by fun_prop) _⟩
/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology ℚ≥0 := orderTopology_of_ordConnected (t := Set.Ici 0)
/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousInv₀ ℚ≥0 := inferInstance

-- Special case of `IsBoundedSMul.continuousSMul` but this shortcut instance reduces dependencies
/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousSMul ℚ ℝ where
  continuous_smul := continuous_induced_dom.fst'.smul (M := ℝ) (X := ℝ) continuous_snd
/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [TopologicalSpace R] [MulAction ℚ R] [MulAction ℚ≥0 R] [IsScalarTower ℚ≥0 ℚ R]
    [ContinuousSMul ℚ R] : ContinuousSMul ℚ≥0 R where
  continuous_smul := by
    conv in _ • _ => rw [← NNRat.cast_smul_eq_nnqsmul ℚ]
    fun_prop
/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousSMul ℚ≥0 NNReal where
  continuous_smul := Continuous.subtype_mk (by fun_prop) _

end NNRat

