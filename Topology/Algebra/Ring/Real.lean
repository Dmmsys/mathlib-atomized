/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Bornology.Real
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Real

/-!
# Topological algebra properties of ℝ

This file defines topological field/(semi)ring structures on the
(extended) (nonnegative) reals and shows the algebraic operations are
(uniformly) continuous.

It also includes a bit of more general topological theory of the reals,
needed to define the structures and prove continuity.
-/

public section

assert_not_exists StarRing UniformContinuousConstSMul UniformOnFun

noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoncompactSpace ℝ := Int.isClosedEmbedding_coe_real.noncompactSpace
/-
**Real.uniformContinuous_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.uniformContinuous_add : UniformContinuous fun p : Real × Real => p.1 
+ p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用定理 `rat_add_continuous_lemma`：rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) 
: exists δ > 0, forall {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ -> abv (a₂ - b₂) < δ
 -> abv (a₁ + …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
-/
theorem Real.uniformContinuous_add : UniformContinuous fun p : ℝ × ℝ => p.1 + p.2 :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0
    ⟨δ, δ0, fun _ _ h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ h₁ h₂⟩
/-
**Real.uniformContinuous_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.uniformContinuous_neg : UniformContinuous (@Neg.neg Real _)
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
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
-/
theorem Real.uniformContinuous_neg : UniformContinuous (@Neg.neg ℝ _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by simpa only [abs_sub_comm, Real.dist_eq, neg_sub_neg] using h⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUniformAddGroup ℝ :=
  IsUniformAddGroup.mk' Real.uniformContinuous_add Real.uniformContinuous_neg
/-
**Real.uniformContinuous_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.uniformContinuous_const_mul {x : Real} : UniformContinuous (x * ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_continuousAt_zero`：∀ {α : Type u_1} {β : Type u_2} 
[inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom : Type 
u_3}   [inst_3 : UniformSpac…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem Real.uniformContinuous_const_mul {x : ℝ} : UniformContinuous (x * ·) :=
  uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom ℝ x)
    (continuous_const_smul x).continuousAt

-- short-circuit type class inference
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalAddGroup ℝ := by infer_instance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalRing ℝ := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalDivisionRing ℝ := inferInstance

namespace EReal

/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousNeg EReal := ⟨negOrderIso.continuous⟩

end EReal

namespace NNReal

/-!
Instances for the following typeclasses are defined:

* `IsTopologicalSemiring ℝ≥0`
* `ContinuousSub ℝ≥0`
* `ContinuousInv₀ ℝ≥0` (continuity of `x⁻¹` away from `0`)
* `ContinuousSMul ℝ≥0 α` (whenever `α` has a continuous `MulAction ℝ α`)

Everything is inherited from the corresponding structures on the reals.
-/
-- short-circuit type class inference
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalSemiring ℝ≥0 where
  toContinuousAdd := continuousAdd_induced toRealHom
  toContinuousMul := continuousMul_induced toRealHom
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousSub ℝ≥0 :=
  ⟨((continuous_coe.fst'.sub continuous_coe.snd').max continuous_const).subtype_mk _⟩
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousInv₀ ℝ≥0 := inferInstance

variable {α : Type*}
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [MulAction ℝ α] [ContinuousSMul ℝ α] :
    ContinuousSMul ℝ≥0 α where
  continuous_smul := continuous_induced_dom.fst'.smul continuous_snd

end NNReal

namespace ENNReal

open Filter NNReal Set Topology

/-
**ENNReal.isEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：isEmbedding_coe : IsEmbedding ((↑) : Real>=0 -> Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.isEmbedding_of_ordConnected`：StrictMono.isEmbedding_of_ordCon
nected {α β : Type*} [LinearOrder α] [LinearOrder β] [TopologicalSpace α] [h : O
rderTopology α] [Topological…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.coe_strictMono`：coe_strictMono : StrictMono ofNNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.range_coe'`：range_coe' : range ofNNReal = Iio ∞
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
-/
theorem isEmbedding_coe : IsEmbedding ((↑) : ℝ≥0 → ℝ≥0∞) :=
  coe_strictMono.isEmbedding_of_ordConnected <| by rw [range_coe']; exact ordConnected_Iio

@[simp, norm_cast]
/-
**ENNReal.tendsto_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : Real>=0} : Tendsto (fun
 a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `ENNReal.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : Real>=0 ->
 Real>=0∞)
-/
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0} {a : ℝ≥0} :
    Tendsto (fun a => (m a : ℝ≥0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe.tendsto_nhds_iff.symm
/-
**ENNReal.isOpenEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：isOpenEmbedding_coe : IsOpenEmbedding ((↑) : Real>=0 -> Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : Real>=0 ->
 Real>=0∞)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.range_coe'`：range_coe' : range ofNNReal = Iio ∞
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
-/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℝ≥0 → ℝ≥0∞) :=
  ⟨isEmbedding_coe, by rw [range_coe']; exact isOpen_Iio⟩
/-
**ENNReal.nhds_coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhds_coe_coe {r p : Real>=0} : 𝓝 ((r : Real>=0∞), (p : Real>=0∞)) = (𝓝 (r,
 p)).map fun p : Real>=0 × Real>=0 => (↑p.1, ↑p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `Topology.IsOpenEmbedding.prodMap`：∀ {X : Type u} {Y : Type v} {W : Type 
u_1} {Z : Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   
[inst_2 : TopologicalS…
· 使用定理 `ENNReal.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑) 
: Real>=0 -> Real>=0∞)
-/
theorem nhds_coe_coe {r p : ℝ≥0} :
    𝓝 ((r : ℝ≥0∞), (p : ℝ≥0∞)) = (𝓝 (r, p)).map fun p : ℝ≥0 × ℝ≥0 => (↑p.1, ↑p.2) :=
  ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousAdd ℝ≥0∞ := by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  simp only [ContinuousAt, some_eq_coe, nhds_coe_coe, ← coe_add, tendsto_map'_iff,
    Function.comp_def, tendsto_coe, tendsto_add]
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousInv ℝ≥0∞ := ⟨OrderIso.invENNReal.continuous⟩

end ENNReal

