/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Basic properties of metric spaces, and instances.

-/

public section

open Set Filter Bornology Topology
open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}
variable [PseudoMetricSpace α]
variable {γ : Type w} [MetricSpace γ]

namespace Metric

variable {x : γ} {s : Set γ}

-- see Note [lower instance priority]
/-
**Metric.** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) _root_.MetricSpace.instT0Space : T0Space γ where
  t0 _ _ h := eq_of_dist_eq_zero <| Metric.inseparable_iff.1 h

/-- A map between metric spaces is a uniform embedding if and only if the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
/-
**Metric.isUniformEmbedding_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isUniformEmbedding_iff' [PseudoMetricSpace β] {f : γ -> β} : IsUniformEmbe
dding f ↔ (forall ε > 0, exists δ > 0, forall {a b : γ}, dist a b < δ -> dist (f
 a) (f b) < ε) ∧ forall δ > 0, exists ε > 0, forall {a b : γ}, dist (f a) (f b) 
< ε -> dist a b < δ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUniformEmbedding_iff_isUniformInducing`：isUniformEmbedding_iff_isUnifo
rmInducing [T0Space α] {f : α -> β} : IsUniformEmbedding f ↔ IsUniformInducing f
· 使用定理 `MetricSpace.instT0Space`：∀ {γ : Type w} [inst : MetricSpace γ], T0Space 
γ
· 使用定理 `Metric.isUniformInducing_iff`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {f : α → β},   IsUniformInducing f
 ↔ UniformContinuo…
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A map between metric spaces is a uniform embedding if and only if the distance b
etween `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and convers
ely.
-/
theorem isUniformEmbedding_iff' [PseudoMetricSpace β] {f : γ → β} :
    IsUniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, dist a b < δ → dist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, dist (f a) (f b) < ε → dist a b < δ := by
  rw [isUniformEmbedding_iff_isUniformInducing, isUniformInducing_iff, uniformContinuous_iff]

/-- If a `PseudoMetricSpace` is a T₀ space, then it is a `MetricSpace`. -/
/-
**Metric._root_.MetricSpace.ofT0PseudoMetricSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `M
etric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `PseudoMetricSpace` is a T₀ space, then it is a `MetricSpace`.
-/
abbrev _root_.MetricSpace.ofT0PseudoMetricSpace (α : Type*) [PseudoMetricSpace α] [T0Space α] :
    MetricSpace α where
  toPseudoMetricSpace := ‹_›
  eq_of_dist_eq_zero hdist := (Metric.inseparable_iff.2 hdist).eq

-- see Note [lower instance priority]
/-- A metric space induces an emetric space -/
/-
**Metric.** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A metric space induces an emetric space
-/
instance (priority := 100) _root_.MetricSpace.toEMetricSpace : EMetricSpace γ :=
  .ofT0PseudoEMetricSpace γ
/-
**Metric.isClosed_of_pairwise_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isClosed_of_pairwise_le_dist {s : Set γ} {ε : Real} (hε : 0 < ε) (hs : s.P
airwise fun x y => ε <= dist x y) : IsClosed s
参数：hε : 0 < ε；hs : s.Pairwise fun x y => ε <= dist x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_spaced_out`：isClosed_of_spaced_out [T0Space α] {V₀ : Set (α 
× α)} (V₀_in : V₀ in 𝓤 α) {s : Set α} (hs : s.Pairwise fun x y => (x, y) ∉ V₀) :
 IsClosed s
· 使用定理 `MetricSpace.instT0Space`：∀ {γ : Type w} [inst : MetricSpace γ], T0Space 
γ
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isClosed_of_pairwise_le_dist {s : Set γ} {ε : ℝ} (hε : 0 < ε)
    (hs : s.Pairwise fun x y => ε ≤ dist x y) : IsClosed s :=
  isClosed_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hs
/-
**Metric.isClosedEmbedding_of_pairwise_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metric
`。
形式化陈述：isClosedEmbedding_of_pairwise_le_dist {α : Type*} [TopologicalSpace α] [Di
screteTopology α] {ε : Real} (hε : 0 < ε) {f : α -> γ} (hf : Pairwise fun x y =>
 ε <= dist (f x) (f y)) : IsClosedEmbedding f
参数：hε : 0 < ε；hf : Pairwise fun x y => ε <= dist (f x) (f y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosedEmbedding_of_spaced_out`：isClosedEmbedding_of_spaced_out {α} [To
pologicalSpace α] [DiscreteTopology α] [T0Space β] {f : α -> β} {s : Set (β × β)
} (hs : s in 𝓤 β) (hf…
· 使用定理 `MetricSpace.instT0Space`：∀ {γ : Type w} [inst : MetricSpace γ], T0Space 
γ
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isClosedEmbedding_of_pairwise_le_dist {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    {ε : ℝ} (hε : 0 < ε) {f : α → γ} (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    IsClosedEmbedding f :=
  isClosedEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf

/-- If `f : β → α` sends any two distinct points to points at distance at least `ε > 0`, then
`f` is a uniform embedding with respect to the discrete uniformity on `β`. -/
/-
**Metric.isUniformEmbedding_bot_of_pairwise_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `M
etric`。
形式化陈述：isUniformEmbedding_bot_of_pairwise_le_dist {β : Type*} {ε : Real} (hε : 0 
< ε) {f : β -> α} (hf : Pairwise fun x y => ε <= dist (f x) (f y)) : @IsUniformE
mbedding _ _ ⊥ (by infer_instance) f
参数：hε : 0 < ε；hf : Pairwise fun x y => ε <= dist (f x) (f y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformEmbedding_of_spaced_out`：isUniformEmbedding_of_spaced_out {α} {
f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β) (hf : Pairwise fun x y => (f x, f 
y) ∉ s) : @IsUniformEm…
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
If `f : β → α` sends any two distinct points to points at distance at least `ε >
 0`, then
`f` is a uniform embedding with respect to the discrete uniformity on `β`.
-/
theorem isUniformEmbedding_bot_of_pairwise_le_dist {β : Type*} {ε : ℝ} (hε : 0 < ε) {f : β → α}
    (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    @IsUniformEmbedding _ _ ⊥ (by infer_instance) f :=
  isUniformEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf

end Metric

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. In this definition, the distance
is given separately, to be able to prescribe some expression which is not defeq to the push-forward
of the edistance to reals. -/
/-
**EMetricSpace.toMetricSpaceOfDist** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EMetricSpace.toMetricSpaceOfDist {α : Type u} [EMetricSpace α] (dist : α -
> α -> Real) (dist_nonneg : forall x y, 0 <= dist x y) (h : forall x y, edist x 
y = .ofReal (dist x y)) : MetricSpace α
参数：dist : α -> α -> Real；dist_nonneg : forall x y, 0 <= dist x y；h : forall x y,
 edist x y = .ofReal (dist x y)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EMetricSpace.instT0Space`：∀ {γ : Type w} [inst : EMetricSpace γ], T0Spac
e γ

--- 原说明 ---
One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that th
e edist and the
uniformity are defeq in the metric space and the emetric space. In this definiti
on, the distance
is given separately, to be able to prescribe some expression which is not defeq 
to the push-forward
of the edistance to reals.
-/
abbrev EMetricSpace.toMetricSpaceOfDist {α : Type u} [EMetricSpace α] (dist : α → α → ℝ)
    (dist_nonneg : ∀ x y, 0 ≤ dist x y) (h : ∀ x y, edist x y = .ofReal (dist x y)) :
    MetricSpace α :=
  letI := PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist dist_nonneg h
  MetricSpace.ofT0PseudoMetricSpace _

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. -/
/-
**EMetricSpace.toMetricSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EMetricSpace.toMetricSpace {α : Type u} [EMetricSpace α] (h : forall x y :
 α, edist x y != ⊤) : MetricSpace α
参数：h : forall x y : α, edist x y != ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that th
e edist and the
uniformity are defeq in the metric space and the emetric space.
-/
abbrev EMetricSpace.toMetricSpace {α : Type u} [EMetricSpace α] (h : ∀ x y : α, edist x y ≠ ⊤) :
    MetricSpace α :=
  EMetricSpace.toMetricSpaceOfDist (ENNReal.toReal <| edist · ·) (by simp) (by simp [h])

/-- Metric space structure pulled back by an injective function. Injectivity is necessary to
ensure that `dist x y = 0` only if `x = y`. -/
/-
**MetricSpace.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MetricSpace.induced {γ β} (f : γ -> β) (hf : Function.Injective f) (m : Me
tricSpace β) : MetricSpace γ
参数：f : γ -> β；hf : Function.Injective f；m : MetricSpace β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Metric space structure pulled back by an injective function. Injectivity is nece
ssary to
ensure that `dist x y = 0` only if `x = y`.
-/
abbrev MetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : MetricSpace β) :
    MetricSpace γ :=
  { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun h => hf (dist_eq_zero.1 h) }

/-- Pull back a metric space structure by a uniform embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `UniformSpace` structure. -/
/-
**IsUniformEmbedding.comapMetricSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [m : MetricSpac
e β] (f : α -> β) (h : IsUniformEmbedding f) : MetricSpace α
参数：f : α -> β；h : IsUniformEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a metric space structure by a uniform embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `UniformSpace` 
structure.
-/
abbrev IsUniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [m : MetricSpace β] (f : α → β)
    (h : IsUniformEmbedding f) : MetricSpace α :=
  .replaceUniformity (.induced f h.injective m) h.comap_uniformity.symm

/-- Pull back a metric space structure by an embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `TopologicalSpace` structure. -/
/-
**Topology.IsEmbedding.comapMetricSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.comapMetricSpace {α β} [TopologicalSpace α] [m : Metr
icSpace β] (f : α -> β) (h : IsEmbedding f) : MetricSpace α
参数：f : α -> β；h : IsEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a metric space structure by an embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `TopologicalSpa
ce` structure.
-/
abbrev Topology.IsEmbedding.comapMetricSpace {α β} [TopologicalSpace α] [m : MetricSpace β]
    (f : α → β) (h : IsEmbedding f) : MetricSpace α :=
  .replaceTopology (.induced f h.injective m) h.eq_induced
/-
**Subtype.metricSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.metricSpace {α : Type*} {p : α -> Prop} [MetricSpace α] : MetricSp
ace (Subtype p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
instance Subtype.metricSpace {α : Type*} {p : α → Prop} [MetricSpace α] :
    MetricSpace (Subtype p) :=
  .induced Subtype.val Subtype.coe_injective ‹_›

@[to_additive]
/-
**MulOpposite.instMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instMetricSpace {α : Type*} [MetricSpace α] : MetricSpace αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance MulOpposite.instMetricSpace {α : Type*} [MetricSpace α] : MetricSpace αᵐᵒᵖ :=
  MetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

section Real

/-- Instantiate the reals as a metric space. -/
/-
**Real.metricSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.metricSpace : MetricSpace Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Instantiate the reals as a metric space.
-/
instance Real.metricSpace : MetricSpace ℝ := .ofT0PseudoMetricSpace ℝ

end Real

section NNReal

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace ℝ≥0 :=
  inferInstanceAs <| MetricSpace (Subtype _)
/-
**NNReal.isUniformEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNReal.isUniformEmbedding_coe : IsUniformEmbedding NNReal.toReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformEmbedding_subtype_val`：isUniformEmbedding_subtype_val {p : α ->
 Prop} : IsUniformEmbedding (Subtype.val : Subtype p -> α)
-/
theorem NNReal.isUniformEmbedding_coe : IsUniformEmbedding NNReal.toReal :=
  isUniformEmbedding_subtype_val
/-
**NNReal.isEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNReal.isEmbedding_coe : Topology.IsEmbedding NNReal.toReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `NNReal.isUniformEmbedding_coe`：NNReal.isUniformEmbedding_coe : IsUniform
Embedding NNReal.toReal
-/
theorem NNReal.isEmbedding_coe : Topology.IsEmbedding NNReal.toReal :=
  isUniformEmbedding_coe.isEmbedding
/-
**NNReal.isClosedEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNReal.isClosedEmbedding_coe : Topology.IsClosedEmbedding NNReal.toReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem NNReal.isClosedEmbedding_coe : Topology.IsClosedEmbedding NNReal.toReal :=
  isClosed_Ici.isClosedEmbedding_subtypeVal

end NNReal

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MetricSpace β] : MetricSpace (ULift β) :=
  fast_instance% MetricSpace.induced ULift.down ULift.down_injective ‹_›

section Prod

/-
**Prod.metricSpaceMax** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.metricSpaceMax [MetricSpace β] : MetricSpace (γ × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.metricSpaceMax [MetricSpace β] : MetricSpace (γ × β) :=
  .ofT0PseudoMetricSpace _

end Prod

section Pi

open Finset

variable {X : β → Type*} [Fintype β] [∀ b, MetricSpace (X b)]

/-- A finite product of metric spaces is a metric space, with the sup distance. -/
/-
**metricSpacePi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：metricSpacePi : MetricSpace (forall b, X b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of metric spaces is a metric space, with the sup distance.
-/
instance metricSpacePi : MetricSpace (∀ b, X b) := .ofT0PseudoMetricSpace _

end Pi

namespace Metric

section SecondCountable

open TopologicalSpace

-- TODO: use `Countable` instead of `Encodable`
/-- A metric space is second countable if one can reconstruct up to any `ε>0` any element of the
space from countably many data. -/
/-
**Metric.secondCountable_of_countable_discretization** 是 Mathlib 中的一个定理，位于命名空间 `
Metric`。
形式化陈述：secondCountable_of_countable_discretization {α : Type u} [PseudoMetricSpac
e α] (H : forall ε > (0 : Real), exists (β : Type*) (_ : Encodable β) (F : α -> 
β), forall x y, F x = F y -> dist x y <= ε) : SecondCountableTopology α
参数：H : forall ε > (0 : Real), exists (β : Type*) (_ : Encodable β) (F : α -> β),
 forall x y, F x = F y -> dist x y <= ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.secondCountable_of_almost_dense_set`：secondCountable_of_almost_de
nse_set (H : forall ε > (0 : Real), exists s : Set α, s.Countable ∧ forall x, ex
ists y in s, dist x y <= ε) : Se…
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.apply_rangeSplitting`：apply_rangeSplitting (f : α -> β) (x : range f
) : f (rangeSplitting f x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A metric space is second countable if one can reconstruct up to any `ε>0` any el
ement of the
space from countably many data.
-/
theorem secondCountable_of_countable_discretization {α : Type u} [PseudoMetricSpace α]
    (H : ∀ ε > (0 : ℝ), ∃ (β : Type*) (_ : Encodable β) (F : α → β),
      ∀ x y, F x = F y → dist x y ≤ ε) :
    SecondCountableTopology α := by
  refine secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := rangeSplitting F
  refine ⟨range Finv, ⟨countable_range _, fun x => ?_⟩⟩
  let x' := Finv ⟨F x, mem_range_self _⟩
  have : F x' = F x := apply_rangeSplitting F _
  exact ⟨x', mem_range_self _, hF _ _ this.symm⟩

end SecondCountable

end Metric

section EqRel

-- TODO: add `dist_congr` similar to `edist_congr`?
/-
**SeparationQuotient.instDist** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparationQuotient.instDist {α : Type u} [PseudoMetricSpace α] : Dist (Sep
arationQuotient α) where dist
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SeparationQuotient.instDist {α : Type u} [PseudoMetricSpace α] :
    Dist (SeparationQuotient α) where
  dist := lift₂ dist fun x y x' y' hx hy ↦ by rw [dist_edist, dist_edist, ← edist_mk x,
    ← edist_mk x', mk_eq_mk.2 hx, mk_eq_mk.2 hy]
/-
**SeparationQuotient.dist_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeparationQuotient.dist_mk {α : Type u} [PseudoMetricSpace α] (p q : α) : 
dist (mk p) (mk q) = dist p q
参数：p q : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SeparationQuotient.dist_mk {α : Type u} [PseudoMetricSpace α] (p q : α) :
    dist (mk p) (mk q) = dist p q :=
  rfl
/-
**SeparationQuotient.instMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparationQuotient.instMetricSpace {α : Type u} [PseudoMetricSpace α] : Me
tricSpace (SeparationQuotient α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SeparationQuotient.instMetricSpace {α : Type u} [PseudoMetricSpace α] :
    MetricSpace (SeparationQuotient α) :=
  EMetricSpace.toMetricSpaceOfDist dist (surjective_mk.forall₂.2 fun _ _ ↦ dist_nonneg) <|
    surjective_mk.forall₂.2 edist_dist

end EqRel

namespace PseudoEMetricSpace

open ENNReal

variable {X : Type*} (m : PseudoEMetricSpace X) (d : X → X → ℝ≥0∞) (hd : d = edist)

/-- Build new pseudoemetric space from an old one where the edistance is provably (but typically
non-definitionally) equal to some given edistance. We also provide convenience versions for
PseudoMetric, Emetric and Metric spaces. -/
-- See note [forgetful inheritance]
-- See note [reducible non-instances]
/-
**PseudoEMetricSpace.replaceEDist** 是 Mathlib 中的一个缩写定义，位于命名空间 `PseudoEMetricSpac
e`。
形式化陈述：replaceEDist : PseudoEMetricSpace X where edist
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev replaceEDist : PseudoEMetricSpace X where
  edist := d
  edist_self := by simp [hd]
  edist_comm := by simp [hd, edist_comm]
  edist_triangle := by simp [hd, edist_triangle]
  uniformity_edist := by simp [hd, uniformity_edist]
  __ := m
/-
**PseudoEMetricSpace.replaceEDist_eq** 是 Mathlib 中的一个引理，位于命名空间 `PseudoEMetricSpa
ce`。
形式化陈述：replaceEDist_eq : m.replaceEDist d hd = m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.ext`：∀ {α : Type u_2} {m m' : PseudoEMetricSpace α}, 
m.toEDist = m'.toEDist → m = m'
· 使用定理 `EDist.ext`：∀ {α : Type u_2} {x y : EDist α}, edist = edist → x = y
-/
lemma replaceEDist_eq : m.replaceEDist d hd = m := by ext : 2; exact hd

-- Check uniformity is unchanged
/-
**PseudoEMetricSpace.** 是 Mathlib 中的一个示例，位于命名空间 `PseudoEMetricSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (replaceEDist m d hd).toUniformSpace = m.toUniformSpace := by
  dsimp +instances [replaceEDist]

end PseudoEMetricSpace

namespace PseudoMetricSpace
variable {X : Type*} (m : PseudoMetricSpace X) (d : X → X → ℝ) (hd : d = dist)

/-- Build new pseudometric space from an old one where the distance is provably (but typically
non-definitionally) equal to some given distance. We also provide convenience versions for
PseudoEMetric, Emetric and Metric spaces. -/
-- See note [forgetful inheritance]
-- See note [reducible non-instances]
/-
**PseudoMetricSpace.replaceDist** 是 Mathlib 中的一个缩写定义，位于命名空间 `PseudoMetricSpace`。
形式化陈述：replaceDist : PseudoMetricSpace X where dist
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev replaceDist : PseudoMetricSpace X where
  dist := d
  dist_self := by simp [hd]
  dist_comm := by simp [hd, dist_comm]
  dist_triangle := by simp [hd, dist_triangle]
  edist_dist := by simp [hd, edist_dist]
  uniformity_dist := by simp [hd, uniformity_dist]
  cobounded_sets := by simp [hd, cobounded_sets]
  __ := m
/-
**PseudoMetricSpace.replaceDist_eq** 是 Mathlib 中的一个引理，位于命名空间 `PseudoMetricSpace`
。
形式化陈述：replaceDist_eq : m.replaceDist d hd = m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.ext`：PseudoMetricSpace.ext {α : Type*} {m m' : PseudoM
etricSpace α} (h : m.toDist = m'.toDist) : m = m'
· 使用定理 `Dist.ext`：∀ {α : Type u_3} {x y : Dist α}, dist = dist → x = y
-/
lemma replaceDist_eq : m.replaceDist d hd = m := by ext : 2; exact hd

-- Check uniformity is unchanged
/-
**PseudoMetricSpace.** 是 Mathlib 中的一个示例，位于命名空间 `PseudoMetricSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (replaceDist m d hd).toUniformSpace = m.toUniformSpace := by
  dsimp +instances [replaceDist]

-- Check Bornology is unchanged
/-
**PseudoMetricSpace.** 是 Mathlib 中的一个示例，位于命名空间 `PseudoMetricSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (replaceDist m d hd).toBornology = m.toBornology := by
  dsimp +instances [replaceDist]

end PseudoMetricSpace

namespace EMetricSpace

open ENNReal

variable {X : Type*} (m : EMetricSpace X) (d : X → X → ℝ≥0∞) (hd : d = edist)

/-- Build new emetric space from an old one where the edistance is provably (but typically
non-definitionally) equal to some given edistance. We also provide convenience versions for
PseudoEMetric, PseudoMetric and Metric spaces. -/
-- See note [forgetful inheritance]
-- See note [reducible non-instances]
/-
**EMetricSpace.replaceEDist** 是 Mathlib 中的一个缩写定义，位于命名空间 `EMetricSpace`。
形式化陈述：replaceEDist : EMetricSpace X where edist
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev replaceEDist : EMetricSpace X where
  edist := d
  edist_self := by simp [hd]
  edist_comm := by simp [hd, edist_comm]
  edist_triangle := by simp [hd, edist_triangle]
  eq_of_edist_eq_zero := by simp [hd]
/-
**EMetricSpace.replaceEDist_eq** 是 Mathlib 中的一个引理，位于命名空间 `EMetricSpace`。
形式化陈述：replaceEDist_eq : m.replaceEDist d hd = m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetricSpace.ext`：∀ {α : Type u_2} {m m' : EMetricSpace α}, m.toEDist = 
m'.toEDist → m = m'
· 使用定理 `EDist.ext`：∀ {α : Type u_2} {x y : EDist α}, edist = edist → x = y
-/
lemma replaceEDist_eq : m.replaceEDist d hd = m := by ext : 2; exact hd

-- Check uniformity is unchanged
/-
**EMetricSpace.** 是 Mathlib 中的一个示例，位于命名空间 `EMetricSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (replaceEDist m d hd).toUniformSpace = m.toUniformSpace := by
  simp +instances [replaceEDist_eq]

end EMetricSpace

namespace MetricSpace
variable {X : Type*} (m : MetricSpace X) (d : X → X → ℝ) (hd : d = dist)

/-- Build new metric space from an old one where the distance is provably (but typically
non-definitionally) equal to some given distance. We also provide convenience versions for
PseudoEMetric, PseudoMatric and EMetric spaces. -/
-- See note [forgetful inheritance]
-- See note [reducible non-instances]
/-
**MetricSpace.replaceDist** 是 Mathlib 中的一个缩写定义，位于命名空间 `MetricSpace`。
形式化陈述：replaceDist : MetricSpace X where dist
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev replaceDist : MetricSpace X where
  dist := d
  dist_self := by simp [hd]
  dist_comm := by simp [hd, dist_comm]
  dist_triangle := by simp [hd, dist_triangle]
  eq_of_dist_eq_zero := by simp [hd]
/-
**MetricSpace.replaceDist_eq** 是 Mathlib 中的一个引理，位于命名空间 `MetricSpace`。
形式化陈述：replaceDist_eq : m.replaceDist d hd = m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MetricSpace.ext`：MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h :
 m.toDist = m'.toDist) : m = m'
· 使用定理 `Dist.ext`：∀ {α : Type u_3} {x y : Dist α}, dist = dist → x = y
-/
lemma replaceDist_eq : m.replaceDist d hd = m := by ext : 2; exact hd

-- Check uniformity is unchanged
/-
**MetricSpace.** 是 Mathlib 中的一个示例，位于命名空间 `MetricSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (replaceDist m d hd).toUniformSpace = m.toUniformSpace := by
  simp +instances [replaceDist_eq]

-- Check Bornology is unchanged
/-
**MetricSpace.** 是 Mathlib 中的一个示例，位于命名空间 `MetricSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (replaceDist m d hd).toBornology = m.toBornology := by
  simp +instances [replaceDist_eq]

end MetricSpace

