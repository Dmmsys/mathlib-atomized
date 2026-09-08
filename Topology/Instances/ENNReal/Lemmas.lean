/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Topology on extended non-negative reals
-/

@[expose] public section

noncomputable section

open Filter Function Metric Set Topology
open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

section TopologicalSpace

open TopologicalSpace

/-
**ENNReal.isOpen_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：isOpen_ne_top : IsOpen { a : Real>=0∞ | a != ∞ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `ENNReal.instT5Space`：T5Space ENNReal
-/
theorem isOpen_ne_top : IsOpen { a : ℝ≥0∞ | a ≠ ∞ } := isOpen_ne
/-
**ENNReal.isOpen_Ico_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：isOpen_Ico_zero : IsOpen (Ico 0 b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.Ico_eq_Iio`：∀ {y : ENNReal}, Set.Ico 0 y = Set.Iio y
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
-/
theorem isOpen_Ico_zero : IsOpen (Ico 0 b) := by
  rw [ENNReal.Ico_eq_Iio]
  exact isOpen_Iio
/-
**ENNReal.coe_range_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_range_mem_nhds : range ((↑) : Real>=0 -> Real>=0∞) in 𝓝 (r : Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `ENNReal.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑) 
: Real>=0 -> Real>=0∞)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem coe_range_mem_nhds : range ((↑) : ℝ≥0 → ℝ≥0∞) ∈ 𝓝 (r : ℝ≥0∞) :=
  IsOpen.mem_nhds isOpenEmbedding_coe.isOpen_range <| mem_range_self _

@[fun_prop]
/-
**ENNReal.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuous_coe : Continuous ((↑) : Real>=0 -> Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `ENNReal.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : Real>=0 ->
 Real>=0∞)
-/
theorem continuous_coe : Continuous ((↑) : ℝ≥0 → ℝ≥0∞) :=
  isEmbedding_coe.continuous
/-
**ENNReal.tendsto_coe_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_coe_toNNReal {a : Real>=0∞} (ha : a != ⊤) : Tendsto (↑) (𝓝 a.toNNR
eal) (𝓝 a)
参数：ha : a != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Re
al>=0∞)
-/
lemma tendsto_coe_toNNReal {a : ℝ≥0∞} (ha : a ≠ ⊤) : Tendsto (↑) (𝓝 a.toNNReal) (𝓝 a) := by
  nth_rewrite 2 [← coe_toNNReal ha]
  exact continuous_coe.tendsto _
/-
**ENNReal.continuous_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuous_coe_iff {α} [TopologicalSpace α] {f : α -> Real>=0} : (Continuo
us fun a => (f a : Real>=0∞)) ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `ENNReal.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : Real>=0 ->
 Real>=0∞)
-/
theorem continuous_coe_iff {α} [TopologicalSpace α] {f : α → ℝ≥0} :
    (Continuous fun a => (f a : ℝ≥0∞)) ↔ Continuous f :=
  isEmbedding_coe.continuous_iff.symm
/-
**ENNReal.nhds_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhds_coe {r : Real>=0} : 𝓝 (r : Real>=0∞) = (𝓝 r).map (↑)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `ENNReal.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑) 
: Real>=0 -> Real>=0∞)
-/
theorem nhds_coe {r : ℝ≥0} : 𝓝 (r : ℝ≥0∞) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_coe.map_nhds_eq r).symm
/-
**ENNReal.tendsto_nhds_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_nhds_coe_iff {α : Type*} {l : Filter α} {x : Real>=0} {f : Real>=0
∞ -> α} : Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ (↑) : Real>=0 -> α) (𝓝 x) l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.nhds_coe`：nhds_coe {r : Real>=0} : 𝓝 (r : Real>=0∞) = (𝓝 r).map 
(↑)
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_nhds_coe_iff {α : Type*} {l : Filter α} {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ (↑) : ℝ≥0 → α) (𝓝 x) l := by
  rw [nhds_coe, tendsto_map'_iff]
/-
**ENNReal.continuousAt_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuousAt_coe_iff {α : Type*} [TopologicalSpace α] {x : Real>=0} {f : R
eal>=0∞ -> α} : ContinuousAt f ↑x ↔ ContinuousAt (f ∘ (↑) : Real>=0 -> α) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.tendsto_nhds_coe_iff`：tendsto_nhds_coe_iff {α : Type*} {l : Filt
er α} {x : Real>=0} {f : Real>=0∞ -> α} : Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ (↑) 
: Real>=0 -> α) (𝓝…
-/
theorem continuousAt_coe_iff {α : Type*} [TopologicalSpace α] {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    ContinuousAt f ↑x ↔ ContinuousAt (f ∘ (↑) : ℝ≥0 → α) x :=
  tendsto_nhds_coe_iff
/-
**ENNReal.continuous_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuous_ofReal : Continuous ENNReal.ofReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.continuous_coe_iff`：continuous_coe_iff {α} [TopologicalSpace α] 
{f : α -> Real>=0} : (Continuous fun a => (f a : Real>=0∞)) ↔ Continuous f
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_real_toNNReal`：Continuous Real.toNNReal
-/
theorem continuous_ofReal : Continuous ENNReal.ofReal :=
  (continuous_coe_iff.2 continuous_id).comp continuous_real_toNNReal
/-
**ENNReal.tendsto_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_ofReal {f : Filter α} {m : α -> Real} {a : Real} (h : Tendsto m f 
(𝓝 a)) : Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 (ENNReal.ofReal a))
参数：h : Tendsto m f (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_ofReal`：continuous_ofReal : Continuous ENNReal.ofReal
-/
theorem tendsto_ofReal {f : Filter α} {m : α → ℝ} {a : ℝ} (h : Tendsto m f (𝓝 a)) :
    Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 (ENNReal.ofReal a)) :=
  (continuous_ofReal.tendsto a).comp h
/-
**ENNReal.tendsto_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_toNNReal {a : Real>=0∞} (ha : a != ∞) : Tendsto ENNReal.toNNReal (
𝓝 a) (𝓝 a.toNNReal)
参数：ha : a != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.nhds_coe`：nhds_coe {r : Real>=0} : 𝓝 (r : Real>=0∞) = (𝓝 r).map 
(↑)
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem tendsto_toNNReal {a : ℝ≥0∞} (ha : a ≠ ∞) :
    Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal) := by
  lift a to ℝ≥0 using ha
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id
/-
**ENNReal.tendsto_toNNReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_toNNReal_iff {f : α -> Real>=0∞} {u : Filter α} (ha : a != ∞) (hf 
: forall x, f x != ∞) : Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 (a.toNNReal)) ↔ Tend
sto f u (𝓝 a)
参数：ha : a != ∞；hf : forall x, f x != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_comp_toNNReal_comp`：coe_comp_toNNReal_comp {ι : Type*} {f : 
ι -> Real>=0∞} (hf : forall x, f x != ∞) : (fun (x : Real>=0) => (x : Real>=0∞))
 ∘ ENNReal.toNNReal …
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `ENNReal.tendsto_coe_toNNReal`：tendsto_coe_toNNReal {a : Real>=0∞} (ha : 
a != ⊤) : Tendsto (↑) (𝓝 a.toNNReal) (𝓝 a)
· 使用定理 `ENNReal.tendsto_toNNReal`：tendsto_toNNReal {a : Real>=0∞} (ha : a != ∞) 
: Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal)
-/
theorem tendsto_toNNReal_iff {f : α → ℝ≥0∞} {u : Filter α} (ha : a ≠ ∞) (hf : ∀ x, f x ≠ ∞) :
    Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 (a.toNNReal)) ↔ Tendsto f u (𝓝 a) := by
  refine ⟨fun h => ?_, fun h => (ENNReal.tendsto_toNNReal ha).comp h⟩
  rw [← coe_comp_toNNReal_comp hf]
  exact (tendsto_coe_toNNReal ha).comp h
/-
**ENNReal.tendsto_toNNReal_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_toNNReal_iff' {f : α -> Real>=0∞} {u : Filter α} {a : Real>=0} (hf
 : forall x, f x != ∞) : Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 a) ↔ Tendsto f u (𝓝
 a)
参数：hf : forall x, f x != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r
· 使用定理 `ENNReal.tendsto_toNNReal_iff`：tendsto_toNNReal_iff {f : α -> Real>=0∞} {
u : Filter α} (ha : a != ∞) (hf : forall x, f x != ∞) : Tendsto (ENNReal.toNNRea
l ∘ f) u (𝓝 (a.toN…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem tendsto_toNNReal_iff' {f : α → ℝ≥0∞} {u : Filter α} {a : ℝ≥0} (hf : ∀ x, f x ≠ ∞) :
    Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 a) ↔ Tendsto f u (𝓝 a) := by
  rw [← toNNReal_coe a]
  exact tendsto_toNNReal_iff coe_ne_top hf
/-
**ENNReal.eventuallyEq_of_toReal_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal
`。
形式化陈述：eventuallyEq_of_toReal_eventuallyEq {l : Filter α} {f g : α -> Real>=0∞} (
hfi : forallᶠ x in l, f x != ∞) (hgi : forallᶠ x in l, g x != ∞) (hfg : (fun x =
> (f x).toReal) =ᶠ[l] fun x => (g x).toReal) : f =ᶠ[l] g
参数：hfi : forallᶠ x in l, f x != ∞；hgi : forallᶠ x in l, g x != ∞；hfg : (fun x =>
 (f x).toReal) =ᶠ[l] fun x => (g x).toReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
-/
theorem eventuallyEq_of_toReal_eventuallyEq {l : Filter α} {f g : α → ℝ≥0∞}
    (hfi : ∀ᶠ x in l, f x ≠ ∞) (hgi : ∀ᶠ x in l, g x ≠ ∞)
    (hfg : (fun x => (f x).toReal) =ᶠ[l] fun x => (g x).toReal) : f =ᶠ[l] g := by
  filter_upwards [hfi, hgi, hfg] with _ hfx hgx _
  rwa [← ENNReal.toReal_eq_toReal_iff' hfx hgx]
/-
**ENNReal.continuousOn_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuousOn_toNNReal : ContinuousOn ENNReal.toNNReal { a | a != ∞ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ENNReal.tendsto_toNNReal`：tendsto_toNNReal {a : Real>=0∞} (ha : a != ∞) 
: Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal)
-/
theorem continuousOn_toNNReal : ContinuousOn ENNReal.toNNReal { a | a ≠ ∞ } := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNNReal ha)
/-
**ENNReal.tendsto_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_toReal {a : Real>=0∞} (ha : a != ∞) : Tendsto ENNReal.toReal (𝓝 a)
 (𝓝 a.toReal)
参数：ha : a != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {x : R
eal>=0} : Tendsto (fun a => (m a : Real)) f (𝓝 (x : Real)) ↔ Tendsto m f (𝓝 x)
· 使用定理 `ENNReal.tendsto_toNNReal`：tendsto_toNNReal {a : Real>=0∞} (ha : a != ∞) 
: Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal)
-/
theorem tendsto_toReal {a : ℝ≥0∞} (ha : a ≠ ∞) : Tendsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal) :=
  NNReal.tendsto_coe.2 <| tendsto_toNNReal ha
/-
**ENNReal.continuousOn_toReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：continuousOn_toReal : ContinuousOn ENNReal.toReal { a | a != ∞ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `ENNReal.continuousOn_toNNReal`：continuousOn_toNNReal : ContinuousOn ENNR
eal.toNNReal { a | a != ∞ }
-/
lemma continuousOn_toReal : ContinuousOn ENNReal.toReal { a | a ≠ ∞ } :=
  NNReal.continuous_coe.comp_continuousOn continuousOn_toNNReal
/-
**ENNReal.continuousAt_toReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：continuousAt_toReal (hx : x != ∞) : ContinuousAt ENNReal.toReal x
参数：hx : x != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用引理 `ENNReal.continuousOn_toReal`：continuousOn_toReal : ContinuousOn ENNReal.
toReal { a | a != ∞ }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用定理 `ENNReal.isOpen_ne_top`：isOpen_ne_top : IsOpen { a : Real>=0∞ | a != ∞ }
-/
lemma continuousAt_toReal (hx : x ≠ ∞) : ContinuousAt ENNReal.toReal x :=
  continuousOn_toReal.continuousAt (isOpen_ne_top.mem_nhds_iff.mpr hx)

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
/-
**ENNReal.neTopHomeomorphNNReal** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：neTopHomeomorphNNReal : { a | a != ∞ } ≃ₜ Real>=0 where toEquiv
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`.
-/
def neTopHomeomorphNNReal : { a | a ≠ ∞ } ≃ₜ ℝ≥0 where
  toEquiv := neTopEquivNNReal
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 continuousOn_toNNReal
  continuous_invFun := continuous_coe.subtype_mk _

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
/-
**ENNReal.ltTopHomeomorphNNReal** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：ltTopHomeomorphNNReal : { a | a < ∞ } ≃ₜ Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`.
-/
def ltTopHomeomorphNNReal : { a | a < ∞ } ≃ₜ ℝ≥0 := by
  refine (Homeomorph.setCongr ?_).trans neTopHomeomorphNNReal
  simp only [lt_top_iff_ne_top]
/-
**ENNReal.nhds_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhds_top : 𝓝 ∞ = ⨅ (a) (_ : a != ∞), 𝓟 (Ioi a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_top_order`：nhds_top_order [TopologicalSpace α] [Preorder α] [OrderT
op α] [OrderTopology α] : 𝓝 (⊤ : α) = ⨅ (l) (_ : l < ⊤), 𝓟 (Ioi l)
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_top : 𝓝 ∞ = ⨅ (a) (_ : a ≠ ∞), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp [lt_top_iff_ne_top, Ioi]
/-
**ENNReal.nhds_top'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhds_top' : 𝓝 ∞ = ⨅ r : Real>=0, 𝓟 (Ioi ↑r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.nhds_top`：nhds_top : 𝓝 ∞ = ⨅ (a) (_ : a != ∞), 𝓟 (Ioi a)
· 使用定理 `ENNReal.iInf_ne_top`：iInf_ne_top [CompleteLattice α] (f : Real>=0∞ -> α)
 : ⨅ (x) (_ : x != ∞), f x = ⨅ x : Real>=0, f x
-/
theorem nhds_top' : 𝓝 ∞ = ⨅ r : ℝ≥0, 𝓟 (Ioi ↑r) :=
  nhds_top.trans <| iInf_ne_top _
/-
**ENNReal.nhds_top_basis** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhds_top_basis : (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_top_basis`：nhds_top_basis [TopologicalSpace α] [LinearOrder α] [Ord
erTop α] [OrderTopology α] [Nontrivial α] : (𝓝 ⊤).HasBasis (fun a : α => a < ⊤) 
fun …
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
-/
theorem nhds_top_basis : (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a :=
  _root_.nhds_top_basis
/-
**ENNReal.tendsto_nhds_top_iff_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_nhds_top_iff_nnreal {m : α -> Real>=0∞} {f : Filter α} : Tendsto m
 f (𝓝 ∞) ↔ forall x : Real>=0, forallᶠ a in f, ↑x < m a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.nhds_top'`：nhds_top' : 𝓝 ∞ = ⨅ r : Real>=0, 𝓟 (Ioi ↑r)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhds_top_iff_nnreal {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ∞) ↔ ∀ x : ℝ≥0, ∀ᶠ a in f, ↑x < m a := by
  simp only [nhds_top', tendsto_iInf, tendsto_principal, mem_Ioi]
/-
**ENNReal.tendsto_nhds_top_iff_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_nhds_top_iff_nat {m : α -> Real>=0∞} {f : Filter α} : Tendsto m f 
(𝓝 ∞) ↔ forall n : Nat, forallᶠ a in f, ↑n < m a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.tendsto_nhds_top_iff_nnreal`：tendsto_nhds_top_iff_nnreal {m : α 
-> Real>=0∞} {f : Filter α} : Tendsto m f (𝓝 ∞) ↔ forall x : Real>=0, forallᶠ a 
in f, ↑x < m a
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.instArchimedean`：Archimedean NNReal
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_natCast`：coe_natCast (n : Nat) : ((n : Real>=0) : Real>=0∞) 
= n
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
-/
theorem tendsto_nhds_top_iff_nat {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ∞) ↔ ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a :=
  tendsto_nhds_top_iff_nnreal.trans
    ⟨fun h n => by simpa only [ENNReal.coe_natCast] using h n, fun h x =>
      let ⟨n, hn⟩ := exists_nat_gt x
      (h n).mono fun _ => lt_trans <| by rwa [← ENNReal.coe_natCast, coe_lt_coe]⟩
/-
**ENNReal.tendsto_nhds_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_nhds_top {m : α -> Real>=0∞} {f : Filter α} (h : forall n : Nat, f
orallᶠ a in f, ↑n < m a) : Tendsto m f (𝓝 ∞)
参数：h : forall n : Nat, forallᶠ a in f, ↑n < m a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_nhds_top_iff_nat`：tendsto_nhds_top_iff_nat {m : α -> Rea
l>=0∞} {f : Filter α} : Tendsto m f (𝓝 ∞) ↔ forall n : Nat, forallᶠ a in f, ↑n <
 m a
-/
theorem tendsto_nhds_top {m : α → ℝ≥0∞} {f : Filter α} (h : ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a) :
    Tendsto m f (𝓝 ∞) :=
  tendsto_nhds_top_iff_nat.2 h
/-
**ENNReal.tendsto_nat_nhds_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_nat_nhds_top : Tendsto (fun n : Nat => ↑n) atTop (𝓝 ∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.tendsto_nhds_top`：tendsto_nhds_top {m : α -> Real>=0∞} {f : Filt
er α} (h : forall n : Nat, forallᶠ a in f, ↑n < m a) : Tendsto m f (𝓝 ∞)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
-/
theorem tendsto_nat_nhds_top : Tendsto (fun n : ℕ => ↑n) atTop (𝓝 ∞) :=
  tendsto_nhds_top fun n =>
    mem_atTop_sets.2 ⟨n + 1, fun _m hm => mem_ofPred.2 <| Nat.cast_lt.2 <| Nat.lt_of_succ_le hm⟩

@[simp, norm_cast]
/-
**ENNReal.tendsto_coe_nhds_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_coe_nhds_top {f : α -> Real>=0} {l : Filter α} : Tendsto (fun x =>
 (f x : Real>=0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_nhds_top_iff_nnreal`：tendsto_nhds_top_iff_nnreal {m : α 
-> Real>=0∞} {f : Filter α} : Tendsto m f (𝓝 ∞) ↔ forall x : Real>=0, forallᶠ a 
in f, ↑x < m a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用引理 `Filter.atTop_basis_Ioi`：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@
atTop α _).HasBasis (fun _ => True) Ioi
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instArchimedean`：Archimedean NNReal
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_coe_nhds_top {f : α → ℝ≥0} {l : Filter α} :
    Tendsto (fun x => (f x : ℝ≥0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff_nnreal, atTop_basis_Ioi.tendsto_right_iff]; simp

@[simp]
/-
**ENNReal.tendsto_ofReal_nhds_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_ofReal_nhds_top {f : α -> Real} {l : Filter α} : Tendsto (fun x =>
 ENNReal.ofReal (f x)) l (𝓝 ∞) ↔ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.tendsto_coe_nhds_top`：tendsto_coe_nhds_top {f : α -> Real>=0} {l
 : Filter α} : Tendsto (fun x => (f x : Real>=0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop
· 使用定理 `Real.tendsto_toNNReal_atTop_iff`：∀ {α : Type u_2} {l : Filter α} {f : α 
→ ℝ},   Filter.Tendsto (fun x => (f x).toNNReal) l Filter.atTop ↔ Filter.Tendsto
 f l Filter.atTop
-/
theorem tendsto_ofReal_nhds_top {f : α → ℝ} {l : Filter α} :
    Tendsto (fun x ↦ ENNReal.ofReal (f x)) l (𝓝 ∞) ↔ Tendsto f l atTop :=
  tendsto_coe_nhds_top.trans Real.tendsto_toNNReal_atTop_iff
/-
**ENNReal.tendsto_ofReal_atTop** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_ofReal_atTop : Tendsto ENNReal.ofReal atTop (𝓝 ∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_ofReal_nhds_top`：tendsto_ofReal_nhds_top {f : α -> Real}
 {l : Filter α} : Tendsto (fun x => ENNReal.ofReal (f x)) l (𝓝 ∞) ↔ Tendsto f l 
atTop
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem tendsto_ofReal_atTop : Tendsto ENNReal.ofReal atTop (𝓝 ∞) :=
  tendsto_ofReal_nhds_top.2 tendsto_id
/-
**ENNReal.nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhds_zero : 𝓝 (0 : Real>=0∞) = ⨅ (a) (_ : a != 0), 𝓟 (Iio a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_bot_order`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Pre
order α] [inst_2 : OrderBot α] [OrderTopology α],   nhds ⊥ = ⨅ l, ⨅ (_ : ⊥ < l),
 Fil…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_zero : 𝓝 (0 : ℝ≥0∞) = ⨅ (a) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [pos_iff_ne_zero, Iio]
/-
**ENNReal.nhds_zero_basis** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhds_zero_basis : (𝓝 (0 : Real>=0∞)).HasBasis (fun a : Real>=0∞ => 0 < a) 
fun a => Iio a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_bot_basis`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [inst_2 : OrderBot α] [OrderTopology α]   [Nontrivial α], (nhds ⊥).H
asBa…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
-/
theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) fun a => Iio a :=
  nhds_bot_basis
/-
**ENNReal.nhds_zero_basis_Iic** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhds_zero_basis_Iic : (𝓝 (0 : Real>=0∞)).HasBasis (fun a : Real>=0∞ => 0 <
 a) Iic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_bot_basis_Iic`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [inst_2 : OrderBot α] [OrderTopology α]   [Nontrivial α] [Densel
yOrdered…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
-/
theorem nhds_zero_basis_Iic : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) Iic :=
  nhds_bot_basis_Iic

-- TODO: add a TC for `≠ ∞`?
@[instance]
/-
**ENNReal.nhdsGT_coe_neBot** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhdsGT_coe_neBot {r : Real>=0} : (𝓝[>] (r : Real>=0∞)).NeBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsGT_neBot_of_exists_gt`：nhdsGT_neBot_of_exists_gt {a : α} (H : exists
 b, a < b) : NeBot (𝓝[>] a)
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
theorem nhdsGT_coe_neBot {r : ℝ≥0} : (𝓝[>] (r : ℝ≥0∞)).NeBot :=
  nhdsGT_neBot_of_exists_gt ⟨∞, ENNReal.coe_lt_top⟩
/-
**ENNReal.nhdsGT_zero_neBot** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：(nhdsWithin 0 (Set.Ioi 0)).NeBot
参数：Set.Ioi 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.nhdsGT_coe_neBot`：nhdsGT_coe_neBot {r : Real>=0} : (𝓝[>] (r : Re
al>=0∞)).NeBot
-/
@[instance] theorem nhdsGT_zero_neBot : (𝓝[>] (0 : ℝ≥0∞)).NeBot := nhdsGT_coe_neBot
/-
**ENNReal.nhdsGT_one_neBot** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：(nhdsWithin 1 (Set.Ioi 1)).NeBot
参数：Set.Ioi 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.nhdsGT_coe_neBot`：nhdsGT_coe_neBot {r : Real>=0} : (𝓝[>] (r : Re
al>=0∞)).NeBot
-/
@[instance] theorem nhdsGT_one_neBot : (𝓝[>] (1 : ℝ≥0∞)).NeBot := nhdsGT_coe_neBot
/-
**ENNReal.nhdsGT_nat_neBot** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ), (nhdsWithin (↑n) (Set.Ioi ↑n)).NeBot
参数：n : ℕ；nhdsWithin (↑n) (Set.Ioi ↑n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.nhdsGT_coe_neBot`：nhdsGT_coe_neBot {r : Real>=0} : (𝓝[>] (r : Re
al>=0∞)).NeBot
-/
@[instance] theorem nhdsGT_nat_neBot (n : ℕ) : (𝓝[>] (n : ℝ≥0∞)).NeBot := nhdsGT_coe_neBot

@[instance]
/-
**ENNReal.nhdsGT_ofNat_neBot** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhdsGT_ofNat_neBot (n : Nat) [n.AtLeastTwo] : (𝓝[>] (OfNat.ofNat n : Real>
=0∞)).NeBot
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.nhdsGT_coe_neBot`：nhdsGT_coe_neBot {r : Real>=0} : (𝓝[>] (r : Re
al>=0∞)).NeBot
-/
theorem nhdsGT_ofNat_neBot (n : ℕ) [n.AtLeastTwo] : (𝓝[>] (OfNat.ofNat n : ℝ≥0∞)).NeBot :=
  nhdsGT_coe_neBot

@[instance]
/-
**ENNReal.nhdsLT_neBot** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhdsLT_neBot [NeZero x] : (𝓝[<] x).NeBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsLT_neBot_of_exists_lt`：nhdsLT_neBot_of_exists_lt {b : α} (H : exists
 a, a < b) : NeBot (𝓝[<] b)
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem nhdsLT_neBot [NeZero x] : (𝓝[<] x).NeBot :=
  nhdsLT_neBot_of_exists_lt ⟨0, NeZero.pos x⟩

/-- Closed intervals `Set.Icc (x - ε) (x + ε)`, `ε ≠ 0`, form a basis of neighborhoods of an
extended nonnegative real number `x ≠ ∞`. We use `Set.Icc` instead of `Set.Ioo` because this way the
statement works for `x = 0`.
-/
/-
**ENNReal.hasBasis_nhds_of_ne_top'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：hasBasis_nhds_of_ne_top' (xt : x != ∞) : (𝓝 x).HasBasis (· != 0) (fun ε =>
 Icc (x - ε) (x + ε))
参数：xt : x != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.Icc_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Icc ⊥ a = Set.Iic a
· 使用定理 `nhds_bot_basis_Iic`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [inst_2 : OrderBot α] [OrderTopology α]   [Nontrivial α] [Densel
yOrdered…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `nhds_basis_Ioo'`：nhds_basis_Ioo' {a : α} (hl : exists l, l < a) (hu : ex
ists u, a < u) : (𝓝 a).HasBasis (fun b : α × α => b.1 < a ∧ a < b.2) fun b => Io
o b.1…
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_add_pos_lt`：lt_iff_exists_add_pos_lt : a < b ↔ exi
sts r : Real>=0, 0 < r ∧ a + r < b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `Set.Icc_subset_Ioo`：Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a
₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `lt_tsub_comm`：lt_tsub_comm : a < b - c ↔ c < b - a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
Closed intervals `Set.Icc (x - ε) (x + ε)`, `ε ≠ 0`, form a basis of neighborhoo
ds of an
extended nonnegative real number `x ≠ ∞`. We use `Set.Icc` instead of `Set.Ioo` 
because this way the
statement works for `x = 0`.
-/
theorem hasBasis_nhds_of_ne_top' (xt : x ≠ ∞) :
    (𝓝 x).HasBasis (· ≠ 0) (fun ε => Icc (x - ε) (x + ε)) := by
  rcases eq_zero_or_pos x with rfl | x0
  · simp_rw [zero_tsub, zero_add, ← bot_eq_zero, Icc_bot, ← bot_lt_iff_ne_bot]
    exact nhds_bot_basis_Iic
  · refine (nhds_basis_Ioo' ⟨_, x0⟩ ⟨_, xt.lt_top⟩).to_hasBasis ?_ fun ε ε0 => ?_
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      rcases exists_between (tsub_pos_of_lt ha) with ⟨ε, ε0, hε⟩
      rcases lt_iff_exists_add_pos_lt.1 hb with ⟨δ, δ0, hδ⟩
      refine ⟨min ε δ, (lt_min ε0 (coe_pos.2 δ0)).ne', Icc_subset_Ioo ?_ ?_⟩
      · exact lt_tsub_comm.2 ((min_le_left _ _).trans_lt hε)
      · grw [min_le_right]
        exact hδ
    · exact ⟨(x - ε, x + ε), ⟨ENNReal.sub_lt_self xt x0.ne' ε0,
        lt_add_right xt ε0⟩, Ioo_subset_Icc_self⟩
/-
**ENNReal.hasBasis_nhds_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：hasBasis_nhds_of_ne_top (xt : x != ∞) : (𝓝 x).HasBasis (0 < ·) (fun ε => I
cc (x - ε) (x + ε))
参数：xt : x != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.hasBasis_nhds_of_ne_top'`：hasBasis_nhds_of_ne_top' (xt : x != ∞)
 : (𝓝 x).HasBasis (· != 0) (fun ε => Icc (x - ε) (x + ε))
-/
theorem hasBasis_nhds_of_ne_top (xt : x ≠ ∞) :
    (𝓝 x).HasBasis (0 < ·) (fun ε => Icc (x - ε) (x + ε)) := by
  simpa only [pos_iff_ne_zero] using hasBasis_nhds_of_ne_top' xt
/-
**ENNReal.Icc_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：Icc_mem_nhds (xt : x != ∞) (ε0 : ε != 0) : Icc (x - ε) (x + ε) in 𝓝 x
参数：xt : x != ∞；ε0 : ε != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `ENNReal.hasBasis_nhds_of_ne_top'`：hasBasis_nhds_of_ne_top' (xt : x != ∞)
 : (𝓝 x).HasBasis (· != 0) (fun ε => Icc (x - ε) (x + ε))
-/
theorem Icc_mem_nhds (xt : x ≠ ∞) (ε0 : ε ≠ 0) : Icc (x - ε) (x + ε) ∈ 𝓝 x :=
  (hasBasis_nhds_of_ne_top' xt).mem_of_mem ε0
/-
**ENNReal.nhds_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：nhds_of_ne_top (xt : x != ∞) : 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε))
参数：xt : x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `ENNReal.hasBasis_nhds_of_ne_top`：hasBasis_nhds_of_ne_top (xt : x != ∞) :
 (𝓝 x).HasBasis (0 < ·) (fun ε => Icc (x - ε) (x + ε))
-/
theorem nhds_of_ne_top (xt : x ≠ ∞) : 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) :=
  (hasBasis_nhds_of_ne_top xt).eq_biInf
/-
**ENNReal.biInf_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：biInf_le_nhds : forall x : Real>=0∞, ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) <= 𝓝
 x | ∞ => iInf₂_le_of_le 1 one_pos by simpa only [← coe_one, top_sub_coe, top_ad
d, Icc_self, principal_singleton] using pure_le_nhds _ | (x : Real>=0) => (nhds_
of_ne_top coe_ne_top).ge  protected theorem tendsto_nhds_of_Icc {f : Filter α} {
u : α -> Real>=0∞} {a : Real>=0∞} (h : forall ε > 0, forallᶠ x in f, u x in Icc 
(a - ε) (a + ε)) : Tendsto u f (𝓝 a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `ENNReal.nhds_of_ne_top`：nhds_of_ne_top (xt : x != ∞) : 𝓝 x = ⨅ ε > 0, 𝓟 
(Icc (x - ε) (x + ε))
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem biInf_le_nhds : ∀ x : ℝ≥0∞, ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) ≤ 𝓝 x
  | ∞ => iInf₂_le_of_le 1 one_pos <| by
    simpa only [← coe_one, top_sub_coe, top_add, Icc_self, principal_singleton] using pure_le_nhds _
  | (x : ℝ≥0) => (nhds_of_ne_top coe_ne_top).ge
/-
**ENNReal.tendsto_nhds_of_Icc** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {u : α → ENNReal} {a : ENNReal},   (∀ ε > 
0, ∀ᶠ (x : α) in f, u x ∈ Set.Icc (a - ε) (a + ε)) → Filter.Tendsto u f (nhds a)
参数：∀ ε > 0, ∀ᶠ (x : α) in f, u x ∈ Set.Icc (a - ε) (a + ε)；nhds a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.biInf_le_nhds`：biInf_le_nhds : forall x : Real>=0∞, ⨅ ε > 0, 𝓟 (
Icc (x - ε) (x + ε)) <= 𝓝 x | ∞ => iInf₂_le_of_le 1 one_pos by simpa only [← coe
_one, top_s…
-/
protected theorem tendsto_nhds_of_Icc {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ∀ ε > 0, ∀ᶠ x in f, u x ∈ Icc (a - ε) (a + ε)) : Tendsto u f (𝓝 a) := by
  refine Tendsto.mono_right ?_ (biInf_le_nhds _)
  simpa only [tendsto_iInf, tendsto_principal]

/-- Characterization of neighborhoods for `ℝ≥0∞` numbers. See also `tendsto_order`
for a version with strict inequalities. -/
/-
**ENNReal.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {u : α → ENNReal} {a : ENNReal},   a ≠ ⊤ →
 (Filter.Tendsto u f (nhds a) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ∈ Set.Icc (a - ε) 
(a + ε))
参数：Filter.Tendsto u f (nhds a) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ∈ Set.Icc (a - ε)
 (a + ε)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.nhds_of_ne_top`：nhds_of_ne_top (xt : x != ∞) : 𝓝 x = ⨅ ε > 0, 𝓟 
(Icc (x - ε) (x + ε))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Characterization of neighborhoods for `ℝ≥0∞` numbers. See also `tendsto_order`
for a version with strict inequalities.
-/
protected theorem tendsto_nhds {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ∞) :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ∈ Icc (a - ε) (a + ε) := by
  simp only [nhds_of_ne_top ha, tendsto_iInf, tendsto_principal]
/-
**ENNReal.tendsto_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {u : α → ENNReal}, Filter.Tendsto u f (nhd
s 0) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ≤ ε
参数：nhds 0；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `ENNReal.nhds_zero_basis_Iic`：nhds_zero_basis_Iic : (𝓝 (0 : Real>=0∞)).Ha
sBasis (fun a : Real>=0∞ => 0 < a) Iic
-/
protected theorem tendsto_nhds_zero {f : Filter α} {u : α → ℝ≥0∞} :
    Tendsto u f (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ≤ ε :=
  nhds_zero_basis_Iic.tendsto_right_iff
/-
**ENNReal.tendsto_const_sub_nhds_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_const_sub_nhds_zero_iff {l : Filter α} {f : α -> Real>=0∞} {a : Re
al>=0∞} (ha : a != ∞) (hfa : forall n, f n <= a) : Tendsto (fun n => a - f n) l 
(𝓝 0) ↔ Tendsto (fun n => f n) l (𝓝 a)
参数：ha : a != ∞；hfa : forall n, f n <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_nhds_zero`：∀ {α : Type u_1} {f : Filter α} {u : α → ENNR
eal}, Filter.Tendsto u f (nhds 0) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ≤ ε
· 使用定理 `ENNReal.tendsto_nhds`：∀ {α : Type u_1} {f : Filter α} {u : α → ENNReal} 
{a : ENNReal},   a ≠ ⊤ → (Filter.Tendsto u f (nhds a) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f
, u x ∈ Se…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem tendsto_const_sub_nhds_zero_iff {l : Filter α} {f : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ∞)
    (hfa : ∀ n, f n ≤ a) :
    Tendsto (fun n ↦ a - f n) l (𝓝 0) ↔ Tendsto (fun n ↦ f n) l (𝓝 a) := by
  rw [ENNReal.tendsto_nhds_zero, ENNReal.tendsto_nhds ha]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · filter_upwards [h ε hε] with n hn
    refine ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩
    rw [tsub_le_iff_right] at hn ⊢
    rwa [add_comm]
  · filter_upwards [h ε hε] with n hn
    have hN_left := hn.1
    rw [tsub_le_iff_right] at hN_left ⊢
    rwa [add_comm]
/-
**ENNReal.tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {β : Type u_2} [Nonempty β] [inst : SemilatticeSup β] {f : β → ENNReal} 
{a : ENNReal},   a ≠ ⊤ → (Filter.Tendsto f Filter.atTop (nhds a) ↔ ∀ ε > 0, ∃ N,
 ∀ n ≥ N, f n ∈ Set.Icc (a - ε) (a + ε))
参数：Filter.Tendsto f Filter.atTop (nhds a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ∈ Set.Icc
 (a - ε) (a + ε)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `ENNReal.hasBasis_nhds_of_ne_top`：hasBasis_nhds_of_ne_top (xt : x != ∞) :
 (𝓝 x).HasBasis (0 < ·) (fun ε => Icc (x - ε) (x + ε))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} {a : ℝ≥0∞}
    (ha : a ≠ ∞) : Tendsto f atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ∈ Icc (a - ε) (a + ε) :=
  .trans (atTop_basis.tendsto_iff (hasBasis_nhds_of_ne_top ha)) (by simp only [true_and]; rfl)
/-
**ENNReal.tendsto_atTop_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {β : Type u_2} [Nonempty β] [inst : SemilatticeSup β] {f : β → ENNReal},
   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ ε
参数：nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `ENNReal.nhds_zero_basis_Iic`：nhds_zero_basis_Iic : (𝓝 (0 : Real>=0∞)).Ha
sBasis (fun a : Real>=0∞ => 0 < a) Iic
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem tendsto_atTop_zero [Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} :
    Tendsto f atTop (𝓝 0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ ε :=
  .trans (atTop_basis.tendsto_iff nhds_zero_basis_Iic) (by simp only [true_and]; rfl)
/-
**ENNReal.tendsto_atTop_zero_iff_le_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `ENNRe
al`。
形式化陈述：tendsto_atTop_zero_iff_le_of_antitone {β : Type*} [Nonempty β] [Semilattic
eSup β] {f : β -> Real>=0∞} (hf : Antitone f) : Filter.Tendsto f Filter.atTop (𝓝
 0) ↔ forall ε, 0 < ε -> exists n : β, f n <= ε
参数：hf : Antitone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem tendsto_atTop_zero_iff_le_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β]
    {f : β → ℝ≥0∞} (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ ∀ ε, 0 < ε → ∃ n : β, f n ≤ ε := by
  rw [ENNReal.tendsto_atTop_zero]
  refine ⟨fun h ↦ fun ε hε ↦ ?_, fun h ↦ fun ε hε ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn n le_rfl⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, fun m hm ↦ (hf hm).trans hn⟩
/-
**ENNReal.tendsto_atTop_zero_iff_lt_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `ENNRe
al`。
形式化陈述：tendsto_atTop_zero_iff_lt_of_antitone {β : Type*} [Nonempty β] [Semilattic
eSup β] {f : β -> Real>=0∞} (hf : Antitone f) : Filter.Tendsto f Filter.atTop (𝓝
 0) ↔ forall ε, 0 < ε -> exists n : β, f n < ε
参数：hf : Antitone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_atTop_zero_iff_le_of_antitone`：tendsto_atTop_zero_iff_le
_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β] {f : β -> Real>=0∞} (hf
 : Antitone f) : Filter.Tendsto f F…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `ENNReal.div_pos_iff`：∀ {a b : ENNReal}, 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `ENNReal.div_lt_iff`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ c ≠ ⊤ →
 (c / b < a ↔ c < a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ENNReal.mul_lt_mul_right`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → b < c → a
 * b < a * c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem tendsto_atTop_zero_iff_lt_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β]
    {f : β → ℝ≥0∞} (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ ∀ ε, 0 < ε → ∃ n : β, f n < ε := by
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hf]
  constructor <;> intro h ε hε
  · obtain ⟨n, hn⟩ := h (min 1 (ε / 2))
      (lt_min_iff.mpr ⟨zero_lt_one, (ENNReal.div_pos_iff.mpr ⟨hε.ne', by finiteness⟩)⟩)
    · refine ⟨n, hn.trans_lt ?_⟩
      by_cases hε_top : ε = ∞
      · simp [hε_top]
      refine (min_le_right _ _).trans_lt ?_
      rw [ENNReal.div_lt_iff (Or.inr hε.ne') (Or.inr hε_top)]
      conv_lhs => rw [← mul_one ε]
      gcongr; simp
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn.le⟩
/-
**ENNReal.tendsto_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_sub : forall {a b : Real>=0∞}, (a != ∞ ∨ b != ∞) -> Tendsto (fun p
 : Real>=0∞ × Real>=0∞ => p.1 - p.2) (𝓝 (a, b)) (𝓝 (a - b)) | ∞, ∞, h => by simp
 only [ne_eq, not_true_eq_false, or_self] at h | ∞, (b : Real>=0), _ => by rw [t
op_sub_coe]; rw [tendsto_nhds_top_iff_nnreal] refine fun x => ((lt_mem_nhds <| @
coe_lt_top (b + 1 + x)).prod_nhds (ge_mem_nhds <| coe_lt_coe.2 <| lt_add_one b))
.mono fun y hy => ?_ grw [lt_tsub_iff_left, hy.2] exact hy.1 | (a : Real>=0), ∞,
 _ => by rw [sub_top] refi
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `ENNReal.top_sub_coe`：∀ {r : NNReal}, ⊤ - ↑r = ⊤
· 使用定理 `ENNReal.tendsto_nhds_top_iff_nnreal`：tendsto_nhds_top_iff_nnreal {m : α 
-> Real>=0∞} {f : Filter α} : Tendsto m f (𝓝 ∞) ↔ forall x : Real>=0, forallᶠ a 
in f, ↑x < m a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_nhds`：Filter.Eventually.prod_nhds {p : X -> Prop}
 {q : Y -> Prop} {x : X} {y : Y} (hx : forallᶠ x in 𝓝 x, p x) (hy : forallᶠ y in
 𝓝 y, q y) : fora…
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `ge_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `lt_tsub_iff_left`：lt_tsub_iff_left : a < b - c ↔ c + a < b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
（共 49 条，此处仅展示前 30 条）
-/
theorem tendsto_sub : ∀ {a b : ℝ≥0∞}, (a ≠ ∞ ∨ b ≠ ∞) →
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 - p.2) (𝓝 (a, b)) (𝓝 (a - b))
  | ∞, ∞, h => by simp only [ne_eq, not_true_eq_false, or_self] at h
  | ∞, (b : ℝ≥0), _ => by
    rw [top_sub_coe, tendsto_nhds_top_iff_nnreal]
    refine fun x => ((lt_mem_nhds <| @coe_lt_top (b + 1 + x)).prod_nhds
      (ge_mem_nhds <| coe_lt_coe.2 <| lt_add_one b)).mono fun y hy => ?_
    grw [lt_tsub_iff_left, hy.2]
    exact hy.1
  | (a : ℝ≥0), ∞, _ => by
    rw [sub_top]
    refine (tendsto_pure.2 ?_).mono_right (pure_le_nhds _)
    exact ((gt_mem_nhds <| coe_lt_coe.2 <| lt_add_one a).prod_nhds
      (lt_mem_nhds <| @coe_lt_top (a + 1))).mono fun x hx =>
        tsub_eq_zero_iff_le.2 (hx.1.trans hx.2).le
  | (a : ℝ≥0), (b : ℝ≥0), _ => by
    simp only [nhds_coe_coe, tendsto_map'_iff, ← ENNReal.coe_sub, Function.comp_def, tendsto_coe]
    exact continuous_sub.tendsto (a, b)
/-
**ENNReal.Tendsto.sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Tendsto`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNReal} {a b : ENNReal},   F
ilter.Tendsto ma f (nhds a) →     Filter.Tendsto mb f (nhds b) → a ≠ ⊤ ∨ b ≠ ⊤ →
 Filter.Tendsto (fun a => ma a - mb a) f (nhds (a - b))
参数：nhds a；nhds b；fun a => ma a - mb a；nhds (a - b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_sub`：tendsto_sub : forall {a b : Real>=0∞}, (a != ∞ ∨ b 
!= ∞) -> Tendsto (fun p : Real>=0∞ × Real>=0∞ => p.1 - p.2) (𝓝 (a, b)) (𝓝 (a - b
)) | ∞, ∞…
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
protected theorem Tendsto.sub {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h : a ≠ ∞ ∨ b ≠ ∞) :
    Tendsto (fun a => ma a - mb a) f (𝓝 (a - b)) :=
  show Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 - p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a - b)) from
    Tendsto.comp (ENNReal.tendsto_sub h) (hma.prodMk_nhds hmb)
/-
**ENNReal.tendsto_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → b ≠ 0 ∨ a ≠ ⊤ → Filter.Tendsto (fun p =
> p.1 * p.2) (nhds (a, b)) (nhds (a * b))
参数：fun p => p.1 * p.2；nhds (a, b)；nhds (a * b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_nhds_top_iff_nnreal`：tendsto_nhds_top_iff_nnreal {m : α 
-> Real>=0∞} {f : Filter α} : Tendsto m f (𝓝 ∞) ↔ forall x : Real>=0, forallᶠ a 
in f, ↑x < m a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.Eventually.prod_nhds`：Filter.Eventually.prod_nhds {p : X -> Prop}
 {q : Y -> Prop} {x : X} {y : Y} (hx : forallᶠ x in 𝓝 x, p x) (hy : forallᶠ y in
 𝓝 y, q y) : fora…
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.div_lt_top`：div_lt_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y !=
 0) : x / y < ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.div_mul_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → b / a * a = b
· 使用定理 `ENNReal.mul_lt_mul`：mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 38 条，此处仅展示前 30 条）
-/
protected theorem tendsto_mul (ha : a ≠ 0 ∨ b ≠ ∞) (hb : b ≠ 0 ∨ a ≠ ∞) :
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) := by
  have ht : ∀ b : ℝ≥0∞, b ≠ 0 →
      Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 (∞, b)) (𝓝 ∞) := fun b hb => by
    refine tendsto_nhds_top_iff_nnreal.2 fun n => ?_
    rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩
    have : ∀ᶠ c : ℝ≥0∞ × ℝ≥0∞ in 𝓝 (∞, b), ↑n / ↑ε < c.1 ∧ ↑ε < c.2 :=
      (lt_mem_nhds <| div_lt_top coe_ne_top hε.ne').prod_nhds (lt_mem_nhds hεb)
    refine this.mono fun c hc => ?_
    exact (ENNReal.div_mul_cancel hε.ne' coe_ne_top).symm.trans_lt (mul_lt_mul hc.1 hc.2)
  induction a with
  | top => simp only [ne_eq, or_false, not_true_eq_false] at hb; simp [ht b hb, top_mul hb]
  | coe a =>
    induction b with
    | top =>
      simp only [ne_eq, or_false, not_true_eq_false] at ha
      simpa [Function.comp_def, mul_comm, mul_top ha]
        using (ht a ha).comp (continuous_swap.tendsto (ofNNReal a, ∞))
    | coe b =>
      simp only [nhds_coe_coe, ← coe_mul, tendsto_coe, tendsto_map'_iff, Function.comp_def,
        tendsto_mul]
/-
**ENNReal.Tendsto.mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Tendsto`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNReal} {a b : ENNReal},   F
ilter.Tendsto ma f (nhds a) →     a ≠ 0 ∨ b ≠ ⊤ →       Filter.Tendsto mb f (nhd
s b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Tendsto (fun a => ma a * mb a) f (nhds (a * b))
参数：nhds a；nhds b；fun a => ma a * mb a；nhds (a * b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_mul`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → b ≠ 0 ∨ a ≠ ⊤ → 
Filter.Tendsto (fun p => p.1 * p.2) (nhds (a, b)) (nhds (a * b))
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
protected theorem Tendsto.mul {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ∞) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ 0 ∨ a ≠ ∞) : Tendsto (fun a => ma a * mb a) f (𝓝 (a * b)) :=
  show Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a * b)) from
    Tendsto.comp (ENNReal.tendsto_mul ha hb) (hma.prodMk_nhds hmb)
/-
**ENNReal._root_.ContinuousOn.ennreal_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousOn.ennreal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₁ : ∀ x ∈ s, f x ≠ 0 ∨ g x ≠ ∞)
    (h₂ : ∀ x ∈ s, g x ≠ 0 ∨ f x ≠ ∞) : ContinuousOn (fun x => f x * g x) s := fun x hx =>
  ENNReal.Tendsto.mul (hf x hx) (h₁ x hx) (hg x hx) (h₂ x hx)
/-
**ENNReal._root_.Continuous.ennreal_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.ennreal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} (hf : Continuous f)
    (hg : Continuous g) (h₁ : ∀ x, f x ≠ 0 ∨ g x ≠ ∞) (h₂ : ∀ x, g x ≠ 0 ∨ f x ≠ ∞) :
    Continuous fun x => f x * g x :=
  continuous_iff_continuousAt.2 fun x =>
    ENNReal.Tendsto.mul hf.continuousAt (h₁ x) hg.continuousAt (h₂ x)
/-
**ENNReal.Tendsto.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Tendsto`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {m : α → ENNReal} {a b : ENNReal},   Filte
r.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Tendsto (fun b => a * m b) f (nh
ds (a * b))
参数：nhds b；fun b => a * m b；nhds (a * b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ENNReal.Tendsto.mul`：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNRea
l} {a b : ENNReal},   Filter.Tendsto ma f (nhds a) →     a ≠ 0 ∨ b ≠ ⊤ →       F
ilter.Ten…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
protected theorem Tendsto.const_mul {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ∞) : Tendsto (fun b => a * m b) f (𝓝 (a * b)) :=
  by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds]) fun ha : a ≠ 0 =>
    ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb
/-
**ENNReal.Tendsto.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Tendsto`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {m : α → ENNReal} {a b : ENNReal},   Filte
r.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊤ → Filter.Tendsto (fun x => m x * b) f (nh
ds (a * b))
参数：nhds a；fun x => m x * b；nhds (a * b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
-/
protected theorem Tendsto.mul_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ∞) : Tendsto (fun x => m x * b) f (𝓝 (a * b)) := by
  simpa only [mul_comm] using ENNReal.Tendsto.const_mul hm ha
/-
**ENNReal.tendsto_finsetProd_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_finsetProd_of_ne_top {ι : Type*} {f : ι -> α -> Real>=0∞} {x : Fil
ter α} {a : ι -> Real>=0∞} (s : Finset ι) (h : forall i in s, Tendsto (f i) x (𝓝
 (a i))) (h' : forall i in s, a i != ∞) : Tendsto (fun b => ∏ c in s, f c b) x (
𝓝 (∏ c in s, a c))
参数：s : Finset ι；h : forall i in s, Tendsto (f i) x (𝓝 (a i))；h' : forall i in s,
 a i != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `ENNReal.Tendsto.mul`：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNRea
l} {a b : ENNReal},   Filter.Tendsto ma f (nhds a) →     a ≠ 0 ∨ b ≠ ⊤ →       F
ilter.Ten…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用引理 `ENNReal.prod_ne_top`：prod_ne_top (h : forall a in s, f a != ∞) : ∏ a in 
s, f a != ∞
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem tendsto_finsetProd_of_ne_top {ι : Type*} {f : ι → α → ℝ≥0∞} {x : Filter α} {a : ι → ℝ≥0∞}
    (s : Finset ι) (h : ∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) (h' : ∀ i ∈ s, a i ≠ ∞) :
    Tendsto (fun b => ∏ c ∈ s, f c b) x (𝓝 (∏ c ∈ s, a c)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [tendsto_const_nhds]
  | insert _ _ has IH =>
    simp only [Finset.prod_insert has]
    apply Tendsto.mul (h _ (Finset.mem_insert_self _ _))
    · right
      exact prod_ne_top fun i hi => h' _ (Finset.mem_insert_of_mem hi)
    · exact IH (fun i hi => h _ (Finset.mem_insert_of_mem hi)) fun i hi =>
        h' _ (Finset.mem_insert_of_mem hi)
    · exact Or.inr (h' _ (Finset.mem_insert_self _ _))

@[deprecated (since := "2026-04-08")]
alias tendsto_finset_prod_of_ne_top := tendsto_finsetProd_of_ne_top
/-
**ENNReal.continuousAt_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ ⊤ ∨ b ≠ 0 → ContinuousAt (fun x => a * x) b
参数：fun x => a * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
protected theorem continuousAt_const_mul {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ 0) :
    ContinuousAt (a * ·) b :=
  Tendsto.const_mul tendsto_id h.symm
/-
**ENNReal.continuousAt_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ ⊤ ∨ b ≠ 0 → ContinuousAt (fun x => x * a) b
参数：fun x => x * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.Tendsto.mul_const`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊤ → Filter.Ten
dsto (fun x => …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
protected theorem continuousAt_mul_const {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ 0) :
    ContinuousAt (fun x => x * a) b :=
  Tendsto.mul_const tendsto_id h.symm

@[fun_prop]
/-
**ENNReal.continuous_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ ⊤ → Continuous fun x => a * x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ENNReal.continuousAt_const_mul`：∀ {a b : ENNReal}, a ≠ ⊤ ∨ b ≠ 0 → Conti
nuousAt (fun x => a * x) b
-/
protected theorem continuous_const_mul {a : ℝ≥0∞} (ha : a ≠ ∞) : Continuous (a * ·) :=
  continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_const_mul (Or.inl ha)

@[fun_prop]
/-
**ENNReal.continuous_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ ⊤ → Continuous fun x => x * a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ENNReal.continuousAt_mul_const`：∀ {a b : ENNReal}, a ≠ ⊤ ∨ b ≠ 0 → Conti
nuousAt (fun x => x * a) b
-/
protected theorem continuous_mul_const {a : ℝ≥0∞} (ha : a ≠ ∞) : Continuous fun x => x * a :=
  continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_mul_const (Or.inl ha)

@[fun_prop]
/-
**ENNReal.continuous_div_const** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (c : ENNReal), c ≠ 0 → Continuous fun x => x / c
参数：c : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.continuous_mul_const`：∀ {a : ENNReal}, a ≠ ⊤ → Continuous fun x 
=> x * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
-/
protected theorem continuous_div_const (c : ℝ≥0∞) (c_ne_zero : c ≠ 0) :
    Continuous fun x : ℝ≥0∞ => x / c :=
  ENNReal.continuous_mul_const <| ENNReal.inv_ne_top.2 c_ne_zero

@[continuity, fun_prop]
/-
**ENNReal.continuous_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ), Continuous fun a => a ^ n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ENNReal.Tendsto.mul`：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNRea
l} {a b : ENNReal},   Filter.Tendsto ma f (nhds a) →     a ≠ 0 ∨ b ≠ ⊤ →       F
ilter.Ten…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
protected theorem continuous_pow (n : ℕ) : Continuous fun a : ℝ≥0∞ => a ^ n := by
  induction n with
  | zero => simp [continuous_const]
  | succ n IH =>
    simp_rw [pow_add, pow_one, continuous_iff_continuousAt]
    intro x
    refine ENNReal.Tendsto.mul (IH.tendsto _) ?_ tendsto_id ?_ <;> by_cases H : x = 0
    · simp only [H, zero_ne_top, Ne, or_true, not_false_iff]
    · exact Or.inl fun h => H (eq_zero_of_pow_eq_zero h)
    · simp only [H, pow_eq_top_iff, zero_ne_top, false_or, not_true, Ne,
        not_false_iff, false_and]
    · simp only [H, true_or, Ne, not_false_iff]
/-
**ENNReal.continuousOn_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuousOn_sub : ContinuousOn (fun p : Real>=0∞ × Real>=0∞ => p.fst - p.
snd) { p : Real>=0∞ × Real>=0∞ | p != ⟨∞, ∞⟩ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l
· 使用定理 `ENNReal.tendsto_sub`：tendsto_sub : forall {a b : Real>=0∞}, (a != ∞ ∨ b 
!= ∞) -> Tendsto (fun p : Real>=0∞ × Real>=0∞ => p.1 - p.2) (𝓝 (a, b)) (𝓝 (a - b
)) | ∞, ∞…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
-/
theorem continuousOn_sub :
    ContinuousOn (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) { p : ℝ≥0∞ × ℝ≥0∞ | p ≠ ⟨∞, ∞⟩ } := by
  rw [ContinuousOn]
  rintro ⟨x, y⟩ hp
  simp only [Ne, Set.mem_ofPred_eq, Prod.mk_inj] at hp
  exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_sub (not_and_or.mp hp))
/-
**ENNReal.continuous_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuous_sub_left {a : Real>=0∞} (a_ne_top : a != ∞) : Continuous (a - ·
)
参数：a_ne_top : a != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `ENNReal.continuousOn_sub`：continuousOn_sub : ContinuousOn (fun p : Real>
=0∞ × Real>=0∞ => p.fst - p.snd) { p : Real>=0∞ × Real>=0∞ | p != ⟨∞, ∞⟩ }
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem continuous_sub_left {a : ℝ≥0∞} (a_ne_top : a ≠ ∞) : Continuous (a - ·) := by
  change Continuous (Function.uncurry Sub.sub ∘ (a, ·))
  refine continuousOn_sub.comp_continuous (.prodMk_right a) fun x => ?_
  simp only [a_ne_top, Ne, mem_ofPred_eq, Prod.mk_inj, false_and, not_false_iff]
/-
**ENNReal.continuous_nnreal_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuous_nnreal_sub {a : Real>=0} : Continuous fun x : Real>=0∞ => (a : 
Real>=0∞) - x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.continuous_sub_left`：continuous_sub_left {a : Real>=0∞} (a_ne_to
p : a != ∞) : Continuous (a - ·)
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem continuous_nnreal_sub {a : ℝ≥0} : Continuous fun x : ℝ≥0∞ => (a : ℝ≥0∞) - x :=
  continuous_sub_left coe_ne_top
/-
**ENNReal.continuousOn_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuousOn_sub_left (a : Real>=0∞) : ContinuousOn (a - ·) { x : Real>=0∞
 | x != ∞ }
参数：a : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `ENNReal.continuousOn_sub`：continuousOn_sub : ContinuousOn (fun p : Real>
=0∞ × Real>=0∞ => p.fst - p.snd) { p : Real>=0∞ × Real>=0∞ | p != ⟨∞, ∞⟩ }
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `ENNReal.none_eq_top`：none = ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem continuousOn_sub_left (a : ℝ≥0∞) : ContinuousOn (a - ·) { x : ℝ≥0∞ | x ≠ ∞ } := by
  rw [show (fun x => a - x) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨a, x⟩ by rfl]
  apply continuousOn_sub.comp (by fun_prop)
  rintro _ h (_ | _)
  exact h none_eq_top
/-
**ENNReal.continuous_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuous_sub_right (a : Real>=0∞) : Continuous fun x : Real>=0∞ => x - a
参数：a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `ENNReal.continuousOn_sub`：continuousOn_sub : ContinuousOn (fun p : Real>
=0∞ × Real>=0∞ => p.fst - p.snd) { p : Real>=0∞ × Real>=0∞ | p != ⟨∞, ∞⟩ }
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem continuous_sub_right (a : ℝ≥0∞) : Continuous fun x : ℝ≥0∞ => x - a := by
  by_cases a_infty : a = ∞
  · simp [a_infty, continuous_const, tsub_eq_zero_of_le]
  · rw [show (fun x => x - a) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨x, a⟩ by rfl]
    apply continuousOn_sub.comp_continuous (by fun_prop)
    intro x
    simp only [a_infty, Ne, mem_ofPred_eq, Prod.mk_inj, and_false, not_false_iff]
/-
**ENNReal.Tendsto.pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Tendsto`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {m : α → ENNReal} {a : ENNReal} {n : ℕ},  
 Filter.Tendsto m f (nhds a) → Filter.Tendsto (fun x => m x ^ n) f (nhds (a ^ n)
)
参数：nhds a；fun x => m x ^ n；nhds (a ^ n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_pow`：∀ (n : ℕ), Continuous fun a => a ^ n
-/
protected theorem Tendsto.pow {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} {n : ℕ}
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ n) f (𝓝 (a ^ n)) :=
  ((ENNReal.continuous_pow n).tendsto a).comp hm
/-
**ENNReal.le_of_forall_lt_one_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_of_forall_lt_one_mul_le {x y : Real>=0∞} (h : forall a < 1, a * x <= y)
 : x <= y
参数：h : forall a < 1, a * x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `ENNReal.continuousAt_mul_const`：∀ {a b : ENNReal}, a ≠ ⊤ ∨ b ≠ 0 → Conti
nuousAt (fun x => x * a) b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.nhdsLT_neBot`：nhdsLT_neBot [NeZero x] : (𝓝[<] x).NeBot
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0∞} (h : ∀ a < 1, a * x ≤ y) : x ≤ y := by
  have : Tendsto (· * x) (𝓝[<] 1) (𝓝 (1 * x)) :=
    (ENNReal.continuousAt_mul_const (Or.inr one_ne_zero)).mono_left inf_le_left
  rw [one_mul] at this
  exact le_of_tendsto this (eventually_nhdsWithin_iff.2 <| Eventually.of_forall h)
/-
**ENNReal.inv_limsup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_limsup {ι : Sort _} {x : ι -> Real>=0∞} {l : Filter ι} : (limsup x l)⁻
¹ = liminf (fun i => (x i)⁻¹) l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.limsup_apply`：OrderIso.limsup_apply {γ} [ConditionallyCompleteL
attice β] [ConditionallyCompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o
 γ) (hu : f…
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
-/
theorem inv_limsup {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (limsup x l)⁻¹ = liminf (fun i => (x i)⁻¹) l :=
  OrderIso.invENNReal.limsup_apply
/-
**ENNReal.inv_liminf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_liminf {ι : Sort _} {x : ι -> Real>=0∞} {l : Filter ι} : (liminf x l)⁻
¹ = limsup (fun i => (x i)⁻¹) l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.liminf_apply`：OrderIso.liminf_apply {γ} [ConditionallyCompleteL
attice β] [ConditionallyCompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o
 γ) (hu : f…
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
-/
theorem inv_liminf {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (liminf x l)⁻¹ = limsup (fun i => (x i)⁻¹) l :=
  OrderIso.invENNReal.liminf_apply

@[fun_prop]
/-
**ENNReal.continuous_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℤ), Continuous fun x => x ^ n
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `ENNReal.continuous_pow`：∀ (n : ℕ), Continuous fun a => a ^ n
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Continuous.fun_inv`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {f : 
X → G}, …
· 使用定理 `ENNReal.instContinuousInv`：ContinuousInv ENNReal
-/
protected theorem continuous_zpow : ∀ n : ℤ, Continuous (· ^ n : ℝ≥0∞ → ℝ≥0∞)
  | (n : ℕ) => mod_cast ENNReal.continuous_pow n
  | .negSucc n => by simpa using (ENNReal.continuous_pow _).fun_inv

@[deprecated (since := "2026-01-15")] protected alias tendsto_inv_iff := tendsto_inv_iff
/-
**ENNReal.Tendsto.div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Tendsto`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNReal} {a b : ENNReal},   F
ilter.Tendsto ma f (nhds a) →     a ≠ 0 ∨ b ≠ 0 →       Filter.Tendsto mb f (nhd
s b) → b ≠ ⊤ ∨ a ≠ ⊤ → Filter.Tendsto (fun a => ma a / mb a) f (nhds (a / b))
参数：nhds a；nhds b；fun a => ma a / mb a；nhds (a / b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.Tendsto.mul`：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNRea
l} {a b : ENNReal},   Filter.Tendsto ma f (nhds a) →     a ≠ 0 ∨ b ≠ ⊤ →       F
ilter.Ten…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_inv_iff`：tendsto_inv_iff {l : Filter α} {m : α -> G} {a : G} : T
endsto (fun x => (m x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a)
· 使用定理 `ENNReal.instContinuousInv`：ContinuousInv ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
protected theorem Tendsto.div {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ ∞ ∨ a ≠ ∞) : Tendsto (fun a => ma a / mb a) f (𝓝 (a / b)) := by
  apply Tendsto.mul hma _ (tendsto_inv_iff.2 hmb) _ <;> simp [ha, hb]
/-
**ENNReal.Tendsto.const_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Tendsto`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {m : α → ENNReal} {a b : ENNReal},   Filte
r.Tendsto m f (nhds b) → b ≠ ⊤ ∨ a ≠ ⊤ → Filter.Tendsto (fun b => a / m b) f (nh
ds (a / b))
参数：nhds b；fun b => a / m b；nhds (a / b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_inv_iff`：tendsto_inv_iff {l : Filter α} {m : α -> G} {a : G} : T
endsto (fun x => (m x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a)
· 使用定理 `ENNReal.instContinuousInv`：ContinuousInv ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
protected theorem Tendsto.const_div {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ ∞ ∨ a ≠ ∞) : Tendsto (fun b => a / m b) f (𝓝 (a / b)) := by
  apply Tendsto.const_mul (tendsto_inv_iff.2 hm)
  simp [hb]
/-
**ENNReal.Tendsto.div_const** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Tendsto`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {m : α → ENNReal} {a b : ENNReal},   Filte
r.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ 0 → Filter.Tendsto (fun x => m x / b) f (nh
ds (a / b))
参数：nhds a；fun x => m x / b；nhds (a / b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.Tendsto.mul_const`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊤ → Filter.Ten
dsto (fun x => …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
protected theorem Tendsto.div_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) : Tendsto (fun x => m x / b) f (𝓝 (a / b)) := by
  apply Tendsto.mul_const hm
  simp [ha]
/-
**ENNReal.tendsto_inv_nat_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：Filter.Tendsto (fun n => (↑n)⁻¹) Filter.atTop (nhds 0)
参数：fun n => (↑n)⁻¹；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_inv_iff`：tendsto_inv_iff {l : Filter α} {m : α -> G} {a : G} : T
endsto (fun x => (m x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a)
· 使用定理 `ENNReal.instContinuousInv`：ContinuousInv ENNReal
· 使用定理 `ENNReal.tendsto_nat_nhds_top`：tendsto_nat_nhds_top : Tendsto (fun n : Na
t => ↑n) atTop (𝓝 ∞)
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
-/
protected theorem tendsto_inv_nat_nhds_zero : Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
  ENNReal.inv_top ▸ tendsto_inv_iff.2 tendsto_nat_nhds_top
/-
**ENNReal.tendsto_coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal} {b : ENNReal}, Filter.Tendsto (fun b => ↑r - b) (nhds b) (n
hds (↑r - b))
参数：fun b => ↑r - b；nhds b；nhds (↑r - b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_nnreal_sub`：continuous_nnreal_sub {a : Real>=0} : Con
tinuous fun x : Real>=0∞ => (a : Real>=0∞) - x
-/
protected theorem tendsto_coe_sub {b : ℝ≥0∞} :
    Tendsto (fun b : ℝ≥0∞ => ↑r - b) (𝓝 b) (𝓝 (↑r - b)) :=
  continuous_nnreal_sub.tendsto _
/-
**ENNReal.exists_countable_dense_no_zero_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`
。
形式化陈述：exists_countable_dense_no_zero_top : exists s : Set Real>=0∞, s.Countable 
∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_countable_dense_no_bot_top`：exists_countable_dense_no_bot_top [Se
parableSpace α] [Nontrivial α] : exists s : Set α, s.Countable ∧ Dense s ∧ (fora
ll x, IsBot x -> x ∉ s)…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_countable_dense_no_zero_top :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s := by
  obtain ⟨s, s_count, s_dense, hs⟩ :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∉ s) ∧ ∀ x, IsTop x → x ∉ s :=
    exists_countable_dense_no_bot_top ℝ≥0∞
  exact ⟨s, s_count, s_dense, fun h => hs.1 0 (by simp) h, fun h => hs.2 ∞ (by simp) h⟩

end TopologicalSpace

section Liminf

/-
**ENNReal.exists_frequently_lt_of_liminf_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNRe
al`。
形式化陈述：exists_frequently_lt_of_liminf_ne_top {ι : Type*} {l : Filter ι} {x : ι ->
 Real} (hx : liminf (fun n => (Real.nnabs (x n) : Real>=0∞)) l != ∞) : exists R,
 existsᶠ n in l, x n < R
参数：hx : liminf (fun n => (Real.nnabs (x n) : Real>=0∞)) l != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ENNReal.eq_top_of_forall_nnreal_le`：eq_top_of_forall_nnreal_le {x : Real
>=0∞} (h : forall r : Real>=0, ↑r <= x) : x = ∞
· 使用定理 `Filter.le_limsInf_of_le`：le_limsInf_of_le {f : Filter α} {a} (hf : f.IsC
obounded (· >= ·)
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem exists_frequently_lt_of_liminf_ne_top {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => (Real.nnabs (x n) : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, x n < R := by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h r] with i hi using hi.trans (le_abs_self (x i))
/-
**ENNReal.exists_frequently_lt_of_liminf_ne_top'** 是 Mathlib 中的一个定理，位于命名空间 `ENNR
eal`。
形式化陈述：exists_frequently_lt_of_liminf_ne_top' {ι : Type*} {l : Filter ι} {x : ι -
> Real} (hx : liminf (fun n => (Real.nnabs (x n) : Real>=0∞)) l != ∞) : exists R
, existsᶠ n in l, R < x n
参数：hx : liminf (fun n => (Real.nnabs (x n) : Real>=0∞)) l != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ENNReal.eq_top_of_forall_nnreal_le`：eq_top_of_forall_nnreal_le {x : Real
>=0∞} (h : forall r : Real>=0, ↑r <= x) : x = ∞
· 使用定理 `Filter.le_limsInf_of_le`：le_limsInf_of_le {f : Filter α} {a} (hf : f.IsC
obounded (· >= ·)
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, a ≤ -b ↔ b ≤ -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a
 : α), -a ≤ |a|
-/
theorem exists_frequently_lt_of_liminf_ne_top' {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => (Real.nnabs (x n) : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, R < x n := by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h (-r)] with i hi using (le_neg.1 hi).trans (neg_le_abs _)
/-
**ENNReal.exists_upcrossings_of_not_bounded_under** 是 Mathlib 中的一个定理，位于命名空间 `ENN
Real`。
形式化陈述：exists_upcrossings_of_not_bounded_under {ι : Type*} {l : Filter ι} {x : ι 
-> Real} (hf : liminf (fun i => (Real.nnabs (x i) : Real>=0∞)) l != ∞) (hbdd : ¬
IsBoundedUnder (· <= ·) l fun i => |x i|) : exists a b : Rat, a < b ∧ (existsᶠ i
 in l, x i < a) ∧ existsᶠ i in l, ↑b < x i
参数：hf : liminf (fun i => (Real.nnabs (x i) : Real>=0∞)) l != ∞；hbdd : ¬IsBounded
Under (· <= ·) l fun i => |x i|。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Filter.isBoundedUnder_le_abs`：isBoundedUnder_le_abs [AddCommGroup α] [Li
nearOrder α] [IsOrderedAddMonoid α] {f : Filter β} {u : β -> α} : (f.IsBoundedUn
der (· <= ·) fun a…
· 使用定理 `ENNReal.exists_frequently_lt_of_liminf_ne_top`：exists_frequently_lt_of_l
iminf_ne_top {ι : Type*} {l : Filter ι} {x : ι -> Real} (hx : liminf (fun n => (
Real.nnabs (x n) : Real>=0∞)) l != …
· 使用定理 `exists_rat_gt`：exists_rat_gt (x : K) : exists q : Rat, x < q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_add_iff_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 :
 LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b : α},   a < a + b ↔
 0 < b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.exists_frequently_lt_of_liminf_ne_top'`：exists_frequently_lt_of_
liminf_ne_top' {ι : Type*} {l : Filter ι} {x : ι -> Real} (hx : liminf (fun n =>
 (Real.nnabs (x n) : Real>=0∞)) l !=…
· 使用定理 `exists_rat_lt`：exists_rat_lt (x : K) : exists q : Rat, (q : K) < x
· 使用定理 `sub_lt_self_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] (a : α) {b : α}, a - b < a ↔ 0 < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem exists_upcrossings_of_not_bounded_under {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hf : liminf (fun i => (Real.nnabs (x i) : ℝ≥0∞)) l ≠ ∞)
    (hbdd : ¬IsBoundedUnder (· ≤ ·) l fun i => |x i|) :
    ∃ a b : ℚ, a < b ∧ (∃ᶠ i in l, x i < a) ∧ ∃ᶠ i in l, ↑b < x i := by
  rw [isBoundedUnder_le_abs, not_and_or] at hbdd
  obtain hbdd | hbdd := hbdd
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top hf
    obtain ⟨q, hq⟩ := exists_rat_gt R
    refine ⟨q, q + 1, (lt_add_iff_pos_right _).2 zero_lt_one, ?_, ?_⟩
    · refine fun hcon => hR ?_
      filter_upwards [hcon] with x hx using not_lt.2 (lt_of_lt_of_le hq (not_lt.1 hx)).le
    · simp only [IsBoundedUnder, IsBounded, eventually_map, not_exists] at hbdd
      refine fun hcon => hbdd ↑(q + 1) ?_
      filter_upwards [hcon] with x hx using not_lt.1 hx
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top' hf
    obtain ⟨q, hq⟩ := exists_rat_lt R
    refine ⟨q - 1, q, (sub_lt_self_iff _).2 zero_lt_one, ?_, ?_⟩
    · simp only [IsBoundedUnder, IsBounded, eventually_map, not_exists] at hbdd
      refine fun hcon => hbdd ↑(q - 1) ?_
      filter_upwards [hcon] with x hx using not_lt.1 hx
    · refine fun hcon => hR ?_
      filter_upwards [hcon] with x hx using not_lt.2 ((not_lt.1 hx).trans hq.le)

end Liminf

/-
**ENNReal.tendsto_toReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_toReal_iff {ι} {fi : Filter ι} {f : ι -> Real>=0∞} (hf : forall i,
 f i != ∞) {x : Real>=0∞} (hx : x != ∞) : Tendsto (fun n => (f n).toReal) fi (𝓝 
x.toReal) ↔ Tendsto f fi (𝓝 x)
参数：hf : forall i, f i != ∞；hx : x != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_toReal_iff {ι} {fi : Filter ι} {f : ι → ℝ≥0∞} (hf : ∀ i, f i ≠ ∞) {x : ℝ≥0∞}
    (hx : x ≠ ∞) : Tendsto (fun n => (f n).toReal) fi (𝓝 x.toReal) ↔ Tendsto f fi (𝓝 x) := by
  lift f to ι → ℝ≥0 using hf
  lift x to ℝ≥0 using hx
  simp [tendsto_coe]
/-
**ENNReal.tendsto_toReal_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_toReal_zero_iff {ι} {fi : Filter ι} {f : ι -> Real>=0∞} (hf : fora
ll i, f i != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用定理 `ENNReal.tendsto_toReal_iff`：tendsto_toReal_iff {ι} {fi : Filter ι} {f : 
ι -> Real>=0∞} (hf : forall i, f i != ∞) {x : Real>=0∞} (hx : x != ∞) : Tendsto 
(fun n => (f n).…
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_toReal_zero_iff {ι} {fi : Filter ι} {f : ι → ℝ≥0∞}
    (hf : ∀ i, f i ≠ ∞ := by finiteness) :
    Tendsto (fun n ↦ (f n).toReal) fi (𝓝 0) ↔ Tendsto f fi (𝓝 0) := by
  rw [← ENNReal.toReal_zero, tendsto_toReal_iff hf ENNReal.zero_ne_top]

end ENNReal

section

variable [EMetricSpace β]

open ENNReal Filter

/-- In an emetric ball, the distance between points is everywhere finite -/
/-
**edist_ne_top_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_ne_top_of_mem_ball {a : β} {r : Real>=0∞} (x y : eball a r) : edist 
x.1 y.1 != ∞
参数：x y : eball a r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `edist_triangle_left`：edist_triangle_left (x y z : α) : edist x y <= edis
t z x + edist z y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `ENNReal.add_lt_add`：∀ {a b c d : ENNReal}, a < c → b < d → a + b < c + d
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
In an emetric ball, the distance between points is everywhere finite
-/
theorem edist_ne_top_of_mem_ball {a : β} {r : ℝ≥0∞} (x y : eball a r) : edist x.1 y.1 ≠ ∞ :=
  ne_of_lt <|
    calc
      edist x y ≤ edist a x + edist a y := edist_triangle_left x.1 y.1 a
      _ < r + r := by rw [edist_comm a x, edist_comm a y]; exact ENNReal.add_lt_add x.2 y.2
      _ ≤ ∞ := le_top

/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
@[instance_reducible]
/-
**metricSpaceEMetricBall** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：metricSpaceEMetricBall (a : β) (r : Real>=0∞) : MetricSpace (eball a r)
参数：a : β；r : Real>=0∞。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `edist_ne_top_of_mem_ball`：edist_ne_top_of_mem_ball {a : β} {r : Real>=0∞
} (x y : eball a r) : edist x.1 y.1 != ∞

--- 原说明 ---
Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite.
-/
def metricSpaceEMetricBall (a : β) (r : ℝ≥0∞) : MetricSpace (eball a r) :=
  EMetricSpace.toMetricSpace edist_ne_top_of_mem_ball
/-
**nhds_eq_nhds_emetric_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_eq_nhds_emetric_ball (a x : β) (r : Real>=0∞) (h : x in eball a r) : 
𝓝 x = map ((↑) : eball a r -> β) (𝓝 ⟨x, h⟩)
参数：a x : β；r : Real>=0∞；h : x in eball a r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_nhds_subtype_coe_eq_nhds`：map_nhds_subtype_coe_eq_nhds {x : X} (hx :
 p x) (h : forallᶠ x in 𝓝 x, p x) : map ((↑) : Subtype p -> X) (𝓝 ⟨x, hx⟩) = 𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_eball`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α
} {ε : ENNReal}, IsOpen (Metric.eball x ε)
-/
theorem nhds_eq_nhds_emetric_ball (a x : β) (r : ℝ≥0∞) (h : x ∈ eball a r) :
    𝓝 x = map ((↑) : eball a r → β) (𝓝 ⟨x, h⟩) :=
  (map_nhds_subtype_coe_eq_nhds _ <| isOpen_eball.mem_nhds h).symm

end

section

variable [PseudoEMetricSpace α]

open EMetric

/-
**tendsto_iff_edist_tendsto_0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_edist_tendsto_0 {l : Filter β} {f : β -> α} {y : α} : Tendsto 
f l (𝓝 y) ↔ Tendsto (fun x => edist (f x) y) l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_eball`：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real
>=0∞ => 0 < ε) (eball x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `forall_prop_of_false`：∀ {p : Prop} {q : p → Prop}, ¬p → ((∀ (h' : p), q 
h') ↔ True)
· 使用定理 `ENNReal.not_lt_zero`：not_lt_zero : ¬a < 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_edist_tendsto_0 {l : Filter β} {f : β → α} {y : α} :
    Tendsto f l (𝓝 y) ↔ Tendsto (fun x => edist (f x) y) l (𝓝 0) := by
  simp only [Metric.nhds_basis_eball.tendsto_right_iff, Metric.mem_eball,
    @tendsto_order ℝ≥0∞ β _ _, forall_prop_of_false ENNReal.not_lt_zero, forall_const, true_and]

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
/-
**EMetric.cauchySeq_iff_le_tendsto_0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EMetric.cauchySeq_iff_le_tendsto_0 [Nonempty β] [SemilatticeSup β] {s : β 
-> α} : CauchySeq s ↔ exists b : β -> Real>=0∞, (forall n m N : β, N <= n -> N <
= m -> edist (s n) (s m) <= b N) ∧ Tendsto b atTop (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `EMetric.cauchySeq_iff`：cauchySeq_iff [Nonempty β] [SemilatticeSup β] {u 
: β -> α} : CauchySeq u ↔ forall ε > 0, exists N, forall m, N <= m -> forall n, 
N <= n -> e…
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_nhds_zero`：∀ {α : Type u_1} {f : Filter α} {u : α → ENNR
eal}, Filter.Tendsto u f (nhds 0) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ≤ ε
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α

--- 原说明 ---
Yet another metric characterization of Cauchy sequences on integers. This one is
 often the
most efficient.
-/
theorem EMetric.cauchySeq_iff_le_tendsto_0 [Nonempty β] [SemilatticeSup β] {s : β → α} :
    CauchySeq s ↔ ∃ b : β → ℝ≥0∞, (∀ n m N : β, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N) ∧
      Tendsto b atTop (𝓝 0) := EMetric.cauchySeq_iff.trans <| by
  constructor
  · intro hs
    /- `s` is Cauchy sequence. Let `b n` be the diameter of the set `s '' Set.Ici n`. -/
    refine ⟨fun N => Metric.ediam (s '' Ici N), fun n m N hn hm => ?_, ?_⟩
    -- Prove that it bounds the distances of points in the Cauchy sequence
    · exact Metric.edist_le_ediam_of_mem (mem_image_of_mem _ hn) (mem_image_of_mem _ hm)
    -- Prove that it tends to `0`, by using the Cauchy property of `s`
    · refine ENNReal.tendsto_nhds_zero.2 fun ε ε0 => ?_
      rcases hs ε ε0 with ⟨N, hN⟩
      refine (eventually_ge_atTop N).mono fun n hn => Metric.ediam_le ?_
      rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
      exact (hN _ (hn.trans hk) _ (hn.trans hl)).le
  · rintro ⟨b, ⟨b_bound, b_lim⟩⟩ ε εpos
    have : ∀ᶠ n in atTop, b n < ε := b_lim.eventually (gt_mem_nhds εpos)
    rcases this.exists with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    calc edist (s m) (s n) ≤ b N := b_bound m n N hm hn
    _ < ε := hN
/-
**continuous_of_le_add_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_le_add_edist {f : α -> Real>=0∞} (C : Real>=0∞) (hC : C != ∞
) (h : forall x y, f x <= f y + C * edist x y) : Continuous f
参数：C : Real>=0∞；hC : C != ∞；h : forall x y, f x <= f y + C * edist x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ENNReal.tendsto_nhds_of_Icc`：∀ {α : Type u_1} {f : Filter α} {u : α → EN
NReal} {a : ENNReal},   (∀ ε > 0, ∀ᶠ (x : α) in f, u x ∈ Set.Icc (a - ε) (a + ε)
) → Filter.Tendst…
· 使用定理 `ENNReal.exists_nnreal_pos_mul_lt`：exists_nnreal_pos_mul_lt (ha : a != ∞)
 (hb : b != 0) : exists n > 0, ↑(n : Real>=0) * a < b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Metric.closedEBall_mem_nhds`：closedEBall_mem_nhds (x : α) {ε : Real>=0∞}
 (ε0 : 0 < ε) : closedEBall x ε in 𝓝 x
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closedEBall'`：mem_closedEBall' : y in closedEBall x ε ↔ edist
 x y <= ε
· 使用定理 `Metric.mem_closedEBall`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x 
y : α} {ε : ENNReal}, y ∈ Metric.closedEBall x ε ↔ edist y x ≤ ε
-/
theorem continuous_of_le_add_edist {f : α → ℝ≥0∞} (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ x y, f x ≤ f y + C * edist x y) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ENNReal.tendsto_nhds_of_Icc fun ε ε0 => ?_
  rcases ENNReal.exists_nnreal_pos_mul_lt hC ε0.ne' with ⟨δ, δ0, hδ⟩
  rw [mul_comm] at hδ
  filter_upwards [Metric.closedEBall_mem_nhds x (ENNReal.coe_pos.2 δ0)] with y hy
  refine ⟨tsub_le_iff_right.2 <| (h x y).trans ?_, (h y x).trans ?_⟩ <;> grw [← hδ.le] <;> gcongr
  exacts [Metric.mem_closedEBall'.1 hy, Metric.mem_closedEBall.1 hy]
/-
**continuous_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_edist : Continuous fun p : α × α => edist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_le_add_edist`：continuous_of_le_add_edist {f : α -> Real>=0
∞} (C : Real>=0∞) (hC : C != ∞) (h : forall x y, f x <= f y + C * edist x y) : C
ontinuous f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `edist_triangle4`：edist_triangle4 (x y z t : α) : edist x t <= edist x y 
+ edist y z + edist z t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `_private.Mathlib.Topology.Instances.ENNReal.Lemmas.0.continuous_edist._a
bel_1_1`：∀ {α : Type u_1} [inst : PseudoEMetricSpace α] (x y x' y' : α),   edist
 x x' + edist x' y' + edist y' y = edist x' y' + (edist x x' + edist …
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem continuous_edist : Continuous fun p : α × α => edist p.1 p.2 := by
  apply continuous_of_le_add_edist 2 (by decide)
  rintro ⟨x, y⟩ ⟨x', y'⟩
  calc
    edist x y ≤ edist x x' + edist x' y' + edist y' y := edist_triangle4 _ _ _ _
    _ = edist x' y' + (edist x x' + edist y y') := by rw [edist_comm y y']; abel
    _ ≤ edist x' y' + (edist (x, y) (x', y') + edist (x, y) (x', y')) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = edist x' y' + 2 * edist (x, y) (x', y') := by rw [← mul_two, mul_comm]

@[continuity, fun_prop]
/-
**Continuous.edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.edist [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (
hg : Continuous g) : Continuous fun b => edist (f b) (g b)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_edist`：continuous_edist : Continuous fun p : α × α => edist p
.1 p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
-/
theorem Continuous.edist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => edist (f b) (g b) :=
  continuous_edist.comp (hf.prodMk hg :)
/-
**Filter.Tendsto.edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.edist {f g : β -> α} {x : Filter β} {a b : α} (hf : Tendsto
 f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => edist (f x) (g x)) x (𝓝
 (edist a b))
参数：hf : Tendsto f x (𝓝 a)；hg : Tendsto g x (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_edist`：continuous_edist : Continuous fun p : α × α => edist p
.1 p.2
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.edist {f g : β → α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => edist (f x) (g x)) x (𝓝 (edist a b)) :=
  (continuous_edist.tendsto (a, b)).comp (hf.prodMk_nhds hg)
/-
**Metric.isClosed_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.isClosed_closedEBall {a : α} {r : Real>=0∞} : IsClosed (closedEBall
 a r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Continuous.edist`：Continuous.edist [TopologicalSpace β] {f g : β -> α} (
hf : Continuous f) (hg : Continuous g) : Continuous fun b => edist (f b) (g b)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem Metric.isClosed_closedEBall {a : α} {r : ℝ≥0∞} : IsClosed (closedEBall a r) :=
  isClosed_le (by fun_prop) continuous_const

@[deprecated (since := "2026-01-24")]
alias EMetric.isClosed_closedBall := Metric.isClosed_closedEBall

@[simp]
/-
**Metric.ediam_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.ediam_closure (s : Set α) : ediam (closure s) = ediam s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `map_mem_closure₂`：map_mem_closure₂ {f : X -> Y -> Z} {x : X} {y : Y} {s 
: Set X} {t : Set Y} {u : Set Z} (hf : Continuous (uncurry f)) (hx : x in closur
e s) (…
· 使用定理 `continuous_edist`：continuous_edist : Continuous fun p : α × α => edist p
.1 p.2
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_Iic`：closure_Iic (a : α) : closure (Iic a) = Iic a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Metric.ediam_closure (s : Set α) : ediam (closure s) = ediam s := by
  refine le_antisymm (ediam_le fun x hx y hy => ?_) (ediam_mono subset_closure)
  have : edist x y ∈ closure (Iic (ediam s)) :=
    map_mem_closure₂ continuous_edist hx hy fun x hx y hy => edist_le_ediam_of_mem hx hy
  rwa [closure_Iic] at this

@[deprecated (since := "2026-01-04")] alias EMetric.diam_closure := Metric.ediam_closure

@[simp]
/-
**Metric.diam_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.diam_closure {α : Type*} [PseudoMetricSpace α] (s : Set α) : Metric
.diam (closure s) = diam s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_closure`：Metric.ediam_closure (s : Set α) : ediam (closure 
s) = ediam s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Metric.diam_closure {α : Type*} [PseudoMetricSpace α] (s : Set α) :
    Metric.diam (closure s) = diam s := by simp only [Metric.diam, Metric.ediam_closure]
/-
**isClosed_setOfPred_lipschitzOnWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_lipschitzOnWith {α β} [PseudoEMetricSpace α] [PseudoEMe
tricSpace β] (K : Real>=0) (s : Set α) : IsClosed { f : α -> β | LipschitzOnWith
 K f s }
参数：K : Real>=0；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Continuous.edist`：Continuous.edist [TopologicalSpace β] {f g : β -> α} (
hf : Continuous f) (hg : Continuous g) : Continuous fun b => edist (f b) (g b)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem isClosed_setOfPred_lipschitzOnWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (K : ℝ≥0)
    (s : Set α) : IsClosed { f : α → β | LipschitzOnWith K f s } := by
  simp only [LipschitzOnWith, ofPred_forall]
  refine isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_le ?_ ?_
  exacts [.edist (continuous_apply x) (continuous_apply y), continuous_const]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzOnWith := isClosed_setOfPred_lipschitzOnWith
/-
**isClosed_setOfPred_lipschitzWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_lipschitzWith {α β} [PseudoEMetricSpace α] [PseudoEMetr
icSpace β] (K : Real>=0) : IsClosed { f : α -> β | LipschitzWith K f }
参数：K : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isClosed_setOfPred_lipschitzWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (K : ℝ≥0) :
    IsClosed { f : α → β | LipschitzWith K f } := by
  simp only [← lipschitzOnWith_univ, isClosed_setOfPred_lipschitzOnWith]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzWith := isClosed_setOfPred_lipschitzWith
/-
**LipschitzOnWith.closure** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoEMetricSpace α] [inst_1 : Ps
eudoEMetricSpace β] {f : α → β} {s : Set α}   {K : NNReal}, ContinuousOn f (clos
ure s) → LipschitzOnWith K f s → LipschitzOnWith K f (closure s)
参数：closure s；closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.continuous_const_mul`：∀ {a : ENNReal}, a ≠ ⊤ → Continuous fun x 
=> a * x
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `le_on_closure`：le_on_closure [TopologicalSpace β] {f g : β -> α} {s : Se
t β} (h : forall x in s, f x <= g x) (hf : ContinuousOn f (closure s)) (hg : Con
tin…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Continuous.edist`：Continuous.edist [TopologicalSpace β] {f g : β -> α} (
hf : Continuous f) (hg : Continuous g) : Continuous fun b => edist (f b) (g b)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
protected lemma LipschitzOnWith.closure [PseudoEMetricSpace β] {f : α → β} {s : Set α} {K : ℝ≥0}
    (hcont : ContinuousOn f (closure s)) (hf : LipschitzOnWith K f s) :
    LipschitzOnWith K f (closure s) := by
  have := ENNReal.continuous_const_mul (ENNReal.coe_ne_top (r := K))
  refine fun x hx ↦ le_on_closure (fun y hy ↦ le_on_closure (fun x hx ↦ hf hx hy) ?_ ?_ hx) ?_ ?_
  all_goals fun_prop
/-
**lipschitzOnWith_closure_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_closure_iff [PseudoEMetricSpace β] {f : α -> β} {s : Set α
} {K : Real>=0} (hcont : ContinuousOn f (closure s)) : LipschitzOnWith K f (clos
ure s) ↔ LipschitzOnWith K f s
参数：hcont : ContinuousOn f (closure s)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.mono`：LipschitzOnWith.mono (hf : LipschitzOnWith K f t) 
(h : s subseteq t) : LipschitzOnWith K f s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `LipschitzOnWith.closure`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoE
MetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {s : Set α}   {K : NN
Real}, Contin…
-/
lemma lipschitzOnWith_closure_iff [PseudoEMetricSpace β] {f : α → β} {s : Set α} {K : ℝ≥0}
    (hcont : ContinuousOn f (closure s)) :
    LipschitzOnWith K f (closure s) ↔ LipschitzOnWith K f s :=
  ⟨fun hf ↦ hf.mono subset_closure, LipschitzOnWith.closure hcont⟩

namespace Real

/-- For a bounded set `s : Set ℝ`, its `ediam` is equal to `sSup s - sInf s` reinterpreted as
`ℝ≥0∞`. -/
/-
**Real.ediam_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ediam_eq {s : Set Real} (h : Bornology.IsBounded s) : Metric.ediam s = ENN
Real.ofReal (sSup s - sInf s)
参数：h : Bornology.IsBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_empty`：ediam_empty : ediam (∅ : Set X) = 0
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Metric.ediam_le_of_forall_dist_le`：ediam_le_of_forall_dist_le {C : Real}
 (h : forall x in s, forall y in s, dist x y <= C) : ediam s <= ENNReal.ofReal C
· 使用引理 `Real.dist_le_of_mem_Icc`：dist_le_of_mem_Icc {x y x' y' : Real} (hx : x i
n Icc x' y') (hy : y in Icc x' y') : dist x y <= y' - x'
· 使用定理 `Bornology.IsBounded.subset_Icc_sInf_sSup`：∀ {α : Type u_1} [inst : Borno
logy α] [inst_1 : ConditionallyCompleteLattice α] [IsOrderBornology α] {s : Set 
α},   Bornology.IsBounded s → …
· 使用定理 `ENNReal.ofReal_le_of_le_toReal`：ofReal_le_of_le_toReal {a : Real} {b : R
eal>=0∞} (h : a <= ENNReal.toReal b) : ENNReal.ofReal a <= b
· 使用定理 `Metric.diam.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (s : Set α
), Metric.diam s = (Metric.ediam s).toReal
· 使用定理 `Metric.diam_closure`：Metric.diam_closure {α : Type*} [PseudoMetricSpace 
α] (s : Set α) : Metric.diam (closure s) = diam s
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Metric.dist_le_diam_of_mem`：dist_le_diam_of_mem (h : IsBounded s) (hx : 
x in s) (hy : y in s) : dist x y <= diam s
· 使用定理 `Bornology.IsBounded.closure`：∀ {α : Type u} {s : Set α} [inst : PseudoMe
tricSpace α], Bornology.IsBounded s → Bornology.IsBounded (closure s)
· 使用定理 `csSup_mem_closure`：csSup_mem_closure {s : Set α} (hs : s.Nonempty) (B : 
BddAbove s) : sSup s in closure s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Bornology.IsBounded.bddAbove`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dAbove s
· 使用定理 `csInf_mem_closure`：csInf_mem_closure {s : Set α} (hs : s.Nonempty) (B : 
BddBelow s) : sInf s in closure s
· 使用定理 `Bornology.IsBounded.bddBelow`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dBelow s

--- 原说明 ---
For a bounded set `s : Set ℝ`, its `ediam` is equal to `sSup s - sInf s` reinter
preted as
`ℝ≥0∞`.
-/
theorem ediam_eq {s : Set ℝ} (h : Bornology.IsBounded s) :
    Metric.ediam s = ENNReal.ofReal (sSup s - sInf s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp
  refine le_antisymm (Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_) ?_
  · exact Real.dist_le_of_mem_Icc (h.subset_Icc_sInf_sSup hx) (h.subset_Icc_sInf_sSup hy)
  · apply ENNReal.ofReal_le_of_le_toReal
    rw [← Metric.diam, ← Metric.diam_closure]
    calc sSup s - sInf s ≤ dist (sSup s) (sInf s) := le_abs_self _
    _ ≤ Metric.diam (closure s) := dist_le_diam_of_mem h.closure (csSup_mem_closure hne h.bddAbove)
        (csInf_mem_closure hne h.bddBelow)

/-- For a bounded set `s : Set ℝ`, its `Metric.diam` is equal to `sSup s - sInf s`. -/
/-
**Real.diam_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：diam_eq {s : Set Real} (h : Bornology.IsBounded s) : Metric.diam s = sSup 
s - sInf s
参数：h : Bornology.IsBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.diam.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (s : Set α
), Metric.diam s = (Metric.ediam s).toReal
· 使用定理 `Real.ediam_eq`：ediam_eq {s : Set Real} (h : Bornology.IsBounded s) : Met
ric.ediam s = ENNReal.ofReal (sSup s - sInf s)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.sInf_le_sSup`：sInf_le_sSup (s : Set Real) (h₁ : BddBelow s) (h₂ : B
ddAbove s) : sInf s <= sSup s
· 使用定理 `Bornology.IsBounded.bddBelow`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dBelow s
· 使用定理 `Bornology.IsBounded.bddAbove`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dAbove s

--- 原说明 ---
For a bounded set `s : Set ℝ`, its `Metric.diam` is equal to `sSup s - sInf s`.
-/
theorem diam_eq {s : Set ℝ} (h : Bornology.IsBounded s) : Metric.diam s = sSup s - sInf s := by
  rw [Metric.diam, Real.ediam_eq h, ENNReal.toReal_ofReal]
  exact sub_nonneg.2 (Real.sInf_le_sSup s h.bddBelow h.bddAbove)

@[simp]
/-
**Real.ediam_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ediam_Ioo (a b : Real) : Metric.ediam (Ioo a b) = ENNReal.ofReal (b - a)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Metric.ediam_empty`：ediam_empty : ediam (∅ : Set X) = 0
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.ediam_eq`：ediam_eq {s : Set Real} (h : Bornology.IsBounded s) : Met
ric.ediam s = ENNReal.ofReal (sSup s - sInf s)
· 使用定理 `Metric.isBounded_Ioo`：isBounded_Ioo (a b : α) : IsBounded (Ioo a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `csSup_Ioo`：csSup_Ioo [DenselyOrdered α] (h : a < b) : sSup (Ioo a b) = b
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `csInf_Ioo`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {a b
 : α} [DenselyOrdered α], b < a → sInf (Set.Ioo b a) = b
-/
theorem ediam_Ioo (a b : ℝ) : Metric.ediam (Ioo a b) = ENNReal.ofReal (b - a) := by
  rcases le_or_gt b a with (h | h)
  · simp [h]
  · rw [Real.ediam_eq (isBounded_Ioo _ _), csSup_Ioo h, csInf_Ioo h]

@[simp]
/-
**Real.ediam_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ediam_Icc (a b : Real) : Metric.ediam (Icc a b) = ENNReal.ofReal (b - a)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ediam_eq`：ediam_eq {s : Set Real} (h : Bornology.IsBounded s) : Met
ric.ediam s = ENNReal.ofReal (sSup s - sInf s)
· 使用定理 `Metric.isBounded_Icc`：isBounded_Icc (a b : α) : IsBounded (Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `csSup_Icc`：csSup_Icc {a b : α} (h : a <= b) : sSup (Icc a b) = b
· 使用定理 `csInf_Icc`：csInf_Icc {α : Type*} [ConditionallyCompletePartialOrderInf α
] {a b : α} (h : a <= b) : sInf (Icc a b) = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Metric.ediam_empty`：ediam_empty : ediam (∅ : Set X) = 0
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ediam_Icc (a b : ℝ) : Metric.ediam (Icc a b) = ENNReal.ofReal (b - a) := by
  rcases le_or_gt a b with (h | h)
  · rw [Real.ediam_eq (isBounded_Icc _ _), csSup_Icc h, csInf_Icc h]
  · simp [h, h.le]

@[simp]
/-
**Real.ediam_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ediam_Ico (a b : Real) : Metric.ediam (Ico a b) = ENNReal.ofReal (b - a)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Real.ediam_Icc`：ediam_Icc (a b : Real) : Metric.ediam (Icc a b) = ENNRea
l.ofReal (b - a)
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `Real.ediam_Ioo`：ediam_Ioo (a b : Real) : Metric.ediam (Ioo a b) = ENNRea
l.ofReal (b - a)
-/
theorem ediam_Ico (a b : ℝ) : Metric.ediam (Ico a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ ediam_mono Ico_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ico_self)

@[simp]
/-
**Real.ediam_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ediam_Ioc (a b : Real) : Metric.ediam (Ioc a b) = ENNReal.ofReal (b - a)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Real.ediam_Icc`：ediam_Icc (a b : Real) : Metric.ediam (Icc a b) = ENNRea
l.ofReal (b - a)
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `Real.ediam_Ioo`：ediam_Ioo (a b : Real) : Metric.ediam (Ioo a b) = ENNRea
l.ofReal (b - a)
-/
theorem ediam_Ioc (a b : ℝ) : Metric.ediam (Ioc a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ ediam_mono Ioc_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ioc_self)
/-
**Real.diam_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：diam_Icc {a b : Real} (h : a <= b) : Metric.diam (Icc a b) = b - a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ediam_Icc`：ediam_Icc (a b : Real) : Metric.ediam (Icc a b) = ENNRea
l.ofReal (b - a)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diam_Icc {a b : ℝ} (h : a ≤ b) : Metric.diam (Icc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]
/-
**Real.diam_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：diam_Ico {a b : Real} (h : a <= b) : Metric.diam (Ico a b) = b - a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ediam_Ico`：ediam_Ico (a b : Real) : Metric.ediam (Ico a b) = ENNRea
l.ofReal (b - a)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diam_Ico {a b : ℝ} (h : a ≤ b) : Metric.diam (Ico a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]
/-
**Real.diam_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：diam_Ioc {a b : Real} (h : a <= b) : Metric.diam (Ioc a b) = b - a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ediam_Ioc`：ediam_Ioc (a b : Real) : Metric.ediam (Ioc a b) = ENNRea
l.ofReal (b - a)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diam_Ioc {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]
/-
**Real.diam_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：diam_Ioo {a b : Real} (h : a <= b) : Metric.diam (Ioo a b) = b - a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ediam_Ioo`：ediam_Ioo (a b : Real) : Metric.ediam (Ioo a b) = ENNRea
l.ofReal (b - a)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diam_Ioo {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioo a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

end Real

end

namespace ENNReal

section truncateToReal

/-- With truncation level `t`, the truncated cast `ℝ≥0∞ → ℝ` is given by `x ↦ (min t x).toReal`.
Unlike `ENNReal.toReal`, this cast is continuous and monotone when `t ≠ ∞`. -/
/-
**ENNReal.truncateToReal** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：truncateToReal (t x : Real>=0∞) : Real
参数：t x : Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
With truncation level `t`, the truncated cast `ℝ≥0∞ → ℝ` is given by `x ↦ (min t
 x).toReal`.
Unlike `ENNReal.toReal`, this cast is continuous and monotone when `t ≠ ∞`.
-/
noncomputable def truncateToReal (t x : ℝ≥0∞) : ℝ := (min t x).toReal
/-
**ENNReal.truncateToReal_eq_toReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：truncateToReal_eq_toReal {t x : Real>=0∞} (t_ne_top : t != ∞) (x_le : x <=
 t) : truncateToReal t x = x.toReal
参数：t_ne_top : t != ∞；x_le : x <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
lemma truncateToReal_eq_toReal {t x : ℝ≥0∞} (t_ne_top : t ≠ ∞) (x_le : x ≤ t) :
    truncateToReal t x = x.toReal := by
  have x_lt_top : x < ∞ := lt_of_le_of_lt x_le t_ne_top.lt_top
  have obs : min t x ≠ ∞ := by
    simp_all only [ne_eq, min_eq_top, false_and, not_false_eq_true]
  exact (ENNReal.toReal_eq_toReal_iff' obs x_lt_top.ne).mpr (min_eq_right x_le)
/-
**ENNReal.truncateToReal_le** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：truncateToReal_le {t : Real>=0∞} (t_ne_top : t != ∞) {x : Real>=0∞} : trun
cateToReal t x <= t.toReal
参数：t_ne_top : t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.truncateToReal.eq_1`：∀ (t x : ENNReal), t.truncateToReal x = (mi
n t x).toReal
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
lemma truncateToReal_le {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) {x : ℝ≥0∞} :
    truncateToReal t x ≤ t.toReal := by
  rw [truncateToReal]
  gcongr
  exact min_le_left t x
/-
**ENNReal.truncateToReal_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：truncateToReal_nonneg {t x : Real>=0∞} : 0 <= truncateToReal t x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
lemma truncateToReal_nonneg {t x : ℝ≥0∞} : 0 ≤ truncateToReal t x := toReal_nonneg

/-- The truncated cast `ENNReal.truncateToReal t : ℝ≥0∞ → ℝ` is monotone when `t ≠ ∞`. -/
/-
**ENNReal.monotone_truncateToReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：monotone_truncateToReal {t : Real>=0∞} (t_ne_top : t != ∞) : Monotone (tru
ncateToReal t)
参数：t_ne_top : t != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The truncated cast `ENNReal.truncateToReal t : ℝ≥0∞ → ℝ` is monotone when `t ≠ ∞
`.
-/
lemma monotone_truncateToReal {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) : Monotone (truncateToReal t) := by
  intro x y x_le_y
  simp only [truncateToReal]
  gcongr
  exact ne_top_of_le_ne_top t_ne_top (min_le_left _ _)

/-- The truncated cast `ENNReal.truncateToReal t : ℝ≥0∞ → ℝ` is continuous when `t ≠ ∞`. -/
@[fun_prop]
/-
**ENNReal.continuous_truncateToReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：continuous_truncateToReal {t : Real>=0∞} (t_ne_top : t != ∞) : Continuous 
(truncateToReal t)
参数：t_ne_top : t != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用引理 `ENNReal.continuousOn_toReal`：continuousOn_toReal : ContinuousOn ENNReal.
toReal { a | a != ∞ }
· 使用定理 `Continuous.min`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : Topol
ogic…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The truncated cast `ENNReal.truncateToReal t : ℝ≥0∞ → ℝ` is continuous when `t ≠
 ∞`.
-/
lemma continuous_truncateToReal {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) : Continuous (truncateToReal t) := by
  apply continuousOn_toReal.comp_continuous (by fun_prop)
  simp [t_ne_top]

end truncateToReal

section LimsupLiminf

variable {ι : Type*} {f : Filter ι} {u v : ι → ℝ≥0∞}

/-
**ENNReal.limsup_sub_const** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：limsup_sub_const (F : Filter ι) (f : ι -> Real>=0∞) (c : Real>=0∞) : Filte
r.limsup (fun i => f i - c) F = Filter.limsup f F - c
参数：F : Filter ι；f : ι -> Real>=0∞；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.limsup f ⊥ = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_limsSup_of_continuousAt`：Monotone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ENNReal.continuous_sub_right`：continuous_sub_right (a : Real>=0∞) : Cont
inuous fun x : Real>=0∞ => x - a
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
-/
lemma limsup_sub_const (F : Filter ι) (f : ι → ℝ≥0∞) (c : ℝ≥0∞) :
    Filter.limsup (fun i ↦ f i - c) F = Filter.limsup f F - c := by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ x - c)
    (fun _ _ h ↦ tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm
/-
**ENNReal.liminf_sub_const** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：liminf_sub_const (F : Filter ι) [NeBot F] (f : ι -> Real>=0∞) (c : Real>=0
∞) : Filter.liminf (fun i => f i - c) F = Filter.liminf f F - c
参数：F : Filter ι；f : ι -> Real>=0∞；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_limsInf_of_continuousAt`：Monotone.map_limsInf_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsInf) (cobdd …
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ENNReal.continuous_sub_right`：continuous_sub_right (a : Real>=0∞) : Cont
inuous fun x : Real>=0∞ => x - a
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
-/
lemma liminf_sub_const (F : Filter ι) [NeBot F] (f : ι → ℝ≥0∞) (c : ℝ≥0∞) :
    Filter.liminf (fun i ↦ f i - c) F = Filter.liminf f F - c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ x - c)
    (fun _ _ h ↦ tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm
/-
**ENNReal.limsup_const_sub** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：limsup_const_sub (F : Filter ι) (f : ι -> Real>=0∞) {c : Real>=0∞} (c_ne_t
op : c != ∞) : Filter.limsup (fun i => c - f i) F = c - Filter.liminf f F
参数：F : Filter ι；f : ι -> Real>=0∞；c_ne_top : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.limsup f ⊥ = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.liminf_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.liminf f ⊥ = ⊤
· 使用定理 `ENNReal.sub_top`：∀ {a : ENNReal}, a - ⊤ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Antitone.map_limsInf_of_continuousAt`：Antitone.map_limsInf_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_decr : Antitone f) (f_cont : Continu
ousAt f F.limsInf) (cobdd …
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ENNReal.continuous_sub_left`：continuous_sub_left {a : Real>=0∞} (a_ne_to
p : a != ∞) : Continuous (a - ·)
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
-/
lemma limsup_const_sub (F : Filter ι) (f : ι → ℝ≥0∞) {c : ℝ≥0∞} (c_ne_top : c ≠ ∞) :
    Filter.limsup (fun i ↦ c - f i) F = c - Filter.liminf f F := by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm
/-
**ENNReal.liminf_const_sub** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：liminf_const_sub (F : Filter ι) [NeBot F] (f : ι -> Real>=0∞) {c : Real>=0
∞} (c_ne_top : c != ∞) : Filter.liminf (fun i => c - f i) F = c - Filter.limsup 
f F
参数：F : Filter ι；f : ι -> Real>=0∞；c_ne_top : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Antitone.map_limsSup_of_continuousAt`：Antitone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_decr : Antitone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ENNReal.continuous_sub_left`：continuous_sub_left {a : Real>=0∞} (a_ne_to
p : a != ∞) : Continuous (a - ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
-/
lemma liminf_const_sub (F : Filter ι) [NeBot F] (f : ι → ℝ≥0∞) {c : ℝ≥0∞} (c_ne_top : c ≠ ∞) :
    Filter.liminf (fun i ↦ c - f i) F = c - Filter.limsup f F :=
  (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm
/-
**ENNReal.le_limsup_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：le_limsup_mul : limsup u f * liminf v f <= limsup (u * v) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.mul_le_of_forall_lt`：mul_le_of_forall_lt {a b c : Real>=0∞} (h :
 forall a' < a, forall b' < b, a' * b' <= c) : a * b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_limsup_iff`：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.frequently_lt_of_lt_limsup`：frequently_lt_of_lt_limsup {b : β} (h
u : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ENNReal.mul_lt_mul`：mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma le_limsup_mul : limsup u f * liminf v f ≤ limsup (u * v) f :=
  mul_le_of_forall_lt fun a a_u b b_v ↦ (le_limsup_iff).2 fun c c_ab ↦
    Frequently.mono (Frequently.and_eventually ((frequently_lt_of_lt_limsup) a_u)
    ((eventually_lt_of_lt_liminf) b_v)) fun _ ab_x ↦ c_ab.trans (mul_lt_mul ab_x.1 ab_x.2)

/-- See also `ENNReal.limsup_mul_le`. -/
/-
**ENNReal.limsup_mul_le'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：limsup_mul_le' (h : limsup u f != 0 ∨ limsup v f != ∞) (h' : limsup u f !=
 ∞ ∨ limsup v f != 0) : limsup (u * v) f <= limsup u f * limsup v f
参数：h : limsup u f != 0 ∨ limsup v f != ∞；h' : limsup u f != ∞ ∨ limsup v f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.le_mul_of_forall_lt`：le_mul_of_forall_lt {a b c : Real>=0∞} (h₁ 
: a != 0 ∨ b != ∞) (h₂ : a != ∞ ∨ b != 0) (h : forall a' > a, forall b' > b, c <
= a' * b') : c <=…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.limsup_le_iff`：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ENNReal.mul_lt_mul`：mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d

--- 原说明 ---
See also `ENNReal.limsup_mul_le`.
-/
lemma limsup_mul_le' (h : limsup u f ≠ 0 ∨ limsup v f ≠ ∞) (h' : limsup u f ≠ ∞ ∨ limsup v f ≠ 0) :
    limsup (u * v) f ≤ limsup u f * limsup v f := by
  refine le_mul_of_forall_lt h h' fun a a_u b b_v ↦ (limsup_le_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (mul_lt_mul a_x b_x).trans c_ab
/-
**ENNReal.le_liminf_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：le_liminf_mul : liminf u f * liminf v f <= liminf (u * v) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.mul_le_of_forall_lt`：mul_le_of_forall_lt {a b c : Real>=0∞} (h :
 forall a' < a, forall b' < b, a' * b' <= c) : a * b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_liminf_iff`：le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ENNReal.mul_lt_mul`：mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d
-/
lemma le_liminf_mul : liminf u f * liminf v f ≤ liminf (u * v) f := by
  refine mul_le_of_forall_lt fun a a_u b b_v ↦ (le_liminf_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (mul_lt_mul a_x b_x)
/-
**ENNReal.liminf_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：liminf_mul_le (h : limsup u f != 0 ∨ liminf v f != ∞) (h' : limsup u f != 
∞ ∨ liminf v f != 0) : liminf (u * v) f <= limsup u f * liminf v f
参数：h : limsup u f != 0 ∨ liminf v f != ∞；h' : limsup u f != ∞ ∨ liminf v f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.le_mul_of_forall_lt`：le_mul_of_forall_lt {a b c : Real>=0∞} (h₁ 
: a != 0 ∨ b != ∞) (h₂ : a != ∞ ∨ b != 0) (h : forall a' > a, forall b' > b, c <
= a' * b') : c <=…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.liminf_le_iff`：liminf_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.frequently_lt_of_liminf_lt`：frequently_lt_of_liminf_lt {b : β} (h
u : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ENNReal.mul_lt_mul`：mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma liminf_mul_le (h : limsup u f ≠ 0 ∨ liminf v f ≠ ∞) (h' : limsup u f ≠ ∞ ∨ liminf v f ≠ 0) :
    liminf (u * v) f ≤ limsup u f * liminf v f :=
  le_mul_of_forall_lt h h' fun a a_u b b_v ↦ (liminf_le_iff).2 fun c c_ab ↦
    Frequently.mono (((frequently_lt_of_liminf_lt) b_v).and_eventually
    ((eventually_lt_of_limsup_lt) a_u)) fun _ ab_x ↦ (mul_lt_mul ab_x.2 ab_x.1).trans c_ab

/-- If `u : ι → ℝ≥0∞` is bounded, then we have `liminf (toReal ∘ u) = toReal (liminf u)`. -/
/-
**ENNReal.liminf_toReal_eq** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：liminf_toReal_eq [NeBot f] {b : Real>=0∞} (b_ne_top : b != ∞) (le_b : fora
llᶠ i in f, u i <= b) : f.liminf (fun i => (u i).toReal) = (f.liminf u).toReal
参数：b_ne_top : b != ∞；le_b : forallᶠ i in f, u i <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_le_of_le`：liminf_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsBoundedUnder (· >= ·) u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ENNReal.truncateToReal_eq_toReal`：truncateToReal_eq_toReal {t x : Real>=
0∞} (t_ne_top : t != ∞) (x_le : x <= t) : truncateToReal t x = x.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.liminf_congr`：liminf_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u 
f = limin…
· 使用定理 `Monotone.map_liminf_of_continuousAt`：Monotone.map_liminf_of_continuousAt
 {f : R -> S} (f_incr : Monotone f) (a : ι -> R) (f_cont : ContinuousAt f (F.lim
inf a)) (cobdd : F.IsCobo…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `ENNReal.monotone_truncateToReal`：monotone_truncateToReal {t : Real>=0∞} 
(t_ne_top : t != ∞) : Monotone (truncateToReal t)
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用引理 `ENNReal.continuous_truncateToReal`：continuous_truncateToReal {t : Real>=
0∞} (t_ne_top : t != ∞) : Continuous (truncateToReal t)
· 使用定理 `Filter.IsBoundedUnder.isCoboundedUnder_ge`：∀ {α : Type u_1} {γ : Type u_
3} {u : γ → α} {l : Filter γ} [inst : Preorder α] [l.NeBot],   Filter.IsBoundedU
nder (fun x1 x2 => x1 ≤ x2) l u…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `u : ι → ℝ≥0∞` is bounded, then we have `liminf (toReal ∘ u) = toReal (liminf
 u)`.
-/
lemma liminf_toReal_eq [NeBot f] {b : ℝ≥0∞} (b_ne_top : b ≠ ∞) (le_b : ∀ᶠ i in f, u i ≤ b) :
    f.liminf (fun i ↦ (u i).toReal) = (f.liminf u).toReal := by
  have liminf_le : f.liminf u ≤ b := by
    apply liminf_le_of_le ⟨0, by simp⟩
    intro y h
    obtain ⟨i, hi⟩ := (Eventually.and h le_b).exists
    exact hi.1.trans hi.2
  have aux : ∀ᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.liminf u).toReal = ENNReal.truncateToReal b (f.liminf u) := by
    rw [truncateToReal_eq_toReal b_ne_top liminf_le]
  simp_rw [liminf_congr aux, aux']
  have key := Monotone.map_liminf_of_continuousAt (F := f) (monotone_truncateToReal b_ne_top) u
          (continuous_truncateToReal b_ne_top).continuousAt
          (IsBoundedUnder.isCoboundedUnder_ge ⟨b, by simpa only [eventually_map] using le_b⟩)
          ⟨0, Eventually.of_forall (by simp)⟩
  rw [key]
  rfl

/-- If `u : ι → ℝ≥0∞` is bounded, then we have `liminf (toReal ∘ u) = toReal (liminf u)`. -/
/-
**ENNReal.limsup_toReal_eq** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：limsup_toReal_eq [NeBot f] {b : Real>=0∞} (b_ne_top : b != ∞) (le_b : fora
llᶠ i in f, u i <= b) : f.limsup (fun i => (u i).toReal) = (f.limsup u).toReal
参数：b_ne_top : b != ∞；le_b : forallᶠ i in f, u i <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.truncateToReal_eq_toReal`：truncateToReal_eq_toReal {t x : Real>=
0∞} (t_ne_top : t != ∞) (x_le : x <= t) : truncateToReal t x = x.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.limsup_le_of_le`：limsup_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Monotone.map_limsup_of_continuousAt`：Monotone.map_limsup_of_continuousAt
 {f : R -> S} (f_incr : Monotone f) (a : ι -> R) (f_cont : ContinuousAt f (F.lim
sup a)) (bdd_above : F.Is…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `ENNReal.monotone_truncateToReal`：monotone_truncateToReal {t : Real>=0∞} 
(t_ne_top : t != ∞) : Monotone (truncateToReal t)
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用引理 `ENNReal.continuous_truncateToReal`：continuous_truncateToReal {t : Real>=
0∞} (t_ne_top : t != ∞) : Continuous (truncateToReal t)
· 使用定理 `Filter.IsBoundedUnder.isCoboundedUnder_le`：∀ {α : Type u_1} {γ : Type u_
3} {u : γ → α} {l : Filter γ} [inst : Preorder α] [l.NeBot],   Filter.IsBoundedU
nder (fun x1 x2 => x2 ≤ x1) l u…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
If `u : ι → ℝ≥0∞` is bounded, then we have `liminf (toReal ∘ u) = toReal (liminf
 u)`.
-/
lemma limsup_toReal_eq [NeBot f] {b : ℝ≥0∞} (b_ne_top : b ≠ ∞) (le_b : ∀ᶠ i in f, u i ≤ b) :
    f.limsup (fun i ↦ (u i).toReal) = (f.limsup u).toReal := by
  have aux : ∀ᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.limsup u).toReal = ENNReal.truncateToReal b (f.limsup u) := by
    rw [truncateToReal_eq_toReal b_ne_top (limsup_le_of_le ⟨0, by simp⟩ le_b)]
  simp_rw [limsup_congr aux, aux']
  have key := Monotone.map_limsup_of_continuousAt (F := f) (monotone_truncateToReal b_ne_top) u
          (continuous_truncateToReal b_ne_top).continuousAt
          ⟨b, by simpa only [eventually_map] using le_b⟩
          (IsBoundedUnder.isCoboundedUnder_le ⟨0, Eventually.of_forall (by simp)⟩)
  rw [key]
  rfl

@[simp, norm_cast]
/-
**ENNReal.ofNNReal_limsup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNNReal_limsup {u : ι -> Real>=0} (hf : f.IsBoundedUnder (· <= ·) u) : li
msup u f = limsup (fun i => (u i : Real>=0∞)) f
参数：hf : f.IsBoundedUnder (· <= ·) u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.eq_of_forall_nnreal_le_iff`：eq_of_forall_nnreal_le_iff {x y : Re
al>=0∞} : (forall r : Real>=0, ↑r <= x ↔ ↑r <= y) -> x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Filter.le_limsup_iff`：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ofNNReal_limsup {u : ι → ℝ≥0} (hf : f.IsBoundedUnder (· ≤ ·) u) :
    limsup u f = limsup (fun i ↦ (u i : ℝ≥0∞)) f := by
  refine eq_of_forall_nnreal_le_iff fun r ↦ ?_
  rw [coe_le_coe, le_limsup_iff, le_limsup_iff]
  simp [forall_ennreal]

@[simp, norm_cast]
/-
**ENNReal.ofNNReal_liminf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNNReal_liminf {u : ι -> Real>=0} (hf : f.IsCoboundedUnder (· >= ·) u) : 
liminf u f = liminf (fun i => (u i : Real>=0∞)) f
参数：hf : f.IsCoboundedUnder (· >= ·) u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.eq_of_forall_nnreal_le_iff`：eq_of_forall_nnreal_le_iff {x y : Re
al>=0∞} : (forall r : Real>=0, ↑r <= x ↔ ↑r <= y) -> x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Filter.le_liminf_iff`：le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ofNNReal_liminf {u : ι → ℝ≥0} (hf : f.IsCoboundedUnder (· ≥ ·) u) :
    liminf u f = liminf (fun i ↦ (u i : ℝ≥0∞)) f := by
  refine eq_of_forall_nnreal_le_iff fun r ↦ ?_
  rw [coe_le_coe, le_liminf_iff, le_liminf_iff]
  simp [forall_ennreal]
/-
**ENNReal.liminf_add_of_right_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：liminf_add_of_right_tendsto_zero {u : Filter ι} {g : ι -> Real>=0∞} (hg : 
u.Tendsto g (𝓝 0)) (f : ι -> Real>=0∞) : u.liminf (f + g) = u.liminf f
参数：hg : u.Tendsto g (𝓝 0)；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.liminf_le_of_le`：liminf_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsBoundedUnder (· >= ·) u
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_liminf_iff'`：le_liminf_iff' [DenselyOrdered β] {x : β} (h₁ : f
.IsCoboundedUnder (· >= ·) u
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tendsto_nhds_zero`：∀ {α : Type u_1} {f : Filter α} {u : α → ENNR
eal}, Filter.Tendsto u f (nhds 0) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ≤ ε
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.le_of_add_le_add_right`：∀ {a b c : ENNReal}, a ≠ ⊤ → b + a ≤ c +
 a → b ≤ c
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_le_of_le_tsub_left_of_le`：add_le_of_le_tsub_left_of_le (h : a <= c) 
(h2 : b <= c - a) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
（共 36 条，此处仅展示前 30 条）
-/
theorem liminf_add_of_right_tendsto_zero {u : Filter ι} {g : ι → ℝ≥0∞} (hg : u.Tendsto g (𝓝 0))
    (f : ι → ℝ≥0∞) : u.liminf (f + g) = u.liminf f := by
  refine le_antisymm ?_ <| liminf_le_liminf <| .of_forall <| by simp
  refine liminf_le_of_le (by isBoundedDefault) fun b hb ↦ ?_
  rw [Filter.le_liminf_iff']
  rintro a hab
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| lt_min (tsub_pos_of_lt hab) one_pos]
    with i hfg hg
  exact ENNReal.le_of_add_le_add_right (hg.trans_lt <| by simp).ne <|
    (add_le_of_le_tsub_left_of_le hab.le <| hg.trans <| min_le_left ..).trans hfg
/-
**ENNReal.liminf_add_of_left_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：liminf_add_of_left_tendsto_zero {u : Filter ι} {f : ι -> Real>=0∞} (hf : u
.Tendsto f (𝓝 0)) (g : ι -> Real>=0∞) : u.liminf (f + g) = u.liminf g
参数：hf : u.Tendsto f (𝓝 0)；g : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENNReal.liminf_add_of_right_tendsto_zero`：liminf_add_of_right_tendsto_ze
ro {u : Filter ι} {g : ι -> Real>=0∞} (hg : u.Tendsto g (𝓝 0)) (f : ι -> Real>=0
∞) : u.liminf (f + g) = u.limi…
-/
theorem liminf_add_of_left_tendsto_zero {u : Filter ι} {f : ι → ℝ≥0∞} (hf : u.Tendsto f (𝓝 0))
    (g : ι → ℝ≥0∞) : u.liminf (f + g) = u.liminf g := by
  rw [add_comm, liminf_add_of_right_tendsto_zero hf]
/-
**ENNReal.limsup_add_of_right_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_add_of_right_tendsto_zero {u : Filter ι} {g : ι -> Real>=0∞} (hg : 
u.Tendsto g (𝓝 0)) (f : ι -> Real>=0∞) : u.limsup (f + g) = u.limsup f
参数：hg : u.Tendsto g (𝓝 0)；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.le_limsup_of_le`：le_limsup_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsBoundedUnder (· <= ·) u
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.limsup_le_iff'`：limsup_le_iff' [DenselyOrdered β] {x : β} (h₁ : I
sCoboundedUnder (· <= ·) f u
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tendsto_nhds_zero`：∀ {α : Type u_1} {f : Filter α} {u : α → ENNR
eal}, Filter.Tendsto u f (nhds 0) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ≤ ε
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_of_le_tsub_left_of_le`：add_le_of_le_tsub_left_of_le (h : a <= c) 
(h2 : b <= c - a) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem limsup_add_of_right_tendsto_zero {u : Filter ι} {g : ι → ℝ≥0∞} (hg : u.Tendsto g (𝓝 0))
    (f : ι → ℝ≥0∞) : u.limsup (f + g) = u.limsup f := by
  refine le_antisymm ?_ <| limsup_le_limsup <| .of_forall <| by simp
  refine le_limsup_of_le (by isBoundedDefault) fun b hb ↦ ?_
  rw [Filter.limsup_le_iff']
  rintro a hba
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| tsub_pos_of_lt hba] with i hf hg
  calc f i + g i
    _ ≤ b + g i := by gcongr
    _ ≤ a := add_le_of_le_tsub_left_of_le hba.le hg
/-
**ENNReal.limsup_add_of_left_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_add_of_left_tendsto_zero {u : Filter ι} {f : ι -> Real>=0∞} (hf : u
.Tendsto f (𝓝 0)) (g : ι -> Real>=0∞) : u.limsup (f + g) = u.limsup g
参数：hf : u.Tendsto f (𝓝 0)；g : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENNReal.limsup_add_of_right_tendsto_zero`：limsup_add_of_right_tendsto_ze
ro {u : Filter ι} {g : ι -> Real>=0∞} (hg : u.Tendsto g (𝓝 0)) (f : ι -> Real>=0
∞) : u.limsup (f + g) = u.lims…
-/
theorem limsup_add_of_left_tendsto_zero {u : Filter ι} {f : ι → ℝ≥0∞} (hf : u.Tendsto f (𝓝 0))
    (g : ι → ℝ≥0∞) : u.limsup (f + g) = u.limsup g := by
  rw [add_comm, limsup_add_of_right_tendsto_zero hf]

end LimsupLiminf

end ENNReal -- namespace

/-
**Dense.lipschitzWith_extend** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Dense.lipschitzWith_extend {α β : Type*} [PseudoEMetricSpace α] [EMetricSp
ace β] [CompleteSpace β] {s : Set α} (hs : Dense s) {f : s -> β} {K : Real>=0} (
hf : LipschitzWith K f) : LipschitzWith K (hs.extend f)
参数：hs : Dense s；hf : LipschitzWith K f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `Dense.uniformContinuous_extend`：uniformContinuous_extend [CompleteSpace 
β] (hs : Dense s) (hf : UniformContinuous f) : UniformContinuous (hs.extend f)
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Continuous.edist`：Continuous.edist [TopologicalSpace β] {f g : β -> α} (
hf : Continuous f) (hg : Continuous g) : Continuous fun b => edist (f b) (g b)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ENNReal.continuous_const_mul`：∀ {a : ENNReal}, a ≠ ⊤ → Continuous fun x 
=> a * x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Dense.prod`：Dense.prod {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dens
e t) : Dense (s ×ˢ t)
· 使用定理 `Dense.extend_eq`：extend_eq [T2Space β] (hs : Dense s) (hf : Continuous f
) (x : s) : hs.extend f x = f x
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
lemma Dense.lipschitzWith_extend {α β : Type*}
    [PseudoEMetricSpace α] [EMetricSpace β] [CompleteSpace β]
    {s : Set α} (hs : Dense s) {f : s → β} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (hs.extend f) := by
  have : IsClosed {p : α × α | edist (hs.extend f p.1) (hs.extend f p.2) ≤ K * edist p.1 p.2} := by
    have : Continuous (hs.extend f) := (hs.uniformContinuous_extend hf.uniformContinuous).continuous
    apply isClosed_le (by fun_prop)
    exact (ENNReal.continuous_const_mul (by simp)).comp (by fun_prop)
  have : Dense {p : α × α | edist (hs.extend f p.1) (hs.extend f p.2) ≤ K * edist p.1 p.2} := by
    apply (hs.prod hs).mono
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have Ax : hs.extend f x = f ⟨x, hx⟩ := hs.extend_eq hf.continuous ⟨x, hx⟩
    have Ay : hs.extend f y = f ⟨y, hy⟩ := hs.extend_eq hf.continuous ⟨y, hy⟩
    simp only [Set.mem_ofPred_eq, Ax, Ay]
    exact hf ⟨x, hx⟩ ⟨y, hy⟩
  simpa only [Dense, IsClosed.closure_eq, Set.mem_ofPred_eq, Prod.forall] using! this
