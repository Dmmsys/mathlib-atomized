/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Topology on `ℝ≥0`

The basic lemmas for the natural topology on `ℝ≥0` .

## Main statements

Various mathematically trivial lemmas are proved about the compatibility
of limits and sums in `ℝ≥0` and `ℝ`. For example

* `tendsto_coe {f : Filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
  Filter.Tendsto (fun a, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ Filter.Tendsto m f (𝓝 x)`

says that the limit of a filter along a map to `ℝ≥0` is the same in `ℝ` and `ℝ≥0`, and

* `coe_tsum {f : α → ℝ≥0} : ((∑'a, f a) : ℝ) = (∑'a, (f a : ℝ))`

says that says that a sum of elements in `ℝ≥0` is the same in `ℝ` and `ℝ≥0`.

Similarly, some mathematically trivial lemmas about infinite sums are proved,
a few of which rely on the fact that subtraction is continuous.

-/

@[expose] public section

noncomputable section

open Filter Metric Set TopologicalSpace Topology

variable {ι : Sort*} {n : ℕ}

namespace NNReal

variable {α : Type*} {L : SummationFilter α}

section coe

/-
**NNReal.isOpen_Ico_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：isOpen_Ico_zero {x : NNReal} : IsOpen (Set.Ico 0 x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ico_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Ico ⊥ a = Set.Iio a
-/
lemma isOpen_Ico_zero {x : NNReal} : IsOpen (Set.Ico 0 x) :=
  Ico_bot (a := x) ▸ isOpen_Iio

open Filter Finset

@[fun_prop]
/-
**NNReal._root_.continuous_real_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.continuous_real_toNNReal : Continuous Real.toNNReal :=
  (continuous_id.max continuous_const).subtype_mk _

/-- `Real.toNNReal` bundled as a continuous map for convenience. -/
@[simps -fullyApplied]
/-
**NNReal._root_.ContinuousMap.realToNNReal** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Real.toNNReal` bundled as a continuous map for convenience.
-/
noncomputable def _root_.ContinuousMap.realToNNReal : C(ℝ, ℝ≥0) :=
  .mk Real.toNNReal continuous_real_toNNReal

@[simp]
/-
**NNReal.map_coe_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：map_coe_nhdsGT (x : Real>=0) : (𝓝[>] x).map toReal = 𝓝[>] ↑x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `NNReal.isEmbedding_coe`：NNReal.isEmbedding_coe : Topology.IsEmbedding NN
Real.toReal
· 使用定理 `NNReal.image_coe_Ioi`：image_coe_Ioi (x : Real>=0) : toReal '' Ioi x = Io
i ↑x
-/
theorem map_coe_nhdsGT (x : ℝ≥0) : (𝓝[>] x).map toReal = 𝓝[>] ↑x := by
  rw [isEmbedding_coe.map_nhdsWithin_eq, image_coe_Ioi]

@[simp]
/-
**NNReal.map_coe_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：map_coe_nhdsGE (x : Real>=0) : (𝓝[>=] x).map toReal = 𝓝[>=] ↑x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `NNReal.isEmbedding_coe`：NNReal.isEmbedding_coe : Topology.IsEmbedding NN
Real.toReal
· 使用定理 `NNReal.image_coe_Ici`：image_coe_Ici (x : Real>=0) : toReal '' Ici x = Ic
i ↑x
-/
theorem map_coe_nhdsGE (x : ℝ≥0) : (𝓝[≥] x).map toReal = 𝓝[≥] ↑x := by
  rw [isEmbedding_coe.map_nhdsWithin_eq, image_coe_Ici]
/-
**NNReal._root_.ContinuousOn.ofReal_map_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `NNRe
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousOn.ofReal_map_toNNReal {f : ℝ≥0 → ℝ≥0} {s : Set ℝ} {t : Set ℝ≥0}
    (hf : ContinuousOn f t) (h : Set.MapsTo Real.toNNReal s t) :
    ContinuousOn (fun x ↦ f x.toNNReal : ℝ → ℝ) s :=
  continuous_subtype_val.comp_continuousOn <| hf.comp continuous_real_toNNReal.continuousOn h

@[simp, norm_cast]
/-
**NNReal.tendsto_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tendsto_coe {f : Filter α} {m : α -> Real>=0} {x : Real>=0} : Tendsto (fun
 a => (m a : Real)) f (𝓝 (x : Real)) ↔ Tendsto m f (𝓝 x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `tendsto_subtype_rng`：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Typ
e u_5} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filt
er.Tendst…
-/
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
    Tendsto (fun a => (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ Tendsto m f (𝓝 x) :=
  tendsto_subtype_rng.symm
/-
**NNReal.tendsto_coe'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tendsto_coe' {f : Filter α} [NeBot f] {m : α -> Real>=0} {x : Real} : Tend
sto (fun a => m a : α -> Real) f (𝓝 x) ↔ exists hx : 0 <= x, Tendsto m f (𝓝 ⟨x, 
hx⟩)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {x : R
eal>=0} : Tendsto (fun a => (m a : Real)) f (𝓝 (x : Real)) ↔ Tendsto m f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem tendsto_coe' {f : Filter α} [NeBot f] {m : α → ℝ≥0} {x : ℝ} :
    Tendsto (fun a => m a : α → ℝ) f (𝓝 x) ↔ ∃ hx : 0 ≤ x, Tendsto m f (𝓝 ⟨x, hx⟩) :=
  ⟨fun h => ⟨ge_of_tendsto' h fun c => (m c).2, tendsto_coe.1 h⟩, fun ⟨_, hm⟩ => tendsto_coe.2 hm⟩
/-
**NNReal.map_coe_atTop** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Filter.map NNReal.toReal Filter.atTop = Filter.atTop
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_val_Ici_atTop`：map_val_Ici_atTop [Preorder α] [IsDirectedOrde
r α] (a : α) : map ((↑) : Ici a -> α) atTop = atTop
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
-/
@[simp] theorem map_coe_atTop : map toReal atTop = atTop := map_val_Ici_atTop 0

@[simp]
/-
**NNReal.comap_coe_atTop** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：comap_coe_atTop : comap toReal atTop = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.atTop_Ici_eq`：atTop_Ici_eq [Preorder α] [IsDirectedOrder α] (a : 
α) : atTop = comap ((↑) : Ici a -> α) atTop
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
-/
theorem comap_coe_atTop : comap toReal atTop = atTop := (atTop_Ici_eq 0).symm

@[simp, norm_cast]
/-
**NNReal.tendsto_coe_atTop** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tendsto_coe_atTop {f : Filter α} {m : α -> Real>=0} : Tendsto (fun a => (m
 a : Real)) f atTop ↔ Tendsto m f atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.tendsto_Ici_atTop`：tendsto_Ici_atTop [Preorder α] [IsDirectedOrde
r α] {a : α} {f : β -> Ici a} {l : Filter β} : Tendsto f l atTop ↔ Tendsto (fun 
x => (f x : α)…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
-/
theorem tendsto_coe_atTop {f : Filter α} {m : α → ℝ≥0} :
    Tendsto (fun a => (m a : ℝ)) f atTop ↔ Tendsto m f atTop :=
  tendsto_Ici_atTop.symm
/-
**NNReal._root_.tendsto_real_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.tendsto_real_toNNReal {f : Filter α} {m : α → ℝ} {x : ℝ} (h : Tendsto m f (𝓝 x)) :
    Tendsto (fun a => Real.toNNReal (m a)) f (𝓝 (Real.toNNReal x)) :=
  (continuous_real_toNNReal.tendsto _).comp h

@[simp]
/-
**NNReal._root_.Real.map_toNNReal_atTop** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.map_toNNReal_atTop : map Real.toNNReal atTop = atTop := by
  rw [← map_coe_atTop, Function.LeftInverse.filter_map @Real.toNNReal_coe]
/-
**NNReal._root_.tendsto_real_toNNReal_atTop** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.tendsto_real_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop :=
  Real.map_toNNReal_atTop.le

@[simp]
/-
**NNReal._root_.Real.comap_toNNReal_atTop** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.comap_toNNReal_atTop : comap Real.toNNReal atTop = atTop := by
  refine le_antisymm ?_ tendsto_real_toNNReal_atTop.le_comap
  refine (atTop_basis_Ioi' 0).ge_iff.2 fun a ha ↦ ?_
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop a.toNNReal)] with x hx
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg ha.le).1 hx

@[simp]
/-
**NNReal._root_.Real.tendsto_toNNReal_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNRea
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.tendsto_toNNReal_atTop_iff {l : Filter α} {f : α → ℝ} :
    Tendsto (fun x ↦ (f x).toNNReal) l atTop ↔ Tendsto f l atTop := by
  rw [← Real.comap_toNNReal_atTop, tendsto_comap_iff, Function.comp_def]
/-
**NNReal._root_.Real.tendsto_toNNReal_atTop** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.tendsto_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop :=
  Real.tendsto_toNNReal_atTop_iff.2 tendsto_id
/-
**NNReal.nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：nhds_zero : 𝓝 (0 : Real>=0) = ⨅ (a : Real>=0) (_ : a != 0), 𝓟 (Iio a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_bot_order`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Pre
order α] [inst_2 : OrderBot α] [OrderTopology α],   nhds ⊥ = ⨅ l, ⨅ (_ : ⊥ < l),
 Fil…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem nhds_zero : 𝓝 (0 : ℝ≥0) = ⨅ (a : ℝ≥0) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp only [bot_lt_iff_ne_bot]; rfl
/-
**NNReal.nhds_zero_basis** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：nhds_zero_basis : (𝓝 (0 : Real>=0)).HasBasis (fun a : Real>=0 => 0 < a) fu
n a => Iio a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_bot_basis`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [inst_2 : OrderBot α] [OrderTopology α]   [Nontrivial α], (nhds ⊥).H
asBa…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0)).HasBasis (fun a : ℝ≥0 => 0 < a) fun a => Iio a :=
  nhds_bot_basis


@[norm_cast]
/-
**NNReal.hasSum_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：hasSum_coe {f : α -> Real>=0} {r : Real>=0} : HasSum (fun a => (f a : Real
)) (r : Real) L ↔ HasSum f r L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
    HasSum (fun a => (f a : ℝ)) (r : ℝ) L ↔ HasSum f r L := by
  simp only [HasSum, ← coe_sum, tendsto_coe]
/-
**NNReal._root_.HasSum.toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.HasSum.toNNReal {f : α → ℝ} {y : ℝ} (hf₀ : ∀ n, 0 ≤ f n)
    (hy : HasSum f y L) : HasSum (fun x => Real.toNNReal (f x)) y.toNNReal L := by
  rcases L.neBot_or_eq_bot with _ | hL
  · lift y to ℝ≥0 using hy.nonneg hf₀
    lift f to α → ℝ≥0 using hf₀
    simpa [hasSum_coe] using hy
  · simp [HasSum, hL]
/-
**NNReal.hasSum_real_toNNReal_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：hasSum_real_toNNReal_of_nonneg {f : α -> Real} (hf_nonneg : forall n, 0 <=
 f n) (hf : Summable f L) : HasSum (fun n => Real.toNNReal (f n)) (Real.toNNReal
 (∑'[L] n, f n)) L
参数：hf_nonneg : forall n, 0 <= f n；hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.toNNReal`：∀ {α : Type u_2} {L : SummationFilter α} {f : α → ℝ} {y
 : ℝ},   (∀ (n : α), 0 ≤ f n) → HasSum f y L → HasSum (fun x => (f x).toNNReal) 
y.toN…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem hasSum_real_toNNReal_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf : Summable f L) :
    HasSum (fun n => Real.toNNReal (f n)) (Real.toNNReal (∑'[L] n, f n)) L :=
  hf.hasSum.toNNReal hf_nonneg

@[norm_cast]
/-
**NNReal.summable_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_coe {f : α -> Real>=0} : (Summable (fun a => (f a : Real)) L) ↔ S
ummable f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SummationFilter.neBot_or_eq_bot`：neBot_or_eq_bot (L : SummationFilter β)
 : L.NeBot ∨ L.filter = ⊥
· 使用定理 `HasSum.nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [
inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 :
 To…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.hasSum_coe`：hasSum_coe {f : α -> Real>=0} {r : Real>=0} : HasSum 
(fun a => (f a : Real)) (r : Real) L ↔ HasSum f r L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem summable_coe {f : α → ℝ≥0} :
    (Summable (fun a => (f a : ℝ)) L) ↔ Summable f L := by
  rcases L.neBot_or_eq_bot with _ | hL
  · constructor
    · exact fun ⟨a, ha⟩ => ⟨⟨a, ha.nonneg fun x => (f x).2⟩, hasSum_coe.1 ha⟩
    · exact fun ⟨a, ha⟩ => ⟨a.1, hasSum_coe.2 ha⟩
  · simp [Summable, HasSum, hL]
/-
**NNReal.summable_mk** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_mk {f : α -> Real} (hf : forall n, 0 <= f n) : Summable (fun n =>
 ⟨f n, hf n⟩ : α -> Real>=0) L ↔ Summable f L
参数：hf : forall n, 0 <= f n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
-/
theorem summable_mk {f : α → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Summable (fun n ↦ ⟨f n, hf n⟩ : α → ℝ≥0) L ↔ Summable f L :=
  Iff.symm <| summable_coe (f := fun x => ⟨f x, hf x⟩)

@[norm_cast]
/-
**NNReal.coe_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_tsum {f : α -> Real>=0} : ↑(∑'[L] a, f a) = ∑'[L] a, (f a : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFil
ter β} {G : Type u_…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `continuous_real_toNNReal`：Continuous Real.toNNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_tsum {f : α → ℝ≥0} : ↑(∑'[L] a, f a) = ∑'[L] a, (f a : ℝ) :=
  Function.LeftInverse.map_tsum (g := NNReal.toRealHom)
    f NNReal.continuous_coe continuous_real_toNNReal (fun x ↦ by simp)
/-
**NNReal.coe_tsum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_tsum_of_nonneg {f : α -> Real} (hf₁ : forall n, 0 <= f n) : NNReal.mk 
(∑'[L] n, f n) (tsum_nonneg hf₁) = ∑'[L] n, NNReal.mk (f n) (hf₁ n)
参数：hf₁ : forall n, 0 <= f n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_tsum`：coe_tsum {f : α -> Real>=0} : ↑(∑'[L] a, f a) = ∑'[L] a
, (f a : Real)
-/
theorem coe_tsum_of_nonneg {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
    NNReal.mk (∑'[L] n, f n) (tsum_nonneg hf₁) = ∑'[L] n, NNReal.mk (f n) (hf₁ n) :=
  NNReal.eq <| Eq.symm <| coe_tsum (f := fun x => ⟨f x, hf₁ x⟩)

nonrec theorem tsum_mul_left (a : ℝ≥0) (f : α → ℝ≥0) :
    ∑'[L] x, a * f x = a * ∑'[L] x, f x :=
  NNReal.eq <| by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_left]

nonrec theorem tsum_mul_right (f : α → ℝ≥0) (a : ℝ≥0) :
    ∑'[L] x, f x * a = (∑'[L] x, f x) * a :=
  NNReal.eq <| by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_right]
/-
**NNReal.summable_comp_injective** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_comp_injective {β : Type*} {f : α -> Real>=0} (hf : Summable f) {
i : β -> α} (hi : Function.Injective i) : Summable (f ∘ i)
参数：hf : Summable f；hi : Function.Injective i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
-/
theorem summable_comp_injective {β : Type*} {f : α → ℝ≥0} (hf : Summable f) {i : β → α}
    (hi : Function.Injective i) : Summable (f ∘ i) := by
  rw [← summable_coe] at hf ⊢
  exact hf.comp_injective hi
/-
**NNReal.summable_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_nat_add (f : Nat -> Real>=0) (hf : Summable f) (k : Nat) : Summab
le fun i => f (i + k)
参数：f : Nat -> Real>=0；hf : Summable f；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.summable_comp_injective`：summable_comp_injective {β : Type*} {f :
 α -> Real>=0} (hf : Summable f) {i : β -> α} (hi : Function.Injective i) : Summ
able (f ∘ i)
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem summable_nat_add (f : ℕ → ℝ≥0) (hf : Summable f) (k : ℕ) : Summable fun i => f (i + k) :=
  summable_comp_injective hf <| add_left_injective k

nonrec theorem summable_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) :
    (Summable fun i => f (i + k)) ↔ Summable f := by
  rw [← summable_coe, ← summable_coe]
  exact @summable_nat_add_iff ℝ _ _ _ (fun i => (f i : ℝ)) k

nonrec theorem hasSum_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) {a : ℝ≥0} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i ∈ range k, f i) := by
  rw [← hasSum_coe, hasSum_nat_add_iff (f := fun n => toReal (f n)) k]; norm_cast
/-
**NNReal.sum_add_tsum_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：sum_add_tsum_nat_add {f : Nat -> Real>=0} (k : Nat) (hf : Summable f) : ∑'
 i, f i = (∑ i in range k, f i) + ∑' i, f (i + k)
参数：k : Nat；hf : Summable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.sum_add_tsum_nat_add'`：∀ {M : Type u_1} [inst : AddCommMonoid M
] [inst_1 : TopologicalSpace M] [T2Space M] [ContinuousAdd M] {f : ℕ → M}   {k :
 ℕ}, (Summable fun n…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.summable_nat_add_iff`：∀ {f : ℕ → NNReal} (k : ℕ), (Summable fun i
 => f (i + k)) ↔ Summable f
-/
theorem sum_add_tsum_nat_add {f : ℕ → ℝ≥0} (k : ℕ) (hf : Summable f) :
    ∑' i, f i = (∑ i ∈ range k, f i) + ∑' i, f (i + k) :=
  (((summable_nat_add_iff k).2 hf).sum_add_tsum_nat_add').symm
/-
**NNReal.iInf_real_pos_eq_iInf_nnreal_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iInf_real_pos_eq_iInf_nnreal_pos [CompleteLattice α] {f : Real -> α} : ⨅ (
n : Real) (_ : 0 < n), f n = ⨅ (n : Real>=0) (_ : 0 < n), f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iInf_mono'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Comp
leteLattice α] {f : ι → α} {g : ι' → α},   (∀ (i : ι), ∃ i', g i' ≤ f i) → iInf 
…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `iInf₂_mono'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {κ : ι → So
rt u_6} {κ' : ι' → Sort u_7} [inst : CompleteLattice α]   {f : (i : ι) → κ i → α
}…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem iInf_real_pos_eq_iInf_nnreal_pos [CompleteLattice α] {f : ℝ → α} :
    ⨅ (n : ℝ) (_ : 0 < n), f n = ⨅ (n : ℝ≥0) (_ : 0 < n), f n :=
  le_antisymm (iInf_mono' fun r => ⟨r, le_rfl⟩) (iInf₂_mono' fun r hr => ⟨⟨r, hr.le⟩, hr, le_rfl⟩)

end coe

/-
**NNReal.tendsto_cofinite_zero_of_summable** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tendsto_cofinite_zero_of_summable {α} {f : α -> Real>=0} (hf : Summable f)
 : Tendsto f cofinite (𝓝 0)
参数：hf : Summable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tendsto_cofinite_zero`：∀ {α : Type u_1} {G : Type u_4} [inst : 
TopologicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   {f : α
 → G}, Summable f → …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
-/
theorem tendsto_cofinite_zero_of_summable {α} {f : α → ℝ≥0} (hf : Summable f) :
    Tendsto f cofinite (𝓝 0) := by
  simp only [← summable_coe, ← tendsto_coe] at hf ⊢
  exact hf.tendsto_cofinite_zero
/-
**NNReal.tendsto_atTop_zero_of_summable** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tendsto_atTop_zero_of_summable {f : Nat -> Real>=0} (hf : Summable f) : Te
ndsto f atTop (𝓝 0)
参数：hf : Summable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `NNReal.tendsto_cofinite_zero_of_summable`：tendsto_cofinite_zero_of_summa
ble {α} {f : α -> Real>=0} (hf : Summable f) : Tendsto f cofinite (𝓝 0)
-/
theorem tendsto_atTop_zero_of_summable {f : ℕ → ℝ≥0} (hf : Summable f) : Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_summable hf

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
nonrec theorem tendsto_tsum_compl_atTop_zero {α : Type*} (f : α → ℝ≥0) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  simp_rw [← tendsto_coe, coe_tsum, NNReal.coe_zero]
  exact tendsto_tsum_compl_atTop_zero fun a : α => (f a : ℝ)

/-- `x ↦ x ^ n` as an order isomorphism of `ℝ≥0`. -/
/-
**NNReal.powOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：powOrderIso (n : Nat) (hn : n != 0) : Real>=0 ≃o Real>=0
参数：n : Nat；hn : n != 0。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x ↦ x ^ n` as an order isomorphism of `ℝ≥0`.
-/
def powOrderIso (n : ℕ) (hn : n ≠ 0) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (fun x ↦ x ^ n) (fun x y h =>
      pow_left_strictMonoOn₀ hn (zero_le (a := x)) (zero_le (a := y)) h) <|
    (continuous_id.pow _).surjective (tendsto_pow_atTop hn) <| by
      simpa [OrderBot.atBot_eq, pos_iff_ne_zero]

section Monotone

/-- A monotone, bounded above sequence `f : ℕ → ℝ` has a finite limit. -/
@[deprecated tendsto_atTop_ciSup (since := "2026-01-14")]
/-
**NNReal._root_.Real.tendsto_of_bddAbove_monotone** 是 Mathlib 中的一个定理，位于命名空间 `NNR
eal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monotone, bounded above sequence `f : ℕ → ℝ` has a finite limit.
-/
theorem _root_.Real.tendsto_of_bddAbove_monotone {f : ℕ → ℝ} (h_bdd : BddAbove (Set.range f))
    (h_mon : Monotone f) : ∃ r : ℝ, Tendsto f atTop (𝓝 r) :=
  ⟨iSup f, tendsto_atTop_ciSup h_mon h_bdd⟩

/-- An antitone, bounded below sequence `f : ℕ → ℝ` has a finite limit. -/
@[deprecated tendsto_atTop_ciInf (since := "2026-01-14")]
/-
**NNReal._root_.Real.tendsto_of_bddBelow_antitone** 是 Mathlib 中的一个定理，位于命名空间 `NNR
eal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An antitone, bounded below sequence `f : ℕ → ℝ` has a finite limit.
-/
theorem _root_.Real.tendsto_of_bddBelow_antitone {f : ℕ → ℝ} (h_bdd : BddBelow (Set.range f))
    (h_ant : Antitone f) : ∃ r : ℝ, Tendsto f atTop (𝓝 r) :=
  ⟨iInf f, tendsto_atTop_ciInf h_ant h_bdd⟩

variable {ι : Type*} [Preorder ι]

/-- An antitone sequence `f : ℕ → ℝ≥0` has a finite limit. -/
@[deprecated tendsto_atTop_ciInf (since := "2026-01-14")]
/-
**NNReal.tendsto_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：tendsto_of_antitone {f : Nat -> Real>=0} (h_ant : Antitone f) : exists r :
 Real>=0, Tendsto f atTop (𝓝 r)
参数：h_ant : Antitone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_ciInf`：tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : B
ddBelow <| range f) : Tendsto f atTop (𝓝 (⨅ i, f i))
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
An antitone sequence `f : ℕ → ℝ≥0` has a finite limit.
-/
theorem tendsto_of_antitone {f : ℕ → ℝ≥0} (h_ant : Antitone f) :
    ∃ r : ℝ≥0, Tendsto f atTop (𝓝 r) := ⟨iInf f, tendsto_atTop_ciInf h_ant (by simp)⟩

end Monotone

/-
**NNReal.iSup_pow_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：iSup_pow_of_ne_zero (hn : n != 0) (f : ι -> Real>=0) : (⨆ i, f i) ^ n = ⨆ 
i, f i ^ n
参数：hn : n != 0；f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrderIso.map_ciSup'`：map_ciSup' (e : α ≃o β) (f : ι -> α) : e (⨆ i, f i)
 = ⨆ i, e (f i)
-/
lemma iSup_pow_of_ne_zero (hn : n ≠ 0) (f : ι → ℝ≥0) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n :=
  (NNReal.powOrderIso n hn).map_ciSup' _
/-
**NNReal.iSup_pow** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：iSup_pow [Nonempty ι] (f : ι -> Real>=0) (n : Nat) : (⨆ i, f i) ^ n = ⨆ i,
 f i ^ n
参数：f : ι -> Real>=0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `NNReal.iSup_pow_of_ne_zero`：iSup_pow_of_ne_zero (hn : n != 0) (f : ι -> 
Real>=0) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n
-/
lemma iSup_pow [Nonempty ι] (f : ι → ℝ≥0) (n : ℕ) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _

end NNReal

namespace ENNReal

attribute [simp] ENNReal.top_pow

/-- `x ↦ x ^ n` as an order isomorphism of `ℝ≥0∞`.

See also `ENNReal.orderIsoRpow`. -/
/-
**ENNReal.powOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：powOrderIso (n : Nat) (hn : n != 0) : Real>=0∞ ≃o Real>=0∞
参数：n : Nat；hn : n != 0。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal

--- 原说明 ---
`x ↦ x ^ n` as an order isomorphism of `ℝ≥0∞`.

See also `ENNReal.orderIsoRpow`.
-/
def powOrderIso (n : ℕ) (hn : n ≠ 0) : ℝ≥0∞ ≃o ℝ≥0∞ :=
  (NNReal.powOrderIso n hn).withTopCongr.copy (· ^ n) _
    (by cases n; (· cases hn rfl); · ext (_ | _) <;> rfl) rfl
/-
**ENNReal.iSup_pow_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_pow_of_ne_zero (hn : n != 0) (f : ι -> Real>=0∞) : (⨆ i, f i) ^ n = ⨆
 i, f i ^ n
参数：hn : n != 0；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
lemma iSup_pow_of_ne_zero (hn : n ≠ 0) (f : ι → ℝ≥0∞) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n :=
  (powOrderIso n hn).map_iSup _
/-
**ENNReal.iSup_pow** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_pow [Nonempty ι] (f : ι -> Real>=0∞) (n : Nat) : (⨆ i, f i) ^ n = ⨆ i
, f i ^ n
参数：f : ι -> Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ENNReal.iSup_pow_of_ne_zero`：iSup_pow_of_ne_zero (hn : n != 0) (f : ι ->
 Real>=0∞) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n
-/
lemma iSup_pow [Nonempty ι] (f : ι → ℝ≥0∞) (n : ℕ) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _
/-
**ENNReal.iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iSup₂_pow_of_ne_zero {κ : ι → Sort*} (f : (i : ι) → κ i → ℝ≥0∞) {n : ℕ} (hn : n ≠ 0) :
    (⨆ i, ⨆ j, f i j) ^ n = ⨆ i, ⨆ j, f i j ^ n :=
  (powOrderIso n hn).map_iSup₂ f

end ENNReal

open NNReal in
/-
**Real.iSup_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Real.iSup_pow [Nonempty ι] {f : ι -> Real} (hf : forall i, 0 <= f i) (n : 
Nat) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n
参数：hf : forall i, 0 <= f i；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NNReal.iSup_pow`：iSup_pow [Nonempty ι] (f : ι -> Real>=0) (n : Nat) : (⨆
 i, f i) ^ n = ⨆ i, f i ^ n
-/
lemma Real.iSup_pow [Nonempty ι] {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (n : ℕ) :
    (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  lift f to ι → ℝ≥0 using hf; dsimp; exact mod_cast NNReal.iSup_pow f n
/-
**Real.iSup_pow_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Real.iSup_pow_of_ne_zero {f : ι -> Real} (hf : forall i, 0 <= f i) (hn : n
 != 0) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n
参数：hf : forall i, 0 <= f i；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Real.iSup_pow`：Real.iSup_pow [Nonempty ι] {f : ι -> Real} (hf : forall i
, 0 <= f i) (n : Nat) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n
-/
lemma Real.iSup_pow_of_ne_zero {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (hn : n ≠ 0) :
    (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  cases isEmpty_or_nonempty ι
  · simp [hn]
  · exact iSup_pow hf _
